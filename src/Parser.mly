

(* This file is free software, part of smtlib-utils. See file "license" for more details. *)

(** {1 Parser for SMTLIB2.6} *)

(* vim:SyntasticToggleMode:
   vim:set ft=yacc: *)

%{

  let consts =
    let module A = Ast in
    let tbl = Hashtbl.create 32 in
    let mkc c name ~loc = function
      | [] -> c
      | _ ->
        A.parse_errorf ~loc "wrong arity for constant %s" name
    and mkf1 f name ~loc = function
      | [t] -> f t
      | _ ->
        A.parse_errorf ~loc "wrong arity for unary function %s" name
    and mkl f _name ~loc:_ args =
      f args
    and arith_op op _name ~loc:_ args =
      A.arith op args
    in
    List.iter (fun (s,f) -> Hashtbl.add tbl s f) [
      ("true", mkc A.true_);
      ("false", mkc A.false_);
      ("or", mkl A.or_);
      ("and", mkl A.and_);
      ("not", mkf1 A.not_);
      ("+", arith_op A.Add);
      ("-", arith_op A.Minus);
      ("*", arith_op A.Mult);
      ("/", arith_op A.Div);
      ("<=", arith_op A.Leq);
      ("<", arith_op A.Lt);
      (">=", arith_op A.Geq);
      (">", arith_op A.Gt);
    ];
    tbl

  let apply_const ~loc name args =
    let module A = Ast in
    try
      let f = Hashtbl.find consts name in
      f name ~loc args
    with Not_found ->
      if args=[] then A.const name else A.app name args
%}

%token EOI

%token LEFT_PAREN "("
%token RIGHT_PAREN ")"

%token PAR "par"
%token ARROW "=>"

%token DISTINCT "distinct"
%token EQ "="
%token IF "ite"
%token MATCH "match"
%token FUN "lambda"
%token LET "let"
%token AS "as"
%token WILDCARD "_"
%token IS "is"
%token AT "@"
%token BANG "!"

%token DATA "declare-datatypes"
%token ASSERT "assert"
%token FORALL "forall"
%token EXISTS "exists"
%token DECLARE_SORT "declare-sort"
%token DECLARE_CONST "declare-const"
%token DECLARE_FUN "declare-fun"
%token DEFINE_FUN "define-fun"
%token DEFINE_FUN_REC "define-fun-rec"
%token DEFINE_FUNS_REC "define-funs-rec"
%token CHECK_SAT "check-sat"
%token CHECK_SAT_ASSUMING "check-sat-assuming"
%token GET_VALUE "get-value"

%token <string>IDENT
%token <string>QUOTED

%start <Ast.term> parse_term
%start <Ast.ty> parse_ty
%start <Ast.statement> parse
%start <Ast.statement list> parse_list

%%

parse_list: l=stmt* EOI {l}
parse: t=stmt EOI { t }
parse_term: t=term EOI { t }
parse_ty: t=ty EOI { t }

cstor_arg:
  | "(" name=IDENT ty=ty ")" { name, ty }

cstor_dec:
  | "(" c=IDENT l=cstor_arg* ")" { c, l }

cstor:
  | dec=cstor_dec { let c,l = dec in Ast.mk_cstor ~vars:[] c l }
  | "(" "par" "(" vars=var+ ")" dec=cstor_dec ")"
    { let c,l = dec in Ast.mk_cstor ~vars c l }

cstors:
  | "(" l=cstor+ ")" { l }

%inline ty_decl:
  | s=IDENT n=IDENT  {
      let loc = Loc.mk_pos $startpos $endpos in
      try
        let n = int_of_string n in
        s, n
      with Failure _ ->
        Ast.parse_errorf ~loc "expected arity to be an integer, not `%s`" n
  }

ty_decl_paren:
  | "(" ty=ty_decl ")" { ty }

fun_def_mono:
  | f=IDENT "(" args=typed_var* ")"
    ret=ty
    { f, args, ret }

fun_decl_mono:
  | f=IDENT "(" args=ty* ")"
    ret=ty
    { f, args, ret }

fun_decl:
  | tup=fun_decl_mono { let f, args, ret = tup in [], f, args, ret }
  | "(" "par"
      "(" tyvars=tyvar* ")"
      "(" tup=fun_decl_mono ")"
    ")"
    { let f, args, ret = tup in tyvars, f, args, ret }

fun_rec:
  | tup=fun_def_mono body=term
    {
      let f, args, ret = tup in
      Ast.mk_fun_rec ~ty_vars:[] f args ret body
    }
  | "(" "par"
      "(" l=tyvar* ")"
      "(" tup=fun_def_mono body=term ")"
    ")"
    {
      let f, args, ret = tup in
      Ast.mk_fun_rec ~ty_vars:l f args ret body
    }

funs_rec_decl:
  | "(" tup=fun_def_mono ")"
    {
      let f, args, ret = tup in
      Ast.mk_fun_decl ~ty_vars:[] f args ret
    }
  | "(" "par"
      "(" l=tyvar* ")"
      "(" tup=fun_def_mono ")"
    ")"
    {
      let f, args, ret = tup in
      Ast.mk_fun_decl ~ty_vars:l f args ret
    }

par_term:
  | "(" "par" "(" tyvars=tyvar+ ")" t=term ")"
  { tyvars, t }
  | t=term
  { [], t }

anystr:
  | s=IDENT {s}
  | s=QUOTED {s}

prop_lit:
  | s=var { s, true }
  | "(" not_=IDENT s=var ")" {
    if not_ = "not" then s, false
    else
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.parse_errorf ~loc "expected `not`, not `%s`" not_
    }

stmt:
  | "(" "assert" t=term ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.assert_ ~loc t
    }
  | "(" "declare-sort" td=ty_decl ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      let s, n = td in
      Ast.decl_sort ~loc s ~arity:n
    }
  | "(" "declare-datatypes"
      "(" tys=ty_decl_paren+ ")"
      "(" l=cstors+ ")"
    ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.data_zip ~loc tys l
    }
  | "(" "declare-fun" tup=fun_decl ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      let tyvars, f, args, ret = tup in
      Ast.decl_fun ~loc ~tyvars f args ret
    }
  | "(" "declare-const" f=IDENT ty=ty ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.decl_fun ~loc ~tyvars:[] f [] ty
    }
  | "(" "define-fun" f=fun_rec ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.fun_def ~loc f
    }
  | "(" "define-fun-rec" f=fun_rec ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.fun_rec ~loc f
    }
  | "(" "define-funs-rec"
      "(" decls=funs_rec_decl+ ")"
      "(" bodies=term+ ")"
    ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.funs_rec ~loc decls bodies
    }
  | "(" "check-sat" ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.check_sat ~loc ()
    }
  | "(" "check-sat-assuming" "(" l=prop_lit* ")" ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.check_sat_assuming ~loc l
    }
  | "(" "get-value" l=term+ ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.get_value ~loc l
    }
  | "(" s=IDENT args=anystr* ")"
    {
      let loc = Loc.mk_pos $startpos $endpos in
      match s, args with
      | "exit", [] -> Ast.exit ~loc ()
      | "set-logic", [l] -> Ast.set_logic ~loc l
      | "set-info", [a;b] -> Ast.set_info ~loc a b
      | "set-option", l -> Ast.set_option ~loc l
      | "get-option", [a] -> Ast.get_option ~loc a
      | "get-info", [a] -> Ast.get_info ~loc a
      | "get-assertions", [] -> Ast.get_assertions ~loc ()
      | "get-assignment", [] -> Ast.get_assignment ~loc ()
      | "get-proof", [] -> Ast.get_proof ~loc ()
      | "get-model", [] -> Ast.get_model ~loc ()
      | "get-unsat-core", [] -> Ast.get_unsat_core ~loc ()
      | "get-unsat-assumptions", [] -> Ast.get_unsat_assumptions ~loc ()
      | "reset", [] -> Ast.reset ~loc ()
      | "reset-assertions", [] -> Ast.reset_assertions ~loc ()
      | "push", [x] ->
        (try Ast.push ~loc (int_of_string x) with _ ->
         Ast.parse_errorf ~loc "expected an integer argument for push, not %s" x)
      | "pop", [x] ->
        (try Ast.pop ~loc (int_of_string x) with _ ->
         Ast.parse_errorf ~loc "expected an integer argument for pop, not %s" x)
      | _ ->
        Ast.parse_errorf ~loc "expected statement"
    }
  | error
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.parse_errorf ~loc "expected statement"
    }

var:
  | "_" { "_" }
  | s=IDENT { s }
tyvar:
  | s=IDENT { s }

ty:
  | s=IDENT {
    begin match s with
      | "Bool" -> Ast.ty_bool
      | "Real" -> Ast.ty_real
      | _ -> Ast.ty_const s
    end
    }
  | "(" s=IDENT args=ty+ ")"
    { Ast.ty_app s args }
  | "(" "=>" tup=ty_arrow_args ")"
    {
      let args, ret = tup in
      Ast.ty_arrow_l args ret }

ty_arrow_args:
  | a=ty ret=ty { [a], ret }
  | a=ty tup=ty_arrow_args { a :: fst tup, snd tup }

typed_var:
  | "(" s=var ty=ty ")" { s, ty }

case:
  | "(" c=IDENT rhs=term ")"
    { Ast.Match_case (c, [], rhs) }
  | "(" "(" c=IDENT vars=var+ ")" rhs=term ")"
    { Ast.Match_case (c, vars, rhs) }
  | "(" "_" rhs=term ")"
    { Ast.Match_default rhs }

binding:
  | "(" v=var t=term ")" { v, t }

term:
  | s=QUOTED { Ast.const s }
  | s=IDENT {
    let loc = Loc.mk_pos $startpos $endpos in
    apply_const ~loc s []
    }
  | t=composite_term { t }
  | error
    {
      let loc = Loc.mk_pos $startpos $endpos in
      Ast.parse_errorf ~loc "expected term"
    }

attr:
  | a=IDENT b=anystr { a,b }

composite_term:
  | "(" t=term ")" { t }
  | "(" "ite" a=term b=term c=term ")" { Ast.if_ a b c }
  | "(" "distinct" l=term+ ")" { Ast.distinct l }
  | "(" "=" a=term b=term ")" { Ast.eq a b }
  | "(" "=>" a=term b=term ")" { Ast.imply a b }
  | "(" f=IDENT args=term+ ")" {
    let loc = Loc.mk_pos $startpos $endpos in
    apply_const ~loc f args }
  | "(" f=composite_term args=term+ ")" { Ast.ho_app_l f args }
  | "(" "@" f=term arg=term ")" { Ast.ho_app f arg }
  | "(" "!" t=term attrs=attr+ ")" { Ast.attr t attrs }
  | "(" "match" lhs=term "(" l=case+ ")" ")"
    { Ast.match_ lhs l }
  | "(" "lambda" "(" vars=typed_var+ ")" body=term ")"
    { Ast.fun_l vars body }
  | "(" "(" "_" "is" c=IDENT ")" t=term ")"
    { Ast.is_a c t }
  | "(" "let" "(" l=binding+ ")" r=term ")"
    { Ast.let_ l r }
  | "(" "as" t=term ty=ty ")"
    { Ast.cast t ~ty }
  | "(" "forall" "(" vars=typed_var+ ")" f=term ")"
    { Ast.forall vars f }
  | "(" "exists" "(" vars=typed_var+ ")" f=term ")"
    { Ast.exists vars f }

%%
