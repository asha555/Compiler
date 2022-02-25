(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)
open Tigercommon
module S = Symbol
module A = Absyn
module E = Semenv
module Err = Errenv
module EFmt = ErrorFormatter
module Ty = Types
module PT = Prtypes
module TA = Tabsyn

(** Context record contains the environments we use in our translation *)

let heap: Ty.ty S.table = S.empty

type context =
  { venv: E.enventry S.table (* Γ from our formal typing rules *)
  ; tenv: Ty.ty S.table (* Δ from our formal typing rules *)
  ; err: Err.errenv (* error environment *)
  ; breakable: bool (* whether we can break out at the current location*) 
  ; unassignable: E.enventry S.table (* some vars that cannot be assigned (iterators of for-loops) *)
}

(*Exp of { exp_base: exp_base; pos: pos; ty: T.ty }
*)
let exp_ty (TA.Exp{ty;_}as e)  = (e,ty)
let var_ty (TA.Var{ty;_}as v) = (v,ty)

exception NotImplemented
(* the final code should work without this exception *)

open Ty
let rec transExp ({venv; tenv; err; breakable; unassignable} : context) e =
  let rec trexp (A.Exp {exp_base; pos}) =
    let (^!) exp_base ty = TA.Exp {exp_base;pos;ty} in
    match exp_base with
    | A.IntExp n ->  TA.IntExp n ^! INT 

    | A.StringExp s -> TA.StringExp s ^! STRING 

    (* the above cases have been implemented in class *)
    | A.OpExp {left; oper; right} -> 
      let e_exp1, t_exp1 = exp_ty(trexp left) in 
      let e_exp2, t_exp2 = exp_ty(trexp right) in 
      let actualT_exp1 = actualTy {venv; tenv; err; breakable; unassignable} t_exp1 in
      let actualT_exp2 = actualTy {venv; tenv; err; breakable; unassignable} t_exp2 in
      (match actualT_exp1, actualT_exp2 with 
      | Ty.INT, Ty.INT -> TA.OpExp {left = e_exp1; right = e_exp2; oper = oper} ^! Ty.INT
      | Ty.STRING, Ty.STRING -> (match oper with 
        | A.EqOp | A.GeOp | A.GtOp | A.LeOp | A.LtOp | A.NeqOp -> 
          TA.OpExp {left = e_exp1; right = e_exp2; oper = oper} ^! Ty.INT
        | _ -> Err.error err pos (EFmt.errorArith); ErrorExp ^! Ty.ERROR)
      | ty1, ty2 -> (match oper with
        | A.NeqOp | A.EqOp -> 
          if ty1 != Ty.VOID && (ty1 != Ty.NIL || ty2 != Ty.NIL) && (isSubtype {venv; tenv; err; breakable; unassignable} ty1 ty2 "OpExp oper ty1, ty2" || isSubtype {venv; tenv; err; breakable; unassignable} ty2 ty1 "OpExp oper ty1, ty2")
          then TA.OpExp {left = e_exp1; right = e_exp2; oper = oper} ^! Ty.INT
          else (Err.error err pos (EFmt.errorEqNeqComparison ty1 ty2); ErrorExp ^! Ty.ERROR)
        | _ -> Err.error err pos (EFmt.errorArith); ErrorExp ^! Ty.ERROR))

    | A.CallExp {func; args} -> (match S.look (venv, func) with 
      | Some E.FunEntry {formals;result} -> 
        let argsExp, argsTy = List.split (List.map (fun e_x -> (exp_ty(trexp e_x))) args) in 
        let isArgsCorrectTypes = List.fold_left2 (fun isArgsCorrect arg formal -> isArgsCorrect && (isSubtype {venv; tenv; err; breakable; unassignable} arg formal "isArgsCorrect")) true argsTy formals in 
        let isArgsCorrectAmount = List.length args = List.length formals in
        if isArgsCorrectTypes && isArgsCorrectAmount 
        then CallExp {func=func; args=argsExp} ^! result
        else (Err.error err pos (EFmt.errorFunctionArguments func); ErrorExp ^! Ty.ERROR) 
      | _ -> (Err.error err pos (EFmt.errorFunctionUndefined func); ErrorExp ^! Ty.ERROR))

    | A.SeqExp explist -> (match List.length explist with
      | 0 -> TA.SeqExp [] ^! Ty.VOID (* NoVal rule *)
      | 1 -> (List.hd (List.map trexp explist))
      | _ -> 
        let e_list = List.map trexp explist in
        let t_list = List.map (fun e -> let _, t = exp_ty e in t) e_list in
        let length_t_list = List.length t_list in
        let t_list_without_last_elem = List.filteri (fun i _ -> i < length_t_list-1) t_list in
      if List.for_all (fun t -> t != Ty.NIL) t_list_without_last_elem
      then TA.SeqExp e_list ^! (match (List.nth e_list ((List.length e_list)-1)) with
        | Exp { exp_base; pos; ty} -> ty)
      else (Err.error err pos ("Only the last element of a seqence expression can be nil."); ErrorExp ^! Ty.ERROR))

    | A.IfExp {test; thn; els=None} -> 
      let e1, t1=exp_ty(trexp test) in
      let e2, t2=exp_ty(trexp thn) in
      if t1 = Ty.INT then 
        (
          if t2=Ty.VOID 
          then TA.IfExp {test=e1; thn=e2; els=None} ^! t2 
          else (Err.error err pos (EFmt.errorIfThenShouldBeVoid t2); ErrorExp ^! Ty.ERROR)
        ) 
      else (Err.error err pos (EFmt.errorIntRequired t1); ErrorExp ^! Ty.ERROR)

    | A.IfExp {test; thn; els=Some elsExp} -> 
      let e1, t1 = exp_ty(trexp test) in 
      let e2, t2 = exp_ty(trexp thn) in 
      let e3, t3 = exp_ty(trexp elsExp) in 
      if (actualTy {venv; tenv; err; breakable; unassignable} t1) = Ty.INT
      then 
        (if isSubtype {venv; tenv; err; breakable; unassignable} t2 t3 "A.IfExp then and else should have same type" && isSubtype {venv; tenv; err; breakable; unassignable} t3 t2 "A.IfExp then and else should have same type"
        then TA.IfExp {test=e1; thn=e2; els=Some e3} ^! (getParentType {venv; tenv; err; breakable; unassignable} t2 t3)
        else (Err.error err pos (EFmt.errorIfBranchesNotSameType t2 t3); ErrorExp ^! Ty.ERROR)) 
      else (Err.error err pos (EFmt.errorIntRequired t1); ErrorExp ^! Ty.ERROR)

    | A.WhileExp {test;body} -> let exp_test, type_test = exp_ty(trexp test) in (match actualTy {venv; tenv; err; breakable; unassignable} type_test with
      | Ty.INT ->
        let _ = {venv; tenv; err; breakable; unassignable} in
        let exp_body,t_body = exp_ty(transExp {venv; tenv; err; breakable=true; unassignable} body) in (match t_body with
          | Ty.VOID -> WhileExp{test = exp_test; body = exp_body } ^! Ty.VOID
          | _ ->  (Err.error err pos (EFmt.errorWhileShouldBeVoid t_body); ErrorExp ^! Ty.ERROR))
      | _ -> ( (Err.error err pos (EFmt.errorIntRequired type_test); ErrorExp ^! Ty.ERROR))) 

    | A.LetExp {decls; body} -> 
      let newVenv, newTenv, declExps = transDecls {venv; tenv; err; breakable; unassignable} decls in 
      let bodyExp, bodyTy = exp_ty(transExp {venv=newVenv; tenv=newTenv; err; breakable; unassignable} body) in
      TA.LetExp {decls = declExps; body = bodyExp} ^! bodyTy
      

    | A.VarExp v -> let v, vTy = var_ty (trvar v) in (match Some(vTy) with
       | None -> Err.error err pos ("The type has only been saved in the environment. It has not been defined"); ErrorExp ^! Ty.ERROR
       | _-> VarExp v ^! vTy)

    | A.AssignExp {var; exp} -> 
      let v_lval, t_lval = var_ty(trvar var) in 
      let e_exp, t_exp= exp_ty(trexp exp) in 
      if assignable {venv; tenv; err; breakable; unassignable} var
      then if isSubtype {venv; tenv; err; breakable; unassignable} t_exp t_lval ""
        then TA.AssignExp {var=v_lval; exp=e_exp} ^! Ty.VOID
        else (Err.error err pos ("A.AssignExp: Variable and experession type mismatch"); ErrorExp ^! Ty.VOID)
      else (Err.error err pos (EFmt.errorVariableUnassignable (match var with
      | Var {var_base=SimpleVar sym; _} -> sym 
      | _ -> S.symbol "doesNotExists")); ErrorExp ^! Ty.VOID)
        
    | A.ArrayExp {typ; size; init} -> 
      let e_size, t_size = exp_ty(trexp size) in 
      let e_init, t_init = exp_ty(trexp init) in
      let tau_mark = lookUpType {venv; tenv; err; breakable; unassignable} typ pos "ArrayExp" in 
      let arr_tau = actualTy {venv; tenv; err; breakable; unassignable} tau_mark in 
      if t_size = Ty.INT
      then (match arr_tau with
      | Ty.ARRAY(tau, _) ->
        if isSubtype {venv; tenv; err; breakable; unassignable} t_init tau "A.ArrayExp array element type required"
        then TA.ArrayExp {size=e_size; init=e_init} ^! tau_mark
        else (Err.error err pos (EFmt.errorArrayInitType t_init tau); print_newline(); print_string "tau: "; printType tau; print_string "\nt_init: "; printType t_init; ErrorExp ^! Ty.ERROR)
      | _ -> (Err.error err pos "The type isn't an array type"; print_newline(); print_string "arr_tau was not an array!"; ErrorExp ^! Ty.ERROR))
      else (Err.error err pos (EFmt.errorIntRequired t_size); ErrorExp ^! Ty.ERROR)

    | A.BreakExp -> 
      if breakable
      then BreakExp ^! Ty.VOID
      else (Err.error err pos (EFmt.errorBreak); ErrorExp ^! Ty.ERROR)

    | A.ForExp {var; escape; lo; hi; body} ->
      let e_lo, t_lo = exp_ty(trexp lo) in
      let e_hi, t_hi = exp_ty(trexp hi) in
      (match t_lo, t_hi with
      | Ty.INT, Ty.INT -> 
        let newVenv = S.enter (venv, var, E.VarEntry Ty.INT) in
        let newUnassignable = S.enter (unassignable, var, E.VarEntry Ty.INT) in
        let e_body, t_body = exp_ty (transExp {venv=newVenv; tenv; err; breakable=true; unassignable=newUnassignable} body) in
        (match t_body with
        | Ty.VOID -> TA.ForExp {var; escape; lo=e_lo; hi=e_hi; body=e_body} ^! Ty.VOID
        | _ -> (Err.error err pos "\nForExp. The last expression in a for-loop must have type void\n"; ErrorExp ^! Ty.ERROR))
      | _ -> (Err.error err pos "\nForExp. the iterator high and low values must be integers\n"; ErrorExp ^! Ty.ERROR))

    | A.NilExp -> TA.NilExp ^! Ty.NIL

    | A.RecordExp {fields; typ} ->
      let t = lookUpType {venv; tenv; err; breakable; unassignable} typ pos "RecordExp" in
      let rec_t = actualTy {venv; tenv; err; breakable; unassignable} t in
      (match rec_t with
        | Ty.RECORD(sym_ty_list, _) ->
          (match doesExpretionsMatchTypes {venv; tenv; err; breakable; unassignable} sym_ty_list fields with
          | expressionsMatchTypes, sym_exp_list -> if expressionsMatchTypes
            then TA.RecordExp {fields = sym_exp_list} ^! t
            else (Printf.printf "\nTypes of arguments does not match field types\n"; ErrorExp ^! Ty.ERROR))
        | _ -> (Err.error err pos ("Record error"); ErrorExp ^! Ty.ERROR))
  
  and trvar (A.Var{var_base;pos}) = 
    let (^@) var_base ty = TA.Var {var_base;pos;ty} in 
    match var_base with 
    | A.SimpleVar s -> (match S.look (venv, s) with 
      | Some (E.VarEntry ty) -> (SimpleVar s) ^@ ty
      | Some E.FunEntry {formals; result} -> (Err.error err pos ("'"^(S.name s)^"' is a function not a simple var!"); (SimpleVar s) ^@ Ty.ERROR)
      | None -> (Err.error err pos ("The type of '"^(S.name s)^"' is saved but not defined in the tenv!"); (SimpleVar s) ^@ Ty.ERROR))
    | A.FieldVar (var, sym) ->
      let v_lval, t_lval = var_ty(trvar var) in 
      let rec_ty = actualTy {venv; tenv; err; breakable; unassignable} t_lval in 
      (match rec_ty with
      | Ty.RECORD (sym_ty_list, _) ->
        if List.exists (fun sym_ty->match sym_ty with
          | sym_i, _ -> sym_i = sym) sym_ty_list
        then 
          let _, ty_field = List.find (fun sym_ty->match sym_ty with
          | sym_i, _ -> sym_i = sym) sym_ty_list in
          TA.FieldVar (v_lval,sym) ^@ ty_field
        else
          (Err.error err pos "This field is not part of the record!!!"; TA.FieldVar (v_lval, sym) ^@ Ty.ERROR)
      | _ -> (Err.error err pos "This var is NOT a record type!!!";TA.FieldVar (v_lval, sym) ^@ Ty.ERROR))      
      | A.SubscriptVar (var, exp) -> 
        let v_lval, t_lval = var_ty(trvar var) in
        let t_lvalArrTy = actualTy {venv; tenv; err; breakable; unassignable} t_lval in 
        let e_exp, t_exp = exp_ty(trexp exp) in 
        (match actualTy {venv; tenv; err; breakable; unassignable} t_lvalArrTy with 
        | Ty.ARRAY (t_inner,_) -> (match actualTy {venv; tenv; err; breakable; unassignable} t_exp with
          | Ty.INT -> SubscriptVar(v_lval,e_exp) ^@ t_inner
          | _ -> (Err.error err pos (EFmt.errorIntRequired t_exp); SubscriptVar(v_lval, e_exp)^@ Ty.ERROR)   
        )
        | _ -> (Err.error err pos ("Array var didn't have array type"); SubscriptVar(v_lval, e_exp)^@ Ty.ERROR))
  in
    trexp e

and getParentType context t1 t2 = match actualTy context t1, actualTy context t2 with
| Ty.RECORD (l,u), Ty.NIL -> t1
| Ty.NIL, Ty.RECORD (l,u) -> t2
| _ -> t1

and assignable {venv; tenv; err; breakable; unassignable} (Var{var_base; _}): bool =
  match var_base with
    | SimpleVar sym -> 
      (match S.look (unassignable, sym) with
      | Some _ -> false
      | None -> true)
    | _ -> true

and transDecls ({venv; tenv; err; breakable; unassignable} : context) decls = transDeclsRec {venv; tenv; err; breakable; unassignable} decls []
and transDeclsRec ({venv; tenv; err; breakable; unassignable} : context) decls declExps = (match List.length decls with
| 0 -> (venv, tenv, declExps)
| _ -> let (newVenv, newTenv, declExp) = transDecl {venv; tenv; err; breakable; unassignable} (List.hd decls) in 
       transDeclsRec {venv=newVenv; tenv=newTenv; err; breakable; unassignable} (List.tl decls) (declExps @ [declExp]))
and transDecl ({venv; tenv; err; breakable; unassignable} : context) decl = match decl with
  | A.FunctionDec fundecl_list -> 
    let venv' = List.fold_left (fun newVenv fdecl -> (match fdecl with
      | A.Fdecl {name; params; result; body; pos} -> 
        let formals = List.map (fun p->
          (match p with
          | A.Field {name; escape; typ=(symTyp, posTyp); pos} -> 
            let ty: Ty.ty = lookUpType {venv; tenv; err; breakable; unassignable} symTyp posTyp "" in ty)) params in
        let res: Ty.ty = 
          (match result with
          | Some (sym_result,pos_result) -> lookUpType {venv; tenv; err; breakable; unassignable} sym_result pos_result ""
          | None -> Ty.VOID) in
        S.enter (newVenv, name, E.FunEntry {formals; result=res}))
    ) venv fundecl_list in
    let newFundecl_list: TA.fundecldata list = List.fold_left (fun newFundecl_list fdecl -> (match fdecl with
      | A.Fdecl {name; params; result; body; pos} -> 
        let venv'' = (
          List.fold_left (fun newVenv p -> match p with
            | A.Field {name; escape; typ=(symTy, posTy); pos} -> 
              let t_field = lookUpType {venv=venv';tenv;err;breakable=false; unassignable} symTy posTy "newFundecl_list fields" in
              S.enter (newVenv, name, E.VarEntry t_field)
          ) venv' params
        ) in
        let e_body, t_body = exp_ty (
          transExp {venv=venv''; tenv; err; breakable=false; unassignable} body
        ) in
        let newArgs: TA.argdata list = List.map (fun p -> (match p with
        | A.Field {name; escape; typ=(symTy, posTy); pos} ->
          let t_field = lookUpType {venv=venv';tenv;err;breakable; unassignable} symTy posTy "newArgs fields" in
          TA.Arg {name; escape; ty=t_field; pos})
        ) params in
        let newResult: Ty.ty = (match result with
          | Some (sym, pos) -> 
            lookUpType {venv=venv';tenv;err;breakable; unassignable} sym pos "newResult"
          | None -> Ty.VOID
        ) in
        let newFdecl = (
          TA.Fdecl {name; args=newArgs; result=newResult; body=e_body; pos}
        ) in
        if isSubtype {venv; tenv; err; breakable; unassignable} t_body newResult "newFundecl_list"
        then newFdecl::newFundecl_list
        else (Err.error err pos "Function output type doesn't match the declared result type"; newFundecl_list))
    ) [] fundecl_list in
    let newFunctiondeclNameList: S.symbol list = getListNames_fromFundeclList fundecl_list in 
    (if containsDuplicates newFunctiondeclNameList
    then Err.error err Lexing.dummy_pos "Function output type doesn't match the declared result type"
    ; venv',tenv, TA.FunctionDec (List.rev newFundecl_list))

  | A.VarDec {name; escape; typ = None; init; pos} ->
    let e, eTy = exp_ty(transExp {venv; tenv; err; breakable; unassignable} init) in 
    if eTy != Ty.NIL && eTy != Ty.VOID
    then S.enter (venv, name, E.VarEntry eTy), tenv, TA.VarDec {name=name; escape=ref true; typ=eTy; init=e; pos}
    else (Err.error err pos ("The initial value cannot be nil nor void if the type is not explicitly annotated"); (venv, tenv, TA.VarDec {name=name; escape=ref true; typ=Ty.NIL; init=e; pos}))
  
  | A.VarDec {name; escape; typ = Some typ'; init; pos} ->
    let e, eTy = exp_ty(transExp {venv; tenv; err; breakable; unassignable} init) in (match typ' with
    | typeSym,pos -> 
      let t = lookUpType {venv; tenv; err; breakable; unassignable} typeSym pos "VarDec" in
      if isSubtype {venv; tenv; err; breakable; unassignable} eTy t "A.VarDec"
      then (S.enter (venv, name, E.VarEntry t), tenv, TA.VarDec {name=name; escape=ref true; typ=t; init=e; pos})
      else (Err.error err pos ("A.VarDec: Variable and experession type mismatch"); (venv, tenv, TA.VarDec {name=name; escape=ref true; typ=Ty.NIL; init=e; pos})))
  
  | A.TypeDec typedecl_list ->
    let name_list = List.map (fun e -> match e with | A.Tdecl {name; ty; pos} -> name) typedecl_list in
    let newTenv = List.fold_left (fun tenv' tdecl -> match tdecl with
    | A.Tdecl { name; ty; pos} -> 
      S.enter (tenv', name, Ty.NAME (name, ref None))
    ) tenv typedecl_list in
    let tenv_with_defs = List.iter (fun tdecl -> match tdecl with
    | A.Tdecl { name; ty; pos} -> 
      let a = Some (mkType ty {venv; tenv=newTenv; err; breakable; unassignable}) in 
      (match lookUpType {venv; tenv=newTenv; err; breakable; unassignable} name pos "" with
      | Ty.NAME (sym, ty_option_ref) -> ty_option_ref := a
      | Ty.NIL -> Err.error err Lexing.dummy_pos "A type cannot be declared as type nil"
      | Ty.VOID -> Err.error err Lexing.dummy_pos "A type cannot be declared as type void"
      | _ -> print_string ""
      )) typedecl_list in
    
    let new_typedecl_list = List.map (fun tdecl -> match tdecl with
    | A.Tdecl { name; ty; pos} -> 
      let newTy = lookUpType {venv; tenv=newTenv; err; breakable; unassignable} name pos "new_typedecl_list" in 
      TA.Tdecl { name; ty=newTy; pos}) typedecl_list in 
    
    if not (containsDuplicates name_list) && (eachRecordHasUniqueFieldNames typedecl_list)
    then (if nocycles {venv; tenv=newTenv; err; breakable; unassignable} name_list
      then venv, newTenv, TA.TypeDec new_typedecl_list
      else (Err.error err Lexing.dummy_pos ("There is a cycle!!!"); venv, tenv, TA.TypeDec new_typedecl_list))
    else (Err.error err Lexing.dummy_pos ("either the list of types contains duplicate names or a record contains duplicate names!!!"); venv, tenv, TA.TypeDec new_typedecl_list)

and containsDuplicates name_list = List.exists (fun n1 -> 
    let list = List.find_all (fun n2 -> n1 = n2) name_list in
    (List.length list) > 1
  ) name_list 

and eachRecordHasUniqueFieldNames typedecl_list = List.for_all (
  fun tdecl -> match tdecl with 
  | A.Tdecl { name; ty=A.RecordTy fielddata_list; pos } -> 
    let field_names = List.map (fun fielddata -> match fielddata with
      | A.Field { name; escape; typ; pos } -> name
    ) fielddata_list in
    not (containsDuplicates field_names)
  | _ -> true
) typedecl_list



and printType ty = match ty with
      | Ty.INT -> print_string "int"
      | Ty.STRING -> print_string "string"
      | Ty.ARRAY (arrTy, unique) -> 
        (
          print_string "array("; 
          printType arrTy; 
          print_string ")"
        )
      | Ty.RECORD (sym_ty_list, unique) -> 
        (
          print_string "record(";
          List.iter (fun (sym', ty') -> (print_string (S.name sym'); print_string ": "; printType ty'; print_string " | " )) sym_ty_list;
          print_string ")";
        )
      | Ty.NAME (sym, tyOptionRef) -> 
        (
          print_string "name("; 
          print_string (S.name sym);
          print_string ")";
        )
      | Ty.NIL -> print_string "NIL"
      | Ty.VOID -> print_string "VOID"
      | Ty.ERROR -> print_string "ERROR"

and getListNames_fromFundeclList fundecl_list : S.symbol list = 
  List.map (fun fdecl -> match fdecl with
    | A.Fdecl { name; _} -> name) fundecl_list
and mkType name_ty {venv; tenv; err; breakable; unassignable} = match name_ty with
  | A.NameTy (sym, pos) -> lookUpType {venv; tenv; err; breakable; unassignable} sym Lexing.dummy_pos "mkType->NameTy"
  | A.ArrayTy (sym, pos) -> Ty.ARRAY (lookUpType {venv; tenv; err; breakable; unassignable} sym pos "mkType->ArrayTy", Ty.mkUnique())
  | A.RecordTy fielddata_list -> 
    let sym_ty_list = List.map (fun fielddata -> match fielddata with
    | A.Field {name; escape; typ; pos} -> (match typ with
      | ty_sym,pos ->
        (name, lookUpType {venv; tenv; err; breakable; unassignable} ty_sym Lexing.dummy_pos "mkType->RecordTy"))) fielddata_list in 
    Ty.RECORD (sym_ty_list, Ty.mkUnique())
      
and isSubtype context subtype parenttype calledFrom = (match subtype,parenttype with
        | Ty.INT, Ty.INT -> true
        | Ty.STRING, Ty.STRING -> true
        | Ty.ARRAY (t1, u1), Ty.ARRAY (t2, u2) -> u1 = u2
        | Ty.RECORD (l1, u1), Ty.RECORD (l2, u2) -> u1 = u2
        | Ty.NAME (s1, _), Ty.NAME (s2, _) -> s1 = s2 || isSubtype context (actualTy context subtype) parenttype calledFrom
        | Ty.NAME (s1, _), _ -> isSubtype context (actualTy context subtype) parenttype calledFrom
        | _, Ty.NAME (s2, _) -> isSubtype context subtype (actualTy context parenttype) calledFrom
        | Ty.NIL, Ty.RECORD (l, u) -> true
        | Ty.RECORD (l, u), Ty.NIL -> true
        | Ty.VOID, Ty.VOID -> true
        | Ty.NIL, Ty.NIL -> true
        | _ -> ((*print_string "\n\nisSubType called from: ";print_string calledFrom;print_string "\nsubtype: ";printType subtype; print_string "\nparenttype: ";printType parenttype; print_newline();*)false))
      
and lookUpType {venv; tenv; err; breakable; unassignable} sym pos debugger =
  match S.look (tenv,sym) with 
  | None -> 
    (
      print_newline();  
      print_newline();
      print_string debugger;
      print_newline();
      Err.error err pos (EFmt.errorTypeDoesNotExist sym); Ty.ERROR
    ) 
  | Some ty -> ty


and tenvContainsType tenv sym = match S.look (tenv, sym) with
  | None -> false
  | Some _ -> true

and tenvContainsTypes tenv symbols = List.for_all (tenvContainsType tenv) symbols

    (* NAME of Symbol.symbol * ty option ref *)
and actualTy {venv; tenv; err; breakable; unassignable} t: Ty.ty = match t with 
  |Ty.NAME (_,r) -> (match !r with 
    | None -> (Err.error err Lexing.dummy_pos ("The name-type is not defined"); Ty.ERROR)
    | Some i -> actualTy {venv; tenv; err; breakable; unassignable} i )
  | _-> t

and doesExpretionsMatchTypes context sym_ty_list sym_exp_list = 
  let expressionsMatchTypes, sym_exp_list = doesExpretionsMatchTypes_rec context sym_ty_list sym_exp_list [] in
  expressionsMatchTypes, List.rev sym_exp_list

and doesExpretionsMatchTypes_rec context sym_ty_list sym_exp_list new_sym_exp_list = match sym_exp_list with
  | [] -> true, new_sym_exp_list
  | _ -> (match List.hd sym_exp_list with 
    | sym,exp -> 
      let e_exp, t_exp = exp_ty(transExp context exp) in
      let fieldTy = returnSymbolType context sym_ty_list sym in
      if isSubtype context t_exp fieldTy "doesExpretionsMatchTypes_rec"
      then doesExpretionsMatchTypes_rec context sym_ty_list (List.tl sym_exp_list) ((sym,e_exp) :: new_sym_exp_list)
      else 
        (
        print_string "\nfieldTy: ";printType fieldTy;
        print_string "\ninit type: ";printType t_exp;print_newline();
        false, new_sym_exp_list))
  
and returnSymbolType {venv; tenv; err; breakable; unassignable} sym_ty_list sym = match sym_ty_list with
  | [] -> (Err.error err Lexing.dummy_pos ("The symbol '"^(S.name sym)^"' is not in this list of symbols!");Ty.ERROR)
  | _ -> (match List.hd sym_ty_list with s, t -> 
    if s = sym 
    then t
    else returnSymbolType {venv; tenv; err; breakable; unassignable} (List.tl sym_ty_list) sym)
  
and nocycles {venv; tenv; err; breakable; unassignable} newTypeSym_list = 
  List.for_all (fun ty_sym -> let ty = lookUpType {venv; tenv; err; breakable; unassignable} ty_sym Lexing.dummy_pos "nocycles" in nocycles_from {venv; tenv; err; breakable; unassignable} ty []) newTypeSym_list

and nocycles_from {venv; tenv; err; breakable; unassignable} ty previouslyEncountered =
  match ty with
  | INT -> true
  | STRING -> true
  | RECORD (sym_ty_list, _) ->
    List.for_all (fun (_, rec_field_t) -> (match rec_field_t with
    | NAME (sym, _) -> tenvContainsType tenv sym
    | _ -> nocycles_from {venv; tenv; err; breakable; unassignable} rec_field_t [])) sym_ty_list
  | ARRAY (arr_ty, _) ->
    (match arr_ty with
    | NAME (sym, _) -> tenvContainsType tenv sym
    | _ -> nocycles_from {venv; tenv; err; breakable; unassignable} arr_ty [])
  | NAME (sym, ty_option_ref) -> 
    if List.exists (fun prevSym -> sym = prevSym) previouslyEncountered
    then false
    else (match ty_option_ref with
    | { contents = Some ty } -> nocycles_from {venv; tenv; err; breakable; unassignable} ty (sym :: previouslyEncountered)
    | _ -> (Err.error err Lexing.dummy_pos ("Each type must be defined before cycle-check"); false))
  | VOID | NIL | ERROR -> (Err.error err Lexing.dummy_pos ("Fields cannot be declared as type VOID nor NIL or there have been a type-error"); false)
(*check that there is no cycles that dosn't pass through a reccord or array*)


and typeIsNil exp = let _,t=exp_ty exp in match t with
| Ty.NIL -> true
| _ -> false

  (* no need to change the implementation of the top level function *)

let transProg (e : A.exp) : TA.exp * Err.errenv =
  let err = Err.initial_env in
  let res = transExp {venv= E.baseVenv; tenv = E.baseTenv; err; breakable=false; unassignable= S.empty} e in 
  if typeIsNil res
  then (Err.error err Lexing.dummy_pos (EFmt.errorInferNilType); res, err)
  else res, err
  