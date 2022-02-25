(**************************************************************************)
(* AU compilation. - DONE                                                       *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)

open Tigercommon 
open Tigerhoist

module H = Habsyn
module Ty = Types
module S = Symbol
module B = Cfgbuilder

module SymbolMap = Map.Make 
    (struct type t = S.symbol let compare = compare end)
module UniqueMap = Map.Make 
    (struct type t = Ty.unique let compare = compare end)

type unique_env = Ll.uid UniqueMap.t  
type fdecl_summary =
  { parent_opt: Ll.gid option 
  ; locals_uid: Ll.uid 
  ; locals_tid: Ll.tid 
  ; offset_of_symbol: S.symbol -> int 
  }

let fresh = 
  let open Freshsymbols in 
  let env = empty in 
  gensym env
 
let void_operand = Ll.Id (S.symbol "void_operand")
let ptr_i8 = Ll.Ptr I8 
let (<$>) f g x = f (g x)
let id = Fun.id
let ($>) b1 b2 = b2 <$> b1 (* buildlet composition *)
let (@>) (b,op) k = b $> k op
let ty_of_exp (H.Exp{ty;_}) = ty 
let ty_of_var (H.Var{ty;_}) = ty
let ty_of_arg (H.Arg{ty;_}) = ty
let name_of_arg (H.Arg{name;_}) = name 
  
let default_sl_name = S.symbol "$sl" 
let locals_type_name name = (S.symbol @@ "$locals_" ^ (S.name name))
let ty_dec_name name = (S.symbol @@ "t_$" ^ (S.name name)) 
  
(* add instruction with fresh symbol *)
let aiwf (s : string) (i : Ll.insn) : B.buildlet * Ll.operand = 
  let sym = fresh s in 
  B.add_insn (Some sym, i), Ll.Id sym 

let aawf (s : string) (t : Ll.ty) : B.buildlet * Ll.operand =
  let sym = fresh s in
  B.add_alloca (sym, t), Ll.Id sym

let ai (i : Ll.insn) : B.buildlet * Ll.operand =
  B.add_insn (None, i), void_operand

let ( <$> ) f g x = f (g x) (* function application *)
let ( $> ) b1 b2 = b2 <$> b1 (* convenient for sequencing buildlets *)
let ty_of_exp (H.Exp {ty; _}) = ty (* type extractors *)
let ptr_i8 = Ll.Ptr I8 (* generic pointer type *)

type summary_env = fdecl_summary SymbolMap.t
exception NotImplemented
exception CodeGenerationBug 

let rec actualTy t : Ty.ty = match t with 
| Ty.NAME (_,r) -> (match !r with 
  | None -> Ty.ERROR 
  | Some i -> actualTy i)
|_ -> t

let getOption (optionVal : 'a option) : 'a = match optionVal with
| Some v -> v
| None -> raise CodeGenerationBug
let get_1_2 (a,_) = a
let get_2_2 (_,a) = a
let get_1_3 (a,_,_) = a
let get_2_3 (_,a,_) = a
let get_3_3 (_,_,a) = a

let listMap3_of_1 (f : 'a1 -> 'b1 * 'c1 * 'd1) (l : 'a1 list) : 'b1 list * 'c1 list * 'd1 list =
  let appendThree ((elemA : 'a2), (elemB : 'b2), (elemC : 'c2)) ((lA : 'a2 list), (lB : 'b2 list), (lC : 'c2 list)) =
    (elemA :: lA), (elemB :: lB), (elemC :: lC) in
  let rec listMapRec (f : 'a3 -> 'b3 * 'c3 * 'd3) (l : 'a3 list) : 'b3 list * 'c3 list * 'd3 list =
    if List.length l < 1
    then [], [], []
    else appendThree (f (List.hd l)) (listMapRec f (List.tl l))
  in 
    listMapRec f l


type context 
  = { break_lbl: Ll.lbl option     
    ; summary: fdecl_summary
    ; uenv: unique_env
    ; senv: summary_env (* Look up parent find fdecl summary - then as before *)
    ; gdecls: (Ll.gid * Ll.gdecl) list ref
    ; result: Ty.ty
    }

let rec getRecordContent (ty : Ty.ty) : (S.symbol * Ty.ty) list * Ty.unique = match ty with
| Ty.RECORD (symTyList, unique) -> symTyList, unique
| Ty.NAME (_, tyOptionRef) -> (match !tyOptionRef with
  | Some t -> getRecordContent t
  | None -> raise CodeGenerationBug)
| _ -> raise CodeGenerationBug

let getRecordUnique (ty : Ty.ty) : Ty.unique = 
  get_2_2 (getRecordContent ty)

let getRecordSymTyList (ty : Ty.ty) : (S.symbol * Ty.ty) list = 
  get_1_2 (getRecordContent ty)

let recordSize (fieldTypes : Ll.ty list) : B.buildlet * Ll.operand =
  let rec recordSizeRec ((fieldTypes : Ll.ty list)) (op_prev_aggregation : Ll.operand) : (B.buildlet * Ll.operand) = 
    if List.length fieldTypes = 0
    then
      B.id_buildlet, op_prev_aggregation
    else
      let ty : Ll.ty = List.hd fieldTypes in 
      let b_tySizePtr, o_tySizePtr = aiwf "ty_sizePtr" (Gep (ty, Null, [Const 1])) in
      let b_tySizeInt, o_tySizeInt = aiwf "ty_sizeInt" (Ptrtoint (ty, o_tySizePtr, I64)) in
      let b_aggregation, o_aggregation = aiwf "size_aggregation" (Binop (Add, I64, o_tySizeInt, op_prev_aggregation)) in
      let b_theRest, o_theRest = recordSizeRec (List.tl fieldTypes) o_aggregation in 
      B.seq_buildlets [b_tySizePtr; b_tySizeInt; b_aggregation; b_theRest], o_theRest
  in
    recordSizeRec fieldTypes (Const 0)

let addNilDereferenceCheck (o_varRec : Ll.operand) : B.buildlet =
    let then_label = fresh "then" in
    let merge_label = fresh "merge" in
    let b_icmp, o_icmp = aiwf "i1" (Ll.Icmp (Eq, ptr_i8, o_varRec, Null)) in
    b_icmp $> B.term_block (Cbr (o_icmp, then_label, merge_label)) $> B.start_block then_label $> 
    get_1_2 (ai (Ll.Call (I64, Gid (S.symbol "recFieldError"), []))) $> B.term_block (Br merge_label) $>
    B.start_block merge_label

let checkIndexTooGreat o_arrSize o_exp =
  let then_label = fresh "then" in
  let merge_label = fresh "merge" in
  let b_icmp, o_icmp = aiwf "i1" (Ll.Icmp (Ll.Sge, I64, o_exp, o_arrSize)) in
  b_icmp $> B.term_block (Cbr (o_icmp, then_label, merge_label)) $> B.start_block then_label $> 
  get_1_2 (ai (Ll.Call (I64, Gid (S.symbol "arrInxError"), [(I64,o_exp)]))) $> B.term_block (Br merge_label) $>
  B.start_block merge_label

let checkIndexTooSmall o_exp =
  let then_label = fresh "then" in
  let merge_label = fresh "merge" in
  let b_icmp, o_icmp = aiwf "i1" (Ll.Icmp (Ll.Slt, I64, o_exp, Ll.Const 0)) in
  b_icmp $> B.term_block (Cbr (o_icmp, then_label, merge_label)) $> B.start_block then_label $> 
  get_1_2 (ai (Ll.Call (I64, Gid (S.symbol "arrInxError"), [(I64,o_exp)]))) $> B.term_block (Br merge_label) $>
  B.start_block merge_label

let addIndexOutOfBoundsCheck arrllty o_var o_exp = 
  let b_bitcastToI64, o_bitcastToI64 = aiwf "castToI64" (Bitcast (arrllty, o_var, Ptr(I64))) in
  let b_gep, o_gep = aiwf "gep" (Ll.Gep (I64, o_bitcastToI64, [Ll.Const (-1)])) in
  let b_load, o_load = aiwf "load" (Ll.Load (I64, o_gep)) in
  get_1_2 (ai (Ll.Comment "beginArrayOutOfBoundsCheck")) $> b_bitcastToI64 $> b_gep $> b_load $> 
  (checkIndexTooGreat o_load o_exp) $> (checkIndexTooSmall o_exp) $> get_1_2 (ai (Ll.Comment "endArrayOutOfBoundsCheck"))


let matchStringCnd (oper : Oper.oper) : Ll.operand = Gid (S.symbol (match oper with
| EqOp -> "stringEqual"
| NeqOp -> "stringNotEq"
| LtOp -> "stringLess"
| LeOp -> "stringLessEq"
| GtOp -> "stringGreater"
| GeOp -> "stringGreaterEq"
| _ -> raise CodeGenerationBug))

let matchCnd (oper : Oper.oper) : Ll.cnd = match oper with
| EqOp -> Eq 
| NeqOp -> Ne
| LtOp -> Slt
| LeOp -> Sle
| GtOp -> Sgt
| GeOp -> Sge
| _ -> raise CodeGenerationBug

let matchBop (oper : Oper.oper) : Ll.bop = match oper with
| PlusOp -> Add 
| MinusOp -> Sub
| TimesOp -> Mul        
| DivideOp -> SDiv
| ExponentOp | _ -> raise CodeGenerationBug

let rec llty_of_ty (ty : Ty.ty) : Ll.ty = match ty with
| Ty.INT -> I64
| Ty.STRING | Ty.ARRAY(_,_) | Ty.NIL | Ty.RECORD (_,_)-> Ptr I8
| Ty.VOID -> Void
|Ty.NAME (_, {contents = (Some t)}) -> llty_of_ty t
|_-> raise CodeGenerationBug

(* Obs: this is a rather tricky piece of code; 2019-10-12 *)
let cg_tydecl (tenv : unique_env ref) (H.Tdecl{name; ty ; _}) : (S.symbol * Ll.ty) option = 
  match actualTy ty with 
  Ty.INT -> Some (name, I64)
  |Ty.STRING | Ty.ARRAY(_,_) | Ty.NIL -> Some(name, Ptr I8)
  |Ty.NAME(sym,_) -> Some (name, Namedt sym)
  |Ty.RECORD(symTyList,uniq) -> 
   (match UniqueMap.find_opt uniq !tenv with 
   | Some tid -> Some(name, Namedt tid) 
   | None ->
    tenv := UniqueMap.add uniq name !tenv;
    let recordType = Ll.Struct (List.map (fun (_,t)->llty_of_ty t) symTyList) in 
    Some (name, recordType)
    )
  | _ -> raise CodeGenerationBug 

(* --- monadic interface;) ----------------------------- *)

(* Notes on the monadic interface:

1) Monadic interface is not necessary at all, and one could just 
   program with buildlets as before; it's just a little bit more 
   concise, but one _really_ needs to know what they are doing.

2) Some useful info on the OCmal let* notation here
   http://jobjo.github.io/2019/04/24/ocaml-has-some-new-shiny-syntax.html 

3) Observe that the new OCaml notation conflicts with JaneStreet 
   pre-processors, so we don't have any pre-processing in this library.
*)

type 'a m = B.buildlet * 'a
let bind ((builder, op):'a m) (f:'a -> 'b m):'b m =
  let ( builder', op') = f op in 
  (builder $> builder', op')
let return x = (B.id_buildlet, x)  
let (let*) = bind
(* --- end of monadic interface ------------------------ *)

let unit b = (b, ())    
let build_store t o1 o2 = B.add_insn (None, Store (t,o1,o2))
let gep_0 ty op i = Ll.Gep (ty, op, [Const 0; Const i])

let rec cgExp (ctxt : context) (Exp{exp_base;pos=_;ty=tyTopExp}:H.exp) : B.buildlet * Ll.operand = 
  let cgE = cgExp ctxt in
  let open Ll in
  match exp_base with 
  | H.IntExp n -> (B.id_buildlet, Const n)

  | H.StringExp s ->
    let str_uid = fresh "str" in
    let str_type = Struct [I64; Array (String.length s,I8)] in
    let gdecl_list : gdecl list = [(I64, GInt (String.length s));(Array (String.length s,I8), GString s)] in
    let ginit_struct = GStruct gdecl_list in
    ctxt.gdecls := (str_uid, (str_type, ginit_struct)) :: !(ctxt.gdecls);
    let b_ptr, o_ptr = aiwf "str_ptr" (Bitcast (Ptr (str_type), Gid str_uid, ptr_i8)) in
    (b_ptr, o_ptr)

  | H.OpExp {left; oper; right} ->
    let b_rightOp, op_right = cgE right in
    let b_leftOp, op_left = cgE left in
    (match actualTy (ty_of_exp left) with
    | INT -> (match oper with
      | EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp -> (*comprison*)
        let cnd = matchCnd oper in
        let b_icmp, o_icmp = aiwf "res_i1" (Icmp (cnd, I64, op_left, op_right)) in
        let b_zext, o_zext = aiwf "res_i64" (Zext (I1, o_icmp, I64)) in
        b_leftOp $> b_rightOp $> b_icmp $> b_zext, o_zext
      | PlusOp | MinusOp | TimesOp -> (*arithmetic*)
        let bop = matchBop oper in
        let b_binop, o_binop = aiwf "res" (Binop (bop, I64, op_left, op_right)) in
        b_leftOp $> b_rightOp $> b_binop, o_binop
      | ExponentOp -> 
        let b_call, o_call = aiwf "res" (Call (I64, Gid (S.symbol "exponent"), [(I64, op_left);(I64, op_right)])) in
        b_leftOp $> b_rightOp $> b_call, o_call
      | DivideOp ->
        let bop = SDiv in
        let o_then = fresh "then" in
        let o_merge = fresh "merge" in
        let b_compare, o_compare = aiwf "compare" (Icmp (Eq, I64, op_right, Const 0)) in
        let b_callDivisionByZero, _ = ai (Call (I64, Gid (S.symbol "divisionByZero"), [])) in
        let b_insn, o_res = aiwf "res" (Binop (bop, I64, op_left, op_right)) in
        (b_leftOp $> b_rightOp $> b_compare $> B.term_block (Cbr (o_compare, o_then, o_merge)) $>
        B.start_block o_then $> b_callDivisionByZero $> B.term_block (Br o_merge) $>
        B.start_block o_merge $> b_insn, o_res))
    | STRING ->
      let b_call, o_call = aiwf "res" (Call (I64, matchStringCnd oper, [(ptr_i8, op_left);(ptr_i8, op_right)])) in
      b_leftOp $> b_rightOp $> b_call, o_call
    | _ ->
      let cnd = (match oper with
      | EqOp -> Eq 
      | NeqOp -> Ne
      | _ -> raise CodeGenerationBug) in 
      let llty = llty_of_ty (ty_of_exp left) in
      let b_icmp, o_icmp = aiwf "res_i1" (Icmp (cnd, llty, op_left, op_right)) in
      let b_zext, o_zext = aiwf "res_i64" (Zext (I1, o_icmp, I64)) in
      b_leftOp $> b_rightOp $> b_icmp $> b_zext, o_zext)
    
  | H.CallExp {func; lvl_diff; args} ->
      let args_build_list = ref [] in
      let argLLVM = List.map (fun e -> let b,o = cgE e in let ty = llty_of_ty (ty_of_exp e) in args_build_list := List.concat [!args_build_list; [b]];(ty, o)) args in
      let argLLVM_with_dummy = List.concat [[ptr_i8, Null]; argLLVM] in
      let args_buildlet = B.seq_buildlets !args_build_list in
      let b_call, o_call = (match S.name func with
      | "print" -> ai (Call (Void, Gid func, argLLVM_with_dummy))
      | "flush" -> ai (Call (Void, Gid func, argLLVM_with_dummy))
      | "getChar" -> aiwf "res" (Call (ptr_i8, Gid func, argLLVM_with_dummy))
      | "ord" -> aiwf "res" (Call (I64, Gid func, argLLVM_with_dummy))
      | "chr" -> aiwf "res" (Call (ptr_i8, Gid func, argLLVM_with_dummy))
      | "size" -> aiwf "res" (Call (I64, Gid func, argLLVM_with_dummy))
      | "substring" -> aiwf "res" (Call (ptr_i8, Gid func, argLLVM_with_dummy))
      | "concat" -> aiwf "res" (Call (ptr_i8, Gid func, argLLVM_with_dummy))
      | "not" -> aiwf "res" (Call (I64, Gid func, argLLVM_with_dummy))
      | "tigerexit" -> ai (Call (Void, Gid func, argLLVM_with_dummy))
      | _ -> 
        let b_localsLevelDiff, o_localsLevelDiff, summaryLevelDiff = getSummary ctxt lvl_diff in
        let argLLVM_with_locals = List.concat [[Ptr(Namedt summaryLevelDiff.locals_tid), o_localsLevelDiff]; argLLVM] in
        let b_customCall, o_custom_Call = 
          if tyTopExp = Ty.VOID
          then ai (Call (llty_of_ty tyTopExp, Gid func, argLLVM_with_locals))
          else aiwf "res" (Call (llty_of_ty tyTopExp, Gid func, argLLVM_with_locals)) in
        b_localsLevelDiff $> b_customCall, o_custom_Call) in
      args_buildlet $> b_call, o_call

  | H.SeqExp exps -> 
    let op_res_ptr : operand ref = ref Null in 
    let buildlets_list = List.map (fun e -> let build, op = cgE e in op_res_ptr := op; build) exps in
    (B.seq_buildlets buildlets_list, !op_res_ptr)

  | H.IfExp {test; thn; els=None} ->
    let build_test,op_test_i64 = cgE test in
    let b_icmp, o_icmp = aiwf "res_i1" (Icmp (Ne, I64, op_test_i64, Const 0)) in
    let build_thn,_ = cgE thn in
    let thn_label = fresh "thn" in
    let merge_label = fresh "merge" in
    let thn_block = B.start_block thn_label $> build_thn $> B.term_block (Br merge_label) in
    let merge_block = B.start_block merge_label in
    build_test $> b_icmp $> B.term_block (Cbr (o_icmp, thn_label, merge_label)) $> thn_block $> merge_block, void_operand

  | H.IfExp {test; thn; els=Some e} -> 
    let build_test,op_test_i64 = cgE test in
    let b_icmp, o_icmp = aiwf "i64_to_i1" (Icmp (Ne, I64, op_test_i64, Const 0)) in
    let build_thn,op_thn = cgE thn in
    let build_els,op_els = cgE e in
    let llty = llty_of_ty (ty_of_exp thn) in
    let thn_label = fresh "thn" in
    let els_label = fresh "els" in
    let merge_label = fresh "merge" in
    if llty == Void 
    then
      build_test $> b_icmp $> B.term_block (Cbr (o_icmp, thn_label, els_label)) $>
      B.start_block thn_label $> build_thn $> B.term_block (Br merge_label) $>
      B.start_block els_label $> build_els $> B.term_block (Br merge_label) $>
      B.start_block merge_label, void_operand
    else
      let b_alloc, o_alloc = aawf "res" llty in
      let store_thn_res = build_store llty op_thn o_alloc in
      let store_els_res = build_store llty op_els o_alloc in
      let b_load, o_load = aiwf "load" (Load (llty, o_alloc)) in
      b_alloc $> build_test $> b_icmp $> B.term_block (Cbr (o_icmp, thn_label, els_label)) $> 
      B.start_block thn_label $> build_thn $> store_thn_res $> B.term_block (Br merge_label) $>
      B.start_block els_label $> build_els $> store_els_res $> B.term_block (Br merge_label) $>
      B.start_block merge_label $> b_load, o_load

  | H.WhileExp {test; body} ->
    let test_label = fresh "test" in 
    let body_label = fresh "body" in 
    let end_label = fresh "end" in
    let build_test, op_test_i64 = cgE test in
    let b_icmp, o_icmp = aiwf "i64_to_i1" (Icmp (Ne, I64, op_test_i64, Const 0)) in
    let build_body, _ = cgExp {ctxt with break_lbl = Some end_label} body in
    B.term_block (Br test_label) $> 
    B.start_block test_label $> build_test $> b_icmp $> B.term_block (Cbr (o_icmp, body_label, end_label)) $>
    B.start_block body_label $> build_body $> B.term_block (Br test_label) $>
    B.start_block end_label, void_operand
    
  | H.LetExp {vardecl= VarDec {name; typ; init; _}; body; _} ->
    let b_init, o_init = cgE init in 
    let b_gep, o_gep = aiwf "ptr" (Gep ((Namedt ctxt.summary.locals_tid), (Id ctxt.summary.locals_uid), [Const 0; Const (ctxt.summary.offset_of_symbol name)])) in
    let b_store = build_store (llty_of_ty typ) o_init o_gep in
    let b_body, o_body = cgE body in
    b_init $> b_gep $> b_store $> b_body, o_body

  | H.VarExp v -> cgVarLoad ctxt v

  | H.AssignExp {var; exp} -> 
    let b_exp, o_exp = cgE exp in
    let b_varPtr, o_varPtr = cgVarPtr ctxt var in
    let b_store = build_store (llty_of_ty (ty_of_var var)) o_exp o_varPtr in
    b_exp $> b_varPtr $> b_store, o_exp

  | H.BreakExp -> (match ctxt.break_lbl with 
    | None -> raise CodeGenerationBug
    | Some lbl -> B.term_block(Br lbl) $> B.start_block (fresh ""), void_operand)

  | H.NilExp -> id, Null

  | H.RecordExp {fields} ->
    let b_initValues, lltys, ty_opList = listMap3_of_1 (fun (_, e) -> 
      let b, o = cgE e in
      let ty = llty_of_ty (ty_of_exp e) in
      b, ty, (ty, o)
    ) fields in
    let b_recordSize, o_recordSize = recordSize lltys in
    let b_recordPtr, o_recordPtr = aiwf "recordPtr" (Call (ptr_i8, Gid (S.symbol "allocRecord"), [(I64, o_recordSize)])) in
    let llty_record : ty = Struct lltys in
    let b_castRecordPtr, o_castRecordPtr = aiwf "castRecordPtr" (Bitcast (ptr_i8, o_recordPtr, Ptr(llty_record))) in
    let b_gep_and_store_fields : B.buildlet = B.seq_buildlets (List.mapi (fun (i: int) ((ty_field: ty), (o_field: operand))-> 
      let b_gep, o_gep = aiwf "gep" (Gep (llty_record, o_castRecordPtr, [Const 0; Const i])) in 
      let b_store = build_store ty_field o_field o_gep in 
      B.seq_buildlets [b_gep; b_store]
      ) ty_opList) in
    (B.seq_buildlets b_initValues) $> b_recordSize $> b_recordPtr $> b_castRecordPtr $> b_gep_and_store_fields, o_recordPtr

  | H.ArrayExp {size; init} ->
    let build_size, op_size = cgE size  in
    let build_init, op_init = cgE init in
    let b_alloc, o_alloc = aiwf "alloc" (Alloca (llty_of_ty (ty_of_exp init))) in
    let b_store = build_store (llty_of_ty (ty_of_exp init)) op_init o_alloc in
    let b_castAlloc, o_castAlloc = aiwf "castedAlloc" (Bitcast (Ptr(llty_of_ty (ty_of_exp init)), o_alloc, ptr_i8)) in
    let b_elemSize, o_elemSize = aiwf "elem_size" (Gep ((llty_of_ty (ty_of_exp init)), Null, [Const 1])) in
    let b_castElemSize, o_castElemSize = aiwf "casted_elem_size" (Ptrtoint ((llty_of_ty (ty_of_exp init)), o_elemSize, I64)) in
    let argLLVM = [(I64, op_size); (I64, o_castElemSize); (ptr_i8, o_castAlloc)] in
    let b_call, o_call = aiwf "arr_ptr" (Call (ptr_i8, Gid (S.symbol "initArray"), argLLVM)) in
    build_size $> build_init $> b_alloc $> b_store $> b_castAlloc $> b_elemSize $> b_castElemSize $> b_call, o_call

and cgVarLoad (ctxt : context) (H.Var {var_base; pos; ty}) =
  let b_ptr, o_ptr = cgVarPtr ctxt (H.Var {var_base; pos; ty}) in
  let b_load, o_load = aiwf "load" (Load (llty_of_ty ty, o_ptr)) in
  b_ptr $> b_load, o_load

and cgVarPtr (ctxt : context) (H.Var {var_base; pos=_; ty}) =
  match var_base with
  | H.AccessVar (level_diff, varname) ->
    let b_gep, o_gep = gepVar ctxt level_diff varname in
    let b_seq = B.seq_buildlets [b_gep] in
    b_seq, o_gep

  | FieldVar (var, sym) ->
    let getIndexLlty (sym : S.symbol) (symTyList : (S.symbol * Ty.ty) list) : (int * Ll.ty) = 
      let rec getIndexLltyRec (sym : S.symbol) (symTyList : (S.symbol * Ty.ty) list) (index : int) : (int * Ll.ty) =
        if get_1_2 (List.hd symTyList) = sym
        then index, llty_of_ty (get_2_2 (List.hd symTyList))
        else getIndexLltyRec sym (List.tl symTyList) (index+1)
      in
      getIndexLltyRec sym symTyList 0
    in
    let lltyRecord = Ll.Namedt (UniqueMap.find (getRecordUnique (ty_of_var var)) ctxt.uenv) in
    let list_of_fieldsTy : (S.symbol * Ty.ty) list = getRecordSymTyList (ty_of_var var) in
    let b_varRec, o_varRec = cgVarLoad ctxt var in
    let b_check = addNilDereferenceCheck o_varRec in
    let fieldNumber, _ = getIndexLlty sym list_of_fieldsTy in
    let b_castedAddress, o_castedAddress = aiwf "castedAddress" (Bitcast (ptr_i8, o_varRec, Ptr(lltyRecord))) in
    let b_gep, o_gep = aiwf "gepFieldCgVar" (Gep (lltyRecord, o_castedAddress, [Const 0; Const fieldNumber])) in
    b_varRec $> b_check $> b_castedAddress $> b_gep, o_gep

  | SubscriptVar (var, exp) ->
    let b_exp, o_exp = cgExp ctxt exp in
    let b_var, o_var = cgVarLoad ctxt var in
    let b_check = addIndexOutOfBoundsCheck (llty_of_ty (ty_of_var var)) o_var o_exp in
    let lltyElem = llty_of_ty ty in
    let b_bitcastToElemTy, o_bitcastToElemTy = aiwf "castToElemTy" (Bitcast (llty_of_ty (ty_of_var var), o_var, Ptr(lltyElem))) in
    let b_gep, o_gep = aiwf "gepArrCgVar" (Gep (lltyElem, o_bitcastToElemTy, [o_exp])) in
    b_exp $> b_var $> b_check $> b_bitcastToElemTy $> b_gep, o_gep
  
and gepVar (ctxt : context) (level_diff : int) (varname : S.symbol) : (B.cfg_builder -> B.cfg_builder) * Ll.operand = 
  gepVarRec ctxt level_diff ctxt.summary (Ll.Id ctxt.summary.locals_uid) varname

and gepVarRec (ctxt : context) (level_diff : int) (summary_current_level : fdecl_summary) (o_loaded_locals : Ll.operand) (varname : S.symbol) : (B.cfg_builder -> B.cfg_builder) * Ll.operand = 
  if level_diff = 0
  then 
    let o_gep = fresh ("address"^(string_of_int level_diff)) in
    let b_gep = B.add_insn (Some o_gep, Gep ((Namedt summary_current_level.locals_tid), o_loaded_locals, [Const 0; Const (summary_current_level.offset_of_symbol varname)])) in
    b_gep, Id o_gep
  else 
    let o_gep = fresh "address1" in
    let b_gep = B.add_insn (Some o_gep, Gep ((Namedt summary_current_level.locals_tid), o_loaded_locals, [Const 0; Const 0])) in
    let parent_summary = (SymbolMap.find (getOption summary_current_level.parent_opt) ctxt.senv) in
    let o_load = fresh "load1" in
    let b_load = B.add_insn (Some o_load, Load (Ptr(Namedt parent_summary.locals_tid), Id o_gep)) in
    let b_theRest, o_theRest = gepVarRec ctxt (level_diff-1) parent_summary (Id o_load) varname in
    b_gep $> b_load $> b_theRest, o_theRest

and getSummary (ctxt : context) (level_diff : int) : ((B.cfg_builder -> B.cfg_builder) * Ll.operand * fdecl_summary) = 
  let rec getSummaryRec (ctxt : context) (level_diff : int) (summary_current_level : fdecl_summary) (o_loaded_locals : Ll.operand) : ((B.cfg_builder -> B.cfg_builder) * Ll.operand * fdecl_summary) =
    if level_diff = 0
    then 
      B.id_buildlet, o_loaded_locals, summary_current_level
    else 
      let o_gep = fresh "address1" in
      let b_gep = B.add_insn (Some o_gep, Gep ((Namedt summary_current_level.locals_tid), o_loaded_locals, [Const 0; Const 0])) in
      let parent_summary = (SymbolMap.find (getOption summary_current_level.parent_opt) ctxt.senv) in
      let o_load = fresh "load1" in
      let b_load = B.add_insn (Some o_load, Load (Ptr(Namedt parent_summary.locals_tid), Id o_gep)) in
      let b_theRest, o_theRest, summary = getSummaryRec ctxt (level_diff-1) parent_summary (Id o_load) in
      B.seq_buildlets [b_gep; b_load; b_theRest], o_theRest, summary
  in
    getSummaryRec ctxt level_diff ctxt.summary (Id ctxt.summary.locals_uid)


    (* --- From this point on the code requires no changes --- *)

(* Creates summary of a function declaration; relies on the alpha conversion *)
let cg_fdecl_summary senv_ref ( H.Fdecl{name; parent_opt; locals; _}) : S.symbol * Ll.ty = 
  let locals_uid = fresh "locals" in
  let locals_tid = locals_type_name name in 
  let offset_of_symbol = 
    let locals_map = default_sl_name :: (List.map fst locals) 
                     |> List.mapi (fun i x -> (x,i)) 
                     |> List.to_seq 
                     |> SymbolMap.of_seq in 
    fun sym -> SymbolMap.find sym locals_map in 
  senv_ref := SymbolMap.add name 
      {parent_opt; locals_uid; locals_tid; offset_of_symbol} !senv_ref;
  let sl_type = 
    match parent_opt with 
    | Some p -> Ll.Ptr (Namedt (p |> locals_type_name))
    | None -> Ll.Ptr I8 in  
  let locals_ty =
    Ll.Struct (sl_type:: List.map (fun (_, t) -> llty_of_ty t ) locals) in
  (locals_tid, locals_ty)

(* --- Code genartion of function bodies --- *)
let cg_fdecl senv uenv gdecls (H.Fdecl{name; args; result; body; _}) =
  (*  Function bodies are generated in 5 steps
      1. Creating the translation context
      2. Allocating the locals structure with all the variables
      3. Copying the arguments to the locals
      4. Generating the code for the function body
      5. Terminate the function

      Because we use buildlets, the order in which we take steps 2-4 does not 
      matter as long as we compose the resulting buildlets correctly in the
      end.
  *)

  let open Ll in (* locally open the Ll module; for convenience *)

  (* Extract the necessary information from the function summary environment *)
  let {parent_opt;locals_uid;locals_tid;offset_of_symbol;_} as summary = 
    SymbolMap.find name senv in

  (* Get the name of the static link
     - either from the lookup in the summary, if the function is not main
     - a dummy i8*, for the main function
  *) 
  let sl_type  = 
    match parent_opt with 
    | Some p -> Ptr (Namedt (SymbolMap.find p senv).locals_tid)
    | None -> Ptr I8 in

  (* A tuple that contains all sl-related information  *)
  let sl_info = (default_sl_name, sl_type) in 

  (* Step 1 -- this is our context *)
  let ctxt = {  summary; 
                break_lbl = None; 
                uenv;
                senv;
                gdecls;
                result              
             } in
  
  (* A buildlet for allocating the locals structure *)
  let build_alloca = B.add_alloca (locals_uid, Namedt locals_tid) in

  (* Aux list of arguments with SL added in the beginning *)
  let args' = sl_info:: List.map 
                (fun (H.Arg{name;ty;_}) -> (name,llty_of_ty ty)) args in 
  
  let copy_one_arg (name,ty) = (* A buildlet for copying one argument *)
    let (build_gep,op_gep) = aiwf "arg" 
      (gep_0 (* Use GEP to find where to store the argument *)
        (Namedt locals_tid)
        (Id locals_uid)
        (offset_of_symbol name)) in
    (* Observe how we return the composition of two buildlets *)
    build_gep $> build_store ty (Id name) op_gep in

  let copy_args = (* A buildlet that copies all of the arguments *)
        List.rev args' |> List.map copy_one_arg |> B.seq_buildlets in 

  let ret_ty, tr = match result with 
      Ty.VOID -> Void, fun _ -> Ret (Void, None)
    | t -> let llty = llty_of_ty t in 
      llty, fun op -> Ret (llty, Some op) in 

  let build_body, op = (* Get the builder for the body and the operand with 
                          the result; observe that we pass the context.  *)
    cgExp {ctxt with result=result} body in

  let build_function  (* Putting it all together *)
      = build_alloca                                          (* Step 2 *)
        $> copy_args                                          (* Step 3 *) 
        $> build_body                                         (* Step 4 *)
        $> B.term_block (tr op) in                            (* Step 5 *)

  let cfg_builder = (* Apply the buildlet; we get a cfg_builder *)
      build_function B.empty_cfg_builder in

  name,
  { fty = sl_type::List.map (llty_of_ty<$>ty_of_arg) args, ret_ty
  ; param = default_sl_name :: List.map name_of_arg args 
  ; cfg = B.get_cfg cfg_builder 
  }

let codegen_prog (H.Program{tdecls; fdecls})  : Ll.prog = 
  let tenv = ref UniqueMap.empty in
  let senv = ref SymbolMap.empty in 
  let gdecls = ref [] in 
  let tdecls1 = List.filter_map (cg_tydecl tenv) tdecls in 
  let tdecls2 = List.map (cg_fdecl_summary senv) fdecls in 
  let fdecls = List.map (cg_fdecl !senv !tenv gdecls) fdecls in 
  let tdecls = tdecls1 @ tdecls2 in 
  let gdecls = !gdecls in let open Ll in
  {tdecls; gdecls; fdecls}

let runtime_fns = 
  let fns =
    [ "i8* @allocRecord(i64)"   (* runtime functions *)
    ; "i8* @initArray (i64, i64, i8*)"
    ; "i64 @arrInxError (i64)"
    ; "i64 @recFieldError()"
    ; "i64 @divisionByZero()"
    ; "i64 @stringEqual (i8*, i8*)"
    ; "i64 @stringNotEq (i8*, i8*)"
    ; "i64 @stringLess (i8*, i8*)"
    ; "i64 @stringLessEq (i8*, i8*)"
    ; "i64 @stringGreater (i8*, i8*)"
    ; "i64 @stringGreaterEq (i8*, i8*)"
    ; "i64 @exponent(i64, i64)"

    (* user visible functions; note SL argument *)

    ; "void @print      (i8*, i8*)"   
    ; "void @flush      (i8*)"
    ; "i8*  @getChar    (i8*)"
    ; "i64  @ord        (i8*, i8*)"
    ; "i8*  @chr        (i8*, i64)"
    ; "i64  @size       (i8*, i8*)"
    ; "i8*  @substring  (i8*, i8*, i64, i64)"
    ; "i8*  @concat     (i8*, i8*, i8*)"
    ; "i64  @not        (i8*, i64)"
    ; "void @tigerexit  (i8*, i64)"
    ] in 
  let mkDeclare s = "declare " ^ s ^ "\n"
  in String.concat "" (List.map mkDeclare fns)

let ll_target_triple:string = 
  let ic = Unix.open_process_in "uname" in
  let uname = input_line ic in
  let () = close_in ic in
  match uname with 
    "Darwin" -> "target triple = \"x86_64-apple-macosx10.15.0\""
  | "Linux"  -> "target triple = \"x86_64-pc-linux-gnu\""
  | _ -> ""
