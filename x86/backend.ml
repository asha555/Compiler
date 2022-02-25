(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)

(* ll ir compilation -------------------------------------------------------- *)
open Tigercommon 
module S = Symbol
open X86
open Ll
open Asm

exception BackendFatal (* Impossible Cases *)

type os = Linux | Darwin
let os =  
  let ic = Unix.open_process_in "uname" in
  let uname = input_line ic in
  let () = close_in ic in
  match uname with 
  | "Linux" -> Linux 
  | "Darwin" -> Darwin 
  | _ -> raise BackendFatal

let mangle s = match os with 
| Linux -> Symbol.name s
| Darwin -> "_" ^ (Symbol.name s)
    
let compile_cnd (c:Ll.cnd) : X86.cnd = match c with
| Ll.Eq  -> X86.Eq
| Ll.Ne  -> X86.Neq
| Ll.Slt -> X86.Lt
| Ll.Sle -> X86.Le
| Ll.Sgt -> X86.Gt
| Ll.Sge -> X86.Ge

let compile_bop (c:Ll.bop) : X86.opcode = match c with
| Ll.Add  -> X86.Addq
| Ll.Sub  -> X86.Subq
| Ll.Mul  -> X86.Imulq
| Ll.SDiv -> X86.Idivq
| Ll.Shl -> X86.Shlq
| Ll.Lshr -> X86.Shrq
| Ll.Ashr -> X86.Sarq
| Ll.And ->X86.Andq
| Ll.Or -> X86.Orq
| Ll.Xor -> X86.Xorq

let get_1_2 (e,_) = e

let get_2_2 (_,e) = e

let getSome (aOption : 'a option) : 'a = match aOption with
| Some a -> a
| None -> raise BackendFatal

let isSome (aOption : 'a option) : bool = match aOption with
| Some _ -> true
| None -> false

type layout = (Ll.uid * X86.operand) list
type ctxt = { tdecls : (Ll.tid * Ll.ty) list
            ; layout : layout
            }

let lookup m x = 
  List.assoc x m 

let rec actualTy (ctxt : ctxt) (ty : Ll.ty) : Ll.ty = match ty with
| Namedt tid -> actualTy ctxt (lookup ctxt.tdecls tid)
| _ -> ty

let compile_operand (ctxt : ctxt) (opX86 : X86.operand) (opLl : Ll.operand) : ins = match opLl with 
| Null -> Movq, [~$ 0; opX86]
| Const(i) -> Movq, [~$ i; opX86]
| Gid gid -> Leaq, [Ind3 (Lbl (mangle gid), Rip); opX86] 
| Id uid -> Movq, [lookup ctxt.layout uid; opX86]

let isZeroConstOperand (opLl : Ll.operand) : bool = match opLl with 
| Const(0) -> true
| _ -> false

let getConst (op : operand) : int = match op with
| Const n -> n
| _ -> raise BackendFatal

let rec size_ty (uidTyList : (uid * ty) list) (ty: Ll.ty) : quad = match ty with
| Ll.I1 | Ll.I64 | Ll.Ptr _ -> 8
| Ll.Struct tyList -> List.fold_left (fun size ty -> size + size_ty uidTyList ty ) 0 tyList
| Ll.Array (n, arrTy) -> n * size_ty uidTyList arrTy
| Ll.Namedt uid -> size_ty uidTyList (lookup uidTyList uid)
| Void | I8 | Ll.Fun _ -> 0

let getNextTy (ctxt : ctxt) (ty : ty) (indexOp : operand) : ty = match actualTy ctxt ty with
| Array (_, elemTy) -> elemTy
| Struct tyList -> List.nth tyList (getConst indexOp)
| _ -> raise BackendFatal

let rec addOffset (ctxt : ctxt) (ty : ty) (opList : Ll.operand list) : ins list = match opList with
| op :: tl -> 
  let elemTy = getNextTy ctxt ty op in 
  if isZeroConstOperand op
  then addOffset ctxt elemTy tl
  else 
  [
    compile_operand ctxt (~% R11) op;
    Imulq, [~$ (size_ty ctxt.tdecls elemTy); ~% R11];
    Addq, [~% R11; ~% R10] 
  ] @ addOffset ctxt elemTy tl
| _ -> []

let compile_gep (ctxt : ctxt) (ty, op : ty * operand) (opList : Ll.operand list) : reg * ins list =
  let initialAddr = compile_operand ctxt (~% R10) op in
  let addOffsetCalc = addOffset ctxt (Array (0,ty)) opList in
  R10, initialAddr :: addOffsetCalc

let arg_loc: int -> X86.operand = function
| 0 -> ~% Rdi
| 1 -> ~% Rsi
| 2 -> ~% Rdx
| 3 -> ~% Rcx
| 4 -> ~% R08
| 5 -> ~% R09
| n -> Ind3 (Lit (16+8*(n-6)), Rbp)

let compile_call (ctxt:ctxt) (_,op: ty*Ll.operand) (args: (ty*Ll.operand) list): ins list = 
  let function_addr = [compile_operand ctxt (~% R10) op] in
  let args_reg = List.filteri (fun i _ -> i < 6) args in
  let args_stack = List.filteri (fun i _ -> i >= 6) args in
  let place_args_from_reg = List.flatten (List.mapi (fun i (_,oper) -> [compile_operand ctxt (~% R11) oper; Movq, [~% R11; arg_loc i]]) args_reg) in
  let place_args_from_stack = List.flatten (List.map (fun (_,oper) -> [compile_operand ctxt (~% R11) oper; Pushq,[~% R11]]) (List.rev args_stack)) in
  let remove_args_from_stack = 
    let num_args_on_stack = List.length args - 6 in
    if num_args_on_stack > 0
    then [ Addq, [~$ (8 * num_args_on_stack); ~% Rsp] ]
    else [] in
  function_addr @ place_args_from_reg @ place_args_from_stack (*place_args*) @ [Callq,[~% R10]] @ remove_args_from_stack

let compile_insn (ctxt : ctxt) (uidOpt, insn : uid option * insn) : ins list = 
  [X86.Comment ("compile_insn: "^Ll.string_of_insn insn), [] ] @
  match insn with
| Binop (bop, _, op1, op2) -> 
  let ins = (match bop with
  | Add | Sub | Mul | And | Or | Xor | Shl | Lshr | Ashr -> [ 
    compile_bop bop, [~% Rsi; ~% Rax] ]
  | SDiv -> [ 
      Cqto, [];
      compile_bop bop, [~% Rsi] ] ) in
  [
    compile_operand ctxt (~% Rax) op1;
    compile_operand ctxt (~% Rsi) op2;] @
    ins @ 
  [ Movq, [~% Rax; lookup ctxt.layout (getSome uidOpt)] ]
| Alloca ty ->
  [
    Subq, [~$ (size_ty ctxt.tdecls ty); ~% Rsp];
    Movq, [~% Rsp; lookup ctxt.layout (getSome uidOpt)]
  ]
| Load (_, op) ->
  [
    compile_operand ctxt (~% Rdi) op;
    Movq, [Ind2 Rdi; ~% Rsi];
    Movq, [~% Rsi; lookup ctxt.layout (getSome uidOpt)]
  ]
| Store (_, op1, op2) ->
  [
    compile_operand ctxt (~% Rdi) op1;
    compile_operand ctxt (~% Rsi) op2;
    Movq, [~% Rdi; Ind2 Rsi]
  ]
| Icmp (cnd, _, op1, op2) -> 
  [
    compile_operand ctxt (~% Rdi) op1;
    compile_operand ctxt (~% Rsi) op2;
    Cmpq, [~% Rsi; ~% Rdi];
    X86.Movq, [~$ 0; lookup ctxt.layout (getSome uidOpt)];
    Set (compile_cnd cnd), [lookup ctxt.layout (getSome uidOpt)];
  ]
| Call (ty, op, tyOpList) -> 
  compile_call ctxt (ty, op) tyOpList @
  if isSome uidOpt
  then [ Movq, [~% Rax; lookup ctxt.layout (getSome uidOpt)] ]
  else []
| Bitcast (_, op, _) | Zext (_, op, _) | Ptrtoint (_, op, _) ->
  [
    compile_operand ctxt (~% Rdi) op;
    Movq, [~% Rdi; lookup ctxt.layout (getSome uidOpt)]
  ]
| Gep (ty, op, opList) ->
  let resultReg, insList = compile_gep ctxt (ty, op) opList in 
  insList @ [ Movq, [~% resultReg; lookup ctxt.layout (getSome uidOpt)] ]
| Comment str -> 
  [Comment str, []]

let compile_terminator (ctxt : ctxt) (term : terminator): ins list = 
  [X86.Comment ("compile_terminator: "^Ll.string_of_terminator term), []] @
  match term with
| Ret (ty, opOption) -> (match ty with
  | Void -> fun l -> l
  | _ -> fun l -> (compile_operand ctxt (~% Rax) (getSome opOption)) :: l)
  [
    Movq, [~% Rbp; ~% Rsp]; 
    Popq, [~% Rbp]; 
    Retq, []
  ]
| Br lbl -> [Jmp, [~$$ (mangle lbl)]]
| Cbr (op, lbl1, lbl2) -> [
    compile_operand ctxt (~% Rax) op; 
    Cmpq, [~$ 0; ~% Rax];
    J Neq, [~$$ (mangle lbl1)];
    Jmp, [~$$ (mangle lbl2)]
  ]

let newlinesToNewComments s = List.map (fun s->X86.Comment s, []) (String.split_on_char '\n' s)

let makeElem (ctxt : ctxt) (uid : uid) (block : block) (prependIns : ins list) : elem =
  let insList : ins list = List.fold_left (fun agg insn -> (agg @ compile_insn ctxt insn)) [] block.insns in
  let terminator : ins list = compile_terminator ctxt block.terminator in
  gtext (mangle uid) (prependIns @ insList @ terminator)
  
let makeElems (ctxt : ctxt) (function_uid : uid) (cfg : cfg) (prologue : ins list) =  
  let firstElem : elem = makeElem ctxt function_uid (get_1_2 cfg) prologue in
  let restElems : elem list = List.map (fun (uid, block) -> makeElem ctxt uid block []) (get_2_2 cfg) in
  firstElem :: restElems
  
let makeLayout (uidList : uid list) : (Ll.uid * X86.operand) list = 
  let offset = ref 0 in
  List.map (
    fun uid -> 
      offset := !offset - 8;
      uid, Ind3 (Lit !offset, Rbp)
    ) uidList

let makeArgsToStackIns (layout : (uid * X86.operand) list) (params : uid list) : ins list = 
  List.flatten (List.mapi (fun i uid -> 
    (X86.Comment ("Arg "^string_of_int i^": reg to stack"), []) ::
    if i < 6 
    then [ Movq, [arg_loc i; lookup layout uid] ]
    else 
      [ 
        Movq, [arg_loc i; ~% Rdi]; 
        Movq, [~% Rdi; lookup layout uid]
      ](*[ Pushq, [lookup layout uid] ]*)) params) (*What we had before - both works, the new one is easier to read in the generated code: Movq, [arg_loc i; ~% Rdi]; Movq, [~% Rdi; lookup layout uid]*)

let getUidsFromCfg ((block, lblBlockList) : cfg) : uid list =
  List.filter_map (fun (uidOpt, _) -> uidOpt)
    (block.insns @ (List.fold_left (
      fun agg (_,block) -> 
        block.insns @ agg ) [] lblBlockList))

let compile_fdecl (tdecls: (uid * ty) list) (func: uid)  (fundecl: fdecl): elem list = 
  let comments_fdecl = List.hd (newlinesToNewComments ("compile_fdecl: "^Ll.string_of_named_fdecl (func, fundecl))) in
  let allUids = getUidsFromCfg fundecl.cfg @ fundecl.param in
  let layout = makeLayout allUids in
  let argsToStack = makeArgsToStackIns layout fundecl.param in
  let prologue = [
    comments_fdecl;
    X86.Comment "compile_prologue", [];
    Pushq, [~% Rbp];
    Movq, [~% Rsp; ~% Rbp];
    Subq, [~$ (8*List.length allUids); Reg(Rsp)]
  ] in
  makeElems {tdecls; layout} func fundecl.cfg (prologue @ argsToStack)

(* compile_gdecl ------------------------------------------------------------ *)
let rec compile_ginit = function 
    GNull -> [Quad (Lit 0)]
  | (GGid gid)   -> [Quad (Lbl (mangle gid))]
  | (GInt c)     -> [Quad (Lit c)]
  | (GString s)  -> [Asciz s]
  | (GArray gs)  -> List.concat (List.map compile_gdecl gs)
  | (GStruct gs) -> List.concat (List.map compile_gdecl gs)
and compile_gdecl (_, g) = compile_ginit g

let compile_prog ({tdecls; gdecls; fdecls}:Ll.prog) : X86.prog =  
  let g (lbl, gdecl) = Asm.data (mangle lbl) (compile_gdecl gdecl) in 
  let f (name, fdecl) = compile_fdecl tdecls name fdecl in 
  (List.map g gdecls) @ (List.concat (List.map f fdecls))

(*EOF*)