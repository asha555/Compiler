(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)

open Tigercommon 
module S = Symbol 
module Ty = Types

type enventry 
  = VarEntry of Types.ty 
  | FunEntry of { formals: Types.ty list; result: Types.ty }

  let baseTenvFunc = [
    (S.symbol "int", Ty.INT);
    (S.symbol "string", Ty.STRING);
    (S.symbol "void", Ty.VOID);
    (S.symbol "nil",Ty.NIL);
  
  ]
  
let baseVenvFunc = [
  (S.symbol "print", FunEntry{formals = [Ty.STRING]; result = Ty.VOID});
  (S.symbol "flush", FunEntry{formals = []; result = Ty.VOID});
  (S.symbol "getchar", FunEntry{formals = []; result = Ty.STRING});
  (S.symbol "ord", FunEntry{formals = [Ty.STRING]; result = Ty.INT});
  (S.symbol "chr", FunEntry{formals = [Ty.INT]; result = Ty.STRING});
  (S.symbol "size", FunEntry{formals = [Ty.STRING]; result = Ty.INT});
  (S.symbol "substring", FunEntry{formals = [Ty.STRING;Ty.INT;Ty.INT]; result = Ty.STRING});
  (S.symbol "concat", FunEntry{formals = [Ty.STRING;Ty.STRING]; result = Ty.STRING});
  (S.symbol "not", FunEntry{formals = [Ty.INT]; result = Ty.INT});
  (S.symbol "exit", FunEntry{formals = [Ty.INT]; result = Ty.VOID})]

let baseVenv = List.fold_left (fun accTable sym_enventry -> S.enter (accTable, (fst sym_enventry), (snd sym_enventry))) S.empty baseVenvFunc

let baseTenv = List.fold_left (fun accTable sym_ty -> S.enter (accTable, (fst sym_ty), (snd sym_ty))) S.empty baseTenvFunc



