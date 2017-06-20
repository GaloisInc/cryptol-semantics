Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.

Require Import AST.

(* right side of this generated from cryptol implementation *)

Import HaskellListNotations.


Definition gf28Add := (NonRecursive (Decl 244 (DExpr (ETAbs 305 (EAbs 249 (EWhere (EApp (EApp (ETApp (ETApp (ETApp (EVar 42) (TCon (TF TCAdd) [TCon (TC (TCNum 1)) [],TVar (TVBound 305 KNum)])) (TUser 243 [] (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []]))) (TCon (TC (TCNum 0)) [])) (EVar 250)) (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 0)) []))) [(Recursive [(Decl 250 (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar 34) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 305 KNum))) (TUser 243 [] (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []]))) (EList [(ETApp (EVar 29) (TUser 243 [] (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))])) (EComp (EApp (EApp (ETApp (EVar 28) (TUser 243 [] (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []]))) (EVar 251)) (EVar 252)) [[(From 251 (EVar 249))],[(From 252 (EVar 250))]]))))])])))))).