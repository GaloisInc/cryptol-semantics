Require Import Cryptol.Coqlib.
Require Import Cryptol.Bitvectors.

Require Import Cryptol.AST.
Require Import Cryptol.Semantics.
Require Import Cryptol.Utils.
Require Import Cryptol.Builtins.
Require Import Cryptol.BuiltinSem.
Require Import Cryptol.BuiltinSyntax.
Require Import Cryptol.Values.        
Require Import Cryptol.Bitstream.
Require Import Cryptol.Lib.
Require Import Cryptol.GlobalExtends.
Require Import Cryptol.GetEachN.

Require Import Cryptol.EvalTac.
Require Import Cryptol.Eager.

Require Import Cryptol.ExtToBitvector.
Require Import Cryptol.Prims.

Import HaskellListNotations.
Require Import List.
Import ListNotations.
Require Import String.
Open Scope string.


Definition where_test : Expr :=
  (EAbs (243,"M")
      (EWhere
       (EVar (244,"W"))
       [(Recursive
         [(Decl (244,"W")
           (DExpr
            (EApp
             (EApp
              (ETApp
               (ETApp
                (ETApp
                 (EVar (34,"#"))
                 (ETyp (TCon (TC (TCNum 8)) [])))
                (ETyp (TCon (TC (TCNum 8)) [])))
               (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
              (EVar (243,"M")))
             (EComp
              (EApp
               (EApp
                (ETApp
                 (EVar (1,"+"))
                 (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                (EApp
                 (EApp
                  (ETApp
                   (ETApp
                    (ETApp
                     (EVar (40,"@"))
                     (ETyp (TCon (TC (TCNum 16)) [])))
                    (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                   (ETyp (TCon (TC (TCNum 8)) [])))
                  (EVar (244,"W")))
                 (EApp
                  (EApp
                   (ETApp
                    (EVar (2,"-"))
                    (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                   (EVar (245,"j")))
                  (ETApp
                   (ETApp
                    (EVar (0,"demote"))
                    (ETyp (TCon (TC (TCNum 1)) [])))
                   (ETyp (TCon (TC (TCNum 8)) []))))))
               (EApp
                (EApp
                 (ETApp
                  (ETApp
                   (ETApp
                    (EVar (40,"@"))
                    (ETyp (TCon (TC (TCNum 16)) [])))
                   (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                  (ETyp (TCon (TC (TCNum 8)) [])))
                 (EVar (244,"W")))
                (EApp
                 (EApp
                  (ETApp
                   (EVar (2,"-"))
                   (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                  (EVar (245,"j")))
                 (ETApp
                  (ETApp
                   (EVar (0,"demote"))
                   (ETyp (TCon (TC (TCNum 8)) [])))
                  (ETyp (TCon (TC (TCNum 8)) []))))))
              [[(From (245,"j") (ETApp
                                 (ETApp
                                  (ETApp
                                   (EVar (49,"fromTo"))
                                   (ETyp (TCon (TC (TCNum 8)) [])))
                                  (ETyp (TCon (TC (TCNum 15)) [])))
                                 (ETyp (TCon (TC (TCNum 8)) []))))]]))))])])).

Lemma test_eval :
  forall GE TE SE,
    GE (34, "#") = Some (mb 3 2 Append) /\ SE (34,"#") = None ->
    GE (49, "fromTo") = Some (mb 3 0 fromTo) /\ SE (49,"fromTo") = None ->
    forall n xv,
    has_type xv (tseq n (tseq 8 tbit)) ->
    forall x,
    eager_eval_expr GE TE SE x (to_sval xv) ->
    exists v,
      eager_eval_expr GE TE SE (EApp where_test x) v.
Proof.
  induction n; intros.
  inversion H1. subst.
  destruct l; try solve [simpl in *; congruence].
  
(*  eexists.
  unfold where_test.
  e. e.
  e. g.
  use append_eval.
  eapply eager_eval_local_var; eauto. simpl.
  unfold extend. simpl.
  instantiate (1 := nil).
  reflexivity.
  e. 
  ec. ec. simpl.
  use fromTo_eval.
  unfold extend. simpl. intuition.
  reflexivity.
  unfold fromTo_ev. unfold to_sval. fold to_sval.
  rewrite list_of_strictval_of_strictlist.
  reflexivity.
  repeat fold to_sval.*)

  Focus 2.
  
  
  
  
Admitted.
  