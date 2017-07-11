Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Bitvectors.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.
Require Import BuiltinSem.
Require Import Values.        
Require Import Bitstream.

Require Import EvalTac.

Import HaskellListNotations.
Open Scope string.

Require Import Xor.

(* expects a type variable, but ignores it *)
Definition decrypt : Expr := (ETApp (EVar (243,"decrypt")) (ETyp (TCon (TC (TCNum 3)) nil))).
Definition encrypt : Expr := (ETApp (EVar (242,"encrypt")) (ETyp (TCon (TC (TCNum 3)) nil))).

Notation "eval_expr* GE E V" := (eval_expr GE _ E V) (at level 99, only printing).
Notation "vcons* V EXP" := (vcons V EXP _) (at level 98, only printing).
Notation "force_list* V VS" := (force_list _ _ V VS) (at level 97, only printing).

Lemma single_bit_roundtrip :
  forall (b b' : bool),
    (if (if b then (if b' then false else true) else b') then (if b' then false else true) else b') = b.
Proof.
  intros. destruct b; destruct b'; simpl; auto.
Qed.


Lemma xor_roundtrip :
  forall pt,
    Forall (n_bits 8%nat) pt ->
    forall k,
      n_bits (8%nat) k ->
      exists ciphertext,
        eval_expr ge empty (EApp (EApp encrypt (EValue (thunk_list k))) (EList (map EList (map (map EValue) pt))) ) ciphertext /\
        exists v',
          eval_expr ge empty (EApp (EApp decrypt (EValue (thunk_list k))) (EValue ciphertext)) v' /\
          exists vls,
            force_list ge empty v' vls /\
            Forall2 (force_list ge empty) vls pt.
Proof.
  induction 1; intros;
    do 9 match goal with
         | [ H : n_bits _ _ |- _ ] => inversion H
         end; subst.
  - clear -H.
    eexists. split.
    e. e. e. g.
    repeat e. 
    repeat e. repeat e. repeat e.
    repeat e. repeat e.
    e. 
    eapply eval_comp_imp_nil.
    repeat e. simpl. omega.
    eexists.  split.
    e. e. e. g. e. e. e.
    e. e. e. e. eapply eval_comp. eapply eval_comp_imp_nil.
    repeat e. simpl. omega.

    eexists. split.
    e. e.
    
  - clear -H1 H H0 IHForall.
    inversion H. inversion H3. inversion H6. inversion H9. inversion H12.
    inversion H15. inversion H18. inversion H21. inversion H24. subst.
    clear -H1 H H0 IHForall.
    eapply IHForall in H1; eauto.
    clear IHForall. destruct H1. destruct H1.
    inversion H1. subst.
    destruct H2. destruct H2. destruct H3. destruct H3.
    inversion H7. subst.

    init_globals ge.

    eexists; split.
    + e. (* run encrypt *)
      -- e. simpl. e. g.
         repeat e. repeat e. repeat e. repeat e.
         repeat e.
      -- simpl. e. e. e. repeat e. eassumption. (* use part of inductive hypothesis *)
      -- e. e. e. eapply idx_last. e. e. e. e. e. e. e. e. e. repeat e.
         e. e. e. e. e.
         eapply eval_lift_binary_builtin.
         simpl; auto. simpl. instantiate (3 := (EVar (3,"")) :: nil). reflexivity.
         e. e. e. eapply eval_binary_over_bit_to_bit. simpl. reflexivity.
         e. e.
    +
Admitted.
(*      (* BELOW MIGHT BE RIGHT IDK *)
      eexists; split. (* run decrypt *)
      e. e. e. g.
      e. repeat e. e. e. e. e. e. e.
      e. eapply idx_last. e. e. e. e. e. e. e.
      e. e. e. repeat e. repeat e.
      e. e. e. e. e.
      eapply eval_lift_binary_builtin.
      simpl. auto.
      simpl.
      instantiate (3 := (EVar (3,"")) :: nil). reflexivity.
      simpl. e. e. e. simpl.
      eapply eval_binary_over_bit_to_bit. reflexivity. e. e.

      * destruct vs.
        -- (* encrypt/decrypt exactly one byte, nothing more *)
          eexists. split.
          e. eapply eval_comp_imp_nil. e. e. e. e.
          eapply eval_comp_imp_nil. repeat e. simpl. omega.
          e. simpl. omega.
          e. simpl. e.
          rewrite single_bit_roundtrip. e.
          e. e. e. e. simpl. eapply eval_binary_over_bit_to_bit. reflexivity.
          e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          e. e. simpl.
          rewrite single_bit_roundtrip. e.
          e. e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          simpl. e. e. simpl.
          rewrite single_bit_roundtrip. e.
          e. e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          simpl. e. e. simpl.
          rewrite single_bit_roundtrip. e.
          e. e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          simpl. e. e. simpl.
          rewrite single_bit_roundtrip. e.
          e. e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          simpl. e. e. simpl.
          rewrite single_bit_roundtrip. e.
          e. e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          simpl. e. e. simpl.
          rewrite single_bit_roundtrip. e.
          e. e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
          simpl. e. e. simpl.
          rewrite single_bit_roundtrip. eapply force_cons.
          eapply eval_lift_binary_nil. eapply eval_lift_binary_nil. e. e. e. e.
          destruct l; simpl in H8; inversion H8. e.
        -- (* inductive case, encrypt/decrypt one byte then apply IH *)
          
          simpl.
          
          destruct l; try solve [simpl in H8; inversion H8].
          inversion H0. subst. inversion H11. inversion H10.
          inversion H15. inversion H18. inversion H21.
          inversion H24. inversion H27. inversion H30. inversion H33. subst.
          clear H33 H27 H21 H15 H10 H18 H24 H30.
          simpl in H8. simpl in H7. inversion H8. inversion H7.
          subst.

          inversion H14. subst.
          destruct vs0; simpl in H20; try congruence.
          inversion H20. subst.
          inversion H10. subst.
          inversion H21. subst.
          inversion H23. subst.
          inversion H25. subst.
          inversion H27. subst.
          inversion H29. subst.
          inversion H31. subst.
          inversion H33. subst.
          inversion H35. subst.
          clear H35.
          inversion H32. subst.
          inversion H30. subst.
          inversion H28. subst.
          inversion H26. subst.
          inversion H24. subst.
          inversion H22. subst.
          inversion H19. subst.
          inversion H17. subst.
          
          eexists. split.

          eapply force_cons.

          --- 
            e. e. eapply idx_last. e. e.
            e. e. e. e. e. e. 
            e. e.
            e. e. e. e.
            e. e. e. repeat e. repeat e. e. e. e. e.
            eapply eval_lift_binary_builtin. simpl. auto.
            simpl. instantiate (3 := (EVar (3,""))::nil). reflexivity.
            e. e. e.
            eapply eval_binary_over_bit_to_bit.
            simpl. reflexivity.
            e. e. e. e. e. e. e. e. e. repeat e.
            e. e. e. e. e.
            eapply eval_lift_binary_builtin. simpl. auto.
            simpl. instantiate (3 := (EVar (3,""))::nil). reflexivity.
            e. e. e.
            eapply eval_binary_over_bit_to_bit.
            simpl. reflexivity.
            e. e.

          --- (* inductive hypothesis needs to be used here I think *)
            
            e. e. e. e. e. e. e. e. e. e. e. e.
            e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e.
            e. eapply eval_lift_binary_builtin.
            e. simpl. instantiate (3 := (EVar (3,""))::nil). reflexivity.
            e. e. e. eapply eval_binary_over_bit_to_bit. reflexivity.
            e. e. e.
            (* HERE *)
            (* What are the useful hypotheses? *)
            *)