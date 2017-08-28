Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
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

Import HaskellListNotations.
Open Scope string.

Require Import HMAC.HMAC.

Require Import HMAC.HMAC_spec.

Require Import HMAC.HMAC_lib.

Require Import HMAC.Kinit_eval.


(* lemma for when the length of the key is the same as the length of the block *)
Lemma Hmac_eval_keylen_is_blocklength :
  forall (key : ext_val) keylen,
    has_type key (bytestream keylen) -> 
    forall GE TE SE, 
      wf_env ge GE TE SE ->
      (forall id, In id [(371, "ks");(372, "okey");(373, "ikey");(374, "internal")] -> GE id = None) ->
      forall h hf,
        good_hash h GE TE SE hf ->
        forall msg msglen unused,
          has_type msg (bytestream msglen) ->
          exists v,
            eager_eval_expr GE TE SE (apply (tapply (EVar hmac) ((typenum (Z.of_nat msglen)) :: (typenum (Z.of_nat keylen)) :: (typenum unused) :: (typenum (Z.of_nat keylen)) :: nil)) (h :: h :: h :: (EValue key) :: (EValue msg) :: nil)) (to_sval v) /\ hmac_model hf key msg = Some v.
Proof.
  intros.
  rename H into Hkeytype.
  rename H1 into HIDs.
  rename H2 into Hgood_hash.
  rename H3 into Hmsgtype.
  init_globals ge.
  abstract_globals ge.
  edestruct good_hash_complete_eval; eauto.
  repeat break_exists.
  destruct H.

  inversion Hkeytype. subst.
  inversion Hmsgtype. subst.
  remember (hf (eseq (map (fun x3 : ext_val => xor_const 54 x3) l ++ l0))) as hv1.
  assert (HT : exists n, has_type hv1 (tseq n tbit)). {
    assert (exists n, has_type (eseq (map (fun x3 : ext_val => xor_const 54 x3) l ++ l0)) (bytestream n)). {
      eexists. econstructor.
      rewrite Forall_app. split.
      eapply Forall_map. eauto.
      intros. eapply xor_const_byte; eauto.
      eauto.
    }
    break_exists.
    eapply H1 in H2.
    repeat break. subst. eauto.
  }
  break_exists.
  edestruct ext_val_list_of_strictval; try eassumption.
  
  eexists; split.
  
  e. e. e. e. e. e. e. e. e.
  gen_global hmac.
  ag.
  
  e.
  e.
  e.
  e.
  e. e.
  e.
  e.
  e.
  e.
  e.

  e.
  e. 
  lv.
  e. e. e. e. e. 

  ag.

  e. e.
  e. e.

  g.
  e.

  (* evaluate the match *)
  econstructor. econstructor.

  g.

  (* call Kinit function *)
  (* START *)
  {
    eapply kinit_eval.
    solve_wf_env.
    exact Hkeytype.
    eapply good_hash_same_eval; eauto.
    gex.
    lv. et. et. et. lv.
  }  (* END *)
  
  simpl.
  rewrite list_of_strictval_of_strictlist. 
  reflexivity.
  
  (* Begin model section *)
  {
    eapply eager_eval_bind_senvs. eassumption.
    instantiate (1 := fun x => to_sval (xor_const 92 x)).  
    intros. e. e. e.
    ag.
    e. e. lv. e. e. e. ag.
    e. e. e. 
    reflexivity.
    e. lv. lv. 
    simpl. 
    inversion H6. subst. simpl.
    unfold strictnum.
    unfold Z.to_nat. unfold Pos.to_nat.
    unfold Pos.iter_op. unfold Init.Nat.add.
    rewrite xor_num. reflexivity.
    rewrite H7. eassumption.
    congruence.
  }
  (* End model section *)

  e. g.
  e. e. e. e. ag.
  e. e. e. e. e. lv. e. e. e. e. e. ag.
  e. e. e. e. g.
  e. ec. ec. 
  g.
  { (* TODO: make this one tactic *)
    eapply kinit_eval.
    solve_wf_env.
    exact Hkeytype.
    eapply good_hash_same_eval; eauto.
    gex.
    lv. et. et. et. lv.
  }
  simpl.
  rewrite list_of_strictval_of_strictlist. 
  reflexivity.

  eapply eager_eval_bind_senvs. eassumption.
  instantiate (1 := fun x => to_sval (xor_const 54 x)).  
  intros. e. e. e. ag. 
  e. e. lv. e. e. e. ag. 
  e. e. e. reflexivity.
  e. lv. lv.
  inversion H6. subst. simpl.
  unfold strictnum.
  rewrite xor_num. reflexivity.
  rewrite H7. eassumption.
  simpl. unfold Pos.to_nat. simpl. congruence.

  e. lv. e. lv. lv. 

  unfold to_sval. fold to_sval.  
  rewrite append_strict_list. 
  reflexivity.

  eapply global_extends_eager_eval.

  replace (map (fun x3 : ext_val => to_sval (xor_const 54 x3)) l) with
      (map to_sval (map (fun x3 => xor_const 54 x3) l)) by (rewrite list_map_compose; reflexivity).
  rewrite <- list_append_map.
  remember (app (map (fun x3 : ext_val => xor_const 54 x3) l) l0) as ll.
  replace (strict_list (map to_sval ll)) with (to_sval (eseq ll)) by (reflexivity).
  subst ll.
  
  eapply H1.
  econstructor.

  rewrite Forall_app. split; auto.
  eapply Forall_map. eassumption.

  intros. eapply xor_const_byte; eauto.

  unfold bind_decl_groups.
  unfold bind_decl_group.
  unfold declare.

  gex.

  e. lv.

  simpl.
  rewrite <- Heqhv1.
  rewrite H3. reflexivity.
  
  e. lv. lv.

  rewrite append_strict_list. reflexivity.
  eapply global_extends_eager_eval.

  (* get to_sval out to outside *)
  (* evaluate the hash function *)

  replace (map (fun x4 : ext_val => to_sval (xor_const 92 x4)) l) with
  (map to_sval (map (xor_const 92) l)) by
      (clear -l; 
       induction l; simpl; auto; f_equal; eapply IHl; eauto).
    
  rewrite get_each_n_map_commutes.

  rewrite map_strict_list_map_map_to_sval.
  rewrite <- list_append_map.
  rewrite strict_list_map_to_sval.

  assert (exists n, has_type (eseq (map (xor_const 92) l ++ map eseq (get_each_n (Pos.to_nat 8) x4))) (bytestream n)). {
    eapply has_type_seq_append.
    exists (Datatypes.length (map (xor_const 92) l)).
    econstructor.
    eapply Forall_map. eassumption.
    intros. eapply xor_const_byte; eauto.
    subst hv1.
    inversion H2. subst.
    rewrite <- H6 in *.
    eapply list_of_strictval_to_sval in H3. inversion H3.
    subst. 
    remember H1 as HHash.
    clear HeqHHash.
    symmetry in H6.    
    eapply good_hash_fully_padded in H6; try eassumption.
    eapply type_stream_of_bytes in H6; eauto.
    
  }

  break_exists.
  eapply H1 in H6. break_and. eassumption.
  
  gex.
  
  (* our result matches the model *)
  subst hv1.
  eapply list_of_strictval_to_sval in H3.
  simpl. rewrite H3.

  reflexivity.

  Unshelve.
  all: exact id.
  
Qed.
