Require Import Cryptol.Coqlib.
Require Import Cryptol.BvectorExt.
Require Import Cryptol.Bitstream.
Require Import Cryptol.Eager.
Require Import Cryptol.Semantics.
Require Import Cryptol.AST.

Require Import otp.FCF.
Require Import otp.OTP_FCF.
Require Import otp.OTP_verif.
Require Import otp.OTP_cryptol.
Require Import otp.OTP_lib.

(* cryptol version is otp_encrypt *)
(* FCF version is OTP_encrypt *)

  
Theorem cryptol_OTP_secure :
  forall key msg bvkey,
    (* inputs have correct type *)
    has_type key byte -> 
    has_type msg byte ->
    to_bvector 8 key = Some bvkey ->
    (forall n, @rand_indist 8 (ret bvkey) n) ->
    eager_eval_expr ge tempty sempty
                    (EApp (EApp (EVar encrypt) (EValue key)) (EValue msg)) (to_sval (otp_encrypt key msg)) /\
    exists bv, to_bvector 8 (otp_encrypt key msg) = Some bv /\
               forall n, @rand_indist 8 (ret bv) n.
Proof.
  intros.
  remember H as Hkey. remember H0 as Hmsg.
  clear HeqHkey. clear HeqHmsg.
  eapply otp_equiv in H0; try exact H.
  split. assumption.
  
  assert (Htype : has_type (otp_encrypt key msg) byte). {

    unfold otp_encrypt.
    eapply has_type_xor_ext'; eauto.
    
  }
  assert (exists bvmsg, to_bvector 8 msg = Some bvmsg).
  eapply to_bvector_succeeds'; eauto.
  destruct H3 as [bvmsg].
  
  eapply same_otp in H3; try exact H1; eauto.
  eexists. rewrite H3. split; auto.
  intros.
  eapply OTP_encrypt_indist; eauto.
Qed.
