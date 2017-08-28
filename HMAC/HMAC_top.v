Require Import HMAC.HMAC_specs_equiv.
Require Import HMAC.HMAC_spec.
Require Import HMAC.HMAC_verif.
Require Import HMAC.HMAC.
Require Import HMAC.HMAC_lib.

Require Import Cryptol.GlobalExtends.

Require Import Cryptol.Coqlib.
Require Import Cryptol.Lib.
Require Import Cryptol.Utils.
Require Import Cryptol.AST.
Require Import Cryptol.Bitstream.
Require Import Cryptol.Eager.
Require Import Cryptol.GetEachN.
Require Import Cryptol.Semantics.

Require Import Bvector.

Require Import List.
Import ListNotations.

Theorem HMAC_cryptol_to_FCF (MSGT : Set) :
  (* input to HMAC has the correct number of bits in the right shape *)
  forall key keylen msg msglen,
    has_type key (bytestream keylen) ->
    has_type msg (bytestream msglen) ->
    (* environment is well formed *)
    forall GE TE SE, 
      wf_env ge GE TE SE ->
      (forall id, In id [(371, "ks");(372, "okey");(373, "ikey");(374, "internal")] -> GE id = None) ->
      (* hash function *)
      forall h hf c p HashBlock iv ,
        good_hash h GE TE SE hf ->
        @correct_model_hash c p hf (h_star p HashBlock iv) ->
        forall (splitAndPad : MSGT -> list (Bvector (c + p))) nmsg nkey,
          eappend (map bv_to_extval (splitAndPad nmsg)) = msg ->
          bv_to_extval nkey = key ->
          forall opad ipad,
            same_bits 92 opad ->
            same_bits 54 ipad ->
            forall fpad,
              (forall x, bv_to_extval' (app_fpad fpad (h_star p HashBlock iv x)) = bv_to_extval' (h_star p HashBlock iv x)) ->
              forall unused,
          eager_eval_expr
            GE TE SE (apply (tapply (EVar hmac) ((typenum (Z.of_nat msglen)) :: (typenum (Z.of_nat keylen)) :: (typenum unused) :: (typenum (Z.of_nat keylen)) :: nil)) (h :: h :: h :: (EValue key) :: (EValue msg) :: nil))
            (to_sval (eseq (bv_to_extval' (@HMAC c p HashBlock iv MSGT splitAndPad fpad opad ipad nkey nmsg)))).
Proof.
  intros.
  edestruct Hmac_eval_keylen_is_blocklength. eapply H. eauto. eauto.
  eauto. eapply H0.
  destruct H10.
  eapply HMAC_equiv in H11. rewrite <- H11 in H10.
  eapply H10.
  all: eauto.
Qed.
          
