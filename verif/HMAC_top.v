
Require Import HMAC_specs_equiv.
Require Import HMAC_verif.


(*

Theorem HMAC_equiv (MSGT : Set) :
  forall keylen msglen key msg,
    has_type key (bytestream keylen) ->
    has_type msg (bytestream msglen) ->
    forall c p hf res HashBlock iv (splitAndPad : MSGT -> list (Bvector (b c p))),
      hmac_model hf key msg = Some res ->
      @correct_model_hash c p hf (h_star p HashBlock iv) ->
      forall nmsg nkey,
        eappend (map bv_to_extval (splitAndPad nmsg)) = msg ->
        bv_to_extval nkey = key ->
        forall opad ipad,
          same_bits 92 opad ->
          same_bits 54 ipad ->
          forall fpad,
            (forall x, bv_to_extval' (app_fpad fpad (h_star p HashBlock iv x)) = bv_to_extval' (h_star p HashBlock iv x)) ->
            eseq (bv_to_extval' (@HMAC c p HashBlock iv MSGT splitAndPad fpad opad ipad nkey nmsg)) = res.


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
*)