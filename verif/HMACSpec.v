(* This spec has been modified from its original version *)
(* (https://github.com/PrincetonUniversity/VST/blob/master/sha/HMAC_functional_prog.v)*)
(* It has been formatted to fit your verification environment *)

Require Import Bitvectors.
Require Import Coqlib.
Require Import List. Import ListNotations.

Module HP.

(*SHA256: blocksize = 64bytes
    corresponds to
    #define SHA_LBLOCK	16
    #define SHA256_CBLOCK	(SHA_LBLOCK*4) *)

Definition isbyteZ (i: Z) := (0 <= i < 256)%Z.
  
Module Type HASH_FUNCTION.
  Parameter BlockSize:nat. (*measured in bytes; 64 in SHA256*)
  Parameter DigestLength: nat. (*measured in bytes; 32 in SHA256*)
  Parameter Hash : list Z -> list Z.
  Parameter Hash_isbyteZ: forall m, Forall isbyteZ (Hash m).
End HASH_FUNCTION.


Definition byte := @Int 8.

Definition byte_repr := @repr 8.

Module Type HMAC_Module.
  Parameter HMAC: byte -> byte -> list Z -> list Z -> list Z.
End HMAC_Module.

Module HMAC_FUN (HF:HASH_FUNCTION)  <: HMAC_Module.

Definition sixtyfour {A} (i:A): list A:= list_repeat HF.BlockSize i.

(*Reading rfc4231 reveals that padding happens on the right*)
Definition zeroPad (k: list Z) : list Z :=
  k ++ list_repeat (HF.BlockSize-length k) Z0.

Definition mkKey (l:list Z) : list Z :=
  if Z.gtb (Zlength l) (Z.of_nat HF.BlockSize)
  then (zeroPad (HF.Hash l))
  else zeroPad l.

Definition KeyPreparation (l:list Z) : list byte := map byte_repr (mkKey l).

Definition mkArg (key:list byte) (pad:byte): list byte :=
       (map (fun p => xor (fst p) (snd p))
          (combine key (sixtyfour pad))).
Definition mkArgZ key (pad:byte): list Z :=
     map unsigned (mkArg key pad).
(*
Definition Ipad := P.Ipad.
Definition Opad := P.Opad.
*)
(*innerArg to be applied to message, (map Byte.repr (mkKey password)))*)

Definition innerArg IP (text: list Z) key : list Z :=
  (mkArgZ key IP) ++ text.

Definition INNER IP k text := HF.Hash (innerArg IP text k).

Definition outerArg OP (innerRes: list Z) key: list Z :=
  (mkArgZ key OP) ++ innerRes.

Definition OUTER OP k innerRes := HF.Hash (outerArg OP innerRes k).

Definition HmacCore IP OP txt (key: list byte): list Z := OUTER OP key (INNER IP key txt).

Definition HASH a txt :=  HF.Hash (a ++ txt).

Definition HmacCore' IP OP txt (key: list byte): list Z :=
  HASH (mkArgZ key OP) (HASH (mkArgZ key IP) txt).

Goal forall IP OP txt key, HmacCore IP OP txt key = HmacCore' IP OP txt key.
Proof. intros. reflexivity. Qed.

Definition HMAC IP OP txt password: list Z :=
  let key := KeyPreparation password in
  HmacCore IP OP txt key.

Lemma map_list_repeat:
  forall A B (f: A -> B) n x,
     map f (list_repeat n x) = list_repeat n (f x).
Proof. induction n; simpl; intros; f_equal; auto.
Qed.

Lemma SF_ByteRepr x: isbyteZ x ->
                     sixtyfour x =
                     map unsigned (sixtyfour (byte_repr x)).
Proof. intros. unfold sixtyfour.
       rewrite map_list_repeat. f_equal.
       unfold unsigned. unfold byte_repr. unfold repr. unfold intval. 
       destruct H.
       rewrite Z_mod_modulus_eq. unfold modulus.
       unfold two_power_nat. simpl.
       rewrite Zmod_small; omega.
       congruence.
Qed.

Lemma length_SF {A} (a:A) :length (sixtyfour a) = HF.BlockSize.
Proof. apply length_list_repeat. Qed.

Lemma isbyte_hmaccore ipad opad m k:
   Forall isbyteZ (HmacCore (byte_repr ipad) (byte_repr opad) m k).
Proof. apply HF.Hash_isbyteZ. Qed.

End HMAC_FUN.

End HP.