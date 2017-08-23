(* This file is extremely similar to the HMAC_functional_prog.v file at https://github.com/PrincetonUniversity/VST/blob/master/sha/HMAC_functional_prog.v *)
(* It has been altered slightly in a few minor ways *)
(* 1. It uses our modified Bitvectors library, which has resulted in a few bit widths added below *)
(* 2. From 1, Byte.repr has been changed to @repr 8 *)
(* 3. It has had relevant definitions copied from general_lemmas.v, just below *)
(* 4. The import paths have changed *)

Require Import Cryptol.Coqlib.
Require Import Cryptol.Bitvectors.
Require Import List. Import ListNotations.

(* copied from sha.general_lemmas *)
Definition isbyteZ (i: Z) := (0 <= i < 256)%Z.

Lemma map_list_repeat:
  forall A B (f: A -> B) n x,
     map f (list_repeat n x) = list_repeat n (f x).
Proof. induction n; simpl; intros; f_equal; auto.
Qed.
(* end copied from general_lemmas *)                                             

(* Our bitvectors library is more general *)
(* A byte is an 8 bit int *)
Definition byte := @Int 8.

Module HP.

  
(*SHA256: blocksize = 64bytes
    corresponds to
    #define SHA_LBLOCK	16
    #define SHA256_CBLOCK	(SHA_LBLOCK*4) *)

Module Type HASH_FUNCTION.
  Parameter BlockSize:nat. (*measured in bytes; 64 in SHA256*)
  Parameter DigestLength: nat. (*measured in bytes; 32 in SHA256*)
  Parameter Hash : list Z -> list Z.
  Parameter Hash_isbyteZ: forall m, Forall isbyteZ (Hash m).
End HASH_FUNCTION.


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

Definition KeyPreparation (l:list Z) : list byte := map (@repr 8) (mkKey l).

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

Lemma SF_ByteRepr x: isbyteZ x ->
                     sixtyfour x =
                     map (@unsigned 8) (sixtyfour (repr x)).
Proof. intros. unfold sixtyfour.
 rewrite map_list_repeat.
 rewrite unsigned_repr; trivial. destruct H.
 assert (BMU: (@max_unsigned 8) = 255). reflexivity. omega.
Qed.

Lemma length_SF {A} (a:A) :length (sixtyfour a) = HF.BlockSize.
Proof. apply length_list_repeat. Qed.

Lemma isbyte_hmaccore ipad opad m k:
   Forall isbyteZ (HmacCore (@repr 8 ipad) (@repr 8 opad) m k).
Proof. apply HF.Hash_isbyteZ. Qed.

End HMAC_FUN.

End HP.