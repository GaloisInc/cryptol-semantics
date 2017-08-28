(* Taken from the VST repository *)
(* Andrew W. Appel and Stephen Yi-Hsien Lin,
    May 2013, October 2013, March 2014 *)

Require Recdef.
(*Require Import VST.floyd.coqlib3.
Require Import VST.floyd.sublist.*)
Require Import Cryptol.Bitvectors.
Require Import Cryptol.Coqlib.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List.
(*Require Import sha.general_lemmas.*)

(*
(* THIS BLOCK OF STUFF is not needed to define SHA256,
  but is useful for reasoning about it *)
Definition LBLOCKz : Z := 16. (* length of a block, in 32-bit integers *)
Definition WORD : Z := 4.  (* length of a word, in bytes *)
Definition CBLOCKz : Z := (LBLOCKz * WORD)%Z. (* length of a block, in characters *)
Definition hi_part (z: Z) := Int.repr (z / Int.modulus).
Definition lo_part (z: Z) := Int.repr z.

Fixpoint little_endian_integer (contents: list int) : int :=
 match contents with
 | nil => Int.zero
 | c::cr => Int.or (Int.shl (little_endian_integer cr) (Int.repr 8)) c
 end.
Definition big_endian_integer (contents: list int) : int :=
   little_endian_integer (rev contents).
(* END OF "THIS BLOCK OF STUFF" *)
*)
Import ListNotations.


Lemma skipn_length:
  forall {A} n (al: list A),
    (length al >= n)%nat ->
    (length (skipn n al) = length al - n)%nat.
Proof.
 induction n; destruct al; simpl; intros; auto.
 apply IHn. omega.
Qed.

Lemma skipn_short :
  forall {A} n (l:list A),
    (length l <= n)%nat ->
    skipn n l = nil.
Proof.
  induction n; simpl; intros.
  destruct l; trivial. simpl in H. omega.
  destruct l; trivial.
  apply IHn. simpl in H. omega.
Qed.

(* PREPROCESSING: CONVERTING STRINGS TO PADDED MESSAGE BLOCKS *)

(*converting a string to a list of Z *)
Fixpoint str_to_Z (str : string) : list Z :=
  match str with
    |EmptyString => nil
    |String c s => Z.of_N (N_of_ascii c) :: str_to_Z s
    end.

(* Taken from general_lemmas *)
Definition Z_to_Int (a b c d : Z) : @Int 32 :=
  @or 32 (@or 32 (@or 32 (@shl 32 (repr a) (repr 24)) (@shl 32 (repr b) (repr 16)))
            (@shl 32 (repr c) (repr 8))) (repr d).

Fixpoint Zlist_to_intlist (nl: list Z) : list Int :=
  match nl with
  | h1::h2::h3::h4::t => Z_to_Int h1 h2 h3 h4 :: Zlist_to_intlist t
  | _ => nil
  end.

Definition Shr b x := shru x (@repr 32 b).

Fixpoint intlist_to_Zlist (l: list (@Int 32)) : list Z :=
  match l with
  | nil => nil
  | i::r =>
    unsigned (Shr 24 i) ::
                 unsigned (and (Shr 16 i) (repr 255)) ::
                 unsigned (and (Shr 8 i) (repr 255)) ::
                 unsigned (and i (repr 255)) ::
                 intlist_to_Zlist r
  end.

Definition generate_and_pad msg :=
  let n := Zlength msg in
   Zlist_to_intlist (msg ++ [128%Z]
                ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0)
           ++ [repr (n * 8 / @modulus 32); repr (n * 8)].

(*ROUND FUNCTION*)

(*hardcoding the constants, first 32 bits of the fractional parts of the cube roots of the first 64 prime numbers*)
Definition K256 := map (@repr 32)
  [1116352408 ; 1899447441; 3049323471; 3921009573;
   961987163   ; 1508970993; 2453635748; 2870763221;
   3624381080; 310598401  ; 607225278  ; 1426881987;
   1925078388; 2162078206; 2614888103; 3248222580;
   3835390401; 4022224774; 264347078  ; 604807628;
   770255983  ; 1249150122; 1555081692; 1996064986;
   2554220882; 2821834349; 2952996808; 3210313671;
   3336571891; 3584528711; 113926993  ; 338241895;
   666307205  ; 773529912  ; 1294757372; 1396182291;
   1695183700; 1986661051; 2177026350; 2456956037;
   2730485921; 2820302411; 3259730800; 3345764771;
   3516065817; 3600352804; 4094571909; 275423344;
   430227734  ; 506948616  ; 659060556  ; 883997877;
   958139571  ; 1322822218; 1537002063; 1747873779;
   1955562222; 2024104815; 2227730452; 2361852424;
   2428436474; 2756734187; 3204031479; 3329325298].

(*functions used for round function*)
Definition Ch (x y z : @Int 32) : @Int 32 :=
  xor (and x y) (and (not x) z).

Definition Maj (x y z : @Int 32) : @Int 32 :=
  xor (xor (and x z) (and y z)) (and x y).

Definition Rotr b x := ror x (@repr 32 b).



Definition Sigma_0 (x : @Int 32) : @Int 32 :=
          xor (xor (Rotr 2 x) (Rotr 13 x)) (Rotr 22 x).
Definition Sigma_1 (x : @Int 32) : @Int 32 :=
          xor (xor (Rotr 6 x) (Rotr 11 x)) (Rotr 25 x).
Definition sigma_0 (x : @Int 32) : @Int 32 :=
          xor (xor (Rotr 7 x) (Rotr 18 x)) (Shr 3 x).
Definition sigma_1 (x : @Int 32) : @Int 32 :=
          xor (xor (Rotr 17 x) (Rotr 19 x)) (Shr 10 x).

(* word function *)
Function W (M: Z -> @Int 32) (t: Z) {measure Z.to_nat t} : @Int 32 :=
  if zlt t 16
  then M t
  else  (add (add (sigma_1 (W M (t-2))) (W M (t-7)))
               (add (sigma_0 (W M (t-15))) (W M (t-16)))).
Proof.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
Qed.

(*registers that represent intermediate and final hash values*)
Definition registers := list (@Int 32).

(*initializing the values of registers, first thirty-two bits of the fractional
    parts of the square roots of the first eight prime numbers*)
Definition init_registers : registers :=
  map repr  [1779033703; 3144134277; 1013904242; 2773480762;
                        1359893119; 2600822924; 528734635; 1541459225].

Definition nthi (il: list (@Int 32)) (t: Z) := nth (Z.to_nat t) il Bitvectors.zero.

Definition rnd_function (x : registers) (k : @Int 32) (w : @Int 32) : registers:=
  match x with
  |  [a; b; c; d; e; f; g; h] =>
     let T1 := add (add (add (add h (Sigma_1 e)) (Ch e f g)) k) w in
     let T2 := add (Sigma_0 a) (Maj a b c) in
       [add T1 T2; a; b; c; add d T1; e; f; g]
  | _ => nil  (* impossible *)
  end.

Function Round  (regs: registers) (M: Z ->@Int 32) (t: Z)
        {measure (fun t => Z.to_nat(t+1)) t} : registers :=
 if zlt t 0 then regs
 else rnd_function (Round regs M (t-1)) (nthi K256 t) (W M t).
Proof. intros; apply Z2Nat.inj_lt; omega.
Qed.

(* Taken from verif_dotprod.v*)
Fixpoint map2 {A B C: Type} (f: A -> B -> C) (al: list A) (bl: list B) : list C :=
  match al, bl with
  | a::al', b::bl' => f a b :: map2 f al' bl'
  | _, _ => nil
  end.

Definition hash_block (r: registers) (block: list (@Int 32)) : registers :=
      map2 add r (Round r (nthi block) 63).

Function hash_blocks (r: registers) (msg: list (@Int 32)) {measure length msg} : registers :=
  match msg with
  | nil => r
  | _ => hash_blocks (hash_block r (firstn 16 msg)) (skipn 16 msg)
  end.
Proof.
  intros.
  destruct (lt_dec (length msg) 16).
  rewrite skipn_short. simpl; omega. subst msg. simpl in *. omega.
  rewrite <- teq; auto.
  rewrite skipn_length. simpl; omega.
  omega.
Qed.

Definition SHA_256 (str : list Z) : list Z :=
  intlist_to_Zlist (hash_blocks init_registers (generate_and_pad str)).
