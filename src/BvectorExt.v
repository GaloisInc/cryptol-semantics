Require Import Bvector.
Require Import Cryptol.AST.
Require Import Cryptol.Bitstream.
Require Import Cryptol.Coqlib.
Require Import Cryptol.GetEachN.

Fixpoint to_bvector (w : nat) (e : ext_val) : option (Bvector w) :=
  match e,w with
  | eseq (ebit b :: r),S n =>
    match to_bvector n (eseq r) with
    | Some bv => 
      Some (Vector.cons bool b n bv)
    | _ => None
    end
  | eseq nil, O => Some (Vector.nil bool)
  | _,_ => None
  end.

Lemma to_bvector_succeeds :
  forall l n,
    has_type (eseq l) (tseq n tbit) ->
    exists bv,
      to_bvector n (eseq l) = Some bv.
Proof.
  induction l; intros.

  * inversion H. subst. simpl.
    eauto.

  * inversion H. subst. inversion H2.
    subst.
    edestruct IHl. econstructor; eauto.
    inversion H3. subst.
    simpl. rewrite H0.
    eauto.
Qed.

Lemma bytestream_type :
  forall l t,
    Forall (fun x => has_type x t) l ->
    has_type (eseq l) (tseq (length l) t).
Proof.
  induction l; intros.
  econstructor; eauto.
  inversion H. subst.
  econstructor; eauto.
Qed.

Fixpoint bv_to_extval' {w : nat} (bv : Bvector w) : list ext_val :=
  match bv with
  | Vector.nil => nil
  | Vector.cons b _ r => ebit b :: bv_to_extval' r
  end.
  
Definition bv_to_extval {w : nat} (bv : Bvector w) : ext_val :=
  let bits := bv_to_extval' bv in
  let bytes := get_each_n 8 bits in
  eseq (map eseq bytes).
