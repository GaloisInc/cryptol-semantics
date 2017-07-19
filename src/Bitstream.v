Require Import String.
Require Import AST.
Require Import List.
Require Import Values.

(* We need easy ways of writing down inputs to cryptol functions *)
(* They only need base type bit, and structures *)

(* make some kind of type, convertible to val and strictval *)

Inductive ext_val :=
| ebit (b : bool)
| eseq (l : list ext_val)
| etup (l : list ext_val)
| erec (f : list (string * ext_val))
.

Fixpoint to_val (e : ext_val) : val :=
  let fix go_pair (p : string * ext_val) := 
      match p with
      | (s,t) => (s, to_val t)
      end in
  let fix go_list_pair (ps : list (string * ext_val)) :=
      match ps with
      | nil => nil
      | p :: ps => (go_pair p) :: (go_list_pair ps)
      end in
  match e with
  | ebit b => bit b
  | eseq l => thunk_list (map to_val l)
  | etup l => tuple (map to_val l)
  | erec f => rec (go_list_pair f)
  end.
        
Fixpoint to_sval (e : ext_val) : strictval :=
  let fix go_pair (p : string * ext_val) := 
      match p with
      | (s,t) => (s, to_sval t)
      end in
  let fix go_list_pair (ps : list (string * ext_val)) :=
      match ps with
      | nil => nil
      | p :: ps => (go_pair p) :: (go_list_pair ps)
      end in
  match e with
  | ebit b => sbit b
  | eseq l => strict_list (map to_sval l)
  | etup l => stuple (map to_sval l)
  | erec f => srec (go_list_pair f)
  end.

Inductive ext_type :=
| tbit
| tseq (len : nat) (t : ext_type)
| ttup (l : list ext_type)
| trec (l : list (string * ext_type))
.

Inductive has_type : ext_val -> ext_type -> Prop :=
| is_bit :
    forall b,
      has_type (ebit b) tbit
| is_seq :
    forall l t,
      Forall (fun x => has_type x t) l ->
      has_type (eseq l) (tseq (length l) t)
| is_tup :
    forall l lt,
      Forall2 has_type l lt ->
      has_type (etup l) (ttup lt)
| is_rec :
    forall l lt,
      Forall2 has_type (map snd l) lt ->
      has_type (erec l) (trec (combine (map fst l) lt))
.

Definition byte : ext_type := tseq 8 tbit.
Definition bytestream (n : nat) := tseq n byte.
Definition word : ext_type := tseq 64 tbit.



Definition n_bits (n : nat) (v : val) : Prop :=
  exists ev,
    has_type ev (tseq n tbit) /\ to_val ev = v.

Definition sn_bits (n : nat) (v : strictval) : Prop :=
  exists ev,
    has_type ev (tseq n tbit) /\ to_sval ev = v.
    

(*
Inductive n_bits : nat -> list val -> Prop :=
| empty_bits :
    n_bits O nil
| another_bit :
    forall n l b,
      n_bits n l ->
      n_bits (S n) (bit b :: l).
*)

Require Import Eager.
Require Import List.


Lemma strict_list_injective :
  forall x y,
    strict_list x = strict_list y ->
    x = y.
Proof.
  induction x; intros. simpl in *.
  destruct y; simpl in H; try congruence.
  simpl in H. destruct y; simpl in H; try congruence.
  inversion H. subst. eapply IHx in H2. congruence.
Qed.

Lemma n_bits_eval :
  forall n x ge TE E,
    n_bits n x ->
    exists vs,
      eager_eval_expr ge TE E (EValue x) (strict_list vs) /\ length vs = n.
Proof.
  induction n; intros;
    unfold n_bits in *;
    destruct H. destruct H.
  inversion H. destruct l; simpl in *; try congruence. subst.
  eexists; split. simpl. econstructor; eauto. instantiate (1 := nil). econstructor; eauto. reflexivity.

  destruct H. inversion H. subst.
  destruct l; simpl in *; try congruence.
  inversion H3.
  subst. inversion H4.
  subst. inversion H1. subst.
  edestruct IHn; eauto.
  eexists; split; eauto.
  econstructor. eauto.
  destruct H0.

  
  eexists; split; eauto.
  simpl. inversion H0. subst.
  econstructor. instantiate (1 := (sbit b :: x)).
  simpl. econstructor; eauto.
  econstructor. econstructor.
  simpl. congruence.

  Unshelve. exact tempty.
  exact sempty.
Qed.

