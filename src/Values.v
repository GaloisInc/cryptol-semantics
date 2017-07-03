Require Import AST.
Require Import String.
Require Import Coqlib.
Require Import Bitvectors.

(* Now mutually defined with Expr in AST.v *)
(* Inductive val := *)
(* | bit (b : bool) (* Can we ever get this now? *) *)
(* (*| bits {n} (b : BitV n) (* bitvector *)*) *)
(* | close (id : ident) (e : Expr) (E : ident -> option val)  (* closure *) *)
(* | tclose (id : ident) (e : Expr) (E : ident -> option val) (* type closure *) *)
(* | tuple (l : list val) (* heterogeneous tuples *) *)
(* | rec (l : list (string * val)) (* records *) *)
(* | typ (t : Typ) (* type value, used to fill in type variables *) *)
(* | vcons (v : val) (e : Expr) (E : ident -> option val) (* lazy list: first val computed, rest is thunked *) *)
(* | vnil (* empty list *) *)
(* . *)

(*
Definition unoption_bit (v : option val) : val :=
  match v with 
  | Some (bit b) => bit b
  | _            => bit false
end.

Fixpoint all_bit (l : list val) : bool :=
  match l with 
  | nil => true
  | cons x xs => 
      match x with 
      | (bit x') => all_bit xs
      | _        => false
      end
end. 

Fixpoint to_bit (v : val) : option (


Function to_bitv {ws : nat} (l : list val) : option (BitV ws) :=
  if all_bit l then Some (map unoption_bit l)  
               else None. 
 
*)










(* convert a forced list of bits to a bitvector *)
Fixpoint to_bitv {ws : nat} (l : list val) : option (BitV ws) :=
  match l, ws with
  | nil, O => Some (@repr 0 0)
  | (bit b) :: r, S n =>
    match @to_bitv n r with
    | Some bv => Some (@repr (S n) (unsigned bv + if b then (two_power_nat n) else 0))
    | None => None
    end
  | _,_ => None
  end.

Fixpoint from_bitv' {ws : nat} (n : nat) (bv : BitV ws) : list val :=
  match n with
  | O => nil
  | S n' => (bit (testbit bv (Z.of_nat n')) :: from_bitv' n' bv)
  end.

Definition from_bitv {ws : nat} (bv : BitV ws) : list val :=
  from_bitv' ws bv.  


Lemma tobit_length :
  forall l ws bv,
    @to_bitv ws l = Some bv ->
    ws = length l.
Proof.
  induction l; intros.
  unfold to_bitv in *. destruct ws; simpl in H; inv H. reflexivity.
  destruct ws; simpl in H. destruct a; simpl in H; inv H.
  destruct a; simpl in H; try solve [inv H].
  match goal with
  | [ H : context[ match ?X with _ => _ end ] |- _ ] => destruct X eqn:?
  end; inv H.
  eapply IHl in Heqo. simpl. auto.
Qed.

Lemma tobitv_cons : forall a l ws (bv : BitV (S ws)),
  to_bitv (a :: l) = Some bv -> 
    exists (bv' : BitV ws),
    to_bitv l = Some bv'.
Proof. 
  (* Need to find the right induction *)
  (*intro a. intro l. revert a. *)induction l; intros.    
  - inversion H. eapply tobit_length in H. inversion H. simpl. eauto.
  - destruct ws.   
    + eapply tobit_length in H. inversion H. 
    + (* This looks right *)inversion H. destruct a; try congruence. destruct a0; try congruence. destruct l; try congruence. 
      * eapply tobit_length in H. inversion H. simpl. eauto. 
      * clear H1. (* I believe this (?) *) 
    admit. 
Admitted.
  
Lemma tobit_frombit :
  forall l ws bv,
    to_bitv l = Some bv ->
    @from_bitv' ws ws bv = l.
Proof.
  induction l; intros.
  - eapply tobit_length in H. subst. simpl. reflexivity.
  - destruct ws. simpl in H. destruct a; congruence.
    apply tobitv_cons in H. destruct H. apply IHl in H.
    unfold from_bitv' in H.   
Admitted. 
(*
  simpl in H. destruct a; try congruence. destruct (to_bitv l). 
  - inversion H. destruct b. 
    + simpl. f_equal. 
      * f_equal. destruct (repr (unsigned b0 + two_power_nat ws)). 
        destruct (Z.of_nat ws). 
        
  - inversion H.
*)  
     

(* @NATE: This lemma, or something like it, is what we want proven about to_bitv and from_bitv *)
(*Lemma tobit_frombit :
  forall l ws bv,
    to_bitv l = Some bv ->
    @from_bitv' ws ws bv = l.
Proof.
  induction l; intros.
  eapply tobit_length in H. subst. simpl. reflexivity.
  destruct ws. simpl in H. destruct a; congruence.
  simpl. 
  simpl in H. destruct a; try congruence.
  match goal with
  | [ H : context[ match ?X with _ => _ end ] |- _ ] => destruct X eqn:?
  end; inv H.
  eapply IHl in Heqo.
  f_equal. f_equal.
Admitted.
*)

Definition env := ident -> option val.
Definition empty : env := fun _ => None.

(* Conversion from fully computed finite list to lazy list via trivial thunking *)
Fixpoint thunk_list (l : list val) : val :=
  match l with
  | nil => vnil
  | f :: r =>
    vcons f (EValue (thunk_list r)) empty
  end.
