Require Import AST.
Require Import String.
Require Import Coqlib.
Require Import Bitvectors.
Require Import Utils. 
Require Import Omega. 


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



Fixpoint from_bitv' (ws : nat) (n : nat) (bv : BitV ws) : list val :=
  match n with
  | O => nil
  | S n' => (bit (testbit bv (Z.of_nat n')) :: from_bitv' ws n' bv)
  end.

Definition from_bitv {ws : nat} (bv : BitV ws) : list val :=
  from_bitv' ws ws bv.  

Definition three := @repr 3 3.
Eval compute in from_bitv three.  
Eval compute in three. 


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
(*
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
Admitted.*)
  

Lemma frombitv_cons : forall l width length (bv : BitV width), 
  from_bitv' width length bv = l -> 
    exists a, 
    from_bitv' width (S length) bv = (a::l).
Proof.
  intros. simpl. rewrite H. eauto. 
Qed.  

Lemma testbit_single : forall ws l1 (b0 : BitV ws) (b : bool) len (bv : BitV (S ws)), 
  len = length l1 -> 
  to_bitv l1 = Some b0 -> 
  repr (unsigned b0 + (if b then two_power_nat ws else 0)) = bv -> 
   testbit bv (Z.of_nat len) = b.
Proof. 
  induction ws; intros.
  - destruct b. 
Admitted.  

Lemma testbit_tobitv : forall len ws l1 l2 v (bv : BitV ws), 
  len = length l1 -> 
    @to_bitv ws (l2 ++ v :: l1) = Some bv -> 
    bit (testbit bv (Z.of_nat len)) = v. 
Proof. 
  induction ws; intros.  
  - inversion H0. destruct l2; simpl in *; try congruence. destruct v; inversion H2. destruct v0; try congruence.
  - simpl in H0. destruct l2 eqn:?; simpl in *; try congruence. destruct v eqn:?; simpl in *; try congruence. destruct (to_bitv l1) eqn:?. inversion H0. clear H0. f_equal. eapply testbit_single. 
    + instantiate (1:=l1). assumption.  
    + instantiate (1:=b0). assumption. 
    + reflexivity. 
    + inversion H0. 
    + destruct v0 eqn:?; try congruence. destruct (to_bitv (l++v::l1)) eqn :?. eapply IHws in H; eauto.
(* H0 and H should get us close. Perhaps a lemma about increasing the width not changing the testbit result if we know something like H0 *)

Admitted.

   


Lemma list_helper : forall {A : Type} (l1 : list A) (l2 : list A) (v v0 : A), 
   (l2 ++ v :: nil) ++ v0 :: l1 = l2 ++ (v :: v0 :: l1). 
Proof.
  intros. induction l2. 
  - simpl. reflexivity. 
  - simpl. rewrite IHl2. reflexivity. 
Qed.   


(* Main theorem, can produce a simplified corollary *)
Theorem tobit_frombit :
  forall len v l1 l2 width (bv : BitV width),
    (width >= len)%nat -> 
    to_bitv (l2++v::l1) = Some bv ->
    length l1 = len -> 
    from_bitv' width len bv = l1.
Proof.
  induction len; intros. 
  - simpl. apply length_zero_iff_nil in H1. auto. 
  - destruct l1. inversion H1. simpl. f_equal. clear -H0 H1. destruct width.
    + inversion H1. eapply testbit_tobitv. instantiate (1:=l1). reflexivity. instantiate (1:=(l2++(cons v nil))). rewrite list_helper. assumption. 
    + inversion H1. eapply testbit_tobitv. instantiate (1:=l1). reflexivity. instantiate (1:=(l2++(cons v nil))). rewrite list_helper. assumption. 
    + eapply IHlen. 
      * omega. 
      * instantiate (1:=v0). instantiate (1:=l2++(cons v nil)). rewrite list_helper. assumption. 
      * inversion H1. reflexivity. 
Qed. 
  

        

(*

  induction l; intros.
  - unfold to_bitv in H0. destruct width; simpl in H0. 
    + inversion H0. inversion H. simpl. reflexivity.
    + inversion H0. 
  - destruct width; simpl in H0; destruct a; try congruence.
     
    destruct length. 
    + simpl. exfalso. *) 
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
