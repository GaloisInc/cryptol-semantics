(*Add LoadPath "~/Desktop/Galois/cryptol-semantics/src".*)
Require Import AST.
Require Import String.
Require Import Coqlib.
Require Import Bitvectors.
Require Import Utils. 
Require Import Omega. 

Import HaskellListNotations. 

(* STATUS. only things left to do:
   OPTIONAL. 
      - Cleaner corollary from theorem 
  (using from_bitv instead of from_bitv')
*)


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


(**************** Functions ****************)

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

(**************** Results ****************)

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
  
Lemma to_bitv_width_zero : forall l (bv : BitV 0), 
  to_bitv l = Some bv -> l = nil. 
Proof. 
  destruct l; intros. 
  - reflexivity. 
  - exfalso. inversion H. destruct v; try congruence. 
Qed. 

Lemma intval_width_zero : forall (bv : BitV 0), 
  intval bv = 0.
Proof. 
  intros. unfold intval. destruct bv. unfold two_power_nat in intrange. simpl in intrange. omega. 
Qed. 

Lemma frombitv_cons : forall l width length (bv : BitV width), 
  from_bitv' width length bv = l -> 
    exists a, 
    from_bitv' width (S length) bv = (a::l).
Proof.
  intros. simpl. rewrite H. eauto. 
Qed. 

Lemma frombit_nil : forall ws (bv : BitV ws), 
  from_bitv bv = [] -> ws = 0%nat. 
Proof. 
  intros. unfold from_bitv in H. destruct ws eqn:?; try congruence.
  inversion H.
Qed. 

Lemma list_helper : forall {A : Type} (l1 : list A) (l2 : list A) (v v0 : A), 
   (l2 ++ v :: nil) ++ v0 :: l1 = l2 ++ (v :: v0 :: l1). 
Proof.
  intros. induction l2. 
  - simpl. reflexivity. 
  - simpl. rewrite IHl2. reflexivity. 
Qed.   

Lemma lt_irrefl : forall n, 
  ~(two_power_nat n < two_power_nat n). 
Proof. 
  intros. omega.  
Qed. 

Lemma testbit_power_two : forall n, 
  Z.testbit (two_power_nat n) (Z.of_nat n) = true. 
Proof.
  intros. rewrite Zsign_bit.
  destruct (zlt (two_power_nat n) (two_power_nat n)) eqn:?. 
   - exfalso. clear Heqs.  apply lt_irrefl in l. exact l.  
   - reflexivity. 
   - generalize (two_power_nat_pos n). intros. split; try omega. 
     rewrite two_power_nat_S. omega.
Qed.

Lemma lt_rewrite_larger : forall a b c,  
  a < b -> 
    b + b < c -> 
    a + b < c. 
Proof. 
  intros. omega. 
Qed.  

Lemma testbit_single : forall ws l1 (b0 : BitV ws) (b : bool) len (bv : BitV (S ws)), 
  len = length l1 -> 
  to_bitv l1 = Some b0 -> 
  repr (unsigned b0 + (if b then two_power_nat ws else 0)) = bv -> 
   testbit bv (Z.of_nat len) = b.
Proof. 
  induction ws; intros.
  - unfold two_power_nat in H1. simpl in H1. rewrite <- H1. apply to_bitv_width_zero in H0. subst. simpl. unfold unsigned. 
    assert (intval b0 = 0). { apply intval_width_zero. }
    rewrite H. simpl. destruct b; auto. 
  - rewrite <- H1. rewrite testbit_repr.
    Focus 2. unfold zwordsize. split. omega. 
    apply Nat2Z.inj_lt. apply tobit_length in H0. omega.

    unfold unsigned. destruct b. 
    + apply tobit_length in H0. rewrite <- H0 in H. rewrite H. rewrite Zsign_bit. destruct (zlt (intval b0 + two_power_nat (S ws)) (two_power_nat (S ws))) eqn :?. 
      * exfalso. clear Heqs. generalize (intrange b0). intros. omega. 
      * reflexivity. 
      * split. 
         -- generalize (intrange b0). intros. omega. 
         -- generalize (intrange b0). intros. rewrite 3 two_power_nat_S. rewrite two_power_nat_S in H2. inversion H2. eapply lt_rewrite_larger in H4. omega. instantiate (1:=(2*(2*(2*two_power_nat ws)))). omega.
    + apply tobit_length in H0. rewrite <- H0 in H. rewrite H. rewrite Zsign_bit. destruct (zlt (intval b0 + two_power_nat (S ws)) (two_power_nat (S ws))) eqn :?. 
      * exfalso. clear Heqs. generalize (intrange b0). intros. omega. 
      * clear Heqs. generalize (intrange b0). intros. destruct (zlt (intval b0 + 0) (two_power_nat (S ws))) eqn:?. 
         -- reflexivity. 
         -- exfalso. replace (intval b0 + 0) with (intval b0) by omega. omega.   
      * split. 
         -- generalize (intrange b0). intros. omega. 
         -- generalize (intrange b0). intros. replace (intval b0 + 0) with (intval b0) by omega. rewrite two_power_nat_S. omega. 
Qed. 


Lemma z_two_power_nat :
  forall x,
    2 ^ Z.of_nat x = two_power_nat x.
Proof.
  intros. 
  rewrite two_power_nat_correct.
  rewrite Zpower_nat_Z.
  reflexivity.
Qed.

Lemma testbit_widen :
  forall wsbig wssmall zidx bv_z,
    (wsbig >= wssmall)%nat ->
    Z.of_nat wssmall > zidx ->
    testbit (@repr wsbig bv_z) zidx = testbit (@repr wssmall bv_z) zidx.
Proof.
  intros. unfold testbit.
  rewrite unsigned_repr_eq. rewrite unsigned_repr_eq.
  unfold modulus.
  replace (two_power_nat wsbig) with (2 ^ (Z.of_nat wsbig)).
  
  rewrite Z.mod_pow2_bits_low.
  replace (two_power_nat wssmall) with (2 ^ (Z.of_nat wssmall)).
  rewrite Z.mod_pow2_bits_low.
  reflexivity.
  omega.
  eapply z_two_power_nat; eauto.
  omega.
  eapply z_two_power_nat; eauto.
Qed.

Lemma repr_mod :
  forall {ws} z,
    ws <> O ->
    @repr ws z = @repr ws (z mod (@modulus ws)).
Proof.
  intros. unfold repr.
  eapply unsigned_eq. simpl.
  repeat rewrite Z_mod_modulus_eq by auto.
  rewrite Z.mod_mod. reflexivity. unfold modulus.
  generalize (two_power_nat_pos ws). intros. omega.
Qed.

Lemma testbit_tobitv : forall len ws l1 l2 v (bv : BitV ws), 
  len = length l1 -> 
    @to_bitv ws (l2 ++ v :: l1) = Some bv -> 
    bit (testbit bv (Z.of_nat len)) = v. 
Proof.
  induction ws; intros.  
  - inversion H0. destruct l2; simpl in *; try congruence. destruct v; inversion H2. destruct v0; try congruence.
  - simpl in H0. destruct l2 eqn:?; simpl in *; try congruence. destruct v eqn:?; simpl in *; try congruence. destruct (to_bitv l1) eqn:?. inversion H0. f_equal. eapply testbit_single. 
    + eauto. 
    + eauto. 
    + reflexivity. 
    + inversion H0. 
    + remember H as Hlen. clear HeqHlen. destruct v0 eqn:?; try congruence. destruct (to_bitv (l++v::l1)) eqn :?. eapply IHws in H; eauto. 
      * subst. inversion H0. subst.
        clear H0. f_equal.
        erewrite testbit_widen.
        instantiate (1 := ws).
        
        Focus 3.
        eapply tobit_length in Heqo. rewrite Heqo.
        destruct l; simpl; auto. rewrite Zpos_P_of_succ_nat. omega.
        rewrite Zpos_P_of_succ_nat. rewrite app_length.
        simpl.
        unfold Z.of_nat. destruct (length l + S (length l1))%nat eqn :?. simpl. omega. destruct (length l1) eqn:?. simpl. 
        apply Zgt_pos_0.
        rewrite Zpos_P_of_succ_nat. rewrite Zpos_P_of_succ_nat.  omega. 
          
        Focus 2. omega.

        rewrite repr_mod.
        replace ((unsigned b0 + (if b then two_power_nat ws else 0)) mod modulus) with (unsigned b0).
        rewrite repr_unsigned. reflexivity.
        unfold modulus. destruct b.
        
        rewrite Zplus_mod. rewrite Z_mod_same_full. rewrite Zmod_small. rewrite Zmod_small. omega. 
       
        unfold unsigned. generalize (intrange b0). intros. omega.
        rewrite Zmod_small. generalize (intrange b0). intros. 
        assert (unsigned b0 + 0 = unsigned b0) by omega. rewrite H0.  
        unfold unsigned. omega. 
        unfold unsigned. generalize (intrange b0). intros. omega. 
        assert (unsigned b0 + 0 = unsigned b0) by omega. rewrite H. rewrite Zmod_small. reflexivity. 
        generalize (intrange b0). unfold unsigned. intros. omega. 
        
        destruct ws. 
        apply tobit_length in Heqo. symmetry in Heqo. rewrite length_zero_iff_nil in Heqo. destruct l. simpl in Heqo. inversion Heqo. inversion Heqo. 
  
        auto.  

      * congruence.
Qed. 


Lemma tobit_frombit' :
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

Lemma tobit_frombit : forall l ws (bv : BitV ws), 
  to_bitv l = Some bv -> from_bitv bv = l. 
Proof. 
  intros. destruct l.
  - apply tobit_length in H. simpl in H. destruct ws. 
     + unfold from_bitv. simpl. reflexivity. 
     + inversion H. 
  - unfold from_bitv. destruct ws. 
    + inversion H. destruct v; congruence.
    + simpl.
      assert (Datatypes.length l = ws). {
        eapply tobit_length in H.
        simpl in H. inversion H. auto.
      }
      erewrite tobit_frombit'; try solve [eauto].
      f_equal. 
      eapply testbit_tobitv; eauto.
      instantiate (1 := nil). assumption.
      instantiate (2 := nil).
      eapply H.
Qed.
    
Lemma from_bitv'_widen :
  forall ws' ws bv,
    (ws' >= ws)%nat ->
    from_bitv' ws' ws (@repr ws' bv) = from_bitv' ws ws (@repr ws bv).
Proof.
Admitted.

Lemma frombit_tobit : forall l ws (bv : BitV ws), 
  from_bitv bv = l -> to_bitv l = Some bv. 
Proof. 
  induction l; intros.
  - apply frombit_nil in H. subst. simpl. generalize (intval_width_zero).
    intros. f_equal. eapply f_equal. apply unsigned_eq. simpl. unfold unsigned. rewrite H. reflexivity.
  - unfold from_bitv in H. unfold from_bitv in IHl. destruct ws.
    + inversion H.
    + simpl in H. inversion H.
      destruct bv. replace ({| intval := intval; intrange := intrange |}) with (@repr (S ws) intval) in *.
      erewrite (from_bitv'_widen (S ws) ws) in * by omega.
      simpl.
      subst l. specialize (IHl _ _ eq_refl).
      rewrite IHl.
      simpl.
      

Admitted. 

(* Main theorem *)
Theorem tobit_frombit_equiv : forall l ws (bv : BitV ws), 
  to_bitv l = Some bv <-> from_bitv bv = l. 
Proof. 
  intros. split. 
  apply tobit_frombit. 
  apply frombit_tobit.
Qed.

Definition env := ident -> option val.
Definition empty : env := fun _ => None.


(* Conversion from fully computed finite list to lazy list via trivial thunking *)
Fixpoint thunk_list (l : list val) : val :=
  match l with
  | nil => vnil
  | f :: r =>
    vcons f (EVar (0,""%string)) tempty (fun x => if ident_eq (0,""%string) x then Some (thunk_list r) else None)
  end.
