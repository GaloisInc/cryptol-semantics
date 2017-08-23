Require Import List.
Import ListNotations.

Require Import Cryptol.Lib.

Require Import Cryptol.Coqlib.


(* Works as long as you pass in enough fuel *)
(* just use the length of the list *)
Fixpoint get_each_n' {A : Type} (fuel : nat) (tot : nat) (l : list A) : list (list A) :=
  match l,fuel with
  | _ :: _,S fuel' => (firstn tot l) :: get_each_n' fuel' tot (list_drop tot l)
  | _,_ => nil
  end.

Definition get_each_n {A : Type} (tot : nat) (l : list A) :=
  get_each_n' (length l) tot l.

Lemma get_each_n'_fuel :
  forall {A} n (l : list A) fuel tot,
    (n >= length l)%nat ->
    (fuel >= length l)%nat ->
    tot <> O ->
    get_each_n' fuel tot l = get_each_n' (length l) tot l.
Proof.
  induction n; intros.
  destruct l; simpl in *; destruct fuel; try reflexivity; omega.
  destruct l. simpl in *.
  destruct fuel; reflexivity.
  assert (n >= length l)%nat by (simpl in *; omega).
  simpl. destruct tot; try omega.
  simpl. destruct fuel; simpl in *; try omega.
  f_equal.
  assert (tot = O \/ tot <> O) by omega.
  destruct H3. subst. simpl.
  eapply IHn; eauto; omega.
  assert (length (list_drop tot l) <= length l)%nat by (eapply list_drop_length; eauto).
  erewrite IHn; try omega.
  symmetry.
  eapply IHn; omega.
Qed.
    

Lemma get_each_n_head :
  forall {A : Type} (l l' : list A) n,
    n = length l ->
    n <> O ->
    get_each_n n (l ++ l') = [l] ++ get_each_n n l'.
Proof.
  induction l; intros.
  simpl in *. congruence.
  simpl in *.
  destruct n; inversion H.
  assert (n = O \/ n <> O) by omega.
  destruct H1. subst. 
  destruct l; simpl in H1; try omega.
  simpl. unfold get_each_n. simpl. reflexivity.
  unfold get_each_n. simpl.
  rewrite firstn_app.
  rewrite list_drop_app.
  f_equal.
  unfold get_each_n in IHl.
  eapply get_each_n'_fuel; eauto.
  
  rewrite app_length.
  omega.
Qed.

Lemma get_each_n'_zero :
  forall {A} fuel (l : list A),
    l <> nil ->
    get_each_n' fuel O l = repeat [] fuel.
Proof.
  induction fuel; intros.
  simpl. destruct l; reflexivity.
  simpl. destruct l; try congruence.
  erewrite IHfuel; eauto.
Qed.


Lemma get_each_n'_map_commutes_strong :
  forall {A B : Type} (f : A -> B) len k l fuel n,
    (len >= Datatypes.length l)%nat ->
    (k >= fuel)%nat ->
    get_each_n' fuel n (map f l) = map (map f) (get_each_n' fuel n l).
Proof.
  induction len; induction k; intros.
  assert (fuel = O) by omega. subst. simpl.
  destruct l; reflexivity.
  destruct l; simpl in H; try omega.
  simpl. destruct fuel; simpl; reflexivity.
  destruct fuel; try omega.
  destruct l; simpl; reflexivity.
  assert (fuel = S k \/ k >= fuel)%nat by omega.
  destruct H1. subst.
  simpl. destruct l; simpl; auto.
  f_equal. erewrite <- firstn_map. reflexivity.
  replace (f a :: map f l) with (map f (a :: l)) by auto.
  erewrite list_map_drop.
  assert (n = O \/ n > O)%nat by omega.
  destruct H1. subst. repeat erewrite get_each_n'_zero by (simpl; congruence).
  eapply map_repeat_nil.
  eapply IHlen.
  eapply length_list_drop in H1.
  instantiate (1 := a :: l) in H1.
  omega. congruence.
  instantiate (1 := k). omega.
  eauto.
Qed.

Lemma get_each_n_map_commutes :
  forall {A B : Type} (f : A -> B) n l,
    get_each_n n (map f l) = map (map f) (get_each_n n l).
Proof.
  intros.
  unfold get_each_n.
  erewrite get_each_n'_map_commutes_strong.
  erewrite map_length. reflexivity.
  instantiate (1 := Datatypes.length l). omega.
  instantiate (1 := Datatypes.length (map f l)). omega.
Qed.

(* Everything below is for type_stream_of_bytes *)
Lemma get_each_n'_extra_fuel :
  forall {A} fuel fuel' n (l : list A),
    (fuel >= fuel')%nat ->
    (fuel' >= Datatypes.length l)%nat ->
    (n <> O) ->
    get_each_n' fuel n l = get_each_n' fuel' n l.
Proof.
  induction fuel; intros.
  assert (fuel' = O) by omega.
  subst. destruct l; simpl in *; try omega.
  reflexivity.
  assert (fuel' = S fuel \/ fuel >= fuel')%nat by omega.
  destruct H2. subst. reflexivity.

  destruct l; simpl.
  simpl in *.
  destruct fuel'; simpl; auto.

  destruct fuel'. simpl in H0; omega.
  simpl. f_equal.

  simpl in H0.
  assert (fuel >= fuel')%nat by omega.
  assert (fuel' >= length l)%nat by omega.
  destruct n; try congruence.
  
  unfold list_drop. fold list_drop.
  eapply IHfuel. omega.
  generalize (list_drop_length l n). intros. omega.
  congruence.
Qed.

  