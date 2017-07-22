(* This file is an example on how to write normal fixpoints over weird trees *)
(* These trees come up sometimes when expressing the syntax of programs, especially when representing records *)
(* This walks you through what seems to be the simplest solution *)

Require Import List.
Import ListNotations.


(* A very common design pattern is for a type to contain lists of itself *)
(* it could be other things, but it is very commonly lists *)


(* This is the simplest example I can think of *)
Inductive simple_tree :=
| leaf
| internal (f : list simple_tree)
.


(* Coq can figure this out *)
Fixpoint better_id (s : simple_tree) : simple_tree :=
  match s with
  | leaf => leaf
  | internal l => internal (map better_id l)
  end.

(* This is particularly common for representing records *)
(* could also be used to represent a trie *)
(* B is the type of data at the leaves *)
(* A is the type of label for internal links *)
Inductive labeled_tree {A B : Type} :=
| tleaf (x : B)
| tinternal (l : list (A * labeled_tree))
.

(* Now it is hard to write functions over this type *)
(* Coq doesn't like this: *)
(* Error: Cannot guess decreasing argument of fix. *)

(*
Fixpoint map_leaves {A B C : Type} (f : B -> C) (t : @labeled_tree A B) {struct t} : @labeled_tree A C :=
  match t with
  | tleaf x => tleaf (f x)
  | tinternal l =>
    let labels := map fst l in
    let subts' := map (fun x => map_leaves f (snd x)) l in
    tinternal (combine labels subts')
  end.
*)

(* If we actually want to write this function, we have some fun times ahead of us *)

(* We could try to write a size function which we could use as a decreasing measure *)
(* But we quickly run into the exact same problem we had before *)

(*
Fixpoint size {A B : Type} : (t : @labeled_tree A B) : nat :=
  match t with
  | tleaf _ => S O
  | tinternal l => 
    ???
  .
 *)


(* If you want, you can define it this way: *)
Fixpoint map_leaves {A B C : Type} (f : B -> C) (t : @labeled_tree A B) : @labeled_tree A C :=
  let fix go_pair p :=
      match p with
      | (lab,subt) => (lab,map_leaves f subt)
      end in
  let fix go_list_pair lp :=
      match lp with
      | nil => nil
      | p :: r => (go_pair p) :: (go_list_pair r)
      end in
  match t with
  | tleaf x => tleaf (f x)
  | tinternal l => tinternal (go_list_pair l)
  end.

(* If you want to minimize the number of internal fixes, do more like this *)
Fixpoint map_leaves' {A B C : Type} (f : B -> C) (t : @labeled_tree A B) {struct t} : @labeled_tree A C :=
  let fix go_list_pair f lp :=
      match lp with
      | nil => nil
      | (lab,subt) :: r => (lab, map_leaves' f subt) :: (go_list_pair f r)
      end in
  match t with
  | tleaf x => tleaf (f x)
  | tinternal l => tinternal (go_list_pair f l)
  end.

                                                 

Definition go_list_pair {A B C : Type} :=
  let fix go_list_pair (f : B -> C) (lp : list (A * @labeled_tree A B)) :=
      match lp with
      | nil => nil
      | (lab,subt) :: r => (lab, @map_leaves' A B C f subt) :: (go_list_pair f r)
      end in go_list_pair.


(* Now we've defined a bunch of functions, but that's just the
beginning. Coq is great because we can prove things about our
programs. Suppose we want to prove things about these functions: *)

(* That requires us to induct over these funny trees *)

(* Suppose we want trees where the labels and the data are nats *)
(* and we really want all the conatined nats to not be zero *)
(* but the labels can be anything *)
(* At this point I have no idea why, but it's a simple example *)
Inductive nonzero : @labeled_tree nat nat -> Prop :=
| leaf_nonzero :
    forall n,
      n <> O ->
      nonzero (tleaf n)
| internal_nonzero :
    forall l,
      Forall nonzero (map snd l) ->
      nonzero (tinternal l)
.

(* Now, it's easy to write relational properties like the one above, but much harder to prove things about them. *)

(* Suppose we add one to all the leaves *)
(* This transformation should preserve the nonzero property *)
Lemma nonzero_succ_preserved_garden :
  forall t,
    nonzero t ->
    nonzero (map_leaves S t).
Proof.
  induction t; intros. 
  - econstructor; eauto.

  - induction l; intros.
    + inversion H. subst. econstructor; eauto.
    + inversion H. subst. simpl in H1. inversion H1. subst.
      assert (nonzero (tinternal l)). econstructor; eauto.
      specialize (IHl H0).
      unfold map_leaves. fold (@map_leaves nat nat).
      econstructor. econstructor.

      destruct a. simpl. simpl in H3.
      
      Focus 2.
      inversion IHl. eassumption.
      
      (* However, here we need to know about l0, which means we need better induction *)
Abort.

Definition labeled_tree_rect_full 
  (A B : Type)
    (P : @labeled_tree A B -> Type)
    (Pl : list (A * @labeled_tree A B) -> Type)
    (Hleaf : forall x, P (tleaf x))
    (Hinternal : forall l, Pl l -> P (tinternal l))
    (Hnil : Pl nil)
    (Hcons : forall a f r, P f -> Pl r -> Pl ((a,f) :: r))
    (t : @labeled_tree A B) : P t :=
    let fix go t :=
        let fix go_list_pair lp :=
            match lp as _lp return Pl _lp with
            | nil => Hnil
            | (a,f) :: r => Hcons a f r (go f) (go_list_pair r)
            end in
        match t as _t return P _t with
        | tleaf x => Hleaf x
        | tinternal l => Hinternal l (go_list_pair l)
        end in
    go t.

Definition labeled_tree_ind'
  (A B : Type)
    (P : @labeled_tree A B -> Prop)
    (Hleaf : forall x, P (tleaf x))
    (Hinternal : forall l, Forall P (map snd l) -> P (tinternal l))
    (t : @labeled_tree A B) : P t.
  
  eapply labeled_tree_rect_full.
  eapply Hleaf.
  eapply Hinternal.
  econstructor.
  intros. econstructor; eauto.
Defined.

Lemma nonzero_succ_preserved :
  forall t,
    nonzero t ->
    nonzero (map_leaves' S t).
Proof.
  induction t using labeled_tree_ind'; intros.
  - inversion H. subst.
    simpl. econstructor; eauto.
    
  - inversion H0. subst.
    simpl.
    match goal with
    | [ |- nonzero (tinternal (?X l)) ] =>
      replace X with (@go_list_pair nat nat nat S)
    end.
    Focus 2.
    unfold go_list_pair.
    simpl.
    
    reflexivity.
    
    induction l; simpl. econstructor; eauto.
    destruct a. simpl.
    econstructor; eauto.
    simpl.
    simpl in H. inversion H. subst.
    inversion H0. subst.
    simpl in *.
    inversion H3. subst.
    specialize (H4 H7).
    econstructor. eassumption.
    assert (nonzero (tinternal (go_list_pair S l))).
    eapply IHl; eauto. econstructor; eauto.
    inversion H1. eauto.
Qed.
    
