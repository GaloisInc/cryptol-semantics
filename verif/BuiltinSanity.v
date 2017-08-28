Require Import Cryptol.BuiltinSyntax.
Require Import String.

(* Sanity check to make sure all the prims are in the table above *)
Lemma id_for_all_prims :
  forall p,
  exists s x y,
    lookup s table = Some (mb x y p).
Proof.
  intros. 
  unfold table.

  destruct p;
    unfold lookup;
    do 3 eexists;
  match goal with
  | [ |- context[if string_dec ?X ?Y then _ else _] ] => instantiate (3 := X); reflexivity
  end.

Qed.

