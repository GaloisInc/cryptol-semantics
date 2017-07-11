
(* Verbatim ASTs from cryptol: *)
(* First we need some list notation to match Haskell *)
Open Scope list_scope.
Module HaskellListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Definition  Nothing {A : Type} : option A := None.
End HaskellListNotations.

Import HaskellListNotations.


Fixpoint collect {A : Type} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | Some x :: r =>
    match collect r with
    | Some l' => Some (x :: l')
    | _ => None
    end
  | _ => None
  end.

