
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

