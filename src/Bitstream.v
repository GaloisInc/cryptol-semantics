
Require Import AST.

(* any finite bitstream *)
(* use to state correctness of crypto functions *)
Inductive finite_bitstream : list val -> Prop :=
| empty_stream :
    finite_bitstream nil
| one_more :
    forall b l,
      finite_bitstream l ->
      finite_bitstream (bit b :: l).

(* bits with length encoded *)
Inductive n_bits : nat -> list val -> Prop :=
| empty_bits :
    n_bits O nil
| another_bit :
    forall n l b,
      n_bits n l ->
      n_bits (S n) (bit b :: l).