Require Import List.
Import ListNotations.
Require Import String.

Require Import Cryptol.Coqlib.
Require Import Cryptol.Bitvectors.

Require Import Cryptol.AST.
Require Import Cryptol.Semantics.
Require Import Cryptol.Utils.
Require Import Cryptol.Builtins.
Require Import Cryptol.BuiltinSem.
Require Import Cryptol.Values.        
Require Import Cryptol.Bitstream.

Require Import Cryptol.EvalTac.
Require Import Cryptol.Eager.
 
Import HaskellListNotations.
Open Scope string.
Require Import HMAC.HMAC_lib. 

Require Import otp.OTP_cryptol. 


Fixpoint xor_ext (l1 l2 : list ext_val) : option (list ext_val) := 
  match l1 with 
  | (ebit x :: xs) => match l2 with
       | (ebit y :: ys) => match (xor_ext xs ys) with 
             | Some bs => Some ((ebit (xorb x y)) :: bs)
             | _ => None
             end
       | [] => Some []
       | _ => None
       end
  | [] => Some []
  | _ => None
  end. 

Definition xor_ext' (x y : ext_val) : ext_val :=
  match x with 
  | eseq l1 => match y with 
    | eseq l2 => match xor_ext l1 l2 with
       | Some bs => eseq bs
       | _ => ebit false
       end
    | _ => ebit false
    end
  | _ => ebit false
  end.

Definition otp_encrypt (key msg : ext_val) : ext_val :=
  xor_ext' key msg.
  

Lemma length_cons : forall {A : Type} n x (xs : list A), 
  Datatypes.length xs = n <-> 
  Datatypes.length (x::xs) = S n.
Proof.
  split. 
  - destruct n; intros.
    + rewrite length_zero_iff_nil in H. subst. simpl. reflexivity.
    + inversion H. simpl. reflexivity.
  - intros. inversion H. reflexivity.  
Qed.

Lemma bool_destr : forall (b: bool),
    (if b then true else false) = b. 
Proof. 
  destruct b; auto. 
Qed.


Theorem otp_equiv :
  forall key msg,
    (* key is the right type *)
    has_type key byte ->
    (* msg is the right type *)
    has_type msg byte ->
    (* applying the encrypt function to the key and value gives the model *)
    eager_eval_expr ge tempty sempty
                    (EApp (EApp (EVar encrypt) (EValue key)) (EValue msg))
                    (to_sval (otp_encrypt key msg)).
Proof.
  intros.
  (* break apart bytes into elements *)
  inversion H. do 9 (destruct l; simpl in H1; try omega).
  inversion H0. do 9 (destruct l; simpl in H5; try omega).
  subst.
  (* each element is a bit *)
  repeat match goal with
         | [ H : Forall _ _ |- _ ] => inversion H; clear H
         end;
    repeat match goal with
           | [ H : has_type _ tbit |- _ ] => inversion H; clear H
           end;
    subst.

  (* evaluate the function *)
  e. e. g. e. e. e. e. e. e. e.
  g.
  e. e. lv. e. lv. e.
  lv. lv.
  simpl. unfold xorb.
  repeat rewrite bool_destr.
  reflexivity.
Qed.
