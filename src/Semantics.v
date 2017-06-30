Require Import String.
Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

(* Borrow from CompCert *)
Require Import Coqlib.

(*Require Import Integers.*)
Require Import Bitvectors.
Require Import AST.
Require Import Builtins.
Require Import Values.
Require Import BuiltinSem.

Open Scope list_scope.

Fixpoint declare (l : list Declaration) (ge : genv) :=
  match l with
  | nil => ge
  | (Decl id (DExpr e)) :: r =>
    declare r (extend ge id e)
  | (Decl id DPrim) :: r =>
    match lookup_prim id with
    | Some exp =>
      declare r (extend ge id exp)
    | None => declare r ge (* TODO: maybe handle this as an error? *)
    end
  end.

Definition bind_decl_group (g : DeclGroup) (ge : genv) : genv :=
  match g with
  | Recursive l => declare l ge
  | NonRecursive d => declare (d :: nil) ge
  end.

Fixpoint bind_decl_groups (lg : list DeclGroup) (ge : genv) : genv :=
  match lg with
  | nil => ge
  | g :: gs =>
    bind_decl_groups gs (bind_decl_group g ge)
  end.


(* record lookup *)
Fixpoint lookup (str : string) (l : list (string * val)) : option val :=
  match l with
  | nil => None
  | (s,v) :: r =>
    if string_dec str s then Some v else lookup str r
  end.

Inductive Forall3 {A B C : Type} (TR : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
| Forall3_nil :
    Forall3 TR [] [] []
| Forall3_cons :
    forall x y z lx ly lz,
      TR x y z ->
      Forall3 TR lx ly lz ->
      Forall3 TR (x :: lx) (y :: ly) (z :: lz).

  


Inductive eval_expr (ge : genv) : env -> Expr -> val -> Prop :=
| eval_builtin_sem :
    forall E l b v,
      eval_builtin ge E b l v ->
      eval_expr ge E (EBuiltin b l) v
| eval_list :
    forall E l vs vres,
      Forall2 (eval_expr ge E) l vs ->
      vres = thunk_list vs ->
      eval_expr ge E (EList l) vres
| eval_tuple :
    forall E l vs,
      Forall2 (eval_expr ge E) l vs ->
      eval_expr ge E (ETuple l) (tuple vs)
| eval_tuple_sel :
    forall E e l n v,
      eval_expr ge E e (tuple l) ->
      nth_error l n = Some v ->
      eval_expr ge E (ESel e (TupleSel n)) v
| eval_record :
    forall E l vs,
      Forall2 (eval_expr ge E) (map snd l) vs ->
      eval_expr ge E (ERec l) (rec (combine (map fst l) vs))
| eval_record_sel :
    forall E l str v e,
      eval_expr ge E e (rec l) ->
      lookup str l = Some v ->
      eval_expr ge E (ESel e (RecordSel str)) v
| eval_if :
    forall E c t f v b,
      eval_expr ge E c (bit b) ->
      eval_expr ge E (if b then t else f) v ->
      eval_expr ge E (EIf c t f) v
| eval_local_var :
    forall E id v,
      E id = Some v ->
      eval_expr ge E (EVar id) v
| eval_global_var :
    forall E id v exp,
      E id = None ->
      ge id = Some exp ->
      eval_expr ge E exp v ->
      eval_expr ge E (EVar id) v
| eval_abs :
    forall E id exp,
      eval_expr ge E (EAbs id exp) (close id exp E)
| eval_app :
    forall E f id exp E' a av v,
      eval_expr ge E f (close id exp E') ->
      eval_expr ge E a av ->
      eval_expr ge (extend E' id av) exp v ->
      eval_expr ge E (EApp f a) v
| eval_where : (* TODO: this might not get scoping right, as decls might not shadow existing locals correctly *)
    forall E exp decls v, 
      eval_expr (bind_decl_groups decls ge) E exp v ->
      eval_expr ge E (EWhere exp decls) v
| eval_list_sel :
    forall E idx vidx {w : nat} (i : BitV w) e v vs,
      eval_expr ge E idx vidx ->
      force_list ge E vidx vs ->
      to_bitv vs = Some i ->
      select_list ge E (Z.to_nat (unsigned i)) e v ->
      eval_expr ge E (ESel e (ListSel idx)) v
| eval_tapp :
    forall E e id e' E' v t te,
      eval_expr ge E e (tclose id e' E') ->
      eval_expr ge E te (typ t) -> 
      eval_expr ge (extend E' id (typ t)) e' v ->
      eval_expr ge E (ETApp e te) v
| eval_typ :
    forall E t,
      eval_expr ge E (ETyp t) (typ t)
| eval_tabs :
    forall E e id,
      eval_expr ge E (ETAbs id e) (tclose id e E)
| eval_append_nil :
    forall E e1 e2 v,
      eval_expr ge E e1 vnil ->
      eval_expr ge E e2 v ->
      eval_expr ge E (EAppend e1 e2) v
| eval_append_cons :
    forall v eR ER E  vfirst vrest E' e1 e2,
      eval_expr ge E e1 (vcons v eR ER) ->
      eval_expr ge ER eR vfirst ->
      eval_expr ge E e2 vrest ->
      E' = extend (extend empty (1,"first") vfirst) (0,"rest") vrest ->
      eval_expr ge E (EAppend e1 e2) (vcons v (EAppend (EVar (1,"first")) (EVar (0,"rest"))) E')
| eval_head :
    forall E e v e' E',
      eval_expr ge E e (vcons v e' E') ->
      eval_expr ge E (EHead e) v
| eval_tail_zero :
    forall E e v e' E',
      eval_expr ge E e (vcons v e' E') ->
      eval_expr ge E (ETail O e) v
| eval_tail_succ :
    forall E e v e' E' n v',
      eval_expr ge E e (vcons v e' E') ->
      eval_expr ge E' (ETail n e') v' ->
      eval_expr ge E (ETail (S n) e) v'
| eval_value :
    forall E v,
      eval_expr ge E (EValue v) v
(* Force complete evaluation of a lazy list *)
(* Used for converting a list of bits into a number to evaluate arithmetic *)
with force_list (ge : genv) : env -> val -> list val -> Prop :=
     | force_nil :
         forall E,
           force_list ge E vnil nil
     | force_cons :
         forall E E' e v v' l,
           eval_expr ge E' e v' ->
           force_list ge E v' l ->
           force_list ge E (vcons v e E') (v::l)
                
(* select the nth element from a lazy list *)
with select_list (ge : genv) : env -> nat -> Expr -> val -> Prop :=
     | select_zero :
         forall E e v re rE,
           eval_expr ge E e (vcons v re rE) ->
           select_list ge E O e v
     | select_succ :
         forall E e v re rE n v',
           eval_expr ge E e (vcons v' re rE) ->
           select_list ge rE n re v ->
           select_list ge E (S n) e v
(*     | select_comp :
         forall E e compExp compE llm n E' v,
           eval_expr ge E e (vcomp compExp compE llm) ->
           par_match ge compE n llm E' ->
           eval_expr ge E' compExp v ->
           select_list ge E n e v
     | select_app_1 :
         forall E e e1 e2 AE n v,
           eval_expr ge E e (vapp  e1 e2 AE) ->
           select_list ge AE n e1 v ->
           select_list ge E n e v
     | select_app_2 :
         forall E e e1 e2 AE n v m k,
           eval_expr ge E e (vapp e1 e2 AE) ->
           length ge AE e1 m ->
           select_list ge AE k e2 v ->
           n = (m + k)%nat ->
           select_list ge E n e v
     | select_slice :
         forall E e lo hi lexp AE n k v,
           eval_expr ge E e (vslice lo hi lexp AE) ->
           k = (lo + n)%nat ->
           select_list ge AE k lexp v ->
           select_list ge E n e v
     | select_split : (* yields a slice, gets selected again *)
         forall E e k j lexp AE lo hi n,
           eval_expr ge E e (vsplit k j lexp AE) ->
           lo = (n * (Z.to_nat j))%nat ->
           hi = (lo + (Z.to_nat j))%nat ->
           select_list ge E n e (vslice lo hi lexp AE)
*)
(*
with par_match (ge : genv) : env -> nat -> list (list Match) -> env -> Prop :=
     | par_one :
         forall E n,
           par_match ge E n nil E
     | par_more :
         forall E n lm E' lr E'',
           index_match ge E n lm E' ->
           par_match ge E' n lr E'' ->
           par_match ge E n (lm :: lr) E''
(* provide the nth bound environment for one part of a list comprehension *)
with index_match (ge : genv) : env -> nat -> list Match -> env -> Prop :=
     | idx_last : (* take the nth element from the last list *)
         forall E n id e v,
           select_list ge E n e v ->
           index_match ge E n ((From id e) :: nil) (extend E id v)
     | idx_mid : (* take the mid element from *)
         forall E E' n r v id e m t len,
           index_match ge E n r E' ->
           select_list ge E (S m) e v ->
           matchlength ge E r len ->
           (* m * matchlength r  + n *)
           t = (((S m) * len) + n)%nat ->
           index_match ge E t ((From id e) :: r) (extend E' id v)
     | idx_first :
         forall E n r E' v id e,
           index_match ge E n r E' ->
           select_list ge E O e v ->
           index_match ge E n ((From id e) :: r) (extend E' id v)
with matchlength (ge : genv) : env -> list Match -> nat -> Prop :=
     | len_one :
         forall E id e n,
           length ge E e n ->
           matchlength ge E ((From id e) :: nil) n
     | len_more :
         forall E id e r n l m,
           matchlength ge E r n ->
           length ge E e m ->
           l = (m * n)%nat ->
           matchlength ge E ((From id e) :: r) l
with length (ge : genv) : env -> Expr -> nat -> Prop :=
     | len_nil :
         forall E e,
           eval_expr ge E e vnil ->
           length ge E e O
     | len_cons :
         forall E e v rE re n,
           eval_expr ge E e (vcons v re rE) ->
           length ge rE re n ->
           length ge E e (S n)
*)
with eval_builtin (ge : genv) : env -> builtin -> list Expr -> val -> Prop :=
(* | eval_demote : *)
(*     forall {ws : nat} (w n : Z) (b : BitV ws), *)
(*       ws = Z.to_nat w -> *)
(*       b = @repr ws n -> *)
(*       eval_builtin ge Demote ((typ (TCon (TC (TCNum n)) nil)) :: (typ (TCon (TC (TCNum w)) nil)) :: nil) (bits b) *)
| eval_plus_base : (* evaluate plus over bitvectors *)
    forall {w} (b1 b2 : BitV w) E v1 v2 v3 l1 l2 t e1 e2,
      (* TODO: eval_expr t (bitv_type w)*)
      eval_expr ge E e1 v1 ->
      eval_expr ge E e2 v2 ->
      force_list ge E v1 l1 ->
      force_list ge E v2 l2 ->
      to_bitv l1 = Some b1 ->
      to_bitv l2 = Some b2 ->
      v3 = thunk_list (from_bitv (add b1 b2)) ->
      eval_builtin ge E Plus (t :: e1 :: e2 :: nil) (v3)
| eval_at_vnil : (* This case seems weird, but it's necessary (cryptol does this) *)
    forall E l v t1 t2 t3 idx,
      select_list ge E O l v ->
      eval_expr ge E idx vnil ->
      eval_builtin ge E At (t1 :: t2 :: t3 :: l :: idx :: nil) v
| eval_true :
    forall E,
      eval_builtin ge E true_builtin nil (bit true)
| eval_false :
    forall E,
      eval_builtin ge E false_builtin nil (bit false)
| eval_lift_over_2_lists :
    forall E l1 vs1 l2 vs2 v targs largs bi lv1 lv2 vl,
      (* is_binary_builtin bi -> *)
      largs = targs ++ (l1 :: l2 :: nil) -> (* last 2 are the values, could be arbitrary # of type args *)
      eval_expr ge E l1 lv1 ->
      eval_expr ge E l2 lv2 ->
      force_list ge E lv1 vs1 ->
      force_list ge E lv2 vs2 ->
      Forall3 (fun a1 => fun a2 => fun v => eval_builtin ge E bi (targs ++ a1 :: a2 :: nil) v) (map EValue vs1) (map EValue vs2) vl ->
      v = thunk_list vl ->
      eval_builtin ge E bi largs v
(* | eval_minus : *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @sub w b1 b2 -> *)
(*       eval_builtin ge Minus (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* | eval_times : *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @mul w b1 b2 -> *)
(*       eval_builtin ge Times (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* | eval_div : *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @divu w b1 b2 -> (* I assume that division is unsigned in cryptol *) *)
(*       unsigned b2 <> 0 -> (* no division by 0 *) *)
(*       eval_builtin ge Div (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* | eval_mod : *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @modu w b1 b2 -> *)
(*       eval_builtin ge Mod (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* (* | eval_exp : *) (* TODO: write pow over bits, or implement in Cryptol *) *)
(* (*     forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t, *) *)
(* (*       b3 = @exp w nz b1 b2 -> *) *)
(* (*       eval_builtin ge Exp (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *) *)
(* (* | eval_lg2 : *) (* TODO: what is lg2? log base 2? *) *)
(* (*     forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t, *) *)
(* (*       b3 = @lg2 w nz b1 b2 -> *) *)
(* (*       eval_builtin ge lg2 (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *) *)
(* | eval_negate : *)
(*     forall {w : nat} (b1 b2 : BitV w) t, *)
(*       b2 = @neg w b1 -> *)
(*       eval_builtin ge Neg (t :: (bits b1) :: nil) (bits b2) *)
(* | eval_compl : *)
(*     forall {w : nat} (b1 b2 : BitV w) t, *)
(*       b2 = @not w b1 -> *)
(*       eval_builtin ge Compl (t :: (bits b1) :: nil) (bits b2) *)
(* | eval_lt : *)
(*     forall {w : nat} (b1 b2 : BitV w) (b : bool) t, *)
(*       b = @ltu w b1 b2 -> *)
(*       eval_builtin ge Lt (t :: (bits b1) :: (bits b2) :: nil) (bit b) *)
(* | eval_gt : *)
(*     forall {w : nat} (b1 b2 : BitV w) (b : bool) t, *)
(*       b = @gtu w b1 b2 -> *)
(*       eval_builtin ge Gt (t :: (bits b1) :: (bits b2) :: nil) (bit b) *)
(* | eval_le :   *)
(*     forall {w : nat} (b1 b2 : BitV w) (b : bool) t, *)
(*       b = @leu w b1 b2 -> *)
(*       eval_builtin ge Le (t :: (bits b1) :: (bits b2) :: nil) (bit b) *)
(* | eval_ge : *)
(*     forall {w : nat} (b1 b2 : BitV w) (b : bool) t, *)
(*       b = @geu w b1 b2 -> *)
(*       eval_builtin ge Ge (t :: (bits b1) :: (bits b2) :: nil) (bit b) *)
(* | eval_eq : *)
(*     forall {w : nat} (b1 b2 : BitV w) (b : bool) t, *)
(*       b = @eq w b1 b2 -> *)
(*       eval_builtin ge Eq (t :: (bits b1) :: (bits b2) :: nil) (bit b) *)
(* | eval_neq : *)
(*     forall {w : nat} (b1 b2 : BitV w) (b : bool) t, *)
(*       b = @neq w b1 b2 -> *)
(*       eval_builtin ge Neq (t :: (bits b1) :: (bits b2) :: nil) (bit b) *)
(* | eval_and : *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @and w b1 b2 -> *)
(*       eval_builtin ge And (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* | eval_or : *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @or w b1 b2 -> *)
(*       eval_builtin ge Or (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* | eval_xor : *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @xor w b1 b2 -> *)
(*       eval_builtin ge Xor (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* | eval_zero : (* TODO: cryptol's builtin zero works in more cases than this *) *)
(*     forall {ws : nat} (w : Z) (b : BitV ws), *)
(*       ws = Z.to_nat w -> *)
(*       b = @repr ws 0 ->  *)
(*       eval_builtin ge Zero ((typ (TCon (TC (TCNum w)) nil)) :: nil) (bits b) *)
(* | eval_shiftl : *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @shl w b1 b2 -> *)
(*       eval_builtin ge Shiftl (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* | eval_shiftr : *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @shru w b1 b2 -> *)
(*       eval_builtin ge Shiftr (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* | eval_rotl :     *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @rol w b1 b2 -> *)
(*       eval_builtin ge Rotl (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* | eval_rotr :     *)
(*     forall {w : nat} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @ror w b1 b2 -> *)
(*       eval_builtin ge Rotr (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
(* (*                    *)
(* | eval_append : *)
(*     forall E t1 t2 t3 v1 v2 e1 e2, *)
(*       e1 = EVar (1,"") -> *)
(*       e2 = EVar (2,"") -> *)
(*       E = extend (extend empty (1,"") v1) (2,"") v2  -> *)
(*       eval_expr ge E (EAppend e1 e2) v -> *)
(*       eval_builtin ge Append (t1 :: t2 :: t3 :: v1 :: v2 :: nil) v *) *)
(* | eval_at_bits : *)
(*     forall {w : nat} E n e v t1 t2 t3 v1 (b : BitV w), *)
(*       select_list ge E n e v -> *)
(*       E = extend empty (0,"") v1 -> *)
(*       e = EVar (0,"") -> *)
(*       n = Z.to_nat (unsigned b) -> *)
(*       eval_builtin ge At (t1 :: t2 :: t3 :: v1 :: (bits b) :: nil) v *)
(*| eval_splitAt :
    forall E e v front back t,
      E = extend empty (1,"") v ->
      e = EVar (1,"") ->
      eval_builtin ge splitAt ((typ (TCon (TC (TCNum front)) nil)) :: (typ (TCon (TC (TCNum back)) nil)) :: t :: v :: nil)
                   (tuple ((vslice O (Z.to_nat front) e E) :: (vslice (Z.to_nat front) (Z.to_nat (front + back)) e E) :: nil))
| eval_split :
    forall E e v n m t,
      E = extend empty (1,"") v ->
      e = EVar (1,"") ->
      eval_builtin ge split ((typ (TCon (TC (TCNum n)) nil)) :: (typ (TCon (TC (TCNum m)) nil)) :: t :: v :: nil)
                   (vsplit n m e E)*)
(*| eval_join : *)
(* Produces the one dimensional cartesian product of a 2 dimensional sequence *)
(* sorta like a list comprehension *)
    
.


