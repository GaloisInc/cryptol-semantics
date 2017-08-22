Require Import String.
Require Import List.
Import ListNotations.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Bitvectors.
Require Import Builtins.


(* An identifier is both a unique identifier and a name, but the name is meaningless *)
Definition ident : Type := Z * string.

(* This definition is what makes the name meaningless *)
(* We leave the name in since it helps with reading ASTs *)
Definition ident_eq :
  forall (x y : ident),
    { fst x = fst y } + { fst x <> fst y }.
Proof.
  decide equality;
  eapply Pos.eq_dec. 
Defined.

Inductive ext_val :=
| ebit (b : bool)
| eseq (l : list ext_val)
| etup (l : list ext_val)
| erec (f : list (string * ext_val))
.

Definition ext_val_rect_mut_full
           (P : ext_val -> Type)
           (Pl : list ext_val -> Type)
           (Pp : string * ext_val -> Type)
           (Plp : list (string * ext_val) -> Type)
           (Hbit : forall b, P (ebit b))
           (Hseq : forall l, Pl l -> P (eseq l))
           (Htup : forall l, Pl l -> P (etup l))
           (Hrec : forall f, Plp f -> P (erec f))
           (Hnil : Pl nil)
           (Hcons : forall e es, P e -> Pl es -> Pl (e :: es))
           (Hpnil : Plp nil)
           (Hpcons : forall se ses, Pp se -> Plp ses -> Plp (se :: ses))
           (Hpair : forall s e, P e -> Pp (s,e))
           (e : ext_val) : P e :=
  let fix go e :=
      let fix go_list es :=
          match es as es_ return Pl es_ with
          | nil => Hnil
          | e :: es => Hcons e es (go e) (go_list es)
          end in
      let go_pair p :=
          let '(s,e) := p in
          Hpair s e (go e) in
      let fix go_pair_list ps :=
          match ps as ps_ return Plp ps_ with
          | nil => Hpnil
          | p :: ps => Hpcons p ps (go_pair p) (go_pair_list ps)
          end in
      match e with
      | ebit b => Hbit b
      | eseq l => Hseq l (go_list l)
      | etup l => Htup l (go_list l)
      | erec f => Hrec f (go_pair_list f)
      end in go e.

Definition ext_val_ind_mut
           (P : ext_val -> Prop)
           (Hbit : forall b, P (ebit b))
           (Hseq : forall l, Forall P l -> P (eseq l))
           (Htup : forall l, Forall P l -> P (etup l))
           (Hrec : forall f, Forall P (map snd f) -> P (erec f))
           (e : ext_val) : P e.
  
  eapply ext_val_rect_mut_full.
  exact Hbit.
  exact Hseq.
  exact Htup.
  exact Hrec.
  econstructor.
  intros. econstructor; eauto.
  simpl. econstructor.
  simpl. intros.
  econstructor; eauto. exact X.
  simpl. intros. assumption.
Defined.

Definition BitV (n : nat) : Type := (@Bitvectors.Int n).

Inductive Kind :=
| KType
| KNum
| KProp
(* | Kind :-> Kind *)
.

Inductive userType :=
| UserTC (id : ident) (k : Kind)
.

Inductive TypeConstr :=
| TCNum (z : Z)
| TCInf
| TCBit
| TCSeq
| TCFun
| TCTuple (n : nat)
| TCNewtype (u : userType)
.

Inductive TFun :=
| TCWidth
| TCAdd
| TCSub
| TCMul
| TCDiv
| TCMod
| TCExp
| TCMin
| TCMax
| TCLenFromThen
| TCLenFromThenTo
.

Inductive TConstr :=
| TC (t : TypeConstr)
| TF (tf : TFun)
.     

Inductive TV_t :=
| TVFree (uid : Z) (k : Kind) (l : list TV_t)
| TVBound (uid : Z) (k : Kind)
.

Inductive Typ :=
| TCon (tc : TConstr) (l : list Typ)
| TVar (tv : TV_t)
| TUser (id : ident) (l : list Typ) (t : Typ)
| TRec (l : list (string * Typ))
.

Definition Typ_rect_full
           (P : Typ -> Type)
           (Pl : list Typ -> Type)
           (Plp : list (string * Typ) -> Type)
           (HTCon : forall tc l, Pl l -> P (TCon tc l))
           (HTVar : forall tv, P (TVar tv))
           (HTUser : forall id l t, Pl l -> P t -> P (TUser id l t))
           (HTRec : forall l, Plp l -> P (TRec l))
           (HPlnil : Pl nil)
           (HPlcons : forall f r, P f -> Pl r -> Pl (f :: r))
           (HPlpnil : Plp nil)
           (HPlpcons : forall s f r, P f -> Plp r -> Plp ((s,f)::r))
           (t : Typ) : P t :=
  let fix go t :=
      let fix go_list l :=
          match l as _l return Pl _l with
          | nil => HPlnil
          | f :: r => HPlcons f r (go f) (go_list r)
          end in
      let fix go_list_pair lp :=
          match lp as _lp return Plp _lp with
          | nil => HPlpnil
          | (s,f) :: r => HPlpcons s f r (go f) (go_list_pair r)
          end in
      match t with
      | TCon tc l => HTCon tc l (go_list l)
      | TVar tv => HTVar tv
      | TUser id l t => HTUser id l t (go_list l) (go t)
      | TRec lp => HTRec lp (go_list_pair lp)
      end in
  go t.

Definition Typ_ind_useful
           (P : Typ -> Prop)
           (HTCon : forall tc l, Forall P l -> P (TCon tc l))
           (HTVar : forall tv, P (TVar tv))
           (HTUser : forall id l t, Forall P l -> P t -> P (TUser id l t))
           (HTRec : forall l, Forall P (map snd l) -> P (TRec l))
           (t : Typ) : P t.
Proof.
  eapply Typ_rect_full.
  eapply HTCon.
  eapply HTVar.
  eapply HTUser.
  eapply HTRec.
  all: intros; econstructor; eauto.
Defined.

(* Type level values *)
Inductive Tval :=
| tvrec (l : list (string * Tval)) (* record *)
| tvtup (l : list Tval) (* tuple *)
| tvseq (len : Tval) (elem : Tval)
| tvfun (argt : Tval) (res : Tval)
| tvnum (z : Z)
| tvbit
| tvinf (* length of infinite streams *)
.


Inductive Expr :=
(* builtin *)
| EBuiltin (b : builtin) (l : list Expr)
(* Literal finite list, e.g. [1,2,3] *)
| EList (l : list Expr)
(* Tuples, e.g. (1,2,3) *)
| ETuple (l : list Expr)
(* Records *)
| ERec (l : list (string * Expr))
(* select: pull one datum out of a record/tuple/list *)
| ESel (e : Expr) (s : Selector)
(* If/then/else, e.g. if cond then t else f *)
| EIf (cond t f : Expr)
(* List Comprehension, e.g. [ p + q | p <- xs | q <- ys ] *)
| EComp (e : Expr) (l : list (list Match))
(* Variable, e.g. 'x' *)
| EVar (id : ident)
(* Type abstraction *)
| ETAbs (id : ident) (e : Expr)
(* Type application *)
| ETApp (e : Expr) (t : Expr)
(* Type *)
| ETyp (t : Typ)
(* Function application, e.g. f v *)
| EApp (f v : Expr)
(* Anonymous function, e.g. \\x -> x *)
| EAbs (id : ident) (e : Expr)
(* MISSING: EProofAbs *)
(* MISSING: EProofApp *)
(* Where, e.g. 1 + x where { x = 2 } *)
| EWhere (e : Expr) (l : list DeclGroup)

(* The following expressions are not in the source langugage, but are *)
(* necessary for evaluation *)
(* list append *)
| EAppend (e1 e2 : Expr)
(* first element of list *)
| EHead (e : Expr)
(* drop first n elements of list, leave the rest *)
| EDrop (n : nat) (e : Expr)
(* take first n elements of a list, throw out rest *)
| ETake (n : nat) (e : Expr)
(* Expression that is a value *)
| EValue (v : ext_val)
(* Lifted evaluation of unary builtin *)
| ELiftUnary (b : builtin) (targs : list Expr) (e : Expr)
(* Lifted evaluation of binary builtin *)             
| ELiftBinary (b : builtin) (targs : list Expr) (e1 e2 : Expr) (env1 env2 : ident -> option val)
(* List Comprehension Implementation: keep track of where you are with a nat *)
| ECompImp (e : Expr) (n : nat) (llm : list (list Match))
with Match :=
     | From (id : ident) (e : Expr)
     | MLet (d : Declaration)
with DeclDef :=
     | DExpr (e : Expr)
     | DPrim
with Declaration := 
     | Decl (id : ident) (d : DeclDef)
with DeclGroup :=
     | Recursive (l : list Declaration)
     | NonRecursive (d : Declaration)
with Selector :=
     | TupleSel (n : nat)
     | ListSel (e : Expr)
     | RecordSel (s : string)
with val :=
     | bit (b : bool) (* Can we ever get this now? *)
     | close (id : ident) (e : Expr) (TE : ident -> option Tval) (E : ident -> option val)  (* closure *)
     | tclose (id : ident) (e : Expr) (TE : ident -> option Tval) (E : ident -> option val) (* type closure *)
     | tuple (l : list val) (* heterogeneous tuples *)
     | rec (l : list (string * val)) (* records *)
     | vcons (v : val) (e : Expr) (TE : ident -> option Tval) (E : ident -> option val) (* lazy list: first val computed, rest is thunked *)
     | vnil (* empty list *)
with strictval :=
     | sbit (b : bool)
     | stuple (l : list strictval) (* heterogeneous tuples *)
     | srec (l : list (string * strictval)) (* records *)
     | sclose (id : ident) (e : Expr) (TE : ident -> option Tval) (E : ident -> option strictval)
     | stclose (id : ident) (e : Expr) (TE : ident -> option Tval) (E : ident -> option strictval)
     | svcons (f r : strictval) 
     | svnil (* empty list *)
.

Fixpoint strict_list (lv : list strictval) : strictval :=
  match lv with
  | nil => svnil
  | f :: r => svcons f (strict_list r)
  end.

Fixpoint list_of_strictval (v : strictval) : option (list strictval) :=
  match v with
  | svnil => Some nil
  | svcons f r =>
    match list_of_strictval r with
    | Some lvr => Some (f :: lvr)
    | _ => None
    end
  | _ => None
  end.

Lemma list_of_strictval_of_strictlist :
  forall l,
    list_of_strictval (strict_list l) = Some l.
Proof.
  induction l; intros; simpl; auto.
  rewrite IHl. reflexivity.
Qed.

Definition extend { vtype : Type } (E : ident -> option vtype) (id : ident) (v : vtype) :=
  fun x => if ident_eq x id then Some v else E x.

Definition genv := ident -> option Expr.
Definition gempty : genv := fun _ => None.

Definition env := ident -> option val.
Definition empty : env := fun _ => None.

Definition senv := ident -> option strictval.
Definition sempty : senv := fun _ => None.

Definition tenv := ident -> option Tval.
Definition tempty : tenv := fun _ => None.

(* Induction principles *)
(* Exprs *)


Definition Expr_mut_rect_full 
           (P : Expr -> Type)
           (Pl : list Expr -> Type)
           (Pllm : list (list Match) -> Type)
           (Plm : list Match -> Type)
           (Pm : Match -> Type)
           (Ppl : list (string * Expr) -> Type)
           (Pd : Declaration -> Type)
           (Pld : list Declaration -> Type)
           (Pdd : DeclDef -> Type)
           (Pg : DeclGroup -> Type)
           (Pldg : list DeclGroup -> Type)
           (HEBuiltin : forall (b : builtin) (l : list Expr), Pl l -> P (EBuiltin b l))
           (HEList : forall l : list Expr, Pl l -> P (EList l))
           (HETuple : forall l : list Expr, Pl l -> P (ETuple l))
           (HERec : forall l : list (string * Expr), Ppl l -> P (ERec l))
           (HESel : forall e : Expr, P e -> forall s : Selector, P (ESel e s))
           (HEIf : forall cond : Expr, P cond -> forall t : Expr, P t -> forall f4 : Expr, P f4 -> P (EIf cond t f4))
           (HEComp : forall e : Expr, P e -> forall l : list (list Match), Pllm l -> P (EComp e l))
           (HEVar : forall id : ident, P (EVar id))
           (HETAbs : forall (id : ident) (e : Expr), P e -> P (ETAbs id e))
           (HETApp : forall e : Expr, P e -> forall t : Expr, P t -> P (ETApp e t))
           (HETyp : forall t : Typ, P (ETyp t))
           (HEApp : forall f : Expr, P f -> forall v : Expr, P v -> P (EApp f v))
           (HEAbs : forall (id : ident) (e : Expr), P e -> P (EAbs id e))
           (HEWhere : forall e : Expr, P e -> forall l : list DeclGroup, Pldg l -> P (EWhere e l))
           (HEAppend : forall e1 : Expr, P e1 -> forall e2 : Expr, P e2 -> P (EAppend e1 e2))
           (HEHead : forall e : Expr, P e -> P (EHead e))
           (HEDrop : forall (n : nat) (e : Expr), P e -> P (EDrop n e))
           (HETake : forall (n : nat) (e : Expr), P e -> P (ETake n e))
           (HEValue : forall v : ext_val, P (EValue v))
           (HELiftUnary : forall (b : builtin) (targs : list Expr) (e : Expr), P e -> Pl targs -> P (ELiftUnary b targs e))
           (HELiftBinary : forall (b : builtin) (targs : list Expr) (e1 : Expr),
               P e1 -> forall e2 : Expr, P e2 -> forall env1 env2 : ident -> option val, Pl targs -> P (ELiftBinary b targs e1 e2 env1 env2))
           (HECompImp : forall e : Expr, P e -> forall (n : nat) (llm : list (list Match)), Pllm llm -> P (ECompImp e n llm))
           (HmFrom : forall id e, P e -> Pm (From id e))
           (HmMlet : forall d, Pd d -> Pm (MLet d))
           (HNonRecursive : forall d, Pd d -> Pg (NonRecursive d))
           (HRecursive : forall ld, Pld ld -> Pg (Recursive ld))
           (HPddPrim : Pdd DPrim)
           (HPddDexpr : forall e, P e -> Pdd (DExpr e))
           (HPddPd : forall id dd, Pdd dd -> Pd (Decl id dd))
           (Hnil : Pl nil)
           (HCons : forall f r, P f -> Pl r -> Pl (f :: r))
           (HPnil : Ppl nil)
           (HPcons : forall s f r, P f -> Ppl r -> Ppl ((s,f) :: r))
           (HPlmnil : Plm nil)
           (HPllmnil : Pllm nil)
           (HPlmcons : forall m l, Pm m -> Plm l -> Plm (m :: l))
           (Hpllmcons : forall ms ls, Plm ms -> Pllm ls -> Pllm (ms :: ls))
           (HPldnil : Pld nil)
           (HPldcons : forall d ds, Pd d -> Pld ds -> Pld (d :: ds))
           (Hldgnil : Pldg nil)
           (Hldgcons : forall f r, Pg f -> Pldg r -> Pldg (f :: r))
           (e : Expr) : 
    P e :=
  let fix go_expr e :=
      let fix go_list l :=
          match l as _l return Pl _l with
          | nil => Hnil
          | f :: r => HCons f r (go_expr f) (go_list r)
          end in
      let fix go_list_pair lp :=
          match lp as _lp return Ppl _lp with
          | nil => HPnil
          | (s,f) :: r => HPcons s f r (go_expr f) (go_list_pair r)
          end in
      let fix go_decldef dd :=
          match dd as _dd return Pdd _dd with
          | DExpr e => HPddDexpr e (go_expr e)
          | DPrim => HPddPrim
          end in
      let fix go_declaration d :=
          match d as _d return Pd _d with
          | Decl id dd => HPddPd id dd (go_decldef dd)
          end in
      let fix go_list_declaration ld :=
          match ld as _ld return Pld _ld with
          | nil => HPldnil
          | (f :: r) => HPldcons f r (go_declaration f) (go_list_declaration r)
          end in
      let fix go_declgroup dg :=
          match dg as _dg return Pg _dg with
          | NonRecursive d => HNonRecursive d (go_declaration d)
          | Recursive ld => HRecursive ld (go_list_declaration ld)
          end in
      let fix go_list_declgroup ldg :=
          match ldg as _ldg return Pldg _ldg with
          | nil => Hldgnil
          | f :: r => Hldgcons f r (go_declgroup f) (go_list_declgroup r)
          end in
      let fix go_match m :=
          match m as _m return Pm _m with
          | From id e => HmFrom id e (go_expr e)
          | MLet d => HmMlet d (go_declaration d) 
          end in
      let fix go_list_match lm :=
          match lm as _lm return Plm _lm with
          | nil => HPlmnil
          | m :: rm => HPlmcons m rm (go_match m) (go_list_match rm)
          end in
      let fix go_list_list_match llm :=
          match llm as _llm return Pllm _llm with
          | nil => HPllmnil
          | ms :: ls => Hpllmcons ms ls (go_list_match ms) (go_list_list_match ls)
          end in
      match e with
      | EBuiltin bi le => HEBuiltin bi le (go_list le)
      | EList le => HEList le (go_list le)
      | ETuple le => HETuple le (go_list le)
      | ERec lp => HERec lp (go_list_pair lp)
      | ESel e s => HESel e (go_expr e) s 
      | EIf eif ethen eelse => HEIf eif (go_expr eif) ethen (go_expr ethen) eelse (go_expr eelse)
      | EComp e llm => HEComp e (go_expr e) llm (go_list_list_match llm)
      | EVar id => HEVar id 
      | ETAbs id e => HETAbs id e (go_expr e)
      | ETApp e1 e2 => HETApp e1 (go_expr e1) e2 (go_expr e2) 
      | ETyp t => HETyp t
      | EApp e1 e2 => HEApp e1 (go_expr e1) e2 (go_expr e2)
      | EAbs id e => HEAbs id e (go_expr e)
      | EWhere e ld => HEWhere e (go_expr e) ld (go_list_declgroup ld) 
      | EAppend e1 e2 => HEAppend e1 (go_expr e1) e2 (go_expr e2)
      | EHead e => HEHead e (go_expr e)
      | EDrop n e => HEDrop n e (go_expr e)
      | ETake n e => HETake n e (go_expr e)
      | EValue v => HEValue v 
      | ELiftUnary bi le e => HELiftUnary bi le e (go_expr e) (go_list le) 
      | ELiftBinary bi targs l r lE rE => HELiftBinary bi targs l (go_expr l) r (go_expr r) lE rE (go_list targs)
      | ECompImp e n llm => HECompImp e (go_expr e) n llm (go_list_list_match llm)
      end in go_expr e.


Definition Pl (P : Expr -> Prop) : list Expr -> Prop :=
  Forall P.

Definition Pdd (P : Expr -> Prop) : DeclDef -> Prop :=
  fun dd =>
    match dd with
    | DExpr e => P e
    | DPrim => True
    end.

Definition Pd (P : Expr -> Prop) : Declaration -> Prop :=
  fun d => match d with
           | Decl _ dd => Pdd P dd
           end.

Definition Pld (P : Expr -> Prop) : list Declaration -> Prop :=
  Forall (Pd P).

Definition Pg (P : Expr -> Prop) : DeclGroup -> Prop :=
  fun dg =>
    match dg with
    | Recursive l => Pld P l
    | NonRecursive d => Pd P d
    end.
                           
Definition Pldg (P : Expr -> Prop) : list DeclGroup -> Prop :=
  Forall (Pg P).

Definition Pm (P : Expr -> Prop) : Match -> Prop :=
  fun m =>
    match m with
    | MLet d => Pd P d
    | From _ e => P e
    end.

Definition Plm (P : Expr -> Prop) : list Match -> Prop :=
  Forall (Pm P).

Definition Pllm (P : Expr -> Prop) : list (list Match) -> Prop :=
  Forall (Plm P).

Definition Ppl {A : Type} (P : Expr -> Prop) : list (A * Expr) -> Prop :=
  fun l => Forall P (map snd l).

Definition Expr_ind_useful 
           (P : Expr -> Prop)
           (HEBuiltin : forall (b : builtin) (l : list Expr), (Pl P) l -> P (EBuiltin b l))
           (HEList : forall l : list Expr, (Pl P) l -> P (EList l))
           (HETuple : forall l : list Expr, (Pl P) l -> P (ETuple l))
           (HERec : forall l : list (string * Expr), (Ppl P) l -> P (ERec l))
           (HESel : forall e : Expr, P e -> forall s : Selector, P (ESel e s))
           (HEIf : forall cond : Expr, P cond -> forall t : Expr, P t -> forall f4 : Expr, P f4 -> P (EIf cond t f4))
           (HEComp : forall e : Expr, P e -> forall l : list (list Match), (Pllm P) l -> P (EComp e l))
           (HEVar : forall id : ident, P (EVar id))
           (HETAbs : forall (id : ident) (e : Expr), P e -> P (ETAbs id e))
           (HETApp : forall e : Expr, P e -> forall t : Expr, P t -> P (ETApp e t))
           (HETyp : forall t : Typ, P (ETyp t))
           (HEApp : forall f : Expr, P f -> forall v : Expr, P v -> P (EApp f v))
           (HEAbs : forall (id : ident) (e : Expr), P e -> P (EAbs id e))
           (HEWhere : forall e : Expr, P e -> forall l : list DeclGroup, (Pldg P) l -> P (EWhere e l))
           (HEAppend : forall e1 : Expr, P e1 -> forall e2 : Expr, P e2 -> P (EAppend e1 e2))
           (HEHead : forall e : Expr, P e -> P (EHead e))
           (HEDrop : forall (n : nat) (e : Expr), P e -> P (EDrop n e))
           (HETake : forall (n : nat) (e : Expr), P e -> P (ETake n e))
           (HEValue : forall v : ext_val, P (EValue v))
           (HELiftUnary : forall (b : builtin) (targs : list Expr) (e : Expr), P e -> (Pl P) targs -> P (ELiftUnary b targs e))
           (HELiftBinary : forall (b : builtin) (targs : list Expr) (e1 : Expr),
               P e1 -> forall e2 : Expr, P e2 -> forall env1 env2 : ident -> option val, (Pl P) targs -> P (ELiftBinary b targs e1 e2 env1 env2))
           (HECompImp : forall e : Expr, P e -> forall (n : nat) (llm : list (list Match)), (Pllm P) llm -> P (ECompImp e n llm))
           (HmFrom : forall id e, P e -> (Pm P) (From id e))
           (HmMlet : forall d, (Pd P) d -> (Pm P) (MLet d))
           (HNonRecursive : forall d, (Pd P) d -> (Pg P) (NonRecursive d))
           (HRecursive : forall ld, (Pld P) ld -> (Pg P) (Recursive ld))
           (HPddPrim : (Pdd P) DPrim)
           (HPddDexpr : forall e, P e -> (Pdd P) (DExpr e))
           (HPddPd : forall id dd, (Pdd P) dd -> (Pd P) (Decl id dd))
           (e : Expr) : 
    P e .
Proof.
  eapply Expr_mut_rect_full; try solve [eassumption].
  all: try (  instantiate (1 := Plm P));
    intros; econstructor; eauto.
Defined.



(* strictvals *)

(* vals *)
