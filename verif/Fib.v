
(* DONE        Change .cry so it uses + and (-) 
   DONE (?)    Figure out numbers for Plus, Eq, Neg
   PARTIAL     Use tactics to finish proofs
   DONE        Write Fib in coq (using 32 bit nats from compcert library)
   PARTIAL     Prove equivalence of Fib implementations
*)




Require Import List.
Import ListNotations.

(* Borrow from CompCert *)
Require Import Coqlib.

Require Import Bitvectors.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.
Require Import BuiltinSem. 
Require Import Values.    
Require Import BuiltinSanity. 
Require Import EvalTac. 

(* right side of this generated from cryptol implementation *)

Import HaskellListNotations.



Definition fib_cry := [(NonRecursive (Decl (242,"demote") DPrim)),(NonRecursive (Decl (243,"+") DPrim)),(NonRecursive (Decl (244,"-") DPrim)),(NonRecursive (Decl (245,"*") DPrim)),(NonRecursive (Decl (246,"/") DPrim)),(NonRecursive (Decl (247,"%") DPrim)),(NonRecursive (Decl (248,"^^") DPrim)),(NonRecursive (Decl (249,"lg2") DPrim)),(NonRecursive (Decl (251,"True") DPrim)),(NonRecursive (Decl (252,"False") DPrim)),(NonRecursive (Decl (253,"negate") DPrim)),(NonRecursive (Decl (254,"complement") DPrim)),(NonRecursive (Decl (255,"<") DPrim)),(NonRecursive (Decl (256,">") DPrim)),(NonRecursive (Decl (257,"<=") DPrim)),(NonRecursive (Decl (258,">=") DPrim)),(NonRecursive (Decl (259,"==") DPrim)),(NonRecursive (Decl (260,"!=") DPrim)),(NonRecursive (Decl (261,"===") (DExpr (ETAbs (329,"a") (ETAbs (330,"b") (EAbs (331,"f") (EAbs (332,"g") (EAbs (333,"x") (EApp (EApp (ETApp (EVar (259,"==")) (TVar (TVBound 31 KType))) (EApp (EVar (331,"f")) (EVar (333,"x")))) (EApp (EVar (332,"g")) (EVar (333,"x")))))))))))),(NonRecursive (Decl (262,"!==") (DExpr (ETAbs (334,"a") (ETAbs (335,"b") (EAbs (336,"f") (EAbs (337,"g") (EAbs (338,"x") (EApp (EApp (ETApp (EVar (260,"!=")) (TVar (TVBound 41 KType))) (EApp (EVar (336,"f")) (EVar (338,"x")))) (EApp (EVar (337,"g")) (EVar (338,"x")))))))))))),(NonRecursive (Decl (263,"min") (DExpr (ETAbs (339,"a") (EAbs (340,"x") (EAbs (341,"y") (EIf (EApp (EApp (ETApp (EVar (255,"<")) (TVar (TVBound 50 KType))) (EVar (340,"x"))) (EVar (341,"y"))) (EVar (340,"x")) (EVar (341,"y"))))))))),(NonRecursive (Decl (264,"max") (DExpr (ETAbs (342,"a") (EAbs (343,"x") (EAbs (344,"y") (EIf (EApp (EApp (ETApp (EVar (256,">")) (TVar (TVBound 56 KType))) (EVar (343,"x"))) (EVar (344,"y"))) (EVar (343,"x")) (EVar (344,"y"))))))))),(NonRecursive (Decl (265,"/\\") (DExpr (EAbs (345,"x") (EAbs (346,"y") (EIf (EVar (345,"x")) (EVar (346,"y")) (EVar (252,"False")))))))),(NonRecursive (Decl (266,"\\/") (DExpr (EAbs (347,"x") (EAbs (348,"y") (EIf (EVar (347,"x")) (EVar (251,"True")) (EVar (348,"y")))))))),(NonRecursive (Decl (267,"==>") (DExpr (EAbs (349,"a") (EAbs (350,"b") (EIf (EVar (349,"a")) (EVar (350,"b")) (EVar (251,"True")))))))),(NonRecursive (Decl (268,"&&") DPrim)),(NonRecursive (Decl (269,"||") DPrim)),(NonRecursive (Decl (270,"^") DPrim)),(NonRecursive (Decl (271,"zero") DPrim)),(NonRecursive (Decl (272,"<<") DPrim)),(NonRecursive (Decl (273,">>") DPrim)),(NonRecursive (Decl (274,"<<<") DPrim)),(NonRecursive (Decl (275,">>>") DPrim)),(NonRecursive (Decl (276,"#") DPrim)),(NonRecursive (Decl (277,"splitAt") DPrim)),(NonRecursive (Decl (278,"join") DPrim)),(NonRecursive (Decl (279,"split") DPrim)),(NonRecursive (Decl (280,"reverse") DPrim)),(NonRecursive (Decl (281,"transpose") DPrim)),(NonRecursive (Decl (282,"@") DPrim)),(NonRecursive (Decl (283,"@@") DPrim)),(NonRecursive (Decl (284,"!") DPrim)),(NonRecursive (Decl (285,"!!") DPrim)),(NonRecursive (Decl (286,"update") DPrim)),(NonRecursive (Decl (287,"updateEnd") DPrim)),(NonRecursive (Decl (288,"updates") (DExpr (ETAbs (404,"a") (ETAbs (405,"b") (ETAbs (406,"c") (ETAbs (407,"d") (EAbs (408,"xs0") (EAbs (409,"idxs") (EAbs (410,"vals") (EWhere (EApp (EApp (ETApp (ETApp (ETApp (EVar (284,"!")) (TCon (TF TCAdd) [TCon (TC (TCNum 1)) [],TVar (TVBound 124 KNum)])) (TCon (TC TCSeq) [TVar (TVBound 121 KNum),TVar (TVBound 122 KType)])) (TCon (TC (TCNum 0)) [])) (EVar (411,"xss"))) (ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 0)) []))) [(Recursive [(Decl (411,"xss") (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar (276,"#")) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 124 KNum))) (TCon (TC TCSeq) [TVar (TVBound 121 KNum),TVar (TVBound 122 KType)])) (EList [(EVar (408,"xs0"))])) (EComp (EApp (EApp (EApp (ETApp (ETApp (ETApp (EVar (286,"update")) (TVar (TVBound 121 KNum))) (TVar (TVBound 122 KType))) (TVar (TVBound 123 KNum))) (EVar (412,"xs"))) (EVar (413,"i"))) (EVar (414,"b"))) [[(From (412,"xs") (EVar (411,"xss")))],[(From (413,"i") (EVar (409,"idxs")))],[(From (414,"b") (EVar (410,"vals")))]]))))])]))))))))))),(NonRecursive (Decl (289,"updatesEnd") (DExpr (ETAbs (415,"a") (ETAbs (416,"b") (ETAbs (417,"c") (ETAbs (418,"d") (EAbs (419,"xs0") (EAbs (420,"idxs") (EAbs (421,"vals") (EWhere (EApp (EApp (ETApp (ETApp (ETApp (EVar (284,"!")) (TCon (TF TCAdd) [TCon (TC (TCNum 1)) [],TVar (TVBound 159 KNum)])) (TCon (TC TCSeq) [TVar (TVBound 156 KNum),TVar (TVBound 157 KType)])) (TCon (TC (TCNum 0)) [])) (EVar (422,"xss"))) (ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 0)) []))) [(Recursive [(Decl (422,"xss") (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar (276,"#")) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 159 KNum))) (TCon (TC TCSeq) [TVar (TVBound 156 KNum),TVar (TVBound 157 KType)])) (EList [(EVar (419,"xs0"))])) (EComp (EApp (EApp (EApp (ETApp (ETApp (ETApp (EVar (287,"updateEnd")) (TVar (TVBound 156 KNum))) (TVar (TVBound 157 KType))) (TVar (TVBound 158 KNum))) (EVar (423,"xs"))) (EVar (424,"i"))) (EVar (425,"b"))) [[(From (423,"xs") (EVar (422,"xss")))],[(From (424,"i") (EVar (420,"idxs")))],[(From (425,"b") (EVar (421,"vals")))]]))))])]))))))))))),(NonRecursive (Decl (290,"fromThen") DPrim)),(NonRecursive (Decl (291,"fromTo") DPrim)),(NonRecursive (Decl (292,"fromThenTo") DPrim)),(NonRecursive (Decl (293,"infFrom") DPrim)),(NonRecursive (Decl (294,"infFromThen") DPrim)),(NonRecursive (Decl (295,"error") DPrim)),(NonRecursive (Decl (296,"pmult") DPrim)),(NonRecursive (Decl (297,"pdiv") DPrim)),(NonRecursive (Decl (298,"pmod") DPrim)),(NonRecursive (Decl (299,"random") DPrim)),(NonRecursive (Decl (303,"take") (DExpr (ETAbs (451,"front") (ETAbs (452,"back") (ETAbs (453,"elem") (EAbs (454,"__p1") (EWhere (EVar (456,"x")) [(NonRecursive (Decl (455,"__p2") (DExpr (EApp (ETApp (ETApp (ETApp (EVar (277,"splitAt")) (TVar (TVBound 214 KNum))) (TVar (TVBound 215 KNum))) (TVar (TVBound 216 KType))) (EVar (454,"__p1")))))),(NonRecursive (Decl (456,"x") (DExpr (ESel (EVar (455,"__p2")) (TupleSel 0))))),(NonRecursive (Decl (457,"__p0") (DExpr (ESel (EVar (455,"__p2")) (TupleSel 1)))))])))))))),(NonRecursive (Decl (304,"drop") (DExpr (ETAbs (458,"front") (ETAbs (459,"back") (ETAbs (460,"elem") (EAbs (461,"__p4") (EWhere (EVar (464,"y")) [(NonRecursive (Decl (462,"__p5") (DExpr (EApp (ETApp (ETApp (ETApp (EVar (277,"splitAt")) (TVar (TVBound 231 KNum))) (TVar (TVBound 232 KNum))) (TVar (TVBound 233 KType))) (EVar (461,"__p4")))))),(NonRecursive (Decl (463,"__p3") (DExpr (ESel (EVar (462,"__p5")) (TupleSel 0))))),(NonRecursive (Decl (464,"y") (DExpr (ESel (EVar (462,"__p5")) (TupleSel 1)))))])))))))),(NonRecursive (Decl (305,"tail") (DExpr (ETAbs (465,"a") (ETAbs (466,"b") (EAbs (467,"xs") (EApp (ETApp (ETApp (ETApp (EVar (304,"drop")) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 249 KNum))) (TVar (TVBound 250 KType))) (EVar (467,"xs"))))))))),(NonRecursive (Decl (306,"width") (DExpr (ETAbs (468,"bits") (ETAbs (469,"len") (ETAbs (470,"elem") (EAbs (471,"__p6") (ETApp (ETApp (EVar (242,"demote")) (TVar (TVBound 256 KNum))) (TVar (TVBound 255 KNum)))))))))),(NonRecursive (Decl (307,"undefined") (DExpr (ETAbs (472,"a") (EApp (ETApp (ETApp (EVar (295,"error")) (TVar (TVBound 260 KType))) (TCon (TC (TCNum 9)) [])) (EList [(ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 117)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 110)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 100)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 101)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 102)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 105)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 110)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 101)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 100)) [])) (TCon (TC (TCNum 8)) []))])))))),(NonRecursive (Decl (308,"groupBy") (DExpr (ETAbs (473,"each") (ETAbs (474,"parts") (ETAbs (475,"elem") (ETApp (ETApp (ETApp (EVar (279,"split")) (TVar (TVBound 266 KNum))) (TVar (TVBound 265 KNum))) (TVar (TVBound 267 KType))))))))),(NonRecursive (Decl (310,"trace") DPrim)),(NonRecursive (Decl (311,"traceVal") (DExpr (ETAbs (480,"n") (ETAbs (481,"a") (EAbs (482,"msg") (EAbs (483,"x") (EApp (EApp (EApp (ETApp (ETApp (ETApp (EVar (310,"trace")) (TVar (TVBound 273 KNum))) (TVar (TVBound 274 KType))) (TVar (TVBound 274 KType))) (EVar (482,"msg"))) (EVar (483,"x"))) (EVar (483,"x")))))))))),(Recursive [(Decl (484,"fib") (DExpr (EAbs (485,"n") (EIf (EApp (EApp (ETApp (EVar (259,"==")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar (485,"n"))) (ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 32)) []))) (ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) [])) (EIf (EApp (EApp (ETApp (EVar (259,"==")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar (485,"n"))) (ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) []))) (ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) [])) (EApp (EApp (ETApp (EVar (243,"+")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EApp (EVar (484,"fib")) (EApp (EApp (ETApp (EVar (243,"+")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar (485,"n"))) (EApp (ETApp (EVar (253,"negate")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) [])))))) (EApp (EVar (484,"fib")) (EApp (EApp (ETApp (EVar (243,"+")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar (485,"n"))) (EApp (ETApp (EVar (253,"negate")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (ETApp (ETApp (EVar (242,"demote")) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 32)) [])))))))))))])].

Definition width : nat := 32. 
Definition fibident : ident := (484, "fib"). 
Definition fibvar : ident := (12, "var"). 

(* Lemma nz : width <> O. *)
(* Proof.  *)
(*   unfold width. congruence.  *)
(* Qed. *)


(* Global environment *)
Definition fib_ge := bind_decl_groups fib_cry gempty. 


Definition nz32 (n:Z) := bits (@repr width n). 
Definition Env (n:Z) := extend empty fibvar (nz32 n). 

Definition E := Env 0. 

(* Fib 0 = 1 *)
Lemma eval_fib0 : eval_expr fib_ge E (EApp (EVar fibident) (EVar fibvar)) (nz32 1).
Proof. 
  e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. 
  e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. 
  (* lol *)
Qed. 

Definition E1 := Env 1.
 
(* Fib 1 = 1 *) 
Lemma eval_fib1 : eval_expr fib_ge E1 (EApp (EVar fibident) (EVar fibvar)) (nz32 1). 
Proof. 
  repeat e.

Qed. 

Definition E3 := Env 3.

(* Fib 3 = 3 *) 
Lemma eval_fib3 : eval_expr fib_ge E3 (EApp (EVar fibident) (EVar fibvar)) (nz32 3).
Proof. 
  repeat e. (* Takes like 10 min *)

Qed.  
  








(*  Old version before Semantics.v changes


(* Grab some useful tactics : 
  e: applies econstructor and some simplification whenever there is no choice to be made (not an If or Var) 
  global: resolves the constructor for a var in the global env
  local: resolves the constructor for a var in the local env  *)

(* right side of this generated from cryptol implementation Fib.cry *)

Definition fib_cry : DeclGroup := (Recursive [(Decl 484 (DExpr (EAbs 485 (EIf (EApp (EApp (ETApp (EVar 259) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar 485)) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 32)) []))) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) [])) (EIf (EApp (EApp (ETApp (EVar 259) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar 485)) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) []))) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) [])) (EApp (EApp (ETApp (EVar 243) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EApp (EVar 484) (EApp (EApp (ETApp (EVar 243) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar 485)) (EApp (ETApp (EVar 253) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) [])))))) (EApp (EVar 484) (EApp (EApp (ETApp (EVar 243) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar 485)) (EApp (ETApp (EVar 253) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 32)) [])))))))))))]).

Definition width : nat := 32. 
Definition fibnum : ident := 484. 
Definition fibvar : ident := 12. 

(* A non-zero width *)
Lemma nz : width <> O.
Proof. 
  unfold width. congruence. 
Qed.

(* 242 -> plus *)
(* 259 -> eq *)
(* 243 -> neg *)
Definition plus_decl := builtin_binop 242 Plus.
Definition eq_decl := builtin_binop 259 Eq.
Definition neg_decl := builtin_unop 243 Neg.


(* Global environment *)
Definition fib_ge := bind_decl_group fib_cry
                                    (bind_decl_group neg_decl
                                    (bind_decl_group eq_decl
                                    (bind_decl_group plus_decl
                                                     gempty))). 

(* Local environment *)
Definition Env (n:Z) := extend empty fibvar (bits (@repr width nz n)). 



Definition E := Env 0. 


(* Fib 0 = 1 *)
Lemma eval_fib0 : eval_expr fib_ge E (EApp (EVar fibnum) (EVar fibvar)) (bits (@repr width nz 1)). 
Proof.
  e. 
  - global. e. 
  - local. 
  - eapply eval_if_t. 
    + e. e. e. global. e. local.  
      * unfold extend. e. 
      * e. 
      * e. 
        -- local. 
        -- local.   
        -- econstructor. exact nz. exact nz. reflexivity.   
    + e. 
  Unshelve. exact nz. 
Qed.   
     

Definition E1 := Env 1.  

(* Fib 1 = 1 *)
Lemma eval_fib1 : eval_expr fib_ge E1 (EApp (EVar fibnum) (EVar fibvar)) (bits (@repr width nz 1)).  
Proof. 
  e. 
  - global. e. 
  - local. 
  - eapply eval_if_f.                 (* Doesn't match first base case *)
    + e. e. e. global. e. local.  
      * unfold extend. e. 
      * e. 
      * e. 
        -- local. 
        -- local.   
        -- econstructor; try exact nz. reflexivity. 
    + eapply eval_if_t.               (* Matches second base case *)
      * e. e. e. global. e. local.  
        -- unfold extend. e. 
        -- e. 
        -- e. 
           ++ local. 
           ++ local.   
           ++ econstructor; try exact nz. reflexivity. 
      * e.  
  Unshelve. all: exact nz. 
Qed.    

Definition E2 := Env 2. 

Lemma plus_fib12s : (eval_expr fib_ge E2 (EApp (EVar 242) (EApp (EVar fibvar) (EVar fibvar))) (bits (@repr width nz 24))).
Proof. 
  e. 
  - global. e. 
  - e. 
    + eapply eval_global_var. unfold E2. unfold Env. unfold extend. simpl. 
Admitted. 

(*Lemma plus_f0_f1 : eval_expr fib_ge E2 (EApp (EVar 242) (eval_expr fib_ge E (EApp (EVar fibnum) (EVar fibvar))) (eval_expr fib_ge E1 (EApp (EVar fibnum) (EVar fibvar)))) (bits (@repr width nz 0)).  
*)

(* Fib 2 = 2 *)
Lemma eval_fib2 : eval_expr fib_ge E2 (EApp (EVar fibnum) (EVar fibvar)) (bits (@repr width nz 2)).
Proof. 
  e. 
  - global. e. 
  - local. 
  - eapply eval_if_f.                  (* Doesn't match first base case *)
    + e. e. e. global. e. local.  
      * unfold extend. e. 
      * e. 
      * e. 
        -- local. 
        -- local.   
        -- econstructor; try exact nz. reflexivity. 
    + eapply eval_if_f.                (* Doesn't match second base case *)
      * e. e. e. global. e. local.  
        -- unfold extend. e. 
        -- e. 
        -- e. 
          ++ local. 
          ++ local.   
          ++ econstructor; try exact nz. reflexivity. 
      * econstructor.                  (* Take recursive case *)
      (* Something is going wrong in the next line *)
      e. e. e. global. e. e. global. e. e. e. e. global. e. local. e. local. 
        -- (* This isn't true - eapply eval_neg.*) 
Admitted. 

Definition E3 := Env 3. 

(* Fib 3 = 3 *)
Lemma eval_fib3 : eval_expr fib_ge E3 (EApp (EVar fibnum) (EVar fibvar)) (bits (@repr width nz 3)).
Proof. 
  econstructor. 
  - unfold fib_ge. simpl. eapply eval_global_var.
    + unfold E. unfold extend. simpl. unfold empty. reflexivity. 
    + simpl. reflexivity. 
    + econstructor. 
  - econstructor. unfold E. unfold extend. simpl. reflexivity. 
  - eapply eval_if_f. e. e. e. global. e. local. local. local. e. local. local.
    + econstructor; try exact nz. reflexivity.
    + eapply eval_if_f. e. e. e. global. e. local. local. local. e. local. local.
      * econstructor; try exact nz. reflexivity. 
      * (* Getting closer. This econstructor is maybe not right*)
    econstructor. e. e. e. global. e. e. global. local. e.  e. e. global. local. local. e. local.
Admitted.   
        


(*
 (* #3 *)unfold fib_ge. simpl. 
    econstructor. 
    econstructor. 
    econstructor. 
    econstructor. 
    econstructor. 
    + unfold extend. simpl. 


 (* #3 *)eapply eval_if_t. 
    + econstructor. 
      econstructor. 
      econstructor. 
      econstructor. unfold extend. simpl. unfold E. unfold extend. simpl. unfold empty. 


 (* #3 *)unfold fib_ge. simpl. econstructor. econstructor. econstructor. econstructor. eapply eval_global_var.
    unfold extend. simpl. unfold E. unfold extend. simpl. unfold empty. reflexivity.


 (* #3 *) econstructor.      
    + econstructor.
      econstructor. 
      econstructor. 
      * econstructor. unfold extend. simpl. unfold E. 
        unfold extend. simpl. unfold empty. (* This isn't true. So E doesn't have everything we need (?) *)  


*)



*)