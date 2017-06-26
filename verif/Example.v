Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.
Require Import BuiltinSem.
Require Import Values.        

Require Import Tactics.

Import HaskellListNotations.
Open Scope string.

(* verbatim whole prog from cryptol *)
Definition whole_prog := [(NonRecursive (Decl (0,"demote") DPrim)),(NonRecursive (Decl (1,"+") DPrim)),(NonRecursive (Decl (2,"-") DPrim)),(NonRecursive (Decl (3,"*") DPrim)),(NonRecursive (Decl (4,"/") DPrim)),(NonRecursive (Decl (5,"%") DPrim)),(NonRecursive (Decl (6,"^^") DPrim)),(NonRecursive (Decl (7,"lg2") DPrim)),(NonRecursive (Decl (9,"True") DPrim)),(NonRecursive (Decl (10,"False") DPrim)),(NonRecursive (Decl (11,"negate") DPrim)),(NonRecursive (Decl (12,"complement") DPrim)),(NonRecursive (Decl (13,"<") DPrim)),(NonRecursive (Decl (14,">") DPrim)),(NonRecursive (Decl (15,"<=") DPrim)),(NonRecursive (Decl (16,">=") DPrim)),(NonRecursive (Decl (17,"==") DPrim)),(NonRecursive (Decl (18,"!=") DPrim)),(NonRecursive (Decl (19,"===") (DExpr (ETAbs (30,"") (ETAbs (31,"") (EAbs (89,"f") (EAbs (90,"g") (EAbs (91,"x") (EApp (EApp (ETApp (EVar (17,"==")) (TVar (TVBound 31 KType))) (EApp (EVar (89,"f")) (EVar (91,"x")))) (EApp (EVar (90,"g")) (EVar (91,"x")))))))))))),(NonRecursive (Decl (20,"!==") (DExpr (ETAbs (40,"") (ETAbs (41,"") (EAbs (94,"f") (EAbs (95,"g") (EAbs (96,"x") (EApp (EApp (ETApp (EVar (18,"!=")) (TVar (TVBound 41 KType))) (EApp (EVar (94,"f")) (EVar (96,"x")))) (EApp (EVar (95,"g")) (EVar (96,"x")))))))))))),(NonRecursive (Decl (21,"min") (DExpr (ETAbs (50,"") (EAbs (98,"x") (EAbs (99,"y") (EIf (EApp (EApp (ETApp (EVar (13,"<")) (TVar (TVBound 50 KType))) (EVar (98,"x"))) (EVar (99,"y"))) (EVar (98,"x")) (EVar (99,"y"))))))))),(NonRecursive (Decl (22,"max") (DExpr (ETAbs (56,"") (EAbs (101,"x") (EAbs (102,"y") (EIf (EApp (EApp (ETApp (EVar (14,">")) (TVar (TVBound 56 KType))) (EVar (101,"x"))) (EVar (102,"y"))) (EVar (101,"x")) (EVar (102,"y"))))))))),(NonRecursive (Decl (23,"/\\") (DExpr (EAbs (103,"x") (EAbs (104,"y") (EIf (EVar (103,"x")) (EVar (104,"y")) (EVar (10,"False")))))))),(NonRecursive (Decl (24,"\\/") (DExpr (EAbs (105,"x") (EAbs (106,"y") (EIf (EVar (105,"x")) (EVar (9,"True")) (EVar (106,"y")))))))),(NonRecursive (Decl (25,"==>") (DExpr (EAbs (107,"a") (EAbs (108,"b") (EIf (EVar (107,"a")) (EVar (108,"b")) (EVar (9,"True")))))))),(NonRecursive (Decl (26,"&&") DPrim)),(NonRecursive (Decl (27,"||") DPrim)),(NonRecursive (Decl (28,"^") DPrim)),(NonRecursive (Decl (29,"zero") DPrim)),(NonRecursive (Decl (30,"<<") DPrim)),(NonRecursive (Decl (31,">>") DPrim)),(NonRecursive (Decl (32,"<<<") DPrim)),(NonRecursive (Decl (33,">>>") DPrim)),(NonRecursive (Decl (34,"#") DPrim)),(NonRecursive (Decl (35,"splitAt") DPrim)),(NonRecursive (Decl (36,"join") DPrim)),(NonRecursive (Decl (37,"split") DPrim)),(NonRecursive (Decl (38,"reverse") DPrim)),(NonRecursive (Decl (39,"transpose") DPrim)),(NonRecursive (Decl (40,"@") DPrim)),(NonRecursive (Decl (41,"@@") DPrim)),(NonRecursive (Decl (42,"!") DPrim)),(NonRecursive (Decl (43,"!!") DPrim)),(NonRecursive (Decl (44,"update") DPrim)),(NonRecursive (Decl (45,"updateEnd") DPrim)),(NonRecursive (Decl (46,"updates") (DExpr (ETAbs (121,"") (ETAbs (122,"") (ETAbs (123,"") (ETAbs (124,"") (EAbs (166,"xs0") (EAbs (167,"idxs") (EAbs (168,"vals") (EWhere (EApp (EApp (ETApp (ETApp (ETApp (EVar (42,"!")) (TCon (TF TCAdd) [TCon (TC (TCNum 1)) [],TVar (TVBound 124 KNum)])) (TCon (TC TCSeq) [TVar (TVBound 121 KNum),TVar (TVBound 122 KType)])) (TCon (TC (TCNum 0)) [])) (EVar (169,"xss"))) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 0)) []))) [(Recursive [(Decl (169,"xss") (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar (34,"#")) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 124 KNum))) (TCon (TC TCSeq) [TVar (TVBound 121 KNum),TVar (TVBound 122 KType)])) (EList [(EVar (166,"xs0"))])) (EComp (EApp (EApp (EApp (ETApp (ETApp (ETApp (EVar (44,"update")) (TVar (TVBound 121 KNum))) (TVar (TVBound 122 KType))) (TVar (TVBound 123 KNum))) (EVar (170,"xs"))) (EVar (171,"i"))) (EVar (172,"b"))) [[(From (170,"xs") (EVar (169,"xss")))],[(From (171,"i") (EVar (167,"idxs")))],[(From (172,"b") (EVar (168,"vals")))]]))))])]))))))))))),(NonRecursive (Decl (47,"updatesEnd") (DExpr (ETAbs (156,"") (ETAbs (157,"") (ETAbs (158,"") (ETAbs (159,"") (EAbs (177,"xs0") (EAbs (178,"idxs") (EAbs (179,"vals") (EWhere (EApp (EApp (ETApp (ETApp (ETApp (EVar (42,"!")) (TCon (TF TCAdd) [TCon (TC (TCNum 1)) [],TVar (TVBound 159 KNum)])) (TCon (TC TCSeq) [TVar (TVBound 156 KNum),TVar (TVBound 157 KType)])) (TCon (TC (TCNum 0)) [])) (EVar (180,"xss"))) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 0)) []))) [(Recursive [(Decl (180,"xss") (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar (34,"#")) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 159 KNum))) (TCon (TC TCSeq) [TVar (TVBound 156 KNum),TVar (TVBound 157 KType)])) (EList [(EVar (177,"xs0"))])) (EComp (EApp (EApp (EApp (ETApp (ETApp (ETApp (EVar (45,"updateEnd")) (TVar (TVBound 156 KNum))) (TVar (TVBound 157 KType))) (TVar (TVBound 158 KNum))) (EVar (181,"xs"))) (EVar (182,"i"))) (EVar (183,"b"))) [[(From (181,"xs") (EVar (180,"xss")))],[(From (182,"i") (EVar (178,"idxs")))],[(From (183,"b") (EVar (179,"vals")))]]))))])]))))))))))),(NonRecursive (Decl (48,"fromThen") DPrim)),(NonRecursive (Decl (49,"fromTo") DPrim)),(NonRecursive (Decl (50,"fromThenTo") DPrim)),(NonRecursive (Decl (51,"infFrom") DPrim)),(NonRecursive (Decl (52,"infFromThen") DPrim)),(NonRecursive (Decl (53,"error") DPrim)),(NonRecursive (Decl (54,"pmult") DPrim)),(NonRecursive (Decl (55,"pdiv") DPrim)),(NonRecursive (Decl (56,"pmod") DPrim)),(NonRecursive (Decl (57,"random") DPrim)),(NonRecursive (Decl (61,"take") (DExpr (ETAbs (214,"") (ETAbs (215,"") (ETAbs (216,"") (EAbs (212,"__p1") (EWhere (EVar (214,"x")) [(NonRecursive (Decl (213,"__p2") (DExpr (EApp (ETApp (ETApp (ETApp (EVar (35,"splitAt")) (TVar (TVBound 214 KNum))) (TVar (TVBound 215 KNum))) (TVar (TVBound 216 KType))) (EVar (212,"__p1")))))),(NonRecursive (Decl (214,"x") (DExpr (ESel (EVar (213,"__p2")) (TupleSel 0))))),(NonRecursive (Decl (215,"__p0") (DExpr (ESel (EVar (213,"__p2")) (TupleSel 1)))))])))))))),(NonRecursive (Decl (62,"drop") (DExpr (ETAbs (231,"") (ETAbs (232,"") (ETAbs (233,"") (EAbs (219,"__p4") (EWhere (EVar (222,"y")) [(NonRecursive (Decl (220,"__p5") (DExpr (EApp (ETApp (ETApp (ETApp (EVar (35,"splitAt")) (TVar (TVBound 231 KNum))) (TVar (TVBound 232 KNum))) (TVar (TVBound 233 KType))) (EVar (219,"__p4")))))),(NonRecursive (Decl (221,"__p3") (DExpr (ESel (EVar (220,"__p5")) (TupleSel 0))))),(NonRecursive (Decl (222,"y") (DExpr (ESel (EVar (220,"__p5")) (TupleSel 1)))))])))))))),(NonRecursive (Decl (63,"tail") (DExpr (ETAbs (249,"") (ETAbs (250,"") (EAbs (225,"xs") (EApp (ETApp (ETApp (ETApp (EVar (62,"drop")) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 249 KNum))) (TVar (TVBound 250 KType))) (EVar (225,"xs"))))))))),(NonRecursive (Decl (64,"width") (DExpr (ETAbs (255,"") (ETAbs (256,"") (ETAbs (257,"") (EAbs (229,"__p6") (ETApp (ETApp (EVar (0,"demote")) (TVar (TVBound 256 KNum))) (TVar (TVBound 255 KNum)))))))))),(NonRecursive (Decl (65,"undefined") (DExpr (ETAbs (260,"") (EApp (ETApp (ETApp (EVar (53,"error")) (TVar (TVBound 260 KType))) (TCon (TC (TCNum 9)) [])) (EList [(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 117)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 110)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 100)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 101)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 102)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 105)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 110)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 101)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 100)) [])) (TCon (TC (TCNum 8)) []))])))))),(NonRecursive (Decl (66,"groupBy") (DExpr (ETAbs (265,"") (ETAbs (266,"") (ETAbs (267,"") (ETApp (ETApp (ETApp (EVar (37,"split")) (TVar (TVBound 266 KNum))) (TVar (TVBound 265 KNum))) (TVar (TVBound 267 KType))))))))),(NonRecursive (Decl (68,"trace") DPrim)),(NonRecursive (Decl (69,"traceVal") (DExpr (ETAbs (273,"") (ETAbs (274,"") (EAbs (240,"msg") (EAbs (241,"x") (EApp (EApp (EApp (ETApp (ETApp (ETApp (EVar (68,"trace")) (TVar (TVBound 273 KNum))) (TVar (TVBound 274 KType))) (TVar (TVBound 274 KType))) (EVar (240,"msg"))) (EVar (241,"x"))) (EVar (241,"x")))))))))),(NonRecursive (Decl (242,"id") (DExpr (EAbs (243,"x") (EWhere (EApp (EVar (244,"rec")) (EVar (243,"x"))) [(Recursive [(Decl (244,"rec") (DExpr (EAbs (245,"k") (EIf (EApp (EApp (ETApp (EVar (17,"==")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar (245,"k"))) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 32)) []))) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 32)) [])) (EApp (EApp (ETApp (EVar (1,"+")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) []))) (EApp (EVar (244,"rec")) (EApp (EApp (ETApp (EVar (1,"+")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar (245,"k"))) (EApp (ETApp (EVar (11,"negate")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) []))))))))))])])))))].


Definition width : nat := 32.

Lemma nz :
  width <> O.
Proof.
  unfold width. congruence.
Qed.


Definition id_ge := bind_decl_groups whole_prog gempty.

Definition E := extend empty (12,"input") (bits (@repr width nz 2)).

Ltac ec := econstructor; try unfold mb; try reflexivity.
Ltac g := eapply eval_global_var; try reflexivity; try (unfold mb; simpl).

Ltac e :=
  match goal with
  | [ |- eval_expr _ ?E (EVar ?id) _ ] =>
    try solve [ec]; g
  | [ |- _ ] => ec
  end.

Lemma eval_id :
    eval_expr id_ge E (EApp (EVar (242,"id")) (EVar (12,"input"))) (bits (@repr width nz 2)).
Proof.
  unfold id_ge.
  repeat e.
  
  Unshelve.
  all: cbv; omega.
Qed.


