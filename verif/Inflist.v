
(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Bitvectors.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.
Require Import Bitvectors.
Require Import Values.

Import HaskellListNotations.
Open Scope string_scope.
(*
Definition whole_prog := [(NonRecursive (Decl (0,"demote") DPrim)),(NonRecursive (Decl (1,"+") DPrim)),(NonRecursive (Decl (2,"-") DPrim)),(NonRecursive (Decl (3,"*") DPrim)),(NonRecursive (Decl (4,"/") DPrim)),(NonRecursive (Decl (5,"%") DPrim)),(NonRecursive (Decl (6,"^^") DPrim)),(NonRecursive (Decl (7,"lg2") DPrim)),(NonRecursive (Decl (9,"True") DPrim)),(NonRecursive (Decl (10,"False") DPrim)),(NonRecursive (Decl (11,"negate") DPrim)),(NonRecursive (Decl (12,"complement") DPrim)),(NonRecursive (Decl (13,"<") DPrim)),(NonRecursive (Decl (14,">") DPrim)),(NonRecursive (Decl (15,"<=") DPrim)),(NonRecursive (Decl (16,">=") DPrim)),(NonRecursive (Decl (17,"==") DPrim)),(NonRecursive (Decl (18,"!=") DPrim)),(NonRecursive (Decl (19,"===") (DExpr (ETAbs (87,"a") (ETAbs (88,"b") (EAbs (89,"f") (EAbs (90,"g") (EAbs (91,"x") (EApp (EApp (ETApp (EVar (17,"==")) (TVar (TVBound 31 KType))) (EApp (EVar (89,"f")) (EVar (91,"x")))) (EApp (EVar (90,"g")) (EVar (91,"x")))))))))))),(NonRecursive (Decl (20,"!==") (DExpr (ETAbs (92,"a") (ETAbs (93,"b") (EAbs (94,"f") (EAbs (95,"g") (EAbs (96,"x") (EApp (EApp (ETApp (EVar (18,"!=")) (TVar (TVBound 41 KType))) (EApp (EVar (94,"f")) (EVar (96,"x")))) (EApp (EVar (95,"g")) (EVar (96,"x")))))))))))),(NonRecursive (Decl (21,"min") (DExpr (ETAbs (97,"a") (EAbs (98,"x") (EAbs (99,"y") (EIf (EApp (EApp (ETApp (EVar (13,"<")) (TVar (TVBound 50 KType))) (EVar (98,"x"))) (EVar (99,"y"))) (EVar (98,"x")) (EVar (99,"y"))))))))),(NonRecursive (Decl (22,"max") (DExpr (ETAbs (100,"a") (EAbs (101,"x") (EAbs (102,"y") (EIf (EApp (EApp (ETApp (EVar (14,">")) (TVar (TVBound 56 KType))) (EVar (101,"x"))) (EVar (102,"y"))) (EVar (101,"x")) (EVar (102,"y"))))))))),(NonRecursive (Decl (23,"/\\") (DExpr (EAbs (103,"x") (EAbs (104,"y") (EIf (EVar (103,"x")) (EVar (104,"y")) (EVar (10,"False")))))))),(NonRecursive (Decl (24,"\\/") (DExpr (EAbs (105,"x") (EAbs (106,"y") (EIf (EVar (105,"x")) (EVar (9,"True")) (EVar (106,"y")))))))),(NonRecursive (Decl (25,"==>") (DExpr (EAbs (107,"a") (EAbs (108,"b") (EIf (EVar (107,"a")) (EVar (108,"b")) (EVar (9,"True")))))))),(NonRecursive (Decl (26,"&&") DPrim)),(NonRecursive (Decl (27,"||") DPrim)),(NonRecursive (Decl (28,"^") DPrim)),(NonRecursive (Decl (29,"zero") DPrim)),(NonRecursive (Decl (30,"<<") DPrim)),(NonRecursive (Decl (31,">>") DPrim)),(NonRecursive (Decl (32,"<<<") DPrim)),(NonRecursive (Decl (33,">>>") DPrim)),(NonRecursive (Decl (34,"#") DPrim)),(NonRecursive (Decl (35,"splitAt") DPrim)),(NonRecursive (Decl (36,"join") DPrim)),(NonRecursive (Decl (37,"split") DPrim)),(NonRecursive (Decl (38,"reverse") DPrim)),(NonRecursive (Decl (39,"transpose") DPrim)),(NonRecursive (Decl (40,"@") DPrim)),(NonRecursive (Decl (41,"@@") DPrim)),(NonRecursive (Decl (42,"!") DPrim)),(NonRecursive (Decl (43,"!!") DPrim)),(NonRecursive (Decl (44,"update") DPrim)),(NonRecursive (Decl (45,"updateEnd") DPrim)),(NonRecursive (Decl (46,"updates") (DExpr (ETAbs (162,"a") (ETAbs (163,"b") (ETAbs (164,"c") (ETAbs (165,"d") (EAbs (166,"xs0") (EAbs (167,"idxs") (EAbs (168,"vals") (EWhere (EApp (EApp (ETApp (ETApp (ETApp (EVar (42,"!")) (TCon (TF TCAdd) [TCon (TC (TCNum 1)) [],TVar (TVBound 124 KNum)])) (TCon (TC TCSeq) [TVar (TVBound 121 KNum),TVar (TVBound 122 KType)])) (TCon (TC (TCNum 0)) [])) (EVar (169,"xss"))) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 0)) []))) [(Recursive [(Decl (169,"xss") (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar (34,"#")) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 124 KNum))) (TCon (TC TCSeq) [TVar (TVBound 121 KNum),TVar (TVBound 122 KType)])) (EList [(EVar (166,"xs0"))])) (EComp (EApp (EApp (EApp (ETApp (ETApp (ETApp (EVar (44,"update")) (TVar (TVBound 121 KNum))) (TVar (TVBound 122 KType))) (TVar (TVBound 123 KNum))) (EVar (170,"xs"))) (EVar (171,"i"))) (EVar (172,"b"))) [[(From (170,"xs") (EVar (169,"xss")))],[(From (171,"i") (EVar (167,"idxs")))],[(From (172,"b") (EVar (168,"vals")))]]))))])]))))))))))),(NonRecursive (Decl (47,"updatesEnd") (DExpr (ETAbs (173,"a") (ETAbs (174,"b") (ETAbs (175,"c") (ETAbs (176,"d") (EAbs (177,"xs0") (EAbs (178,"idxs") (EAbs (179,"vals") (EWhere (EApp (EApp (ETApp (ETApp (ETApp (EVar (42,"!")) (TCon (TF TCAdd) [TCon (TC (TCNum 1)) [],TVar (TVBound 159 KNum)])) (TCon (TC TCSeq) [TVar (TVBound 156 KNum),TVar (TVBound 157 KType)])) (TCon (TC (TCNum 0)) [])) (EVar (180,"xss"))) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 0)) []))) [(Recursive [(Decl (180,"xss") (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar (34,"#")) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 159 KNum))) (TCon (TC TCSeq) [TVar (TVBound 156 KNum),TVar (TVBound 157 KType)])) (EList [(EVar (177,"xs0"))])) (EComp (EApp (EApp (EApp (ETApp (ETApp (ETApp (EVar (45,"updateEnd")) (TVar (TVBound 156 KNum))) (TVar (TVBound 157 KType))) (TVar (TVBound 158 KNum))) (EVar (181,"xs"))) (EVar (182,"i"))) (EVar (183,"b"))) [[(From (181,"xs") (EVar (180,"xss")))],[(From (182,"i") (EVar (178,"idxs")))],[(From (183,"b") (EVar (179,"vals")))]]))))])]))))))))))),(NonRecursive (Decl (48,"fromThen") DPrim)),(NonRecursive (Decl (49,"fromTo") DPrim)),(NonRecursive (Decl (50,"fromThenTo") DPrim)),(NonRecursive (Decl (51,"infFrom") DPrim)),(NonRecursive (Decl (52,"infFromThen") DPrim)),(NonRecursive (Decl (53,"error") DPrim)),(NonRecursive (Decl (54,"pmult") DPrim)),(NonRecursive (Decl (55,"pdiv") DPrim)),(NonRecursive (Decl (56,"pmod") DPrim)),(NonRecursive (Decl (57,"random") DPrim)),(NonRecursive (Decl (61,"take") (DExpr (ETAbs (209,"front") (ETAbs (210,"back") (ETAbs (211,"elem") (EAbs (212,"__p1") (EWhere (EVar (214,"x")) [(NonRecursive (Decl (213,"__p2") (DExpr (EApp (ETApp (ETApp (ETApp (EVar (35,"splitAt")) (TVar (TVBound 214 KNum))) (TVar (TVBound 215 KNum))) (TVar (TVBound 216 KType))) (EVar (212,"__p1")))))),(NonRecursive (Decl (214,"x") (DExpr (ESel (EVar (213,"__p2")) (TupleSel 0))))),(NonRecursive (Decl (215,"__p0") (DExpr (ESel (EVar (213,"__p2")) (TupleSel 1)))))])))))))),(NonRecursive (Decl (62,"drop") (DExpr (ETAbs (216,"front") (ETAbs (217,"back") (ETAbs (218,"elem") (EAbs (219,"__p4") (EWhere (EVar (222,"y")) [(NonRecursive (Decl (220,"__p5") (DExpr (EApp (ETApp (ETApp (ETApp (EVar (35,"splitAt")) (TVar (TVBound 231 KNum))) (TVar (TVBound 232 KNum))) (TVar (TVBound 233 KType))) (EVar (219,"__p4")))))),(NonRecursive (Decl (221,"__p3") (DExpr (ESel (EVar (220,"__p5")) (TupleSel 0))))),(NonRecursive (Decl (222,"y") (DExpr (ESel (EVar (220,"__p5")) (TupleSel 1)))))])))))))),(NonRecursive (Decl (63,"tail") (DExpr (ETAbs (223,"a") (ETAbs (224,"b") (EAbs (225,"xs") (EApp (ETApp (ETApp (ETApp (EVar (62,"drop")) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 249 KNum))) (TVar (TVBound 250 KType))) (EVar (225,"xs"))))))))),(NonRecursive (Decl (64,"width") (DExpr (ETAbs (226,"bits") (ETAbs (227,"len") (ETAbs (228,"elem") (EAbs (229,"__p6") (ETApp (ETApp (EVar (0,"demote")) (TVar (TVBound 256 KNum))) (TVar (TVBound 255 KNum)))))))))),(NonRecursive (Decl (65,"undefined") (DExpr (ETAbs (230,"a") (EApp (ETApp (ETApp (EVar (53,"error")) (TVar (TVBound 260 KType))) (TCon (TC (TCNum 9)) [])) (EList [(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 117)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 110)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 100)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 101)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 102)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 105)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 110)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 101)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 100)) [])) (TCon (TC (TCNum 8)) []))])))))),(NonRecursive (Decl (66,"groupBy") (DExpr (ETAbs (231,"each") (ETAbs (232,"parts") (ETAbs (233,"elem") (ETApp (ETApp (ETApp (EVar (37,"split")) (TVar (TVBound 266 KNum))) (TVar (TVBound 265 KNum))) (TVar (TVBound 267 KType))))))))),(NonRecursive (Decl (68,"trace") DPrim)),(NonRecursive (Decl (69,"traceVal") (DExpr (ETAbs (238,"n") (ETAbs (239,"a") (EAbs (240,"msg") (EAbs (241,"x") (EApp (EApp (EApp (ETApp (ETApp (ETApp (EVar (68,"trace")) (TVar (TVBound 273 KNum))) (TVar (TVBound 274 KType))) (TVar (TVBound 274 KType))) (EVar (240,"msg"))) (EVar (241,"x"))) (EVar (241,"x")))))))))),(NonRecursive (Decl (242,"id") (DExpr (EAbs (252,"x") (EWhere (EApp (EVar (253,"rec")) (EVar (252,"x"))) [(Recursive [(Decl (253,"rec") (DExpr (EAbs (254,"k") (EIf (EApp (EApp (ETApp (EVar (17,"==")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar (254,"k"))) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 32)) []))) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 32)) [])) (EApp (EApp (ETApp (EVar (1,"+")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) []))) (EApp (EVar (253,"rec")) (EApp (EApp (ETApp (EVar (1,"+")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar (254,"k"))) (EApp (ETApp (EVar (11,"negate")) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) []))))))))))])]))))),(NonRecursive (Decl (243,"inflist") (DExpr (EApp (ETApp (EVar (51,"infFrom")) (TCon (TC (TCNum 8)) [])) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])))))),(NonRecursive (Decl (244,"rc") (DExpr (ERec [("x",(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) []))),("y",(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 5)) [])) (TCon (TC (TCNum 8)) [])))])))),(NonRecursive (Decl (245,"my_true") (DExpr (ESel (EVar (244,"rc")) (RecordSel "x"))))),(NonRecursive (Decl (246,"tup") (DExpr (ETuple [(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 4)) [])) (TCon (TC (TCNum 8)) []))])))),(NonRecursive (Decl (247,"my_3") (DExpr (ESel (EVar (246,"tup")) (TupleSel 2))))),(NonRecursive (Decl (248,"sup") (DExpr (EWhere (EVar (255,"y")) [(NonRecursive (Decl (255,"y") (DExpr (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) [])))))])))),(NonRecursive (Decl (249,"gf28Add") (DExpr (ETAbs (256,"n") (EAbs (257,"ps") (EWhere (EApp (EApp (ETApp (ETApp (ETApp (EVar (42,"!")) (TCon (TF TCAdd) [TCon (TC (TCNum 1)) [],TVar (TVBound 331 KNum)])) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (TCon (TC (TCNum 0)) [])) (EVar (258,"sums"))) (ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 0)) []))) [(Recursive [(Decl (258,"sums") (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar (34,"#")) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 331 KNum))) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (EList [(ETApp (EVar (29,"zero")) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []]))])) (EComp (EApp (EApp (ETApp (EVar (28,"^")) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (EVar (259,"p"))) (EVar (260,"s"))) [[(From (259,"p") (EVar (257,"ps")))],[(From (260,"s") (EVar (258,"sums")))]]))))])])))))),(NonRecursive (Decl (250,"gex") (DExpr (EApp (ETApp (EVar (249,"gf28Add")) (TCon (TC (TCNum 2)) [])) (EList [(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) []))]))))),(NonRecursive (Decl (251,"sum") (DExpr (EAbs (261,"x") (EWhere (EVar (262,"rec")) [(NonRecursive (Decl (262,"rec") (DExpr (EComp (EApp (EApp (ETApp (EVar (1,"+")) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (EVar (263,"p"))) (EVar (264,"q"))) [[(From (263,"p") (EVar (261,"x")))],[(From (264,"q") (EList [(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 4)) [])) (TCon (TC (TCNum 8)) []))]))]]))))])))))].

Lemma nz :
  8%nat <> 0%nat.
Proof.
  congruence.
Qed.

Definition three := bits (@repr 8 nz 3).

Lemma rec_eval :
  eval_expr rec_ge empty (EVar 247) (bits (@repr 8 nz 3)).
Proof.
  eapply eval_global_var. reflexivity. unfold rec_ge.
  simpl. reflexivity.
  econstructor. eapply eval_global_var. reflexivity.
  unfold rec_ge. simpl. reflexivity.
  econstructor. simpl.
  repeat econstructor.
  simpl. reflexivity.
  Unshelve.
  all: unfold Z.to_nat; unfold Pos.to_nat; simpl; try congruence.
Qed.

Definition tup := (NonRecursive (Decl 248 (DExpr (ETuple [(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 4)) [])) (TCon (TC (TCNum 8)) []))])))).

Definition tupsel := (NonRecursive (Decl 249 (DExpr (ESel (EVar 248) (TupleSel 2))))).

Definition tupsel_ge := bind_decl_group tup (bind_decl_group tupsel gempty).

Lemma tupsel_eval :
  eval_expr tupsel_ge empty (EVar 249) three.
Proof.
  eapply eval_global_var; try reflexivity.
  econstructor.
  eapply eval_global_var; try reflexivity.
  econstructor; eauto.
  repeat (econstructor; eauto).
  simpl. f_equal. unfold three. f_equal.
  Unshelve.
  all: unfold Z.to_nat; unfold Pos.to_nat; simpl; try congruence.
Qed.

Definition one := bits (@repr 8 nz 1).
Definition two := bits (@repr 8 nz 2).

Lemma finlist_sel_eval :
  eval_expr (bind_decl_group finlist gempty) empty finlist_sel_exp three.
Proof.
  e. e.
  match goal with
  | [ |- select_list _ _ ?N _ _ ] => replace N with (S (S O)) by (simpl; reflexivity)
  end.
  econstructor.
  global. e.
  repeat econstructor. simpl. reflexivity.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. econstructor. simpl. reflexivity.
  Unshelve.
  all: exact nz.
Qed.


Definition where_decl := (NonRecursive (Decl 250 (DExpr (EWhere (EVar 259) [(NonRecursive (Decl 259 (DExpr (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) [])))))])))).

Lemma where_eval :
  eval_expr (bind_decl_group where_decl gempty) empty (EVar 250) three.
Proof.
  global.
  e. e. global.
  e.
Qed.

Definition listcomp := (NonRecursive (Decl 251 (DExpr (EAbs 261 (EWhere (EVar 262) [(NonRecursive (Decl 262 (DExpr (EComp (EApp (EApp (ETApp (EVar 1) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (EVar 263)) (EVar 264)) [[(From 263 (EVar 261))],[(From 264 (EList [(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 4)) [])) (TCon (TC (TCNum 8)) []))]))]]))))]))))). 

Definition comp_idx_expr : Expr := ESel (EApp (EVar 251) (EVar 246)) (ListSel (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) []))).

Definition six := bits (@repr 8 nz 6).

Lemma listcomp_eval :
  eval_expr (bind_decl_groups (listcomp :: finlist :: plus_decl :: nil) gempty) empty comp_idx_expr six.
Proof.
  unfold comp_idx_expr.
  e.
  e.
  eapply select_comp.
  e. global. e. global. e.
  repeat econstructor. e.
  global. e.
  
  econstructor. econstructor.
  econstructor.
  econstructor. simpl. reflexivity.

  econstructor. econstructor.
  reflexivity.
  eapply select_zero. econstructor. reflexivity.
  econstructor. econstructor. 
  econstructor. econstructor.
  
  repeat econstructor. reflexivity.
  econstructor. econstructor. reflexivity.
  econstructor. econstructor. reflexivity.
  econstructor. econstructor.
  econstructor. e. global. econstructor. econstructor.
  reflexivity.
  econstructor. econstructor. reflexivity.
  econstructor. econstructor. reflexivity.
  econstructor. reflexivity.
  econstructor. omega.
  Unshelve.
  all: exact nz.
Qed.

  
Definition gf28Add := (NonRecursive (Decl 249 (DExpr (ETAbs 331 (EAbs 255 (EWhere (EApp (EApp (ETApp (ETApp (ETApp (EVar 42) (TCon (TF TCAdd) [TCon (TC (TCNum 1)) [],TVar (TVBound 331 KNum)])) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (TCon (TC (TCNum 0)) [])) (EVar 256)) (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 0)) []))) [(Recursive [(Decl 256 (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar 34) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 331 KNum))) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (EList [(ETApp (EVar 29) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []]))])) (EComp (EApp (EApp (ETApp (EVar 28) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (EVar 257)) (EVar 258)) [[(From 257 (EVar 255))],[(From 258 (EVar 256))]]))))])])))))).

Definition add_call := (NonRecursive (Decl 250 (DExpr (EApp (ETApp (EVar 249) (TCon (TC (TCNum 2)) [])) (EList [(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) []))]))))).

Definition gf28_add_ge := bind_decl_groups (gf28Add :: add_call :: plus_decl :: nil) gempty.


Lemma eval_gf28_add :
  eval_expr gf28_add_ge empty (EVar 250) three.
Proof.
  unfold gf28_add_ge. unfold bind_decl_groups.
  global.
  e.
  e. global.
  e. e. e. repeat econstructor.
  e. e. e. e. e. e. eapply eval_global_var.
  unfold extend. simpl. reflexivity.
  (* TODO *)
  
Admitted.  

*)