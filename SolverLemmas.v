Require Import Lia.
Require Import SolverDefinitions.

Local Open Scope positive_scope.

Local Open Scope nat_scope.
Lemma in_permute {A: Type} (l: list A) (x : A) : 
  (In x l) -> NoDup l -> exists l', (incl l (x :: l')) /\ (incl (x :: l') l) /\ NoDup (x :: l').
Proof.
  intros Hx Hdup.
  induction l as [| y l'' Hi].
  - contradiction.
  - {
    destruct Hx.
    - {
      exists l''.
      repeat (rewrite H).
      unfold incl.
      split.
      - intros Ha. auto.
      - split. intros Ha. auto. rewrite NoDup_cons_iff in Hdup. destruct Hdup; auto. constructor; auto. rewrite <- H. apply H0.
    }
    - {
      apply Hi in H.
      destruct H as [l Hl].
      exists (y :: l).
      split.
      - {
        destruct Hl as [Hl _].
        intros z Hz.
        destruct Hz as [Hyz | Hzl].
        - rewrite Hyz. simpl. right. left. reflexivity.
        - {
          specialize (Hl z). 
          apply Hl in Hzl.
          destruct Hzl as [Hxz | Hzl].
          - rewrite Hxz. simpl. left. reflexivity.
          - simpl. right. right. apply Hzl. 
        }
      }
      - {
        split; destruct Hl as [Hincl Hl]; destruct Hl as [Hl Hdupl].
        - {
          intros z Hz.
          simpl in Hz.
          destruct Hz as [Hxz | Hzl].
          - rewrite Hxz in Hl. specialize (Hl z). right. apply Hl. simpl. left. reflexivity.
          - {
            destruct Hzl as [Hyz | Hzl].
            - rewrite Hyz. left. reflexivity.
            - specialize (Hl z). right. apply Hl. right. apply Hzl.
          }
        }
        - {
          repeat (rewrite NoDup_cons_iff).
          rewrite NoDup_cons_iff in Hdup.
          rewrite NoDup_cons_iff in Hdupl.
          destruct Hdup as [Hyl'' Hdup''].
          destruct Hdupl as [Hxl Hdupl].
          split.
          - {
            intros Hyl.
            apply Hyl''.
            apply (Hl y).
            simpl in Hyl.
            destruct Hyl as [Hyx | Hinxl].
            - simpl. left. auto.
            - exfalso. apply (Hxl Hinxl).
          }
          - {
            split.
            - {
              intros Hyl. 
              apply Hyl''.
              apply (Hl y).
              simpl.
              right.
              auto.
            }
            - apply Hdupl.
          }
        }
      }
      - rewrite NoDup_cons_iff in Hdup. destruct Hdup. auto.
    }
  }
Qed.

Lemma permute_no_dup {A: Type} (l l': list A) : 
  NoDup l -> NoDup l' -> incl l l' -> incl l' l -> length l = length l'.
Proof.
  intros Hdupl Hdupl' Hincl Hincl'.
  apply (NoDup_incl_length Hdupl) in Hincl.
  apply (NoDup_incl_length Hdupl') in Hincl'.
  lia.
Qed.

Lemma incl_neq_llt {A: Type} (l b: list A) : 
  incl l b -> NoDup l -> NoDup b -> (exists x, In x b /\ ~(In x l)) -> (length l) < (length b).
Proof.
  intros Hincl Hdup Hdup' Hex.
  destruct Hex as [x Hx].
  destruct Hx as [Hb Hl].
  generalize dependent b.
  induction l as [| y l' Hi].
  - destruct b. contradiction. simpl. lia.
  - {
    intros b Hincl Hdupb Hinb.
    rewrite NoDup_cons_iff in Hdup.
    destruct Hdup as [Hy Hdup].
    simpl in Hl.
    cut (~In x l').
    - {
      intros Hxl.
      cut (In y b).
      - {
        intros Hyb.
        destruct (in_permute b y Hyb Hdupb) as [b' Hb'].
        destruct Hb' as [Hbyb' Hb'].
        destruct Hb' as [Hyb'b Hdupb'].
        rewrite (permute_no_dup b (y :: b') Hdupb Hdupb' Hbyb' Hyb'b).
        specialize ((Hi Hdup Hxl) b').
        cut (Datatypes.length l' < Datatypes.length b').
        - {
          simpl.
          lia.
        }
        - {
          apply Hi.
          - {
            intros z Hz. 
            specialize (Hbyb' z). 
            specialize (Hincl z).
            cut (In z (y :: b')).
            - {
              simpl.
              intros Hyz.
              destruct Hyz as [Hyz | Hok].
              - exfalso. rewrite Hyz in Hy. apply (Hy Hz).
              - apply Hok.
            }
            - apply Hbyb'. apply Hincl. simpl. right. apply Hz.
          }
          - rewrite NoDup_cons_iff in Hdupb'. destruct Hdupb' as [_ Hdupb']. apply Hdupb'.
          - {
            specialize (Hbyb' x). 
            simpl in Hbyb'. 
            apply Hbyb' in Hinb. 
            destruct Hinb as [Hyx | Hxb'].
            - rewrite Hyx in *. exfalso. apply Hl. left. auto.
            - auto.
          }
        }
      }
      - apply (Hincl y). simpl. left. auto.
    }
    - intros H. apply Hl. right. apply H.
  }
Qed.
Local Close Scope nat_scope.

Lemma ina_eq_in (l: list positive) (x: positive): InA eq x l <-> In x l.
Proof.
  rewrite InA_alt.
  split; intros Hy.
  - {
    destruct Hy as [y Hy].
    destruct Hy as [Hxy Hin].
    rewrite Hxy.
    auto.
  }
  - {
    exists x. 
    split.
    auto. auto.
  }
Qed.

Lemma nodupa_eq_nodup (l: list positive): NoDupA eq l -> NoDup l.
Proof.
  intros Hno.
  induction l; constructor; inversion Hno.
  - {
    rewrite <-ina_eq_in.
    apply H1. 
  }
  - {
    apply IHl.
    apply H2.
  }
Qed.

Lemma flip_spec (b: bool): flip_bool b = true <-> b = false.
Proof.
  split; destruct b; unfold flip_bool; auto.
Qed.

Ltac sintuition := simpl in *; repeat (intros; intuition; try subst; autorewrite with core in *); try congruence; eauto 1.
Ltac crush_set_step := fail.
Ltac crush_set := unfold flip_bool; repeat crush_set_step.
Ltac crush_set_step ::=
  let H' := fresh "H" in
  sintuition; match goal with
  | [ H : context [if ?X then _ else _] |- _ ] => let Hx := fresh "Hx" in destruct X eqn:Hx
  | [ |- context [if ?X then _ else _] ] => let Hx := fresh "Hx" in destruct X eqn:Hx
  | [ H : context [_ = false] |- _ ] => rewrite <- not_true_iff_false in H
  | [ H : (?p =? ?p0) = true |- _ ] => rewrite Coq.PArith.BinPos.Pos.eqb_eq in H
  | [ H : (?p =? ?p0) <> true |- _ ] => rewrite Coq.PArith.BinPos.Pos.eqb_eq in H
  | [ |- context [_ = false] ] => rewrite <- not_true_iff_false
  | [ |- VarSet.mem _ _ = VarSet.mem ?p ?m] => let Hx := fresh "Hx" in destruct (VarSet.mem p m) eqn:Hx
  | [ H : context [In _ (VarSet.elements _)] |- _ ] => rewrite <- ina_eq_in in H; rewrite VarSet.elements_spec1 in H
  | [ |- context [In _ (VarSet.elements _)] ] => rewrite <- ina_eq_in; rewrite VarSet.elements_spec1
  | [ |- context [NoDup (VarSet.elements _)] ] => apply nodupa_eq_nodup; apply VarSet.elements_spec2w
  | [ |- _] => repeat (rewrite VarSet.mem_spec in *); repeat (rewrite VarSet.add_spec in *); repeat (rewrite VarSet.remove_spec); repeat (rewrite VarSet.union_spec); repeat (rewrite flip_spec in *)
  end.

Lemma eqb_refl (x: positive): (x =? x) = true.
Proof.
  induction x; simpl; auto.
Qed.

Lemma SameLiteralsComm (l l': Literal): SameLiterals l l' = SameLiterals l' l.
Proof.
  destruct l; destruct l'; unfold SameLiterals; auto; apply Coq.PArith.BinPos.Pos.eqb_sym.
Qed.

Lemma SameVarsSameLiterals (l l': Literal): SameVarLiterals l l' = false -> SameLiterals l l' = false.
Proof.
  destruct l; destruct l'; unfold SameLiterals, SameVarLiterals; auto.
Qed.

Lemma OppositeSame (l l': Literal): OppositeLiterals l l' = true -> SameLiterals l l' = false.
Proof.
  destruct l; destruct l'; unfold SameLiterals, OppositeLiterals; intros; auto; inversion H.
Qed.

Lemma ContainsFalse (c: Clause) (l l': Literal): ClauseContains (Or c l') l = false -> ClauseContains c l = false.
Proof.
  intros.
  unfold ClauseContains in H.
  destruct (SameLiterals l' l); inversion H.
  auto.
Qed.

Theorem PropagateRemovesVar (c: Clause) (l: Literal): 
  ClauseContains c l = false -> ~ VarSet.In (LitToVar l) (VarsClause (PropagateClause c l)).
Proof.
  induction c as [| c Hi l']; intros Hcl.
  - cut (VarSet.Empty VarSet.empty). auto. apply VarSet.empty_spec.
  - {
    destruct (OppositeLiterals l l') eqn:Hopp; simpl; rewrite Hopp.
    - apply Hi. unfold ClauseContains in Hcl. rewrite SameLiteralsComm in Hcl. apply OppositeSame in Hopp. rewrite Hopp in Hcl. auto.
    - {
      simpl.
      rewrite VarSet.add_spec.
      intros H.
      destruct H as [H|H].
      - destruct l as [v | v]; destruct l' as [v' | v']; 
        unfold OppositeLiterals in Hopp; simpl in *; subst; 
        rewrite eqb_refl in *; inversion Hcl; inversion Hopp. 
      - apply ContainsFalse in Hcl. apply (Hi Hcl H).
    }
  }
Qed.

Theorem PropagateKeepsVars (c: Clause) (l: Literal): 
  VarSet.Subset (VarsClause (PropagateClause c l)) (VarsClause c).
Proof.
  induction c as [| c Hi l']; simpl; intros x.
  - auto.
  - {
    intros H.
    specialize (Hi x).
    destruct (OppositeLiterals l l') eqn:Hopp; simpl; rewrite VarSet.add_spec.
    - right. apply (Hi H).
    - {
      simpl in H. 
      rewrite VarSet.add_spec in H.
      destruct H as [H|H].
      - left. apply H.
      - right. apply (Hi H).
    }
  }
Qed.

Theorem PropagateKeepsVarsCnf (cnf: CNF) (l: Literal):
  VarSet.Subset (VarsCnf (PropagateCnf cnf l)) (VarsCnf cnf).
Proof.
  induction cnf as [| cnf Hi c]; simpl; intros x.
  - auto.
  - {
    repeat (rewrite VarSet.union_spec).
    intros H.
    destruct H as [H|H].
    - left. specialize ((PropagateKeepsVars c l) x) as Hc. apply (Hc H).
    - right. specialize (Hi x). apply (Hi H).
  }
Qed.

Theorem RemoveKeepsVars (cnf: CNF) (l: Literal): 
  VarSet.Subset (VarsCnf (RemoveSatisfied cnf l)) (VarsCnf cnf).
Proof.
  induction cnf as [| cnf Hi c]; simpl; intros x.
  - auto.
  - {
    repeat (rewrite VarSet.union_spec).
    simpl.
    destruct (ClauseContains c l) eqn:Hcont; simpl; repeat (rewrite VarSet.union_spec).
    - specialize (Hi x). intros Hin. right. auto.
    - {
      intros Hin.
      destruct Hin as [Hin | Hin].
      - left. auto.
      - right. auto.
    }
  }
Qed.

Theorem CleanKeepsVars (cnf: CNF) (l: Literal): 
  VarSet.Subset (VarsCnf (CleanCnf cnf l)) (VarsCnf cnf).
Proof.
  intros x H.
  apply (RemoveKeepsVars cnf l).
  apply (PropagateKeepsVarsCnf (RemoveSatisfied cnf l) l).
  auto.
Qed.

Theorem CleanRemovesVar (cnf: CNF) (l: Literal): 
  ~ VarSet.In (LitToVar l) (VarsCnf (CleanCnf cnf l)).
Proof.
  induction cnf as [| cnf Hi c]; simpl.
  - cut (VarSet.Empty VarSet.empty). auto. apply VarSet.empty_spec.
  - {
    unfold CleanCnf in *.
    unfold RemoveSatisfied.
    destruct (ClauseContains c l) eqn:Hcont; fold RemoveSatisfied.
    - apply Hi.
    - {
      unfold PropagateCnf. fold PropagateCnf.
      unfold VarsCnf.
      rewrite VarSet.union_spec.
      intros H.
      destruct H as [H|H].
      - apply ((PropagateRemovesVar c l) Hcont H).
      - apply (Hi H).
    }
  }
Qed.

Lemma AddIncrementSize (vars': VarSet.t) (p: positive): 
  ~ VarSet.In p vars' -> S (VarSet.cardinal vars') = VarSet.cardinal (VarSet.add p vars').
Proof.
  intros Hin.
  repeat (rewrite VarSet.cardinal_spec).
  transitivity (Datatypes.length (p :: (VarSet.elements vars'))).
  - simpl. f_equal.
  - {
   apply permute_no_dup.
   - constructor; crush_set.
   - crush_set.
   - intros x Hx. crush_set.
   - intros x Hx. crush_set.
  }
Qed.

Theorem FindPureIn (cnf: CNF) (l: Literal): Some l = FindPure cnf -> VarSet.In (LitToVar l) (VarsCnf cnf).
Proof.
  intros H.
  induction cnf.
  - inversion H.
  - {
    destruct c; simpl; rewrite VarSet.union_spec.
    - right. apply IHcnf. rewrite H. auto.
    - {
      destruct c; unfold FindPure in H.
      - left. injection H. intros. crush_set. left. subst. auto.
      - right. fold FindPure in H. auto.
    }
  }
Qed.

Theorem AnyVarIn (cnf: CNF) (p: positive):  AnyVar cnf = Some p -> VarSet.In p (VarsCnf cnf).
Proof.
  apply VarSet.choose_spec1.
Qed.

Definition Vars := fun cnf: CNF => VarSet.cardinal (VarsCnf cnf).

Local Open Scope nat_scope.
Theorem CnfReduces (cnf: CNF) (l: Literal): 
VarSet.In (LitToVar l) (VarsCnf cnf) -> Vars (CleanCnf cnf l) < Vars cnf.
Proof.
  intros Hvarin.
  unfold Vars.
  repeat (rewrite VarSet.cardinal_spec).
  apply (incl_neq_llt (VarSet.elements (VarsCnf (CleanCnf cnf l))) (VarSet.elements (VarsCnf cnf))).
  - {
    specialize (CleanKeepsVars cnf l). 
    intros Hsub.
    intros v Hin.
    specialize (Hsub v).
    crush_set.
  }
  - crush_set.
  - crush_set.
  - {
    exists (LitToVar l).
    split.
    - crush_set.
    - specialize (CleanRemovesVar cnf l). crush_set.
  }
Qed.
Local Close Scope nat_scope.

Lemma MaxOr (b1 b2: bool): Max b1 b2 = true <-> (b1 = true \/ b2 = true).
Proof.
  split; destruct b1; destruct b2; unfold Max; intros; destruct H; auto.
Qed.

Lemma MinAnd (b1 b2: bool): Min b1 b2 = true <-> (b1 = true /\ b2 = true).
Proof.
  split; destruct b1; destruct b2; unfold Max; intros; destruct H; auto.
Qed.

Ltac crush_step := fail.
Ltac crush_solver := unfold Solver, SolverDecreasing in *; destruct (_ : nat); repeat crush_step.
Ltac crush_step ::=
  let H' := fresh "H" in
  sintuition; match goal with
  | [ H : context [ContainsBottom _ = _] |- _ ] => rewrite H in *
  | [ H : context [AnyVar _ = _] |- _ ] => rewrite H in *
  | [ H : context [FindPure _ = _] |- _ ] => rewrite H in *
  | [ H : context [SolverDecreasing _ _ = _] |- _ ] => rewrite H in *
  | [ H : context [OppositeLiterals _ _ = _] |- _ ] => rewrite H in *
  | [ |- _] => repeat (rewrite MaxOr in *); repeat (rewrite MinAnd in *); simpl in *; crush_set
  end.
Lemma if_false_false (b b': bool): (if b then b' else b') = b'.
Proof.
  destruct b; auto.
Qed.

Lemma if_true_false (b: bool): (if b then true else false) = b.
Proof.
  destruct b; auto.
Qed.

Lemma if_some_false (b b': bool): (if b then b' else false) = true -> b = true.
Proof.
  destruct b; auto.
Qed.

Local Open Scope nat_scope.
Lemma VarsNeqZero (cnf: CNF) (c: Clause) (l: Literal): 
  ~ Vars (And cnf (Or c l)) = 0.
Proof.
  intros Hvars.
  unfold Vars in Hvars.
  rewrite VarSet.cardinal_spec in Hvars.
  rewrite length_zero_iff_nil in Hvars.
  cut (VarSet.In (LitToVar l) (VarsCnf (And cnf (Or c l)))).
  - rewrite <- VarSet.elements_spec1. rewrite ina_eq_in. rewrite Hvars. apply in_nil.
  - unfold VarsCnf, VarsClause. rewrite VarSet.union_spec. crush_set.
Qed.
Local Close Scope nat_scope.

Lemma SatNoBottom (cnf: CNF) (vars: nat) (m: Model): 
  SolverDecreasing cnf vars = Some m -> ContainsBottom cnf = false.
Proof.
  intros Hsat.
  destruct (ContainsBottom cnf) eqn:Hbot; crush_solver.
Qed.

Lemma BottomUnsat (cnf: CNF) (m: Model): 
  ContainsBottom cnf = true -> ~Models m cnf.
Proof.
  intros Hcont Hm.
  induction cnf.
  - inversion Hcont.
  - {
    destruct c.
    - {
      unfold EvalClause in Hm.
      fold EvalClause in Hm.
      unfold Models, EvalCnf, Min in Hm.
      rewrite if_false_false in Hm.
      inversion Hm.
    }
    - {
      unfold ContainsBottom in Hcont.
      fold ContainsBottom in Hcont.
      unfold Models, EvalCnf, Min in Hm.
      apply if_some_false in Hm.
      apply IHcnf; auto.
    }
  }
Qed.

Lemma PureRemoved (cnf: CNF) (vars: nat) (m: Model) (l: Literal): 
  SolverDecreasing cnf (S vars) = Some m 
    -> FindPure cnf = Some l
    -> SolverDecreasing cnf (S vars) = ExpandResult (SolverDecreasing (CleanCnf cnf l) vars) l.
Proof.
  intros Hsat Hpure.
  apply SatNoBottom in Hsat.
  crush_solver.
Qed.

Lemma NoPureNoVars (cnf: CNF) (vars: nat) (m: Model): 
  SolverDecreasing cnf (S vars) = Some m 
    -> FindPure cnf = None
    -> AnyVar cnf = None
    -> SolverDecreasing cnf (S vars) = Some VarSet.empty.
Proof.
  intros Hsat Hpure Hany.
  apply SatNoBottom in Hsat.
  crush_solver.
Qed.

Lemma PureEval (cnf: CNF) (m: Model) (l: Literal): 
  Models m cnf -> Some l = FindPure cnf -> EvalLiteral m l = true.
Proof.
  intros Hm Hpure.
  induction cnf; inversion Hpure.
  unfold Models, EvalCnf in Hm.
  rewrite MinAnd in Hm.
  fold EvalCnf in Hm.
  fold (Models m cnf) in Hm.
  destruct Hm as [Hm Hcm].
  destruct c; crush_set.
Qed.

Lemma NotNilElements (vars: VarSet.t) (v: positive): 
  VarSet.In v vars -> ~VarSet.elements vars = nil.
Proof.
  intros Hin Hel.
  rewrite <- VarSet.elements_spec1 in Hin.
  rewrite Hel in Hin.
  rewrite ina_eq_in in Hin.
  auto.
Qed.

Lemma ClauseContainsSkips (c: Clause) (l l': Literal): 
  SameLiterals l l' = false -> ClauseContains (Or c l') l = ClauseContains c l.
Proof.
  intros Hsame.
  unfold ClauseContains.
  rewrite SameLiteralsComm in Hsame.
  rewrite Hsame.
  auto.
Qed.

Lemma RemoveSatisfiedSkips (cnf: CNF) (c: Clause) (l l': Literal):
  SameLiterals l l' = false -> ClauseContains c l = false -> RemoveSatisfied (And cnf (Or c l')) l = And (RemoveSatisfied cnf l) (Or c l').
Proof.
  intros Hsame Hcl.
  unfold RemoveSatisfied.
  rewrite ClauseContainsSkips; auto.
  rewrite Hcl.
  auto.
Qed.

Lemma CleanCnfSkips (cnf: CNF) (c: Clause) (l l': Literal): 
  SameLiterals l l' = false -> ClauseContains c l = false -> CleanCnf (And cnf (Or c l')) l = And (CleanCnf cnf l) (PropagateClause (Or c l') l).
Proof.
  intros Hsame Hcl.
  unfold CleanCnf.
  rewrite RemoveSatisfiedSkips; auto.
Qed.

Ltac crush_set ::= unfold ExpandModel, flip_bool; repeat crush_set_step.

Lemma ContainsLitEvalTrue (m: Model) (c: Clause) (l: Literal): 
  ClauseContains c l = true -> EvalClause (ExpandModel m l) c = true.
Proof.
  intros.
  induction c; simpl in H; auto.
  simpl.
  rewrite MaxOr.
  destruct (SameLiterals l l0) eqn:Hsame.
  - {
    right.
    unfold EvalLiteral.
    destruct l; destruct l0; crush_set.
    subst. rewrite VarSet.remove_spec in Hx0. crush_set.
  }
  - {
    left.
    rewrite SameLiteralsComm in Hsame.
    rewrite Hsame in H.
    apply (IHc H).
  }
Qed.

Lemma mem_remove_false (vars: VarSet.t) (p: positive): VarSet.mem p (VarSet.remove p vars) = false.
Proof.
  crush_set.
Qed.

Lemma EvalPropagate (m: Model) (c: Clause) (l: Literal): 
 ClauseContains c l = false -> EvalClause (ExpandModel m l) c = EvalClause m (PropagateClause c l).
Proof.
  induction c; auto.
  unfold PropagateClause.
  destruct (OppositeLiterals l l0) eqn:Hopp; fold PropagateClause.
  - {
    intros Hcont.
    rewrite <- IHc. unfold EvalClause.
    cut (EvalLiteral (ExpandModel m l) l0 = false).
    - intros Hlit. rewrite Hlit. unfold Max. rewrite if_true_false. auto.
    - {
      destruct l; destruct l0; unfold OppositeLiterals in Hopp; 
      inversion Hopp; unfold EvalLiteral; unfold ExpandModel;
      rewrite Coq.PArith.BinPos.Pos.eqb_eq in Hopp; subst.
      - {
        cut (VarSet.mem p0 (VarSet.add p0 m) = true); intros; repeat (rewrite H); auto.
        rewrite VarSet.mem_spec. rewrite VarSet.add_spec. auto.
      }
      - apply mem_remove_false.
    }
    - apply (ContainsFalse c l l0 Hcont).
  }
  - {
    unfold EvalClause. fold EvalClause.
    intros Hcont.
    cut (EvalLiteral (ExpandModel m l) l0 = EvalLiteral m l0).
    - intros Heval. rewrite Heval. f_equal. apply IHc. apply (ContainsFalse c l l0 Hcont).
    - {
      unfold ClauseContains in Hcont. 
      fold ClauseContains in Hcont.
      destruct (SameLiterals l0 l) eqn:Hsame; inversion Hcont.
      destruct l; destruct l0; unfold OppositeLiterals in Hopp; 
      unfold SameLiterals in Hsame; unfold ExpandModel, EvalLiteral, flip_bool; 
      crush_set; exfalso; rewrite VarSet.remove_spec in Hx.
      - apply Hx0. destruct Hx. apply H.
      - apply Hx. auto.
    }
  }
Qed.

Lemma NoVarsModelsEmpty (cnf: CNF): 
  ContainsBottom cnf = false -> AnyVar cnf = None -> Models VarSet.empty cnf.
Proof.
  unfold AnyVar.
  intros Hcont Hany.
  apply VarSet.choose_spec2 in Hany.
  unfold Models, EvalCnf.
  induction cnf; auto.
  fold EvalCnf in IHcnf.
  destruct c.
  - {
    unfold ContainsBottom in Hcont.
    inversion Hcont.
  }
  - {
    cut (VarSet.In (LitToVar l) (VarsCnf (And cnf (Or c l)))).
    - {
      intros Hin.
      exfalso.
      specialize (Hany (LitToVar l)).
      auto.
    }
    - crush_set.
  }
Qed.

Lemma ModelsClean (cnf: CNF) (m: Model) (l: Literal): 
  Models m (CleanCnf cnf l) -> Models (ExpandModel m l) cnf.
Proof.
  induction cnf; unfold Models in *; simpl; intros Hm.
  - unfold EvalCnf. auto.
  - {
    cut (EvalCnf (ExpandModel m l) cnf = true).
    - {
      cut (EvalClause (ExpandModel m l) c = true).
      - intros H1 H2. rewrite H1. rewrite H2. auto.
      - {
        destruct (ClauseContains c l) eqn:Hcont.
        - apply (ContainsLitEvalTrue _ _ _ Hcont).
        - {
          rewrite (EvalPropagate _ _ _ Hcont). 
          unfold CleanCnf, RemoveSatisfied, PropagateCnf in Hm. 
          rewrite Hcont in Hm.
          simpl in Hm.
          rewrite MinAnd in Hm.
          crush_set.
        }
      }
    }
    - {
      apply IHcnf.
      destruct (ClauseContains c l) eqn:Hcont;
      unfold CleanCnf, RemoveSatisfied, PropagateCnf, EvalCnf in Hm; rewrite Hcont in Hm;
      fold RemoveSatisfied in Hm; fold PropagateCnf in Hm; fold EvalCnf in Hm; unfold CleanCnf; auto.
      rewrite MinAnd in Hm.
      crush_set.
    }
  }
Qed.

Lemma EvalExpand (m: Model) (c: Clause) (l: Literal): 
  EvalLiteral m l = true -> EvalClause m c = true -> EvalClause (ExpandModel m l) c = true.
Proof.
  intros Hl Hc.
  induction c.
  - inversion Hc.
  - {
    unfold EvalClause in *.
    fold EvalClause in *.
    rewrite MaxOr in *.
    destruct Hc as [Hc|Hc].
    - crush_set.
    - {
      right. unfold EvalLiteral in *. destruct l; destruct l0; crush_set.
      - destruct Hx; crush_set.
      - split; crush_set.
      - rewrite VarSet.remove_spec in Hx. crush_set.
    }
  }
Qed.

Lemma NotModelsClean (cnf: CNF) (m: Model) (l: Literal): 
  (forall m', ~ Models m' (CleanCnf cnf l)) -> EvalLiteral m l = true -> ~ Models m cnf.
Proof.
  intros Hunsat Hl Hm.
  specialize (Hunsat m).
  induction cnf; unfold Models in *.
  - {
    unfold CleanCnf, RemoveSatisfied, PropagateCnf, EvalCnf in Hunsat.
    auto.
  }
  - {
    crush_step.
    destruct Hm as [Hm Hecl].
    apply IHcnf; auto.
    intros Hunsat'.
    apply Hunsat.
    destruct (ClauseContains c l) eqn:Hcont; unfold CleanCnf, RemoveSatisfied;
    rewrite Hcont; fold RemoveSatisfied; auto.
    unfold PropagateCnf. fold PropagateCnf.
    unfold EvalCnf. fold EvalCnf.
    rewrite MinAnd.
    split; auto.
    induction c.
    - inversion Hecl.
    - {
      destruct (OppositeLiterals l l0) eqn:Hopp.
      - {
        crush_step. 
        rewrite MaxOr in Hecl.
        destruct (SameLiterals l0 l) eqn:Hsame; inversion Hcont.
        destruct Hecl as [Hcm|Hlm].
        - {
          apply IHc; auto.
          rewrite SameLiteralsComm in Hsame.
          rewrite (CleanCnfSkips cnf c l l0 Hsame Hcont) in Hunsat.
          unfold PropagateClause in Hunsat.
          rewrite Hopp in Hunsat.
          fold PropagateClause in Hunsat.
          unfold CleanCnf, RemoveSatisfied.
          rewrite H0.
          fold RemoveSatisfied.
          unfold PropagateCnf.
          fold PropagateCnf.
          unfold CleanCnf in Hunsat.
          apply Hunsat.
        }
        - destruct l; destruct l0; unfold EvalLiteral, OppositeLiterals in *; crush_set.
      }
      - {
        unfold PropagateClause.
        rewrite Hopp.
        fold PropagateClause.
        unfold EvalClause.
        fold EvalClause.
        rewrite MaxOr.
        destruct (SameLiterals l0 l) eqn:Hsame.
        - crush_step.
        - {
          unfold EvalClause in Hecl.
          fold EvalClause in Hecl.
          rewrite MaxOr in Hecl.
          unfold ClauseContains in Hcont.
          rewrite Hsame in Hcont.
          destruct Hecl as [Hecl|Hecl]; fold ClauseContains in Hcont.
          - {
            left.
            apply IHc; auto.
            rewrite SameLiteralsComm in Hsame.
            rewrite (CleanCnfSkips cnf c l l0 Hsame Hcont) in Hunsat.
            unfold PropagateClause in Hunsat.
            rewrite Hopp in Hunsat.
            fold PropagateClause in Hunsat.
            unfold CleanCnf, RemoveSatisfied.
            rewrite Hcont.
            fold RemoveSatisfied.
            unfold PropagateCnf.
            fold PropagateCnf.
            unfold CleanCnf in Hunsat.
            unfold EvalCnf in *.
            fold EvalCnf in *.
            intros H.
            apply Hunsat.
            rewrite <- H.
            f_equal.
            unfold EvalClause.
            fold EvalClause.
            assert (EvalClause m (PropagateClause c l) = true).
            - {
              rewrite <- (EvalPropagate m c l Hcont).
              apply EvalExpand; auto.
            }
            - repeat (rewrite H0). auto.
          }
          - auto.
        }
      }
    }
  }
Qed.

Local Open Scope nat_scope.
Lemma le_zero_eq_zero (n: nat): n <= 0 -> n = 0.
Proof.
  lia.
Qed.

Theorem CorrectSatDecreasing (cnf: CNF) (m: Model) (vars: nat): 
   Vars cnf <= vars -> SolverDecreasing cnf vars = Some m -> Models m cnf.
Proof.
  generalize dependent m.
  generalize dependent cnf.
  induction vars as [|vars Hi]; intros cnf m Hvars Hsat; apply SatNoBottom in Hsat as Hbot.
  - {
    apply le_zero_eq_zero in Hvars.
    unfold SolverDecreasing in Hsat.
    rewrite Hbot in Hsat.
    inversion Hsat.
    destruct cnf.
    - unfold Models, EvalCnf. auto.
    - {
      destruct c.
      - inversion Hbot.
      - exfalso. apply (VarsNeqZero _ _ _ Hvars).
    }
  }  
  - {
    destruct (FindPure cnf) eqn:Hpure.
    - {
      apply (PureRemoved _ _ _ l) in Hsat as Hfound; auto.
      rewrite Hsat in Hfound. 
      destruct (SolverDecreasing (CleanCnf cnf l)) eqn:Hdecr; inversion Hfound.
      specialize (Hi (CleanCnf cnf l) m0).
      apply ModelsClean.
      apply Hi; auto.
      apply le_S_n.
      transitivity (Vars cnf); auto.
      apply CnfReduces.
      symmetry in Hpure.
      apply (FindPureIn _ _ Hpure).
    }
    - {
      destruct (AnyVar cnf) eqn:Hany;
      unfold SolverDecreasing in Hsat; rewrite Hbot in Hsat;
      rewrite Hpure in Hsat; rewrite Hany in Hsat; 
      fold SolverDecreasing in Hsat.
      - {
        destruct (SolverDecreasing (CleanCnf cnf (Var p)) vars) eqn:Hguess.
        - {
          unfold ExpandResult in Hsat.
          injection Hsat.
          intros Hm.
          rewrite <- Hm.
          cut (Models (ExpandModel m0 (Var p)) cnf); auto.
          specialize (Hi (CleanCnf cnf (Var p)) m0).
          apply ModelsClean.
          apply Hi; auto.
          apply le_S_n.
          transitivity (Vars cnf); auto.
          apply CnfReduces.
          unfold AnyVar in Hany.
          apply VarSet.choose_spec1 in Hany.
          auto.
        }
        - {
          destruct (SolverDecreasing (CleanCnf cnf (Not p)) vars) eqn:Hguess'.
          - {
            injection Hsat.
            intros Hm.
            rewrite <- Hm.
            cut (Models (ExpandModel m0 (Not p)) cnf); auto.
            apply ModelsClean.
            specialize (Hi (CleanCnf cnf (Not p)) m0).
            apply Hi; auto.
            apply le_S_n.
            transitivity (Vars cnf); auto.
            apply CnfReduces.
            unfold AnyVar in Hany.
            apply VarSet.choose_spec1 in Hany.
            auto.
          }
          - inversion Hsat.
        }
      }
      - {
        injection Hsat.
        intros Hm.
        rewrite <- Hm.
        apply NoVarsModelsEmpty; auto.
      }
    }
  }
Qed.

Theorem CorrectUnsatDecreasing (cnf: CNF) (vars: nat): 
   Vars cnf <= vars -> SolverDecreasing cnf vars = None -> ~(exists m, Models m cnf).
Proof.
  intros Hvars Hunsat Hm.
  destruct Hm as [m Hm].
  generalize dependent m.
  generalize dependent cnf.
  induction vars as [|vars Hi]; intros cnf Hvars Hunsat m Hm.
  - {
    apply le_zero_eq_zero in Hvars.
    unfold SolverDecreasing in Hunsat.
    destruct (ContainsBottom cnf) eqn:Hcont; auto.
    - apply (BottomUnsat _ _ Hcont Hm).
    - {
      destruct cnf.
      - inversion Hunsat.
      - {
        destruct c.
        - crush_solver.
        - apply (VarsNeqZero _ _ _ Hvars).
      }
    }
  }
  - {
    destruct (ContainsBottom cnf) eqn:Hcont.
    - apply (BottomUnsat _ _ Hcont Hm).
    - {
      destruct (FindPure cnf) eqn:Hpure.
      - {
        assert (SolverDecreasing cnf (S vars) = ExpandResult (SolverDecreasing (CleanCnf cnf l) vars) l) as Hfound.
        - crush_solver.
        - {
          rewrite Hunsat in Hfound. 
          destruct (SolverDecreasing (CleanCnf cnf l)) eqn:Hdecr; inversion Hfound.
          symmetry in Hpure.
          specialize (CnfReduces cnf l (FindPureIn _ _ Hpure)).
          intros Hvars'.
          assert (Vars (CleanCnf cnf l) <= vars) as Hvars''.
          - {
            apply le_S_n.
            transitivity (Vars cnf); auto.
          }
          - {
            specialize (Hi (CleanCnf cnf l) Hvars'' Hdecr).
            refine (NotModelsClean _ _ _ Hi _ Hm).
            apply (PureEval cnf m l); auto.
          }
        }
      }
      - {
        destruct (AnyVar cnf) eqn:Hany;
        unfold SolverDecreasing in Hunsat; rewrite Hcont in Hunsat;
        rewrite Hpure in Hunsat; rewrite Hany in Hunsat; 
        fold SolverDecreasing in Hunsat.
        - {
          destruct (SolverDecreasing (CleanCnf cnf (Var p)) vars) eqn:Hguess.
          - inversion Hunsat.
          - {
            destruct (SolverDecreasing (CleanCnf cnf (Not p)) vars) eqn:Hguess'.
            - inversion Hunsat.
            - {
              destruct (VarSet.mem p m) eqn:Hmem.
              - {
                specialize (CnfReduces cnf (Var p) (AnyVarIn cnf p Hany)).
                intros Hvars'.
                assert (Vars (CleanCnf cnf (Var p)) <= vars) as Hvars''.
                - lia.
                - {
                  specialize (Hi (CleanCnf cnf (Var p)) Hvars'' Hguess).
                  refine (NotModelsClean _ _ _ Hi _ Hm).
                  auto.
                }
              }
              - {
                specialize (CnfReduces cnf (Not p) (AnyVarIn cnf p Hany)).
                intros Hvars'.
                assert (Vars (CleanCnf cnf (Not p)) <= vars) as Hvars''.
                - lia.
                - {
                  specialize (Hi (CleanCnf cnf (Not p)) Hvars'' Hguess').
                  refine (NotModelsClean _ _ _ Hi _ Hm).
                  crush_set.
                }
              }
            }
          }
        }
        - inversion Hunsat.
      }
    }
  }
Qed.

Local Close Scope nat_scope.
Local Close Scope positive_scope.