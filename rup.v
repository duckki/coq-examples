Set Implicit Arguments.
Require Import List Arith Omega Sorting Orders.

(*=============================================================================
 * rup proof checker implementation
 *===========================================================================*)

Module dpll.
  Load dpllResolution.
End dpll.
Import dpll.

Definition litSign l := match l with pos _ => true | neg _ => false end.

Module LitOrder <: TotalLeBool.
  Definition t := lit.
  Definition leb x y := leb (litVar x) (litVar y).
  Theorem leb_total : forall x y, leb x y = true \/ leb y x = true.
    intros.
    edestruct (le_or_lt (litVar x) (litVar y)).
    left; apply leb_correct; auto.
    right; apply leb_correct; omega.
  Qed.
End LitOrder.

Module Import LitSort := Sort LitOrder.

Section rup.
  Variable F : formula.

  Definition asmt := list (option bool).

  Definition getVal (l : asmt) v : option bool := nth v l None.

  Definition okLit assign l :=
    match getVal assign (litVar l) with
      | None => true
      | Some b => match l with
                    | pos _ => b
                    | neg _ => negb b
                  end
    end.

  Fixpoint okClause assign c :=
    match c with
      | nil => false
      | l :: c' => if okLit assign l then true else okClause assign c'
    end.

  Fixpoint okFormula assign f :=
    match f with
      | nil => true
      | c :: f' => if okClause assign c then okFormula assign f' else false
    end.

  Fixpoint extendAsmt n (b : bool) := (* n is the # of padding *)
    match n with
      | 0 => Some b :: nil
      | S n' => None :: extendAsmt n' b
    end.
  
  Fixpoint buildAsmt s c :=
    match c with
      | nil => Some s
      | l :: c' =>
        match leb (length s) (litVar l) with
          | false => None
          | true =>
            let b := negb (litSign l) in
            let s' := s ++ extendAsmt (litVar l - length s) b in
            buildAsmt s' c'
        end
    end.

  Definition rup c :=
    let r := buildAsmt nil (sort c) in
    match r with
      | Some s => if okFormula s F then false else true
      | None => false
    end.

End rup.


(*=============================================================================
 * dropLits facts
 *===========================================================================*)

Lemma remove_lit_assoc : forall c x y, remove_lit x (remove_lit y c)
                                       = remove_lit y (remove_lit x c).
  unfold remove_lit; induction c; simpl; auto; intros.
  repeat match goal with
           | _ => congruence
           | _ => progress simpl
           | |- context[if ?X then _ else _] => destruct X
         end.
Qed.

Lemma dropLitsClause_cons : forall l c x,
                 dropLitsClause x (l :: c)
                 = remove_lit l (dropLitsClause x c).
  induction c; simpl; auto; intros.
  rewrite <- IHc, remove_lit_assoc; simpl; auto.
Qed.
  

(*=============================================================================
 * pf facts
 *===========================================================================*)

Lemma pf_dropLits_cons : forall f l c x, pf (dropLits f (l :: c)) x
                          -> pf (dropLits f c) (l :: x).
  induction 1.
  {
      edestruct In_dropLits_ex as [? [] ]; eauto 3.
      subst.
      assert (In (dropLitsClause x c) (dropLits f c)).
      solve [apply In_dropLits; auto].
      eapply pf_sublist; eauto 3.
      rewrite dropLitsClause_cons.
      apply Forall_forall; intros; simpl.
      destruct (eq_lit_dec x0 l); subst; auto.
      right.
      apply In_neq_remove; auto.
  }
  {
    assert (resolvent (l :: cr)
                      (l :: c3)
                      (l ::c4) v).
    {
      destruct H1; split; simpl.
      destruct (eq_lit_dec (pos v) l); auto; congruence.
      destruct (eq_lit_dec (neg v) l); auto.
    }
    eauto 3.
  }
Qed.

Lemma pf_dropLits_app : forall f c x, pf (dropLits f c) x
                                  -> pf f (c ++ x).
  induction c; try solve [rewrite dropLits_nil; auto].
  intros.
  apply pf_dropLits_cons in H.
  apply IHc in H.
  eapply pf_sublist; try eassumption.
  apply Forall_forall; intros.
  apply in_or_app; simpl.
  edestruct in_app_or; eauto 3.
  simpl in *; tauto.
Qed.

Lemma pf_dropLits_nil : forall f c, pf (dropLits f c) nil -> pf f c.
  intros.
  replace c with (c ++ nil) by (autorewrite with list; auto).
  apply pf_dropLits_app; auto.
Qed.


(*=============================================================================
 * rup facts
 *===========================================================================*)

Lemma okFormula_false : forall s f, okFormula s f = false
                         -> exists c, In c f /\ okClause s c = false.
  induction f; simpl; try congruence.
  destruct (okClause s a) eqn:?; eauto 4; intros.
  destruct IHf as [? [] ]; eauto 4.
Qed.

Lemma okClause_false : forall c s l, okClause s c = false -> In l c
                                     -> okLit s l = false.
  induction c; simpl; try tauto; intros.
  destruct (okLit s a) eqn:?; try congruence.
  destruct H0; subst; auto.
Qed.

Lemma length_extendAsmt : forall n b, length (extendAsmt n b) = S n.
  induction n; simpl; auto.
Qed.

Lemma nth_extendAsmt : forall n b, nth n (extendAsmt n b) None = Some b.
  induction n; simpl; auto.
Qed.

Lemma length_app_extendAsmt : forall g n b, length g <= n
                     -> length (g ++ extendAsmt (n - length g) b) = S n.
  intros; autorewrite with list.
  rewrite length_extendAsmt; omega.
Qed.

Lemma nth_app_extendAsmt : forall g n b, length g <= n
             -> nth n (g ++ extendAsmt (n - length g) b) None = Some b.
  intros; rewrite app_nth2 by omega.
  apply nth_extendAsmt.
Qed.

Lemma buildAsmt_getVal : forall c g s n, buildAsmt g c = Some s -> n < length g
                                         -> getVal s n = nth n g None.
  induction c; simpl; try solve [inversion 1; auto]; intros.
  destruct (leb (length g) (litVar a)) eqn:?; try congruence; intros.
  apply leb_iff in Heqb.
  erewrite IHc; try eassumption.
  apply app_nth1; auto.
  autorewrite with list; omega.
Qed.

Hint Resolve nth_app_extendAsmt.

Lemma buildAsmt_In_getVal : forall s l c g, buildAsmt g c = Some s -> In l c
                              -> getVal s (litVar l) = Some (negb (litSign l)).
  induction c; simpl; try tauto; intros.
  destruct (leb (length g) (litVar a)) eqn:?; try congruence.
  destruct H0; subst.
  {
    apply leb_iff in Heqb.
    erewrite buildAsmt_getVal; eauto 2.
    rewrite length_app_extendAsmt; auto.
  }
  {
    eapply IHc; eauto 3.
  }
Qed.

Lemma buildAsmt_sort_In_getVal : forall s c l, buildAsmt nil (sort c) = Some s
                   -> In l c -> getVal s (litVar l) = Some (negb (litSign l)).
  intros.
  eapply buildAsmt_In_getVal; eauto 3.
  eapply Permutation.Permutation_in; try apply Permuted_sort; auto.
Qed.

Lemma nth_extendAsmt_lt : forall b m n, n < m
                            -> nth n (extendAsmt m b) None = None.
  induction m; simpl; intros; try omega.
  destruct n; auto.
  apply IHm; omega.
Qed.

Lemma buidAsmt_not_In_getVal : forall s n c g, ~ In (pos n) c -> ~ In (neg n) c
                         -> buildAsmt g c = Some s
                         -> length g <= n -> getVal s n = None.
  induction c; simpl.
  {
    unfold getVal; inversion 3; subst; intros.
    apply nth_overflow; auto.
  }
  {
    intros.
    destruct (leb (length g) (litVar a)) eqn:?; try congruence.
    apply leb_iff in Heqb.
    destruct (le_lt_dec n (litVar a)).
    {
      assert (n < litVar a).
      {
        inversion l; try omega.
        exfalso.
        destruct a; subst; simpl in *; tauto.
      }
      clear l.
      assert (getVal s n
              = nth n (g ++ extendAsmt (litVar a - length g) (negb (litSign a)))
                    None).
      {
        eapply buildAsmt_getVal; eauto 3.
        rewrite length_app_extendAsmt; omega.
      }
      rewrite H4.
      rewrite app_nth2 by auto.
      apply nth_extendAsmt_lt; omega.
    }
    {
      eapply IHc; eauto 3; try tauto.
      erewrite length_app_extendAsmt by auto; omega.
    }
  }
Qed.

Lemma buildAsmt_not_In_getVal' : forall c s n, ~ In (pos n) c -> ~ In (neg n) c
                         -> buildAsmt nil c = Some s -> getVal s n = None.
  intros.
  eapply buidAsmt_not_In_getVal; eauto 3.
  simpl; omega.
Qed.

Lemma buildAsmt_getVal_In : forall s b n c, getVal s n = Some b
                        -> buildAsmt nil c = Some s -> In (mkLit (negb b) n) c.
  destruct b; intros; simpl.
  {
    destruct (in_dec eq_lit_dec (neg n) c); auto.
    destruct (in_dec eq_lit_dec (pos n) c); auto.
    {
      exfalso.
      eapply buildAsmt_In_getVal in H0; eauto 3.
      simpl in *; congruence.
    }
    {
      exfalso.
      eapply buildAsmt_not_In_getVal' in H0; eauto 3.
      congruence.
    }
  }
  {
    destruct (in_dec eq_lit_dec (pos n) c); auto.
    destruct (in_dec eq_lit_dec (neg n) c); auto.
    {
      exfalso.
      eapply buildAsmt_In_getVal in H0; eauto 3.
      simpl in *; congruence.
    }
    {
      exfalso.
      eapply buildAsmt_not_In_getVal' in H0; eauto 3.
      congruence.
    }
  }
Qed.


(*=============================================================================
 * LitSort facts
 *===========================================================================*)

Hint Constructors StronglySorted.

Definition ltLit x y := litVar x < litVar y.

Lemma StronglySorted_buildAsmt : forall l g, buildAsmt g l <> None
                                   -> Forall (fun x => length g <= litVar x) l
                                      /\ StronglySorted ltLit l.
  induction l; simpl; auto; intros.
  destruct (leb (length g) (litVar a)) eqn:?; try congruence; intros.
  apply leb_iff in Heqb.
  edestruct IHl; eauto 3.
  rewrite length_app_extendAsmt in H0 by auto.
  split.
  {
    constructor; auto.
    eapply Forall_impl; eauto 3.
    simpl; intros; omega.
  }
  {
    unfold ltLit; constructor; auto.
  }
Qed.

Lemma StronglySorted_buildAsmt' : forall l, buildAsmt nil l <> None
                                  -> StronglySorted ltLit l.
  intros; eapply StronglySorted_buildAsmt; eauto 2.
Qed.
Hint Resolve StronglySorted_buildAsmt'.


(*=============================================================================
 * sublist facts
 *===========================================================================*)

Lemma sublist_of_nil : forall A (l : list A), sublist l nil -> l = nil.
  destruct l; auto.
  inversion_clear 1; simpl in *; tauto.
Qed.


(*=============================================================================
 * dropLits facts
 *===========================================================================*)

Hint Resolve Permutation.Permutation_sym Permutation.Permutation_in.
Hint Resolve Permuted_sort.

Lemma okLit_false_In : forall s a c, buildAsmt nil (sort c) = Some s
                         -> okLit s a = false -> In a c.
  unfold okLit; intros.
  destruct (getVal s (litVar a)) eqn:?; try congruence.
  assert (In (mkLit (negb b) (litVar a)) (sort c)).
  solve [eapply buildAsmt_getVal_In; eauto 3].
  destruct a; subst; [ | rewrite H0 in *]; simpl in *; eauto 4.
Qed.

Lemma In_dropLits : forall f c x, In c f
                                  -> In (dropLitsClause c x) (dropLits f x).
  induction f; simpl; try tauto; destruct 1; subst; auto.
Qed.

Lemma dropLitsClause_cons' : forall l x c, In l x
                           -> dropLitsClause (l :: c) x = dropLitsClause c x.
  induction x; simpl; try tauto; destruct 1; subst.
  destruct (eq_lit_dec l l); congruence.
  destruct (eq_lit_dec a l); auto.
Qed.
  
Lemma okClause_false_dropLitsClause_nil : forall c s x,
                   buildAsmt nil (sort c) = Some s
                   -> okClause s x = false -> sublist (dropLitsClause x c) nil.
  induction x; simpl; intros.
  solve [rewrite dropLitsClause_nil; auto].
  destruct (okLit s a) eqn:?; try congruence.
  rewrite dropLitsClause_cons'; auto.
  eapply okLit_false_In; eauto 3.
Qed.

Lemma okFormula_false_dropLits : forall f c s, buildAsmt nil (sort c) = Some s
                   -> okFormula s f = false -> In nil (dropLits f c).
  intros.
  edestruct okFormula_false as [? [] ]; eauto 3.
  assert (dropLitsClause x c = nil).
  {
    apply sublist_of_nil.
    eapply okClause_false_dropLitsClause_nil; eauto 3.
  }
  rewrite <- H3.
  apply In_dropLits; auto.
Qed.


(*=============================================================================
 * rup => pf
 *===========================================================================*)

Theorem rup_sound : forall f c, rup f c = true -> pf f c.
  unfold rup; intros.
  destruct (buildAsmt nil (sort c)) eqn:?; try congruence.
  destruct (okFormula l f) eqn:?; try congruence.
  apply pf_dropLits_nil.
  constructor.
  eapply okFormula_false_dropLits; eauto 3.
Qed.
Hint Resolve rup_sound.


(*=============================================================================
 * the complete rup proof checker
 *===========================================================================*)

Fixpoint rupRun f l :=
  match l with
    | nil => false (* incomplete proof *)
    | c :: l' =>
      match rup f c with
        | false => false
        | true =>
          match c with
            | nil => true (* properly ending proof *)
            | _ => rupRun (c :: f) l'
          end
      end
  end.


(*=============================================================================
 * the soundness of rupRun
 *===========================================================================*)

Lemma pf_cons : forall c f d, pf (c :: f) d -> pf f c -> pf f d.
  induction 1; intros.
  - inversion_clear H; subst; auto.
  - econstructor 2; try apply H1; auto.
Qed.
Hint Resolve pf_cons.

Theorem rupRun_sound : forall l f, rupRun f l = true -> pf f nil.
  induction l; simpl; try congruence; intros.
  destruct (rup f a) eqn:?; try congruence.
  destruct a; eauto 4.
Qed.

Corollary rupRun_refutable : forall l f, rupRun f l = true -> refutable f nil.
  intros; eapply pf_refutable, rupRun_sound; eauto 3.
Qed.
