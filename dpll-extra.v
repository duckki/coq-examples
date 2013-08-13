Set Implicit Arguments.
Load dpll.

(*=============================================================================
 * more dpll facts
 *===========================================================================*)

Lemma okFormula_false_ex : forall l f, okFormula l f = false
                     -> exists c, In c f /\ okClause l c = false.
  induction f; simpl; try congruence; intros.
  destruct (okClause l a) eqn:?; eauto 4.
  solve [destruct IHf as [? [] ]; eauto 4].
Qed.

Lemma okLit_app : forall l x b y, okLit l x = b
                                   -> litVar x < length l
                                   -> okLit (l ++ y) x = b.
  unfold okLit; intros.
  assert (litVar x < length (l ++ y)).
  solve [autorewrite with list; simpl; omega].
  rewrite getVal_Some in * by auto.
  destruct x; rewrite app_nth1 by auto; auto.
Qed.

Lemma okClause_app : forall l b y x, okClause l x = b
                                   -> wf_clause (length l) x
                                   -> okClause (l ++ y) x = b.
  induction x; simpl; auto; intros.
  erewrite okLit_app by auto; auto.
  destruct (okLit l a) eqn:?; eauto 3.
Qed.

Lemma okFormula_app : forall l b y f, okFormula l f = b
                                  -> wf_formula (length l) f
                                  -> okFormula (l ++ y) f = b.
  induction f; simpl; auto; intros.
  erewrite okClause_app by auto.
  destruct (okClause l a) eqn:?; eauto 3.
Qed.  

Lemma okLit_app' : forall l x y, okLit l x = false
                                 -> okLit (l ++ y) x = false.
  unfold okLit; intros.
  destruct (le_lt_dec (length l) (litVar x)).
  rewrite getVal_None in * by auto; congruence.
  assert (litVar x < length (l ++ y)) by (autorewrite with list; omega).
  rewrite getVal_Some in * by auto.
  destruct x; rewrite app_nth1 by auto; auto.
Qed.

Lemma okClause_app' : forall l y x, okClause l x = false
                                   -> okClause (l ++ y) x = false.
  induction x; simpl; auto; intros.
  destruct (okLit l a) eqn:?; try congruence.
  erewrite okLit_app' by auto; auto.
Qed.

Lemma okFormula_app' : forall l y f, okFormula l f = false
                                     -> okFormula (l ++ y) f = false.
  induction f; simpl; auto; intros.
  destruct (okClause l a) eqn:?; eauto 3.
  destruct (okClause (l ++ y) a) eqn:?; eauto 3.
  erewrite okClause_app' in * by auto; congruence.
Qed.  

Lemma getVal_Some_inv : forall v m b, getVal m v = Some b
                                      -> v < length m /\ nth v m true = b.
  intros.
  destruct (le_lt_dec (length m) v).
  rewrite getVal_None in * by auto; congruence.
  rewrite getVal_Some in * by auto.
  inversion_clear H; auto.
Qed.


(*=============================================================================
 * sublist
 *===========================================================================*)

Section sublist.

  Ltac e := eauto 3 with list.

  Local Hint Constructors Forall : list.
  Local Hint Resolve in_or_app Forall_impl : list.

  Variable A : Type.

  Definition sublist (x y : list A) := List.Forall (fun a => In a y) x.

  Lemma sublist_refl : forall (x : list A), sublist x x.
    unfold sublist; induction x; e.
    constructor; simpl; e.
    eapply Forall_impl; try eassumption; e.
  Qed.

  Lemma sublist_app : forall (l x y : list A), sublist l x \/ sublist l y
                                                 -> sublist l (x ++ y).
    induction l.
    {
      unfold sublist; simpl; intros; e.
    }
    {
      unfold sublist; simpl; intros.
      constructor.
      destruct H; inversion_clear H; e.
      apply IHl.
      destruct H; inversion_clear H; e.
    }
  Qed.

  Lemma sublist_In : forall x (a : A) y, sublist x y -> In a x -> In a y.
    induction x; simpl; try tauto; inversion_clear 1; destruct 1; subst; auto.
  Qed.

End sublist.

Local Hint Resolve sublist_refl sublist_app sublist_In.


(*=============================================================================
 * resolvent
 *===========================================================================*)

Theorem eq_lit_dec : forall x y : lit, { x = y } + { x <> y }.
  decide equality; apply NPeano.Nat.eq_dec.
Qed.

Definition remove_lit := remove eq_lit_dec.
  
Definition resolvent cr c1 c2 v :=
  let c1' := remove_lit (pos v) c1 in
  let c2' := remove_lit (neg v) c2 in
  sublist c1' cr /\ sublist c2' cr.


(*=============================================================================
 * resolvent facts
 *===========================================================================*)

Lemma interpClause_drop_lit : forall i l c, interpClause i c = true
                   -> interpLit i l = false
                   -> interpClause i (remove_lit l c) = true.
  induction c; simpl; try congruence; intros.
  destruct (eq_lit_dec l a); subst.
  rewrite H0 in H; auto.
  simpl; destruct (interpLit i a) eqn:?; simpl in *; auto.
Qed.

Lemma interpClause_exists : forall i x, interpClause i x = true
                             -> exists l, In l x /\ interpLit i l = true.
  induction x; simpl; try congruence; intros.
  destruct (interpLit i a) eqn:?; eauto; simpl in *.
  destruct IHx as [? [] ]; eauto.
Qed.

Lemma interpClause_In : forall l i x, interpLit i l = true -> In l x
                                      -> interpClause i x = true.
  induction x; simpl; try tauto; intros.
  destruct H0; subst.
  rewrite H; auto.
  destruct (interpLit i a) eqn:?; eauto; simpl in *.
Qed.

Lemma interpClause_sublist : forall i x y, interpClause i x = true
                               -> sublist x y -> interpClause i y = true.
  intros.
  edestruct interpClause_exists as [? [] ]; try eassumption.
  eapply interpClause_In; try eassumption.
  eapply Forall_forall in H0; eassumption.
Qed.

Theorem resolvent_sound : forall c1 c2 v i cr, resolvent cr c1 c2 v
       -> interpClause i c1 = true -> interpClause i c2 = true
       -> interpClause i cr = true.
  unfold resolvent; simpl; intros.
  destruct H.
  destruct (i v) eqn:?.
  {
    eapply interpClause_sublist; try apply H2.
    apply interpClause_drop_lit; auto.
    unfold interpLit; rewrite Heqb; auto.
  }
  {
    eapply interpClause_sublist; try apply H.
    apply interpClause_drop_lit; auto.
  }
Qed.
Hint Resolve resolvent_sound.


(*=============================================================================
 * entails
 *===========================================================================*)

Definition entails f c := forall i, interpFormula i f = true
                                    -> interpClause i c = true.

Lemma interpFormula_In : forall f i c, interpFormula i f = true
                                  -> In c f -> interpClause i c = true.
  induction f; simpl; try tauto; intros.
  destruct H0; subst.
  apply Bool.andb_true_iff in H; tauto.
  apply Bool.andb_true_iff in H; destruct H; auto.
Qed.
Hint Resolve interpFormula_In.

Theorem In_entails : forall f c, In c f -> entails f c.
  unfold entails; intros; eauto 3.
Qed.
Hint Resolve In_entails.

Theorem resolvent_entails : forall f c1 c2 v cr, resolvent cr c1 c2 v
       -> entails f c1 -> entails f c2 -> entails f cr.
  unfold entails; intros; eauto 4.
Qed.
Hint Resolve resolvent_entails.


(*=============================================================================
 * pf - resolution-based inference system
 *===========================================================================*)

Inductive pf (f : formula) : clause -> Prop :=
| pf_asm c : In c f -> pf f c
| pf_res cr c1 c2 v : pf f c1 -> pf f c2 -> resolvent cr c1 c2 v -> pf f cr.

Theorem pf_sound : forall f c, pf f c -> entails f c.
  induction 1; eauto 3.
Qed.

Lemma pf_nil_interp_false : forall f, pf f nil
                             -> forall i, interpFormula i f = false.
  intros.
  destruct (interpFormula i f) eqn:?; auto.
  assert (interpClause i nil = true) by (eapply pf_sound; eauto 2).
  simpl in *; congruence.
Qed.

Theorem pf_nil_unsat : forall f, pf f nil -> ~ satisfiable f.
  intros; red; destruct 1.
  assert (interpFormula x f = false).
  solve [apply pf_nil_interp_false; auto].
  congruence.
Qed.


(*=============================================================================
 * more list facts
 *===========================================================================*)

Hint Resolve remove_In.

Lemma remove_In_inv : forall A eq (x y: A) l, x <> y -> In x (remove eq y l)
                                           -> In x l.
  induction l; simpl; try tauto.
  destruct (eq y a); subst; auto.
  destruct 2; subst; auto.
Qed.
Hint Resolve remove_In_inv.

Lemma In_neq_remove : forall A eq (a b : A) l, In a l -> a <> b
                                               -> In a (remove eq b l).
  induction l; simpl; try tauto.
  destruct 1; subst; intros.
  destruct (eq b a); try congruence; auto.
  destruct (eq b a0); try congruence; auto.
Qed.

Lemma sublist_trans : forall A (x y z : list A), sublist x y -> sublist y z
                                                 -> sublist x z.
  intros; apply Forall_forall; eauto 3.
Qed.
Hint Resolve sublist_trans.

Lemma sublist_drop : forall A (a : A) l, In a l -> sublist (a :: l) l.
  intros; apply Forall_forall; destruct 1; subst; auto.
Qed.
Hint Resolve sublist_drop.

Lemma sublist_remove : forall A eq (x : A) l l', remove eq x l = l'
                                                 -> sublist l' l.
  intros; apply Forall_forall; intros.
  destruct (eq x0 x); subst; eauto 3.
  solve [contradict H0; auto].
Qed.

Lemma sublist_remove_lit : forall x l l', remove_lit x l = l'
                                          -> sublist l' l.
  apply sublist_remove.
Qed.
Hint Resolve sublist_remove_lit.

Lemma sublist_add : forall A (a : A) x y, sublist x y -> sublist x (a :: y).
  intros.
  eapply sublist_trans; eauto 3.
  apply Forall_forall; simpl; auto.
Qed.

Lemma sublist_add' : forall A (a : A) x y, sublist x y
                                           -> sublist (a :: x) (a :: y).
  intros.
  apply Forall_forall.
  destruct 1; subst; simpl; eauto 3.
Qed.  

Hint Resolve sublist_add sublist_add'.

Lemma sublist_any : forall A (x : list A), sublist nil x.
  intros; apply Forall_forall; simpl; tauto.
Qed.
Hint Resolve sublist_any.


(*=============================================================================
 * pf facts
 *===========================================================================*)

Hint Constructors pf.

Lemma pf_nil : forall f c, pf f nil -> pf f c.
  intros.
  assert (resolvent c nil nil 0).
  {
    split; simpl; apply Forall_forall; simpl; tauto.
  }
  econstructor 2; try eassumption.
Qed.

Lemma In_sublist_pf : forall x y f, In x f -> sublist x y -> pf f y.
  intros.
  destruct y; [destruct H0; simpl in *; auto; tauto | ].
  assert (resolvent (l :: y) x x (litVar l)) by (split; eauto 3).
  econstructor 2; try eassumption; auto.
Qed.
Hint Resolve In_sublist_pf.

Lemma pf_sublist : forall x y f, pf f x -> sublist x y -> pf f y.
  inversion_clear 1; eauto 3; intros.
  assert (resolvent y c3 c4 v).
  solve [destruct H2; split; eauto 3].
  eauto 3.
Qed.
Hint Resolve pf_sublist.


(*=============================================================================
 * dpll n f = None -> pf f nil
 *===========================================================================*)

Fixpoint dropLitsClause (c : clause) ls :=
  match ls with
    | nil => c
    | l :: ls' => dropLitsClause (remove_lit l c) ls'
  end.

Fixpoint dropLits (f : formula) ls :=
  match f with
    | nil => nil
    | c :: f' => dropLitsClause c ls :: dropLits f' ls
  end.

Definition mkLit (b : bool) v := if b then pos v else neg v.
  
(* list of assumptions into a clause (as negations of assumptions) *)
Fixpoint negate_h s n :=
  match s with
    | nil => nil
    | b :: s'  => mkLit (negb b) n :: negate_h s' (S n)
  end.

Definition negate s := negate_h s 0.

Lemma In_dropLits_ex : forall f c ls, In c (dropLits f ls)
                    -> exists x, In x f /\ c = dropLitsClause x ls.
  induction f; simpl; try tauto; destruct 1; eauto 4.
  edestruct IHf as [? [] ]; eauto 4.
Qed.

Lemma In_dropLits : forall x ls f, In x f
                                   -> In (dropLitsClause x ls) (dropLits f ls).
  induction f; simpl; try tauto; destruct 1; subst; auto.
Qed.
Hint Resolve In_dropLits.

Lemma dropLitsClause_app_inv : forall y x c, dropLitsClause c (x ++ y)
                                  = dropLitsClause (dropLitsClause c x) y.
  induction x; simpl; auto.
Qed.

Lemma negate_h_add : forall b l n, negate_h (l ++ b :: nil) n
                         = negate_h l n ++ mkLit (negb b) (length l + n) :: nil.
  unfold negate; induction l; simpl; auto; intros.
  replace (S (length l + n)) with (length l + (S n)) by omega.
  f_equal; auto.
Qed.

Lemma negate_add : forall b l, negate (l ++ b :: nil)
                             = negate l ++ mkLit (negb b) (length l) :: nil.
  unfold negate; intros; rewrite negate_h_add; repeat f_equal; omega.
Qed.

Lemma dropLitsClause_negate_add : forall x l b,
                 dropLitsClause x (negate (l ++ b :: nil))
                 = remove_lit (mkLit (negb b) (length l))
                              (dropLitsClause x (negate l)).
  intros; rewrite negate_add, dropLitsClause_app_inv; simpl; auto.
Qed.

Lemma pf_dropLits_add : forall b f c l,
                          pf (dropLits f (negate (l ++ b :: nil))) c
                          -> pf (dropLits f (negate l))
                                (mkLit (negb b) (length l) :: c).
  induction 1.
  {
      edestruct In_dropLits_ex as [? [] ]; eauto 3.
      subst.
      assert (In (dropLitsClause x (negate l)) (dropLits f (negate l))).
      solve [apply In_dropLits; auto].
      eapply pf_sublist; eauto 3.
      rewrite dropLitsClause_negate_add.
      apply Forall_forall; intros; simpl.
      destruct (eq_lit_dec x0 (mkLit (negb b) (length l))); subst; auto.
      right.
      apply In_neq_remove; auto.
  }
  {
    assert (resolvent (mkLit (negb b) (length l) :: cr)
                      (mkLit (negb b) (length l) :: c3)
                      (mkLit (negb b) (length l) ::c4) v).
    {
      destruct H1.
      split; simpl.
      destruct (eq_lit_dec (pos v) (mkLit (negb b) (length l))); auto; congruence.
      destruct (eq_lit_dec (neg v) (mkLit (negb b) (length l))); auto.
    }
    eauto 3.
  }
Qed.
Hint Resolve pf_dropLits_add.

Lemma dropLitsClause_nil : forall l, dropLitsClause nil l = nil.
  induction l; simpl; auto.
Qed.
Hint Resolve dropLitsClause_nil.

Lemma In_dropLitsClause : forall l ls c, In l (dropLitsClause c ls)
                                         -> In l c /\ ~ In l ls.
  induction ls; simpl; auto; intros.
  edestruct IHls; eauto 3.
  destruct (eq_lit_dec l a); subst.
  contradict H0; apply remove_In.
  split; eauto 3.
  intro.
  destruct H2; congruence.
Qed.

Lemma In_negate_h : forall m v n, v < length m
                   -> In (mkLit (negb (nth v m true)) (v + n)) (negate_h m n).
  induction m; simpl; intros; try omega.
  destruct v; subst.
  {
    destruct a; auto.
  }
  {
    destruct a; simpl.
    replace (S (v + n)) with (v + S n) by omega.
    right; apply IHm; omega.    
    replace (S (v + n)) with (v + S n) by omega.
    right; apply IHm; omega.    
  }
Qed.

Lemma In_negate : forall m v b, v < length m -> nth v m true = b
                                -> In (mkLit (negb b) v) (negate m).
  unfold negate; intros.
  replace (mkLit (negb b) v) with (mkLit (negb b) (v + 0)) by (f_equal; omega).
  subst; apply In_negate_h; auto.
Qed.

Lemma okLit_false_In_negate : forall m l, okLit m l = false -> In l (negate m).
  unfold okLit; intros.
  destruct (getVal m (litVar l)) eqn:?; try congruence.
  edestruct getVal_Some_inv; eauto 2.
  destruct l; subst; simpl in *.
  change (In (mkLit (negb false) n) (negate m)); apply In_negate; auto.
  apply Bool.negb_false_iff in H.
  change (In (mkLit (negb true) n) (negate m)); apply In_negate; auto.
Qed.
Hint Resolve okLit_false_In_negate.

Lemma dropLitsClause_empty : forall c l, okClause l c = false
                   -> sublist (dropLitsClause c (negate l)) nil.
  intros.
  apply Forall_forall; intros.
  simpl.
  edestruct In_dropLitsClause; eauto 3.
  assert (okLit l x = false) by eauto 3.
  contradict H2; auto.
Qed.

Lemma dropLits_nil : forall f, dropLits f nil = f.
  induction f; simpl; auto; f_equal; auto.
Qed.

Lemma pf_dropLits : forall c f l, In c f -> okClause l c = false
                                  -> pf (dropLits f (negate l)) nil.
  intros.
  assert (sublist (dropLitsClause c (negate l)) nil).
  solve [apply dropLitsClause_empty; auto].
  eauto 3.
Qed.
Hint Resolve pf_dropLits.

Lemma resolve_out : forall r v c d, sublist (c ++ d) r
                                  -> resolvent r (pos v :: c) (neg v :: d) v.
  red; simpl; intros.
  destruct (eq_lit_dec (pos v) (pos v)); try congruence.
  destruct (eq_lit_dec (neg v) (neg v)); try congruence.
  split; eauto.
Qed.

Lemma resolve_drop1 : forall v c, resolvent c (pos v :: c) (neg v :: nil) v.
  intros; apply resolve_out; autorewrite with list; auto.
Qed.

Lemma resolve_drop2 : forall v c, resolvent c (pos v :: nil) (neg v :: c) v.
  intros; apply resolve_out; autorewrite with list; auto.
Qed.

Hint Resolve resolve_drop1 resolve_drop2.

Definition negLit l := match l with pos n => neg n | neg n => pos n end.

Lemma pf_resolve_lit : forall l f c, pf f (l :: c) -> pf f (negLit l :: nil)
                                  -> pf f c.
  intros.
  destruct l; simpl in *.
  assert (resolvent c (pos n :: c) (neg n :: nil) n) by auto; eauto 3.
  assert (resolvent c (pos n :: nil) (neg n :: c) n) by auto; eauto 3.
Qed.
Hint Resolve pf_resolve_lit.

Lemma dpll_h_None_pf_assume : forall f n l, dpll_h f l n = None
                                            -> pf (dropLits f (negate l)) nil.
  induction n; simpl; intros.
  { 
    destruct (okFormula l f) eqn:?; try congruence.
    edestruct okFormula_false_ex as [? [] ]; eauto 3.
  }
  {
    destruct (okFormula l f) eqn:?.
    destruct (dpll_h f (l ++ true :: nil) n) eqn:?; try congruence.
    {
      assert (pf (dropLits f (negate l))
                 (mkLit (negb true) (length l) :: nil)) by auto.
      assert (pf (dropLits f (negate l))
                 (mkLit (negb false) (length l) :: nil)) by auto.
      simpl in *; eauto 3.
    }
    {
      edestruct okFormula_false_ex as [? [] ]; eauto 3.
    }
  }
Qed.

Theorem dpll_None_pf : forall f n, dpll n f = None -> pf f nil.
  unfold dpll; intros.
  replace (pf f nil) with (pf (dropLits f (negate nil)) nil).
  eapply dpll_h_None_pf_assume; eauto 3.
  unfold negate; simpl.
  rewrite dropLits_nil; auto.
Qed.


(*=============================================================================
 * maxVarsFormula and well-formedness
 *===========================================================================*)

Fixpoint maxVarsClause c :=
  match c with
    | nil => 0
    | l :: c' => max (litVar l) (maxVarsClause c')
  end.

Fixpoint maxVarsFormula F :=
  match F with
    | nil => 0
    | c :: F' => max (maxVarsClause c) (maxVarsFormula F')
  end.

Lemma maxVarsClause_wf_clause : forall n x, maxVarsClause x < n -> wf_clause n x.
  induction x; simpl; red; simpl; try tauto; intros.
  apply NPeano.Nat.max_lub_lt_iff in H; destruct H.
  destruct H0; subst; try tauto.
  apply IHx; auto.
Qed.
Hint Resolve maxVarsClause_wf_clause.

Lemma maxVarsFormula_In : forall F c n, maxVarsFormula F < n -> In c F
                                        -> maxVarsClause c < n.
  induction F; simpl; try tauto; destruct 2; subst;
  apply NPeano.Nat.max_lub_lt_iff in H; destruct H; auto.
Qed.
Hint Resolve maxVarsFormula_In.

Lemma maxVarsFormula_lt_wf : forall n F, maxVarsFormula F < n -> wf_formula n F.
  red; intros; eauto 3.
Qed.

Theorem wf_maxVarsFormula : forall F, wf_formula (1 + maxVarsFormula F) F.
  intros; apply maxVarsFormula_lt_wf; omega.
Qed.
Hint Resolve wf_maxVarsFormula.


(*=============================================================================
 * refutable -> pf
 * the exisence of resolution proof
 *===========================================================================*)

Hint Constructors refutable.

Lemma refutable_cons : forall f l b, refutable f l -> refutable f (l ++ (b::nil)).
  inversion_clear 1.
  {
    constructor.
    edestruct okFormula_false_ex as [? [] ]; eauto 3.
    apply okFormula_app'; auto.
  }
  {
    destruct b; auto.
  }
Qed.
Hint Resolve refutable_cons.

Lemma refutable_app : forall f x l, refutable f l -> refutable f (l ++ x).
  induction x; intros; autorewrite with list; auto.
  replace (l ++ a :: x) with ((l ++ a :: nil) ++ x); auto.
  rewrite <- app_assoc; simpl; auto.
Qed.

Lemma refutable_nil_inv : forall f x, refutable f nil -> refutable f x.
  intros.
  change (refutable f (nil ++ x)).
  apply refutable_app; auto.
Qed.
Hint Resolve refutable_nil_inv.

Lemma refutable_contra : forall f l, refutable f l -> okFormula l f = true
                                     -> maxVarsFormula f < length l -> False.
  induction 1; intros; try congruence.
  apply IHrefutable1; autorewrite with list; try omega.
  apply okFormula_app; auto.
  apply maxVarsFormula_lt_wf; auto.
Qed.

Theorem refutable_dpll_None : forall f, refutable f nil
                                        -> exists n, dpll n f = None.
  intros.
  destruct (dpll (1 + maxVarsFormula f) f) eqn:?; eauto 3.
  {
    exfalso.
    assert (refutable f l) by auto.
    eapply refutable_contra; eauto 2.
    erewrite dpll_length by eauto 2; omega.
  }
Qed.
  
Theorem refutable_pf : forall f, refutable f nil -> pf f nil.
  intros; edestruct refutable_dpll_None; eauto 2.
  eapply dpll_None_pf; eauto 2.
Qed.

(*
Goal forall m f n, dpll_h f m n = None
                   -> forall x, x >= n -> dpll_h f m x = None.
  induction x; destruct n; auto; try omega; intros.
  {
    unfold dpll; simpl.
    destruct (okFormula m f) eqn:?; auto.
    destruct (dpll_h f (m ++ true :: nil) x) eqn:?; auto.
  }

Corollary dpll_some_not_refutable : forall n f, dpll n f <> None
                                      -> wf_formula n f -> ~ refutable f nil.
  red; intros.
  contradict H.
*)    


(*=============================================================================
 * pf -> refutable
 *===========================================================================*)

Lemma entails_nil_refutable : forall f, entails f nil -> refutable f nil.
  intros.
  eapply dpll_refutable with (1 + maxVarsFormula f); eauto.
  destruct (dpll (1 + maxVarsFormula f) f) eqn:?; auto.
  assert (interpFormula (m2i l) f = true).
  solve [eapply dpll_Some_interp; eauto 3].
  apply H in H0; simpl in *; congruence.
Qed.

Theorem pf_refutable : forall f, pf f nil -> refutable f nil.
  intros; apply entails_nil_refutable, pf_sound; auto.
Qed.


(*=============================================================================
 * refutation completeness of resolution
 *===========================================================================*)

Theorem unsat_pf_nil : forall f, ~ satisfiable f -> pf f nil.
  intros.
  apply refutable_pf.
  eapply dpll_refutable with (1 + maxVarsFormula f); eauto.
  destruct (dpll (1 + maxVarsFormula f) f) eqn:?; auto.
  contradict H; eapply dpll_sat_sound; eauto 3; congruence.
Qed.
  
Corollary unsat_pf_nil' : forall f, ~ (exists g, satFormula g f) -> pf f nil.
  intros.
  apply unsat_pf_nil.
  contradict H; apply satisfiable_satFormula; auto.
Qed.


(*=============================================================================
 * summary
 *===========================================================================*)

Corollary unsat_refutable : forall f, ~ satisfiable f -> refutable f nil.
  intros; apply pf_refutable, unsat_pf_nil; auto.
Qed.

Goal forall f, satisfiable f -> exists n m, dpll n f = Some m /\ wf_formula n f.
  intros; destruct (dpll (1 + maxVarsFormula f) f) eqn:?; eauto 4.
  contradict H; eapply dpll_unsat_sound'; eauto 3.
Qed.

Goal forall n f, wf_formula n f -> ~ satisfiable f -> dpll n f = None.
  intros.
  destruct (dpll n f) eqn:?; eauto 3.
  contradict H0; eapply dpll_sat_sound; eauto 3; congruence.
Qed.

Goal forall f, refutable f nil -> ~ satisfiable f.
  intros; apply pf_nil_unsat, refutable_pf; auto.
Qed.

(* theorems
  dpll = None => refutable
  refutable => ~ sat (Coq)
    dpll = None => ~ sat (Coq)
  ----
  sat => sat (Coq)
    dpll = None => ~ sat
  dpll = Some => sat
    dpll = Some => sat (Coq)
  ----
  pf => ~ sat
  dpll = None => pf
  refutable => pf
    pf => refutable
    ~ sat => refutable
  ----
  ~ sat => pf
  ~ sat (Coq) => pf
  sat => dpll = Some
  ~ sat => dpll = None (contraposition)
*)


(* summary
  ~ sat (Coq) <=> ~ sat <=> refutable <=> dpll = None (also, dpll = Some <=> sat)
  sat => sat (Coq)      <---- one directional
  ----
  denoteFormula <=> sat (Coq)
  refutable <=> pf
*)
