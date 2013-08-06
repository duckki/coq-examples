Set Implicit Arguments.
Require Import List Arith Omega.

(*=============================================================================
 * dpll
 *===========================================================================*)

Inductive lit := pos : nat -> lit | neg : nat -> lit.
Definition clause := list lit.
Definition formula := list clause.

Section dpll.
  Variable numVars : nat.
  Variable F : formula.

  Definition litVar l := match l with pos v => v | neg v => v end.

  Fixpoint getVal (l : list bool) v : option bool :=
    match l with
      | nil => None
      | b :: l' => match v with
                     | 0 => Some b
                     | S v' => getVal l' v'
                   end
    end.

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

  Fixpoint dpll_h assign n :=
    match okFormula assign F with
      | false => None
      | true =>
        match n with
          | 0 => Some assign
          | S n' =>
            match dpll_h (assign ++ true :: nil) n' with
              | Some assign' => Some assign'
              | None => dpll_h (assign ++ false :: nil) n'
            end
        end
    end.

  Definition dpll := dpll_h nil numVars.
    
End dpll.


(*=============================================================================
 * dpll test
 *===========================================================================*)

Example numVars := 4.

Example c1 := pos 3 :: nil.
Example c2 := neg 3 :: nil.

Example f1 := (@nil clause).
Example f2 := c1 :: nil.
Example f3 := c2 :: nil.
Example f4 := c1 :: c2 :: nil.

Eval compute in dpll numVars f3.


(*=============================================================================
 * semantics
 *===========================================================================*)

Definition interp := nat -> bool.

Definition interpLit (I : interp) (l : lit) :=
  match l with
    | pos n => I n
    | neg n => negb (I n)
  end.

Definition interpClause (I : interp) (c : clause) :=
  fold_right (fun l b => orb (interpLit I l) b) false c.

Definition interpFormula (I : interp) (f : formula) :=
  fold_right (fun c b => andb (interpClause I c) b) true f.

Definition satisfiable f := exists i, interpFormula i f = true.

Definition entails f c := forall i, interpFormula i f = true
                                    -> interpClause i c = true.


(*=============================================================================
 * semantics tests
 *===========================================================================*)

Example I n := match n with 0 => false | 1 => true | _ => true end.
Eval simpl in interpLit I (pos 0).

Goal forall (i : interp), interpClause i nil = false.
  simpl; auto.
Qed.

Goal forall (i : interp), interpFormula i nil = true.
  simpl; auto.
Qed.

Goal forall (i : interp) v, interpClause i ((pos v) :: (neg v) :: nil) = true.
  simpl; intros.
  destruct (i v) eqn:?; simpl; auto.
Qed.

Goal forall (i : interp), interpFormula i (c1 :: c2 :: nil) = false.
  simpl; intros.
  destruct (i 3) eqn:?; simpl; auto.
Qed.


(*=============================================================================
 * well-formedness of formula
 *===========================================================================*)

Definition wf_clause nv c := forall l, In l c -> litVar l < nv.
Definition wf_formula nv f := forall c, In c f -> wf_clause nv c.


(*=============================================================================
 * well-formedness tests
 *===========================================================================*)

Ltac wf :=
  unfold wf_formula; simpl; intros;
  repeat match goal with
           | _ => progress (subst; simpl)
           | |- wf_clause _ ?c => try unfold c; red; intros
           | H: _ \/ _ |- _ => destruct H
           | H: In _ _ |- _ => inversion_clear H
           | _ => tauto || omega || solve [auto]
         end.

Example f1_wf : wf_formula numVars f1.
  wf.
Qed.

Example f2_wf : wf_formula numVars f2.
  wf.
Qed.

Example f3_wf : wf_formula numVars f3.
  wf.
Qed.

Example f4_wf : wf_formula numVars f4.
  wf.
Qed.


(*=============================================================================
 * well-formedness facts
 *===========================================================================*)

Lemma wf_clause_cons_inv : forall nv c l, wf_clause nv (l :: c) -> litVar l < nv.
  intros.
  apply H; simpl; auto.
Qed.
Hint Resolve wf_clause_cons_inv.

Lemma wf_clause_cons_inv' : forall l n c, wf_clause n (l :: c) -> wf_clause n c.
  unfold wf_clause; intros; simpl in *; auto.
Qed.
Hint Resolve wf_clause_cons_inv'.

Lemma wf_formula_cons_inv : forall f nv c, wf_formula nv (c :: f)
                                           -> wf_clause nv c.
  intros.
  apply H; simpl; auto.
Qed.
Hint Resolve wf_formula_cons_inv.

Lemma wf_formula_cons_inv' : forall c f nv, wf_formula nv (c :: f)
                                          -> wf_formula nv f.
  unfold wf_formula; intros; simpl in *; auto.
Qed.
Hint Resolve wf_formula_cons_inv'.


(*=============================================================================
 * dpll correctness (SAT case)
 *===========================================================================*)

Lemma getVal_Some : forall m n, n < length m -> getVal m n = Some (nth n m true).
  induction m; simpl; intros; try omega.
  destruct n; auto.
  apply IHm; omega.
Qed.

Lemma getVal_None : forall n m, length m <= n -> getVal m n = None.
  induction n; destruct m; simpl; auto; try omega; intros.
  apply IHn; omega.
Qed.

Definition m2i m n := nth n m true.

Lemma getVal_m2i : forall m n, n < length m -> getVal m n = Some (m2i m n).
  unfold m2i; apply getVal_Some; auto.
Qed.

Lemma okLit_interpLit : forall m a, okLit m a = true -> litVar a < length m
                                    -> interpLit (m2i m) a = true.
  unfold okLit, interpLit; intros.
  rewrite getVal_m2i in * by auto.
  destruct a; simpl in *; auto.
Qed.
Hint Resolve okLit_interpLit.

Lemma okClause_interpClause : forall nv m c, okClause m c = true
                                  -> length m >= nv -> wf_clause nv c
                                  -> interpClause (m2i m) c = true.
  induction c; simpl; intros; try congruence.
  apply Bool.orb_true_iff.
  destruct (okLit m a) eqn:?; subst.
  {
    left; apply okLit_interpLit; auto.
    assert (litVar a < nv) by (apply H1; simpl; auto).
    omega.
  }
  {
    right.
    apply IHc; eauto 3.
  }
Qed.
Hint Resolve okClause_interpClause.

Lemma okFormula_interpFormula : forall nv m F, okFormula m F = true
                                    -> length m >= nv -> wf_formula nv F
                                    -> interpFormula (m2i m) F = true.
  induction F; simpl; auto; intros.
  destruct (okClause m a) eqn:?; try congruence.
  apply Bool.andb_true_iff; split; eauto 3.
Qed.

Ltac dpll :=
  try match goal with
        | H: None = Some _ |- _ => inversion H
        | H: Some _ = None |- _ => inversion H
        | H: Some _ = Some _ |- _ => inversion H; clear H; subst
      end; auto.

Lemma dpll_h_okFormula : forall F n m m', dpll_h F m n = Some m'
                                          -> okFormula m' F = true.
  induction n; simpl; intros;
  destruct (okFormula m F) eqn:?; dpll.
  destruct (dpll_h F (m ++ true :: nil) n) eqn:?; dpll; eauto 3.
Qed.

Lemma dpll_h_length : forall F n m m', dpll_h F m n = Some m'
                                          -> length m' = length m + n.
  induction n; simpl; intros;
  destruct (okFormula m F) eqn:?; dpll.
  destruct (dpll_h F (m ++ true :: nil) n) eqn:?; dpll; eauto 3.
  {
    replace (length m + S n) with (length (m ++ true :: nil) + n); eauto.
    autorewrite with list; simpl; omega.
  }
  {
    replace (length m + S n) with (length (m ++ false :: nil) + n); eauto.
    autorewrite with list; simpl; omega.
  }
Qed.

Theorem dpll_okFormula : forall F nv m , dpll nv F = Some m
                                         -> okFormula m F = true.
  unfold dpll; intros; eapply dpll_h_okFormula; eauto 3.
Qed.
Hint Resolve dpll_okFormula.

Theorem dpll_length : forall F nv m , dpll nv F = Some m
                                      -> length m = nv.
  unfold dpll; intros.
  change (length m = length nil(A:=bool) + nv).
  eapply dpll_h_length; eauto 3.
Qed.
Hint Resolve dpll_length.

Theorem dpll_Some_sound : forall F m nv, dpll nv F = Some m -> wf_formula nv F
                                         -> satisfiable F.
  red; intros.
  assert (length m = nv) by eauto 3.
  exists (m2i m); eapply okFormula_interpFormula; try eassumption; eauto 3; omega.
Qed.


(*=============================================================================
 * if satsifiable, there exists a finite model.
 *===========================================================================*)

Definition clamp f nv n := if lt_dec n nv then f n else true.

Lemma clamp_eq_lt : forall n x i, x < n -> clamp i n x = i x.
  unfold clamp; intros.
  destruct (lt_dec x n); auto; tauto.
Qed.

Lemma interpLit_clamp : forall nv i x, litVar x < nv -> interpLit i x = true
                                       -> interpLit (clamp i nv) x = true.
  unfold interpLit; intros.
  destruct x; rewrite clamp_eq_lt by auto; auto.
Qed.
Hint Resolve interpLit_clamp.

Lemma interpClause_clamp : forall nv i c, wf_clause nv c
                              -> interpClause i c = true
                              -> interpClause (clamp i nv) c = true.
  induction c; simpl; auto; intros.
  apply Bool.orb_true_iff.
  apply Bool.orb_true_iff in H0; destruct H0; eauto 4.
Qed.
Hint Resolve interpClause_clamp.
  
Lemma interpFormula_clamp : forall nv i F, wf_formula nv F
                                -> interpFormula i F = true
                                -> interpFormula (clamp i nv) F = true.
  induction F; simpl; auto; intros.
  apply Bool.andb_true_iff in H0; destruct H0.
  apply Bool.andb_true_iff; split; eauto 3.
Qed.
Hint Resolve interpFormula_clamp.

Lemma clamp_m2i : forall i n,
                       exists m, length m = n /\ forall v, clamp i n v = m2i m v.
  induction n; intros.
  {
    exists nil; simpl; auto.
    split; auto; intros.
    destruct v; auto.
  }
  {
    destruct IHn as [? [] ].
    exists (x ++ (i n) :: nil); intros.
    autorewrite with list; simpl; split; try omega; intros.
    specialize (H0 v).
    unfold clamp, m2i in *; destruct (lt_dec v (S n)).
    {
      destruct (lt_dec v n).
      {
        rewrite H0; subst.
        rewrite app_nth1; auto.
      }
      {
        assert (v = n) by omega; subst.
        rewrite app_nth2; auto.
        replace (length x - length x) with 0 by omega.
        simpl; auto.
      }
    }
    {
      destruct (lt_dec v n); try omega; subst.
      rewrite app_nth2 by omega.
      destruct (v - length x) eqn:?; try omega.
      simpl.
      destruct n; auto.
    }
  }
Qed.

Lemma interpLit_compat : forall x y l, (forall v, x v = y v)
                             -> interpLit x l = true -> interpLit y l = true.
  unfold interpLit; intros; auto.
  destruct l; rewrite <- H; auto.
Qed.
Hint Resolve interpLit_compat.

Lemma interpClause_compat : forall x y c, (forall v, x v = y v)
                              -> interpClause x c = true
                              -> interpClause y c = true.
  induction c; simpl; auto; intros.
  apply Bool.orb_true_iff in H0.
  destruct H0; apply Bool.orb_true_iff; eauto 3.
Qed.
Hint Resolve interpClause_compat.

Lemma interpFormula_compat : forall x y F, (forall v, x v = y v)
                                 -> interpFormula x F = true
                                 -> interpFormula y F = true.
  induction F; simpl; auto; intros.
  apply Bool.andb_true_iff in H0; destruct H0.
  apply Bool.andb_true_iff; split; eauto 3.
Qed.  
Hint Resolve interpFormula_compat.

Lemma satisfiable_model : forall nv F, wf_formula nv F -> satisfiable F
                  -> exists m, interpFormula (m2i m) F = true /\ length m = nv.
  destruct 2.
  assert (interpFormula (clamp x nv) F = true) by auto.
  destruct (clamp_m2i x nv) as [? [] ]; eauto 4.
Qed.


(*=============================================================================
 * dpll correctness (UNSAT case)
 *===========================================================================*)

Lemma okLit_interpLit' : forall m x, okLit m x = false
                                     -> interpLit (m2i m) x = false.
  unfold okLit; intros.
  destruct (le_lt_dec (length m) (litVar x)).
  rewrite getVal_None in * by auto; congruence.
  rewrite getVal_m2i in * by auto; auto.
  destruct x; simpl in *; auto.
Qed.
Hint Resolve okLit_interpLit'.

Lemma okClause_interpClause' : forall m x, okClause m x = false
                                           -> interpClause (m2i m) x = false.
  induction x; simpl; auto; intros.
  apply Bool.orb_false_iff.
  destruct (okLit m a) eqn:?; try congruence; auto.
Qed.
Hint Resolve okClause_interpClause'.

Lemma okFormula_interpFormula' : forall m F, okFormula m F = false
                                             -> interpFormula (m2i m) F = false.
  induction F; simpl; auto; intros.
  apply Bool.andb_false_iff.
  destruct (okClause m a) eqn:?; auto.
Qed.
Hint Resolve okFormula_interpFormula'.


Lemma okLit_app : forall b m x, okLit m x = false
                                -> okLit (m ++ b :: nil) x = false.
  unfold okLit; simpl; intros.
  destruct (le_lt_dec (length m) (litVar x)).
  rewrite getVal_None in * by auto; congruence.
  rewrite getVal_Some in * by (autorewrite with list; omega).
  destruct x; simpl in *; rewrite app_nth1 by auto; auto.
Qed.
Hint Resolve okLit_app.

Lemma okClause_app : forall b m x, okClause m x = false
                                   -> okClause (m ++ b :: nil) x = false.
  induction x; simpl; auto; intros.
  destruct (okLit m a) eqn:?; try congruence; auto.
  destruct (okLit (m ++ b :: nil) a) eqn:?; auto.
  assert (okLit (m ++ b :: nil) a = false) by auto; congruence.
Qed.
Hint Resolve okClause_app.

Lemma okFormula_app : forall b m F, okFormula m F = false
                                    -> okFormula (m ++ b :: nil) F = false.
  induction F; simpl; auto; intros.
  destruct (okClause m a) eqn:?, (okClause (m ++ b :: nil) a) eqn:?; auto.
  assert (okClause (m ++ b :: nil) a = false) by auto; congruence.
Qed.
Hint Resolve okFormula_app.

Lemma okFormua_app' : forall F x m, okFormula m F = false
                                    -> okFormula (m ++ x) F = false.
  induction x; simpl; intros; autorewrite with list; auto.
  replace (m ++ a :: x) with ((m ++ a :: nil) ++ x)
    by (rewrite <- app_assoc; simpl; auto); auto.
Qed.
Hint Resolve okFormua_app'.

Lemma dpll_h_None : forall n m x F, dpll_h F m n = None -> length x = n
                     -> okFormula (m ++ x) F = false.
  induction n; simpl; intros.
  {
    destruct (okFormula m F) eqn:?; dpll.
  }
  {
    destruct (okFormula m F) eqn:?; dpll.
    destruct (dpll_h F (m ++ true :: nil) n) eqn:?; dpll.
    destruct x; simpl in *; try omega.
    replace (m ++ b :: x) with ((m ++ b :: nil) ++ x)
      by (rewrite <- app_assoc; simpl; auto).
    destruct b; auto.
  }
Qed.

Lemma dpll_None : forall nv m F, dpll nv F = None -> length m = nv
                               -> okFormula m F = false.
  intros.
  replace m with (nil ++ m) by auto.
  eapply dpll_h_None; eauto.
Qed.
  
Lemma dpll_None' : forall nv F m, dpll nv F = None -> length m = nv
                    -> interpFormula (m2i m) F = false.
  intros.
  apply okFormula_interpFormula'.
  eapply dpll_None; eauto 3.
Qed.

Theorem dpll_None_sound : forall nv F, dpll nv F = None -> wf_formula nv F
                                       -> ~ satisfiable F.
  red; intros.
  edestruct satisfiable_model as [? [] ]; eauto 3.
  assert (interpFormula (m2i x) F = false).
  solve [eapply dpll_None'; eauto 3; omega].
  congruence.
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
 * conjecture : stronger theorem
 *===========================================================================*)

Conjecture conj : forall F n, dpll n F = None
                              -> dpll (1 + maxVarsFormula F) F = None.

Lemma satisfiable_model' : forall F, satisfiable F
                             -> exists m, interpFormula (m2i m) F = true
                                          /\ length m = 1 + maxVarsFormula F.
  destruct 1.
  assert (wf_formula (1 + maxVarsFormula F) F) by auto.
  assert (interpFormula (clamp x (1 + maxVarsFormula F)) F = true) by auto.
  destruct (clamp_m2i x (1 + maxVarsFormula F)) as [? [] ]; eauto 4.
Qed.

Theorem dpll_None_sound' : forall n F, dpll n F = None
                                       -> ~ satisfiable F.
  red; intros.
  assert (dpll (1 + maxVarsFormula F) F = None).
  solve [eapply conj; eauto 3].
  edestruct satisfiable_model' as [? [] ]; eauto 3.
  assert (wf_formula (1 + maxVarsFormula F) F) by auto.
  assert (interpFormula (m2i x) F = false).
  solve [eapply dpll_None'; eauto 3].
  congruence.
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
 * interp facts
 *===========================================================================*)

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

Lemma interpClause_In' : forall x i l, interpClause i x = false
                           -> In l x -> interpLit i l = false.
  induction x; simpl; try tauto; intros.
  eapply Bool.orb_false_iff in H; destruct H.
  destruct H0; subst; auto.
Qed.

Hint Resolve interpClause_In interpClause_In'.

Lemma interpClause_sublist : forall i x y, interpClause i x = true
                               -> sublist x y -> interpClause i y = true.
  intros.
  edestruct interpClause_exists as [? [] ]; try eassumption.
  eapply interpClause_In; try eassumption.
  eapply Forall_forall in H0; eassumption.
Qed.

Lemma interpClause_sublist' : forall i x y, interpClause i y = false
                                -> sublist x y -> interpClause i x = false.
  induction x; simpl; intros; auto.
  apply Bool.orb_false_iff.
  inversion_clear H0; eauto 4.
Qed.

Hint Resolve interpClause_sublist interpClause_sublist'.

Lemma interpClause_app : forall i x y,
                           interpClause i x = true \/ interpClause i y = true
                           -> interpClause i (x ++ y) = true.
  intros; unfold interpClause; rewrite fold_right_app.
  destruct H.
  {
    destruct (fold_right (fun (l : lit) (b : bool) => (interpLit i l || b)%bool)
                false y); simpl; auto.
    induction x; simpl in *; auto.
    destruct (interpLit i a); auto.
  }
  {
    unfold interpClause in H; rewrite H.
    induction x; simpl; auto.
    destruct (interpLit i a); auto.
  }
Qed.
  
Lemma interpFormula_In : forall f i c, interpFormula i f = true
                                  -> In c f -> interpClause i c = true.
  induction f; simpl; try tauto; intros.
  destruct H0; subst.
  apply Bool.andb_true_iff in H; tauto.
  apply Bool.andb_true_iff in H; destruct H; auto.
Qed.
Hint Resolve interpFormula_In.

Corollary In_entails : forall f c, In c f -> entails f c.
  unfold entails; intros; eauto 3.
Qed.
Hint Resolve In_entails.


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

Corollary resolvent_entails : forall f c1 c2 v cr, resolvent cr c1 c2 v
       -> entails f c1 -> entails f c2 -> entails f cr.
  unfold entails; intros; eauto 4.
Qed.
Hint Resolve resolvent_entails.


(*=============================================================================
 * Example : (direct) resolution
 *===========================================================================*)

Definition resolve x y v := remove_lit (pos v) x ++ remove_lit (neg v) y.

(* resolve is always is a resolvent *)
Lemma resolve_resolvent : forall x y v, resolvent (resolve x y v) x y v.
  unfold resolve, resolvent; split; auto.
Qed.

Theorem resolve_sound : forall i c1 c2 v,
       interpClause i c1 = true -> interpClause i c2 = true
       -> interpClause i (resolve c1 c2 v) = true.
  intros; eapply resolvent_sound; try apply resolve_resolvent; auto.
Qed.


(*=============================================================================
 * pf
 *===========================================================================*)

Inductive pf (f : formula) : clause -> Prop :=
| pf_asm c : In c f -> pf f c
| pf_res cr c1 c2 v : pf f c1 -> pf f c2 -> resolvent cr c1 c2 v -> pf f cr.

Theorem pf_sound : forall f c, pf f c -> entails f c.
  induction 1; eauto 3.
Qed.
Hint Resolve pf_sound.

Lemma pf_nil_interp_false : forall f, pf f nil
                             -> forall i, interpFormula i f = false.
  intros.
  destruct (interpFormula i f) eqn:?; auto.
  assert (interpClause i nil = true) by (eapply pf_sound; eauto 2).
  simpl in *; congruence.
Qed.

Lemma pf_nil_unsat : forall f, pf f nil -> ~ satisfiable f.
  intros; red; destruct 1.
  assert (interpFormula x f = false).
  solve [apply pf_nil_interp_false; auto].
  congruence.
Qed.


(*=============================================================================
 * todo: pf is refutation complete
 *===========================================================================*)

Conjecture pf_complete : forall f, entails f nil -> pf f nil.

Lemma unsat_pf_nil : forall f, ~ satisfiable f -> pf f nil.
  intros; apply pf_complete.
  red; intros.
  contradict H.
  red; eauto.
Qed.
  
Theorem dpll_pf : forall n F, wf_formula n F -> dpll n F = None -> pf F nil.
  intros; apply unsat_pf_nil.
  eapply dpll_None_sound; eauto 2.
Qed.
  

(*=============================================================================
 * denotation into Coq
 *===========================================================================*)

Definition context := list Prop.

Definition denoteLit (g : context) (l : lit) : Prop :=
  match l with
    | pos n => nth n g False
    | neg n => ~ nth n g False
  end.

Fixpoint denoteClause (g : context) (c : clause) : Prop :=
  match c with
    | nil => False
    | l :: c' => denoteLit g l \/ denoteClause g c'
  end.

Fixpoint denoteFormula (g : context) f : Prop :=
  match f with
    | nil => True
    | c :: f' => denoteClause g c /\ denoteFormula g f'
  end.

Lemma denoteFormula_In : forall f g c, denoteFormula g f -> In c f
                                       -> denoteClause g c.
  induction f; simpl; try tauto; intros.
  destruct H, H0; subst; try tauto; auto.
Qed.
Hint Resolve denoteFormula_In.

Lemma denoteClause_exists : forall g x, denoteClause g x
                             -> exists l, In l x /\ denoteLit g l.
  induction x; simpl; try tauto; intros.
  destruct H; eauto 4.
  destruct IHx as [? [] ]; eauto.
Qed.

Lemma denoteClause_In : forall l g x, denoteLit g l -> In l x
                                      -> denoteClause g x.
  induction x; simpl; try tauto; destruct 2; subst; auto.
Qed.
Hint Resolve denoteClause_In.

Lemma denoteClause_sublist : forall x g y, denoteClause g x
                               -> sublist x y -> denoteClause g y.
  intros.
  edestruct denoteClause_exists as [? [] ]; eauto 3.
Qed.
Hint Resolve denoteClause_sublist.

Lemma denoteClause_remove_lit : forall g l c, denoteClause g c
               -> denoteClause g (remove_lit l c) \/ denoteLit g l.
  induction c; simpl; try tauto; destruct 1; subst; auto.
  {
    destruct (eq_lit_dec l a); subst; simpl; auto.
  }
  {
    destruct (eq_lit_dec l a); subst; simpl; auto.
    destruct IHc; auto.
  }
Qed.

Lemma denoteLit_contra : forall g v, denoteLit g (pos v) -> denoteLit g (neg v)
                                     -> False.
  simpl; tauto.
Qed.
Hint Resolve denoteLit_contra.

Lemma denoteClause_resolvent : forall c1 c2 v g cr, resolvent cr c1 c2 v
                                 -> denoteClause g c1 -> denoteClause g c2
                                 -> denoteClause g cr.
  unfold resolvent; destruct 1; intros.
  edestruct denoteClause_remove_lit; try apply H1; eauto 3.
  edestruct denoteClause_remove_lit; try apply H2; eauto 3.
  exfalso; eauto 3.
Qed.
Hint Resolve denoteClause_resolvent.

Lemma pf_denote_sound : forall f g c, pf f c -> denoteFormula g f
                                      -> denoteClause g c.
  induction 1; intros; eauto 4.
Qed.


(*=============================================================================
 * trimmed denotation
 *===========================================================================*)

Fixpoint denoteClause' (g : context) (c : clause) : Prop :=
  match c with
    | nil => False
    | l :: nil => denoteLit g l
    | l :: c' => denoteLit g l \/ denoteClause' g c'
  end.

Fixpoint denoteFormula' (g : context) f : Prop :=
  match f with
    | nil => True
    | c :: nil => denoteClause' g c
    | c :: f' => denoteClause' g c /\ denoteFormula' g f'
  end.

Lemma denoteClause_trim : forall g c, denoteClause' g c -> denoteClause g c.
  induction c; simpl; try tauto; intros.
  destruct c; auto; simpl in *; tauto.
Qed.
Hint Resolve denoteClause_trim.

Lemma denoteFormula_trim : forall g x, denoteFormula' g x -> denoteFormula g x.
  induction x; simpl; try tauto; intros.
  destruct x; simpl; auto.
  destruct H.
  split; auto.
  apply IHx; auto.
Qed.
Hint Resolve denoteFormula_trim.

Lemma denoteClause_trim' : forall g c, denoteClause g c -> denoteClause' g c.
  induction c; simpl; try tauto; intros.
  destruct H, c; auto; simpl in *; tauto.
Qed.

Lemma pf_denote_sound' : forall f g c, pf f c -> denoteFormula' g f
                                       -> denoteClause' g c.
  intros.
  apply denoteClause_trim'.
  eapply pf_denote_sound; eauto 3.
Qed.


(*=============================================================================
 * reification
 *===========================================================================*)

Ltac inList x xs :=
  match xs with
    | nil => false
    | x :: _ => true
    | _ :: ?xs' => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  match b with
    | true => xs
    | false => constr:(x :: xs)
  end.

Ltac lookup x xs :=
  match xs with
    | x :: _ => constr:O
    | _ :: ?xs' => let n := lookup x xs' in constr:(S n)
  end.


Ltac allVars xs e :=
  match e with
    | ~ ?e' => allVars xs e'
    | ?e1 /\ ?e2 => let xs := allVars xs e1 in allVars xs e2
    | ?e1 \/ ?e2 => let xs := allVars xs e1 in allVars xs e2
    | _ => addToList e xs
  end.

Ltac reifyLit g e :=
  match e with
    | not ?e' => let v := lookup e' g in constr:(neg v)
    | _ => let v := lookup e g in constr:(pos v)
  end.

Ltac reifyClause g e :=
  match e with
    | ?x \/ ?y =>
      let l := reifyLit g x in
      let c := reifyClause g y in
      constr:(l :: c)
    | _ =>
      let l := reifyLit g e in
      constr:(l :: nil)
  end.

Ltac reifyFormula g e :=
  match e with
    | ?x /\ ?y =>
      let c := reifyClause g x in
      let f := reifyFormula g y in
      constr:(c :: f)
    | _ =>
      let c := reifyClause g e in
      constr:(c :: nil)
  end.

Ltac reify :=
  match goal with
    | |- ?F =>
      let g := allVars tt F in
      let f := reifyFormula g F in
      pose f
  end.


(*=============================================================================
 * reification tests
 *===========================================================================*)

Section reification_test.
  Variables A B C D : Prop.

  Goal (A /\ ~ B) -> A.
    match goal with
      | |- ?F -> ?C =>
        let _g := allVars (@nil Prop) F in
        let _f := reifyFormula _g F in
        let _c := reifyClause _g C in
        pose (g:=_g); pose (f:=_f); pose (c:=_c)
    end.
    intro.
    change (denoteFormula' g f) in H.
    change (denoteClause' g c).
    eapply pf_denote_sound'; eauto 3.
    {
      constructor; wf.
    }
  Qed.
End reification_test.


(*=============================================================================
 * reflection tests
 *===========================================================================*)

Section PigeonHole.
  Variables p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop.

  Definition hole2 :=
    (~p1 \/ ~p3) /\
    (~p1 \/ ~p5) /\
    (~p3 \/ ~p5) /\
    (~p2 \/ ~p4) /\
    (~p2 \/ ~p6) /\
    (~p4 \/ ~p6) /\
    (p1 \/ p2) /\
    (p3 \/ p4) /\
    (p5 \/ p6).

  Definition hole3 :=
    (~p1 \/ ~p4) /\
    (~p1 \/ ~p7) /\
    (~p1 \/ ~p10) /\
    (~p4 \/ ~p7) /\
    (~p4 \/ ~p10) /\
    (~p7 \/ ~p10) /\

    (~p2 \/ ~p5) /\
    (~p2 \/ ~p8) /\
    (~p2 \/ ~p11) /\
    (~p5 \/ ~p8) /\
    (~p5 \/ ~p11) /\
    (~p8 \/ ~p11) /\

    (~p3 \/ ~p6) /\
    (~p3 \/ ~p9) /\
    (~p3 \/ ~p12) /\
    (~p6 \/ ~p9) /\
    (~p6 \/ ~p12) /\
    (~p9 \/ ~p12) /\

    (p1 \/ p2 \/ p3) /\
    (p4 \/ p5 \/ p6) /\
    (p7 \/ p8 \/ p9) /\
    (p10 \/ p11 \/ p12).

  (*Goal hole2 -> False.
    unfold hole2; tauto.
  Qed.*)

  Goal hole3 -> False. (* tauto will be very slow *)
    unfold hole3.
    match goal with
      | |- ?F -> False =>
        let _g := allVars (@nil Prop) F in
        let _f := reifyFormula _g F in
        pose (g:=_g); pose (f:=_f)
    end.
    intro H.
    change (denoteFormula' g f) in H.
    change (denoteClause' g nil).
    eapply pf_denote_sound'; eauto 3.
    assert (wf_formula 12 f) by wf.
    eapply dpll_pf; try eassumption.
    compute; auto.
  Qed.

End PigeonHole.
