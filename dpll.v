(*=============================================================================
 * A simple DPLL implementation and its correctness proof, along with
 * a reflective tactic.
 * - Author: Duckki Oe
 * - Updated: 8/9/2013
 *===========================================================================*)
(*=============================================================================
  ++ list of theorems (corollaries are indented)
  dpll = None => refutable
  refutable => ~ sat (Coq)
    dpll = None => ~ sat (Coq)
  ----------------------------
  sat => sat (Coq) (equivalently, ~ sat (Coq) => ~ sat)
    dpll = None => ~ sat
  dpll = Some => sat (equivalently, ~ sat => dpll = None)
    dpll = Some => sat (Coq)
  ----------------------------
  denoteFormula -> sat (Coq)   (note: the other direction is also true)
  ----------------------------
  refutable => dpll = None
  ----------------------------
    refutable => ~ sat
    ~ sat => refutable
    ~ sat => ~ sat (Coq)
    sat => dpll = Some

  ++ summary of relations
  dpll = None <=> refutable <=> ~ sat <=> ~ sat (Coq)
    (equivalently, dpll = Some <=> sat)
  sat => sat (Coq)  <---- Note: one directional
  denoteFormula <=> sat (Coq)
 *===========================================================================*)
Set Implicit Arguments.
Require Import List Arith Omega.

(*=============================================================================
 * dpll implementation
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
 * logic utility
 *===========================================================================*)

Lemma dnc : forall p : Prop, ~~ (p \/ ~p).
  tauto.
Qed.


(*=============================================================================
 * dpll facts
 *===========================================================================*)

Lemma getVal_Some : forall m n, n < length m -> getVal m n = Some (nth n m true).
  induction m; simpl; intros; try omega; destruct n; intuition.
Qed.

Lemma getVal_None : forall n m, length m <= n -> getVal m n = None.
  induction n; destruct m; simpl; auto; try omega; intuition.
Qed.

Lemma okLit_false_lt : forall s l, okLit s l = false -> litVar l < length s.
  unfold okLit; intros; destruct (getVal s (litVar l)) eqn:?; try congruence.
  destruct (le_lt_dec (length s) (litVar l)); auto.
  rewrite getVal_None in * by auto; congruence.
Qed.
Hint Resolve okLit_false_lt.

Lemma okClause_In : forall s c l, okClause s c = false -> In l c
                                  -> okLit s l = false.
  induction c; simpl; try tauto; intros.
  destruct (okLit s a) eqn:?; try congruence.
  destruct H0; subst; auto.
Qed.
Hint Resolve okClause_In.


(*=============================================================================
 * refutational proofs
 *===========================================================================*)

Inductive refutable (F : formula) (l : list bool) : Prop :=
| refutable_base  : okFormula l F = false -> refutable F l
| refutable_split : refutable F (l ++ true :: nil)
                    -> refutable F (l ++ false :: nil) -> refutable F l.

Hint Constructors refutable.

Lemma dpll_h_refutable : forall n f l, dpll_h f l n = None -> refutable f l.
  induction n; simpl; intros.
  {
    destruct (okFormula l f) eqn:?; try congruence; auto.
  }
  {
    destruct (okFormula l f) eqn:?; auto.
    destruct (dpll_h f (l ++ true :: nil) n) eqn:?; try congruence; auto.
  }
Qed.

Lemma dpll_refutable : forall n f, dpll n f = None -> refutable f nil.
  intros; eapply dpll_h_refutable; eauto 2.
Qed.


(*=============================================================================
 * denotational satisfiability
 *===========================================================================*)

Definition context := nat -> Prop.

Section denoteSat.
  Variable g : context.

  Definition satLit l :=
    match l with
      | pos n => g n
      | neg n => ~ g n
    end.

  Definition satClause c := exists l, In l c /\ satLit l.

  Definition satFormula f := forall c, In c f -> satClause c.
End denoteSat.


(*=============================================================================
 * m2i - turn a finite model into a interpretation function
 *===========================================================================*)

Definition nth2fun {A} (l : list A) d := fun n => nth n l d.
Definition m2i m := nth2fun m true.

Lemma m2i_app_lt : forall x y v, v < length x -> m2i (x ++ y) v = m2i x v.
  unfold m2i, nth2fun; intros; rewrite app_nth1; auto.
Qed.

Lemma m2i_app_ge : forall x y v, v >= length x
                                 -> m2i (x ++ y) v = m2i y (v - length x).
  unfold m2i, nth2fun; intros; rewrite app_nth2; auto.
Qed.

Lemma getVal_m2i : forall m n, n < length m -> getVal m n = Some (m2i m n).
  unfold m2i, nth2fun; apply getVal_Some; auto.
Qed.


(*=============================================================================
 * refutable ==> unsat (denotational)
 *===========================================================================*)

Definition assumed (g : context) m
  := forall v, v < length m -> if m2i m v then g v else ~ g v.

Hint Resolve in_eq in_cons.

Lemma okClause_false : forall g s x, okClause s x = false -> assumed g s
                                     -> ~ satClause g x.
  intros; red; destruct 1 as [? [] ].
  assert (okLit s x0 = false) by eauto 3.
  assert (litVar x0 < length s) by auto.
  specialize (H0 _ H4).
  unfold okLit in *; rewrite getVal_m2i in * by auto.
  destruct x0; simpl in *.
  solve [rewrite H3 in *; tauto].
  solve [apply Bool.negb_false_iff in H3; rewrite H3 in *; tauto].
Qed.
Hint Resolve okClause_false.

Lemma okFormula_false : forall s g f, okFormula s f = false -> assumed g s
                                      -> ~ satFormula g f.
  induction f; simpl; try congruence; intros.
  destruct (okClause s a) eqn:?.
  {
    intro; eelim IHf; eauto 3.
    red; auto.
  }
  intro.
  assert (satClause g a) by auto.
  contradict H2; eauto 3.
Qed.
Hint Resolve okFormula_false.

Lemma assume_add_true : forall g l, assumed g l -> g (length l)
                                    -> assumed g (l ++ true :: nil).
  red; intros.
  destruct (le_lt_dec (length l) v).
  {
    rewrite m2i_app_ge; auto.
    assert (length l = v).
    solve [autorewrite with list in *; simpl in *; omega].
    rewrite H2; simpl.
    replace (v - v) with 0 by omega; simpl; congruence.
  }
  {
    rewrite m2i_app_lt by auto; apply H; auto.
  }
Qed.
Hint Resolve assume_add_true.

Lemma assume_add_false : forall g l, assumed g l -> ~ g (length l)
                                     -> assumed g (l ++ false :: nil).
  red; intros.
  destruct (le_lt_dec (length l) v).
  {
    rewrite m2i_app_ge; auto.
    assert (length l = v).
    solve [autorewrite with list in *; simpl in *; omega].
    rewrite H2; simpl.
    replace (v - v) with 0 by omega; simpl; congruence.
  }
  {
    rewrite m2i_app_lt by auto; apply H; auto.
  }
Qed.
Hint Resolve assume_add_false.

Lemma refutable_unsat_h : forall g f s, refutable f s -> assumed g s
                                      -> ~ satFormula g f.
  induction 1; intros; eauto 3.
  intro; elim (@dnc (g (length l))); red; destruct 1; contradict H2; auto.
Qed.

Theorem refutable_unsat : forall g f, refutable f nil -> ~ satFormula g f.
  intros; eapply refutable_unsat_h; eauto 3.
  red; simpl; intros; omega.
Qed.

Corollary dpll_unsat_sound : forall n g f, dpll n f = None -> ~ satFormula g f.
  intros; eapply refutable_unsat, dpll_refutable; eauto 2.
Qed.


(*=============================================================================
 * classical semantics
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


(*=============================================================================
 * semantics tests
 *===========================================================================*)

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

Example I n := match n with 0 => false | 1 => true | _ => true end.
Eval simpl in interpLit I (pos 0).


(*=============================================================================
 * denotational satisfiability and classical satisfiability
 *===========================================================================*)

(* a trivial Coq context from classical Boolean model *)
Definition i2g (i : interp) v := if i v then True else False.

Lemma denoteLit_i2g : forall i l, interpLit i l = true -> satLit (i2g i) l.
  destruct l; simpl; unfold i2g; intros;
  destruct (i n); simpl in *; auto; congruence.
Qed.    
Hint Resolve denoteLit_i2g.

Lemma satClause_i2g : forall i x, interpClause i x = true
                                     -> satClause (i2g i) x.
  induction x; simpl; try congruence; intros.
  apply Bool.orb_true_iff in H; destruct H.
  exists a; simpl; auto.
  destruct IHx as [? [] ]; auto.
  exists x0; simpl; auto.
Qed.
Hint Resolve satClause_i2g.

Lemma satFormula_i2g : forall i x, interpFormula i x = true
                                     -> satFormula (i2g i) x.
  induction x; red; simpl; try tauto; intros.
  apply Bool.andb_true_iff in H; destruct H.
  destruct H0; subst; auto.
  apply IHx; auto.
Qed.
Hint Resolve satFormula_i2g.

Theorem satisfiable_satFormula : forall f, satisfiable f
                                           -> exists g, satFormula g f.
  destruct 1; exists (i2g x); auto.
Qed.

Corollary dpll_unsat_sound' : forall n f, dpll n f = None -> ~ satisfiable f.
  red; intros; edestruct satisfiable_satFormula; eauto 2.
  contradict H1; eapply dpll_unsat_sound; eauto 2.
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
 * dpll soundness (SAT case)
 *===========================================================================*)

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

Ltac options :=
  try match goal with
        | H: None = Some _ |- _ => inversion H
        | H: Some _ = None |- _ => inversion H
        | H: Some _ = Some _ |- _ => inversion H; clear H; subst
      end; auto.

Lemma dpll_h_okFormula : forall F n m m', dpll_h F m n = Some m'
                                          -> okFormula m' F = true.
  induction n; simpl; intros;
  destruct (okFormula m F) eqn:?; options.
  destruct (dpll_h F (m ++ true :: nil) n) eqn:?; options; eauto 3.
Qed.

Lemma dpll_okFormula : forall F nv m , dpll nv F = Some m
                                         -> okFormula m F = true.
  unfold dpll; intros; eapply dpll_h_okFormula; eauto 3.
Qed.
Hint Resolve dpll_okFormula.

Lemma dpll_h_length : forall F n m m', dpll_h F m n = Some m'
                                          -> length m' = length m + n.
  induction n; simpl; intros;
  destruct (okFormula m F) eqn:?; options.
  destruct (dpll_h F (m ++ true :: nil) n) eqn:?; options; eauto 3.
  {
    replace (length m + S n) with (length (m ++ true :: nil) + n); eauto.
    autorewrite with list; simpl; omega.
  }
  {
    replace (length m + S n) with (length (m ++ false :: nil) + n); eauto.
    autorewrite with list; simpl; omega.
  }
Qed.

Lemma dpll_length : forall F nv m , dpll nv F = Some m
                                      -> length m = nv.
  unfold dpll; intros.
  change (length m = length nil(A:=bool) + nv).
  eapply dpll_h_length; eauto 3.
Qed.
Hint Resolve dpll_length.

Lemma dpll_Some_interp : forall nv F m, dpll nv F = Some m -> wf_formula nv F
                                       -> interpFormula (m2i m) F = true.
  intros.
  assert (length m = nv) by eauto 3.
  eapply okFormula_interpFormula; try eassumption; eauto 3; omega.
Qed.

Theorem dpll_sat_sound : forall F nv, dpll nv F <> None -> wf_formula nv F
                                     -> satisfiable F.
  red; intros.
  destruct (dpll nv F) eqn:?; try congruence.
  exists (m2i l); eapply dpll_Some_interp; eauto 3.
Qed.

Corollary dpll_sat_sound' : forall n f, dpll n f <> None -> wf_formula n f
                                       -> exists g, satFormula g f.
  intros; eapply satisfiable_satFormula, dpll_sat_sound; eauto 3.
Qed.


(*=============================================================================
 * denotation into Coq (for reflective tactics)
 *===========================================================================*)

Section denotation.
  Variable g : context.

  Definition denoteLit l :=
    match l with
      | pos n => g n
      | neg n => ~ g n
    end.

  Fixpoint denoteClause c :=
    match c with
      | nil => False
      | l :: c' => denoteLit l \/ denoteClause c'
    end.

  Fixpoint denoteFormula f :=
    match f with
      | nil => True
      | c :: f' => denoteClause c /\ denoteFormula f'
    end.
End denotation.


(*=============================================================================
 * denoteFormula -> satFormula
 *===========================================================================*)

Lemma denoteClause_satClause : forall g c, denoteClause g c -> satClause g c.
  induction c; simpl; try tauto; destruct 1.
  exists a; simpl; auto.
  destruct IHc as [? [] ]; auto.
  exists x; simpl; auto.
Qed.
Hint Resolve denoteClause_satClause.

Lemma denoteFormula_satClause : forall g f c, denoteFormula g f -> In c f
                                              -> satClause g c.
  induction f; simpl; try tauto; destruct 1, 1; subst; auto.
Qed.
Hint Resolve denoteFormula_satClause.

Theorem denoteFormula_satFormula : forall g f, denoteFormula g f
                                               -> satFormula g f.
  red; intros; eauto 3.
Qed.
Hint Resolve denoteFormula_satFormula.


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

Theorem denoteFormula_trim : forall g x, denoteFormula' g x -> denoteFormula g x.
  induction x; simpl; try tauto; intros.
  destruct x; simpl; auto.
  destruct H.
  split; auto.
  apply IHx; auto.
Qed.
Hint Resolve denoteFormula_trim.


(*=============================================================================
 * reification
 *===========================================================================*)

Theorem dpll_correct : forall n g f, dpll n f = None -> ~ denoteFormula' g f.
  red; intros; assert (satFormula g f) by auto.
  contradict H1; eapply dpll_unsat_sound; eauto.
Qed.


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
    change (denoteFormula' (nth2fun g True) f) in H.
    change (denoteClause' (nth2fun g True) c).
  Abort.
End reification_test.


(*=============================================================================
 * reflective tactic
 *===========================================================================*)

Ltac dpll_h :=
  match goal with
    | |- ~ ?F =>
      let g := allVars (@nil Prop) F in
      let f := reifyFormula g F in
      change (~ denoteFormula' (nth2fun g True) f);
      apply (dpll_correct (length g)); auto
  end.

Ltac dpll := solve [dpll_h].

Section PigeonHole.
  Variables p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop.

  Example hole2 :=
    (~p1 \/ ~p3) /\
    (~p1 \/ ~p5) /\
    (~p3 \/ ~p5) /\
    (~p2 \/ ~p4) /\
    (~p2 \/ ~p6) /\
    (~p4 \/ ~p6) /\
    (p1 \/ p2) /\
    (p3 \/ p4) /\
    (p5 \/ p6).

  Example hole3 :=
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

  Goal ~ hole2.
    unfold hole2; dpll.
  Qed.

  Goal ~ hole3. (* tauto will be very slow *)
    unfold hole3; dpll.
  Qed.

End PigeonHole.


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
 * numVarsFormula and well-formedness
 *===========================================================================*)

Fixpoint numVarsClause c :=
  match c with
    | nil => 0
    | l :: c' => max (litVar l + 1) (numVarsClause c')
  end.

Fixpoint numVarsFormula F :=
  match F with
    | nil => 0
    | c :: F' => max (numVarsClause c) (numVarsFormula F')
  end.

Lemma numVarsClause_wf_clause : forall n x, numVarsClause x <= n
                                            -> wf_clause n x.
  red; induction x; simpl; try tauto; intros.
  apply NPeano.Nat.max_lub_iff in H; destruct H.
  destruct H0; subst; try omega; auto.
Qed.
Hint Resolve numVarsClause_wf_clause.

Lemma numVarsFormula_In : forall F c n, numVarsFormula F <= n -> In c F
                                        -> numVarsClause c <= n.
  induction F; simpl; try tauto; destruct 2; subst;
  apply NPeano.Nat.max_lub_iff in H; destruct H; auto.
Qed.
Hint Resolve numVarsFormula_In.

Lemma numVarsFormula_lt_wf : forall n F, numVarsFormula F <= n
                                         -> wf_formula n F.
  red; intros; eauto 3.
Qed.

Theorem wf_numVarsFormula : forall F, wf_formula (numVarsFormula F) F.
  intros; apply numVarsFormula_lt_wf; omega.
Qed.
Hint Resolve wf_numVarsFormula.

Lemma wf_clause_numVarsClause : forall n x, wf_clause n x
                                            -> numVarsClause x <= n.
  induction x; simpl; try omega; intros.
  assert (litVar a < n) by auto.
  apply Max.max_lub; eauto 3; omega.
Qed.
Hint Resolve wf_clause_numVarsClause.

Lemma wf_formula_numVarsFormula : forall n f, wf_formula n f
                                              -> numVarsFormula f <= n.
  induction f; simpl; intros; try omega.
  apply Max.max_lub; eauto 3.
Qed.
Hint Resolve wf_formula_numVarsFormula.


(*=============================================================================
 * refutable -> dpll = None
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
                                     -> numVarsFormula f <= length l -> False.
  induction 1; intros; try congruence.
  apply IHrefutable1; autorewrite with list; try omega.
  apply okFormula_app; auto.
  apply numVarsFormula_lt_wf; auto.
Qed.

Theorem refutable_dpll_None : forall n f, refutable f nil -> wf_formula n f
                                          -> dpll n f = None.
  intros; destruct (dpll n f) eqn:?; eauto 3.
  exfalso.
  assert (refutable f l) by auto.
  eapply refutable_contra; eauto 2.
  erewrite dpll_length by eauto 2; eauto 3.
Qed.

Corollary refutable_dpll_None' : forall f, refutable f nil
                                        -> exists n, dpll n f = None.
  intros; exists (numVarsFormula f); apply refutable_dpll_None; auto.
Qed.


(*=============================================================================
 * more corollaries
 *===========================================================================*)

Goal forall f, refutable f nil -> ~ satisfiable f.
  intros.
  assert (dpll (numVarsFormula f) f = None).
  solve [apply refutable_dpll_None; auto].
  eapply dpll_unsat_sound'; eauto 3.
Qed.
  
Goal forall f, ~ satisfiable f -> refutable f nil.
  intros.
  destruct (dpll (numVarsFormula f) f) eqn:?; auto.
  contradict H; eapply dpll_sat_sound; eauto 3; congruence.
  eapply dpll_refutable; eauto 3.
Qed.

Goal forall f g, ~ satisfiable f -> ~ satFormula g f.
  intros.
  destruct (dpll (numVarsFormula f) f) eqn:?; auto.
  contradict H; eapply dpll_sat_sound; eauto 3; congruence.
  eapply dpll_unsat_sound; eauto 3.
Qed.  

Goal forall f, satisfiable f -> exists n m, dpll n f = Some m /\ wf_formula n f.
  intros; destruct (dpll (numVarsFormula f) f) eqn:?; eauto 4.
  contradict H; eapply dpll_unsat_sound'; eauto 3.
Qed.
