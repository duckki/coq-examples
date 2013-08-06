Set Implicit Arguments.
Require Import Omega.

Section Ind_base_k.
  Variable P : nat -> Prop.
  Variable k : nat.
  Hypothesis Pk : P k.
  Hypothesis PS : forall n, P n -> k <= n -> P (S n).

  Theorem P_ind_base_k : forall n, k <= n -> P n.
    induction n; inversion 1; subst; auto.
  Qed.
End Ind_base_k.

Section strong_ind.
  Variable P : nat -> Prop.
  Hypothesis H : forall n, (forall m, m < n -> P m) -> P n.

  Lemma strong_ind' : forall n m, m < n -> P m.
    induction n; intros; intuition; omega.
  Qed.

  Theorem strong_ind : forall n, P n.
    intros; apply strong_ind' with (S n); auto.
  Qed.
End strong_ind.

Require Import Even.

Section Ind_even.
  Variable P : nat -> Prop.
  Hypothesis P_base : P 0.
  Hypothesis P_step : forall n, P n -> even n -> P (S (S n)).

  Theorem P_ind_even : forall n, even n -> P n.
    induction n using strong_ind; intuition.
    repeat match goal with
             | _ => solve [auto]
             | H: even _ |- _ => inversion H; clear H; subst
             | H: odd _  |- _ => inversion H; clear H; subst
           end.
  Qed.
End Ind_even.


Definition nzn: Type := {n: nat | n <> O}.

Section Ind_nzn.
  Lemma S_nzn : forall n, S n <> 0.
    red; intros; discriminate.
  Qed.

  Definition one : nzn.
    refine (exist _ 1 _); apply S_nzn.
  Defined.

  Definition Succ (n : nzn) : nzn.
    refine (match n with
              | exist v p => exist _ (S v) _
            end); apply S_nzn.
  Defined.

  Variable P : nzn -> Type.
  Hypothesis P_base : P one.
  Hypothesis P_step : forall n, P n -> P (Succ n).
  Hypothesis proofIrr : forall n (H H': S n <> 0), H = H'.

  Theorem nzn_rect : forall n, P n.
    destruct n.
    induction x; try congruence.
    destruct (eq_nat_dec x 0); subst.
    {
      replace n with (@S_nzn 0); auto.
    }
    {
      specialize (IHx n0).
      specialize (P_step IHx).
      replace n with (@S_nzn x); auto.
    }
  Defined.

End Ind_nzn.

Section Ind_nzn'.
  Variable P : nzn -> Prop.
  Hypothesis P_base : P one.
  Hypothesis P_step : forall n, P n -> P (Succ n).
  Hypothesis proofIrr : forall n (H H': S n <> 0), H = H'.
  
  Theorem nzn_ind : forall n, P n.
    intros; apply nzn_rect; auto.
  Qed.

End Ind_nzn'.
