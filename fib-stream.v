Require Import Arith.
Set Implicit Arguments.

(* ===========================================================================
 * some useful coinductive definitions (from the CPDT book by Adam Chlipala)
 * ========================================================================= *)

CoInductive stream (A : Type) : Type :=
  | Cons : A -> stream A -> stream A.

CoInductive stream_eq A : stream A -> stream A -> Prop :=
| stream_eq_refl : forall v s1 s2, stream_eq s1 s2
                                   -> stream_eq (Cons v s1) (Cons v s2).


(* ===========================================================================
 * fibonacci number stream (slightly modifed from Harley's example)
 * ========================================================================= *)

CoFixpoint fib_stream_aux (n:nat) (m:nat) := Cons (n + m) (fib_stream_aux m (n + m)).
Definition fib_stream := Cons 0 (Cons 1 (fib_stream_aux 0 1)).


(* ===========================================================================
 * finite observation of streams
 * ========================================================================= *)

Fixpoint stream_nth A (s:stream A) (n:nat) : A :=
  match s with
    | Cons v s' =>
      match n with
        | 0 => v
        | S n' => stream_nth s' n'
      end
  end.

Theorem stream_eq_nth_eq : forall A n (a b : stream A),
                             stream_eq a b
                             -> stream_nth a n = stream_nth b n.
  induction n; destruct 1; intuition; simpl; apply IHn; assumption.
Qed.


(* ===========================================================================
 * correspondence between fib_stream and a recursive definition of fib
 * ========================================================================= *)

(* a recursive definition *)
Fixpoint fib (n:nat) : nat :=
  match n with
    | 0 => 0
    | S n' =>
      match n' with
        | 0 => 1
        | S n'' => fib n'' + fib n'
      end
  end.


(* some helper definition and lemma *)
CoFixpoint stream_plus (a b: stream nat) : stream nat :=
  match a, b with
    | Cons n a', Cons m b' => Cons (n + m) (stream_plus a' b')
  end.

Lemma stream_nth_plus : forall n s s', stream_nth s n + stream_nth s' n
                                       = stream_nth (stream_plus s s') n.
  induction n; destruct s, s'; simpl; intuition.
Qed.


(* tools for coinduction (from the CPDT book by Adam Chlipala) *)
Definition frob A (s : stream A) : stream A :=
  match s with
    | Cons h t => Cons h t
  end.

Theorem frob_eq : forall A (s : stream A), s = frob s.
  destruct s; reflexivity.
Qed.


(* a fact about fib_stream_aux *)
Lemma fib_stream_aux_plus : forall n m,
      stream_eq (fib_stream_aux n m)
                (stream_plus (Cons n (Cons m (fib_stream_aux n m)))
                             (Cons m (fib_stream_aux n m))).
  cofix; intros.
  rewrite (frob_eq (stream_plus (Cons n (Cons m (fib_stream_aux n m))) (Cons m (fib_stream_aux n m)))).
  rewrite (frob_eq (fib_stream_aux n m)).
  simpl.
  constructor.
  apply fib_stream_aux_plus.
Qed.


(* strong induction *)
Require Import Omega.

Section strong_ind.
  Variable P : nat -> Prop.

  Hypothesis H : forall n, (forall m, m < n -> P m) -> P n.

  Lemma strong_ind' : forall n m, m < n -> P m.
    induction n; intuition; omega.
  Qed.

  Theorem strong_ind : forall n, P n.
    intros; apply strong_ind' with (S n); omega.
  Qed.
End strong_ind.


(* main theorem *)
Theorem fib_stream_eq_fib : forall n, stream_nth fib_stream n = fib n.
  induction n using strong_ind; intuition.
  destruct n; simpl in *; intuition; rewrite <- (H n) by omega.
  destruct n; simpl in *; intuition; rewrite <- (H n) by omega.
  rewrite stream_nth_plus by auto.
  apply stream_eq_nth_eq.
  apply fib_stream_aux_plus.
Qed.
