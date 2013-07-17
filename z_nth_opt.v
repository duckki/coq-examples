Require Import List ZArith.
Local Open Scope Z_scope. 
 
Section z_nth_opt.

  Variable K : Type.
 
  Ltac lift :=
    match goal with
      | H: _ |- _ => apply -> Z.eqb_eq in H
      | H: _ |- _ => apply <- Zlt_is_lt_bool in H
      | H: _ |- _ => apply -> Z.ltb_ge in H
      | _ => apply -> Zlt_is_lt_bool
      | _ => apply <- Z.eqb_eq
    end.

  Ltac break_if :=
    match goal with
      | _ => lift
      | |- context [if ?tst then _ else _ ] =>
        let vn := fresh "_iftst_" in
        destruct tst eqn: vn
    end.

  Function z_nth_opt (lst: list K) (i: Z) : option K :=
    if (i <? 0) then None
    else
      match lst with
      | nil => None
      | x :: xs =>
          if (i =? 0)
          then Some x
          else z_nth_opt xs (i-1)
      end.
 
  Goal forall (i: Z) (x: K) (xs: list K), i <> 0
         -> z_nth_opt (x::xs) i = z_nth_opt xs (i-1).
  Proof. 
    induction xs; simpl; intros; repeat break_if; auto; omega.
  Qed.

End z_nth_opt.
