Require Import proofsystem.
Require Import coinduction.

Section Semantics.

  Parameter cfg : Set.
  Parameter R : cfg -> cfg -> Prop.

  Definition claims_of_rule (env:Type) (l r : formula cfg env) (x : cfg) (P : cfg -> Prop) : Prop :=
     exists e, l e x /\ (forall x', r e x' -> P x').
  Definition claims_of_system (rules : system cfg) (x : cfg) (P : cfg -> Prop) : Prop :=
    exists (env:Type) l r, rules env l r /\ claims_of_rule env l r x P.
  Definition claims_of_opt_system (rules : option (system cfg)) : Spec cfg :=
    match rules with
    | Some actual_rules => claims_of_system actual_rules
    | None => fun x P => False
    end.

Definition interp (C : option (system cfg)) (A : system cfg)
           env (l r : formula cfg env) (X : Spec cfg) : Prop :=
  forall x P, claims_of_rule env l r x P ->
              step R (trans R X) x P.

Ltac assert_arg H :=
  match type of H with
  | ?T -> _ => let HT := fresh "HT" in assert T as HT;[|specialize (H HT);clear HT]
  end.

Lemma rl_to_coinduction: forall C A env (l r : formula cfg env) (X : Spec cfg)
    (H_A: forall x P, claims_of_system A x P ->
           (match C with None => reaches R x P \/ X x P
                       | Some _ => next R (reaches R) x P end))
    (H_C: forall x P, claims_of_opt_system C x P -> X x P),
    IS cfg R C A env l r ->
    forall x P, claims_of_rule env l r x P ->
    match C with
      | None => trans R X x P
      | Some _ => next R (trans R X) x P
    end.
Proof.
  intros until 2;induction 1;destruct 1 as (rho & ? & ?);
        repeat match goal with | [H : _ |- _] => specialize (H H_A H_C) end.
  + (* is_step *)
    destruct (H _ _ H0) as [[]].
    assert (P x0) by auto.
    destruct C;eauto using next, trans.
  + (* is_axiom *)
    intros.
    specialize (H_A x P).
    assert_arg H_A.
    do 7 (eassumption || esplit).
    destruct C;destruct H_A;eauto using next,trans.
  + (* is_refl *)
    destruct C;[destruct H|auto using ddone].
  + (* is_trans *)
    clear H H0.
    specialize (IHIS1 x (phi' rho)).
    assert_arg IHIS1.
    eexists;esplit;[eassumption|]. trivial.
    assert_arg IHIS2.
      clear -H_A H_C.
      intros.
      destruct H as (? & ? & ? & ? & ?).
      assert (A x0 x1 x2 -> reaches R x P \/ X x P) by
        (clear H;intros;specialize (H_A x P);
            assert_arg H_A;[solve[repeat (eassumption || esplit)]|
         destruct C;destruct H_A;eauto using reaches]).
      destruct C as [C|];[|solve[auto]].
      destruct H;[|solve[auto]].
      clear H1.
      right. apply H_C. simpl. repeat (eassumption || esplit).
    assert_arg IHIS2;[solve[destruct 1]|].
    destruct C as [C | ].
    - (* C is Some -> this is the interesting case *)
    destruct IHIS1. econstructor;[eassumption|].
    eapply dtrans';[eassumption|].
    intros. apply IHIS2.
    repeat (eassumption || esplit).
    - (* C is None *)
    eapply dtrans';[eassumption|].
    intros. apply IHIS2.
    repeat (eassumption || esplit).
  + (* is_conseq *)
    apply H in H2. clear H.
    apply IHIS.
    repeat (eassumption || esplit).
    eauto.
  + (* is_case *)
    destruct H1.
    apply IHIS1;repeat (eassumption || esplit).
    apply IHIS2;repeat (eassumption || esplit).
  + (* is_abstr *)
    destruct H0.
    apply IHIS.
    repeat (eassumption || esplit).
  + (* is_abstr' *)
    apply IHIS.
    destruct H1.
    specialize (H rho x0).
    repeat (eassumption || esplit).
    intros. specialize (H x'). destruct H.
    eauto.
  + (* is_circ *)
    admit. (* not allowed in set circularity proofs *)
  + (* is_subst *)
    apply IHIS.
    repeat (eassumption || esplit).
  + (* is_lf *)
    apply IHIS.
    destruct H0.
    repeat (eassumption || esplit).
    eauto.
Admitted.

Theorem rl_is_coinduction: forall C A env (l r : formula cfg env)
    (H_A: forall x P, claims_of_system A x P -> next R (reaches R) x P),
    IS cfg R (Some C) A env l r ->
    forall x P, claims_of_rule env l r x P -> step R (trans R (claims_of_system C)) x P.
Proof.
intro C; intros.
cut (next R (trans R (claims_of_system C)) x P).
clear. destruct 1;eauto using step.
eapply rl_to_coinduction with (C:=Some C) (X:=claims_of_system C);
try eassumption.
trivial.
Qed.
End Semantics.
