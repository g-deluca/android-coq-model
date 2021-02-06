(* In this file we show that in a particular scenario, intent spoofing is not possible *)

Require Export Exec.
Require Export Estado.
Require Export Operaciones.
Require Export Semantica.
Require Export ErrorManagement.
Require Export Tacticas.
Require Export Maps.

Lemma vsToAllCmpDifferent: forall (s:System), validstate s -> allCmpDifferent s.
Proof.
intros s H_vs.
unfold validstate in H_vs.
apply H_vs.
Qed.

Lemma vsToNotRepeatedCmps: forall (s:System), validstate s -> notRepeatedCmps s.
Proof.
intros s H_vs.
unfold validstate in H_vs.
apply H_vs.
Qed.

Lemma intentSpoofing : forall (a1 a2:idApp)(c1 c2:Cmp)(ic1:iCmp)(i:Intent)(s:System),
validstate s ->
inApp c1 a1 s ->
inApp c2 a2 s ->
a1 <> a2 ->
~canBeStarted c2 s ->
(map_apply iCmp_eq (running (state s)) ic1 = Value iCmp c1 ->
~ isCProvider c1 ->
(cmpName i) = Some (getCmpId c2) ->
~ (pre_receiveIntent i ic1 a2 s)).


Proof.
intros a1 a2 c1 c2 ic1 i s H_vs H_c1_in_a1 H_c2_in_a2
H_a1_not_a2 H_not_canBeStarted_c2 H_running H_not_CP_c1 H_cmpName.
unfold not; intro H_pre_receive.
destruct H_pre_receive as [_ [c2' H_conj]].
destruct H_conj as [H_intentForApp H_conj].
destruct H_conj as [H_notCP_c2' H_exists].
destruct H_exists as [c1' H_conj].
destruct H_conj as [H_running_ic1_c1' H_conj].
destruct H_conj as [H_notCP_c1' H_conj].
destruct H_conj as [H_canStart_c1_c2' H_conj].
destruct H_conj as [H_intAct H_intBroad].
clear H_intAct; clear H_intBroad.
generalize (vsToAllCmpDifferent s H_vs).
generalize (vsToNotRepeatedCmps s H_vs).
intros H_notRepeatedCmps H_allCmpDifferent.

absurd (canBeStarted c2 s).

(*~ (canBeStarted c2 s)*)
intro; auto.

(*canBeStarted c2 s)*)
destruct H_intentForApp as [H_cmpName_c2' H_conj].
destruct H_conj as [H_sentIntents H_c2'_in_a2].
rewrite H_cmpName_c2' in H_cmpName.
inversion H_cmpName as [H_idc2'_idc2].
symmetry in H_idc2'_idc2.
unfold allCmpDifferent in H_allCmpDifferent.
rewrite <- (H_allCmpDifferent c2 c2' a2 a2 H_c2_in_a2 H_c2'_in_a2 H_idc2'_idc2) in H_canStart_c1_c2'.

destruct H_canStart_c1_c2' as [a1' H_exists].
destruct H_exists as [a2' H_conj].
destruct H_conj as [H_c1'_in_a1' H_conj].
destruct H_conj as [H_c2_in_a2' H_or].

elim (H_or).

intro.
absurd (a1=a2).
assumption.
rewrite H_running_ic1_c1' in H_running;
inversion H_running.
rewrite H1 in H_c1'_in_a1'.
unfold notRepeatedCmps in H_notRepeatedCmps.
rewrite (H_notRepeatedCmps c1 a1 a1' H_c1_in_a1 H_c1'_in_a1').
rewrite (H_notRepeatedCmps c2 a2 a2' H_c2_in_a2 H_c2_in_a2').
assumption.

intro H_conj.
apply H_conj.
Qed.



