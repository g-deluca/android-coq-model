Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Import Classical.
Require Import Estado.
Require Import DefBasicas.
Require Import Semantica.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.
Require Import MyList.
Require Import ListAuxFuns.
Require Import ValidStateLemmas.
Require Import SameEnvLemmas.
Require Import Semantica.
Require Import RuntimePermissions.
Require Import EqTheorems.
Require Import Trace.
Require Import PropertiesAuxFuns.

Require Import TraceRelatedLemmas.
Require Import Coq.Arith.Lt.

Section IfOldAppRunThenVerified.

Lemma inductMe : forall
(initState : System)
(initStateValid : validstate initState)
(a : idApp)
(l : list Action)
(aIsTheSame : ~ In (uninstall a) l)
(notVerified : ~ In (verifyOldApp a) l)
(couldntRun : ~canRun a initState)
(aInstalled: 
  In a (apps (state initState)) \/
  (exists x0, In x0 (systemImage (environment initState)) /\ idSI x0 = a)),
validstate ((last (trace initState l)) initState) /\
(In a (apps (state ((last (trace initState l)) initState))) \/ (exists x0, In x0 (systemImage (environment ((last (trace initState l)) initState))) /\ idSI x0 = a)) /\
(~canRun a ((last (trace initState l)) initState)).
Proof.
    intros.
    induction l using rev_ind.
  - simpl. split; auto.
  - assert (~In (uninstall a) l).
    unfold not;intros.
    apply aIsTheSame.
    rewrite in_app_iff.
    left;auto.
    assert (~In (verifyOldApp a) l).
    unfold not;intros.
    apply notVerified.
    rewrite in_app_iff.
    left;auto.
    specialize (IHl H H0).
    destruct IHl.
    split.
    rewrite (lastTraceApp initState l x initState).
    apply stepIsInvariant. auto.

    rewrite lastTraceApp.
    remember (last (trace initState l) initState) as lastSys.
    destruct H2.

    assert (x<>uninstall a) as xNotUninstallA.
    unfold not;intros.
    apply aIsTheSame.
    rewrite in_app_iff.
    right.
    rewrite H4.
    apply in_eq.

    split.
    destruct H2.
    left.

    apply aInAppsAndNotUninstalled;auto.
    right.
    destruct H2.
    exists x0.
    destruct H2.
    split;auto.

    assert (systemImage (environment (system (step lastSys x))) = systemImage (environment lastSys)).
    destruct x;simpl.
    unfold install_safe; case_eq (install_pre i m c l0 lastSys);intros;simpl;auto.
    unfold uninstall_safe; case_eq (uninstall_pre i lastSys);intros;simpl;auto.
    unfold grant_safe; case_eq (grant_pre p i lastSys);intros;simpl;auto.
    unfold grantAuto_safe; case_eq (grantAuto_pre p i lastSys);intros;simpl;auto.
    unfold revoke_safe; case_eq (revoke_pre p i lastSys);intros;simpl;auto.
    unfold revokegroup_safe; case_eq (revokegroup_pre i i0 lastSys);intros;simpl;auto.
    auto.
    unfold read_safe; case_eq (read_pre i c u lastSys);intros;simpl;auto.
    unfold write_safe; case_eq (write_pre i c u v lastSys);intros;simpl;auto.
    unfold startActivity_safe; case_eq (startActivity_pre i i0 lastSys);intros;simpl;auto.
    unfold startActivity_safe; case_eq (startActivity_pre i i0 lastSys);intros;simpl;auto.
    unfold startService_safe; case_eq (startService_pre i i0 lastSys);intros;simpl;auto.
    unfold sendBroadcast_safe; case_eq (sendBroadcast_pre i i0 o lastSys);intros;simpl;auto.
    unfold sendBroadcast_safe; case_eq (sendBroadcast_pre i i0 o lastSys);intros;simpl;auto.
    unfold sendStickyBroadcast_safe; case_eq (sendStickyBroadcast_pre i i0 lastSys);intros;simpl;auto.
    unfold resolveIntent_safe; case_eq (resolveIntent_pre i i0 lastSys);intros;simpl;auto.
    unfold receiveIntent_safe; case_eq (receiveIntent_pre i i0 i1 lastSys);intros;simpl;auto.
    unfold receiveIntent_post.
    destruct (maybeIntentForAppCmp i i1 i0 lastSys);auto. 
    unfold stop_safe; case_eq (stop_pre i lastSys);intros;simpl;auto.
    unfold grantP_safe; case_eq (grantP_pre i c i0 u p lastSys);intros;simpl;auto.
    unfold revokeDel_safe; case_eq (revokeDel_pre i c u p lastSys);intros;simpl;auto.
    unfold call_safe; case_eq (call_pre i s lastSys);intros;simpl;auto.
    unfold verifyOldApp_safe; case_eq (verifyOldApp_pre i lastSys);intros;simpl;auto.
    rewrite H5;auto.

    assert (x <> verifyOldApp a) as xNotVerifyOldApp.
    unfold not;intros.
    apply notVerified.
    rewrite in_app_iff.
    right.
    rewrite H4.
    apply in_eq.

    unfold not; intros.
    apply H3.
    unfold canRun in H4.
    unfold canRun.
    destruct H4. left.
 (* Caso alreadyVerifiedIsTheSame*)
 -- apply (alreadyVerifiedSame x a); auto.
 (* Caso manifestIsTheSame *)
 -- destruct H4 as [m [n [H4 [H5 H6]]]].
    right. exists m, n.
    split; auto.
    unfold isManifestOfApp.
    destruct H4.

    left. apply (manifestsSame x); auto.

    right. clear H5 H6.
    destruct H4 as [sysapp [H4 [H5 H6]]].
    exists sysapp.
    split; auto.
    apply (sysImgSame x lastSys H1 sysapp);auto.
Qed.

Theorem ifOldAppRunThenWasVerified :
  forall
    (initState lastState: System)
    (a: idApp)
    (l: list Action)
    (aInstalled:In a (apps (state initState)) \/ (exists x0, In x0 (systemImage (environment initState)) /\ idSI x0 = a))
    (vsInit: validstate initState)
    (oldApp: isOldApp a initState)
    (notVerified: ~(In a (alreadyVerified (state initState))))
    (canRunLastState: canRun a lastState)
    (aIsTheSame : ~ In (uninstall a) l)
    (fromInitToLast: last (trace initState l) initState  = lastState),
    In (verifyOldApp a) l.
Proof.
    intros.
    apply NNPP.
    unfold not;intros.
    assert (validstate (last (trace initState l) initState) /\ (In a (apps (state (last (trace initState l) initState))) \/ (exists x0, In x0 (systemImage (environment (last (trace initState l) initState))) /\ idSI x0 = a)) /\ ~ (canRun a (last (trace initState l) initState))).
    apply inductMe;auto.
    unfold canRun. unfold not.
    intros. destruct H0.
    contradiction.
    unfold isOldApp in oldApp.
    destruct oldApp as [m [n [H1 [H2 nLTVulnerableSdk]]]].
    destruct H0 as [m' [n' [H3 [H4 nGTVulnerableSdk]]]].

    assert (m=m').
    apply (sameAppSameManifest initState vsInit a); auto.

    rewrite <- H0 in H4.
    rewrite H2 in H4.
    inversion H4.
    rewrite <- H6 in nGTVulnerableSdk.
    assert (n<n).
    apply (lt_trans n vulnerableSdk); auto.
    apply lt_irrefl in H5; auto.

    destruct H0.
    destruct H1.
    rewrite fromInitToLast in H2.
    contradiction.
Qed.

End IfOldAppRunThenVerified.