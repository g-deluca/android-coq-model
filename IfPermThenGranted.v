(* In this file we prove that if at some initial state an application doesn't have a permission and
after executing some actions it ends up having it, then one of those actions was the one that granted
that permission to that application *)

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
Require Export PropertiesAuxFuns.

Require Import TraceRelatedLemmas.

Section IfPermThenGranted.

Lemma inductMe : forall
(initState : System)
(initStateValid : validstate initState)
(a : idApp)
(p : Perm)
(pDangerous:pl p = dangerous)
(l : list Action)
(aIsTheSame : ~ In (uninstall a) l)
(notRegranted : ~ In (grant p a) l)
(notRegrantedAuto : ~ In (grantAuto p a) l)
(didntHavePerm : ~appHasPermission a p initState)
(wasInstalled: In a (apps (state initState)) \/ (exists x0, In x0 (systemImage (environment initState)) /\ idSI x0 = a)),
validstate ((last (trace initState l)) initState) /\ (In a (apps (state ((last (trace initState l)) initState))) \/ (exists x0, In x0 (systemImage (environment ((last (trace initState l)) initState))) /\ idSI x0 = a)) /\ (~appHasPermission a p ((last (trace initState l)) initState)).
Proof.
    intros.
    induction l using rev_ind.
    simpl.
    split;auto.
    assert (~In (uninstall a) l).
    unfold not;intros.
    apply aIsTheSame.
    rewrite in_app_iff.
    left;auto.
    assert (~In (grant p a) l).
    unfold not;intros.
    apply notRegranted.
    rewrite in_app_iff.
    left;auto.
    specialize (IHl H H0).
    destruct IHl.
    unfold not. intros.
    apply notRegrantedAuto.
    rewrite in_app_iff.
    left; auto.
    split.
    rewrite (lastTraceApp initState l x initState).
    apply stepIsInvariant.
    auto.
    rewrite (lastTraceApp).
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
    unfold grant_safe; case_eq (grant_pre p0 i lastSys);intros;simpl;auto.
    unfold grantAuto_safe; case_eq (grantAuto_pre p0 i lastSys);intros;simpl;auto.
    unfold revoke_safe; case_eq (revoke_pre p0 i lastSys);intros;simpl;auto.
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
    unfold grantP_safe; case_eq (grantP_pre i c i0 u p0 lastSys);intros;simpl;auto.
    unfold revokeDel_safe; case_eq (revokeDel_pre i c u p0 lastSys);intros;simpl;auto.
    unfold call_safe; case_eq (call_pre i s lastSys);intros;simpl;auto.
    unfold verifyOldApp_safe; case_eq (verifyOldApp_pre i lastSys);intros;simpl;auto.
    rewrite H5;auto.


    assert (x<>grant p a) as xNotGrantPA.
    unfold not;intros.
    apply notRegranted.
    rewrite in_app_iff.
    right.
    rewrite H4.
    apply in_eq.

    assert (x<>grantAuto p a) as xNotGrantAutoPA.
    unfold not; intros.
    apply notRegrantedAuto.
    rewrite in_app_iff.
    right.
    rewrite H4.
    apply in_eq.

    unfold not;intros.
    apply H3.
    unfold appHasPermission in H4.
    unfold appHasPermission.
    destruct H4.
    destruct H4.
    destruct H4.
    left.
    apply (permAIsTheSame p x x0);auto.
    right.
    destruct H4.
    destruct H5.
    destruct H5.
    destruct H6.
    destruct H6.
    destruct H6.
    assert (map_apply idApp_eq (defPerms (environment lastSys)) a=Value idApp x1).
    apply (defPermsSame x);auto.
    split.
    unfold permExists.
    right.
    unfold usrDefPerm.
    left.
    exists a,x1.
    auto.
    split.
    exists x0.
    destruct H5.
    split;auto.
    unfold isManifestOfApp.
    destruct H5.
    left.
    apply (manifestsSame x);auto.
    right.
    destruct H5.
    destruct_conj H5.
    exists x2.
    split;auto.
    apply (sysImgSame x lastSys H1 x2);auto.
    left.
    exists x1.
    auto.
    rewrite pDangerous in *.
    destruct H6.
    inversion H6.
    destruct H6.
    destruct H6.
    destruct H6; inversion H6.
    destruct H6. inversion H6.
Qed.



    Theorem ifPermThenGrantedProof : forall
    (initState lastState:System)
    (initStateValid:validstate initState)
    (a:idApp)
    (aInstalled:In a (apps (state initState)) \/ (exists x0, In x0 (systemImage (environment initState)) /\ idSI x0 = a))
    (p:Perm)
    (pDangerous:pl p = dangerous)
    (aHasPerm : appHasPermission a p lastState)
    (aDidntHavePerm :~appHasPermission a p initState)
    (l:list Action)
    (aIsTheSame :~In (uninstall a) l)
    (fromInitToLast : last (trace initState l) initState = lastState),
    In (grant p a) l \/ In (grantAuto p a) l.
Proof.
    intros.
    apply NNPP.
    unfold not;intros.
    assert (validstate (last (trace initState l) initState) /\ (In a (apps (state (last (trace initState l) initState))) \/ (exists x0, In x0 (systemImage (environment (last (trace initState l) initState))) /\ idSI x0 = a)) /\ ~ appHasPermission a p (last (trace initState l) initState)).
    apply inductMe;auto.
    destruct H0.
    destruct H1.
    rewrite fromInitToLast in H2.
    contradiction.
Qed.

End IfPermThenGranted.

