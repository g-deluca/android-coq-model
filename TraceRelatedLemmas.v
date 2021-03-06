Require Import DefBasicas.
Require Import Trace.
Require Import ListAuxFuns.
Require Import Maps.
Require Import AuxFunsCorrect.
Require Import ValidStateLemmas.
Require Import EqTheorems.
Require Import Tacticas.
Require Import Classical.
Require Import FunInd.

Section TraceRelatedProperties.
Lemma lastTraceApp : forall (initState:System) l x y, last (trace initState (l ++ x :: nil)) y = system (step (last (trace initState l) initState) x).
Proof.
    intros.
    functional induction (trace initState (l)).
    simpl.
    auto.
    rewrite <-app_comm_cons.
    unfold trace.
    fold trace.
    assert (last (system (step s action) :: trace (system (step s action)) (rest ++ x :: nil)) y = last (trace (system (step s action)) (rest ++ x :: nil)) y).
    apply lastConsLast.
    unfold not;intros.
    destruct rest.
    simpl in H.
    inversion H.
    simpl in H.
    inversion H.
    rewrite H.
    rewrite IHl0.
    assert ((last (system (step s action) :: trace (system (step s action)) rest) s)=(last (trace (system (step s action)) rest) (system (step s action)))).
    destruct ((trace (system (step s action)) rest)).
    auto.
    apply lastConsLast.
    unfold not;intros.
    inversion H0.
    rewrite H0.
    auto.
Qed.

Lemma aInAppsAndNotUninstalled : forall
    (s:System)
    (sValid : validstate s)
    (a:idApp)
    (aInS : In a (apps (state s)))
    (x:Action)
    (xNotUninstallA : x <> uninstall a),
    In a (apps (state (system (step s x)))).
Proof.
    intros.
    destruct x;
    simpl.
    unfold install_safe; case_eq (install_pre i m c l s);intros;auto.
    simpl.
    right;auto.
    
    unfold uninstall_safe; case_eq (uninstall_pre i s);intros;auto.
    simpl.
    apply removeSthElse.
    split;auto.
    unfold not;intros.
    apply xNotUninstallA.
    rewrite H0;auto.
    
    unfold grant_safe; case_eq (grant_pre p i s);intros;auto.
    unfold grantAuto_safe; case_eq (grantAuto_pre p i s);intros;auto.
    unfold revoke_safe; case_eq (revoke_pre p i s);intros;auto.
    unfold revokegroup_safe; case_eq (revokegroup_pre i i0 s);intros;auto.
    auto.
    unfold read_safe; case_eq (read_pre i c u s);intros;auto.
    unfold write_safe; case_eq (write_pre i c u v s);intros;auto.
    unfold startActivity_safe; case_eq (startActivity_pre i i0 s);intros;auto.
    unfold startActivity_safe; case_eq (startActivity_pre i i0 s);intros;auto.
    unfold startService_safe; case_eq (startService_pre i i0 s);intros;auto.
    unfold sendBroadcast_safe; case_eq (sendBroadcast_pre i i0 o s);intros;auto.
    unfold sendBroadcast_safe; case_eq (sendBroadcast_pre i i0 o s);intros;auto.
    unfold sendStickyBroadcast_safe; case_eq (sendStickyBroadcast_pre i i0 s);intros;auto.
    unfold resolveIntent_safe; case_eq (resolveIntent_pre i i0 s);intros;auto.
    unfold receiveIntent_safe; case_eq (receiveIntent_pre i i0 i1 s);intros;auto.
    simpl.
    unfold receiveIntent_post.
    destruct (maybeIntentForAppCmp i i1 i0 s);auto. 
    unfold stop_safe; case_eq (stop_pre i s);intros;auto.
    unfold grantP_safe; case_eq (grantP_pre i c i0 u p s);intros;auto.
    unfold revokeDel_safe; case_eq (revokeDel_pre i c u p s);intros;auto.
    unfold call_safe; case_eq (call_pre i s0 s);intros;auto.
    unfold verifyOldApp_safe; case_eq (verifyOldApp_pre i s);intros;auto.
Qed.

Lemma alreadyVerifiedSame : forall
    (x:Action)
    (a:idApp)
    (s:System)
    (sValid : validstate s)
    ( aInStep: In a (alreadyVerified (state (system (step s x)))))
    (xNotVerifyA : x <> verifyOldApp a)
    (xNotUninstallA : x <> uninstall a),
    In a (alreadyVerified (state s)).
Proof.
    intros.
    destruct x; simpl in *.

    unfold install_safe in *.
    case_eq (install_pre i m c l s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold uninstall_safe in *.
    case_eq (uninstall_pre i s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.
    rewrite <- removeSthElse in aInStep.
    destruct aInStep. auto.

    (* @TODO: Create a tactic that encapsulates this steps *)
    unfold grant_safe in *.
    case_eq (grant_pre p i s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold grantAuto_safe in *.
    case_eq (grantAuto_pre p i s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold revoke_safe in *.
    case_eq (revoke_pre p i s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold revokegroup_safe in *.
    case_eq (revokegroup_pre i i0 s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    auto.

    unfold read_safe in *.
    case_eq (read_pre i c u s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold write_safe in *.
    case_eq (write_pre i c u v s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold startActivity_safe in *.
    case_eq (startActivity_pre i i0 s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold startActivity_safe in *.
    case_eq (startActivity_pre i i0 s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold startService_safe in *.
    case_eq (startService_pre i i0 s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold sendBroadcast_safe in *.
    case_eq (sendBroadcast_pre i i0 o s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold sendBroadcast_safe in *.
    case_eq (sendBroadcast_pre i i0 o s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold sendStickyBroadcast_safe in *.
    case_eq (sendStickyBroadcast_pre i i0 s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold resolveIntent_safe in *.
    case_eq (resolveIntent_pre i i0 s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold receiveIntent_safe in *.
    case_eq (receiveIntent_pre i i0 i1 s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.
    unfold receiveIntent_post in *.
    destruct (maybeIntentForAppCmp i i1 i0 s); auto.

    unfold stop_safe in *.
    case_eq (stop_pre i s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold grantP_safe in *.
    case_eq (grantP_pre i c i0 u p s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold revokeDel_safe in *.
    case_eq (revokeDel_pre i c u p s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold call_safe in *.
    case_eq (call_pre i s0 s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.

    unfold verifyOldApp_safe in *.
    case_eq (verifyOldApp_pre i s);intros;rewrite H in aInStep;
      simpl in aInStep; auto.
    destruct aInStep.
    rewrite H0 in xNotVerifyA.
    contradiction. auto.
Qed.

Lemma manifestsSame : forall
        (x:Action)
        (a:idApp)
        (s:System)
        (sValid:validstate s)
        (aWasInstalled : In a (apps (state s)) \/ (exists x0, In x0 (systemImage (environment s)) /\ idSI x0 = a))
(xNotUninstallA : x <> uninstall a)
(x1 : Manifest)
(manifestx1 : map_apply idApp_eq (manifest (environment (system (step s x)))) a = Value idApp x1),
map_apply idApp_eq (manifest (environment s)) a = Value idApp x1.
Proof.
    intros.
    destruct x;simpl in manifestx1.
    unfold install_safe in manifestx1.
    case_eq (install_pre i m c l s);intros;rewrite H in manifestx1;
    simpl in manifestx1;
    auto.
    assert (i<>a).
    unfold install_pre in H.
    unfold not;intros.
    rewrite H0 in H.
    assert (isAppInstalled a s).
    unfold isAppInstalled.
    auto.
    rewrite isAppInstalled_iff in H1.
    rewrite H1 in H.
    inversion H.
    rewrite overrideNotEq in manifestx1;auto.
    
    unfold uninstall_safe in manifestx1.
    case_eq (uninstall_pre i s);intros;rewrite H in manifestx1;
    simpl in manifestx1;
    auto.
    assert (a<>i).
    unfold not;intros.
    rewrite H0 in xNotUninstallA.
    destruct xNotUninstallA.
    auto.
    rewrite<- dropSthElse in manifestx1;auto.
    
    unfold grant_safe in manifestx1; case_eq (grant_pre p i s);intros;rewrite H in manifestx1;auto.
    unfold grantAuto_safe in manifestx1; case_eq (grantAuto_pre p i s);intros;rewrite H in manifestx1;auto.
    unfold revoke_safe in manifestx1; case_eq (revoke_pre p i s);intros;rewrite H in manifestx1;auto.
    unfold revokegroup_safe in manifestx1; case_eq (revokegroup_pre i i0 s);intros;rewrite H in manifestx1;auto.
    auto.
    unfold read_safe in manifestx1; case_eq (read_pre i c u s);intros;rewrite H in manifestx1;auto.
    unfold write_safe in manifestx1; case_eq (write_pre i c u v s);intros;rewrite H in manifestx1;auto.
    unfold startActivity_safe in manifestx1; case_eq (startActivity_pre i i0 s);intros;rewrite H in manifestx1;auto.
    unfold startActivity_safe in manifestx1; case_eq (startActivity_pre i i0 s);intros;rewrite H in manifestx1;auto.
    unfold startService_safe in manifestx1; case_eq (startService_pre i i0 s);intros;rewrite H in manifestx1;auto.
    unfold sendBroadcast_safe in manifestx1; case_eq (sendBroadcast_pre i i0 o s);intros;rewrite H in manifestx1;auto.
    unfold sendBroadcast_safe in manifestx1; case_eq (sendBroadcast_pre i i0 o s);intros;rewrite H in manifestx1;auto.
    unfold sendStickyBroadcast_safe in manifestx1; case_eq (sendStickyBroadcast_pre i i0 s);intros;rewrite H in manifestx1;auto.
    unfold resolveIntent_safe in manifestx1; case_eq (resolveIntent_pre i i0 s);intros;rewrite H in manifestx1;auto.
    unfold receiveIntent_safe in manifestx1; case_eq (receiveIntent_pre i i0 i1 s);intros;rewrite H in manifestx1;auto.
    unfold receiveIntent_post in manifestx1.
    destruct (maybeIntentForAppCmp i i1 i0 s);auto. 
    unfold stop_safe in manifestx1; case_eq (stop_pre i s);intros;rewrite H in manifestx1;auto.
    unfold grantP_safe in manifestx1; case_eq (grantP_pre i c i0 u p s);intros;rewrite H in manifestx1;auto.
    unfold revokeDel_safe in manifestx1; case_eq (revokeDel_pre i c u p s);intros;rewrite H in manifestx1;auto.
    unfold call_safe in manifestx1; case_eq (call_pre i s0 s);intros;rewrite H in manifestx1;auto.
    unfold verifyOldApp_safe in manifestx1; case_eq (verifyOldApp_pre i s);intros;rewrite H in manifestx1;auto.
Qed.

Lemma sysImgSame : forall
        (x:Action)
        (s:System)
        (sValid:validstate s)
        (sysapp:SysImgApp)
(sysAppNew : In sysapp (systemImage (environment (system (step s x))))),
In sysapp (systemImage (environment s)).
Proof.
    intros.
    destruct x;simpl in sysAppNew.
    unfold install_safe in sysAppNew; case_eq (install_pre i m c l s);intros;rewrite H in sysAppNew;auto.
    unfold uninstall_safe in sysAppNew; case_eq (uninstall_pre i s);intros;rewrite H in sysAppNew;auto.
    unfold grant_safe in sysAppNew; case_eq (grant_pre p i s);intros;rewrite H in sysAppNew;auto.
    unfold grantAuto_safe in sysAppNew; case_eq (grantAuto_pre p i s);intros;rewrite H in sysAppNew;auto.
    unfold revoke_safe in sysAppNew; case_eq (revoke_pre p i s);intros;rewrite H in sysAppNew;auto.
    unfold revokegroup_safe in sysAppNew; case_eq (revokegroup_pre i i0 s);intros;rewrite H in sysAppNew;auto.
    auto.
    unfold read_safe in sysAppNew; case_eq (read_pre i c u s);intros;rewrite H in sysAppNew;auto.
    unfold write_safe in sysAppNew; case_eq (write_pre i c u v s);intros;rewrite H in sysAppNew;auto.
    unfold startActivity_safe in sysAppNew; case_eq (startActivity_pre i i0 s);intros;rewrite H in sysAppNew;auto.
    unfold startActivity_safe in sysAppNew; case_eq (startActivity_pre i i0 s);intros;rewrite H in sysAppNew;auto.
    unfold startService_safe in sysAppNew; case_eq (startService_pre i i0 s);intros;rewrite H in sysAppNew;auto.
    unfold sendBroadcast_safe in sysAppNew; case_eq (sendBroadcast_pre i i0 o s);intros;rewrite H in sysAppNew;auto.
    unfold sendBroadcast_safe in sysAppNew; case_eq (sendBroadcast_pre i i0 o s);intros;rewrite H in sysAppNew;auto.
    unfold sendStickyBroadcast_safe in sysAppNew; case_eq (sendStickyBroadcast_pre i i0 s);intros;rewrite H in sysAppNew;auto.
    unfold resolveIntent_safe in sysAppNew; case_eq (resolveIntent_pre i i0 s);intros;rewrite H in sysAppNew;auto.
    unfold receiveIntent_safe in sysAppNew; case_eq (receiveIntent_pre i i0 i1 s);intros;rewrite H in sysAppNew;auto.
    unfold receiveIntent_post in sysAppNew.
    destruct (maybeIntentForAppCmp i i1 i0 s);auto. 
    unfold stop_safe in sysAppNew; case_eq (stop_pre i s);intros;rewrite H in sysAppNew;auto.
    unfold grantP_safe in sysAppNew; case_eq (grantP_pre i c i0 u p s);intros;rewrite H in sysAppNew;auto.
    unfold revokeDel_safe in sysAppNew; case_eq (revokeDel_pre i c u p s);intros;rewrite H in sysAppNew;auto.
    unfold call_safe in sysAppNew; case_eq (call_pre i s0 s);intros;rewrite H in sysAppNew;auto.
    unfold verifyOldApp_safe in sysAppNew; case_eq (verifyOldApp_pre i s);intros;rewrite H in sysAppNew;auto.
Qed.

Lemma permAIsTheSame : forall
(p : Perm)
(x : Action)
(x0 : list Perm)
(a : idApp)
(s : System)
(sValid : validstate s)
(aWasInstalled : In a (apps (state s)) \/ (exists x0, In x0 (systemImage (environment s)) /\ idSI x0 = a))
(xNotUninstallA : x <> uninstall a)
(xNotGrantPA : x <> grant p a)
(xNotGrantAutoPA : x <> grantAuto p a)
(permsAIsx0 : map_apply idApp_eq (perms (state (system (step s x)))) a = Value idApp x0)
(pInx0 : In p x0),
(exists l0 : list Perm,
  map_apply idApp_eq (perms (state s)) a = Value idApp l0 /\ In p l0).
Proof.
    intros.
    destruct x;
    simpl in permsAIsx0.
    
    unfold install_safe in permsAIsx0.
    case_eq (install_pre i m c l s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0.
    exists x0;auto.
    exists x0.
    split;auto.
    rewrite overrideNotEq in permsAIsx0;auto.
    unfold install_pre in H.
    unfold not;intros.

    rewrite H0 in permsAIsx0.
    rewrite<- addAndApply with (indexeq := idApp_eq) (i:=a) (mp:= perms (state s)) in permsAIsx0.
    inversion permsAIsx0.
    rewrite<- H2 in *.
    inversion pInx0.

    unfold uninstall_safe in permsAIsx0.
    case_eq (uninstall_pre i s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0.
    exists x0;auto.
    unfold dropAppPerms in permsAIsx0.
    assert (a<>i).
    unfold not;intros.
    rewrite H0 in xNotUninstallA.
    destruct xNotUninstallA.
    auto.
    rewrite <-dropSthElse in permsAIsx0;auto.
    assert (exists l, map_apply idApp_eq (perms (state s)) a = Value idApp l).
    apply ifInAppsOrSysAppThenPerms;auto.
    destruct H1 as [l].
    remember (fun p0 : Perm => negb (InBool Perm Perm_eq p0 match map_apply idApp_eq (defPerms (environment s)) i with | Value _ l0 => l0 | Error _ _ => nil end)) as filterFun.
    exists l.
    split;auto.
    assert (map_apply idApp_eq (addAll idApp (list Perm) idApp_eq (map (fun key : idApp => (key, match map_apply idApp_eq (perms (state s)) key with | Value _ l => filter filterFun l | Error _ _ => nil end)) (map_getKeys (perms (state s)))) (perms (state s))) a = Value idApp (filter filterFun l) ).
    apply inAddAll.
    remember (fun pair : idApp * list Perm => if idApp_eq (fst pair) a then true else false) as f.
    remember (map (fun key : idApp => (key, match map_apply idApp_eq (perms (state s)) key with | Value _ l0 => filter filterFun l0 | Error _ _ => nil end)) (map_getKeys (perms (state s)))) as l2.
    assert (In (a, filter filterFun l) l2).
    rewrite Heql2.
    rewrite in_map_iff.
    exists a.
    rewrite H1.
    split;auto.
    rewrite <-(valueIffInGetKeys idApp_eq).
    rewrite H1.
    unfold is_Value;auto.
    apply permsCorrect;auto.
    assert (exists x,hd_error (filter f l2) = Some x /\ f x=true /\ In x l2).
    apply ifExistsFilterHdError.
    exists (a, filter filterFun l).
    rewrite filter_In.
    split;auto.
    rewrite Heqf.
    simpl.
    destruct idApp_eq;auto.
    destruct H3.
    destruct_conj H3.
    rewrite H4.
    destruct x.
    rewrite Heqf in H3.
    simpl in H3.
    destruct idApp_eq in H3.
    rewrite e in *.
    assert (l0 = filter filterFun l).
    rewrite Heql2 in H6.
    rewrite in_map_iff in H6.
    destruct H6.
    destruct H5.
    inversion H5.
    rewrite H8 in *.
    rewrite H1;auto.
    rewrite H5.
    auto.
    discriminate H3.
    rewrite H2 in permsAIsx0.
    inversion permsAIsx0.
    rewrite <-H4 in pInx0.
    rewrite filter_In in pInx0.
    destruct pInx0.
    auto.

    unfold grant_safe in permsAIsx0;
    case_eq (grant_pre p0 i s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0.
    exists x0;auto.
    unfold grantPermission in permsAIsx0.
    assert ( exists x, map_apply idApp_eq (perms (state s)) a=Value idApp x).
    apply ifInAppsOrSysAppThenPerms;auto.
    destruct H0 as [l].
    elim (classic (i=a));intros.
    rewrite H1 in *.
    rewrite H0 in permsAIsx0.
    exists l.
    rewrite <-addAndApply in permsAIsx0.
    inversion permsAIsx0.
    rewrite <-H3 in pInx0.
    inversion pInx0.
    rewrite H2 in xNotGrantPA.
    destruct xNotGrantPA.
    auto.
    split;auto.
    exists x0.
    destruct (map_apply idApp_eq (perms (state s)) i).
    rewrite overrideNotEq in permsAIsx0;auto.
    auto.

    unfold grantAuto_safe in permsAIsx0;
      case_eq (grantAuto_pre p0 i s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0.
    exists x0. auto.
    unfold grantPermission in permsAIsx0.
    assert ( exists x, map_apply idApp_eq (perms (state s)) a=Value idApp x).
    apply ifInAppsOrSysAppThenPerms;auto.
    destruct H0 as [l H0].
    destruct (idApp_eq i a).
    rewrite e in *.
    rewrite H0 in permsAIsx0.
    exists l.
    rewrite <-addAndApply in permsAIsx0.
    inversion permsAIsx0.
    rewrite <- H2 in pInx0.
    inversion pInx0.
    rewrite H1 in xNotGrantAutoPA.
    destruct xNotGrantAutoPA.
    auto.
    split;auto.
    exists x0.
    destruct (map_apply idApp_eq (perms (state s)) i).
    rewrite overrideNotEq in permsAIsx0;auto.
    auto.

    unfold revoke_safe in permsAIsx0;
    case_eq (revoke_pre p0 i s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0.
    exists x0;auto.
    unfold revokePermission in permsAIsx0.
    elim (classic (i=a));intros.
    rewrite H0 in *.
    assert ( exists x, map_apply idApp_eq (perms (state s)) a=Value idApp x).
    apply ifInAppsOrSysAppThenPerms;auto.
    destruct H1 as [l].
    rewrite H1 in permsAIsx0.
    rewrite <-addAndApply in permsAIsx0.
    inversion permsAIsx0.
    rewrite <-H3 in pInx0.
    rewrite <-removeSthElse in pInx0.
    destruct pInx0.
    exists l.
    auto.
    destruct (map_apply idApp_eq (perms (state s)) i).
    rewrite overrideNotEq in permsAIsx0;auto.
    exists x0;auto.
    exists x0;auto.

    unfold revokegroup_safe in permsAIsx0; case_eq (revokegroup_pre i i0 s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0.
    exists x0; auto.
    unfold revokeAllPermsOfGroup in permsAIsx0.
    assert ( exists x, map_apply idApp_eq (perms (state s)) a=Value idApp x).
    apply ifInAppsOrSysAppThenPerms;auto.
    destruct H0 as [l H0].
    destruct (idApp_eq i0 a).
    rewrite e in *.
    rewrite H0 in permsAIsx0.
    rewrite <- addAndApply in permsAIsx0.
    inversion permsAIsx0.
    exists l. split; auto.
    rewrite <- H2 in pInx0.
    apply inRemoveAll in pInx0.
    destruct pInx0. auto.
    destruct (map_apply idApp_eq (perms (state s)) i0).
    rewrite overrideNotEq in permsAIsx0.
    exists x0; auto. auto.
    exists x0; auto.

    exists x0;auto.
    unfold read_safe in permsAIsx0; case_eq (read_pre i c u s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold write_safe in permsAIsx0; case_eq (write_pre i c u v s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold startActivity_safe in permsAIsx0; case_eq (startActivity_pre i i0 s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold startActivity_safe in permsAIsx0; case_eq (startActivity_pre i i0 s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold startService_safe in permsAIsx0; case_eq (startService_pre i i0 s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold sendBroadcast_safe in permsAIsx0; case_eq (sendBroadcast_pre i i0 o s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold sendBroadcast_safe in permsAIsx0; case_eq (sendBroadcast_pre i i0 o s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold sendStickyBroadcast_safe in permsAIsx0; case_eq (sendStickyBroadcast_pre i i0 s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold resolveIntent_safe in permsAIsx0; case_eq (resolveIntent_pre i i0 s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold receiveIntent_safe in permsAIsx0; case_eq (receiveIntent_pre i i0 i1 s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold receiveIntent_post in permsAIsx0.
    destruct (maybeIntentForAppCmp i i1 i0 s);auto. 
    unfold stop_safe in permsAIsx0; case_eq (stop_pre i s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold grantP_safe in permsAIsx0; case_eq (grantP_pre i c i0 u p0 s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold revokeDel_safe in permsAIsx0; case_eq (revokeDel_pre i c u p0 s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    unfold call_safe in permsAIsx0; case_eq (call_pre i s0 s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.

    unfold verifyOldApp_safe in permsAIsx0; case_eq (verifyOldApp_pre i s);intros;rewrite H in permsAIsx0;simpl in permsAIsx0;exists x0;auto.
    destruct (idApp_eq i a).
    rewrite e in *.
    rewrite <- addAndApply in permsAIsx0.
    inversion permsAIsx0.
    rewrite <- H1 in pInx0. inversion pInx0.
    rewrite overrideNotEq in permsAIsx0; auto.
Qed.

Lemma defPermsSame : forall
        (x:Action)
        (a:idApp)
        (s:System)
        (sValid:validstate s)
        (aWasInstalled : In a (apps (state s)) \/ (exists x0, In x0 (systemImage (environment s)) /\ idSI x0 = a))
(xNotUninstallA : x <> uninstall a)
(x1 : list Perm)
(defpermsx1 : map_apply idApp_eq (defPerms (environment (system (step s x)))) a = Value idApp x1),
map_apply idApp_eq (defPerms (environment s)) a = Value idApp x1.
Proof.
    intros.
    destruct x;simpl in defpermsx1.
    
    unfold install_safe in defpermsx1.
    case_eq (install_pre i m c l s);intros;rewrite H in defpermsx1;
    simpl in defpermsx1;
    auto.
    assert (i<>a).
    unfold install_pre in H.
    unfold not;intros.
    rewrite H0 in H.
    assert (isAppInstalled a s).
    unfold isAppInstalled.
    auto.
    rewrite isAppInstalled_iff in H1.
    rewrite H1 in H.
    inversion H.
    rewrite overrideNotEq in defpermsx1;auto.
    
    unfold uninstall_safe in defpermsx1.
    case_eq (uninstall_pre i s);intros;rewrite H in defpermsx1;
    simpl in defpermsx1;
    auto.
    assert (a<>i).
    unfold not;intros.
    rewrite H0 in xNotUninstallA.
    destruct xNotUninstallA.
    auto.
    rewrite<- dropSthElse in defpermsx1;auto.
    
    unfold grant_safe in defpermsx1; case_eq (grant_pre p i s);intros;rewrite H in defpermsx1;auto.
    unfold grantAuto_safe in defpermsx1; case_eq (grantAuto_pre p i s);intros;rewrite H in defpermsx1;auto.
    unfold revoke_safe in defpermsx1; case_eq (revoke_pre p i s);intros;rewrite H in defpermsx1;auto.
    unfold revokegroup_safe in defpermsx1; case_eq (revokegroup_pre i i0 s);intros;rewrite H in defpermsx1;auto.
    auto.
    unfold read_safe in defpermsx1; case_eq (read_pre i c u s);intros;rewrite H in defpermsx1;auto.
    unfold write_safe in defpermsx1; case_eq (write_pre i c u v s);intros;rewrite H in defpermsx1;auto.
    unfold startActivity_safe in defpermsx1; case_eq (startActivity_pre i i0 s);intros;rewrite H in defpermsx1;auto.
    unfold startActivity_safe in defpermsx1; case_eq (startActivity_pre i i0 s);intros;rewrite H in defpermsx1;auto.
    unfold startService_safe in defpermsx1; case_eq (startService_pre i i0 s);intros;rewrite H in defpermsx1;auto.
    unfold sendBroadcast_safe in defpermsx1; case_eq (sendBroadcast_pre i i0 o s);intros;rewrite H in defpermsx1;auto.
    unfold sendBroadcast_safe in defpermsx1; case_eq (sendBroadcast_pre i i0 o s);intros;rewrite H in defpermsx1;auto.
    unfold sendStickyBroadcast_safe in defpermsx1; case_eq (sendStickyBroadcast_pre i i0 s);intros;rewrite H in defpermsx1;auto.
    unfold resolveIntent_safe in defpermsx1; case_eq (resolveIntent_pre i i0 s);intros;rewrite H in defpermsx1;auto.
    unfold receiveIntent_safe in defpermsx1; case_eq (receiveIntent_pre i i0 i1 s);intros;rewrite H in defpermsx1;auto.
    unfold receiveIntent_post in defpermsx1.
    destruct (maybeIntentForAppCmp i i1 i0 s);auto. 
    unfold stop_safe in defpermsx1; case_eq (stop_pre i s);intros;rewrite H in defpermsx1;auto.
    unfold grantP_safe in defpermsx1; case_eq (grantP_pre i c i0 u p s);intros;rewrite H in defpermsx1;auto.
    unfold revokeDel_safe in defpermsx1; case_eq (revokeDel_pre i c u p s);intros;rewrite H in defpermsx1;auto.
    unfold call_safe in defpermsx1; case_eq (call_pre i s0 s);intros;rewrite H in defpermsx1;auto.
    unfold verifyOldApp_safe in defpermsx1; case_eq (verifyOldApp_pre i s);intros;rewrite H in defpermsx1;auto.
Qed.



End TraceRelatedProperties.