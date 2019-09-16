(* En este archivo se demuestra la corrección de la acción uninstall *)
Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Export ListAuxFuns.
Require Import Classical.
Require Import Estado.
Require Import DefBasicas.
Require Import EqTheorems.
Require Import Semantica.
Require Import Operaciones.
Require Import RuntimePermissions.
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.
Require Import ValidStateLemmas.

Section Uninstall.


Lemma postUninstallCorrect : forall (s:System) (a:idApp), (pre (uninstall a) s) -> validstate s -> post_uninstall a s (uninstall_post a s).
Proof.
    intros.
    unfold post_uninstall.
    simpl in H.
    unfold pre_uninstall in H;simpl in H.
    destruct H.
    unfold uninstall_post;simpl.
    
    split.
    unfold removeApp.
    unfold removeManifest.
    unfold removeCert.
    simpl.
    split.
    intros.
    assert (a'<>a /\ In a' (apps (state s))).
    rewrite<- removeSthElse in H2.
    auto.
    destruct H3.
    auto.
    split;intros.
    elim (classic (a'=a));intros.
    right;auto.
    left.
    apply removeSthElse;auto.
    split;intros.
    apply remove_In.
    split;intros.
    split;intros.
    apply (valueDropValue idApp_eq a a'); auto.
    split;intros.
    elim (classic (a=a'));intros.
    right;auto.
    left.
    apply valueDropValue.
    split;auto.
    split.
    apply valueDropNotValue.
    apply dropPreservesCorrectness.
    mapcorrect H0.
    
    
    split;intros.
    apply (valueDropValue idApp_eq a a'); auto.
    split;intros.
    elim (classic (a=a'));intros.
    right;auto.
    left.
    apply (valueDropValue idApp_eq a a'); auto.
    split.
    apply valueDropNotValue.
    apply dropPreservesCorrectness.
    mapcorrect H0.
    
    split.
    unfold revokePerms.
    unfold uninstall_post;simpl.
    unfold dropAppPerms.
    assert (exists lPerm:(list Perm), map_apply idApp_eq (defPerms (environment s)) a = Value idApp lPerm) as exlperm.
    apply (ifInAppThenDefPerms s H0 a);auto.
    destruct exlperm as [lPerm exlperm].
    rewrite exlperm.
    split;intros.
    apply (valueDropValue) in H2.
    destruct H2.
    remember (map (fun key : idApp => (key, match map_apply idApp_eq (perms (state s)) key with | Value l => filter (fun p : Perm => negb (InBool Perm Perm_eq p lPerm)) l | Error _ => nil end)) (map_getKeys (perms (state s)))) as indexAndVals.
    elim (classic (In a' (map (fun pair=>fst pair) indexAndVals)));intros.
    assert (In a' (map_getKeys (perms (state s)))).
    rewrite in_map_iff in H4.
    destruct H4.
    destruct x.
    destruct H4.
    simpl in H4.
    rewrite HeqindexAndVals in H5.
    rewrite in_map_iff in H5.
    destruct H5.
    destruct H5.
    inversion H5.
    rewrite H8 in *.
    rewrite H4 in *;auto.
    rewrite <-(valueIffInGetKeys idApp_eq) in H5.
    unfold is_Value in H5.
    case_eq (map_apply idApp_eq (perms (state s)) a');intros.
    exists l;auto.
    rewrite H6 in H5.
    destruct H5.
    apply permsCorrect;auto.
    rewrite notInAddAll in H2.
    exists lPerm';auto.
    auto.
    
    split;intros.
    elim (classic (a=a'));intros.
    right;auto.
    left.
    exists ( filter (fun p : Perm => negb (InBool Perm Perm_eq p lPerm)) lPerm0).
    split.
    rewrite<- (dropSthElse).
    apply inAddAll;auto.
    remember (fun p : Perm => negb (InBool Perm Perm_eq p lPerm)) as dasFun.
    remember (fun pair : idApp * list Perm => if idApp_eq (fst pair) a' then true else false) as filterFun.
    remember (map (fun key : idApp => (key, match map_apply idApp_eq (perms (state s)) key with | Value l => filter dasFun l | Error _ => nil end)) (map_getKeys (perms (state s)))) as theList.
    assert (In (a', filter dasFun lPerm0) (filter filterFun theList)).
    rewrite filter_In.
    split.
    rewrite HeqtheList.
    rewrite in_map_iff.
    exists a'.
    split.
    rewrite H2;auto.
    rewrite <-(valueIffInGetKeys idApp_eq);auto.
    rewrite H2.
    unfold is_Value;auto.
    apply permsCorrect;auto.
    rewrite HeqfilterFun.
    simpl.
    destruct idApp_eq;auto.
    assert (exists x,hd_error (filter filterFun theList) = Some x /\ filterFun x=true /\ In x theList).
    apply ifExistsFilterHdError.
    exists (a',filter dasFun lPerm0);auto.
    destruct H5.
    destruct_conj H5.
    assert (x=(a',filter dasFun lPerm0)).
    destruct x.
    rewrite HeqfilterFun in H5.
    simpl in H5.
    destruct idApp_eq in H5.
    rewrite e in *.
    rewrite HeqtheList in H8.
    rewrite in_map_iff in H8.
    destruct H8.
    destruct H7.
    inversion H7.
    rewrite H2 in *.
    auto.
    discriminate H5.
    rewrite <-H7;auto.
    auto.
    intros.
    inversion H4.
    split;intros.
    destruct H5.
    rewrite filter_In.
    split;auto.
    rewrite negb_true_iff.
    rewrite <-not_true_iff_false.
    unfold not;intros.
    apply H7.
    unfold InBool in H8.
    rewrite existsb_exists in H8.
    destruct H8.
    destruct H8.
    destruct Perm_eq in H9.
    rewrite e.
    auto.
    discriminate H9.
    rewrite filter_In in H5.
    destruct H5.
    split;auto.
    rewrite negb_true_iff in H7.
    rewrite <-not_true_iff_false in H7.
    unfold not;intros.
    apply H7.
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    split;auto.
    destruct Perm_eq;auto.
    split.
    apply valueDropNotValue.
    apply dropPreservesCorrectness.
    apply addAllPreservesCorrectness.
    apply permsCorrect;auto.
    
    split.
    unfold revokePermGroups.
    unfold uninstall_post;simpl.
    split;intros.
    apply (valueDropValue idApp_eq a a'); auto.
    split;intros.
    elim (classic (a=a'));intros.
    right;auto.
    left.
    apply (valueDropValue idApp_eq a a'); auto.
    split.
    apply valueDropNotValue.
    apply dropPreservesCorrectness.
    mapcorrect H0.
    
    split.
    unfold removeDefPerms.
    split;intros.
    apply (valueDropValue idApp_eq a a'); auto.
    split;intros.
    elim (classic (a=a'));intros.
    right;auto.
    left.
    apply (valueDropValue idApp_eq a a'); auto.
    split.
    apply valueDropNotValue.
    apply dropPreservesCorrectness.
    mapcorrect H0.
    
    split.
    unfold removeRes;simpl.
    unfold dropAllRes.
    split;intros.
    assert ( map_apply rescontdomeq (resCont (state s)) (a', r) = Value (idApp * res) v /\ ~(In (a',r) (filter (fun pair : idApp * res => if idApp_eq a (fst pair) then true else false) (map_getKeys (resCont (state s)))))).
    apply valueDropThenValue.
    auto.
    destruct H3.
    auto.
    split;intros.
    elim (classic (a'=a));intros.
    right;auto.
    left.
    apply valueDropThenValue.
    split;auto.
    unfold not;intros.
    rewrite filter_In in H4.
    destruct H4.
    simpl in H5.
    apply H3.
    destruct idApp_eq in H5.
    auto.
    discriminate H5.
    split;intros.
    elim (classic (In (a,r) (filter (fun pair : idApp * res => if idApp_eq a (fst pair) then true else false) (map_getKeys (resCont (state s))))));intros.
    apply valueDropAllNotValue.
    auto.
    assert (map_apply rescontdomeq (dropAll (idApp * res) Val rescontdomeq (filter (fun pair : idApp * res => if idApp_eq a (fst pair) then true else false) (map_getKeys (resCont (state s)))) (resCont (state s))) (a, r)= map_apply rescontdomeq (resCont (state s)) (a,r)).
    apply dropNotIn;auto.
    rewrite H3.
    unfold not;intros.
    apply H2.
    rewrite filter_In.
    simpl.
    split.
    unfold map_getKeys.
    rewrite in_map_iff.
    unfold is_Value in H4.
    case_eq (map_apply rescontdomeq (resCont (state s)) (a, r));intros.
    rewrite valueIffExists in H5.
    exists ({| item_index := (a, r); item_info := v |}).
    simpl.
    auto.
    apply resContCorrect;auto.
    rewrite H5 in H4.
    inversion H4.
    destruct idApp_eq;auto.
    apply dropAllPreservesCorrectness.
    mapcorrect H0.
    
    
    split.
    unfold revokeOtherTPerm;simpl.
    unfold dropAllTPerms.
    split;intros.
    rewrite valueDropThenValue in H2.
    destruct H2.
    auto.
    split;intros.
    elim (classic (exists m : Manifest, isManifestOfApp a m s /\ In (cmpCP cp) (cmp m)));intros.
    right;auto.
    left.
    rewrite valueDropThenValue.
    split;auto.
    unfold not;intros.
    apply H3.
    rewrite filter_In in H4.
    destruct H4.
    simpl in H5.
    unfold InBool in H5.
    rewrite existsb_exists in H5.
    destruct H5.
    destruct H5.
    unfold getCProviders in H5.
    rewrite filter_In in H5.
    destruct H5.
    assert (inApp x a s).
    apply getAllCmpInstalledInApp;auto.
    split;auto.
    unfold isAppInstalled.
    left;auto.
    unfold inApp in H8.
    destruct H8.
    exists x0.
    destruct H8.
    unfold isManifestOfApp.
    destruct Cmp_eq in H6.
    rewrite e.
    auto.
    discriminate H6.
    split;intros.
    
    
    elim (classic (In (ic,cp,u) (filter (fun tuple3 : iCmp * CProvider * uri => InBool Cmp Cmp_eq (cmpCP (snd3 iCmp CProvider uri tuple3)) (getCProviders a s)) (map_getKeys (delTPerms (state s))))));intros.
    apply valueDropAllNotValue.
    auto.
    assert (map_apply deltpermsdomeq (dropAll (iCmp * CProvider * uri) PType deltpermsdomeq (filter (fun tuple3 : iCmp * CProvider * uri => InBool Cmp Cmp_eq (cmpCP (snd3 iCmp CProvider uri tuple3)) (getCProviders a s)) (map_getKeys (delTPerms (state s)))) (delTPerms (state s))) (ic, cp, u) = map_apply deltpermsdomeq (delTPerms (state s)) (ic,cp,u)).
    apply dropNotIn;auto.
    rewrite H4.
    unfold not;intros.
    apply H3.
    rewrite filter_In.
    simpl.
    split.
    unfold map_getKeys.
    rewrite in_map_iff.
    unfold is_Value in H5.
    case_eq (map_apply deltpermsdomeq (delTPerms (state s)) (ic, cp, u));intros.
    rewrite valueIffExists in H6.
    exists {| item_index := (ic, cp, u); item_info := p |}.
    simpl.
    auto.
    apply delTPermsCorrect;auto.
    rewrite H6 in H5.
    inversion H5.
    unfold InBool.
    rewrite existsb_exists.
    exists (cmpCP cp).
    split.
    unfold getCProviders.
    rewrite filter_In.
    split.
    apply inAppGetAllCmp;auto.
    simpl;auto.
    destruct Cmp_eq;auto.
    apply dropAllPreservesCorrectness.
    mapcorrect H0.
    
    
    
    split;intros.
    
    unfold revokePPerm;simpl.
    unfold dropAllPPerms.
    split;intros.
    
    
    rewrite valueDropThenValue in H2.
    destruct H2.
    auto.
    split;intros.
    elim (classic (a'=a));intros.
    right.
    left;auto.
    elim (classic (exists m : Manifest, isManifestOfApp a m s /\ In (cmpCP cp) (cmp m)));intros.
    right;auto.
    left.
    rewrite valueDropThenValue.
    split;auto.
    unfold not;intros.
    rewrite filter_In in H5.
    destruct H5.
    simpl in H6.
    destruct idApp_eq in H6.
    contradiction.
    unfold InBool in H6.
    rewrite existsb_exists in H6.
    destruct H6.
    destruct H6.
    unfold getCProviders in H6.
    rewrite filter_In in H6.
    destruct H6.
    assert (inApp x a s).
    apply getAllCmpInstalledInApp;auto.
    split;auto.
    unfold isAppInstalled.
    left;auto.
    unfold inApp in H9.
    destruct H9.
    apply H4.
    exists x0.
    destruct H9.
    unfold isManifestOfApp.
    destruct Cmp_eq in H7.
    rewrite e.
    auto.
    discriminate H7.
    
    split;intros.
    
    
    elim (classic (In (a,cp,u) (filter (fun tuple3 : idApp * CProvider * uri => if idApp_eq (fst3 idApp CProvider uri tuple3) a then true else InBool Cmp Cmp_eq (cmpCP (snd3 idApp CProvider uri tuple3)) (getCProviders a s)) (map_getKeys (delPPerms (state s))))));intros.
    apply valueDropAllNotValue.
    auto.
    assert (map_apply delppermsdomeq (dropAll (idApp * CProvider * uri) PType delppermsdomeq (filter (fun tuple3 : idApp * CProvider * uri => if idApp_eq (fst3 idApp CProvider uri tuple3) a then true else InBool Cmp Cmp_eq (cmpCP (snd3 idApp CProvider uri tuple3)) (getCProviders a s)) (map_getKeys (delPPerms (state s)))) (delPPerms (state s))) (a, cp, u) = map_apply delppermsdomeq (delPPerms (state s)) (a,cp,u)).
    apply dropNotIn;auto.
    rewrite H3.
    unfold not;intros.
    apply H2.
    rewrite filter_In.
    simpl.
    split.
    unfold map_getKeys.
    rewrite in_map_iff.
    unfold is_Value in H4.
    case_eq (map_apply delppermsdomeq (delPPerms (state s)) (a, cp, u));intros.
    rewrite valueIffExists in H5.
    exists {| item_index := (a, cp, u); item_info := p |}.
    simpl.
    auto.
    apply delPPermsCorrect;auto.
    rewrite H5 in H4.
    inversion H4.
    destruct idApp_eq.
    auto.
    absurd (a<>a); auto.
    split;intros.
    
    
    elim (classic (In (a',cp,u) (filter (fun tuple3 : idApp * CProvider * uri => if idApp_eq (fst3 idApp CProvider uri tuple3) a then true else InBool Cmp Cmp_eq (cmpCP (snd3 idApp CProvider uri tuple3)) (getCProviders a s)) (map_getKeys (delPPerms (state s))))));intros.
    apply valueDropAllNotValue.
    auto.
    assert (map_apply delppermsdomeq (dropAll (idApp * CProvider * uri) PType delppermsdomeq (filter (fun tuple3 : idApp * CProvider * uri => if idApp_eq (fst3 idApp CProvider uri tuple3) a then true else InBool Cmp Cmp_eq (cmpCP (snd3 idApp CProvider uri tuple3)) (getCProviders a s)) (map_getKeys (delPPerms (state s)))) (delPPerms (state s))) (a', cp, u) = map_apply delppermsdomeq (delPPerms (state s)) (a',cp,u)).
    apply dropNotIn;auto.
    rewrite H4.
    unfold not;intros.
    apply H3.
    rewrite filter_In.
    simpl.
    split.
    unfold map_getKeys.
    rewrite in_map_iff.
    unfold is_Value in H5.
    case_eq (map_apply delppermsdomeq (delPPerms (state s)) (a', cp, u));intros.
    rewrite valueIffExists in H6.
    exists {| item_index := (a', cp, u); item_info := p |}.
    simpl.
    auto.
    apply delPPermsCorrect;auto.
    rewrite H6 in H5.
    inversion H5.
    destruct idApp_eq.
    auto.
    unfold InBool.
    rewrite existsb_exists.
    exists (cmpCP cp).
    split.
    unfold getCProviders.
    rewrite filter_In.
    split.
    apply inAppGetAllCmp;auto.
    simpl;auto.
    destruct Cmp_eq;auto.
    apply dropAllPreservesCorrectness.
    mapcorrect H0.
    
    split;auto.
Qed.

Lemma notPreUninstallThenError : forall (s:System) (a:idApp), ~(pre (uninstall a) s) -> validstate s -> exists ec : ErrorCode, response (step s (uninstall a)) = error ec /\ ErrorMsg s (uninstall a) ec /\ s = system (step s (uninstall a)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_uninstall in H.
    unfold uninstall_safe.
    unfold uninstall_pre.
    case_eq (negb (InBool idApp idApp_eq a (apps (state s))));intros.
    exists no_such_app.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H1.
    invertBool H1.
    intro.
    apply H1.
    unfold InBool.
    rewrite existsb_exists.
    exists a.
    destruct idApp_eq;auto.

    case_eq (isAnyCmpRunning a s);intros.
    exists app_is_running.
    split;auto.
    split;auto.
    invertBool H2.
    intro.
    apply H2.
    apply isAnyCmpRunningCorrect;auto.

    destruct H.
    rewrite negb_false_iff in H1.
    unfold InBool in H1.
    rewrite existsb_exists in H1.
    destruct H1.
    destruct H.
    destruct idApp_eq in H1.
    rewrite <- e in H.
    split;auto.
    unfold isAnyCmpRunning in H2.
    case_eq (map_apply idApp_eq (manifest (environment s)) a);intros.
    rewrite H3 in H2.
    invertBool H2.
    intro.
    apply H2.
    rewrite existsb_exists.
    exists c.
    split.
    unfold inApp in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    rewrite H5 in H3.
    inversion H3.
    rewrite <-H8;auto.
    destruct H5.
    destruct_conj H5.
    absurd (In a (apps (state s)) /\ In x1 (systemImage (environment s)) /\ idSI x1 = a).
    apply sysAppInApps;auto.
    split;auto.
    unfold isCmpRunning.
    unfold InBool.
    rewrite existsb_exists.
    exists (getCmpId c).
    split.
    rewrite in_map_iff.
    exists c.
    split;auto.
    unfold getRunningCmps.
    apply inGetValuesBack.
    exists (Value iCmp c).
    split;auto.
    rewrite in_map_iff.
    exists ic.
    split;auto.
    rewrite <-(valueIffInGetKeys iCmp_eq).
    unfold is_Value.
    rewrite H4.
    auto.
    apply runningCorrect;auto.
    destruct idCmp_eq;auto.
    apply ifInAppsThenManifest in H;auto.
    destruct H.
    rewrite H in H3.
    discriminate H3.
    discriminate H1.
Qed.
Lemma uninstallIsSound : forall (s:System) (a:idApp),
        validstate s -> exec s (uninstall a) (system (step s (uninstall a))) (response (step s (uninstall a))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (uninstall a) s));intro.
    left.
    assert(uninstall_pre a s = None).
    unfold uninstall_pre.
    destruct H0.
    assert (InBool idApp idApp_eq a (apps (state s)) = true).
    unfold InBool.
    rewrite existsb_exists.
    exists a.
    split;auto.
    destruct idApp_eq;auto.
    rewrite H2.
    assert (negb true=false).
    rewrite negb_false_iff;auto.
    rewrite H3.
    assert (isAnyCmpRunning a s=false).
    apply isAnyCmpRunningCorrect.
    auto.
    auto.
    rewrite H4;auto.
    
    unfold step;simpl.
    unfold uninstall_safe;simpl.
    rewrite H1;simpl.
    split;auto.
    split;auto.
    apply postUninstallCorrect;auto.
    right.
    apply notPreUninstallThenError;auto.
    
Qed.

End Uninstall.
