(* En este archivo se demuestra la corrección de la acción grant*)
Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Export ListAuxFuns.
Require Import Classical.
Require Import Estado.
Require Import DefBasicas.
Require Import EqTheorems.
Require Import Semantica.
Require Import RuntimePermissions.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.
Require Import ValidStateLemmas.

Section Grant.

Lemma postGrantCorrect : forall (s:System) (a:idApp) (p:Perm), (pre (grant p a) s) -> validstate s -> post_grant p a s (grant_post p a s).
Proof.
    intros.
    unfold post_grant.
    simpl in H.
    unfold pre_grant in H;simpl in H.
    destruct H.
    
    split.
    destruct H.
    destruct H.
    assert (In a (apps (state s)) \/ (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a)).
    destruct H.
    left.
    apply (ifManifestThenInApps s H0 a x);auto.
    right.
    destruct H.
    destruct_conj H.
    exists x0;auto.
    assert (exists v, map_apply idApp_eq (perms (state s)) a = Value idApp v).
    apply (ifInAppsOrSysAppThenPerms);auto.
    destruct H4.
    unfold grantPerm.
    unfold grant_post;unfold grantPermission;simpl.
    rewrite H4.
    split;intros.
    elim (classic (a=a'));intros.
    
    exists (p::x0).
    split.
    rewrite H6.
    rewrite<- (addAndApply idApp_eq a' (p::x0) (perms (state s))).
    auto.
    rewrite H6 in H4.
    rewrite H4 in H5.
    assert (x0=lPerm).
    inversion H5.
    auto.
    intros.
    rewrite H7.
    apply in_cons.
    auto.
    
    exists lPerm.
    split.
    rewrite overrideNotEq; auto.
    intros.
    auto.
    
    split;intros.
    elim (classic (a=a'));intro.
    
    
    exists x0.
    split.
    rewrite H6 in H4.
    auto.
    intros.
    split;auto.
    rewrite H6 in H5.
    rewrite <-(addAndApply idApp_eq a' (p::x0) (perms (state s))) in H5.
    inversion H5.
    rewrite <-H10 in H7.
    inversion H7.
    auto.
    contradiction.
    
    exists lPerm'.
    rewrite overrideNotEq in H5.
    split;auto.
    intros;contradiction.
    auto.
    split.
    exists (p::x0).
    split.
    symmetry.
    apply addAndApply.
    apply in_eq.
    apply addPreservesCorrectness.
    apply permsCorrect;auto.
    
    repeat (split;auto).
Qed.

Lemma notPreGrantThenError : forall (s:System) (a:idApp) (p:Perm), ~(pre (grant p a) s) -> validstate s -> exists ec : ErrorCode, response (step s (grant p a)) = error ec /\ ErrorMsg s (grant p a) ec /\ s = system (step s (grant p a)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_grant in H.
    unfold grant_safe.
    unfold grant_pre.
    
    case_eq (negb (InBool idPerm idPerm_eq (idP p) (permsInUse a s)));intros.
    exists perm_not_in_use.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H1.
    invertBool H1.
    intro.
    apply H1.
    destruct H2.
    unfold InBool.
    rewrite existsb_exists.
    exists (idP p).
    unfold permsInUse.
    destruct H2.
    rewrite H2.
    destruct idPerm_eq;auto.


    case_eq (negb (InBool Perm Perm_eq p (getAllPerms s)));intros.
    exists no_such_perm.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H2.
    invertBool H2.
    intro;apply H2.
    unfold getAllPerms.
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    rewrite in_app_iff.
    split.
    destruct H3.
    left.
    apply isSysPermCorrect;auto.
    right.
    apply inUsrDefPermsIff;auto.
    destruct Perm_eq;auto.

    case_eq (InBool Perm Perm_eq p (grantedPermsForApp a s));intros.
    exists perm_already_granted.
    split;auto.
    split;auto.
    unfold InBool in H3.
    rewrite existsb_exists in H3.
    destruct H3.
    destruct H3.
    unfold grantedPermsForApp in H3.
    case_eq (map_apply idApp_eq (perms (state s)) a);intros; rewrite H5 in H3.
    exists l.
    destruct Perm_eq in H4.
    rewrite e;auto.
    discriminate H4.
    inversion H3.
    case_eq ((if permLevel_eq (pl p) dangerous then false else true));intros.
    exists perm_not_dangerous.
    split;auto.
    split;auto.
    destruct permLevel_eq in H4.
    discriminate H4.
    auto.
    case_eq (isSomethingBool idGrp (maybeGrp p));intros.
    exists perm_is_grouped.
    split;auto.
    split;auto.
    unfold isSomethingBool in H5.
    destruct (maybeGrp p).
    intro.
    discriminate H6.
    discriminate H5.

    destruct H.
    split.
    rewrite negb_false_iff in H1.
    unfold InBool in H1.
    rewrite existsb_exists in H1.
    destruct H1.
    destruct H.
    unfold permsInUse in H.

    unfold isManifestOfApp.
    case_eq (map_apply idApp_eq (manifest (environment s)) a);intros;rewrite H6 in *.
    exists m.
    destruct idPerm_eq in H1.
    rewrite e.
    split;auto.
    discriminate H1.

    case_eq ((map (fun sysapp : SysImgApp => use (manifestSI sysapp)) (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))));intros;rewrite H7 in *;simpl in H.
    destruct H.
    assert (In l (map (fun sysapp : SysImgApp => use (manifestSI sysapp)) (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s))))).
    rewrite H7.
    apply in_eq.
    rewrite in_map_iff in H8.
    destruct H8.
    destruct H8.
    exists (manifestSI x0).
    split.
    right.
    exists x0.
    rewrite filter_In in H9.
    destruct H9.
    destruct idApp_eq in H10.
    rewrite e;auto.
    discriminate H10.
    destruct idPerm_eq in H1.
    rewrite e.
    rewrite H8 in *.
    auto.
    discriminate H1.



    split.
    rewrite negb_false_iff in H2.
    unfold InBool in H2.
    rewrite existsb_exists in H2.
    destruct H2.
    destruct H.
    destruct Perm_eq in H2.
    rewrite e.
    unfold getAllPerms in H.
    rewrite in_app_iff in H.
    destruct H.
    left.
    apply isSysPermCorrect;auto.
    right.
    apply inUsrDefPermsIff;auto.
    discriminate H2.
    split.
    invertBool H3.
    intro;apply H3.
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    destruct H.
    destruct H.
    unfold grantedPermsForApp.
    rewrite H.
    destruct Perm_eq;auto.
    split.
    destruct permLevel_eq in H4.
    auto.
    discriminate H4.
    unfold isSomethingBool in H5.
    destruct (maybeGrp p).
    discriminate H5.
    auto.
Qed.
Lemma grantIsSound : forall (s:System) (a:idApp) (p:Perm),
        validstate s -> exec s (grant p a) (system (step s (grant p a))) (response (step s (grant p a))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (grant p a) s));intro.
    left.
    assert(grant_pre p a s = None).
    unfold grant_pre.
    destruct H0.
    
    assert (InBool idPerm idPerm_eq (idP p) (permsInUse a s) = true).
    unfold InBool.
    rewrite existsb_exists.
    exists (idP p).
    split.
    destruct H0.
    destruct H0.
    unfold permsInUse.
    destruct H0.
    rewrite H0.
    auto.
    case_eq (map_apply idApp_eq (manifest (environment s)) a);intros.
    apply ifManifestThenInApps in H3;auto.
    destruct H0.
    assert (~(In a (apps (state s)) /\ In x0 (systemImage (environment s)) /\ idSI x0 = a)).
    apply sysAppInApps;auto.
    destruct_conj H0.
    destruct H4;auto.
    destruct H0.
    destruct_conj H0.
    assert (In x0 (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))).
    rewrite filter_In.
    rewrite H0.
    destruct idApp_eq;auto.
    remember (fun sysapp : SysImgApp => use (manifestSI sysapp)) as theFun.
    remember (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s))) as theList.
    assert ((hd nil (map theFun theList)) = theFun (hd defaultSysApp theList )).
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists x0;auto.
    rewrite H7.
    rewrite HeqtheFun.
    assert ((hd defaultSysApp theList)=x0).
    rewrite HeqtheList in H5.
    assert (exists x0, In x0 (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))).
    exists x0;auto.
    apply ifExistsFilter with (dflt:=defaultSysApp) in H8.
    rewrite HeqtheList.
    remember (hd defaultSysApp (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))) as theHead.
    destruct H8.
    apply (notDupSysAppVS s);auto.
    rewrite H0 in *.
    destruct idApp_eq in H9;auto.
    discriminate H9.

    rewrite H8;rewrite H6;auto.




    destruct idPerm_eq.
    auto.
    auto.
    rewrite H2.
    assert (negb true=false).
    rewrite negb_false_iff;auto.
    rewrite H3.
    
    assert (InBool Perm Perm_eq p (getAllPerms s) = true).
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    split.
    destruct H1.
    unfold getAllPerms.
    apply in_app_iff.
    destruct H1.
    left.
    apply isSysPermCorrect;auto.
    right.
    unfold usrDefPerms.
    apply in_concat.
    unfold usrDefPerm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H1.
    exists x0.
    split.
    apply in_app_iff.
    left.
    apply inGetValuesBack.
    exists (map_apply idApp_eq (defPerms (environment s)) x).
    split.
    apply in_map_iff.
    exists x.
    split.
    auto.
    apply (ifDefPermsThenInApps s H x x0);auto.
    auto.
    auto.
    destruct H1.
    destruct H1.
    exists (defPermsSI x).
    split.
    apply in_app_iff.
    right.
    apply in_map_iff.
    exists x.
    split;auto.
    auto.
    destruct Perm_eq.
    auto.
    destruct n;auto.
    rewrite H4.
    assert (negb true=false).
    rewrite negb_false_iff;auto.
    rewrite H3.
    
    
    
    assert (InBool Perm Perm_eq p (grantedPermsForApp a s) <> true).
    unfold InBool.
    unfold not;intros.
    rewrite existsb_exists in H6.
    destruct H6.
    destruct H6.
    destruct H1.
    apply H8.
    unfold grantedPermsForApp in H6.
    case_eq (map_apply idApp_eq (perms (state s)) a);intros; rewrite H9 in H6.
    exists l.
    destruct Perm_eq in H7.
    rewrite<- e in H6.
    split;auto.
    discriminate H7.
    destruct H6.
    rewrite not_true_iff_false in H6.
    rewrite H6.
    destruct_conj H1.
    destruct permLevel_eq.
    unfold isSomethingBool.
    rewrite H10.
    auto.
    contradiction.
    
    
    unfold step;simpl.
    unfold grant_safe;simpl.
    rewrite H1;simpl.
    split;auto.
    split;auto.
    apply postGrantCorrect;auto.
    right.
    apply (notPreGrantThenError);auto.
Qed.
End Grant.
