(* En este archivo se demuestra la corrección de la acción grantGroup *)
Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Export ListAuxFuns.
Require Import Classical.
Require Import Estado.
Require Import DefBasicas.
Require Import Semantica.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.
Require Import ValidStateLemmas.

Section GrantGroup.

Lemma postGrantGroupCorrect : forall (s:System) (a:idApp) (p:idGrp), (pre (grantPermGroup p a) s) -> validstate s -> post_grantGroup p a s (grantgroup_post p a s).
Proof.
    intros.
    unfold post_grantGroup.
    simpl in H.
    unfold pre_grantGroup in H;simpl in H.
    destruct H.
    
    split.
    destruct H1.
    destruct H1.
    destruct H1.
    assert (exists v, map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp v).
    assert (In a (apps (state s)) \/ (exists sysapp:SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a)).
    destruct H1.
    left.
    apply (ifManifestThenInApps s H0 a x);auto.
    right.
    destruct H1.
    destruct_conj H1.
    exists x1;auto.
    apply (ifInAppsOrSysAppThenGrantedGroups);auto.
    destruct H3.
    unfold Semantica.grantPermGroup.
    unfold grantgroup_post;unfold grantPermissionGroup;simpl.
    rewrite H3.
    split;intros.
    elim (classic (a=a'));intros.
    
    exists (p::x1).
    split.
    rewrite H5.
    rewrite<- (addAndApply idApp_eq a' (p::x1) (grantedPermGroups (state s))).
    auto.
    rewrite H5 in H3.
    rewrite H3 in H4.
    assert (x1=lGrp).
    inversion H4.
    auto.
    intros.
    rewrite H6.
    apply in_cons.
    auto.
    
    exists lGrp.
    split.
    rewrite overrideNotEq; auto.
    intros.
    auto.
    
    split;intros.
    elim (classic (a=a'));intro.
    
    
    exists x1.
    split.
    rewrite H5 in H3.
    auto.
    intros.
    split;auto.
    rewrite H5 in H4.
    rewrite <-(addAndApply idApp_eq a' (p::x1) (grantedPermGroups (state s))) in H4.
    inversion H4.
    rewrite <-H9 in H6.
    inversion H6.
    auto.
    contradiction.
    
    exists lGrp'.
    rewrite overrideNotEq in H4.
    split;auto.
    intros;contradiction.
    auto.
    split.
    exists (p::x1).
    split.
    symmetry.
    apply addAndApply.
    apply in_eq.
    apply addPreservesCorrectness.
    apply grantedPermGroupsCorrect;auto.
    
    repeat (split;auto).
Qed.

Lemma notPreGrantGroupThenError : forall (s:System) (a:idApp) (p:idGrp), ~(pre (grantPermGroup p a) s) -> validstate s -> exists ec : ErrorCode, response (step s (grantPermGroup p a)) = error ec /\ ErrorMsg s (grantPermGroup p a) ec /\ s = system (step s (grantPermGroup p a)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_grantGroup in H.
    unfold grantgroup_safe.
    unfold grantgroup_pre.
    case_eq (map_apply idApp_eq (grantedPermGroups (state s)) a);intros.
    dontcare (InBool idGrp idGrp_eq p l).
    exists group_already_granted.
    split;auto.
    split;auto.
    unfold InBool in H2.
    rewrite existsb_exists in H2.
    destruct H2.
    destruct H2.
    destruct idGrp_eq in H3.
    rewrite e.
    exists l;auto.
    discriminate H3.
    case_eq (existsb (fun p0 : Perm => match maybeGrp p0 with | Some g' => if idGrp_eq g' p then true else false | None => false end) (filter (fun p0 : Perm => match pl p0 with | dangerous => true | normal => false | signature => false | signatureOrSys => false end) (filter (fun p0 : Perm => InBool idPerm idPerm_eq (idP p0) (permsInUse a s)) (getAllPerms s))));intros.
    destruct H.
    rewrite existsb_exists in H3.
    destruct H3.
    rewrite filter_In in H.
    destruct H.
    rewrite filter_In in H.
    destruct H.
    destruct H.
    unfold InBool in H5.
    rewrite existsb_exists in H5.
    destruct H5.
    destruct H5.
    unfold permsInUse in H5.
    case_eq (map_apply idApp_eq (manifest (environment s)) a);intros;rewrite H7 in H5.
    split.
    rewrite H1.
    invertBool H2.
    intro.
    apply H2.
    destruct H8.
    destruct H8.
    inversion H8.
    rewrite H11 in *.
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    destruct idGrp_eq;auto.


    exists m.
    exists x.
    split.
    unfold RuntimePermissions.isManifestOfApp.
    left;auto.
    destruct idPerm_eq in H6.
    rewrite e.
    split;auto.
    split.
    unfold getAllPerms in H.
    rewrite in_app_iff in H.
    destruct H.
    left.
    apply isSysPermCorrect;auto.
    right.
    apply inUsrDefPermsIff ;auto.
    split.
    case_eq (maybeGrp x);intros;rewrite H8 in H3.
    destruct idGrp_eq in H3.
    rewrite e0.
    auto.
    discriminate H3.
    discriminate H3.
    case_eq (pl x);intros;rewrite H8 in H4;auto;discriminate H4.
    discriminate H6.

    split.
    intro.
    destruct H8.
    destruct H8.
    rewrite H1 in H8.
    inversion H8.
    rewrite H11 in *.
    unfold InBool in H2.
    rewrite<- not_true_iff_false in H2.
    destruct H2.
    rewrite existsb_exists.
    exists p.
    destruct idGrp_eq;auto.
    unfold RuntimePermissions.isManifestOfApp.


    case_eq ((map (fun sysapp : SysImgApp => use (manifestSI sysapp)) (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))));intros;rewrite H8 in *;simpl in H5.
    destruct H5.
    assert (In l0 (map (fun sysapp : SysImgApp => use (manifestSI sysapp)) (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s))))).
    rewrite H8.
    apply in_eq.
    rewrite in_map_iff in H9.
    destruct H9.
    destruct H9.
    exists (manifestSI x1).
    exists x.
    split.
    right.
    exists x1.
    rewrite filter_In in H10.
    destruct H10.
    destruct idApp_eq in H11.
    rewrite e;auto.
    discriminate H11.
    destruct idPerm_eq in H6.
    rewrite e.
    rewrite H9 in *.
    split;auto.
    split.
    unfold getAllPerms in H.
    rewrite in_app_iff in H.
    destruct H.
    left.
    apply isSysPermCorrect;auto.
    right.
    apply inUsrDefPermsIff;auto.
    split.
    destruct (maybeGrp x).
    destruct idGrp_eq in H3.
    rewrite e0;auto.
    discriminate H3.
    discriminate H3.
    destruct (pl x);auto; discriminate H4.
    discriminate H6.



    exists group_not_in_use.
    split;auto.
    split;auto.
    invertBool H3.
    intro;apply H3.
    destruct H4.
    destruct H4.
    rewrite existsb_exists.
    exists x0.
    destruct_conj H4.
    split.
    rewrite filter_In.
    rewrite H9.
    split;auto.
    rewrite filter_In.
    split.
    unfold getAllPerms.
    rewrite in_app_iff.
    destruct H6.
    left.
    apply isSysPermCorrect;auto.
    right.
    apply inUsrDefPermsIff ;auto.
    unfold InBool.
    rewrite existsb_exists.
    exists (idP x0).
    unfold permsInUse.
    rewrite H5.
    destruct idPerm_eq;auto.
    rewrite H7.
    destruct idGrp_eq;auto.
    exists no_such_app.
    split;auto.
    split;auto.
    intro.
    apply ifInAppsThenGrantedGroups in H2;auto.
    destruct H2.
    rewrite H2 in H1.
    discriminate H1.
Qed.


Lemma grantgroupIsSound : forall (s:System) (a:idApp) (p:idGrp),
        validstate s -> exec s (grantPermGroup p a) (system (step s (grantPermGroup p a))) (response (step s (grantPermGroup p a))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (grantPermGroup p a) s));intro.
    left.
    assert(grantgroup_pre p a s = None).
    unfold grantgroup_pre.
    destruct H0.
    
    destruct H1.
    destruct H1.
    destruct H1.


    unfold RuntimePermissions.isManifestOfApp in H1.

    assert (exists l : list idGrp, map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp l).
    apply (ifInAppsOrSysAppThenGrantedGroups);auto.
    destruct H1.
    left.
    apply ifManifestThenInApps with (m:=x);auto.
    right.
    destruct H1.
    destruct_conj H1.
    exists x1;auto.
    destruct H3.
    rewrite H3.




    assert (InBool idGrp idGrp_eq p x1=false).
    unfold InBool.
    rewrite <-not_true_iff_false.
    unfold not;intros.
    rewrite existsb_exists in H4.
    destruct H4.
    destruct H4.
    apply H0.
    exists x1.
    destruct idGrp_eq in H5.
    rewrite e.
    auto.
    discriminate H5.
    rewrite H4.
    
    assert (existsb (fun p0 : Perm => match maybeGrp p0 with | Some g' => if idGrp_eq g' p then true else false | None => false end) (filter (fun p0 : Perm => match pl p0 with | dangerous => true | normal => false | signature => false | signatureOrSys => false end) (filter (fun p0 : Perm => InBool idPerm idPerm_eq (idP p0) (permsInUse a s)) (getAllPerms s)))=true).
    
    rewrite existsb_exists.
    exists x0.
    destruct H2.
    destruct H5.
    destruct H6.
    split.
    rewrite filter_In.
    split.
    rewrite filter_In.
    split.
    
    unfold getAllPerms.
    rewrite in_app_iff.
    destruct H5.
    left.
    apply isSysPermCorrect.
    auto.
    right.
    unfold usrDefPerms.
    rewrite in_concat.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H5.
    exists x3.
    split;auto.
    rewrite in_app_iff.
    left.
    apply inGetValuesBack.
    exists (map_apply idApp_eq (defPerms (environment s)) x2).
    split;auto.
    rewrite H5.
    rewrite in_map_iff.
    exists x2.
    split;auto.
    apply (ifDefPermsThenInApps s H x2 x3);auto.
    
    destruct H5.
    destruct H5.
    exists (defPermsSI x2).
    split;auto.
    rewrite in_app_iff.
    right.
    rewrite in_map_iff.
    exists x2.
    split;auto.
    
    unfold InBool.
    rewrite existsb_exists.
    exists (idP x0).
    split.
    unfold permsInUse.
    destruct H1.
    rewrite H1.
    auto.



    case_eq (map_apply idApp_eq (manifest (environment s)) a);intros.
    apply ifManifestThenInApps in H8;auto.
    destruct H1.
    assert (~(In a (apps (state s)) /\ In x2 (systemImage (environment s)) /\ idSI x2 = a)).
    apply sysAppInApps;auto.
    destruct_conj H1.
    destruct H9;auto.
    destruct H1.
    destruct_conj H1.
    assert (In x2 (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))).
    rewrite filter_In.
    rewrite H1.
    destruct idApp_eq;auto.
    remember (fun sysapp : SysImgApp => use (manifestSI sysapp)) as theFun.
    remember (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s))) as theList.
    assert ((hd nil (map theFun theList)) = theFun (hd defaultSysApp theList )).
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists x2;auto.
    rewrite H12.
    rewrite HeqtheFun.
    assert ((hd defaultSysApp theList)=x2).
    rewrite HeqtheList in H10.
    assert (exists x0, In x0 (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))).
    exists x2;auto.
    apply ifExistsFilter with (dflt:=defaultSysApp) in H13.
    rewrite HeqtheList.
    remember (hd defaultSysApp (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))) as theHead.
    destruct H13.
    apply (notDupSysAppVS s);auto.
    rewrite H1 in *.
    destruct idApp_eq in H14;auto.
    discriminate H14.

    rewrite H13;rewrite H11;auto.





    destruct idPerm_eq.
    auto.
    destruct n.
    auto.
    rewrite H7;auto.
    rewrite H6;auto.
    destruct idGrp_eq.
    auto.
    destruct n.
    auto.
    rewrite H5.
    auto.
    
    unfold step;simpl.
    unfold grantgroup_safe;simpl.
    rewrite H1;simpl.
    split;auto.
    split;auto.
    apply postGrantGroupCorrect;auto.
    right.
    apply notPreGrantGroupThenError;auto.
    
Qed.
End GrantGroup.
