(* En este archivo se demuestra la corrección de la acción install *)
Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Import Classical.
Require Import Estado.
Require Import EqTheorems.
Require Import DefBasicas.
Require Import Semantica.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.
Require Import MyList.
Require Import ListAuxFuns.
Require Import ValidStateLemmas.

Section Install.

Lemma postInstallCorrect : forall (s:System) (a:idApp) (m:Manifest) (c:Cert) (lRes: list res), (pre (install a m c lRes) s) -> validstate s -> post_install a m c lRes s (install_post a m c lRes s).
Proof.
    intros.
    unfold post_install.
    assert (~In a (apps (state s)) /\ ~(exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a)).
    simpl in H.
    unfold pre_install in H.
    destruct H.
    unfold isAppInstalled in H.
    apply notOrAndNot.
    auto.
    
    split. simpl. auto.

    split. 
 -  unfold initializePermLists;(repeat (split;intros));
    unfold install_post;simpl.
    destruct H1 as [noInApp H1].
    assert (a<>a').
    simpl in H.
    assert (statesConsistency s).
    destruct H0.
    destruct_conj H3.
    auto.
    destruct (H3 a).
    destruct H5.
    destruct H5.
    destruct H6.
    destruct H8.
    destruct H9.
    assert (~(exists l : list idGrp, map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp l)).
    intro.
    specialize (H10 H11).
    destruct H10; contradiction.
    intro.
    apply H11.
    rewrite H12.
    exists lGrp.
    auto.
-- rewrite <- H2.
   apply overrideNotEq. auto.
-- elim (classic (a=a'));intros.
   right; auto.
   left. simpl in H2.
   rewrite overrideNotEq in H2. auto. auto.
-- exists (map getGroupFromPerm
            (filter
              (fun p : Perm =>
                isPermNormal p && isSomethingBool idGrp (maybeGrp p))
             (use m))).
    split.
    rewrite <- addAndApply. auto.
    intros. destruct_conj H2.
    induction (use m).
    simpl in H3. destruct H3.
    assert (isPermNormal p && isSomethingBool idGrp (maybeGrp p) = true).
    unfold isPermNormal. rewrite H2.
    unfold isSomethingBool. rewrite H5. auto.
    destruct H3. rewrite H3.
    simpl. rewrite H4. simpl.
    left.
    unfold getGroupFromPerm.
    rewrite H5. auto.
    simpl.
    case_eq (isPermNormal a0 && isSomethingBool idGrp (maybeGrp a0)); intros.
    simpl. right. apply IHl. auto.
    apply IHl. auto.
--  apply addPreservesCorrectness.
    mapcorrect H0.

 -  destruct H1 as (H1, notExistsSysapp).
    split.
    unfold addManifest; split;intros.
    unfold install_post;simpl.
    assert (a<>a').
    simpl in H.
    assert (statesConsistency s).
    destruct H0.
    destruct_conj H3.
    auto.
    destruct (H3 a).
    destruct H4.
    assert (~(exists m0 : Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m0)).
    apply (contraReciproco (exists m0 : Manifest,
    map_apply idApp_eq (manifest (environment s)) a = Value idApp m0) (In a (apps (state s))) ).
    auto.
    auto.
    unfold not;intros.
    absurd (exists m0 : Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m0).
    auto.
    exists m'.
    rewrite H8.
    auto.
    rewrite<- H2.
    apply (overrideNotEq).
    auto.
    split;intros.
    elim (classic (a=a'));intros.
    right.
    auto.
    left.
    simpl in H2.
    rewrite overrideNotEq in H2.
    auto.
    auto.
    simpl.
    split.
    symmetry.
    apply (addAndApply).
    apply addPreservesCorrectness.
    mapcorrect H0.
    
    split.
    unfold addCert;split;intros.
    unfold install_post;simpl.
    assert (a<>a').
    simpl in H.
    assert (statesConsistency s).
    destruct H0.
    destruct_conj H3.
    auto.
    destruct (H3 a).
    destruct H5.
    destruct H5.
    assert (~(exists c0 : Cert, map_apply idApp_eq (cert (environment s)) a = Value idApp c0)).
    apply (contraReciproco (exists c0 : Cert,
    map_apply idApp_eq (cert (environment s)) a = Value idApp c0) (In a (apps (state s))) ).
    intros.
    auto.
    auto.
    unfold not;intros.
    absurd (exists c0 : Cert, map_apply idApp_eq (cert (environment s)) a = Value idApp c0).
    auto.
    exists c'.
    rewrite H9.
    auto.
    rewrite<- H2.
    apply (overrideNotEq).
    auto.
    split;intros.
    elim (classic (a=a'));intros.
    right.
    auto.
    left.
    simpl in H2.
    rewrite overrideNotEq in H2.
    auto.
    auto.
    split;simpl.
    symmetry.
    apply (addAndApply).
    apply addPreservesCorrectness.
    mapcorrect H0.
    
    split.
    unfold addDefPerms;split;intros.
    unfold install_post;simpl.
    assert (a<>a').
    simpl in H.
    assert (statesConsistency s).
    destruct H0.
    destruct_conj H3.
    auto.
    destruct (H3 a).
    destruct H5.
    destruct H6.
    destruct H6.
    assert (~(exists l : list Perm, map_apply idApp_eq (defPerms (environment s)) a = Value idApp l)).
    apply (contraReciproco (exists l : list Perm, map_apply idApp_eq (defPerms (environment s)) a = Value idApp l) (In a (apps (state s))) ).
    auto.
    auto.
    unfold not;intros.
    absurd (exists l : list Perm, map_apply idApp_eq (defPerms (environment s)) a = Value idApp l).
    auto.
    exists lPerm.
    rewrite H10.
    auto.
    rewrite<- H2.
    apply (overrideNotEq).
    auto.
    split;intros.
    elim (classic (a=a'));intros.
    right.
    auto.
    left.
    simpl in H2.
    rewrite overrideNotEq in H2.
    auto.
    auto.
    split;simpl.
    rewrite<- (addAndApply).
    exists (nonSystemUsrP m).
    split.
    auto.
    exact (nonSystemUsrPCorrect m).
    apply addPreservesCorrectness.
    mapcorrect H0.
    
    split.
    unfold addApp;split;intros.
    unfold install_post;simpl.
    right.
    auto.
    split;intros.
    elim (classic (a=a'));intros.
    right.
    auto.
    left.
    unfold install_post in H2;simpl in H2.
    destruct H2.
    destruct H3;auto.
    auto.
    unfold install_post;simpl.
    left.
    auto.
    
    split.
    unfold install_post.
    unfold addRes;split;intros;simpl.
    assert (a<>a').
    simpl in H.
    assert (resContAppInst s).
    destruct H0.
    destruct_conj H3.
    auto.
    destruct (H3 a' r v).
    auto.
    unfold not;intros.
    apply H1.
    rewrite H5.
    auto.
    unfold not;intros.
    apply notExistsSysapp.
    rewrite H5.
    auto.
    unfold addNewResCont.
    rewrite<- H2.
    apply notInAddAll.
    unfold not;intros.
    rewrite in_map_iff in H4.
    destruct H4.
    destruct H4.
    apply H3.
    rewrite in_map_iff in H5.
    destruct H5.
    destruct H5.
    rewrite <-H5 in H4.
    simpl in H4.
    inversion H4.
    auto.
    unfold addNewResCont.
    split;intros.
    elim (classic (a=a'));intros.
    right.
    rewrite <-H3 in H2.
    assert (~(is_Value (map_apply rescontdomeq (resCont (state s)) (a,r)))).
    apply (notInstalledNoResCont);auto.
    unfold isAppInstalled.
    apply andNotNotOr.
    auto.
    assert (exists n, nth_error (map (fun r0 : res => (a, r0, initVal)) lRes) n = Some ((a,r),v)).
    apply (notValueThenOverriden (idApp*res) Val rescontdomeq (map (fun r0 : res => (a, r0, initVal)) lRes) v (resCont (state s))); auto.
    destruct H5.
    apply nth_error_In in H5.
    rewrite in_map_iff in H5.
    destruct H5.
    destruct H5.
    inversion H5.
    rewrite H8 in H6.
    auto.
    left.
    rewrite<- H2.
    symmetry.
    apply notInAddAll.
    unfold not;intros.
    rewrite in_map_iff in H4.
    destruct H4.
    destruct H4.
    apply H3.
    rewrite in_map_iff in H5.
    destruct H5.
    destruct H5.
    rewrite<-H5 in H4.
    simpl in H4.
    inversion H4.
    auto.
    split.
    intros;apply inAddAll.
    remember (fun pair : idApp * res * Val => if rescontdomeq (fst pair) (a, r) then true else false) as theFun.
    remember (map (fun r0 : res => (a, r0, initVal)) lRes) as theList.
    assert (exists x,hd_error (filter theFun theList) = Some x /\ theFun x=true /\ In x theList).
    apply ifExistsFilterHdError.
    exists (a,r,initVal).
    rewrite filter_In.
    split.
    rewrite HeqtheList.
    rewrite in_map_iff.
    exists r.
    auto.
    rewrite HeqtheFun.
    simpl.
    destruct rescontdomeq;auto.
    destruct H3.
    destruct_conj H3.
    assert (x=(a,r,initVal)).
    rewrite HeqtheFun in H3.
    rewrite HeqtheList in H6.
    rewrite in_map_iff in H6.
    destruct rescontdomeq in H3.
    destruct H6.
    destruct H5.
    rewrite <-H5 in e.
    simpl in e.
    inversion e.
    rewrite H8 in H5.
    auto.
    discriminate H3.
    rewrite H5 in H4.
    auto.
    apply addAllPreservesCorrectness.
    mapcorrect H0.
    
    
    split.
    unfold initializePermLists;(repeat (split;intros));
    unfold install_post;simpl.
    assert (a<>a').
    simpl in H.
    assert (statesConsistency s).
    destruct H0.
    destruct_conj H3.
    auto.
    destruct (H3 a).
    destruct H5.
    destruct H5.
    destruct H6.
    destruct H8.
    destruct H8.
    assert (~(exists l : list Perm, map_apply idApp_eq (perms (state s)) a = Value idApp l)).
    intro.
    specialize(H10 H11).
    destruct H10;contradiction.
    intro.
    apply H11.
    rewrite H12.
    exists lPerm.
    auto.
    rewrite<- H2.
    apply (overrideNotEq).
    auto.
    elim (classic (a=a'));intros.
    right.
    split.
    auto.
    unfold install_post in H2;simpl in H2.
    rewrite H3 in H2.
    assert (map_apply idApp_eq (map_add idApp_eq (perms (state s)) a' nil) a'= Value idApp nil).
    symmetry.
    apply (addAndApply).
    rewrite H4 in H2.
    inversion H2.
    auto.
    left.
    simpl in H2.
    rewrite overrideNotEq in H2.
    auto.
    auto.
    rewrite<-(addAndApply).
    auto.

    apply addPreservesCorrectness.
    mapcorrect H0.
    
(*
    simpl in H.
    assert (statesConsistency s).
    destruct H0.
    destruct_conj H3.
    auto.
    destruct (H3 a).
    destruct H5.
    destruct H5.
    destruct H6.
    destruct H8.
    destruct H9.
    assert (~(exists l : list idGrp, map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp l)).
    intro.
    specialize (H10 H11).
    destruct H10;contradiction.
    intro.
    apply H11.
    rewrite H12.
    exists lGrp.
    auto.
    
    rewrite<- H2.
    apply (overrideNotEq).
    auto.
    elim (classic (a=a'));intros.
    right.
    split.
    auto.
    unfold install_post in H2;simpl in H2.
    rewrite H3 in H2.
    assert (map_apply idApp_eq (map_add idApp_eq (grantedPermGroups (state s)) a' nil) a'= Value idApp nil).
    symmetry.
    apply (addAndApply).
    rewrite H4 in H2.
    inversion H2.
    auto.
    left.
    simpl in H2.
    rewrite overrideNotEq in H2.
    auto.
    auto.
    rewrite<-(addAndApply).
    auto.
    apply addPreservesCorrectness.
    mapcorrect H0.
    apply addPreservesCorrectness.
    mapcorrect H0.
*)
    repeat (split; unfold install_post;simpl;auto).
    
Qed.

Lemma notPreInstallThenError : forall (s:System) (a:idApp) (m:Manifest) (c:Cert) (lRes: list res), ~(pre (install a m c lRes) s) -> validstate s -> exists ec : ErrorCode, response (step s (install a m c lRes)) = error ec /\ ErrorMsg s (install a m c lRes) ec /\ s = system (step s (install a m c lRes)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_install in H.
    unfold install_safe.
    unfold install_pre.
    case_eq (isAppInstalledBool a s);intros.
    simpl;exists app_already_installed.
    apply isAppInstalled_iff in H1;auto.
    dontcare (has_duplicates idCmp idCmp_eq (map getCmpId (cmp m))).
    exists duplicated_cmp_id;auto.
    dontcare (has_duplicates idPerm idPerm_eq (map idP (usrP m))).
    exists duplicated_perm_id;auto.
    dontcare (existsb (fun c0 : Cmp => cmpIdInStateBool c0 s) (cmp m)).
    exists cmp_already_defined.
    split;auto.
    split;auto.
    rewrite existsb_exists in H4.
    destruct H4.
    destruct H4.
    unfold not;intros.
    specialize (H6 x H4).
    rewrite cmpIdInStateBoolCorrect in H6;auto.
    rewrite H6 in H5.
    discriminate H5.

    case_eq (negb (authPermsBool m s));intros.
    exists perm_already_defined.
    split;auto.
    split;auto.
    unfold not;intros.
    rewrite authPermsBoolCorrect in H6;auto.
    rewrite H6 in H5.
    rewrite negb_true_iff in H5.
    discriminate H5.

    dontcare (anyDefinesIntentFilterIncorrectly (cmp m)).
    exists faulty_intent_filter.
    split;auto.
    split;auto.
    unfold anyDefinesIntentFilterIncorrectly in H6.
    rewrite existsb_exists in H6.
    destruct H6.
    destruct H6.
    unfold not;intros.
    specialize (H8 x H6).
    rewrite definesIntentFilterCorrectlyBoolCorrect in H8.
    unfold definesIntentFilterIncorrectly in H7.
    rewrite H8 in H7.
    rewrite negb_true_iff in H7.
    discriminate H7.


    destruct H.
    split.
    invertBool H1.
    rewrite isAppInstalled_iff;auto.

    split;auto.
    split;auto.

    split.
    invertBool H4.
    rewrite existsb_exists in H4.
    apply NNPP.
    intro.
    apply not_all_ex_not in H.
    apply H4.
    destruct H.
    exists x.
    apply notImpliesAndNot in H.
    destruct H.
    split;auto.
    rewrite cmpIdInStateBoolCorrect in H7;auto.
    invertBool H7.
    apply NNPP in H7.
    auto.

    split.
    rewrite negb_false_iff in H5.
    apply authPermsBoolCorrect;auto.
    unfold anyDefinesIntentFilterIncorrectly in H6.
    invertBool H6.
    rewrite existsb_exists in H6.
    apply NNPP.
    intro.
    apply not_all_ex_not in H.
    apply H6.
    destruct H.
    exists x.
    apply notImpliesAndNot in H.
    destruct H.
    split;auto.
    rewrite definesIntentFilterCorrectlyBoolCorrect in H7;auto.
    invertBool H7.
    apply NNPP in H7.
    unfold definesIntentFilterIncorrectly.
    rewrite H7.
    auto.
Qed.

Lemma installIsSound : forall (s:System) (a:idApp) (m:Manifest) (c:Cert) (lRes: list res),
    validstate s -> exec s (install a m  c lRes) (system (step s (install a m  c lRes))) (response (step s (install a m  c lRes))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (install a m c lRes) s));intro.
    left.
    assert(install_pre a m c lRes s = None).
    unfold install_pre.
    assert (isAppInstalledBool a s = false).
    destruct H0.
    assert (isAppInstalledBool a s <> true).
    rewrite <- (isAppInstalled_iff).
    auto.
    rewrite not_true_iff_false in H2.
    auto.
    
    rewrite H1.
    destruct H0.
    destruct H2.
    rewrite H2.
    
    assert (existsb (fun c0 : Cmp => cmpIdInStateBool c0 s) (cmp m)=false).
    destruct H3 as [nodupperm H3].
    destruct H3.
    rewrite <-not_true_iff_false.
    unfold not;intro.
    rewrite existsb_exists in H5.
    destruct H5.
    destruct H5.
    specialize (H3 x).
    specialize (H3 H5).
    assert (cmpIdInStateBool x s=false).
    apply cmpIdInStateBoolCorrect; auto.
    rewrite H6 in H7.
    discriminate H7.
    
    destruct H3 as [nodupperm H3].
    rewrite nodupperm.
    
    rewrite H4.
    
    destruct H3.
    destruct H5.
    assert (authPermsBool m s=true).
    apply (authPermsBoolCorrect); auto.
    
     rewrite H7.
    assert (negb true=false).
    rewrite negb_false_iff.
     auto.
    rewrite H8.
    
    assert (anyDefinesIntentFilterIncorrectly (cmp m)=false).
    unfold anyDefinesIntentFilterIncorrectly.
    rewrite <-not_true_iff_false.
    unfold not;intros.
    rewrite existsb_exists in H9.
    destruct H9.
    destruct H9.
    specialize (H6 x H9).
    unfold definesIntentFilterIncorrectly in H10.
    rewrite negb_true_iff in H10.
    assert (definesIntentFilterCorrectlyBool x = true).
    apply definesIntentFilterCorrectlyBoolCorrect.
    auto.
    rewrite H10 in H11.
    discriminate H11.
    rewrite H9.
    auto.
    split.
    unfold step.
    unfold install_safe.
    rewrite H1.
    auto.
    split;auto.
    unfold post.
    unfold step.
    unfold install_safe.
    rewrite H1.
    simpl.
    apply postInstallCorrect; auto.
    right.
    apply notPreInstallThenError;auto.
 Qed.

End Install.
