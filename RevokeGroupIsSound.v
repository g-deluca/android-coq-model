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

Section RevokeGroup.

Lemma postRevokeGroupCorrect : forall (s:System) (a:idApp) (p:idGrp), (pre (revokePermGroup p a) s) -> validstate s -> post_revokeGroup p a s (revokegroup_post p a s).
Proof.
    intros.
    unfold post_revokeGroup.
    split. simpl; auto.
    simpl in H.
    unfold pre_revokeGroup in H;simpl in H.
    destruct H.
    
    split.
    destruct H.
    unfold Semantica.revokePermGroup.
    unfold revokegroup_post;unfold revokePermissionGroup;simpl.
    rewrite H.
    split;intros.
    elim (classic (a=a'));intros.
    exists x.
    
    split.
    rewrite<- H3.
    auto.
    intros.
    rewrite<- H3 in H2.
    rewrite <-(addAndApply idApp_eq a (remove idGrp_eq p x) (grantedPermGroups (state s))) in H2.
    inversion H2.
    rewrite<- H6 in H4.
    apply removeSthElse in H4.
    destruct H4.
    auto.
    
    exists lGrp'.
    split.
    rewrite overrideNotEq in H2.
    auto.
    auto.
    intros.
    auto.
    
    
    split;intros.
    elim (classic (a=a'));intros.
    exists (remove idGrp_eq p x).
    split.
    rewrite H3.
    symmetry.
    apply addAndApply.
    intros.
    split;auto.
    symmetry.
    apply (notInRemove idGrp x g' p idGrp_eq ).
    rewrite H3 in H.
    rewrite H in H2.
    inversion H2.
    auto.
    auto.
    
    
    exists lGrp.
    split.
    rewrite overrideNotEq.
    auto.
    auto.
    intros.
    contradiction.
    split.
    exists (remove idGrp_eq p x).
    split.
    symmetry.
    apply addAndApply.
    rewrite <-removeSthElse.
    unfold not;intros.
    destruct H2.
    apply H2;auto.
    apply addPreservesCorrectness.
    apply grantedPermGroupsCorrect;auto.

    split.
  - unfold revokegroup_post. unfold revokeGroupedPerms; simpl.
    assert (exists l : list Perm,
             map_apply idApp_eq (perms (state s)) a = Value idApp l).
    destructVS H0.
    destructSC statesConsistencyVS a.
    destruct H.
    destruct grantedPermGroupsSC. clear H1.
    assert (exists l : list idGrp,
        map_apply idApp_eq (grantedPermGroups (state s)) a = Value idApp l).
    exists x; auto.
    apply H2 in H1.
    apply permsSC in H1. auto.
    repeat split.
 -- intros.
    elim (classic (a=a'));intros.
    rewrite <- H3. destruct H1 as [lPerm H1].
    exists lPerm. split; auto.
    intros. unfold revokeAllPermsOfGroup in H2; rewrite H1 in H2.
    rewrite <- H3 in H2.
    rewrite <- addAndApply in H2.
    inversion H2. clear H2.
    rewrite <- H6 in H4. clear H6.
    induction (getPermsOfGroup p a s).
    simpl in H4. auto.
    simpl in H4. apply removeSthElse in H4.
    destruct H4. apply IHl. auto.

    exists lPerm'. destruct H1 as [lPerm H1].
    unfold revokeAllPermsOfGroup in H2. rewrite H1 in H2.
    split.
    apply (overrideNotEq idApp_eq (MyList.removeAll EqTheorems.Perm_eq (getPermsOfGroup p a s) lPerm) (perms (state s))) in H3.
    rewrite <- H3. auto.
    intros; auto.
 -- intros.
    elim (classic (a=a'));intros.
    unfold revokeAllPermsOfGroup.
    rewrite H3. clear H1. rewrite H2.
    exists (MyList.removeAll EqTheorems.Perm_eq (getPermsOfGroup p a' s) lPerm).
    split.
    rewrite <- addAndApply. auto.
    intros. split; auto.

    assert (In p' (getPermsOfGroup p a' s)).
    specialize (notInRemoveAll Perm (getPermsOfGroup p a' s) lPerm p' EqTheorems.Perm_eq H1 H4).
    intros; auto.

    apply (ifInPermsOfGroupThenSome p' p a' s).
    auto.
    exists lPerm. split.
    destruct H1.
    unfold revokeAllPermsOfGroup.
    rewrite H1.
    rewrite overrideNotEq.
    auto. auto.
    intros. contradiction.
 -- destruct H1 as [lPerm H1].
    unfold revokeAllPermsOfGroup. rewrite H1.
    exists (MyList.removeAll EqTheorems.Perm_eq (getPermsOfGroup p a s) lPerm).
    split.

    rewrite <- addAndApply. auto.
    intros. unfold not. intros.
    apply inRemoveAll in H3.
    destruct H3.

    assert (In p0 (getPermsOfGroup p a s)).
    unfold getPermsOfGroup. unfold grantedPermsForApp.
    rewrite H1. clear H1.
    induction lPerm.
    intros. inversion H3.
    simpl in *.
    destruct H3.
    rewrite <- H1 in H2. rewrite H2.
    destruct (idGrp_eq p p).
    simpl. left. auto.
    contradiction.
    apply IHlPerm in H1.
    case_eq (maybeGrp a0); intros.
    simpl. destruct (idGrp_eq p i).
    simpl. right. auto. auto. auto.

    contradiction.
 -- unfold revokeAllPermsOfGroup.
    destruct H1. rewrite H1.
    apply addPreservesCorrectness.
    apply permsCorrect;auto.

  - repeat (split;auto).
Qed.

Lemma notPreRevokeGroupThenError : forall (s:System) (a:idApp) (p:idGrp), ~(pre (revokePermGroup p a) s) -> validstate s -> exists ec : ErrorCode, response (step s (revokePermGroup p a)) = error ec /\ ErrorMsg s (revokePermGroup p a) ec /\ s = system (step s (revokePermGroup p a)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_revokeGroup in H.
    exists group_wasnt_granted.
    assert (revokegroup_pre p a s=Some group_wasnt_granted).
    unfold revokegroup_pre.
    case_eq (map_apply idApp_eq (grantedPermGroups (state s)) a);intros.
    assert (InBool idGrp idGrp_eq p l=false).
    rewrite<- not_true_iff_false.
    unfold not;intros.
    apply H.
    unfold InBool in H2.
    rewrite existsb_exists in H2.
    destruct H2.
    destruct H2.
    unfold grantedPermsForApp in H2.
    destruct idGrp_eq in H3.
    exists l.
    rewrite e.
    auto.
    discriminate H3.
    rewrite H2;auto.
    auto.
    unfold revokegroup_safe.
    rewrite H1.
    simpl.
    auto.
Qed.

Lemma revokegroupIsSound : forall (s:System) (a:idApp) (p:idGrp),
        validstate s -> exec s (revokePermGroup p a) (system (step s (revokePermGroup p a))) (response (step s (revokePermGroup p a))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (revokePermGroup p a) s));intro.
    left.
    assert(revokegroup_pre p a s = None).
    unfold revokegroup_pre.
    destruct H0.
    
    destruct H0.
    rewrite H0.
    assert (InBool idGrp idGrp_eq p x = true).
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    split.
    auto.
    destruct idGrp_eq.
    auto.
    destruct n.
    auto.
    rewrite H2.
    auto.
    
    unfold step;simpl.
    unfold revokegroup_safe;simpl.
    rewrite H1;simpl.
    split;auto.
    split;auto.
    apply postRevokeGroupCorrect;auto.
    right.
    apply notPreRevokeGroupThenError;auto.
    
Qed.
End RevokeGroup.
