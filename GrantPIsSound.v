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
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.
Require Import ValidStateLemmas.

Section GrantP.

Lemma grantPCorrect : forall (s:System) (ic:iCmp) (cp:CProvider) (a:idApp) (u:uri) (pt:PType) (sValid: validstate s),
    (pre (grantP ic cp a u pt) s) -> post_grantP ic cp a u pt s (grantP_post ic cp a u pt s).
Proof.
    intros.
    unfold post_grantP.
    split. simpl; auto.
    simpl in H.
    unfold pre_grantP in H;simpl in H.
    unfold grantP_post; simpl.
    destruct_conj H.
    unfold addDelPPerm.
    split;intros.
    split;intros.
    destruct_conj H4.
    rewrite<- H5,<-H4,<-H7 in *.
    rewrite H2.
    symmetry.
    assert (ptplus pt pt' = ptplus pt' pt).
    apply ptplus_commutes.
    rewrite H6.
    apply addAndApply.
    
    rewrite<- H2.
    apply overrideNotEq.
    unfold not;intros.
    apply H4.
    inversion H5.
    auto.
    split;intros.
    split;intros.
    destruct_conj H4.
    rewrite<- H5,<-H4,<-H7 in *.
    case_eq ( map_apply delppermsdomeq (delPPerms (state s)) (a, cp, u));intros; rewrite H6 in H2; rewrite<- addAndApply in H2; inversion H2.
    rewrite H9.
    assert (ptplus pt p = ptplus p pt).
    apply ptplus_commutes.
    auto.
    rewrite H8.
    auto.
    auto.
    
    case_eq ( map_apply delppermsdomeq (delPPerms (state s)) (a, cp, u));intros; rewrite H5 in H2.
    rewrite<- H2.
    symmetry.
    apply overrideNotEq.
    unfold not;intros.
    apply H4.
    inversion H6.
    auto.
    
    rewrite<- H2.
    symmetry.
    apply overrideNotEq.
    unfold not;intros.
    apply H4.
    inversion H6.
    auto.
    
    split;intros.
    case_eq ( map_apply delppermsdomeq (delPPerms (state s)) (a, cp, u));intros; rewrite<- addAndApply; auto.
    split.
    apply addPreservesCorrectness.
    apply delPPermsCorrect;auto.
    
    repeat (split;auto).
Qed.

Lemma notPreGrantPThenError : forall (s:System) (a:idApp) (ic:iCmp) (cp:CProvider) (u:uri) (pt:PType), ~(pre (grantP ic cp a u pt) s) -> validstate s -> exists ec : ErrorCode, response (step s (grantP ic cp a u pt)) = error ec /\ ErrorMsg s (grantP ic cp a u pt) ec /\ s = system (step s (grantP ic cp a u pt)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_grantP in H.
    unfold grantP_safe.
    unfold grantP_pre.
    case_eq (negb (canGrantBool cp u s));intros.
    exists CProvider_not_grantable.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H1.
    invertBool H1.
    intro;apply H1.
    apply canGrantCorrect;auto.

    case_eq (negb (existsResBool cp u s));intros.
    exists no_such_res.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H2.
    invertBool H2.
    intro;apply H2.
    apply existsRes_iff;auto.

    case_eq (negb (isAppInstalledBool a s));intros.
    exists no_such_app.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H3.
    invertBool H3.
    intro;apply H3.
    apply isAppInstalled_iff;auto.
    
    case_eq (map_apply iCmp_eq (running (state s)) ic);intros.
    unfold canReadBool.
    unfold canWriteBool.

    rewrite negb_false_iff in H1,H2,H3.
    apply canGrantCorrect in H1;auto.
    apply existsRes_iff in H2;auto.
    apply isAppInstalled_iff in H3;auto.


    destruct pt.
    case_eq (negb (canDoThisBool c cp s readE || delPermsBool c cp u Read s));intros.
    exists not_enough_permissions.
    split;auto.
    split;auto.
    exists c.
    split;auto.
    rewrite negb_true_iff in H5.
    invertBool H5.
    unfold canRead.
    intro;apply H5.
    rewrite orb_true_iff.
    destruct H6.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.

    destruct H.
    split;auto.
    split;auto.
    split;auto.
    exists c.
    split;auto.
    rewrite negb_false_iff in H5.
    rewrite orb_true_iff in H5.
    destruct H5.
    unfold canRead.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.

    case_eq (negb (canDoThisBool c cp s writeE || delPermsBool c cp u Write s));intros.
    exists not_enough_permissions.
    split;auto.
    split;auto.
    exists c.
    split;auto.
    rewrite negb_true_iff in H5.
    invertBool H5.
    unfold canWrite.
    intro;apply H5.
    rewrite orb_true_iff.
    destruct H6.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.

    destruct H.
    split;auto.
    split;auto.
    split;auto.
    exists c.
    split;auto.
    rewrite negb_false_iff in H5.
    rewrite orb_true_iff in H5.
    destruct H5.
    unfold canWrite.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    
    
    case_eq (negb (canDoThisBool c cp s readE || delPermsBool c cp u Read s) || negb (canDoThisBool c cp s writeE || delPermsBool c cp u Write s));intros.
    exists not_enough_permissions.
    split;auto.
    split;auto.
    exists c.
    split;auto.
    invertBool H5.
    intro;apply H5.

    rewrite <-negb_andb.
    rewrite negb_false_iff.
    rewrite andb_true_iff.
    destruct H6.
    split;rewrite orb_true_iff.
    unfold canRead in H6.
    destruct H6.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    unfold canWrite in H7.
    destruct H7.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    destruct H.
    split;auto.
    split;auto.
    split;auto.
    exists c.
    split;auto.
    rewrite orb_false_iff in H5.
    destruct H5.
    rewrite negb_false_iff in H,H5.
    rewrite orb_true_iff in H,H5.
    split.
    destruct H.
    left.
    unfold canRead.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    destruct H5.
    left.
    unfold canWrite.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.

    exists instance_not_running.
    split;auto.
Qed.


Lemma grantPIsSound :  forall (s:System) (ic:iCmp) (cp:CProvider) (a:idApp) (u:uri) (pt:PType) (sValid: validstate s),
        exec s (grantP ic cp a u pt) (system (step s (grantP ic cp a u pt))) (response (step s (grantP ic cp a u pt))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (grantP ic cp a u pt) s));intro.
    left.
    simpl.
    assert(grantP_pre ic cp a u pt s = None).
    unfold grantP_pre.
    destruct H.
    destruct_conj H0.
    assert (negb (canGrantBool cp u s)=false).
    rewrite negb_false_iff.
    apply canGrantCorrect;auto.
    rewrite H2.
    assert (negb (existsResBool cp u s)=false).
    rewrite negb_false_iff.
    apply existsRes_iff;auto.
    rewrite H4.
    assert (negb (isAppInstalledBool a s)=false).
    rewrite negb_false_iff.
    apply isAppInstalled_iff;auto.
    rewrite H5.
    destruct H3.
    destruct H3.
    rewrite H3.
    unfold canRead in H6.
    unfold canWrite in H6.
    unfold canReadBool.
    unfold canWriteBool.
    destruct pt.
    
    assert (negb (canDoThisBool x cp s readE || delPermsBool x cp u Read s)=false).
    rewrite negb_false_iff.
    destruct H6.
    assert (canDoThisBool x cp s readE = true).
    apply canDoThisBoolCorrect;auto.
    rewrite H7.
    auto.
    assert (delPermsBool x cp u Read s = true).
    apply delPermsBoolCorrect;auto.
    rewrite H7.
    apply orb_true_r.
    rewrite H7.
    auto.
    
    assert (negb (canDoThisBool x cp s writeE || delPermsBool x cp u Write s)=false).
    rewrite negb_false_iff.
    destruct H6.
    assert (canDoThisBool x cp s writeE = true).
    apply canDoThisBoolCorrect;auto.
    rewrite H7.
    auto.
    assert (delPermsBool x cp u Write s = true).
    apply delPermsBoolCorrect;auto.
    rewrite H7.
    apply orb_true_r.
    rewrite H7.
    auto.
    
    destruct H6.
    
    
    assert (negb (canDoThisBool x cp s readE || delPermsBool x cp u Read s)=false).
    rewrite negb_false_iff.
    destruct H6.
    assert (canDoThisBool x cp s readE = true).
    apply canDoThisBoolCorrect;auto.
    rewrite H8.
    auto.
    assert (delPermsBool x cp u Read s = true).
    apply delPermsBoolCorrect;auto.
    rewrite H8.
    apply orb_true_r.
    rewrite H8.
    
    assert (negb (canDoThisBool x cp s writeE || delPermsBool x cp u Write s)=false).
    rewrite negb_false_iff.
    destruct H7.
    assert (canDoThisBool x cp s writeE = true).
    apply canDoThisBoolCorrect;auto.
    rewrite H9.
    auto.
    assert (delPermsBool x cp u Write s = true).
    apply delPermsBoolCorrect;auto.
    rewrite H9.
    apply orb_true_r.
    rewrite H9.
    auto.
    
    unfold grantP_safe;simpl.
    rewrite H0;simpl.
    split;auto.
    split;auto.
    apply grantPCorrect;auto.
    right.
    apply (notPreGrantPThenError);auto.
    
Qed.
End GrantP.
