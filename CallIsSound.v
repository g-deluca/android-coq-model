(* In this file we demonstrate the soundness of the call operation *)
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
Require Import RuntimePermissions.
Require Import ValidStateLemmas.

Section Call.

Lemma callCorrect : forall (s:System) (ic:iCmp) (sac:SACall) (sValid: validstate s),
    (pre (call ic sac) s) -> post_call ic sac s (call_post ic sac s).
Proof.
    intros.
    unfold post_call.
    unfold call_post; simpl.
    auto.
Qed.

Lemma notPreCallThenError : forall (s:System) (ic:iCmp) (sac:SACall), ~(pre (call  ic sac) s) -> validstate s -> exists ec : ErrorCode, response (step s (call  ic sac)) = error ec /\ ErrorMsg s (call  ic sac) ec /\ s = system (step s (call  ic sac)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_call in H.
    unfold call_safe.
    unfold call_pre.
    case_eq (map_apply iCmp_eq (running (state s)) ic);intros.
    case_eq (existsb (fun p : Perm => negb (appHasPermissionBool (getAppFromCmp c s) p s)) (getMandatoryPerms sac));intros.
    exists not_enough_permissions.
    split;auto.
    split;auto.
    exists c.
    split;auto.
    rewrite existsb_exists in H2.
    apply ex_not_not_all.
    destruct H2.
    destruct H2.
    exists (getAppFromCmp c s).
    apply ex_not_not_all.
    exists x.
    apply ex_not_not_all.
    assert (isSysPerm:=H2).
    apply mandatoryPermsAllSystem in isSysPerm.
    exists isSysPerm.
    rewrite negb_true_iff in H3.
    invertBool H3.
    intro;apply H3.
    apply appHasPermissionCorrect;auto.
    apply H4.
    apply ifRunningThenInApp in H1;auto.
    destruct H1.
    assert (getAppFromCmp c s=x0).
    apply inAppThenGetAppFromCmp in H1;auto.
    rewrite H5;auto.
    unfold not;intros.
    apply mandatoryPermsCorrect;auto.
    destruct H.
    exists c.
    split;auto.
    intros.
    invertBool H2.
    rewrite existsb_exists in H2.
    apply NNPP.
    intro;apply H2.
    exists p.
    split.
    apply (mandatoryPermsCorrect sac p H);auto.
    rewrite negb_true_iff.
    rewrite <-not_true_iff_false.
    intro;apply H5.
    apply inAppThenGetAppFromCmp in H3;auto.
    rewrite H3 in H6.
    apply appHasPermissionCorrect;auto.
    exists instance_not_running;auto.
Qed.

Lemma callIsSound :  forall (s:System) (ic:iCmp) (sac:SACall) (sValid: validstate s),
        exec s (call ic sac) (system (step s (call ic sac))) (response (step s (call ic sac))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (call ic sac) s));intro.
    left.
    simpl.
    assert(call_pre ic sac s = None).
    unfold call_pre.
    destruct H.
    destruct H.
    rewrite H.
    assert (existsb (fun p : Perm => negb (appHasPermissionBool (getAppFromCmp x s) p s)) (getMandatoryPerms sac)=false).
    rewrite <-not_true_iff_false.
    unfold not;intros.
    rewrite existsb_exists in H1.
    destruct H1.
    destruct H1.
    assert (exists a:idApp, inApp x a s).
    apply (ifRunningThenInApp s sValid x ic);auto.
    destruct H3.
    assert (isSystemPerm x0).
    apply (mandatoryPermsAllSystem sac).
    auto.
    rewrite<- (mandatoryPermsCorrect sac x0 H4) in H1.
    specialize (H0 x1 x0 H4 H3 H1).
    rewrite negb_true_iff in H2.
    rewrite<- not_true_iff_false in H2.
    apply H2.
    assert (getAppFromCmp x s = x1).
    apply inAppThenGetAppFromCmp;auto.
    rewrite H5.
    apply appHasPermissionCorrect; auto.
    rewrite H1.
    auto.
    
    
    
    unfold call_safe;simpl.
    rewrite H0;simpl.
    split;auto.
    split;auto.
    apply callCorrect;auto.
    right.
    apply notPreCallThenError;auto.
    
Qed.
End Call.
