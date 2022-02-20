(* En este archivo se demuestra la corrección de la acción write *)
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
Require Import ValidStateLemmas.

Section Write.


Lemma writeCorrect : forall (s:System) (i:iCmp) (c:CProvider) (u:uri) (v:Val), (pre (write i c u v) s) -> validstate s -> post_write i c u v s (write_post i c u v s).
Proof.
    intros.
    unfold post_write.
    unfold write_post.
    split. simpl; auto.
    simpl.
    unfold writeResCont.
    destruct H.
    destruct H.
    destruct H.
    destruct H2.
    destruct H2.
    destruct H3.
    case_eq (map_apply uri_eq (map_res c) u);intros.
    
    split;intros.
    assert (getAppFromCmp (cmpCP c) s = x).
    apply inAppThenGetAppFromCmp;auto.
    rewrite H6.
    elim (classic ( (x,r0) = (a',r)));intros.
    right.
    inversion H7.
    rewrite<- H9.
    split;auto.
    left.
    rewrite overrideNotEq.
    auto.
    unfold not;intros.
    inversion H8.
    rewrite H10 in H7.
    rewrite H11 in H7.
    apply H7.
    auto.
    
    split;intros.
    assert (getAppFromCmp (cmpCP c) s = x).
    apply inAppThenGetAppFromCmp;auto.
    rewrite H6 in H5.
    elim (classic ( (a',r0) = (x,r)));intros.
    right.
    rewrite H7 in H5.
    rewrite <-addAndApply in H5.
    inversion H5.
    inversion H7.
    split;auto.
    left.
    rewrite overrideNotEq in H5.
    auto.
    auto.
    
    split;intros.
    assert (getAppFromCmp (cmpCP c) s = x).
    apply inAppThenGetAppFromCmp;auto.
    rewrite H7.
    inversion H6.
    assert (a'=x).
    destruct H0.
    destruct_conj H8.
    apply (H10 (cmpCP c) a' x);auto.
    rewrite H8.
    rewrite<- addAndApply.
    auto.
    
    repeat (split;auto).
    apply addPreservesCorrectness.
    apply resContCorrect;auto.
    
    split;intros.
    left.
    auto.
    split;intros.
    left.
    auto.
    split;intros.
    rewrite H2 in H4.
    inversion H4.
    
    split.
    apply resContCorrect;auto.
    repeat (split;auto).
    
Qed.

Lemma notPreWriteThenError : forall (s:System) (i:iCmp) (c:CProvider) (u:uri) (v:Val) , ~(pre (write i c u v) s) -> validstate s -> exists ec : ErrorCode, response (step s (write i c u v)) = error ec /\ ErrorMsg s (write i c u v) ec /\ s = system (step s (write i c u v)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_write in H.
    unfold write_safe.
    unfold write_pre.
    case_eq (negb (existsResBool c u s));intros.
    exists no_such_res.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H1.
    invertBool H1.
    intro;apply H1.
    apply existsRes_iff;auto. 
    case_eq (map_apply iCmp_eq (running (state s)) i);intros.
    case_eq ((canWriteBool c0 c s || delPermsBool c0 c u Write s));intros.
    destruct H.
    split.
    rewrite negb_false_iff in H1.
    apply existsRes_iff;auto. 
    exists c0.
    split;auto.
    split.
    apply (notCPRunningVS s H0 i);auto. 
    rewrite orb_true_iff in H3.
    destruct H3.
    left.
    unfold canWriteBool in H.
    unfold canWrite.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.

    exists not_enough_permissions.
    split;auto.
    split;auto.
    exists c0.
    split;auto.
    invertBool H3.
    intro;apply H3.
    rewrite orb_true_iff.
    destruct H4.
    left.
    unfold canWriteBool.
    unfold canWrite in H4.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    
    exists instance_not_running.
    split;auto.

Qed.
Lemma writeIsSound : forall (s:System) (i:iCmp) (c:CProvider) (u:uri) (v:Val),
        validstate s -> exec s (write i c u v) (system (step s (write i c u v))) (response (step s (write i c u v))).
Proof.
    
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (write i c u v) s));intro.
    left.
    assert(write_pre i c u v s = None).
    unfold write_pre.
    destruct H0.
    destruct H1.
    destruct_conj H1.
    assert (negb (existsResBool c u s)=false).
    rewrite negb_false_iff.
    apply existsRes_iff;auto.
    rewrite H3.
    rewrite H2.
    
    
    assert (canWriteBool x c s || delPermsBool x c u Write s = true).
    rewrite orb_true_iff.
    destruct H4.
    left.
    unfold canWrite in H4.
    unfold canWriteBool.
    apply canDoThisBoolCorrect; auto.
    right.
    apply delPermsBoolCorrect; auto.
    
    rewrite H5.
    auto.
    
    
    
    unfold step;simpl.
    unfold write_safe;simpl.
    rewrite H1;simpl.
    split;auto.
    split;auto.
    apply writeCorrect;auto.
    right.
    apply notPreWriteThenError;auto.
    
Qed.
End Write.
