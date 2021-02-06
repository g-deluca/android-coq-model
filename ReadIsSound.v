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

Section Read.


Lemma readCorrect : forall (s:System) (i:iCmp) (c:CProvider) (u:uri), (pre (read i c u) s) -> validstate s -> post_read i c u s (read_post i c u s).
Proof.
    intros.
    unfold post_read.
    unfold read_post.
    auto.
Qed.

Lemma notPreReadThenError : forall (s:System) (i:iCmp) (c:CProvider) (u:uri), ~(pre (read i c u) s) -> validstate s -> exists ec : ErrorCode, response (step s (read i c u)) = error ec /\ ErrorMsg s (read i c u) ec /\ s = system (step s (read i c u)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_read in H.
    unfold read_safe.
    unfold read_pre.
    case_eq (negb (existsResBool c u s));intros.
    exists no_such_res.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H1.
    invertBool H1.
    intro;apply H1.
    apply existsRes_iff;auto. 
    case_eq (map_apply iCmp_eq (running (state s)) i);intros.
    case_eq ((canReadBool c0 c s || delPermsBool c0 c u Read s));intros.
    destruct H.
    split.
    rewrite negb_false_iff in H1.
    apply existsRes_iff;auto. 
    exists c0.
    split;auto.
    rewrite orb_true_iff in H3.
    destruct H3.
    left.
    unfold canReadBool in H.
    unfold canRead.
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
    unfold canReadBool.
    unfold canRead in H4.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    
    exists instance_not_running.
    split;auto.

Qed.

Lemma readIsSound : forall (s:System) (i:iCmp) (c:CProvider) (u:uri),
        validstate s -> exec s (read i c u) (system (step s (read i c u))) (response (step s (read i c u))).
Proof.
    
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (read i c u) s));intro.
    left.
    assert(read_pre i c u s = None).
    unfold read_pre.
    destruct H0.
    destruct H1.
    destruct_conj H1.
    assert (negb (existsResBool c u s)=false).
    rewrite negb_false_iff.
    apply existsRes_iff;auto.
    rewrite H1.
    
    assert (canReadBool x c s || delPermsBool x c u Read s = true).
    rewrite orb_true_iff.
    destruct H3.
    left.
    unfold canRead in H3.
    unfold canReadBool.
    apply canDoThisBoolCorrect; auto.
    right.
    apply delPermsBoolCorrect; auto.
    
    rewrite H2.
    rewrite H4.
    auto.
    
    
    
    unfold step;simpl.
    unfold read_safe;simpl.
    rewrite H1;simpl.
    split;auto.
    split;auto.
    apply readCorrect;auto.
    right.
    apply notPreReadThenError;auto.
    
Qed.
End Read.
