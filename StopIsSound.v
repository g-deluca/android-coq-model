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

Section Stop.

Lemma stopCorrect : forall (s:System) (ic:iCmp) (sValid: validstate s),
    (pre (stop ic) s) -> post_stop ic s (stop_post ic s).
Proof.
    intros.
    unfold post_stop.
    split. simpl; auto.
    simpl in H.
    unfold pre_stop in H;simpl in H.
    destruct H.
    unfold stop_post.
    unfold insNotInState.
    simpl.
    split;intros.
    rewrite valueDropValue in H0.
    destruct H0.
    auto.
    split;intros.
    elim (classic (ic=ic'));intros.
    right;auto.
    left.
    apply valueDropValue.
    auto.
    split.
    apply dropPreservesCorrectness.
    apply runningCorrect;auto.
    split;intros.
    apply valueDropNotValue.
    unfold removeTPerms.
    split;intros.
    rewrite valueDropThenValue in H0.
    destruct H0.
    auto.
    split;intros.
    elim (classic (ic'=ic));intros.
    right;auto.
    left.
    apply valueDropThenValue.
    split;auto.
    unfold not;intros.
    apply H1.
    rewrite filter_In in H2.
    destruct H2.
    simpl in H3.
    destruct iCmp_eq in H3.
    auto.
    discriminate H3.
    split;intros.
    elim (classic (In (ic,cp,u) (filter (fun tuple : iCmp * CProvider * uri => if iCmp_eq ic (fst (fst tuple)) then true else false) (map_getKeys (delTPerms (state s))))));intros.
    apply valueDropAllNotValue.
    auto.
    assert (map_apply deltpermsdomeq (dropAll (iCmp * CProvider * uri) PType deltpermsdomeq (filter (fun tuple : iCmp * CProvider * uri => if iCmp_eq ic (fst (fst tuple)) then true else false) (map_getKeys (delTPerms (state s)))) (delTPerms (state s))) (ic, cp, u) = map_apply deltpermsdomeq (delTPerms (state s)) (ic,cp,u)).
    apply dropNotIn;auto.
    rewrite H1.
    unfold not;intros.
    apply H0.
    rewrite filter_In.
    simpl.
    split.
    unfold map_getKeys.
    rewrite in_map_iff.
    unfold is_Value in H2.
    case_eq (map_apply deltpermsdomeq (delTPerms (state s)) (ic, cp, u));intros.
    rewrite valueIffExists in H3.
    exists {| item_index := (ic, cp, u); item_info := p |}.
    simpl.
    auto.
    apply (delTPermsCorrect);auto.
    rewrite H3 in H2.
    inversion H2.
    destruct iCmp_eq;auto.
    
    
    
    
    
    repeat (split;auto).
    apply dropAllPreservesCorrectness.
    apply delTPermsCorrect;auto.
Qed.

Lemma notPreStopThenError : forall (s:System) (ic:iCmp), ~(pre (stop ic) s) -> validstate s -> exists ec : ErrorCode, response (step s (stop ic)) = error ec /\ ErrorMsg s (stop ic) ec /\ s = system (step s (stop ic)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_stop in H.
    unfold stop_safe.
    unfold stop_pre.
    case_eq(is_ValueBool (map_apply iCmp_eq (running (state s)) ic));intros.
    destruct H.
    unfold is_ValueBool in H1.
    case_eq ((map_apply iCmp_eq (running (state s)) ic));intros;rewrite H in H1;simpl in H1.
    exists c;auto.
    discriminate H1.
    exists instance_not_running.
    split;auto.
    split;auto.
    invertBool H1.
    intro;apply H1.
    unfold is_ValueBool.
    unfold is_Value in H2.
    case_eq ((map_apply iCmp_eq (running (state s)) ic));intros;rewrite H3 in H2;simpl in H2;auto.
Qed.

Lemma stopIsSound : forall (s:System) (ic:iCmp) (sValid: validstate s),
        exec s (stop ic) (system (step s (stop ic))) (response (step s (stop ic))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (stop ic) s));intro.
    left.
    simpl.
    assert(stop_pre ic s = None).
    unfold stop_pre.
    destruct H.
    unfold is_ValueBool.
    rewrite H.
    auto.
    
    unfold stop_safe;simpl.
    rewrite H0;simpl.
    split;auto.
    split;auto.
    apply stopCorrect;auto.
    right.
    apply notPreStopThenError;auto.
    
Qed.
End Stop.
