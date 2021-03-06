(* En este archivo se demuestra la corrección de la acción startActivity *)
Require Export Exec.
Require Import Implementacion.
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

Section StartActivity.

Lemma startActivityCorrect : forall (s:System) (i:Intent) (ic:iCmp) (sValid: validstate s),
    (pre (startActivity i ic) s) -> post_startActivity i ic s (startActivity_post i ic s).
Proof.
    intros.
    unfold post_startActivity.
    simpl in H.
    unfold pre_startActivity in H;simpl in H.
    destruct_conj H.
    unfold addIntent.
    unfold onlyIntentsChanged.
    unfold startActivity_post.
    simpl.
    split; intros.
    split; intros.
    right;auto.
    split;intros.
    destruct H2.
    right.
    inversion H2.
    split;auto.
    unfold createIntent in *.
    simpl.
    repeat (split;auto).
    left;auto.
    left.
    assert (i=createIntent i None).
    case_eq i;intros.
    unfold createIntent.
    simpl.
    rewrite<- H.
    rewrite H2.
    simpl.
    auto.
    rewrite<- H2.
    auto.
    
    repeat (split;auto).
Qed.

Lemma notPreStartActivityThenError : forall (s:System) (i:Intent) (ic:iCmp), ~(pre (startActivity i ic) s) -> validstate s -> exists ec : ErrorCode, response (step s (startActivity i ic)) = error ec /\ ErrorMsg s (startActivity i ic) ec /\ s = system (step s (startActivity i ic)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_startActivity in H.
    unfold startActivity_safe.
    unfold startActivity_pre.
    case_eq (negb (intTypeEqBool (intType i) intActivity));intros.
    exists incorrect_intent_type.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H1.
    invertBool H1.
    intro;apply H1.
    rewrite H2.
    destruct intTypeEqBool;auto.
    case_eq (isSomethingBool Perm (brperm i));intros.
    exists faulty_intent.
    split;auto.
    split;auto.
    unfold isSomethingBool in H2.
    intro.
    destruct (brperm i).
    discriminate H3.
    discriminate H2.
    case_eq (negb (isiCmpRunningBool ic s));intros.
    exists instance_not_running.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H3.
    invertBool H3.
    intro;apply H3.
    apply isiCmpRunningCorrect;auto.
    case_eq ( existsb (fun pair : iCmp * Intent => if idInt_eq (idI i) (idI (snd pair)) then true else false) (sentIntents (state s)));intros.
    exists intent_already_sent.
    split;auto.
    split;auto.
    rewrite existsb_exists in H4.
    destruct H4.
    exists (snd x), (fst x).
    destruct H4.
    split.
    destruct x.
    simpl.
    auto.
    destruct idInt_eq in H5.
    rewrite e;auto.
    discriminate H5.
    destruct H.
    split.
    rewrite negb_false_iff in H1.
    unfold intTypeEqBool in H1.
    destruct (intType i);auto;discriminate H1.
    split.
    unfold isSomethingBool in H2.
    destruct (brperm i);auto;discriminate H2.
    split.
    rewrite negb_false_iff in H3.
    apply isiCmpRunningCorrect;auto.
    invertBool H4.
    intro;apply H4.
    rewrite existsb_exists.
    destruct H.
    destruct H.
    destruct H.
    exists (x0,x).
    split;auto.
    simpl.
    destruct idInt_eq;auto.
Qed.

Lemma startActivityIsSound : forall (s:System) (i:Intent) (ic:iCmp) (sValid: validstate s),
        exec s (startActivity i ic) (system (step s (startActivity i ic))) (response (step s (startActivity i ic))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (startActivity i ic) s));intro.
    left.
    simpl.
    assert(startActivity_pre i ic s = None).
    unfold startActivity_pre.
    destruct H.
    rewrite H.
    unfold intTypeEqBool.
    assert (negb true=false).
    rewrite negb_false_iff.
    auto.
    rewrite H1.
    
    destruct_conj H0.
    rewrite H2.
    unfold isSomethingBool.
    assert (negb (isiCmpRunningBool ic s)=false).
    rewrite negb_false_iff.
    apply isiCmpRunningCorrect; auto.
    rewrite H3.
    assert (existsb (fun pair : iCmp * Intent => if idInt_eq (idI i) (idI (snd pair)) then true else false) (sentIntents (state s))=false).
    rewrite <-not_true_iff_false.
    unfold not;intros.
    rewrite existsb_exists in H5.
    destruct H5.
    destruct H5.
    apply H4.
    exists (snd x).
    destruct idInt_eq in H6.
    exists (fst x).
    case_eq x;intros.
    simpl.
    rewrite<- H7.
    rewrite H7 in e.
    simpl in e.
    split;auto.
    discriminate H6.
    rewrite H5.
    auto.
    
    unfold startActivity_safe;simpl.
    rewrite H0;simpl.
    split;auto.
    split;auto.
    apply startActivityCorrect;auto.
    right.
    apply notPreStartActivityThenError;auto.
    
Qed.
End StartActivity.
