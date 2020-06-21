(* En este archivo se demuestra la corrección de la acción revokeDel *)
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

Section RevokeDel.

Lemma removeAllAppsCorrect : forall (A:Set) (domeq: forall (id1 id2 : (A*CProvider*uri)), {id1 = id2} + {id1 <> id2}) (mp:mapping (A*CProvider*uri) PType) (mpCorrect: map_correct mp) (cp:CProvider) (u:uri) (pt:PType), (forall (ic' : A) (cp' : CProvider) (u' : uri) (pt' : PType), map_apply domeq (removeAllPerms A domeq mp cp u pt) (ic', cp', u') = Value (A * CProvider * uri) pt' -> exists pt'' : PType, map_apply domeq mp (ic', cp', u') = Value (A * CProvider * uri) pt'' /\ (pt'' = pt' \/ cp' = cp /\ u' = u /\ ptminus pt'' pt = Some pt')) /\ (forall (ic' : A) (cp' : CProvider) (u' : uri) (pt' : PType), map_apply domeq mp (ic', cp', u') = Value (A * CProvider * uri) pt' -> ptminus pt' pt = None /\ cp' = cp /\ u' = u \/ (exists pt'' : PType, map_apply domeq (removeAllPerms A domeq mp cp u pt) (ic', cp', u') = Value (A * CProvider * uri) pt'' /\ (pt'' = pt' \/ cp' = cp /\ u' = u /\ ptminus pt' pt = Some pt''))) /\ (forall ic' : A, match map_apply domeq mp (ic', cp, u) with | Value _ pt' => match ptminus pt' pt with | Some pt'' => map_apply domeq (removeAllPerms A domeq mp cp u pt) (ic', cp, u) = Value (A * CProvider * uri) pt'' | None => ~ is_Value (map_apply domeq (removeAllPerms A domeq mp cp u pt) (ic', cp, u)) end | Error _ _ => ~ is_Value (map_apply domeq (removeAllPerms A domeq mp cp u pt) (ic', cp, u)) end).
Proof.
    split;intros.
    unfold removeAllPerms in H.
    rewrite valueDropThenValue in H.
    destruct H.
    remember (map (fun tuple : A * CProvider * uri => (tuple, match map_apply domeq mp tuple with | Value _ pt'0 => match ptminus pt'0 pt with | Some pt'' => pt'' | None => Both end | Error _ _ => Both end)) (filter (fun tuple : A * CProvider * uri => match map_apply domeq mp tuple with | Value _ pt'0 => isSomethingBool PType (ptminus pt'0 pt) | Error _ _ => false end) (filter (fun tuple : A * CProvider * uri => if CProvider_eq cp (snd (fst tuple)) then if uri_eq u (snd tuple) then true else false else false) (map_getKeys mp)))) as indexAndVals.
    elim (classic (In (ic', cp', u') (map (fun pair=>fst pair) indexAndVals)));intros.
    
    case_eq (map_apply domeq mp (ic', cp', u'));intros.
    exists p.
    split;auto.
    right.
    rewrite HeqindexAndVals in H1.
    rewrite in_map_iff in H1.
    destruct H1.
    destruct H1.
    rewrite in_map_iff in H3.
    destruct H3.
    destruct H3.
    rewrite<- H3 in H1.
    simpl in H1.
    rewrite<- H1 in H2.
    rewrite H2 in H3.
    case_eq (ptminus p pt);intros.
    rewrite H5 in H3.
    assert ( map_apply domeq (addAll (A * CProvider * uri) PType domeq indexAndVals mp) (ic', cp', u') = Value (A * CProvider * uri) p0).
    apply inAddAll.
    assert (exists x,hd_error (filter (fun pair : A * CProvider * uri * PType => if domeq (fst pair) (ic', cp', u') then true else false) indexAndVals) = Some x /\ (fun pair : A * CProvider * uri * PType => if domeq (fst pair) (ic', cp', u') then true else false) x=true /\ In x indexAndVals).
    apply ifExistsFilterHdError.
    exists x.
    rewrite filter_In.
    split.
    rewrite HeqindexAndVals.
    rewrite in_map_iff.
    exists (ic', cp', u').
    split;
    rewrite<- H1.
    rewrite H2.
    rewrite H5.
    auto.
    auto.
    rewrite<- H1.
    simpl.
    rewrite <-H3.
    simpl.
    destruct (domeq x0 x0);auto.
    destruct H6.
    destruct H6.
    rewrite H6.
    destruct H7.
    rewrite HeqindexAndVals in H8.
    rewrite in_map_iff in H8.
    destruct H8.
    destruct H8.
    assert (x2=(ic',cp',u')).
    rewrite <-H8 in H7.
    simpl in H7.
    destruct domeq in H7.
    auto.
    discriminate H7.
    rewrite<- H10 in H1.
    rewrite H1 in H2.
    rewrite H2 in H8.
    rewrite H5 in H8.
    rewrite <-H8.
    rewrite <-H10.
    auto.
    rewrite H in H6.
    inversion H6.
    
    rewrite filter_In in H4.
    destruct H4.
    rewrite filter_In in H4.
    destruct H4.
    destruct CProvider_eq in H9.
    destruct uri_eq in H9.
    rewrite H1 in *.
    simpl in e.
    simpl in e0.
    auto.
    discriminate H9.
    discriminate H9.
    assert (False).
    apply H0.
    rewrite filter_In.
    rewrite<- H1.
    rewrite H2.
    rewrite filter_In in H4.
    destruct H4.
    split;auto.
    unfold isSomethingBool.
    rewrite H5.
    auto.
    destruct H6.
    assert (False).
    apply H0.
    rewrite filter_In.
    
    
    rewrite HeqindexAndVals in H1.
    rewrite in_map_iff in H1.
    destruct H1.
    destruct H1.
    rewrite in_map_iff in H3.
    destruct H3.
    destruct H3.
    rewrite<- H3 in H1.
    simpl in H1.
    rewrite<- H1.
    rewrite filter_In in H4.
    destruct H4.
    rewrite H1 in H5.
    rewrite H2 in H5.
    discriminate H5.
    destruct H3.
    rewrite notInAddAll in H.
    exists pt'.
    split;auto.
    auto.
    
    
    split;intros.
    elim (classic ((cp',u')=(cp,u)));intros.
    case_eq (ptminus pt' pt);intros.
    right.
    exists p.
    split.
    unfold removeAllPerms.
    rewrite valueDropThenValue.
    split.
    remember (map (fun tuple : A * CProvider * uri => (tuple, match map_apply domeq mp tuple with | Value _ pt'0 => match ptminus pt'0 pt with | Some pt'' => pt'' | None => Both end | Error _ _ => Both end)) (filter (fun tuple : A * CProvider * uri => match map_apply domeq mp tuple with | Value _ pt'0 => isSomethingBool PType (ptminus pt'0 pt) | Error _ _ => false end) (filter (fun tuple : A * CProvider * uri => if CProvider_eq cp (snd (fst tuple)) then if uri_eq u (snd tuple) then true else false else false) (map_getKeys mp)))) as indexAndVals.
    rewrite (inAddAll (A*CProvider*uri) PType domeq indexAndVals mp p).
    auto.
    assert (exists x,hd_error (filter (fun pair : A * CProvider * uri * PType => if domeq (fst pair) (ic', cp', u') then true else false) indexAndVals) = Some x /\ (fun pair : A * CProvider * uri * PType => if domeq (fst pair) (ic', cp', u') then true else false) x=true /\ In x indexAndVals).
    apply ifExistsFilterHdError.
    exists (ic',cp',u',p).
    rewrite filter_In.
    split.
    rewrite HeqindexAndVals.
    rewrite in_map_iff.
    exists (ic', cp', u').
    split.
    rewrite H.
    rewrite H1.
    auto.
    rewrite filter_In.
    split.
    rewrite filter_In.
    split.
    
    rewrite<- (valueIffInGetKeys domeq (ic',cp',u')  ).
    rewrite H.
    unfold is_Value;auto.
    auto.
    simpl.
    inversion H0.
    destruct CProvider_eq;auto.
    destruct uri_eq;auto.
    rewrite H.
    rewrite H1.
    unfold isSomethingBool.
    auto.
    simpl.
    destruct (domeq (ic', cp', u') (ic', cp', u'));auto.
    destruct H2.
    destruct_conj H2.
    rewrite H3.
    rewrite HeqindexAndVals in H5.
    rewrite in_map_iff in H5.
    destruct H5.
    destruct H4.
    assert (x0=(ic',cp',u')).
    rewrite <-H4 in H2.
    simpl in H2.
    destruct domeq in H2.
    auto.
    discriminate H2.
    rewrite H6 in H4.
    rewrite H in H4.
    rewrite H1 in H4.
    rewrite H4.
    auto.
    
    rewrite filter_In.
    apply or_not_and.
    right.
    rewrite H.
    unfold isSomethingBool.
    rewrite H1.
    apply no_fixpoint_negb.
    right.
    inversion H0.
    auto.
    left.
    inversion H0.
    auto.
    right.
    exists pt'.
    split.
    unfold removeAllPerms.
    
    rewrite valueDropThenValue.
    split.
    rewrite <-H.
    apply notInAddAll.
    rewrite in_map_iff.
    unfold not;intros.
    apply H0.
    destruct H1.
    destruct H1.
    rewrite in_map_iff in H2.
    destruct H2.
    destruct H2.
    rewrite filter_In in H3.
    destruct H3.
    rewrite filter_In in H3.
    destruct H3.
    rewrite<-H2 in H1.
    simpl in H1.
    rewrite H1 in H5.
    simpl in H5.
    destruct CProvider_eq in H5.
    destruct uri_eq in H5.
    rewrite e, e0.
    auto.
    discriminate H5.
    discriminate H5.
    
    
    rewrite filter_In.
    apply or_not_and.
    left.
    rewrite filter_In.
    apply or_not_and.
    right.
    unfold not;intros.
    apply H0.
    destruct CProvider_eq in H1.
    destruct uri_eq in H1.
    rewrite e, e0.
    auto.
    discriminate H1.
    discriminate H1.
    left.
    auto.
    
    unfold removeAllPerms.
    remember (map (fun tuple : A * CProvider * uri => (tuple, match map_apply domeq mp tuple with | Value _ pt' => match ptminus pt' pt with | Some pt'' => pt'' | None => Both end | Error _ _ => Both end)) (filter (fun tuple : A * CProvider * uri => match map_apply domeq mp tuple with | Value _ pt' => isSomethingBool PType (ptminus pt' pt) | Error _ _ => false end) (filter (fun tuple : A * CProvider * uri => if CProvider_eq cp (snd (fst tuple)) then if uri_eq u (snd tuple) then true else false else false) (map_getKeys mp)))) as indexAndVals.
    case_eq (map_apply domeq mp (ic', cp, u));intros.
    case_eq (ptminus p pt);intros.
    rewrite valueDropThenValue.
    split.
    apply inAddAll.
    assert (exists x,hd_error (filter (fun pair : A * CProvider * uri * PType => if domeq (fst pair) (ic', cp, u) then true else false) indexAndVals) = Some x /\ (fun pair : A * CProvider * uri * PType => if domeq (fst pair) (ic', cp, u) then true else false) x=true /\ In x indexAndVals).
    apply ifExistsFilterHdError.
    exists (ic',cp,u,p0).
    rewrite filter_In.
    split.
    rewrite HeqindexAndVals.
    rewrite in_map_iff.
    exists (ic', cp, u).
    split.
    rewrite H.
    rewrite H0.
    auto.
    rewrite filter_In.
    split.
    rewrite filter_In.
    split.
    rewrite<- (valueIffInGetKeys domeq (ic',cp,u)  ).
    rewrite H.
    unfold is_Value;auto.
    auto.
    simpl.
    inversion H0.
    destruct CProvider_eq;auto.
    destruct uri_eq;auto.
    rewrite H.
    rewrite H0.
    unfold isSomethingBool.
    auto.
    simpl.
    destruct (domeq (ic', cp, u) (ic', cp, u));auto.
    destruct H1.
    destruct_conj H1.
    rewrite H2.
    rewrite HeqindexAndVals in H4.
    rewrite in_map_iff in H4.
    destruct H4.
    destruct H3.
    assert (x0=(ic',cp,u)).
    rewrite <-H3 in H1.
    simpl in H1.
    destruct domeq in H1.
    auto.
    discriminate H1.
    rewrite H5 in H3.
    rewrite H in H3.
    rewrite H0 in H3.
    rewrite H3.
    auto.
    
    rewrite filter_In.
    apply or_not_and.
    right.
    rewrite H.
    unfold isSomethingBool.
    rewrite H0.
    apply no_fixpoint_negb.
    rewrite (valueIffInGetKeys domeq (ic',cp,u)).
    rewrite<- (valueIffInGetKeys domeq (ic',cp,u)  ).
    apply valueDropAllNotValue.
    rewrite filter_In.
    split.
    rewrite filter_In.
    split.
    rewrite<- (valueIffInGetKeys domeq (ic',cp,u)  ).
    rewrite H.
    unfold is_Value;auto.
    auto.
    simpl.
    destruct CProvider_eq;auto.
    destruct uri_eq;auto.
    rewrite H.
    rewrite H0.
    unfold isSomethingBool.
    auto.
    apply dropAllPreservesCorrectness.
    apply addAllPreservesCorrectness.
    auto.
    apply dropAllPreservesCorrectness.
    apply addAllPreservesCorrectness.
    auto.
    
    rewrite (valueIffInGetKeys domeq (ic',cp,u)).
    rewrite<- (valueIffInGetKeys domeq (ic',cp,u)  ).
    rewrite dropNotIn.
    rewrite notInAddAll.
    rewrite H.
    unfold is_Value;auto.
    rewrite in_map_iff.
    unfold not;intros.
    destruct H0.
    destruct H0.
    rewrite HeqindexAndVals in H1.
    rewrite in_map_iff in H1.
    destruct H1.
    destruct H1.
    rewrite filter_In in H2.
    destruct H2.
    rewrite filter_In in H2.
    destruct H2.
    rewrite <- H1 in H0.
    simpl in H0.
    rewrite H0 in H2.
    rewrite<- (valueIffInGetKeys domeq (ic',cp,u)) in H2.
    rewrite H in H2.
    unfold is_Value in H2.
    destruct H2.
    auto.
    
    rewrite filter_In.
    apply or_not_and.
    left.
    rewrite filter_In.
    apply or_not_and.
    left.
    rewrite<- (valueIffInGetKeys domeq (ic',cp,u)  ).
    rewrite H.
    unfold is_Value;auto.
    auto.
    apply dropAllPreservesCorrectness.
    apply addAllPreservesCorrectness.
    auto.
    apply dropAllPreservesCorrectness.
    apply addAllPreservesCorrectness.
    auto.
Qed.

Lemma revokeDelCorrect : forall (s:System) (ic:iCmp) (cp:CProvider) (u:uri) (pt:PType) (sValid: validstate s),
    (pre (revokeDel ic cp u pt) s) -> post_revokeDel ic cp u pt s (revokeDel_post ic cp u pt s).
Proof.
    intros.
    unfold post_revokeDel.
    split. simpl; auto.
    unfold revokeDel_post; simpl.
    assert ( (forall (ic' : iCmp) (cp' : CProvider) (u' : uri) (pt' : PType), map_apply deltpermsdomeq (removeAllPerms iCmp deltpermsdomeq (delTPerms (state s)) cp u pt) (ic', cp', u') = Value (iCmp * CProvider * uri) pt' -> exists pt'' : PType, map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp', u') = Value (iCmp * CProvider * uri) pt'' /\ (pt'' = pt' \/ cp' = cp /\ u' = u /\ ptminus pt'' pt = Some pt')) /\ (forall (ic' : iCmp) (cp' : CProvider) (u' : uri) (pt' : PType), map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp', u') = Value (iCmp * CProvider * uri) pt' -> ptminus pt' pt = None /\ cp' = cp /\ u' = u \/ (exists pt'' : PType, map_apply deltpermsdomeq (removeAllPerms iCmp deltpermsdomeq (delTPerms (state s)) cp u pt) (ic', cp', u') = Value (iCmp * CProvider * uri) pt'' /\ (pt'' = pt' \/ cp' = cp /\ u' = u /\ ptminus pt' pt = Some pt''))) /\ (forall ic' : iCmp, match map_apply deltpermsdomeq (delTPerms (state s)) (ic', cp, u) with | Value _ pt' => match ptminus pt' pt with | Some pt'' => map_apply deltpermsdomeq (removeAllPerms iCmp deltpermsdomeq (delTPerms (state s)) cp u pt) (ic', cp, u) = Value (iCmp * CProvider * uri) pt'' | None => ~ is_Value (map_apply deltpermsdomeq (removeAllPerms iCmp deltpermsdomeq (delTPerms (state s)) cp u pt) (ic', cp, u)) end | Error _ _ => ~ is_Value (map_apply deltpermsdomeq (removeAllPerms iCmp deltpermsdomeq (delTPerms (state s)) cp u pt) (ic', cp, u)) end)).
    
    apply removeAllAppsCorrect.
    apply delTPermsCorrect;auto.
    destruct_conj H0.
    split;auto.
    split;auto.
    split;auto.
    assert ( (forall (a' : idApp) (cp' : CProvider) (u' : uri) (pt' : PType), map_apply delppermsdomeq (removeAllPerms idApp delppermsdomeq (delPPerms (state s)) cp u pt) (a', cp', u') = Value (idApp * CProvider * uri) pt' -> exists pt'' : PType, map_apply delppermsdomeq (delPPerms (state s)) (a', cp', u') = Value (idApp * CProvider * uri) pt'' /\ (pt'' = pt' \/ cp' = cp /\ u' = u /\ ptminus pt'' pt = Some pt')) /\ (forall (a' : idApp) (cp' : CProvider) (u' : uri) (pt' : PType), map_apply delppermsdomeq (delPPerms (state s)) (a', cp', u') = Value (idApp * CProvider * uri) pt' -> ptminus pt' pt = None /\ cp' = cp /\ u' = u \/ (exists pt'' : PType, map_apply delppermsdomeq (removeAllPerms idApp delppermsdomeq (delPPerms (state s)) cp u pt) (a', cp', u') = Value (idApp * CProvider * uri) pt'' /\ (pt'' = pt' \/ cp' = cp /\ u' = u /\ ptminus pt' pt = Some pt''))) /\ (forall a' : idApp, match map_apply delppermsdomeq (delPPerms (state s)) (a', cp, u) with | Value _ pt' => match ptminus pt' pt with | Some pt'' => map_apply delppermsdomeq (removeAllPerms idApp delppermsdomeq (delPPerms (state s)) cp u pt) (a', cp, u) = Value (idApp * CProvider * uri) pt'' | None => ~ is_Value (map_apply delppermsdomeq (removeAllPerms idApp delppermsdomeq (delPPerms (state s)) cp u pt) (a', cp, u)) end | Error _ _ => ~ is_Value (map_apply delppermsdomeq (removeAllPerms idApp delppermsdomeq (delPPerms (state s)) cp u pt) (a', cp, u)) end)).
    
    apply removeAllAppsCorrect.
    apply delPPermsCorrect;auto.
    destruct_conj H2.
    split.
    unfold removeAllPerms.
    apply dropAllPreservesCorrectness.
    apply addAllPreservesCorrectness.
    apply delTPermsCorrect;auto.
    split;auto.
    split;auto.
    split;auto.
    
    
    repeat (split;auto).
    unfold removeAllPerms.
    apply dropAllPreservesCorrectness.
    apply addAllPreservesCorrectness.
    apply delPPermsCorrect;auto.
Qed.

Lemma notPreRevokeDelThenError : forall (s:System) (ic:iCmp) (cp:CProvider) (u:uri) (pt:PType), ~(pre (revokeDel ic cp u pt) s) -> validstate s -> exists ec : ErrorCode, response (step s (revokeDel ic cp u pt)) = error ec /\ ErrorMsg s (revokeDel ic cp u pt) ec /\ s = system (step s (revokeDel ic cp u pt)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_revokeDel in H.
    unfold revokeDel_safe.
    unfold revokeDel_pre.
    case_eq (negb (existsResBool cp u s));intros.
    exists no_such_res.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H1.
    invertBool H1.
    intro;apply H1.
    apply existsRes_iff;auto.

    case_eq (map_apply iCmp_eq (running (state s)) ic);intros.
    rewrite negb_false_iff in H1.
    apply existsRes_iff in H1;auto.
    unfold canReadBool.
    unfold canWriteBool.
    destruct pt.
    case_eq (negb (canDoThisBool c cp s readE || delPermsBool c cp u Read s));intros.
    exists not_enough_permissions.
    split;auto.
    split;auto.
    exists c.
    split;auto.
    invertBool H3.
    intro;apply H3.
    rewrite negb_false_iff.
    rewrite orb_true_iff.
    destruct H4.
    left.

    unfold canRead in H4.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    destruct H.
    split;auto.
    exists c.
    split;auto.
    rewrite negb_false_iff in H3.
    unfold canRead.
    rewrite orb_true_iff in H3.
    destruct H3.
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
    rewrite negb_true_iff in H3.
    invertBool H3.
    unfold canWrite.
    intro;apply H3.
    rewrite orb_true_iff.
    destruct H4.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    destruct H.
    split;auto.
    exists c.
    split;auto.
    rewrite negb_false_iff in H3.
    unfold canWrite.
    rewrite orb_true_iff in H3.
    destruct H3.
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
    invertBool H3.
    intro;apply H3.
    rewrite orb_false_iff.
    destruct H4.
    split;rewrite negb_false_iff;rewrite orb_true_iff.
    unfold canRead in H4.
    destruct H4.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    unfold canWrite in H5.
    destruct H5.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.

    destruct H.
    split;auto.
    exists c.
    split;auto.
    rewrite orb_false_iff in H3.
    destruct H3.
    rewrite negb_false_iff in H,H3.
    rewrite orb_true_iff in H,H3.
    split.
    unfold canRead.
    destruct H.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    destruct H3.
    left.
    unfold canWrite.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.

    exists instance_not_running.
    split;auto.
Qed.

Lemma revokeDelIsSound :  forall (s:System) (ic:iCmp) (cp:CProvider) (u:uri) (pt:PType) (sValid: validstate s),
        exec s (revokeDel ic cp u pt) (system (step s (revokeDel ic cp u pt))) (response (step s (revokeDel ic cp u pt))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (revokeDel ic cp u pt) s));intro.
    left.
    simpl.
    assert(revokeDel_pre ic cp u pt s = None).
    unfold revokeDel_pre.
    simpl in H.
    destruct H.
    assert (negb (existsResBool cp u s)=false).
    rewrite negb_false_iff.
    apply existsRes_iff; auto.
    rewrite H1.
    destruct H0.
    destruct H0.
    rewrite H0.
    unfold canRead in H2.
    unfold canWrite in H2.
    unfold canReadBool.
    unfold canWriteBool.
    case_eq pt;intros; rewrite H3 in H2.
    
    assert (canDoThisBool x cp s readE || delPermsBool x cp u Read s=true).
    rewrite orb_true_iff.
    destruct H2.
    left.
    apply canDoThisBoolCorrect; auto.
    right.
    apply delPermsBoolCorrect;auto.
    rewrite H4;auto.
    
    assert (canDoThisBool x cp s writeE || delPermsBool x cp u Write s=true).
    rewrite orb_true_iff.
    destruct H2.
    left.
    apply canDoThisBoolCorrect; auto.
    right.
    apply delPermsBoolCorrect;auto.
    rewrite H4;auto.
    
    destruct H2.
    assert (negb (canDoThisBool x cp s readE || delPermsBool x cp u Read s) || negb (canDoThisBool x cp s writeE || delPermsBool x cp u Write s)=false).
    rewrite orb_false_iff.
    split;rewrite negb_false_iff;rewrite orb_true_iff.
    destruct H2.
    left.
    apply canDoThisBoolCorrect; auto.
    right.
    apply delPermsBoolCorrect;auto.
    destruct H4.
    left.
    apply canDoThisBoolCorrect; auto.
    right.
    apply delPermsBoolCorrect;auto.
    rewrite H5.
    auto.
    
    
    unfold revokeDel_safe;simpl.
    rewrite H0;simpl.
    split;auto.
    split;auto.
    apply revokeDelCorrect;auto.
    right.
    apply (notPreRevokeDelThenError);auto.
    
Qed.
End RevokeDel.
