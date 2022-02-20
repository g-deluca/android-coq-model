(* En este archivo se demuestra la corrección de la acción resolveIntent *)
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

Section ResolveIntent.

Lemma resolveIntentCorrect : forall (s:System) (i:Intent) (a:idApp) (sValid: validstate s),
    (pre (resolveIntent i a) s) -> post_resolveIntent i a s (resolveIntent_post i a s).
Proof.
    intros.
    unfold post_resolveIntent.
    split. simpl; auto.
    simpl in H.
    unfold pre_resolveIntent in H;simpl in H.
    destruct H.
    unfold implicitToExplicitIntent.
    split.
    destruct H.
    destruct H0.
    destruct H1.
    destruct H1.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H3.
    destruct H4.
    destruct H4.

    remember (chooseCmp (x0,x) a s) as theX2.

    assert (remX2 := HeqtheX2).

    exists theX2, x1.
    unfold chooseCmp in HeqtheX2.
    simpl in HeqtheX2.
    rewrite H2 in HeqtheX2.
    remember (fun cmp : Cmp =>
                 existsb
                   (fun iFil : intentFilter =>
                    actionTestBool x iFil s && categoryTestBool x iFil s &&
                    dataTestBool x iFil s) (getFilters cmp)) as theFilterFun.
    remember (
                match intType x with
                | intActivity =>
                    filter (fun c2 : Cmp => canStartBool x1 c2 s)
                      (filter isActivityBool (getAllCmps a s))
                | intService =>
                    filter (fun c2 : Cmp => canStartBool x1 c2 s)
                      (filter isServiceBool (getAllCmps a s))
                | intBroadcast =>
                    filter (fun c2 : Cmp => canStartBool x1 c2 s)
                      (filter isBroadReceiverBool (getAllCmps a s))
                end) as theList.
    assert (In theX2 theList /\ theFilterFun theX2 = true).
    rewrite HeqtheX2.
    apply ifExistsFilter.
    exists x2.
    rewrite filter_In.

    split.
    rewrite HeqtheList.
    destruct (intType x);rewrite filter_In;destruct H4;destruct H4;destruct H4;rewrite <-H4 in *;split; try apply canStartCorrect;auto;rewrite filter_In;split;try apply inAppGetAllCmp;auto.

    rewrite HeqtheFilterFun.
    rewrite existsb_exists.
    destruct_conj H4.
    unfold getFilters.
    destruct (intType x);destruct H6;destruct H6;rewrite<- H6 in *;exists x3;split;auto;rewrite andb_true_iff;split;try rewrite andb_true_iff;try split;try apply actionTestCorrect;auto;try apply categoryTestCorrect;auto;try apply dataTestCorrect;auto.






    destruct H6.

    split.
    rewrite HeqtheList in H6.
    assert (isAppInstalled a s).
    apply ifInAppThenIsAppInstalled with (c:=x2);auto.
    apply getAllCmpInstalledInApp;auto. 


    destruct (intType x);rewrite filter_In in H6;destruct H6;
    rewrite filter_In in H6;destruct H6;auto.


    split.
    exists x0,x.
    split;auto.
    split;auto.
    split;auto.
    split;auto.

    rewrite HeqtheFilterFun in H7.
    rewrite existsb_exists in H7.
    destruct H7.
    destruct H7.
    exists x4.
    split.
    unfold getFilters in H7.
    unfold isActivityBool, isServiceBool, isBroadReceiverBool in  HeqtheList.
    rewrite HeqtheList in H6.
    destruct (intType x);rewrite filter_In in H6;destruct H6;rewrite filter_In in H6;destruct H6;destruct theX2;try discriminate H10.

    exists a0;split;auto.
    exists s0;split;auto.
    exists b;split;auto.

    rewrite andb_true_iff in H8.
    destruct H8.
    rewrite andb_true_iff in H8.
    destruct H8.
    split.
    apply actionTestCorrect with (s:=s);auto.
    split.
    apply categoryTestCorrect with (s:=s);auto.
    apply dataTestCorrect with (s:=s);auto.

    split.
    rewrite HeqtheList in H6.
    destruct (intType x);rewrite filter_In in H6;destruct H6;rewrite filter_In in H6;destruct H6;apply canStartCorrect;auto.

    unfold resolveIntent_post;simpl.
    unfold resolveImplicitToExplicitIntent.
    split;intros.
    elim(classic(idI i = idI i0));intros.
    right;auto.
    left.

    rewrite in_app_iff.
    left.
    rewrite filter_In.
    split;auto.
    simpl.
    destruct idInt_eq.
    contradiction.
    auto.



    assert ((hd (defaultiCmp, i)
           (filter
              (fun pair : iCmp * Intent =>
               if idInt_eq (idI i) (idI (snd pair)) then true else false)
              (sentIntents (state s)))) = (x0,x)).
    remember (fun pair : iCmp * Intent => if idInt_eq (idI i) (idI (snd pair)) then true else false) as otherFun.
    assert (exists x, In x (filter otherFun (sentIntents (state s)))).
    exists (x0,x).
    rewrite filter_In.
    split;auto.
    rewrite HeqotherFun.
    simpl.
    rewrite H.
    destruct idInt_eq;auto.
    apply ifExistsFilter with (dflt:= (defaultiCmp,i)) in H8.
    destruct H8.
    remember (hd (defaultiCmp, i) (filter otherFun (sentIntents (state s)))) as theOtherHead.
    rewrite HeqotherFun in H9.
    destruct theOtherHead.
    simpl in H9.
    destructVS sValid.
    assert (i0 = x0 /\ i1 = x).
    destruct idInt_eq in H9.
    rewrite H in e.
    apply sentIntentsCorrectVS;auto.
    discriminate H9.
    destruct H10.
    rewrite H10,H11;auto.
    rewrite H8.
    unfold chooseCmpId.
    rewrite<- remX2.



    split;intros.
    rewrite in_app_iff in H9.
    destruct H9.
    left.
    rewrite filter_In in H9.
    destruct H9.
    split;auto.
    simpl in H10.
    destruct idInt_eq in H10.
    rewrite negb_true_iff in H10.
    inversion H10.
    auto.

    right.
    rewrite in_map_iff in H9.
    destruct H9.
    destruct H9.
    destruct x4;simpl in *.
    exists i2.
    unfold chooseCmpId in H9.
    
    inversion H9.
    rewrite H12 in *.
    rewrite filter_In in H10.
    destruct H10.
    split;auto.
    simpl in H11.
    destruct idInt_eq in H11;try discriminate H11.
    split;auto.
    unfold overrideIntentName;simpl.
    split;auto.
    split.
    auto.

    repeat split;auto.

    exists (overrideIntentName i0 (getCmpId theX2)).
    split.
    rewrite in_app_iff.
    right.
    rewrite in_map_iff.
    exists (ic, i0).
    simpl.
    split;auto.
    rewrite filter_In.
    split;auto.
    simpl.
    rewrite H10.
    destruct idInt_eq;auto.
    unfold overrideIntentName;simpl.
    repeat split;auto.

    unfold resolveIntent_post;simpl.
    repeat split;auto.
Qed.

    
Lemma notPreResolveIntentThenError : forall (s:System) (i:Intent) (a:idApp), ~(pre (resolveIntent i a) s) -> validstate s -> exists ec : ErrorCode, response (step s (resolveIntent i a)) = error ec /\ ErrorMsg s (resolveIntent i a) ec /\ s = system (step s (resolveIntent i a)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_resolveIntent in H.
    exists no_such_intt.
    assert (resolveIntent_pre i a s=Some no_such_intt).
    unfold resolveIntent_pre.
    dontcare (negb (isAppInstalledBool a s)).
    rewrite negb_false_iff in H1.
    rewrite <-isAppInstalled_iff in H1.
    assert (existsb (fun pair : iCmp * Intent => negb (isSomethingBool idCmp (cmpName (snd pair))) && (if idInt_eq (idI (snd pair)) (idI i) then true else false) && match map_apply iCmp_eq (running (state s)) (fst pair) with | Value _ c1 => existsb (fun iFil : intentFilter => actionTestBool (snd pair) iFil s && categoryTestBool (snd pair) iFil s && dataTestBool (snd pair) iFil s) (MyList.concat (map getFilters match intType (snd pair) with | intActivity => filter (fun c2 : Cmp => canStartBool c1 c2 s) (filter isActivityBool (getAllCmps a s)) | intService => filter (fun c2 : Cmp => canStartBool c1 c2 s) (filter isServiceBool (getAllCmps a s)) | intBroadcast => filter (fun c2 : Cmp => canStartBool c1 c2 s) (filter isBroadReceiverBool (getAllCmps a s)) end)) | Error _ _ => false end) (sentIntents (state s))=false).
    rewrite<- not_true_iff_false.
    unfold not;intros.
    apply H.
    rewrite existsb_exists in H2.
    destruct H2.
    destruct H2.
    destruct x.
    simpl in H3.
    exists i1.
    rewrite andb_true_iff in H3.
    destruct H3.
    rewrite andb_true_iff in H3.
    destruct H3.
    split.
    destruct idInt_eq in H5; auto.
    discriminate H5.
    split.
    destruct (cmpName i1).
    simpl in H3.
    discriminate H3.
    auto.
    exists i0.
    case_eq (map_apply iCmp_eq (running (state s)) i0);intros;rewrite H6 in H4.
    split;auto.
    rewrite existsb_exists in H4.
    destruct H4.
    exists c.
    split;auto.
    destruct H4.
    clear H.
    rewrite in_concat in H4.
    destruct H4.
    destruct H.
    rewrite in_map_iff in H.
    destruct H.
    exists x1.
    destruct H.
    destruct (intType i1);rewrite filter_In in H8;destruct H8;rewrite filter_In in H8;destruct H8;split;try apply getAllCmpInstalledInApp;auto;split; unfold getFilters in H.
    
    exists x.
    destruct x1;simpl in H10;try discriminate H10.
    split.
    exists a0.
    rewrite H.
    auto.
    rewrite andb_true_iff in H7.
    destruct H7.
    rewrite andb_true_iff in H7.
    destruct H7.
    rewrite <-actionTestCorrect in H7;auto.
    rewrite <-categoryTestCorrect in H12;auto.
    rewrite <-dataTestCorrect in H11;auto.
    apply canStartCorrect;auto.
    
    exists x.
    destruct x1;simpl in H10;try discriminate H10.
    split.
    exists s0.
    rewrite H.
    auto.
    rewrite andb_true_iff in H7.
    destruct H7.
    rewrite andb_true_iff in H7.
    destruct H7.
    rewrite <-actionTestCorrect in H7;auto.
    rewrite <-categoryTestCorrect in H12;auto.
    rewrite <-dataTestCorrect in H11;auto.
    apply canStartCorrect;auto.
    
    exists x.
    destruct x1;simpl in H10;try discriminate H10.
    split.
    exists b.
    rewrite H.
    auto.
    rewrite andb_true_iff in H7.
    destruct H7.
    rewrite andb_true_iff in H7.
    destruct H7.
    rewrite <-actionTestCorrect in H7;auto.
    rewrite <-categoryTestCorrect in H12;auto.
    rewrite <-dataTestCorrect in H11;auto.
    apply canStartCorrect;auto.
    discriminate H4.
    rewrite H2;auto.
    unfold resolveIntent_safe.
    rewrite H1.
    simpl.
    auto.
Qed.
    




Lemma resolveIntentIsSound : forall (s:System) (i:Intent) (a:idApp) (sValid: validstate s),
        exec s (resolveIntent i a) (system (step s (resolveIntent i a))) (response (step s (resolveIntent i a))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (resolveIntent i a) s));intro.
    left.
    simpl.
    assert(resolveIntent_pre i a s = None).
    unfold resolveIntent_pre.
    destruct H.
    destruct_conj H.
    assert ( (existsb (fun pair : iCmp * Intent => negb (isSomethingBool idCmp (cmpName (snd pair))) && (if idInt_eq (idI (snd pair)) (idI i) then true else false) && match map_apply iCmp_eq (running (state s)) (fst pair) with | Value _ c1 => existsb (fun iFil : intentFilter => actionTestBool (snd pair) iFil s && categoryTestBool (snd pair) iFil s && dataTestBool (snd pair) iFil s) (MyList.concat (map getFilters match intType (snd pair) with | intActivity => filter (fun c2 : Cmp => canStartBool c1 c2 s) (filter isActivityBool (getAllCmps a s)) | intService => filter (fun c2 : Cmp => canStartBool c1 c2 s) (filter isServiceBool (getAllCmps a s)) | intBroadcast => filter (fun c2 : Cmp => canStartBool c1 c2 s) (filter isBroadReceiverBool (getAllCmps a s)) end)) | Error _ _ => false end) (sentIntents (state s)))=true).
    rewrite existsb_exists.
    destruct H2.
    exists (x0,x).
    destruct H1.
    split;auto.
    unfold isSomethingBool.
    simpl.
    rewrite H.
    destruct idInt_eq.
    destruct H2.
    destruct H2.
    rewrite H2.
    rewrite andb_true_l.
    rewrite existsb_exists.
    destruct H3.
    destruct H3.
    destruct H4.
    destruct H4.
    exists x3.
    split.
    rewrite in_concat.
    destruct_conj H4.
    case_eq (intType x);intros; rewrite H8 in H6; destruct H6; destruct H6.
    
    exists (intFilterA x4).
    split;auto.
    rewrite in_map_iff.
    exists x2.
    split.
    unfold getFilters.
    rewrite<- H6.
    auto.
    rewrite filter_In.
    split;auto.
    unfold intTypeEqBool.
    assert (negb true=false).
    rewrite negb_false_iff.
    auto.
    rewrite filter_In.
    unfold isActivityBool.
    rewrite<- H6.
    split;auto.
    rewrite H6.
    apply inAppGetAllCmp;auto.
    apply canStartCorrect;auto.
    
    exists (intFilterS x4).
    split;auto.
    rewrite in_map_iff.
    exists x2.
    split.
    unfold getFilters.
    rewrite<- H6.
    auto.
    rewrite filter_In.
    split;auto.
    unfold intTypeEqBool.
    assert (negb true=false).
    rewrite negb_false_iff.
    auto.
    rewrite filter_In.
    unfold isActivityBool.
    rewrite<- H6.
    split;auto.
    rewrite H6.
    apply inAppGetAllCmp;auto.
    apply canStartCorrect;auto.
    
    exists (intFilterB x4).
    split;auto.
    rewrite in_map_iff.
    exists x2.
    split.
    unfold getFilters.
    rewrite<- H6.
    auto.
    rewrite filter_In.
    split;auto.
    unfold intTypeEqBool.
    assert (negb true=false).
    rewrite negb_false_iff.
    auto.
    rewrite filter_In.
    unfold isActivityBool.
    rewrite<- H6.
    split;auto.
    rewrite H6.
    apply inAppGetAllCmp;auto.
    apply canStartCorrect;auto.
    
    
    destruct_conj H4.
    assert (actionTestBool x x3 s=true).
    apply actionTestCorrect;auto.
    assert (categoryTestBool x x3 s=true).
    apply categoryTestCorrect;auto.
    assert (dataTestBool x x3 s=true).
    apply dataTestCorrect;auto.
    rewrite H8.
    rewrite H10.
    rewrite H11.
    auto.
    symmetry in H0.
    contradiction.
    rewrite H1.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H3.
    destruct H4.
    destruct H4.
    assert (negb (isAppInstalledBool a s)=false).
    rewrite negb_false_iff.
    apply isAppInstalled_iff.
    clear H1 H5.
    unfold inApp in H4.
    destruct H4.
    destruct H1.
    unfold isAppInstalled.
    destruct H1.
    left.
    apply (ifManifestThenInApps s sValid a x3);auto.
    right.
    destruct H1.
    destruct_conj H1.
    exists x4.
    auto.
    rewrite H6;auto.
    
    unfold resolveIntent_safe;simpl.
    rewrite H0;simpl.
    split;auto.
    split;auto.
    apply resolveIntentCorrect;auto.
    right.
    apply notPreResolveIntentThenError;auto.
    
Qed.
End ResolveIntent.
