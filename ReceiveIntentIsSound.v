(* En este archivo se demuestra la corrección de la acción receiveIntent *)
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

Section ReceiveIntent.

Lemma receiveIntentCorrect : forall (s:System) (i:Intent) (ic:iCmp) (a:idApp) (sValid: validstate s),
    (pre (receiveIntent i ic a) s) -> post_receiveIntent i ic a s (receiveIntent_post i ic a s).
Proof.
    intros.
    unfold post_receiveIntent.
    simpl in H.
    unfold pre_receiveIntent in H;simpl in H.
    destruct H.
    destruct_conj H.
    assert (maybeIntentForAppCmp i a ic s = Some x) as maybeintent.
    apply inttForAppMaybeIntt;auto.
    remember (iCmpGenerator (map_getKeys (running (state s)))) as theIC.
    destruct H2.
    destruct_conj H1.
    split.
    exists theIC.
    exists x.
    split;auto.
    split;auto.
    
    
    assert (~In theIC (map_getKeys (running (state s)))).
    rewrite HeqtheIC.
    apply generatorWorksWell.
    split.
    unfold insNotInState;intros.
    unfold not;intros.
    case_eq (map_apply iCmp_eq (running (state s)) theIC);intros.
    apply H5.
    rewrite valueIffExists in H8.
    unfold map_getKeys.
    rewrite in_map_iff.
    exists {| item_index := theIC; item_info := c |}.
    split;auto.
    apply (runningCorrect);auto.
    rewrite H8 in H7.
    unfold is_Value in H7.
    apply H7.
    split.
    unfold receiveIntent_post.
    unfold runCmp.
    rewrite maybeintent.
    split;intros.
    simpl.
    unfold performRunCmp.
    assert (theIC <> ic').
    unfold not;intros.
    apply H5.
    unfold map_getKeys.
    rewrite in_map_iff.
    rewrite valueIffExists in H7.
    exists {| item_index := ic'; item_info := c' |}.
    simpl.
    auto.
    apply (runningCorrect);auto.
    
    rewrite<- H7.
    simpl.
    apply overrideNotEq.
    rewrite<- HeqtheIC.
    auto.
    split;intros.
    simpl in H7.
    rewrite<- HeqtheIC in H7.
    unfold performRunCmp in H7.
    elim (classic (theIC = ic'));intros.
    right.
    split;auto.
    rewrite H8 in H7.
    symmetry in H7.
    rewrite <-addAndApply in H7.
    inversion H7.
    auto.
    left.
    rewrite overrideNotEq in H7.
    auto.
    auto.
    
    simpl.
    unfold performRunCmp.
    rewrite<- HeqtheIC.
    split.
    symmetry.
    apply addAndApply.
    
    apply addPreservesCorrectness.
    apply runningCorrect;auto.
    
    
    case_eq (intType i);intros.
    split;intros.
    specialize (H4 H7).
    case_eq (path (data i));intros.
    left.
    exists u.
    specialize (H4 u H9).
    destruct H4.
    remember (getAnyCProviderWithUri u s) as theCP.
    
    exists theCP.
    destruct H4.
    split;auto.
    split;auto.
    unfold getAnyCProviderWithUri in HeqtheCP.
    remember (fun cp : CProvider => existsResBool cp u s) as theFun.
    assert (In theCP (getSomes Cmp CProvider (fun cmp : Cmp => match cmp with | cmpAct _ => None | cmpSrv _ => None | cmpCP cp => Some cp | cmpBR _ => None end) (getAllComponents s)) /\ theFun theCP =true).
    rewrite HeqtheCP.
    apply ifExistsFilter.
    exists x1.
    rewrite filter_In.
    split.
    apply inGetSomes.
    exists (cmpCP x1).
    split;auto.
    destruct H4.
    destruct H4.
    apply getAllComponentsIffInApp;auto.
    exists x2.
    auto.
    rewrite HeqtheFun.
    apply existsRes_iff;auto.
    destruct H11.
    rewrite HeqtheFun in H12.
    apply existsRes_iff;auto.
    
    unfold grantTempPerm.
    unfold receiveIntent_post.
    rewrite maybeintent.
    rewrite H7.
    rewrite H9.
    simpl.
    unfold performGrantTempPerm.
    rewrite<-HeqtheIC.
    split;intros.
    split;intros.
    
    assert (theIC <> ic').
    unfold not;intros.
    assert (exists c, map_apply iCmp_eq (running (state s)) ic' = Value iCmp c).
    apply (ifDelTPermsThenRunning s sValid ic' cp' u' pt');auto.
    destruct H13.
    apply H5.
    unfold map_getKeys.
    rewrite in_map_iff.
    exists {| item_index := ic'; item_info := x2 |}.
    simpl.
    split;auto.
    rewrite<- valueIffExists.
    exact H13.
    apply (runningCorrect);auto.
    
    rewrite overrideNotEq.
    auto.
    unfold not;intros.
    apply H12.
    inversion H13.
    auto.
    
    split;intros.
    
    elim (classic (theIC = ic' /\ theCP = cp' /\ u = u'));intros.
    right.
    destruct_conj H12.
    rewrite H13 in H11.
    rewrite <-H12 in H11.
    rewrite HeqtheCP in H11.
    rewrite H15 in H11.
    rewrite <-addAndApply in H11.
    inversion H11.
    auto.
    left.
    rewrite overrideNotEq in H11.
    auto.
    unfold not;intros.
    apply H12.
    rewrite HeqtheCP.
    inversion H13.
    auto.
    rewrite HeqtheCP.
    rewrite<- addAndApply.
    auto.
    apply addPreservesCorrectness.
    apply delTPermsCorrect;auto.
    
    
    right.
    split;auto.
    
    unfold receiveIntent_post.
    rewrite maybeintent.
    rewrite H9.
    simpl.
    rewrite H7.
    auto.
    split;intros;discriminate H8.
    split;intros.
    discriminate H8.
    split;intros.
    
    
    unfold receiveIntent_post.
    rewrite maybeintent.
    simpl.
    rewrite H7.
    auto.
    discriminate H8.
    split;intros.
    discriminate H8.
    split;intros.
    discriminate H8.
    
    
    unfold receiveIntent_post.
    rewrite maybeintent.
    simpl.
    rewrite H7.
    auto.
    
    split.
    unfold removeIntent.
    unfold receiveIntent_post.
    rewrite maybeintent.
    simpl.
    split;intros.
    rewrite <-removeSthElse in H5.
    destruct H5.
    auto.
    split;intros.
    elim (classic ((ic',i') = (ic,i)));intros.
    right.
    inversion H7;auto.
    left.
    apply removeSthElse.
    auto.
    rewrite<- removeSthElse.
    unfold not;intros.
    destruct H5.
    apply H5;auto.
    
    unfold receiveIntent_post.
    rewrite maybeintent.
    simpl.
    repeat (split;auto).
Qed.


Lemma notPreReceiveIntentThenError : forall (s:System) (i:Intent) (ic:iCmp) (a:idApp), ~(pre (receiveIntent i ic a) s) -> validstate s -> exists ec : ErrorCode, response (step s (receiveIntent i ic a)) = error ec /\ ErrorMsg s (receiveIntent i ic a) ec /\ s = system (step s (receiveIntent i ic a)).
Proof.
    intros.
    simpl.
    simpl in H.
    unfold pre_receiveIntent in H.
    unfold receiveIntent_safe.
    unfold receiveIntent_pre.
    case_eq (maybeIntentForAppCmp i a ic s);intros. 
    case_eq (isCProviderBool c);intros.
    exists cmp_is_CProvider.
    split;auto.
    split;auto.
    exists c.
    apply inttForAppMaybeInttBack in H1;auto.
    apply isCProviderBool_iff in H2.
    split;auto.

    case_eq (map_apply iCmp_eq (running (state s)) ic);intros.
    case_eq (isCProviderBool c0);intros.
    exists cmp_is_CProvider.
    split;auto.
    split;auto.
    exists c0.
    apply isCProviderBool_iff in H4.
    split;auto.

    case_eq (negb (canStartBool c0 c s));intros.
    exists a_cant_start_b.
    split;auto.
    split;auto.
    exists c,c0.
    apply inttForAppMaybeInttBack in H1;auto.
    split;auto.
    split;auto.
    rewrite negb_true_iff in H5.
    invertBool H5.
    intro.
    apply H5.
    apply canStartCorrect;auto.

    destruct (intType i).
    destruct (path (data i)).
    case_eq (existsb (receiveIntentCmpRequirements c0 u s (intentActionType i)) (getAllComponents s));intros.
    destruct H.
    exists c.

    split.
    apply inttForAppMaybeInttBack in H1;auto.

    split.
    invertBool H2.
    intro.
    apply H2.
    apply isCProviderBool_iff;auto.

    exists c0.
    split;auto.

    split.
    invertBool H4.
    intro.
    apply H4.
    apply isCProviderBool_iff;auto.

    split.
    rewrite negb_false_iff in H5.
    apply canStartCorrect;auto.
    split;intros.

    rewrite existsb_exists in H6.
    destruct H6.
    destruct H6.
    unfold receiveIntentCmpRequirements in H8.
    destruct x;try discriminate H8.
    exists c1.
    rewrite andb_true_iff in H8.
    destruct H8.
    rewrite andb_true_iff in H8.
    destruct H8.
    inversion H7.
    rewrite <- H12 in *.
    split.
    apply existsRes_iff;auto.
    split.
    apply canGrantCorrect;auto.
    unfold canRead.
    unfold canWrite.
    unfold canReadBool in H9.
    unfold canWriteBool in H9.
    destruct (intentActionType i); try rewrite orb_true_iff in H9.
    destruct H9.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    destruct H9.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.

    rewrite andb_true_iff in H9.
    destruct H9.
    split.
    rewrite orb_true_iff in H9.
    destruct H9.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    rewrite orb_true_iff in H11.
    destruct H11.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    destruct H.
    discriminate H.

    exists no_CProvider_fits.
    split;auto.
    split;auto.
    exists c0.
    split;auto.
    split;auto.
    assert (H7:=True).
    intros.
    inversion H8.
    rewrite <-H10 in *.
    invertBool H6.
    intro.
    apply H6.
    destruct H9.
    destruct_conj H9.
    rewrite existsb_exists.
    exists (cmpCP x).
    split.
    unfold existsRes in H11.
    destruct H11.
    destruct H11.
    apply getAllComponentsIffInApp;auto.
    exists x0;auto.
    unfold receiveIntentCmpRequirements.
    rewrite andb_true_iff.
    split.
    rewrite andb_true_iff.
    split.
    apply existsRes_iff;auto.
    apply canGrantCorrect;auto.
    unfold canRead in H13.
    unfold canWrite in H13.
    unfold canReadBool.
    unfold canWriteBool.
    destruct (intentActionType i).
    rewrite orb_true_iff.
    destruct H13.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    rewrite orb_true_iff.
    destruct H13.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    rewrite andb_true_iff.
    destruct H13.
    split;rewrite orb_true_iff.
    destruct H12.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.
    destruct H13.
    left.
    apply canDoThisBoolCorrect;auto.
    right.
    apply delPermsBoolCorrect;auto.

    destruct H.
    exists c.

    split.
    apply inttForAppMaybeInttBack in H1;auto.

    split.
    invertBool H2.
    intro.
    apply H2.
    apply isCProviderBool_iff;auto.

    exists c0.
    split;auto.

    split.
    invertBool H4.
    intro.
    apply H4.
    apply isCProviderBool_iff;auto.

    split.
    rewrite negb_false_iff in H5.
    apply canStartCorrect;auto.
    split;intros.
    discriminate H6.
    destruct H.
    discriminate H.


    destruct H.
    exists c.

    split.
    apply inttForAppMaybeInttBack in H1;auto.

    split.
    invertBool H2.
    intro.
    apply H2.
    apply isCProviderBool_iff;auto.

    exists c0.
    split;auto.

    split.
    invertBool H4.
    intro.
    apply H4.
    apply isCProviderBool_iff;auto.

    split.
    rewrite negb_false_iff in H5.
    apply canStartCorrect;auto.
    split;intros.
    discriminate H.
    destruct H.
    discriminate H.

    destruct (brperm i).
    case_eq (appHasPermissionBool a p s);intro.
    destruct H.
    exists c.

    split.
    apply inttForAppMaybeInttBack in H1;auto.

    split.
    invertBool H2.
    intro.
    apply H2.
    apply isCProviderBool_iff;auto.

    exists c0.
    split;auto.

    split.
    invertBool H4.
    intro.
    apply H4.
    apply isCProviderBool_iff;auto.

    split.
    rewrite negb_false_iff in H5.
    apply canStartCorrect;auto.
    split;intros.
    discriminate H.
    destruct H.
    exists p.
    rewrite <-appHasPermissionCorrect in H6;auto.
    exists not_enough_permissions.
    split;auto.
    split;auto.
    split;auto.
    split;auto.
    unfold not.
    intros.
    inversion H7.
    exists p.
    split;auto.
    invertBool H6.
    intro.
    apply H6.
    apply appHasPermissionCorrect;auto.

    destruct H.
    exists c.

    split.
    apply inttForAppMaybeInttBack in H1;auto.

    split.
    invertBool H2.
    intro.
    apply H2.
    apply isCProviderBool_iff;auto.

    exists c0.
    split;auto.

    split.
    invertBool H4.
    intro.
    apply H4.
    apply isCProviderBool_iff;auto.

    split.
    rewrite negb_false_iff in H5.
    apply canStartCorrect;auto.
    split;intros.
    discriminate H.
    destruct H.
    destruct H6;auto.
    exists instance_not_running.
    split;auto.
    exists no_such_intt.
    split;auto.
    split;auto.
    intro.
    destruct H2.
    apply inttForAppMaybeIntt in H2;auto.
    rewrite H2 in H1.
    discriminate H1.
Qed.

Lemma receiveIntentIsSound : forall (s:System) (i:Intent) (ic:iCmp) (a:idApp) (sValid: validstate s),
        exec s (receiveIntent i ic a) (system (step s (receiveIntent i ic a))) (response (step s (receiveIntent i ic a))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    elim (classic (pre (receiveIntent i ic a) s));intro.
    left.
    simpl.
    assert(receiveIntent_pre i ic a s = None).
    unfold receiveIntent_pre.
    destruct H.
    destruct_conj H.
    assert (maybeIntentForAppCmp i a ic s = Some x) as maybeintent.
    apply inttForAppMaybeIntt;auto.
    rewrite maybeintent.
    rewrite isCProviderBool_iff in H.
    rewrite not_true_iff_false in H.
    rewrite H.
    destruct H2.
    destruct_conj H1.
    rewrite H2.
    rewrite isCProviderBool_iff in H1.
    rewrite not_true_iff_false in H1.
    rewrite H1.
    assert (canStartBool x0 x s = true).
    apply canStartCorrect;auto.
    rewrite H5.
    assert (negb true=false).
    rewrite negb_false_iff.
    auto.
    rewrite H7.
    case_eq (intType i);intros.
    case_eq (path (data i));intros.
    assert (existsb (receiveIntentCmpRequirements x0 u s (intentActionType i)) (getAllComponents s)=true).
    rewrite existsb_exists.
    specialize (H4 H8 u H9).
    destruct H4.
    destruct_conj H4.
    exists (cmpCP x1).
    unfold receiveIntentCmpRequirements.
    split.
    unfold getAllComponents.
    destruct H10.
    destruct H10.
    destruct H10.
    rewrite in_concat.
    exists (cmp x3).
    rewrite in_app_iff.
    destruct H10.
    split;auto.
    destruct H10.
    left.
    rewrite in_map_iff.
    exists x3.
    split;auto.
    apply inGetValuesBack.
    exists (Value idApp x3).
    split;auto.
    rewrite in_map_iff.
    exists x2.
    split;auto.
    apply (ifManifestThenInApps s sValid x2 x3);auto.
    right.
    rewrite in_map_iff.
    destruct H10.
    destruct_conj H10.
    exists x4.
    rewrite H16.
    auto.
    assert (existsResBool x1 u s = true).
    apply existsRes_iff;auto.
    assert (canGrantBool x1 u s=true).
    apply canGrantCorrect;auto.
    unfold canReadBool.
    unfold canWriteBool.
    unfold canRead in H12.
    unfold canWrite in H12.
    rewrite H11.
    rewrite H13.
    case_eq (intentActionType i);intros; rewrite H14 in H12;destruct H12.
    assert (canDoThisBool x0 x1 s readE=true).
    apply canDoThisBoolCorrect;auto.
    rewrite H15;auto.
    assert (delPermsBool x0 x1 u Read s=true).
    apply delPermsBoolCorrect;auto.
    rewrite H15;auto.
    rewrite orb_true_r.
    auto.
    
    assert (canDoThisBool x0 x1 s writeE=true).
    apply canDoThisBoolCorrect;auto.
    rewrite H15;auto.
    assert (delPermsBool x0 x1 u Write s=true).
    apply delPermsBoolCorrect;auto.
    rewrite H15;auto.
    rewrite orb_true_r.
    auto.
    
    destruct H12.
    assert (canDoThisBool x0 x1 s readE=true).
    apply canDoThisBoolCorrect;auto.
    rewrite H16;auto.
    
    destruct H15.
    assert (canDoThisBool x0 x1 s writeE=true).
    apply canDoThisBoolCorrect;auto.
    rewrite H17;auto.
    assert (delPermsBool x0 x1 u Write s=true).
    apply delPermsBoolCorrect;auto.
    rewrite H17;auto.
    rewrite orb_true_r.
    auto.
    
    destruct H15.
    assert (canDoThisBool x0 x1 s writeE=true).
    apply canDoThisBoolCorrect;auto.
    rewrite H16;auto.
    assert (delPermsBool x0 x1 u Read s=true).
    apply delPermsBoolCorrect;auto.
    rewrite H17;auto.
    rewrite orb_true_r.
    auto.
    
    
    assert (delPermsBool x0 x1 u Read s=true).
    apply delPermsBoolCorrect;auto.
    rewrite H16;auto.
    rewrite orb_true_r.
    auto.
    assert (delPermsBool x0 x1 u Write s=true).
    apply delPermsBoolCorrect;auto.
    rewrite H17;auto.
    rewrite orb_true_r.
    auto.
    
    rewrite H10.
    auto.
    auto.
    auto.
    case_eq (brperm i);intros.
    assert (appHasPermissionBool a p s=true).
    assert (exists p : Perm, brperm i = Some p /\ RuntimePermissions.appHasPermission a p s).
    apply H6.
    split;auto.
    unfold not;intros.
    rewrite H9 in H10.
    inversion H10.
    destruct H10.
    destruct H10.
    rewrite H10 in H9.
    inversion H9.
    rewrite H13 in H11.
    apply appHasPermissionCorrect;auto.
    rewrite H10;auto.
    auto.
    
    unfold receiveIntent_safe;simpl.
    rewrite H0;simpl.
    split;auto.
    split;auto.
    apply receiveIntentCorrect;auto.
    right.
    apply notPreReceiveIntentThenError;auto.
    
Qed.
End ReceiveIntent.
