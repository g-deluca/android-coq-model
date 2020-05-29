(* En este archivo se prueban lemas auxiliares que son 
 * utilizados para demostrar la corrección de la implementación
 * y las propiedades postuladas *)
Require Import Implementacion.
Require Import DefBasicas.
Require Import EqTheorems.
Require Import Estado.
Require Import Semantica.
Require Import Maps.
Require Import MyList.
Require Import Coq.Lists.List.
Require Import Classical.
Require Import Tacticas.
Require Import RuntimePermissions.
Require Import ListAuxFuns.
Require Import ValidStateLemmas.
Require Import Omega.

Section AuxLemmas.

Lemma addAllPreservesCorrectness : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (indexAndVals:list (index*values)) (mp:mapping index values), map_correct mp -> map_correct (addAll index values indexeq indexAndVals mp).
Proof.
    intros.
    unfold addAll.
    induction indexAndVals.
    simpl.
    auto.
    simpl.
    apply addPreservesCorrectness.
    auto.
Qed.


Lemma dropAllPreservesCorrectness : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (indexes:list index) (mp:mapping index values), map_correct mp -> map_correct (dropAll index values indexeq indexes mp).
Proof.
    intros.
    unfold dropAll.
    induction indexes.
    simpl.
    auto.
    simpl.
    apply dropPreservesCorrectness.
    auto.
Qed.

Lemma notInAddAll : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (indexAndVals:list (index*values)) (mp:mapping index values) (idx:index), ~(In idx (map (fun pair=>fst pair) indexAndVals)) -> map_apply indexeq (addAll index values indexeq indexAndVals mp) idx = map_apply indexeq mp idx.
Proof.
    intros.
    unfold addAll.
    induction indexAndVals.
    simpl.
    auto.
    simpl.
    assert (~(In idx (map (fun pair : index * values => fst pair) indexAndVals)) /\ (idx<>fst a)).
    split;unfold not;intros;apply H.
    apply in_cons;auto.
    rewrite H0.
    apply in_eq;auto.
    destruct H0.
    rewrite overrideNotEq.
    apply IHindexAndVals.
    auto.
    auto.
Qed.


Lemma notValueThenOverriden : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (indexAndVals:list (index*values)) (theVal:values) (mp:mapping index values) (idx:index), ~ is_Value (map_apply indexeq mp idx) -> map_apply indexeq (addAll index values indexeq indexAndVals mp) idx = Value index theVal -> (exists n, nth_error indexAndVals n = Some (idx,theVal)).
Proof.
    intros.
    unfold addAll in H0.
    induction indexAndVals.
    simpl in H0.
    rewrite H0 in H.
    simpl in H.
    absurd True; auto.
    simpl in H0.
    elim (classic (fst a=idx));intros.
    rewrite H1 in H0.
    rewrite <-addAndApply in H0.
    inversion H0.
    inversion H1.
    apply In_nth_error.
    case_eq a;intros.
    simpl.
    left;auto.
    rewrite overrideNotEq in H0.
    assert ( exists n : nat, nth_error indexAndVals n = Some (idx, theVal)).
    apply IHindexAndVals;auto.
    destruct H2.
    exists (S x).
    simpl.
    auto.
    auto.
Qed.

Lemma inAddAll : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (indexAndVals:list (index*values)) (mp:mapping index values) (val:values) (idx:index), hd_error (filter (fun pair => If indexeq (fst pair) idx then true else false) indexAndVals) = Some (idx,val) -> map_apply indexeq (addAll index values indexeq indexAndVals mp) idx = Value index val.
Proof.
    intros.
    unfold addAll.
    induction indexAndVals.
    inversion H.
    simpl.
    simpl in H.
    destruct indexeq in H;simpl in H.
    assert (snd a=val).
    inversion H.
    simpl;auto.
    rewrite H0.
    rewrite e.
    symmetry.
    apply addAndApply.
    rewrite overrideNotEq.
    apply IHindexAndVals;auto.
    auto.
Qed.

Lemma valueDropThenValue : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (indexes:list index) (mp:mapping index values) (theVal:values) (idx:index), map_apply indexeq (dropAll index values indexeq indexes mp) idx = Value index theVal <-> map_apply indexeq mp idx = Value index theVal /\ ~(In idx indexes).
Proof.
    unfold dropAll.
    split;intros; induction indexes.
    simpl in H.
    split;auto.
    simpl in H.
    elim (classic (a=idx));intros.
    rewrite H0 in H.
    assert (~(is_Value (map_apply indexeq (map_drop indexeq (fold_right (fun (i : index) (oldmap : mapping index values) => map_drop indexeq oldmap i) mp indexes) idx) idx))).
    apply valueDropNotValue.
    rewrite H in H1.
    simpl in H1.
    absurd True;auto.
    rewrite valueDropValue in H.
    destruct H.
    specialize (IHindexes H).
    destruct IHindexes.
    split;auto.
    unfold not;intros.
    inversion H4; contradiction.
    destruct H.
    
    simpl.
    auto.
    simpl.
    destruct H.
    assert (a<>idx).
    unfold not;intros.
    apply H0.
    rewrite H1.
    apply in_eq.
    apply valueDropValue.
    split;auto.
    apply IHindexes.
    split;auto.
    unfold not;intros.
    apply H0.
    apply in_cons;auto.
Qed.

Lemma valueDropAllNotValue : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (indexes:list index) (mp:mapping index values) (idx:index), In idx indexes -> ~(is_Value (map_apply indexeq (dropAll index values indexeq indexes mp) idx)).
Proof.
    intros.
    unfold not;intros.
    unfold is_Value in H0.
    case_eq ( map_apply indexeq (dropAll index values indexeq indexes mp) idx);intros.
    rewrite valueDropThenValue in H1.
    destruct H1.
    contradiction.
    rewrite H1 in H0.
    auto.
Qed.


Lemma dropNotIn : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (indexes:list index) (mp:mapping index values) (idx:index), ~(In idx indexes) -> map_apply indexeq (dropAll index values indexeq indexes mp) idx = map_apply indexeq mp idx.
Proof.
    intros.
    induction indexes.
    simpl.
    auto.
    simpl.
    assert (~In idx indexes).
    unfold not;intros.
    apply H.
    apply in_cons;auto.
    specialize (IHindexes H0).
    rewrite <-IHindexes.
    symmetry.
    apply dropSthElse.
    unfold not;intros.
    apply H.
    rewrite H1.
    apply in_eq.
Qed.

Lemma notImpliesAndNot : forall (A B:Prop), ~(A->B) -> A /\ ~B.
Proof.
    intros.
    split.
    apply NNPP.
    unfold not;intro.
    apply H.
    intro.
    absurd A; auto.
    unfold not;intro.
    apply H.
    intro.
    auto.
Qed.

   
Lemma ptplus_commutes: forall (pt pt':PType), ptplus pt pt' = ptplus pt' pt.
Proof.
    intros.
    unfold ptplus.
    case_eq pt;intros;case_eq pt';intros; auto.
Qed.

Lemma isAppInstalled_iff: forall (a:idApp) (s:System), isAppInstalled a s <-> isAppInstalledBool a s = true.
Proof.
    split;intro.
    destruct H.
    unfold isAppInstalledBool.
    unfold InBool.
    rewrite existsb_exists.
    exists a.
    split.
    rewrite in_app_iff.
    left.
    auto.
    destruct idApp_eq; auto.
    destruct H.
    unfold isAppInstalledBool.
    unfold InBool.
    rewrite existsb_exists.
    exists a.
    split.
    rewrite in_app_iff.
    right.
    rewrite in_map_iff.
    exists x.
    destruct H.
    split;auto.
    destruct idApp_eq; auto.
    unfold isAppInstalledBool in H.
    unfold InBool in H.
    rewrite existsb_exists in H.
    destruct H.
    unfold isAppInstalled.
    destruct H.
    rewrite in_app_iff in H.
    assert (a=x).
    destruct idApp_eq in H0;auto.
    discriminate H0.
    rewrite <- H1 in H.
    clear H0 H1.
    destruct H.
    left.
    auto.
    right.
    rewrite in_map_iff in H.
    destruct H.
    exists x0.
    destruct H.
    split;auto.
Qed.

Lemma ifInAppThenIsAppInstalled : forall (s:System) (sValid:validstate s) (c:Cmp) (a:idApp), inApp c a s -> isAppInstalled a s.
Proof.
    intros.
    unfold isAppInstalled.
    destruct H.
    destruct H.
    destruct H.
    left.
    apply (ifManifestThenInApps s sValid a x);auto.
    right.
    destruct H.
    destruct H.
    destruct H1.
    exists x0;auto.
Qed.

Lemma getAllComponentsIffInApp : forall (c:Cmp) (s:System) (sValid:validstate s), In c (getAllComponents s) <-> exists a:idApp, inApp c a s.
Proof.
    unfold getAllComponents.
    unfold inApp.
    split;intros.
    rewrite in_concat in H.
    destruct H.
    destruct H.
    rewrite in_app_iff in H.
    destruct H.
    rewrite in_map_iff in H.
    destruct H.
    destruct H.
    assert (exists y:exc Manifest idApp, In y (map (map_apply idApp_eq (manifest (environment s))) (apps (state s))) /\ y = Value idApp x0).
    apply inGetValues.
    auto.
    destruct H2.
    destruct H2.
    rewrite in_map_iff in H2.
    destruct H2.
    exists x2.
    exists x0.
    rewrite <-H in H0.
    split;auto.
    destruct H2.
    rewrite H3 in H2.
    left;auto.
    rewrite in_map_iff in H.
    destruct H.
    destruct H.
    exists (idSI x0).
    exists (manifestSI x0).
    rewrite <-H in H0.
    split;auto.
    right.
    exists x0.
    auto.
    
    destruct H.
    destruct H.
    rewrite in_concat.
    destruct H.
    destruct H.
    exists (cmp x0).
    rewrite in_app_iff.
    split;auto.
    left.
    rewrite in_map_iff.
    exists x0.
    split;auto.
    
    apply inGetValuesBack.
    exists ( map_apply idApp_eq (manifest (environment s)) x ).
    split;auto.
    rewrite in_map_iff.
    exists x.
    split;auto.
    apply (ifManifestThenInApps s sValid x x0);auto.
    destruct H.
    destruct_conj H.
    exists (cmp x0).
    rewrite in_app_iff.
    split;auto.
    right.
    rewrite in_map_iff.
    exists x1.
    rewrite H3.
    auto.
Qed.


Lemma cmpIdInStateBoolCorrect: forall (c:Cmp) (s:System) (sValid:validstate s), cmpNotInState c s <-> cmpIdInStateBool c s = false.
Proof.
    unfold cmpNotInState.
    unfold cmpIdInStateBool.
    split;intros.
    rewrite <-not_true_iff_false.
    unfold not;intro.
    rewrite existsb_exists in H0.
    destruct H0.
    destruct H0.
    rewrite in_map_iff in H0.
    destruct H0.
    destruct H0.
    assert (getCmpId c=x).
    destruct idCmp_eq in H1;auto.
    discriminate H1.
    rewrite <- H3 in H0.
    clear H3 x H1.
    unfold getAllComponents in H2.
    rewrite concat_app in H2.
    rewrite in_app_iff in H2.
    destruct H2;
    rewrite <- flat_map_concat_map in H1;
    rewrite in_flat_map in H1.
    destruct H1.
    destruct H1.
    assert (exists y, In y (map (map_apply idApp_eq (manifest (environment s)))
    (apps (state s))) /\ y=Value idApp x).
    apply inGetValues.
    auto.
    destruct H3.
    destruct H3.
    rewrite in_map_iff in H3.
    destruct H3.
    destruct H3.
    specialize (H x0 x2).
    destruct H.
    unfold inApp.
    exists x.
    split;auto.
    left.
    rewrite<- H4.
    auto.
    auto.
    destruct H1.
    destruct H1.
    specialize (H x0 (idSI x)).
    destruct H.
    unfold inApp.
    exists (manifestSI x).
    split;auto.
    right.
    exists x.
    auto.
    auto.
    
    unfold not;intros.
    rewrite <-not_true_iff_false in H.
    apply H.
    rewrite existsb_exists.
    exists (getCmpId c').
    split.
    rewrite in_map_iff.
    exists c'.
    split;auto.
    unfold getAllComponents.
    rewrite in_concat.
    destruct H0.
    destruct H0.
    exists (cmp x).
    rewrite in_app_iff.
    split;auto.
    destruct H0.
    left.
    rewrite in_map_iff.
    exists x.
    split;auto.
    apply inGetValuesBack.
    exists (Value idApp x).
    rewrite in_map_iff.
    split;auto.
    exists a.
    split;auto.
    apply (ifManifestThenInApps s sValid a x);auto.
    right.
    rewrite in_map_iff.
    destruct H0.
    destruct_conj H0.
    exists x0.
    rewrite H5.
    auto.
    destruct idCmp_eq;auto.
    
Qed.

Lemma isSystemPermBoolCorrect: forall p:Perm, isSystemPermBool p = false -> ~isSystemPermId p.
Proof.
    intros.
    unfold isSystemPermId.
    unfold not;intros.
    destruct H0.
    destruct H0.
    rewrite isSysPermCorrect in H0.
    unfold isSystemPermBool in H.
    unfold InBool in H.
    assert (existsb (fun a' : idPerm => if idPerm_eq (idP p) a' then true else false) (map idP systemPerms) = true).
    rewrite existsb_exists.
    exists (idP x).
    split.
    rewrite in_map_iff.
    exists x.
    split;auto.
    rewrite H1.
    destruct idPerm_eq.
    auto.
    destruct n.
    auto.
    rewrite H in H2.
    discriminate H2.
Qed.


Lemma isSystemPermBoolCorrectBack: forall p:Perm, ~isSystemPermId p -> isSystemPermBool p = false.
Proof.
    intros.
    unfold isSystemPermId in H.
    unfold isSystemPermBool.
    unfold InBool.
    rewrite <-not_true_iff_false.
    unfold not;intros.
    rewrite existsb_exists in H0.
    destruct H0.
    destruct H0.
    rewrite in_map_iff in H0.
    destruct H0.
    destruct H0.
    absurd (exists p' : Perm, isSystemPerm p' /\ idP p' = idP p).
    auto.
    exists x0.
    split.
    rewrite isSysPermCorrect.
    auto.
    destruct idPerm_eq in H1.
    rewrite H0.
    rewrite e.
    auto.
    discriminate H1.
Qed.

Lemma inUsrDefPermsIff : forall (p:Perm) (s:System) (sValid:validstate s), usrDefPerm p s <-> In p (usrDefPerms s).
Proof.
    unfold usrDefPerm.
    unfold usrDefPerms.
    split;intros.
    rewrite in_concat.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    exists x0.
    split;auto.
    rewrite in_app_iff.
    left.
    apply inGetValuesBack.
    exists (Value idApp x0).
    split;auto.
    rewrite in_map_iff.
    exists x.
    assert (In x (apps (state s))).
    apply (ifDefPermsThenInApps s sValid x x0);auto.
    auto.
    destruct H.
    destruct H.
    exists (defPermsSI x).
    split;auto.
    rewrite in_app_iff.
    right.
    rewrite in_map_iff.
    exists x.
    auto.
    
    rewrite in_concat in H.
    destruct H.
    destruct H.
    rewrite in_app_iff in H.
    destruct H.
    left.
    apply inGetValues in H.
    destruct H.
    destruct H.
    rewrite in_map_iff in H.
    destruct H.
    destruct H.
    exists x1.
    exists x.
    rewrite<- H1.
    auto.
    right.
    rewrite in_map_iff in H.
    destruct H.
    destruct H.
    exists x0.
    rewrite H.
    auto.
Qed.

Lemma authPermsBoolCorrect: forall (m:Manifest) (s:System) (sValid:validstate s), authPerms m s <-> authPermsBool m s = true.
Proof.
    unfold authPerms.
    unfold authPermsBool.
    split;intros.
    rewrite negb_true_iff.
    rewrite <-not_true_iff_false.
    unfold not;intros.
    rewrite existsb_exists in H0.
    destruct H0.
    destruct H0.
    unfold nonSystemUsrP in H0.
    rewrite filter_In in H0.
    destruct H0.
    specialize (H x H0).
    assert (~isSystemPermId x).
    rewrite negb_true_iff in H2.
    apply isSystemPermBoolCorrect.
    auto.
    specialize (H H3).
    
    rewrite existsb_exists in H1.
    destruct H1.
    destruct H1.
    apply H.
    exists x0.
    assert (usrDefPerm x0 s).
    apply inUsrDefPermsIff;auto.
    destruct idPerm_eq in H4.
    auto.
    discriminate H4.
    unfold not;intro.
    destruct H2.
    destruct H2.
    rewrite negb_true_iff in H.
    rewrite <-not_true_iff_false in H.
    apply H.
    rewrite existsb_exists.
    apply inUsrDefPermsIff in H2;auto.
    exists p.
    split.
    unfold nonSystemUsrP.
    rewrite filter_In.
    split;auto.
    rewrite negb_true_iff.
    apply isSystemPermBoolCorrectBack; auto.
    rewrite existsb_exists.
    exists x.
    split;auto.
    rewrite H3.
    destruct idPerm_eq;auto.
Qed.

Lemma isNilIffFalse : forall (A:Set) (l:list A), isNil A l = false <-> l<>nil.
Proof.
    split;intros.
    case_eq l;intros; rewrite H0 in H.
    unfold isNil in H;simpl in H.
    discriminate H.
    unfold not;intros.
    symmetry in H1.
    apply nil_cons in H1.
    auto.
    
    case_eq l;intros; rewrite H0 in H.
    destruct H.
    auto.
    unfold isNil.
    auto.
    
Qed.


Lemma isNilIffTrue : forall (A:Set) (l:list A), isNil A l = true <-> l=nil.
Proof.
    split;intros.
    assert (l<>nil->False);intros.
    rewrite<- isNilIffFalse in H0.
    rewrite H0 in H.
    discriminate H.
    apply NNPP.
    auto.
    
    case_eq l;intros.
    unfold isNil.
    auto.
    rewrite H0 in H;auto.
    discriminate H.
Qed.

Lemma definesIntentFilterCorrectlyBoolCorrect: forall c:Cmp, cmpDeclareIntentFilterCorrectly c <-> definesIntentFilterCorrectlyBool c = true.
Proof.
    unfold definesIntentFilterCorrectlyBool.
    unfold cmpDeclareIntentFilterCorrectly.
    split;intros.
    rewrite negb_true_iff.
    rewrite <-not_true_iff_false.
    unfold not;intros.
    rewrite existsb_exists in H0.
    destruct H0.
    destruct H0.
    rewrite andb_true_iff in H1.
    destruct H1.
    rewrite negb_true_iff in H1.
    rewrite andb_false_iff in H1.
    destruct c.
    
    specialize (H x H0).
    destruct H.
    destruct H1.
    left.
    apply isNilIffFalse.
    auto.
    right.
    apply isNilIffFalse.
    auto.
    apply isNilIffTrue.
    auto.
    
    
    specialize (H x H0).
    destruct H.
    destruct H1.
    left.
    apply isNilIffFalse.
    auto.
    right.
    apply isNilIffFalse.
    auto.
    apply isNilIffTrue.
    auto.
    
    apply in_nil in H0.
    auto.
    
    
    specialize (H x H0).
    destruct H.
    destruct H1.
    left.
    apply isNilIffFalse.
    auto.
    right.
    apply isNilIffFalse.
    auto.
    apply isNilIffTrue.
    auto.
    
    rewrite negb_true_iff in H.
    rewrite <-not_true_iff_false in H.
    destruct c;intros.
    
    
    unfold not;intros.
    apply H.
    rewrite existsb_exists.
    exists iFil.
    destruct H1.
    assert (isNil Data (dataFilter iFil)=false).
    apply isNilIffFalse;auto.
    rewrite H3;auto.
    simpl.
    split;auto.
    apply isNilIffTrue;auto.
    
    assert (isNil Category (catFilter iFil)=false).
    apply isNilIffFalse;auto.
    rewrite H3;auto.
    rewrite andb_false_r.
    simpl.
    split;auto.
    apply isNilIffTrue;auto.
    
    
    unfold not;intros.
    apply H.
    rewrite existsb_exists.
    exists iFil.
    destruct H1.
    assert (isNil Data (dataFilter iFil)=false).
    apply isNilIffFalse;auto.
    rewrite H3;auto.
    simpl.
    split;auto.
    apply isNilIffTrue;auto.
    
    assert (isNil Category (catFilter iFil)=false).
    apply isNilIffFalse;auto.
    rewrite H3;auto.
    rewrite andb_false_r.
    simpl.
    split;auto.
    apply isNilIffTrue;auto.
    
    auto.
    
    
    unfold not;intros.
    apply H.
    rewrite existsb_exists.
    exists iFil.
    destruct H1.
    assert (isNil Data (dataFilter iFil)=false).
    apply isNilIffFalse;auto.
    rewrite H3;auto.
    simpl.
    split;auto.
    apply isNilIffTrue;auto.
    
    assert (isNil Category (catFilter iFil)=false).
    apply isNilIffFalse;auto.
    rewrite H3;auto.
    rewrite andb_false_r.
    simpl.
    split;auto.
    apply isNilIffTrue;auto.
    
Qed.

Lemma contraReciproco:forall (A B:Prop), (A->B) -> ~B -> ~A.
Proof.
    intros.
    unfold not;intros.
    specialize (H H1).
    absurd B;auto.
Qed.

Lemma notOrAndNot: forall (A B:Prop), ~(A\/B) -> (~A /\ ~B).
Proof.
    intros.
    unfold not in H.
    split;unfold not;intros;
    destruct H.
    left;auto.
    right;auto.
Qed.

Lemma andNotNotOr : forall (A B:Prop), (~A /\ ~B) -> ~(A\/B).
Proof.
    intros.
    destruct H.
    unfold not;intros.
    destruct H1; contradiction.
Qed.

Lemma nonSystemUsrPCorrect : forall (m:Manifest) (p : Perm), In p (usrP m) /\ ~ isSystemPermId p <-> In p (nonSystemUsrP m).
Proof.
    intros.
    unfold nonSystemUsrP.
    rewrite filter_In.
    split;intros;split;destruct H;auto.
    rewrite negb_true_iff.
    apply isSystemPermBoolCorrectBack. 
    auto.
    rewrite negb_true_iff in H0.
    apply isSystemPermBoolCorrect.
    auto.
Qed.

Lemma isAnyCmpRunningCorrect : forall (a:idApp) (s:System) (sValid:validstate s), (forall (ic : iCmp) (c : Cmp), map_apply iCmp_eq (running (state s)) ic = Value iCmp c -> ~ inApp c a s) -> isAnyCmpRunning a s=false.
Proof.
    intros.
    unfold isAnyCmpRunning.
    case_eq (map_apply idApp_eq (manifest (environment s)) a);intros.
    rewrite <-not_true_iff_false.
    unfold not;intro.
    rewrite existsb_exists in H1.
    destruct H1.
    destruct H1.
    unfold isCmpRunning in H2.
    unfold InBool in H2.
    rewrite existsb_exists in H2.
    destruct H2.
    destruct H2.
    rewrite in_map_iff in H2.
    destruct H2.
    destruct H2.
    unfold getRunningCmps in H4.
    apply inGetValues in H4.
    destruct H4.
    destruct H4.
    rewrite in_map_iff in H4.
    destruct H4.
    destruct H4.
    destruct idCmp_eq in H3.
    clear H3.
    specialize (H x3 x1).
    rewrite H5 in H4.
    specialize (H H4).
    assert (inApp x a s).
    unfold inApp.
    exists m.
    auto.
    assert (x=x1).
    assert (exists a:idApp, inApp x1 a s).
    apply (ifRunningThenInApp s sValid x1 x3).
    auto.
    destruct H7.
    rewrite<- H2 in e.
    apply (inAppSameCmpId s sValid x x1 a x4);auto.
    rewrite H7 in H3.
    contradiction.
    discriminate H3.
    auto.
Qed.





Lemma sysAppMfstThenGetAppAndMfst : forall (a:idApp) (c:Cmp) (s:System) (sValid: validstate s) (sysapp:SysImgApp) (m:Manifest), In c (cmp m) -> In sysapp (systemImage (environment s)) /\ manifestSI sysapp = m /\ idSI sysapp = a -> getManifestAndAppFromCmp c s = (a,m).
Proof.
    intros.
    unfold getManifestAndAppFromCmp.
    remember (fun pair : idApp * exc Manifest idApp => match snd pair with | Value _ mfst => InBool idCmp idCmp_eq (getCmpId c) (map getCmpId (cmp mfst)) | Error _ _ => false end) as theFun.
    remember (map (fun a0 : idApp => (a0, map_apply idApp_eq (manifest (environment s)) a0)) (apps (state s)) ++ map (fun sysapp0 : SysImgApp => (idSI sysapp0, Value idApp (manifestSI sysapp0))) (systemImage (environment s))) as theList.
    remember (defaultApp, Value idApp defaultManifest) as theDfltPair.
    remember (hd theDfltPair (filter theFun theList)) as theHead.
    destruct_conj H0.
    assert (In theHead theList /\ theFun theHead =true).
    rewrite HeqtheHead.
    apply ifExistsFilter.
    exists (a, Value idApp m).
    rewrite filter_In.
    split.
    rewrite HeqtheList.
    rewrite in_app_iff.
    right.
    rewrite in_map_iff.
    exists sysapp.
    rewrite H0, H3.
    auto.
    rewrite HeqtheFun.
    simpl.
    unfold InBool.
    rewrite existsb_exists.
    exists (getCmpId c).
    split.
    rewrite in_map_iff.
    exists c.
    auto.
    destruct idCmp_eq;auto.
    destruct H2.
    rewrite HeqtheFun in H4.
    case_eq (snd theHead);intros.
    rewrite H5 in H4.
    unfold InBool in H4.
    rewrite existsb_exists in H4.
    destruct H4.
    destruct H4.
    rewrite in_map_iff in H4.
    destruct H4.
    destruct H4.
    remember (fst theHead) as a'.
    assert (inApp x0 a' s).
    unfold inApp.
    rewrite HeqtheList in H2.
    rewrite in_app_iff in H2.
    exists m0.
    split;auto.
    destruct H2; rewrite in_map_iff in H2; destruct H2; destruct H2;
    rewrite <-H2 in Heqa', H5;
    simpl in Heqa', H5.
    left.
    rewrite <-Heqa' in H5.
    auto.
    right.
    exists x1.
    inversion H5.
    auto.
    
    assert (inApp c a s).
    unfold inApp.
    exists m.
    split;auto.
    right.
    exists sysapp.
    auto.
    assert (x0=c).
    destruct idCmp_eq in H6.
    rewrite <- e in H4.
    apply (inAppSameCmpId s sValid x0 c a' a);auto.
    discriminate H6.
    rewrite H10 in H8.
    assert (a'=a).
    apply (inAppSameCmp s sValid c a' a);auto.
    
    rewrite HeqtheList in H2.
    rewrite in_app_iff in H2.
    destruct H2; rewrite in_map_iff in H2; destruct H2; destruct H2; rewrite <-H2 in Heqa', H5; simpl in Heqa', H5.
    rewrite<- Heqa' in H12.
    rewrite H11 in H12.
    absurd (In a (apps (state s)) /\ In sysapp (systemImage (environment s)) /\ idSI sysapp = a).
    apply sysAppInApps;auto.
    auto.
    inversion H5.
    rewrite H11 in Heqa'.
    assert (x1=sysapp).
    rewrite <- H3 in Heqa'.
    apply (notDupSysAppVS s);auto.
    rewrite <-H0.
    rewrite H11.
    rewrite H13.
    auto.
    rewrite H5 in H4.
    discriminate H4.
Qed.

Lemma appMfstThenGetAppAndMfst : forall (a:idApp) (c:Cmp) (s:System) (sValid: validstate s) (m:Manifest), In c (cmp m) -> map_apply idApp_eq (manifest (environment s)) a = Value idApp m -> getManifestAndAppFromCmp c s = (a,m).
Proof.
    intros.
    unfold getManifestAndAppFromCmp.
    assert (In a (apps (state s))).
    apply (ifManifestThenInApps s sValid a m);auto.
    remember (fun pair : idApp * exc Manifest idApp => match snd pair with | Value _ mfst => InBool idCmp idCmp_eq (getCmpId c) (map getCmpId (cmp mfst)) | Error _ _ => false end) as theFun.
    remember (map (fun a0 : idApp => (a0, map_apply idApp_eq (manifest (environment s)) a0)) (apps (state s)) ++ map (fun sysapp0 : SysImgApp => (idSI sysapp0, Value idApp (manifestSI sysapp0))) (systemImage (environment s))) as theList.
    remember (defaultApp, Value idApp defaultManifest) as theDfltPair.
    remember (hd theDfltPair (filter theFun theList)) as theHead.
    assert (In theHead theList /\ theFun theHead =true).
    rewrite HeqtheHead.
    apply ifExistsFilter.
    exists (a, Value idApp m).
    rewrite filter_In.
    split.
    rewrite HeqtheList.
    rewrite in_app_iff.
    left.
    rewrite in_map_iff.
    exists a.
    rewrite H0.
    split;auto.
    rewrite HeqtheFun.
    simpl.
    unfold InBool.
    rewrite existsb_exists.
    exists (getCmpId c).
    split.
    rewrite in_map_iff.
    exists c.
    auto.
    destruct idCmp_eq;auto.
    destruct H2.
    rewrite HeqtheFun in H3.
    case_eq (snd theHead);intros.
    rewrite H4 in H3.
    unfold InBool in H3.
    rewrite existsb_exists in H3.
    destruct H3.
    destruct H3.
    rewrite in_map_iff in H3.
    destruct H3.
    destruct H3.
    remember (fst theHead) as a'.
    assert (inApp x0 a' s).
    unfold inApp.
    rewrite HeqtheList in H2.
    rewrite in_app_iff in H2.
    exists m0.
    split;auto.
    destruct H2; rewrite in_map_iff in H2; destruct H2; destruct H2;
    rewrite <-H2 in Heqa', H4;
    simpl in Heqa', H4.
    left.
    rewrite <-Heqa' in H4.
    auto.
    right.
    exists x1.
    inversion H4.
    auto.
    
    
    assert (inApp c a s).
    unfold inApp.
    exists m.
    split;auto.
    assert (x0=c).
    destruct idCmp_eq in H5.
    rewrite<-e in H3.
    apply (inAppSameCmpId s sValid x0 c a' a);auto.
    discriminate H5.
    rewrite H9 in H7.
    assert (a'=a).
    apply (inAppSameCmp s sValid c a' a);auto.
    
    rewrite HeqtheList in H2.
    rewrite in_app_iff in H2.
    destruct H2; rewrite in_map_iff in H2; destruct H2; destruct H2; rewrite <-H2 in Heqa', H4; simpl in Heqa', H4.
    rewrite<- Heqa' in H4.
    rewrite H10 in H4.
    rewrite H0 in H4.
    inversion H4.
    rewrite H10.
    auto.
    rewrite H10 in Heqa'.
    assert (In a (apps (state s))).
    apply (ifManifestThenInApps s sValid a m);auto.
    absurd (In a (apps (state s)) /\ In x1 (systemImage (environment s)) /\ idSI x1 = a).
    apply sysAppInApps;auto.
    auto.
    rewrite H4 in H3.
    discriminate H3.
Qed.

Lemma anyMfstThenGetAppAndMfst : forall (a:idApp) (c:Cmp) (s:System) (sValid: validstate s) (m:Manifest), (map_apply idApp_eq (manifest (environment s)) a = Value idApp m \/ (exists sysapp : SysImgApp, In sysapp (systemImage (environment s)) /\ idSI sysapp = a /\ manifestSI sysapp = m)) -> In c (cmp m) -> getManifestAndAppFromCmp c s = (a,m).
Proof.
    intros.
    destruct H.
    apply appMfstThenGetAppAndMfst;auto.
    destruct H.
    destruct H.
    destruct H1.
    apply (sysAppMfstThenGetAppAndMfst a c s sValid x); auto.
Qed.

Lemma inAppThenGetAppFromCmp : forall (a:idApp) (c:Cmp) (s:System) (sValid: validstate s), inApp c a s -> getAppFromCmp c s = a.
Proof.
    unfold inApp.
    unfold getAppFromCmp.
    intros.
    destruct H.
    destruct H.
    assert (getManifestAndAppFromCmp c s = (a,x)).
    apply anyMfstThenGetAppAndMfst;auto.
    rewrite H1.
    simpl.
    auto.
Qed.

Lemma existsRes_iff : forall (c:CProvider) (u:uri) (s:System) (sValid:validstate s), existsRes c u s <-> existsResBool c u s=true.
Proof.
    unfold existsResBool.
    unfold existsRes.
    split;intros.
    assert (negb (InBool Cmp Cmp_eq (cmpCP c) (getAllComponents s))=false).
    rewrite negb_false_iff.
    unfold InBool.
    rewrite existsb_exists.
    destruct H.
    destruct H.
    exists (cmpCP c).
    split.
    unfold getAllComponents.
    rewrite in_concat.
    destruct H.
    exists (cmp x0).
    split;auto.
    rewrite in_app_iff.
    destruct H.
    destruct H.
    left.
    rewrite in_map_iff.
    exists x0.
    split;auto.
    apply inGetValuesBack.
    exists (map_apply idApp_eq (manifest (environment s)) x).
    split;auto.
    rewrite in_map_iff.
    exists x.
    split;auto.
    apply (ifManifestThenInApps s sValid  x x0);auto.
    
    
    right.
    rewrite in_map_iff.
    destruct H.
    exists x1.
    destruct_conj H.
    split.
    rewrite H4;auto.
    auto.
    destruct_conj H.
    auto.
    destruct Cmp_eq.
    auto.
    destruct n;auto.
    rewrite H0.
    
    destruct H.
    destruct H.
    destruct H1.
    destruct H1.
    rewrite H1.
    destruct H2.
    assert (getAppFromCmp (cmpCP c) s = x).
    apply inAppThenGetAppFromCmp; auto.
    rewrite H3.
    rewrite H2.
    auto.
    
    assert (InBool Cmp Cmp_eq (cmpCP c) (getAllComponents s)=true).
    rewrite <-not_false_iff_true.
    unfold not;intros.
    rewrite<- negb_true_iff in H0.
    rewrite H0 in H.
    discriminate H.
    assert (H0':=H0).
    rewrite<- negb_false_iff in H0.
    rewrite H0 in H.
    
    unfold InBool in H0'.
    rewrite existsb_exists in H0'.
    elim (classic ((exists r:res, map_apply uri_eq (map_res c) u = Value uri r)));intro.
    destruct H1.
    rewrite H1 in H.
    elim (classic ((exists v:Val, map_apply rescontdomeq (resCont (state s)) (getAppFromCmp (cmpCP c) s, x)=Value (idApp*res) v)));intro.
    destruct H2.
    destruct H0'.
    destruct H3.
    destruct Cmp_eq in H4.
    
    unfold getAllComponents in H3.
    rewrite in_concat in H3.
    destruct H3.
    destruct H3.
    rewrite in_app_iff in H3.
    destruct H3; rewrite in_map_iff in H3.
    destruct H3.
    destruct H3.
    apply inGetValues in H6.
    destruct H6.
    destruct H6.
    rewrite in_map_iff in H6.
    destruct H6.
    exists x5.
    split.
    unfold inApp.
    exists x3.
    split.
    left.
    destruct H6.
    rewrite H6.
    auto.
    rewrite H3.
    rewrite e.
    auto.
    exists x.
    split;auto.
    exists x0.
    rewrite e in H2.
    assert (getAppFromCmp x1 s = x5).
    apply inAppThenGetAppFromCmp.
    auto.
    unfold inApp.
    exists x3.
    split.
    left.
    destruct H6.
    rewrite <-H7.
    auto.
    rewrite H3.
    auto.
    rewrite <-H8.
    auto.
    
    destruct H3.
    exists (idSI x3).
    split.
    unfold inApp.
    exists (manifestSI x3).
    destruct H3.
    split.
    right.
    exists x3;split;auto.
    rewrite H3.
    rewrite e.
    auto.
    
    
    exists x.
    split;auto.
    exists x0.
    rewrite e in H2.
    assert (getAppFromCmp x1 s = (idSI x3)).
    apply inAppThenGetAppFromCmp.
    auto.
    unfold inApp.
    exists (manifestSI x3).
    destruct H3.
    split.
    right.
    exists x3.
    split;auto.
    rewrite H3.
    auto.
    rewrite <-H6.
    auto.
    discriminate H4.
    
    case_eq (map_apply rescontdomeq (resCont (state s)) (getAppFromCmp (cmpCP c) s, x));intros.
    destruct H2.
    exists v.
    auto.
    rewrite H3 in H.
    discriminate H.
    
    case_eq (map_apply uri_eq (map_res c) u);intros.
    destruct H1.
    exists r;auto.
    rewrite H2 in H.
    discriminate H.
Qed.

Lemma isCProviderBool_iff : forall c:Cmp, isCProvider c <-> isCProviderBool c = true.
Proof.
    unfold isCProvider.
    unfold isCProviderBool.
    intro.
    assert (False<->false=true).
    split;intros.
    destruct H.
    discriminate H.
    case_eq c;intros;auto.
    split;intros; auto.
Qed.

Lemma defPermsCorrect : forall (s:System) (a:idApp) (sValid : validstate s), isAppInstalled a s -> defPermsForApp s a (getDefPermsForApp a s).
Proof.
    intros.
    unfold getDefPermsForApp.
    unfold defPermsForApp.
    unfold isAppInstalled in H.
    destruct H.
    left.
    assert (exists l: list Perm, map_apply idApp_eq (defPerms (environment s)) a = Value idApp l).
    apply ifInAppThenDefPerms;auto.
    destruct H0.
    rewrite H0.
    auto.
    right.
    destruct H.
    destruct H.
    exists x.
    split;auto.
    split;auto.
    assert (~(In a (apps (state s)))).
    unfold not;intros.
    absurd (In a (apps (state s)) /\ In x (systemImage (environment s)) /\ idSI x = a).
    apply sysAppInApps;auto.
    auto.
    case_eq (map_apply idApp_eq (defPerms (environment s)) a);intros.
    absurd (In a (apps (state s))).
    auto.
    apply (ifDefPermsThenInApps s sValid a l);auto.
    remember (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) as theFun.
    assert (In x (filter theFun (systemImage (environment s)))).
    rewrite filter_In.
    rewrite HeqtheFun.
    rewrite H0.
    destruct idApp_eq;auto.
    remember (filter theFun (systemImage (environment s))) as theList.
    assert (hd nil (map defPermsSI theList) = defPermsSI (hd x theList)).
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists x;auto.
    rewrite H4.
    assert (x=hd x theList).
    rewrite HeqtheList.
    assert (In (hd x (filter theFun (systemImage (environment s)))) (systemImage (environment s)) /\ theFun (hd x (filter theFun (systemImage (environment s))))=true).
    apply ifExistsFilter.
    exists x.
    rewrite filter_In.
    rewrite HeqtheFun.
    rewrite H0.
    destruct idApp_eq;auto.
    destruct H5.
    remember (hd x (filter theFun (systemImage (environment s)))) as head.
    rewrite HeqtheFun in H6.
    destruct idApp_eq in H6.
    symmetry in e.
    rewrite<- e in H0.
    apply (notDupSysAppVS s sValid);auto.
    discriminate H6.
    rewrite<- H5.
    auto.
Qed.

Lemma appCertCorrect : forall (a:idApp) (c:Cert) (s:System) (sValid:validstate s) , appCert a c s -> getAppCert a s = c.
Proof.
    unfold appCert.
    unfold getAppCert.
    intros.
    destruct H.
    rewrite H.
    auto.
    assert (~(In a (apps (state s)))).
    unfold not;intros.
    destruct H.
    destruct H.
    destruct H1.
    absurd (In a (apps (state s)) /\ In x (systemImage (environment s)) /\ idSI x = a).
    apply sysAppInApps;auto.
    auto.
    case_eq (map_apply idApp_eq (cert (environment s)) a);intros.
    absurd (In a (apps (state s))).
    auto.
    apply (ifCertThenInApps s sValid a c0);auto.
    destruct H.
    assert (In x (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))).
    apply filter_In.
    destruct H.
    destruct H2.
    destruct idApp_eq;auto.
    remember (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) as filterf.
    rewrite (ifNotNilHdMap (filter filterf (systemImage (environment s))) certSI x).
    remember (hd x (filter filterf (systemImage (environment s)))) as l.
    assert ( In l (systemImage (environment s)) /\ filterf l = true).
    rewrite Heql.
    apply ifExistsFilter.
    exists x.
    rewrite filter_In.
    destruct H.
    destruct H3.
    split;auto.
    rewrite Heqfilterf.
    destruct idApp_eq;auto.
    assert (l=x).
    destruct H3.
    rewrite Heqfilterf in H4.
    destruct idApp_eq in H4.
    destruct H.
    destruct H5.
    rewrite e in H5.
    apply (notDupSysAppVS s sValid);auto.
    discriminate H4.
    rewrite H4.
    destruct H.
    destruct H5.
    auto.
    unfold not;intros.
    rewrite H3 in H2.
    destruct H2.
Qed.


Lemma appCertCorrectBack : forall (a:idApp) (c:Cert) (s:System) (sValid:validstate s) , getAppCert a s = c -> isAppInstalled a s -> appCert a c s.
Proof.
    unfold appCert.
    unfold getAppCert.
    intros.
    destruct H0.
    assert (exists (c:Cert), map_apply idApp_eq (cert (environment s)) a=Value idApp c).
    apply ifInAppThenCert;auto.
    destruct H1.
    rewrite H1 in H.
    left.
    rewrite <-H.
    auto.
    right.
    destruct H0.
    exists x.
    destruct H0.
    split;auto.
    split;auto.
    case_eq (map_apply idApp_eq (cert (environment s)) a);intros.
    absurd (In a (apps (state s)) /\ In x (systemImage (environment s)) /\ idSI x = a).
    apply sysAppInApps;auto.
    split.
    apply (ifCertThenInApps s sValid a c0);auto.
    auto.
    rewrite H2 in H.
    remember (hd defaultSysApp (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))) as theHead.
    assert (In x ( filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))).
    rewrite filter_In.
    split;auto.
    rewrite H1.
    destruct idApp_eq;auto.
    assert (c=certSI (theHead)).
    rewrite HeqtheHead.
    rewrite <-H.
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists x.
    auto.
    assert (theHead=x).
    remember (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) as theFun.
    assert (In theHead (systemImage (environment s)) /\ theFun theHead =true).
    rewrite HeqtheHead.
    apply ifExistsFilter.
    exists x.
    auto.
    destruct H5.
    rewrite HeqtheFun in H6.
    destruct idApp_eq in H6.
    rewrite e in H1.
    apply (notDupSysAppVS s);auto.
    discriminate H6.
    rewrite <-H5.
    auto.
    
Qed.

Lemma certOfDefinerCorrect : forall (p:Perm) (c:Cert) (s:System) (sValid:validstate s) , certOfDefiner p c s -> getCertOfDefiner p s = c.
Proof.
    unfold certOfDefiner.
    unfold getCertOfDefiner.
    intros.
    remember (filter (fun pair : idApp * list Perm => InBool Perm Perm_eq p (snd pair)) (map (fun a : idApp => (a, getDefPermsForApp a s)) (apps (state s) ++ map idSI (systemImage (environment s))))) as pairs.
    destruct H.
    destruct H.
    destruct H.
    destruct_conj H.
    assert (In (x,x0) pairs /\ hd (x,x0) pairs = (x,x0)).
    assert (In (x,x0) pairs).
    rewrite Heqpairs.
    rewrite filter_In.
    split.
    rewrite in_map_iff.
    exists x.
    split.
    unfold getDefPermsForApp.
    rewrite H0.
    auto.
    rewrite in_app_iff.
    left.
    apply (ifCertThenInApps s sValid x c);auto.
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    destruct Perm_eq;split;auto.
    remember (fun pair : idApp * list Perm => InBool Perm Perm_eq p (snd pair)) as theFilterFun.
    remember (map (fun a : idApp => (a, getDefPermsForApp a s)) (apps (state s) ++ map idSI (systemImage (environment s)))) as theList.
    assert (In (hd (x,x0) pairs) theList /\ theFilterFun (hd (x,x0) pairs)=true).
    rewrite Heqpairs.
    apply ifExistsFilter.
    exists (x,x0).
    rewrite <-Heqpairs.
    auto.
    destruct H3.
    rewrite HeqtheFilterFun in H4.
    unfold InBool in H4.
    rewrite existsb_exists in H4.
    destruct H4.
    destruct H4.
    destruct Perm_eq in H5.
    rewrite<- e in H4.
    remember (hd (x,x0) pairs) as head.
    rewrite HeqtheList in H3.
    rewrite in_map_iff in H3.
    destruct H3.
    destruct H3.
    rewrite in_app_iff in H6.
    assert (defPermsForApp s x x0).
    unfold defPermsForApp.
    left.
    auto.
    assert (defPermsForApp s x2 (getDefPermsForApp x2 s)).
    apply defPermsCorrect;auto.
    unfold isAppInstalled.
    rewrite in_map_iff in H6.
    destruct H6.
    left;auto.
    right.
    destruct H6.
    destruct H6.
    exists x3;auto.
    
    rewrite <-H3 in H4;simpl in H4.
    assert (p=p /\ x=x2).
    apply (notDupPermVS s sValid x x2 p p x0 (getDefPermsForApp x2 s));auto.
    destruct H9.
    assert (getDefPermsForApp x2 s = x0).
    unfold getDefPermsForApp.
    rewrite<- H10.
    rewrite H0.
    auto.
    rewrite <-H3.
    rewrite H11.
    split;auto.
    rewrite H10.
    auto.
    discriminate H5.
    destruct H1.
    
    remember (fun pair : idApp * list Perm => getAppCert (fst pair) s) as theFun.
    assert ( hd defaultCert (map theFun pairs) = theFun (hd (x,x0) pairs)).
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists (x,x0).
    auto.
    rewrite H4.
    rewrite H3.
    rewrite HeqtheFun.
    simpl.
    assert (appCert x c s).
    unfold appCert.
    left.
    auto.
    apply appCertCorrect; auto.
    
    destruct H.
    destruct_conj H.
    
    
    
    
    remember (defPermsSI x) as l.
    remember (idSI x) as a.
    assert (In (a,l) pairs /\ hd (a,l) pairs = (a,l)).
    assert (In (a,l) pairs).
    rewrite Heqpairs.
    rewrite filter_In.
    split.
    rewrite in_map_iff.
    exists a.
    split.
    unfold getDefPermsForApp.
    case_eq (map_apply idApp_eq (defPerms (environment s)) a);intros.
    absurd (In a (apps (state s))).
    unfold not;intros.
    absurd (In a (apps (state s)) /\ In x (systemImage (environment s)) /\ idSI x = a).
    apply sysAppInApps;auto.
    auto.
    apply (ifDefPermsThenInApps s sValid a l0);auto.
    
    
    remember (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) as theFun.
    assert (In x (filter theFun (systemImage (environment s)))).
    rewrite filter_In.
    rewrite HeqtheFun.
    rewrite Heqa.
    destruct idApp_eq;auto.
    assert ( hd nil (map defPermsSI (filter theFun (systemImage (environment s)))) = defPermsSI (hd x (filter theFun (systemImage (environment s))))).
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists x.
    auto.
    rewrite H4.
    assert (hd x (filter theFun (systemImage (environment s)))=x).
    assert (In (hd x (filter theFun (systemImage (environment s)))) (systemImage (environment s)) /\ theFun (hd x (filter theFun (systemImage (environment s))))=true).
    apply ifExistsFilter.
    exists x.
    auto.
    destruct H5.
    remember (hd x (filter theFun (systemImage (environment s)))) as head.
    rewrite HeqtheFun in H6.
    destruct idApp_eq in H6.
    rewrite e in Heqa.
    apply (notDupSysAppVS s);auto.
    
    discriminate H6.
    rewrite H5.
    rewrite Heql.
    auto.
    rewrite in_app_iff.
    right.
    rewrite in_map_iff.
    exists x.
    auto.
    simpl.
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    destruct Perm_eq;auto.
    split;auto.
    
    
    remember (fun pair : idApp * list Perm => InBool Perm Perm_eq p (snd pair)) as theFilterFun.
    remember (map (fun a : idApp => (a, getDefPermsForApp a s)) (apps (state s) ++ map idSI (systemImage (environment s)))) as theList.
    assert (In (hd (a,l) pairs) theList /\ theFilterFun (hd (a,l) pairs)=true).
    rewrite Heqpairs.
    apply ifExistsFilter.
    exists (a,l).
    rewrite <-Heqpairs.
    auto.
    destruct H3.
    rewrite HeqtheFilterFun in H4.
    unfold InBool in H4.
    rewrite existsb_exists in H4.
    destruct H4.
    destruct H4.
    destruct Perm_eq in H5.
    rewrite<- e in H4.
    remember (hd (a,l) pairs) as head.
    rewrite HeqtheList in H3.
    rewrite in_map_iff in H3.
    destruct H3.
    destruct H3.
    rewrite in_app_iff in H6.
    assert (defPermsForApp s a l).
    unfold defPermsForApp.
    
    right.
    exists x.
    auto.
    
    
    
    assert (defPermsForApp s x1 (getDefPermsForApp x1 s)).
    apply defPermsCorrect;auto.
    unfold isAppInstalled.
    rewrite in_map_iff in H6.
    destruct H6.
    left;auto.
    right.
    destruct H6.
    destruct H6.
    exists x2;auto.
    
    rewrite <-H3 in H4;simpl in H4.
    assert (p=p /\ a=x1).
    apply (notDupPermVS s sValid a x1 p p l (getDefPermsForApp x1 s));auto.
    destruct H9.
    assert (getDefPermsForApp x1 s = l).
    unfold getDefPermsForApp.
    rewrite<- H10.
    
    case_eq (map_apply idApp_eq (defPerms (environment s)) a);intros.
    assert (In a (apps (state s))).
    apply (ifDefPermsThenInApps s sValid a l0);auto.
    absurd (In a (apps (state s))).
    absurd (In a (apps (state s)) /\ In x (systemImage (environment s)) /\ idSI x = a).
    apply sysAppInApps;auto.
    auto.
    auto.
    
    remember (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) as theFun.
    assert (In x (filter theFun (systemImage (environment s)))).
    rewrite filter_In.
    rewrite HeqtheFun.
    rewrite Heqa.
    destruct idApp_eq;auto.
    assert ( hd nil (map defPermsSI (filter theFun (systemImage (environment s)))) = defPermsSI (hd x (filter theFun (systemImage (environment s))))).
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists x.
    auto.
    rewrite H13.
    assert (hd x (filter theFun (systemImage (environment s)))=x).
    assert (In (hd x (filter theFun (systemImage (environment s)))) (systemImage (environment s)) /\ theFun (hd x (filter theFun (systemImage (environment s))))=true).
    apply ifExistsFilter.
    exists x.
    auto.
    destruct H14.
    remember (hd x (filter theFun (systemImage (environment s)))) as head2.
    rewrite HeqtheFun in H15.
    destruct idApp_eq in H15.
    
    rewrite e0 in Heqa.
    apply (notDupSysAppVS s);auto.
    
    discriminate H15.
    rewrite H14.
    auto.
    
    
    rewrite <-H3.
    rewrite H11.
    rewrite H10.
    auto.
    discriminate H5.
    destruct H1.
    
    remember (fun pair : idApp * list Perm => getAppCert (fst pair) s) as theFun.
    assert ( hd defaultCert (map theFun pairs) = theFun (hd (a,l) pairs)).
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists (a,l).
    auto.
    rewrite H4.
    rewrite H3.
    rewrite HeqtheFun.
    simpl.
    assert (appCert a c s).
    unfold appCert.
    right.
    exists x.
    auto.
    apply appCertCorrect; auto.
Qed.


Lemma certOfDefinerCorrectBack : forall (p:Perm) (c:Cert) (s:System) (sValid:validstate s) , getCertOfDefiner p s = c -> usrDefPerm p s -> certOfDefiner p c s.
Proof.
    unfold certOfDefiner.
    unfold getCertOfDefiner.
    intros.
    unfold usrDefPerm in H0.
    elim(classic(exists (a : idApp) (l : list Perm), map_apply idApp_eq (defPerms (environment s)) a = Value idApp l /\ In p l));intros.
    clear H0.
    left.
    destruct H1.
    destruct H0.
    destruct H0.
    assert (In (x,x0) (filter (fun pair : idApp * list Perm => InBool Perm Perm_eq p (snd pair)) (map (fun a : idApp => (a, getDefPermsForApp a s)) (apps (state s) ++ map idSI (systemImage (environment s)))))).
    rewrite filter_In.
    simpl.
    split.
    rewrite in_map_iff.
    exists x.
    split.
    unfold getDefPermsForApp.
    rewrite H0.
    auto.
    rewrite in_app_iff.
    left.
    apply (ifDefPermsThenInApps s sValid x x0);auto.
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    destruct Perm_eq;auto.
    remember (fun pair : idApp * list Perm => getAppCert (fst pair) s) as theFun.
    assert (c=theFun (hd (x,x0) (filter (fun pair : idApp * list Perm => InBool Perm Perm_eq p (snd pair)) (map (fun a : idApp => (a, getDefPermsForApp a s)) (apps (state s) ++ map idSI (systemImage (environment s))))))).
    rewrite <-H.
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists (x,x0);auto.
    clear H.
    rewrite HeqtheFun in H3.
    remember (fun pair : idApp * list Perm => InBool Perm Perm_eq p (snd pair)) as theFun2.
    remember (map (fun a : idApp => (a, getDefPermsForApp a s)) (apps (state s) ++ map idSI (systemImage (environment s)))) as theList.
    remember (hd (x, x0) (filter theFun2 theList)) as theHead.
    assert (In theHead theList /\ theFun2 theHead =true).
    rewrite HeqtheHead.
    apply ifExistsFilter.
    exists (x,x0);auto.
    destruct H.
    rewrite HeqtheList in H.
    rewrite HeqtheFun2 in H4.
    rewrite in_map_iff in H.
    destruct H.
    destruct H.
    rewrite <-H in H4.
    simpl in H4.
    assert (defPermsForApp s x x0).
    unfold defPermsForApp.
    left;auto.
    assert (defPermsForApp s x1 (getDefPermsForApp x1 s)).
    apply defPermsCorrect;auto.
    rewrite in_app_iff in H5.
    unfold isAppInstalled.
    destruct H5.
    left;auto.
    right.
    rewrite in_map_iff in H5.
    destruct H5.
    exists x2.
    destruct H5.
    auto.
    assert (p=p /\ x=x1).
    apply (notDupPermVS s sValid x x1 p p x0 (getDefPermsForApp x1 s));auto.
    unfold InBool in H4.
    rewrite existsb_exists in H4.
    destruct H4.
    destruct H4.
    destruct Perm_eq in H8.
    rewrite e.
    auto.
    discriminate H8.
    destruct H8.
    exists x.
    exists x0.
    split;auto.
    split;auto.
    rewrite <-H9 in H.
    rewrite <-H in H3.
    simpl in H3.
    unfold getAppCert in H3.
    assert (exists c:Cert, map_apply idApp_eq (cert (environment s)) x = Value idApp c).
    apply ifInAppThenCert;auto.
    apply (ifDefPermsThenInApps s sValid x x0);auto.
    destruct H10.
    rewrite H10 in H3.
    rewrite H10.
    rewrite H3;auto.
    
    
    destruct H0.
    contradiction.
    right.
    destruct H0.
    destruct H0.
    remember (defPermsSI x) as x0.
    remember (idSI x) as idapp.
    assert (~(In idapp (apps (state s)))).
    unfold not;intros.
    destruct (sysAppInApps s sValid idapp x).
    auto.
    assert (In (idapp,x0) (filter (fun pair : idApp * list Perm => InBool Perm Perm_eq p (snd pair)) (map (fun a : idApp => (a, getDefPermsForApp a s)) (apps (state s) ++ map idSI (systemImage (environment s)))))).
    rewrite filter_In.
    simpl.
    split.
    rewrite in_map_iff.
    exists idapp.
    split.
    unfold getDefPermsForApp.
    case_eq (map_apply idApp_eq (defPerms (environment s)) idapp);intros.
    absurd (In idapp (apps (state s))).
    auto.
    apply (ifDefPermsThenInApps s sValid idapp l);auto.
    remember (hd nil (map defPermsSI (filter (fun sysapp : SysImgApp => if idApp_eq idapp (idSI sysapp) then true else false) (systemImage (environment s))))) as theHead.
    assert (theHead=x0).
    assert (In x (filter (fun sysapp : SysImgApp => if idApp_eq idapp (idSI sysapp) then true else false) (systemImage (environment s)))).
    rewrite filter_In.
    rewrite Heqidapp.
    destruct idApp_eq;auto.
    assert (theHead = defPermsSI (hd x (filter (fun sysapp : SysImgApp => if idApp_eq idapp (idSI sysapp) then true else false) (systemImage (environment s))))).
    rewrite HeqtheHead.
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists x;auto.
    remember (hd x (filter (fun sysapp : SysImgApp => if idApp_eq idapp (idSI sysapp) then true else false) (systemImage (environment s)))) as theHead2.
    assert (theHead2 = x).
    remember (fun sysapp : SysImgApp => if idApp_eq idapp (idSI sysapp) then true else false) as theFun.
    assert (In theHead2 (systemImage (environment s)) /\ theFun theHead2=true).
    rewrite HeqtheHead2.
    apply ifExistsFilter.
    exists x.
    auto.
    destruct H7.
    apply (notDupSysAppVS s);auto.
    rewrite HeqtheFun in H8.
    destruct idApp_eq in H8.
    rewrite <-e.
    auto.
    discriminate H8.
    rewrite H7 in H6.
    rewrite <-Heqx0 in H6.
    auto.
    rewrite H5.
    auto.
    rewrite in_app_iff.
    right.
    rewrite in_map_iff.
    exists x.
    auto.
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    destruct Perm_eq;auto.
    remember (fun pair : idApp * list Perm => getAppCert (fst pair) s) as theFun.
    assert (c=theFun (hd (idapp,x0) (filter (fun pair : idApp * list Perm => InBool Perm Perm_eq p (snd pair)) (map (fun a : idApp => (a, getDefPermsForApp a s)) (apps (state s) ++ map idSI (systemImage (environment s))))))).
    rewrite <-H.
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists (idapp,x0);auto.
    clear H.
    rewrite HeqtheFun in H5.
    remember (fun pair : idApp * list Perm => InBool Perm Perm_eq p (snd pair)) as theFun2.
    remember (map (fun a : idApp => (a, getDefPermsForApp a s)) (apps (state s) ++ map idSI (systemImage (environment s)))) as theList.
    remember (hd (idapp, x0) (filter theFun2 theList)) as theHead.
    assert (In theHead theList /\ theFun2 theHead =true).
    rewrite HeqtheHead.
    apply ifExistsFilter.
    exists (idapp,x0);auto.
    destruct H.
    rewrite HeqtheList in H.
    rewrite HeqtheFun2 in H6.
    rewrite in_map_iff in H.
    destruct H.
    destruct H.
    rewrite <-H in H6.
    simpl in H6.
    assert (defPermsForApp s idapp x0).
    unfold defPermsForApp.
    right.
    exists x;auto.
    
    
    
    assert (defPermsForApp s x1 (getDefPermsForApp x1 s)).
    apply defPermsCorrect;auto.
    rewrite in_app_iff in H7.
    unfold isAppInstalled.
    destruct H7.
    left;auto.
    right.
    rewrite in_map_iff in H7.
    destruct H7.
    exists x2.
    destruct H7.
    auto.
    assert (p=p /\ idapp=x1).
    apply (notDupPermVS s sValid idapp x1 p p x0 (getDefPermsForApp x1 s));auto.
    unfold InBool in H6.
    rewrite existsb_exists in H6.
    destruct H6.
    destruct H6.
    destruct Perm_eq in H10.
    rewrite e.
    auto.
    discriminate H10.
    destruct H10.
    exists x.
    split;auto.
    rewrite <-Heqx0.
    split;auto.
    rewrite <-H11 in H.
    rewrite <-H in H5.
    simpl in H5.
    unfold getAppCert in H5.
    case_eq (map_apply idApp_eq (cert (environment s)) idapp);intros;rewrite H12 in H5.
    absurd (In idapp (apps (state s))).
    auto.
    apply (ifCertThenInApps s sValid idapp c0);auto.
    remember (filter (fun sysapp : SysImgApp => if idApp_eq idapp (idSI sysapp) then true else false) (systemImage (environment s))) as theList2.
    assert (In x theList2).
    rewrite HeqtheList2.
    rewrite filter_In.
    rewrite Heqidapp.
    destruct idApp_eq;auto.
    assert ( hd defaultCert (map certSI theList2) = certSI (hd x theList2)).
    apply ifNotNilHdMap.
    apply inNotNilExists.
    exists x;auto.
    rewrite H14 in H5.
    assert (hd x theList2=x).
    remember (fun sysapp : SysImgApp => if idApp_eq idapp (idSI sysapp) then true else false) as theFun3.
    assert (In (hd x theList2) (systemImage (environment s)) /\ theFun3 (hd x theList2) =true).
    rewrite HeqtheList2.
    apply ifExistsFilter.
    exists x.
    rewrite <-HeqtheList2.
    auto.
    destruct H15.
    rewrite HeqtheFun3 in H16.
    apply (notDupSysAppVS s);auto.
    rewrite <-Heqidapp.
    destruct idApp_eq in H16.
    auto.
    discriminate H16.
    rewrite <-H15.
    auto.
Qed.


Lemma certOfDefinerThenUsrDefPerm : forall (p:Perm) (c:Cert) (s:System) (sValid:validstate s), certOfDefiner p c s -> usrDefPerm p s.
Proof.
    intros.
    unfold usrDefPerm.
    destruct H.
    left.
    destruct H.
    destruct H.
    destruct_conj H.
    exists x.
    exists x0.
    auto.
    right.
    destruct H.
    destruct_conj H.
    exists x.
    auto.
Qed.

Lemma getMfstForAppCorrect : forall (s:System) (sValid:validstate s) (a:idApp) (x:Manifest) (xMfstOfA : isManifestOfApp a x s), getManifestForApp a s = x.
Proof.
    intros.
    unfold getManifestForApp.
    unfold isManifestOfApp in xMfstOfA.
    destruct xMfstOfA.
    rewrite H;auto.
    destruct H.
    destruct H.
    destruct H0.
    case_eq (map_apply idApp_eq (manifest (environment s)) a);intros.
    absurd (In a (apps (state s)) /\ In x0 (systemImage (environment s)) /\ idSI x0 = a).
    apply sysAppInApps;auto.
    split;auto.
    apply (ifManifestThenInApps s sValid a m);auto.
    assert (In x0 (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))).
    rewrite filter_In.
    split;auto.
    rewrite H0.
    destruct idApp_eq;auto.
    rewrite (ifNotNilHdMap (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s))) manifestSI x0 defaultManifest);auto.
    remember (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) as f.
    assert (In (hd x0 (filter f (systemImage (environment s)))) (systemImage (environment s)) /\ f (hd x0 (filter f (systemImage (environment s)))) =true).
    apply ifExistsFilter.
    exists x0;auto.
    destruct H4.
    remember (hd x0 (filter f (systemImage (environment s)))) as dashead.
    rewrite Heqf in H5.
    destruct idApp_eq in H5.
    assert (dashead=x0).
    apply (notDupSysAppVS s);auto.
    rewrite <-e.
    auto.
    rewrite H6;auto.
    discriminate H5.
    apply inNotNilExists.
    exists x0;auto.
Qed.

Lemma isManifestOfAppCorrect : forall (s:System) (sValid:validstate s) (a:idApp) (aInstalled: isAppInstalled a s),
    isManifestOfApp a (getManifestForApp a s) s.
Proof.
    intros.
    assert (exists x, isManifestOfApp a x s).
    unfold isManifestOfApp.
    destruct aInstalled.
    apply ifInAppsThenManifest in H;auto.
    destruct H.
    exists x;auto.
    destruct H.
    exists (manifestSI x).
    right.
    exists x.
    destruct H.
    auto.
    destruct H.
    assert (getManifestForApp a s=x).
    apply getMfstForAppCorrect;auto.
    rewrite H0;auto.
Qed.

Lemma appHasPermissionCorrect : forall (a:idApp) (p:Perm) (s:System) (sValid:validstate s), appHasPermission a p s <-> appHasPermissionBool a p s = true.
Proof.
    unfold appHasPermission.
    unfold appHasPermissionBool.
    split;intros.
    assert (InBool Perm Perm_eq p (getAllPerms s)=true) as permexists.
    assert (permExists p s).
    destruct H.
    destruct H.
    destruct H.
    apply (grantedPermsExistVS s sValid a p x);auto.
    destruct H.
    auto.
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    split.
    unfold getAllPerms.
    rewrite in_app_iff.
    destruct H0.
    left.
    apply isSysPermCorrect;auto.
    right.
    apply inUsrDefPermsIff;auto.
    destruct Perm_eq;auto.
    rewrite permexists.
    rewrite andb_true_l.
    
    assert (isAppInstalled a s) as aIsInstalled.
    unfold isAppInstalled.
    destruct H.
    destruct H.
    destruct H.
    apply (ifPermsThenInApp s sValid a x);auto.
    destruct H.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0.
    left.
    apply (ifManifestThenInApps s sValid a x);auto.
    right.
    destruct H0.
    destruct H0.
    destruct H3.
    exists x0.
    auto.
    assert (isAppInstalledBool a s=true) as aInstBool.
    apply isAppInstalled_iff;auto.
    rewrite aInstBool.
    rewrite andb_true_l.
    
    destruct H.
    assert (InBool Perm Perm_eq p (grantedPermsForApp a s)=true).
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    split.
    unfold grantedPermsForApp.
    destruct H.
    destruct H.
    rewrite H.
    auto.
    destruct Perm_eq;auto.
    rewrite H0.
    apply orb_true_l.
    dontcare( InBool Perm Perm_eq p (grantedPermsForApp a s)).
    clear H0.
    rewrite orb_false_l.
    destruct H.
    destruct H0.
    destruct H0.
    destruct H0.
    assert (getManifestForApp a s=x).
    apply getMfstForAppCorrect;auto.
    rewrite H3.
    assert (InBool idPerm idPerm_eq (idP p) (use x)=true).
    unfold InBool.
    rewrite existsb_exists.
    exists (idP p).
    split;auto.
    destruct idPerm_eq;auto.
    rewrite H4.
    destruct H1.
    destruct H1.
    destruct H1.
    assert (InBool idApp idApp_eq a (apps (state s))=true).
    unfold InBool.
    rewrite existsb_exists.
    exists a.
    split.
    apply (ifDefPermsThenInApps s sValid a x0);auto.
    destruct idApp_eq;auto.
    rewrite H6.
    assert (InBool Perm Perm_eq p (getDefPermsForApp a s)=true).
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    split.
    unfold getDefPermsForApp.
    rewrite H1.
    auto.
    destruct Perm_eq;auto.
    rewrite H7.
    auto.
    dontcare (InBool idApp idApp_eq a (apps (state s)) && InBool Perm Perm_eq p (getDefPermsForApp a s)).
    destruct H1.
    rewrite H1.
    auto.
    destruct H1.
    destruct H1.
    rewrite H1.
    unfold groupIsGranted.
    destruct H6.
    destruct H6.
    destruct_conj H6.
    rewrite H7.
    rewrite H6.
    unfold InBool.
    rewrite existsb_exists.
    exists x0.
    split;auto.
    destruct idGrp_eq;auto.
    destruct H1.
    destruct H1.
    destruct H6.
    destruct H6.
    assert (getAppCert a s = x0).
    apply appCertCorrect;auto.
    assert (getCertOfDefiner p s = x0).
    apply certOfDefinerCorrect;auto.
    rewrite H8.
    rewrite H9.
    destruct Cert_eq;auto.
    assert (InBool Perm Perm_eq p (usrDefPerms s)=true).
    assert (usrDefPerm p s).
    apply (certOfDefinerThenUsrDefPerm p x0);auto.
    unfold InBool.
    rewrite existsb_exists.
    exists p.
    split.
    apply inUsrDefPermsIff;auto.
    destruct Perm_eq;auto.
    rewrite H10.
    destruct H1;rewrite H1.
    auto.
    auto.
    
    
    
    destruct H1;rewrite H1.
    assert ((if Cert_eq (getAppCert a s) manufacturerCert then true else false)=true).
    destruct H6.
    destruct H6.
    assert (getAppCert a s=x0).
    apply appCertCorrect;auto.
    rewrite H8.
    rewrite H7.
    destruct Cert_eq;auto.
    rewrite H7.
    rewrite orb_true_r.
    auto.
    
    
    
    rewrite andb_true_iff in H.
    destruct H.
    rewrite andb_true_iff in H.
    destruct H as [dos H].
    
    rewrite orb_true_iff in H0.
    destruct H0.
    left.
    unfold InBool in H0.
    rewrite existsb_exists in H0.
    destruct H0.
    destruct H0.
    unfold grantedPermsForApp in H0.
    destruct (map_apply idApp_eq (perms (state s)) a).
    exists l.
    destruct Perm_eq in H1.
    rewrite e.
    auto.
    discriminate H1.
    inversion H0.
    right.
    
    split.
    unfold InBool in dos.
    rewrite existsb_exists in dos.
    destruct dos.
    destruct H1.
    unfold getAllPerms in H1.
    rewrite in_app_iff in H1.
    destruct Perm_eq in H2.
    rewrite <-e in H1.
    destruct H1.
    left.
    apply isSysPermCorrect;auto.
    right.
    apply inUsrDefPermsIff;auto.
    discriminate H2.
    
    case_eq (InBool idPerm idPerm_eq (idP p) (use (getManifestForApp a s)));intros;rewrite H1 in H0.
    rewrite <-isAppInstalled_iff in H.
    split.
    unfold InBool in H1.
    rewrite existsb_exists in H1.
    destruct H1.
    destruct H1.
    destruct idPerm_eq in H2.
    rewrite e.
    exists (getManifestForApp a s).
    split;auto.
    apply isManifestOfAppCorrect;auto.
    discriminate H2.
    case_eq (InBool idApp idApp_eq a (apps (state s)) && InBool Perm Perm_eq p (getDefPermsForApp a s));intros.
    left.
    rewrite andb_true_iff in H2.
    destruct H2.
    unfold InBool in H2,H3.
    rewrite existsb_exists in H2,H3.
    destruct H2.
    destruct H2.
    apply ifInAppThenDefPerms in H2;auto.
    destruct H2.
    exists x0.
    destruct idApp_eq in H4.
    rewrite e in *.
    split;auto.
    destruct H3.
    destruct H3.
    destruct Perm_eq in H5.
    rewrite e0.
    unfold getDefPermsForApp in H3.
    rewrite H2 in H3.
    auto.
    discriminate H5.
    discriminate H4.
    rewrite H2 in H0.
    
    right.
    
    destruct (pl p).
    right.
    left.
    split;auto.
    unfold groupIsGranted in H0.
    destruct (maybeGrp p).
    exists i.
    destruct (map_apply idApp_eq (grantedPermGroups (state s)) a).
    exists l.
    unfold InBool in H0.
    rewrite existsb_exists in H0.
    destruct H0.
    destruct H0.
    case_eq (idGrp_eq i x);intros.
    rewrite e.
    auto.
    rewrite H4 in H3.
    discriminate H3.
    discriminate H0.
    discriminate H0.
    left.
    auto.
    right.
    right.
    left.
    split.
    left;auto.
    remember (getAppCert a s) as theCert.
    exists theCert.
    destruct Cert_eq in H0.
    split.
    assert (isAppInstalled a s).
    auto.
    apply appCertCorrectBack;auto.
    apply certOfDefinerCorrectBack;auto.
    case_eq (InBool Perm Perm_eq p (usrDefPerms s));intros;rewrite H3 in H0;simpl in H0.
    unfold InBool in H3.
    rewrite existsb_exists in H3.
    destruct H3.
    destruct H3.
    destruct Perm_eq in H4.
    rewrite <-e0 in H3.
    apply inUsrDefPermsIff;auto.
    discriminate H4.
    discriminate H0.
    rewrite andb_false_r in H0.
    discriminate H0.
    right.
    right.
    case_eq (InBool Perm Perm_eq p (usrDefPerms s) && (if Cert_eq (getAppCert a s) (getCertOfDefiner p s) then true else false));intros;rewrite H3 in H0.
    left.
    
    split;auto.
    remember (getAppCert a s) as theCert.
    exists theCert.
    split.
    assert (isAppInstalled a s).
    auto.
    apply appCertCorrectBack;auto.
    apply certOfDefinerCorrectBack;auto.
    rewrite andb_true_iff in H3.
    destruct H3.
    case_eq (Cert_eq theCert (getCertOfDefiner p s));intros.
    auto.
    rewrite H5 in H4.
    discriminate H4.
    rewrite andb_true_iff in H3.
    destruct H3.
    unfold InBool in H3.
    rewrite existsb_exists in H3.
    destruct H3.
    destruct H3.
    destruct Perm_eq in H5.
    rewrite <-e in H3.
    apply inUsrDefPermsIff;auto.
    discriminate H5.
    rewrite orb_false_l in H0.
    right.
    split;auto.
    exists (getAppCert a s).
    split.
    apply appCertCorrectBack;auto.
    case_eq (Cert_eq (getAppCert a s) manufacturerCert);intros;rewrite H4 in H0.
    auto.
    discriminate H0.
    discriminate H0.
Qed.


Lemma getManifestFromCmpCorrect : forall (x:Manifest) (a:idApp) (s:System) (c:Cmp) (sValid:validstate s), isManifestOfApp a x s /\ inApp c a s -> getManifestFromCmp c s = x.
Proof.
    intros.
    unfold getManifestFromCmp.
    destruct H.
    unfold isManifestOfApp in H.
    unfold inApp in H0.
    destruct H0.
    assert (getManifestAndAppFromCmp c s = (a,x0)).
    destruct H0.
    apply anyMfstThenGetAppAndMfst;auto.
    rewrite H1.
    simpl.
    destruct H0.
    destruct H.
    destruct H0.
    rewrite H in H0.
    inversion H0.
    auto.
    destruct H0.
    destruct_conj H0.
    assert (In a (apps (state s))).
    apply (ifManifestThenInApps s sValid a x);auto.
    absurd (In a (apps (state s)) /\ In x1 (systemImage (environment s)) /\ idSI x1 = a).
    apply (sysAppInApps);auto.
    auto.
    destruct H0.
    assert (In a (apps (state s))).
    apply (ifManifestThenInApps s sValid a x0);auto.
    destruct H.
    destruct_conj H.
    absurd (In a (apps (state s)) /\ In x1 (systemImage (environment s)) /\ idSI x1 = a).
    apply (sysAppInApps);auto.
    auto.
    destruct H.
    destruct H0.
    destruct_conj H.
    destruct_conj H0.
    assert (x1=x2).
    rewrite<-H0 in H.
    apply (notDupSysAppVS s);auto.
    rewrite <-H6 in H7.
    rewrite <-H5.
    auto.
Qed.


Lemma ifInAppAndMfstThenInCmp : forall (x:Manifest) (a:idApp) (s:System) (c:Cmp) (sValid:validstate s), isManifestOfApp a x s -> inApp c a s -> In c (cmp x).
Proof.
    unfold isManifestOfApp.
    unfold inApp.
    intros.
    destruct H0.
    destruct H0.
    assert (x=x0).
    destruct H;destruct H0.
    rewrite H0 in H.
    inversion H;auto.
    destruct H0.
    destruct_conj H0.
    absurd (In a (apps (state s)) /\ In x1 (systemImage (environment s)) /\ idSI x1 = a).
    apply (sysAppInApps);auto.
    assert (In a (apps (state s))).
    apply (ifManifestThenInApps s sValid a x);auto.
    auto.
    destruct H.
    destruct_conj H.
    absurd (In a (apps (state s)) /\ In x1 (systemImage (environment s)) /\ idSI x1 = a).
    apply (sysAppInApps);auto.
    assert (In a (apps (state s))).
    apply (ifManifestThenInApps s sValid a x0);auto.
    auto.
    destruct H.
    destruct H0.
    destruct_conj H.
    destruct_conj H0.
    assert (x1=x2).
    rewrite<-H0 in H.
    apply (notDupSysAppVS s);auto.
    rewrite <-H5 in H6.
    rewrite H6 in H4.
    auto.
    rewrite H2.
    auto.
Qed.





Lemma getCmpMinSdkCorrect : forall (c:Cmp) (s:System) (n:nat) (sValid: validstate s), getCmpMinSdk c s n -> getCmpMinSdkImpl c s=Some n.
Proof.
    unfold getCmpMinSdk.
    unfold getCmpMinSdkImpl.
    intros.
    destruct H.
    destruct H.
    destruct_conj H.
    assert (getManifestFromCmp c s=x0).
    apply (getManifestFromCmpCorrect x0 x s c sValid).
    auto.
    rewrite H1.
    auto.
Qed.

Lemma getCmpMinSdkBack: forall (c:Cmp) (s:System) (n:nat) (sValid: validstate s), (exists a:idApp, inApp c a s) ->getCmpMinSdkImpl c s=Some n -> getCmpMinSdk c s n.
Proof.
    unfold getCmpMinSdk.
    unfold getCmpMinSdkImpl.
    intros.
    destruct H.
    exists x.
    destruct H.
    exists x0.
    destruct H.
    assert (isManifestOfApp x x0 s);auto.
    assert (inApp c x s).
    unfold inApp.
    exists x0.
    auto.
    rewrite (getManifestFromCmpCorrect x0 x) in H0;auto.
Qed.


Lemma getCmpTargetSdkCorrect : forall (c:Cmp) (s:System) (n:nat) (sValid: validstate s), getCmpTargetSdk c s n -> getCmpTargetSdkImpl c s=Some n.
Proof.
    unfold getCmpTargetSdk.
    unfold getCmpTargetSdkImpl.
    intros.
    destruct H.
    destruct H.
    destruct_conj H.
    assert (getManifestFromCmp c s=x0).
    apply (getManifestFromCmpCorrect x0 x s c sValid).
    auto.
    rewrite H1.
    auto.
Qed.

Lemma getCmpTargetSdkBack : forall (c:Cmp) (s:System) (n:nat) (sValid: validstate s), (exists a:idApp, inApp c a s) -> getCmpTargetSdkImpl c s=Some n -> getCmpTargetSdk c s n.
Proof.
    unfold getCmpTargetSdk.
    unfold getCmpTargetSdkImpl.
    intros.
    destruct H.
    exists x.
    destruct H.
    exists x0.
    destruct H.
    assert (isManifestOfApp x x0 s);auto.
    assert (inApp c x s).
    unfold inApp.
    exists x0.
    auto.
    rewrite (getManifestFromCmpCorrect x0 x) in H0;auto.
Qed.

Lemma lebnatCorrect : forall (x y:nat), x<=y <-> lebnat x y = true.
Proof.
    split;intros.
    functional induction (lebnat x y).
    auto.
    omega.
    apply IHb.
    omega.
    functional induction (lebnat x y).
    omega.
    discriminate H.
    specialize (IHb H).
    omega.
Qed.

Lemma getDefaultExpCorrect : forall (cp:CProvider) (s:System) (sValid: validstate s), getDefaultExp cp s -> getDefaultExpBool cp s = true.
Proof.
    unfold getDefaultExp.
    unfold getDefaultExpBool.
    intros.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    assert (getCmpMinSdkImpl (cmpCP cp) s = Some x0).
    apply getCmpMinSdkCorrect;auto.
    rewrite H2.
    assert (getCmpTargetSdkImpl (cmpCP cp) s = Some x).
    apply getCmpTargetSdkCorrect;auto.
    rewrite H3.
    destruct H1.
    assert (lebnat x0 16=true).
    apply lebnatCorrect;auto.
    rewrite H4;auto.
    assert (lebnat x 16=true).
    apply lebnatCorrect;auto.
    rewrite H4;auto.
    apply  orb_true_r.
    
Qed.

Lemma getDefaultExpBack : forall (cp:CProvider) (s:System) (sValid: validstate s), (exists a:idApp, inApp (cmpCP cp) a s) -> getDefaultExpBool cp s = true -> getDefaultExp cp s.
Proof.
    unfold getDefaultExp.
    unfold getDefaultExpBool.
    intros.
    case_eq (getCmpMinSdkImpl (cmpCP cp) s);intros;rewrite H1 in H0.
    case_eq (getCmpTargetSdkImpl (cmpCP cp) s);intros;rewrite H2 in H0.
    exists n0.
    exists n.
    split.
    apply getCmpMinSdkBack;auto.
    split.
    apply getCmpTargetSdkBack;auto.
    rewrite orb_true_iff in H0.
    destruct H0.
    left.
    apply lebnatCorrect;auto.
    right.
    apply lebnatCorrect;auto.
    discriminate H0.
    discriminate H0.
Qed.

Lemma cmpInStateBoolCorrect :forall (c:Cmp) (s:System) (sValid:validstate s), (exists a:idApp, inApp c a s) <-> cmpInStateBool c s = true.
Proof.
    split;intros.
    destruct H.
    unfold cmpInStateBool.
    rewrite existsb_exists.
    exists c.
    split.
    unfold getAllComponents.
    rewrite in_concat.
    destruct H.
    exists (cmp x0).
    destruct H.
    split;auto.
    rewrite in_app_iff.
    destruct H.
    left.
    rewrite in_map_iff.
    exists x0.
    split;auto.
    apply inGetValuesBack.
    exists (map_apply idApp_eq (manifest (environment s)) x).
    split;auto.
    rewrite in_map_iff.
    exists x.
    split;auto.
    apply (ifManifestThenInApps s sValid x x0);auto.
    right.
    rewrite in_map_iff.
    destruct H.
    exists x1.
    destruct_conj H.
    rewrite H3.
    split;auto.
    destruct Cmp_eq;auto.
    
    unfold cmpInStateBool in H.
    rewrite existsb_exists in H.
    destruct H.
    destruct H.
    destruct Cmp_eq in H0.
    rewrite e in H.
    apply getAllComponentsIffInApp;auto .
    discriminate H0.
Qed.

Lemma canDoThisBoolCorrect : forall (c:Cmp) (cp:CProvider) (s:System) (sValid: validstate s) (thisE : CProvider -> option Perm), canDoThis c cp s thisE <-> canDoThisBool c cp s thisE = true.
Proof.
    unfold canDoThis.
    unfold canDoThisBool.
    split;intros.
    destruct H.
    destruct H.
    destruct H.
    assert (InApp:=H).
    destruct H.
    destruct H.
    assert (getManifestAndAppFromCmp c s = (x,x1)).
    apply anyMfstThenGetAppAndMfst;auto.
    rewrite H2.
    destruct H0.
    destruct H0.
    destruct H3.
    assert (getManifestAndAppFromCmp (cmpCP cp) s = (x0,x2)).
    apply anyMfstThenGetAppAndMfst;auto.
    rewrite H5.
    
    assert (negb (cmpInStateBool c s) = false).
    rewrite negb_false_iff.
    apply cmpInStateBoolCorrect;auto.
    exists x.
    auto.
    rewrite H6.
    
    assert (negb (cmpInStateBool (cmpCP cp) s) = false).
    rewrite negb_false_iff.
    assert (inApp (cmpCP cp) x0 s).
    unfold isManifestOfApp in H0.
    unfold inApp.
    exists x2.
    auto.
    apply cmpInStateBoolCorrect;auto.
    exists x0.
    auto.
    rewrite H7.
    
    destruct idApp_eq;auto.
    destruct H4;auto.
    destruct H4;auto.
    destruct H4.
    rewrite H4.
    case_eq (thisE cp);intros.
    specialize (H8 p).
    assert (appHasPermission x p s).
    apply H8.
    left;auto.
    destruct H8.
    left.
    auto.
    apply appHasPermissionCorrect;
    auto.
    apply appHasPermissionCorrect;
    auto.
    
    case_eq (cmpEC cp);intros.
    specialize (H8 p).
    assert (appHasPermission x p s).
    apply H8.
    right.
    left.
    auto.
    apply appHasPermissionCorrect;
    auto.
    
    case_eq (appE x2);intros.
    specialize (H8 p).
    assert (appHasPermission x p s).
    apply H8.
    right.
    right.
    auto.
    apply appHasPermissionCorrect;
    auto.
    auto.
    destruct H4.
    rewrite H4.
    assert (getDefaultExpBool cp s=true).
    apply getDefaultExpCorrect;
    auto.
    rewrite H10.
    
    
    case_eq (thisE cp);intros.
    specialize (H8 p).
    assert (appHasPermission x p s).
    apply H8.
    left;auto.
    destruct H8.
    left.
    auto.
    apply appHasPermissionCorrect;
    auto.
    apply appHasPermissionCorrect;
    auto.
    
    case_eq (cmpEC cp);intros.
    specialize (H8 p).
    assert (appHasPermission x p s).
    apply H8.
    right.
    left.
    auto.
    apply appHasPermissionCorrect;
    auto.
    
    case_eq (appE x2);intros.
    specialize (H8 p).
    assert (appHasPermission x p s).
    apply H8.
    right.
    right.
    auto.
    apply appHasPermissionCorrect;
    auto.
    auto.
    
    assert (negb (cmpInStateBool c s)=false).
    rewrite<- not_true_iff_false.
    unfold not;intros.
    rewrite H0 in H.
    discriminate H.
    rewrite H0 in H.
    assert (negb (cmpInStateBool (cmpCP cp) s)=false).
    rewrite<- not_true_iff_false.
    unfold not;intros.
    rewrite H1 in H.
    discriminate H.
    rewrite H1 in H.
    remember (getManifestAndAppFromCmp c s) as am1.
    exists (fst am1).
    remember (getManifestAndAppFromCmp (cmpCP cp) s) as am2.
    exists (fst am2).
    split.
    clear H.
    rewrite negb_false_iff in H0.
    apply cmpInStateBoolCorrect in H0;auto.
    destruct H0.
    assert (getAppFromCmp c s = x).
    apply inAppThenGetAppFromCmp;auto.
    unfold getAppFromCmp in H0.
    rewrite Heqam1.
    rewrite H0.
    auto.
    exists (snd am2).
    assert (inApp (cmpCP cp) (fst am2) s).
    clear H.
    rewrite negb_false_iff in H1.
    apply cmpInStateBoolCorrect in H1;auto.
    destruct H1.
    assert (getAppFromCmp (cmpCP cp) s = x).
    apply inAppThenGetAppFromCmp;auto.
    unfold getAppFromCmp in H1.
    rewrite Heqam2.
    rewrite H1.
    auto.
    assert ( isManifestOfApp (fst am2) (snd am2) s ).
    clear H.
    assert (hip:=H2).
    unfold inApp in H2.
    destruct H2.
    destruct H.
    unfold isManifestOfApp.
    assert (x=snd am2).
    assert (getManifestFromCmp (cmpCP cp) s = x).
    apply (getManifestFromCmpCorrect x (fst am2));auto.
    rewrite Heqam2.
    unfold getManifestFromCmp in H3.
    auto.
    rewrite <-H3;auto.
    destruct am1.
    destruct am2.
    simpl in *.
    split;auto.
    split.
    clear H.
    apply (ifInAppAndMfstThenInCmp m0 i0 s);auto.
    destruct idApp_eq in H.
    right;auto.
    left.
    destruct (expC cp).
    destruct b.
    split;auto.
    intros.
    destruct (thisE cp).
    destruct H4.
    inversion H4.
    rewrite <-H6.
    apply appHasPermissionCorrect;auto.
    destruct H4.
    destruct H4.
    inversion H4.
    destruct H4.
    inversion H4.
    destruct (cmpEC cp).
    destruct H4.
    inversion H4.
    destruct H4.
    destruct H4.
    inversion H5.
    rewrite <-H7.
    apply appHasPermissionCorrect;auto.
    destruct H4.
    destruct H5.
    inversion H5.
    destruct (appE m0).
    destruct H4.
    inversion H4.
    destruct H4.
    destruct H4.
    inversion H5.
    destruct H4.
    destruct H5.
    inversion H6.
    rewrite <-H8.
    apply appHasPermissionCorrect;auto.
    destruct H4.
    inversion H4.
    destruct H4.
    destruct H4.
    inversion H5.
    destruct H4.
    destruct H5.
    inversion H6.
    discriminate H.
    case_eq (getDefaultExpBool cp s);intros;rewrite H4 in H.
    split.
    right.
    split;auto.
    apply getDefaultExpBack;auto.
    rewrite negb_false_iff in H1.
    apply cmpInStateBoolCorrect;auto .
    clear H0.
    intros.
    destruct (thisE cp).
    destruct H0.
    inversion H0.
    rewrite <-H6.
    apply appHasPermissionCorrect;auto.
    destruct H0.
    destruct H0.
    inversion H0.
    destruct H0.
    inversion H0.
    destruct (cmpEC cp).
    destruct H0.
    inversion H0.
    destruct H0.
    destruct H0.
    inversion H5.
    rewrite <-H7.
    apply appHasPermissionCorrect;auto.
    destruct H0.
    destruct H5.
    inversion H5.
    destruct (appE m0).
    destruct H0.
    inversion H0.
    destruct H0.
    destruct H0.
    inversion H5.
    destruct H0.
    destruct H5.
    inversion H6.
    rewrite <-H8.
    apply appHasPermissionCorrect;auto.
    destruct H0.
    inversion H0.
    destruct H0.
    destruct H0.
    inversion H5.
    destruct H0.
    destruct H5.
    inversion H6.
    discriminate H.
Qed.





Lemma delPermsBoolCorrect : forall (c:Cmp) (cp:CProvider) (u:uri) (pt:PType) (s:System) (sValid:validstate s), delPerms c cp u pt s <-> delPermsBool c cp u pt s = true.
Proof.
    unfold delPerms.
    unfold delPermsBool.
    split;intros.
    destruct H.
    destruct H.
    assert (negb (cmpInStateBool c s) = false).
    rewrite negb_false_iff.
    apply cmpInStateBoolCorrect;auto.
    exists x;auto.
    rewrite H1.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct_conj H0.
    assert (existsb (fun icmp : iCmp => match map_apply deltpermsdomeq (delTPerms (state s)) (icmp, cp, u) with | Value _ (Read as pt') => eq_PType pt' pt | Value _ (Write as pt') => eq_PType pt' pt | Value _ Both => true | Error _ _ => false end) (map (fun pair : iCmp * idApp => fst pair) (filter (fun pair : iCmp * idApp => if idApp_eq (getAppFromCmp c s) (snd pair) then true else false) (map (fun pair : item iCmp Cmp => (item_index pair, getAppFromCmp (item_info pair) s)) (running (state s)))))=true).
    rewrite existsb_exists.
    exists x0.
    split.
    rewrite in_map_iff.
    exists (x0, getAppFromCmp x1 s).
    split;auto.
    rewrite filter_In.
    simpl.
    split.
    rewrite in_map_iff.
    exists (Item x0 x1).
    simpl.
    split;auto.
    rewrite <-(valueIffExists).
    exact H2.
    apply runningCorrect;auto.
    assert (getAppFromCmp c s = x).
    apply inAppThenGetAppFromCmp;auto.
    assert (getAppFromCmp x1 s = x).
    apply inAppThenGetAppFromCmp;auto.
    rewrite H3.
    rewrite H5.
    destruct idApp_eq;auto.
    
    
    destruct H4; rewrite H3; auto.
    destruct pt; auto.
    rewrite H3.
    auto.
    elim (classic((existsb (fun icmp : iCmp => match map_apply deltpermsdomeq (delTPerms (state s)) (icmp, cp, u) with | Value _ (Read as pt') => eq_PType pt' pt | Value _ (Write as pt') => eq_PType pt' pt | Value _ Both => true | Error _ _ => false end) (map (fun pair : iCmp * idApp => fst pair) (filter (fun pair : iCmp * idApp => if idApp_eq (getAppFromCmp c s) (snd pair) then true else false) (map (fun pair : item iCmp Cmp => (item_index pair, getAppFromCmp (item_info pair) s)) (running (state s)))))=true)));intros.
    rewrite H2.
    auto.
    rewrite not_true_iff_false in H2.
    rewrite H2.
    clear H2.
    assert (getAppFromCmp c s = x).
    apply inAppThenGetAppFromCmp;auto.
    rewrite H2.
    destruct H0;rewrite H0.
    auto.
    destruct pt;auto.
    
    
    case_eq (negb (cmpInStateBool c s));intros;rewrite H0 in H.
    discriminate H.
    rewrite negb_false_iff in H0.
    rewrite <-cmpInStateBoolCorrect in H0;auto.
    destruct H0.
    exists x.
    split;auto.
    case_eq (existsb (fun icmp : iCmp => match map_apply deltpermsdomeq (delTPerms (state s)) (icmp, cp, u) with | Value _ (Read as pt') => eq_PType pt' pt | Value _ (Write as pt') => eq_PType pt' pt | Value _ Both => true | Error _ _ => false end) (map (fun pair : iCmp * idApp => fst pair) (filter (fun pair : iCmp * idApp => if idApp_eq (getAppFromCmp c s) (snd pair) then true else false) (map (fun pair : item iCmp Cmp => (item_index pair, getAppFromCmp (item_info pair) s)) (running (state s))))));intros;rewrite H1 in H.
    left.
    rewrite existsb_exists in H1.
    destruct H1.
    destruct H1.
    exists x0.
    rewrite in_map_iff in H1.
    destruct H1.
    destruct H1.
    rewrite filter_In in H3.
    destruct H3.
    rewrite in_map_iff in H3.
    destruct H3.
    destruct H3.
    exists (item_info x2).
    assert ( map_apply iCmp_eq (running (state s)) x0 = Value iCmp (item_info x2)).
    apply valueIffExists.
    apply runningCorrect;auto.
    rewrite <-H3 in H1;simpl in H1.
    rewrite <-H1.
    destruct x2.
    simpl.
    auto.
    split;auto.
    split.
    apply ifRunningThenInApp in H6;auto.
    destruct H6.
    rewrite <-H3 in H4;simpl in H4.
    assert (getAppFromCmp (item_info x2) s = x3).
    apply inAppThenGetAppFromCmp;auto.
    rewrite H7 in *.
    assert (getAppFromCmp c s = x).
    apply inAppThenGetAppFromCmp;auto.
    rewrite H8 in *.
    destruct idApp_eq in H4.
    rewrite e;auto.
    discriminate H4.
    case_eq (map_apply deltpermsdomeq (delTPerms (state s)) (x0, cp, u));intros;rewrite H7 in H2.
    destruct p; unfold eq_PType in H2;destruct pt;try discriminate H2.
    right;auto.
    right;auto.
    left;auto.
    left;auto.
    left;auto.
    discriminate H2.
    clear H1.
    right.
    apply inAppThenGetAppFromCmp in H0;auto.
    rewrite H0 in H.
    case_eq( map_apply delppermsdomeq (delPPerms (state s)) (x, cp, u));intros;rewrite H1 in H.
    destruct p; unfold eq_PType in H;destruct pt;try discriminate H.
    right;auto.
    right;auto.
    left;auto.
    left;auto.
    left;auto.
    discriminate H.
Qed.

Lemma isiCmpRunningCorrect : forall (ic:iCmp) (s:System) (sValid : validstate s), cmpRunning ic s <-> isiCmpRunningBool ic s =true.
Proof.
    unfold cmpRunning.
    unfold isiCmpRunningBool.
    split;intros.
    destruct H.
    destruct H.
    destruct_conj H.
    unfold InBool.
    rewrite existsb_exists.
    exists ic.
    assert (In ic (map_getKeys (running (state s)))).
    rewrite valueIffExists in H.
    unfold map_getKeys.
    rewrite in_map_iff.
    exists {| item_index := ic; item_info := x0 |}.
    split;auto.
    apply runningCorrect;auto.
    destruct iCmp_eq;auto.
    
    unfold InBool in H.
    rewrite existsb_exists in H.
    destruct H.
    destruct H.
    rewrite <-(valueIffInGetKeys iCmp_eq) in H.
    unfold is_Value in H.
    case_eq (map_apply iCmp_eq (running (state s)) x);intros;rewrite H1 in H. 
    destruct iCmp_eq in H0.
    rewrite e.
    assert (~isCProvider c).
    apply (notCPRunningVS s sValid x);auto.
    assert (H3:=H1).
    apply ifRunningThenInApp in H1;auto.
    destruct H1.
    exists x0.
    exists c.
    auto.
    discriminate H0.
    destruct H.
    apply runningCorrect;auto.
Qed.

Lemma canBeStartedCorrect:forall (c:Cmp) (s:System) (sValid:validstate s), canBeStarted c s -> canBeStartedBool c s = true.
Proof.
    unfold canBeStarted.
    unfold canBeStartedBool.
    intros.
    unfold isSomethingBool.
    unfold isNil.
    unfold isSomeTrue.
    destruct c; destruct H.
    rewrite H.
    apply orb_true_l.
    destruct H.
    rewrite H.
    rewrite H0.
    auto.
    
    rewrite H.
    apply orb_true_l.
    destruct H.
    rewrite H.
    rewrite H0.
    auto.
    
    rewrite H.
    apply orb_true_l.
    destruct H.
    rewrite H.
    assert (getDefaultExpBool c s=true).
    apply getDefaultExpCorrect;auto.
    rewrite H1.
    auto.
    
    rewrite H.
    apply orb_true_l.
    destruct H.
    rewrite H.
    rewrite H0.
    auto.
Qed.

Lemma canBeStartedBack:forall (c:Cmp) (s:System) (sValid:validstate s), (exists a:idApp, inApp c a s) -> canBeStartedBool c s = true -> canBeStarted c s.
Proof.
    unfold canBeStarted.
    unfold canBeStartedBool.
    intros.
    unfold isSomeTrue in H0.
    unfold isSomethingBool in H0.
    unfold isNil in H0.
    
    destruct c.
    case_eq (expA a);intros;rewrite H1 in H0.
    case_eq b;intros;rewrite H2 in H0;simpl in H.
    left;auto.
    discriminate H0.
    case_eq (intFilterA a);intros;rewrite H2 in H0;simpl in H.
    right;auto.
    discriminate H0.
    
    case_eq (expS s0);intros;rewrite H1 in H0.
    case_eq b;intros;rewrite H2 in H0;simpl in H.
    left;auto.
    discriminate H0.
    case_eq (intFilterS s0);intros;rewrite H2 in H0;simpl in H.
    right;auto.
    discriminate H0.
    
    case_eq (expC c);intros;rewrite H1 in H0.
    case_eq b;intros;rewrite H2 in H0;simpl in H.
    left;auto.
    discriminate H0.
    case_eq (getDefaultExpBool c s);intros;rewrite H2 in H0;simpl in H.
    right.
    split;auto.
    apply getDefaultExpBack;auto.
    discriminate H0.
    
    case_eq (expB b);intros;rewrite H1 in H0.
    case_eq b0;intros;rewrite H2 in H0;simpl in H.
    left;auto.
    discriminate H0.
    case_eq (intFilterB b);intros;rewrite H2 in H0;simpl in H.
    right;auto.
    discriminate H0.
Qed.


Lemma canStartCorrect : forall (c1 c2: Cmp)(s:System) (sValid: validstate s), canStart c1 c2 s <-> canStartBool c1 c2 s = true.
Proof.
    unfold canStart.
    unfold canStartBool.
    split;intros.
    destruct H.
    destruct H.
    destruct_conj H.
    assert (cmpInStateBool c1 s = true).
    apply cmpInStateBoolCorrect;auto.
    exists x;auto.
    rewrite H1.
    assert (cmpInStateBool c2 s = true).
    apply cmpInStateBoolCorrect;auto.
    exists x0;auto.
    rewrite H3.
    simpl.
    destruct H0.
    destruct H0.
    assert (getManifestAndAppFromCmp c1 s = (x,x1)).
    apply anyMfstThenGetAppAndMfst;auto.
    rewrite H5.
    assert (getAppFromCmp c2 s = x0).
    apply inAppThenGetAppFromCmp;auto.
    rewrite H6.
    destruct idApp_eq.
    auto.
    destruct H2.
    contradiction.
    destruct H2.
    assert (canBeStartedBool c2 s = true).
    apply canBeStartedCorrect;auto.
    rewrite H8.
    simpl.
    destruct c2.
    
    destruct (cmpEA a).
    assert (appHasPermission x p s).
    specialize (H7 p x1).
    apply H7.
    split;auto.
    apply appHasPermissionCorrect;auto.
    
    case_eq (appE x1);intros;auto.
    assert (appHasPermission x p s).
    specialize (H7 p x1).
    apply H7.
    split;auto.
    apply appHasPermissionCorrect;auto.
    
    case_eq (cmpES s0);intros;auto.
    assert (appHasPermission x p s).
    specialize (H7 p x1).
    apply H7.
    split;auto.
    apply appHasPermissionCorrect;auto.
    
    case_eq (appE x1);intros;auto.
    assert (appHasPermission x p s).
    specialize (H7 p x1).
    apply H7.
    split;auto.
    apply appHasPermissionCorrect;auto.
    
    case_eq (cmpEC c);intros;auto.
    assert (appHasPermission x p s).
    specialize (H7 p x1).
    apply H7.
    split;auto.
    apply appHasPermissionCorrect;auto.
    
    case_eq (appE x1);intros;auto.
    assert (appHasPermission x p s).
    specialize (H7 p x1).
    apply H7.
    split;auto.
    apply appHasPermissionCorrect;auto.
    
    case_eq (cmpEB b);intros;auto.
    assert (appHasPermission x p s).
    specialize (H7 p x1).
    apply H7.
    split;auto.
    apply appHasPermissionCorrect;auto.
    
    case_eq (appE x1);intros;auto.
    assert (appHasPermission x p s).
    specialize (H7 p x1).
    apply H7.
    split;auto.
    apply appHasPermissionCorrect;auto.
    
    
    case_eq (negb (cmpInStateBool c1 s));intros;rewrite H0 in H.
    discriminate H.
    case_eq (negb (cmpInStateBool c2 s));intros;rewrite H1 in H.
    discriminate H.
    case_eq (getManifestAndAppFromCmp c1 s);intros;rewrite H2 in H.
    rewrite negb_false_iff in H1, H0.
    apply cmpInStateBoolCorrect in H0;auto.
    apply cmpInStateBoolCorrect in H1;auto.
    destruct H0, H1.
    
    assert (H3:=H0).
    destruct H0.
    assert (getManifestAndAppFromCmp c1 s = (x,x1)).
    destruct H0.
    apply anyMfstThenGetAppAndMfst;auto. 
    exists x.
    exists x0.
    split;auto.
    split;auto.
    rewrite H2 in H4.
    inversion H4.
    rewrite H6 in *.
    rewrite H7 in *.
    case_eq (idApp_eq x (getAppFromCmp c2 s));intros;rewrite H5 in H.
    assert (getAppFromCmp c2 s = x0).
    apply inAppThenGetAppFromCmp;auto.
    rewrite<- H8.
    left;auto.
    rewrite andb_true_iff in H.
    destruct H.
    right.
    split.
    apply canBeStartedBack;auto.
    exists x0;auto.
    intros.
    destruct H9.
    assert (m0=x1).
    destruct H0.
    destruct H9.
    destruct H0.
    rewrite H9 in H0.
    inversion H0;auto.
    destruct H0.
    destruct_conj H0.
    absurd (In x (apps (state s)) /\ In x2 (systemImage (environment s)) /\ idSI x2 = x).
    apply sysAppInApps;auto.
    split;auto.
    apply (ifManifestThenInApps s sValid x m0);auto.
    destruct H0.
    destruct H9.
    destruct_conj H9.
    absurd (In x (apps (state s)) /\ In x2 (systemImage (environment s)) /\ idSI x2 = x).
    apply sysAppInApps;auto.
    split;auto.
    apply (ifManifestThenInApps s sValid x x1);auto.
    destruct H0, H9.
    destruct_conj H0.
    destruct_conj H9.
    assert (x3=x2).
    rewrite <- H0 in H9.
    apply (notDupSysAppVS s);auto.
    rewrite H15 in H16.
    rewrite H16 in H14.
    auto.
    rewrite H11 in H10.
    destruct c2.
    
    destruct (cmpEA a);destruct H10;inversion H10.
    rewrite <-H13.
    apply appHasPermissionCorrect;auto.
    inversion H12.
    destruct (appE x1);inversion H13.
    rewrite <-H15.
    apply appHasPermissionCorrect;auto.
    
    destruct (cmpES s0);destruct H10;inversion H10.
    rewrite <-H13.
    apply appHasPermissionCorrect;auto.
    inversion H12.
    destruct (appE x1);inversion H13.
    rewrite <-H15.
    apply appHasPermissionCorrect;auto.
    
    destruct (cmpEC c);destruct H10;inversion H10.
    rewrite <-H13.
    apply appHasPermissionCorrect;auto.
    inversion H12.
    destruct (appE x1);inversion H13.
    rewrite <-H15.
    apply appHasPermissionCorrect;auto.
    
    destruct (cmpEB b);destruct H10;inversion H10.
    rewrite <-H13.
    apply appHasPermissionCorrect;auto.
    inversion H12.
    destruct (appE x1);inversion H13.
    rewrite <-H15.
    apply appHasPermissionCorrect;auto.
Qed.

Lemma inAppGetAllCmp : forall (c:Cmp) (a:idApp) (s:System) (sValid:validstate s), inApp c a s -> In c (getAllCmps a s).
Proof.
    unfold inApp.
    unfold getAllCmps.
    intros.
    destruct H.
    destruct H.
    destruct H.
    rewrite H.
    auto.
    case_eq (map_apply idApp_eq (manifest (environment s)) a);intros.
    destruct H.
    destruct_conj H.
    assert (In a (apps (state s))).
    apply (ifManifestThenInApps s sValid a m);auto.
    absurd (In a (apps (state s)) /\ In x0 (systemImage (environment s)) /\ idSI x0 = a).
    apply (sysAppInApps);auto.
    auto.
    destruct H.
    assert (hd defaultSysApp (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s)))=x0).
    remember (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) as theFun.
    destruct_conj H.
    assert (In (hd defaultSysApp (filter theFun (systemImage (environment s)))) (systemImage (environment s)) /\ theFun (hd defaultSysApp (filter theFun (systemImage (environment s)))) =true).
    apply ifExistsFilter.
    exists x0.
    rewrite filter_In.
    split;auto.
    rewrite HeqtheFun.
    rewrite H.
    destruct idApp_eq;auto.
    remember ( hd defaultSysApp (filter theFun (systemImage (environment s)))) as theHead.
    destruct H3.
    rewrite HeqtheFun in H5.
    destruct idApp_eq in H5.
    rewrite e in H.
    apply (notDupSysAppVS s);auto.
    discriminate H5.
    rewrite H2.
    destruct_conj H.
    rewrite H5.
    auto.
Qed.


Lemma getAllCmpInstalledInApp : forall (c:Cmp) (a:idApp) (s:System) (sValid:validstate s), In c (getAllCmps a s) /\ isAppInstalled a s -> inApp c a s.
Proof.
    unfold getAllCmps.
    unfold isAppInstalled.
    unfold inApp.
    intros.
    destruct H.
    destruct H0.
    assert (exists m:Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m).
    apply (ifInAppsThenManifest);auto.
    destruct H1.
    rewrite H1 in *.
    exists x.
    split;auto.
    assert (~(exists m:Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m)).
    assert (~ (In a (apps (state s)))).
    unfold not;intros.
    destruct H0.
    absurd (In a (apps (state s)) /\ In x (systemImage (environment s)) /\ idSI x = a).
    apply (sysAppInApps);auto.
    auto.
    unfold not;intros.
    apply H1.
    destruct H2.
    apply (ifManifestThenInApps s sValid a x);auto.
    case_eq (map_apply idApp_eq (manifest (environment s)) a);intros.
    absurd (exists m:Manifest, map_apply idApp_eq (manifest (environment s)) a = Value idApp m).
    auto.
    exists m.
    auto.
    rewrite H2 in *.
    destruct H0.
    exists (manifestSI x).
    assert ((hd defaultSysApp (filter (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) (systemImage (environment s))))=x).
    remember (fun sysapp : SysImgApp => if idApp_eq a (idSI sysapp) then true else false) as theFun.
    destruct H0.
    assert (In (hd defaultSysApp (filter theFun (systemImage (environment s)))) (systemImage (environment s)) /\ theFun (hd defaultSysApp (filter theFun (systemImage (environment s))))=true).
    apply ifExistsFilter.
    exists x.
    rewrite filter_In.
    rewrite HeqtheFun.
    rewrite H3.
    destruct idApp_eq;auto.
    destruct H3.
    remember (hd defaultSysApp (filter theFun (systemImage (environment s)))) as theHead.
    rewrite HeqtheFun in *.
    destruct idApp_eq in H4; destruct H4.
    apply (notDupSysAppVS s);auto.
    discriminate H4.
    rewrite H3 in H.
    split;auto.
    right.
    exists x.
    destruct H0.
    auto.
Qed.
Lemma actionTestCorrect : forall (i:Intent) (iFil:intentFilter) (s:System), actionTest i iFil <-> actionTestBool i iFil s=true.
Proof.
    unfold actionTest. 
    unfold actionTestBool. 
    split;intros.
    destruct H; destruct H.
    rewrite H.
    case_eq (actFilter iFil);intros.
    auto.
    unfold isNil.
    auto.
    destruct H.
    rewrite H.
    unfold InBool.
    rewrite existsb_exists.
    exists x.
    destruct intentAction_eq;split;auto.
    
    destruct (action i).
    right.
    unfold InBool in H.
    rewrite existsb_exists in H.
    destruct H.
    exists x.
    destruct H.
    destruct intentAction_eq in H0.
    rewrite e;auto.
    discriminate H0.
    left.
    split;auto.
    rewrite negb_true_iff in H.
    rewrite <-not_true_iff_false in H.
    unfold not;intros.
    apply H.
    rewrite H0.
    auto.
Qed.


Lemma categoryTestCorrect : forall (i:Intent) (iFil:intentFilter) (s:System), categoryTest i iFil <-> categoryTestBool i iFil s=true.
Proof.
    unfold categoryTest. 
    unfold categoryTestBool. 
    split;intros.
    destruct H.
    rewrite H.
    auto.
    destruct H.
    destruct H.
    case_eq x;intros; rewrite H; rewrite H1.
    auto.
    rewrite negb_true_iff.
    rewrite <-not_true_iff_false.
    unfold not;intros.
    rewrite existsb_exists in H2.
    destruct H2.
    destruct H2.
    specialize (H0 x0).
    assert (In x0 x).
    rewrite H1.
    auto.
    specialize (H0 H4).
    rewrite negb_true_iff in H3.
    rewrite <-not_true_iff_false in H3.
    apply H3.
    unfold InBool.
    rewrite existsb_exists.
    exists x0.
    destruct Category_eq;split;auto.
    
    case_eq (category i);intros;rewrite H0 in H.
    left;auto.
    right.
    exists (category i).
    split;auto.
    intros.
    apply NNPP.
    unfold not;intro.
    rewrite negb_true_iff in H.
    rewrite <-not_true_iff_false in H.
    apply H.
    rewrite existsb_exists.
    exists cat.
    rewrite <-H0.
    split;auto.
    unfold InBool.
    rewrite negb_true_iff.
    rewrite <-not_true_iff_false.
    unfold not;intros.
    apply H2.
    rewrite existsb_exists in H3.
    destruct H3.
    destruct H3.
    destruct Category_eq in H4.
    rewrite e;auto.
    discriminate H4.
Qed.



Lemma inGetSomes : forall (A B:Set) (f:A-> option B) (l:list A) (b:B), (exists a:A, In a l /\ f a = Some b) <-> In b (getSomes A B f l).
Proof.
    split;intros.
    induction l.
    destruct H.
    destruct H.
    inversion H.
    destruct H.
    destruct H.
    elim (classic (x=a));intros.
    rewrite <-H1.
    simpl.
    rewrite H0.
    apply in_eq.
    inversion H.
    symmetry in H2.
    contradiction.
    simpl.
    assert (In b (getSomes A B f l)).
    apply IHl.
    exists x.
    auto.
    case_eq (f a);intros;auto.
    apply in_cons;auto.
    
    functional induction (getSomes A B f l).
    inversion H.
    inversion H.
    exists x.
    split.
    apply in_eq.
    rewrite <-H0.
    auto.
    specialize (IHl0 H0).
    destruct IHl0.
    exists x0.
    destruct H1.
    split;auto.
    apply in_cons;auto.
    specialize (IHl0 H).
    destruct IHl0.
    destruct H0.
    exists x0.
    split;auto.
    apply in_cons;auto.
Qed.


Lemma dataTestCorrect : forall (i:Intent) (iFil:intentFilter) (s:System), dataTest i iFil <-> dataTestBool i iFil s=true.
Proof.
    unfold dataTest. 
    unfold dataTestBool. 
    unfold notUriAndNotMimeBool.
    unfold uriAndNotMimeBool.
    unfold notUriAndMimeBool.
    unfold uriAndMimeBool.
    unfold isSomethingBool.
    unfold isNil.
    split;intros.
    destruct H; destruct H.
    destruct H0.
    rewrite H.
    rewrite H0.
    rewrite H1.
    auto.
    destruct H.
    destruct H0.
    destruct H1.
    case_eq (path (data i));intros;auto.
    rewrite H0.
    assert (InBool Data Data_eq (data i) (dataFilter iFil)=true).
    unfold InBool.
    rewrite existsb_exists.
    exists x.
    destruct H1.
    rewrite H1.
    destruct Data_eq;auto.
    rewrite H3;auto.
    destruct H.
    destruct H.
    rewrite H.
    destruct H0.
    destruct H1.
    destruct H1.
    case_eq (mime (data i));intros;auto.
    assert (InBool Data Data_eq (data i) (dataFilter iFil)=true).
    unfold InBool.
    rewrite existsb_exists.
    exists x.
    rewrite H1.
    destruct Data_eq;auto.
    rewrite H4.
    auto.
    destruct H.
    case_eq (path (data i));intros;auto.
    destruct H0.
    destruct H2.
    destruct H2.
    destruct_conj H2.
    case_eq (mime (data i));intros;auto.
    assert (InBool mimeType mimeType_eq m (getSomes Data mimeType mime (dataFilter iFil))=true).
    unfold InBool.
    rewrite existsb_exists.
    exists m.
    split.
    apply inGetSomes.
    exists x.
    rewrite<- H5.
    auto.
    destruct mimeType_eq;auto.
    rewrite H7.
    destruct H4.
    assert (InBool uri uri_eq u (getSomes Data uri path (dataFilter iFil))=true).
    unfold InBool.
    rewrite existsb_exists.
    exists u.
    split.
    apply inGetSomes.
    exists x0.
    rewrite<- H1.
    auto.
    destruct uri_eq;auto.
    rewrite H8.
    auto.
    
    destruct H4.
    assert (isContentOrFileBool i = true).
    unfold isContentOrFileBool.
    destruct H4.
    rewrite H4.
    unfold eqDataType.
    auto.
    unfold eqDataType.
    rewrite H4.
    auto.
    rewrite H9.
    assert (existsb (fun maybe : option uri => negb match maybe with | Some _ => true | None => false end) (map path (dataFilter iFil))=true).
    rewrite existsb_exists.
    exists None.
    split;auto.
    rewrite in_map_iff.
    exists x0.
    auto.
    rewrite H10.
    assert ((InBool uri uri_eq u (getSomes Data uri path (dataFilter iFil)) || true && true)=true).
    apply orb_true_r.
    rewrite H11.
    auto.
    unfold uriAndMime.
    unfold notUriAndNotMime.
    unfold uriAndNotMime.
    unfold notUriAndMime.
    case_eq (path (data i));intro thepath0;try intro thepath1;try rewrite thepath0 in *;try rewrite thepath1 in *;
    case_eq (mime (data i));intro themime0;try intro themime1;try rewrite themime0 in *;try rewrite themime1 in *;
    case_eq (dataFilter iFil);intro thedfilter0;try intro thedfilter1;try intro thedfilter2;try rewrite thedfilter0 in *;try rewrite thedfilter1 in *;try rewrite thedfilter2 in *.
    
    
    simpl in H.
    discriminate H.
    rewrite orb_true_iff in H.
    destruct H.
    rewrite orb_true_iff in H.
    destruct H.
    rewrite orb_true_iff in H.
    destruct H.
    simpl in H.
    discriminate H.
    simpl in H.
    discriminate H.
    discriminate H.
    rewrite andb_true_iff in H.
    unfold InBool in H.
    destruct H.
    rewrite existsb_exists in H.
    destruct H.
    destruct H.
    right.
    right.
    rewrite orb_true_iff in H0.
    destruct H0.
    rewrite existsb_exists in H0.
    destruct H0.
    destruct H0.
    right.
    split.
    unfold not;intros;inversion H3.
    split.
    unfold not;intros;inversion H3.
    rewrite <-inGetSomes in H.
    destruct H.
    destruct H.
    rewrite <-inGetSomes in H0.
    destruct H0.
    destruct H0.
    destruct mimeType_eq in H1.
    rewrite e.
    exists x1.
    destruct uri_eq in H2.
    rewrite e0.
    exists x2.
    auto.
    discriminate H2.
    discriminate H1.
    right.
    
    
    split.
    unfold not;intros;inversion H2.
    split.
    unfold not;intros;inversion H2.
    rewrite <-inGetSomes in H.
    destruct H.
    destruct H.
    destruct mimeType_eq in H1.
    rewrite e.
    exists x0.
    rewrite andb_true_iff in H0.
    destruct H0.
    rewrite existsb_exists in H3.
    destruct H3.
    destruct H3.
    rewrite in_map_iff in H3.
    destruct H3.
    destruct H3.
    exists x2.
    split;auto.
    split;auto.
    split;auto.
    destruct x1.
    rewrite negb_true_iff in H4.
    discriminate H4.
    right.
    split.
    unfold isContentOrFileBool in H0.
    unfold isContentOrFile.
    rewrite orb_true_iff in H0.
    destruct H0.
    left.
    case_eq (type (data i));intros;rewrite H6 in H0;simpl in H0;try discriminate H0.
    auto.
    right.
    case_eq (type (data i));intros;rewrite H6 in H0;simpl in H0;try discriminate H0.
    auto.
    auto.
    discriminate H1.
    
    simpl in H.
    discriminate H.
    simpl in H.
    rewrite orb_false_r in H.
    rewrite orb_false_r in H.
    right.
    rewrite orb_true_iff in H.
    destruct H.
    destruct Data_eq in H.
    rewrite e.
    left.
    split.
    unfold not;intros;inversion H0.
    split;auto.
    exists thedfilter0.
    split;auto.
    apply in_eq.
    discriminate H.
    left.
    split.
    unfold not;intros;inversion H0.
    split;auto.
    exists (data i).
    split;auto.
    apply in_cons.
    unfold InBool in H.
    rewrite existsb_exists in H.
    destruct H.
    destruct H.
    destruct Data_eq in H0.
    rewrite e;auto.
    discriminate H0.
    simpl in H.
    discriminate H.
    simpl in H.
    
    rewrite orb_false_r in H.
    rewrite orb_true_iff in H.
    right.
    right.
    left.
    split;auto.
    split.
    unfold not;intros;inversion H0.
    exists (data i).
    split;auto.
    destruct H.
    destruct Data_eq in H.
    rewrite e.
    apply in_eq.
    discriminate H.
    apply in_cons.
    unfold InBool in H.
    rewrite existsb_exists in H.
    destruct H.
    destruct H.
    destruct Data_eq in H0.
    rewrite e;auto.
    discriminate H0.
    
    simpl in H.
    left.
    auto.
    simpl in H.
    discriminate H.
Qed.

Lemma canGrantCorrect: forall (cp:CProvider) (u:uri) (s:System) (sValid:validstate s), canGrant cp u s <-> canGrantBool cp u s = true.
Proof.
    unfold canGrant.
    unfold canGrantBool.
    split;intros.
    destruct H.
    destruct H.
    destruct H0.
    assert ( InBool Cmp Cmp_eq (cmpCP cp) (getAllComponents s) =true).
    unfold InBool.
    rewrite existsb_exists.
    exists (cmpCP cp).
    split.
    unfold getAllComponents.
    rewrite in_concat.
    destruct H.
    destruct H.
    exists (cmp x0).
    rewrite in_app_iff.
    split;auto.
    destruct H.
    left.
    rewrite in_map_iff.
    exists x0.
    split;auto.
    apply inGetValuesBack.
    exists (Value idApp x0).
    split;auto.
    rewrite in_map_iff.
    exists x.
    split;auto.
    apply (ifManifestThenInApps s sValid x x0);auto.
    right.
    rewrite in_map_iff.
    destruct H.
    destruct_conj H.
    exists x1.
    rewrite H4.
    auto.
    destruct Cmp_eq;auto.
    rewrite H1.
    rewrite andb_true_l.
    assert (InBool uri uri_eq u (uriP cp)=true).
    unfold InBool.
    rewrite existsb_exists.
    exists u.
    destruct uri_eq;auto.
    rewrite H2;auto.
    destruct H0.
    assert (isNil uri (uriP cp)=true).
    unfold isNil.
    case_eq (uriP cp);intros.
    auto.
    absurd ((exists u' : uri, In u' (uriP cp))).
    auto.
    exists u0.
    rewrite H2.
    apply in_eq;auto.
    rewrite H2.
    rewrite H1.
    simpl.
    rewrite orb_true_r.
    rewrite andb_true_r.
    unfold InBool.
    rewrite existsb_exists.
    exists (cmpCP cp).
    split.
    apply getAllComponentsIffInApp;auto.
    exists x;auto.
    destruct Cmp_eq;auto.
    
    rewrite andb_true_iff in H.
    destruct H.
    rewrite orb_true_iff in H0.
    assert (exists a:idApp, inApp (cmpCP cp) a s).
    rewrite andb_true_iff in H0.
    apply getAllComponentsIffInApp;auto.
    unfold InBool in H.
    rewrite existsb_exists in H.
    destruct H.
    destruct H.
    destruct Cmp_eq in H1.
    rewrite e;auto.
    discriminate H1.
    destruct H1.
    exists x.
    split;auto.
    destruct H0.
    left.
    unfold InBool in H0.
    rewrite existsb_exists in H0.
    destruct H0.
    destruct H0.
    destruct uri_eq in H2.
    rewrite e;auto.
    discriminate H2.
    right.
    rewrite andb_true_iff in H0.
    destruct H0.
    split;auto.
    case_eq (uriP cp);intros;rewrite H3 in H0;simpl in H0.
    rewrite <-inNotNilExists.
    unfold not.
    intro.
    apply H4.
    auto.
    discriminate H0.
Qed.

Lemma inttForAppMaybeIntt : forall (i:Intent) (a:idApp) (c:Cmp) (ic:iCmp) (s:System) (sValid:validstate s),
    intentForApp i a c ic s -> maybeIntentForAppCmp i a ic s = Some c.
Proof.
    unfold intentForApp.
    unfold maybeIntentForAppCmp.
    intros.
    destruct_conj H.
    assert (negb (InBool (iCmp * Intent) sentintentseq (ic, i) (sentIntents (state s)))=false).
    rewrite negb_false_iff.
    unfold InBool.
    rewrite existsb_exists.
    exists (ic,i).
    destruct sentintentseq;auto.
    rewrite H1.
    rewrite H0.
    remember (fun installedcomp : Cmp => if idCmp_eq (getCmpId c) (getCmpId installedcomp) then true else false) as theFilterFun.
    assert (theFilterFun c =true).
    rewrite HeqtheFilterFun.
    destruct idCmp_eq;auto.
    assert (In c (filter theFilterFun (getAllCmps a s))).
    rewrite filter_In.
    split;auto.
    apply inAppGetAllCmp;auto.
    case_eq (filter theFilterFun (getAllCmps a s));intros.
    rewrite H5 in H4.
    inversion H4.
    assert (In c0 (filter theFilterFun (getAllCmps a s))).
    rewrite H5.
    apply in_eq;auto.
    rewrite filter_In in H6.
    destruct H6.
    assert (inApp c0 a s).
    apply getAllCmpInstalledInApp;auto.
    assert (isAppInstalled a s).
    unfold inApp in H2.
    destruct H2.
    unfold isAppInstalled.
    destruct H2.
    destruct H2.
    left.
    apply (ifManifestThenInApps s sValid a x);auto.
    right.
    destruct H2.
    exists x0.
    destruct_conj H2.
    auto.
    auto.
    assert (c=c0).
    rewrite HeqtheFilterFun in H7.
    destruct idCmp_eq in H7.
    apply (inAppSameCmpId s sValid c c0 a a);auto.
    discriminate H7.
    rewrite H9.
    assert (negb (isAppInstalledBool a s)=false).
    rewrite negb_false_iff.
    apply isAppInstalled_iff.
    destruct H8.
    destruct H8.
    unfold isAppInstalled.
    destruct H8.
    left.
    apply (ifManifestThenInApps s sValid a x);auto.
    right.
    destruct H8.
    destruct_conj H8.
    exists x0;auto.
    rewrite H10.
    auto.
Qed.


Lemma inttForAppMaybeInttBack : forall (i:Intent) (a:idApp) (c:Cmp) (ic:iCmp) (s:System) (sValid:validstate s),
    maybeIntentForAppCmp i a ic s = Some c -> intentForApp i a c ic s.
Proof.
    unfold intentForApp.
    unfold maybeIntentForAppCmp.
    intros.
    case_eq (negb (isAppInstalledBool a s));intros;rewrite H0 in H.
    inversion H.
    rewrite negb_false_iff in H0.
    rewrite <-isAppInstalled_iff in H0.
    case_eq (negb (InBool (iCmp * Intent) sentintentseq (ic, i) (sentIntents (state s))));intros;rewrite H1 in H.
    inversion H.
    rewrite negb_false_iff in H1.
    destruct (cmpName i).
    case_eq ( filter (fun installedcomp : Cmp => if idCmp_eq i0 (getCmpId installedcomp) then true else false) (getAllCmps a s));intros;rewrite H2 in H.
    inversion H.
    inversion H.
    rewrite H4 in *.
    assert (In c (c::l)).
    apply in_eq.
    rewrite <-H2 in H3.
    rewrite filter_In in H3.
    destruct H3.
    destruct idCmp_eq in H5.
    rewrite e.
    split;auto.
    split.
    unfold InBool in H1.
    rewrite existsb_exists in H1.
    destruct H1.
    destruct H1.
    destruct sentintentseq in H6.
    rewrite e0;auto.
    discriminate H6.
    apply getAllCmpInstalledInApp;auto.
    discriminate H5.
    inversion H.
Qed.

Lemma ifNotNoneThenSomething : forall (m : option idGrp), ~(m = None) -> (exists (g:idGrp), m = Some g).
Proof.
  intros.
  destruct m.
  - exists i. auto.
  - destruct H. auto. 
Qed.

Lemma ifInPermsOfGroupThenSome : forall (p: Perm) (g: idGrp) (a: idApp) (s: System),
  In p (getPermsOfGroup g a s) -> maybeGrp p = Some g.
Proof.
  intros.
  unfold getPermsOfGroup in H.
  generalize dependent p.
  induction (grantedPermsForApp a s).
  intros.
  simpl in H. inversion H.
  intros. simpl in H.

  case_eq (maybeGrp a0); intros.
  rewrite H0 in *.
  destruct (idGrp_eq g i). simpl in H.
  destruct H.
  rewrite e, <- H. auto.  
  apply IHl. auto.
  apply IHl. auto.
  rewrite H0 in H.
  apply IHl. auto.
Qed.


End AuxLemmas.
