Require Import WitnessesFactory.
Require Import Estado.
Require Import DefBasicas.
Require Import Semantica.
Require Import Maps.
Require Import ListAuxFuns.

Definition witnessPerm :=
    perm witnessPermId (Some witnessPermGrp) dangerous.

Definition witnessState : State :=
    st (a1::a2::nil)
       (a1::a2::nil)
       (addAppValue (list idGrp) a2 (witnessPermGrp::nil) (addAppValue (list idGrp) a1 (witnessPermGrp::nil) emptyPermGroups))
       (addAppValue (list Perm) a2 nil (addAppValue (list Perm) a1 nil emptyPerms))
       emptyRunning
       emptyDelPPerms
       emptyDelTPerms
       emptyResCont
       nil.

Definition a1Mfst :=
    simpleManifest nil (witnessPerm :: nil) nil.

Definition a2Mfst :=
    simpleManifest nil nil (witnessPerm::nil).

Definition witnessEnv : Environment :=
    env 
    (map_add idApp_eq (map_add idApp_eq emptyManifests a1 a1Mfst) a2 a2Mfst)
    (map_add idApp_eq (map_add idApp_eq emptyCerts a1 c) a2 c)
    (map_add idApp_eq (map_add idApp_eq emptyDefPerms a1 nil) a2 (witnessPerm::nil))
    nil.

Definition witnessSys : System :=
    sys witnessState witnessEnv.

Lemma noInAppWitnessSts : forall
(c : Cmp)
(a : idApp),
~(inApp c a witnessSys).
Proof.
    unfold not;intros.
    assert (idappa12:=idAppa1a2Right).
    destruct idappa12 as [proof12 idappa12].
    assert (idappa21:=idAppa2a1Right).
    destruct idappa21 as [proof21 idappa21].
    assert (idappa11:=idAppAALeft a1).
    destruct idappa11 as [proof11 idappa11].
    assert (idappa22:=idAppAALeft a2).
    destruct idappa22 as [proof22 idappa22].
    destruct H.
    destruct H.
    destruct H.
    simpl in H.
    rewrite idappa12 in H.
    simpl in H.
    destruct idApp_eq in H.
    inversion H.
    rewrite <-H2 in H0.
    simpl in H0.
    destruct H0.
    destruct idApp_eq in H.
    inversion H.
    rewrite <-H2 in H0.
    simpl in H0.
    destruct H0.
    inversion H.
    simpl in H.
    destruct H.
    destruct H.
    destruct H.
Qed.

Lemma defPermsOnWitnessSys : forall
    (l:list Perm)
    (a:idApp)
    (lIsDefPermForApp : defPermsForApp witnessSys a l)
    (lNotNil:l<>nil),
    a=a2 /\ l=(witnessPerm::nil).
Proof.
    intros.
    assert (idappa12:=idAppa1a2Right).
    destruct idappa12 as [proof12 idappa12].
    assert (idappa21:=idAppa2a1Right).
    destruct idappa21 as [proof21 idappa21].
    assert (idappa11:=idAppAALeft a1).
    destruct idappa11 as [proof11 idappa11].
    assert (idappa22:=idAppAALeft a2).
    destruct idappa22 as [proof22 idappa22].
    unfold defPermsForApp in lIsDefPermForApp.
    destruct lIsDefPermForApp.
    simpl in H.
    rewrite idappa12 in H.
    simpl in H.
    destruct (idApp_eq a a1).
    inversion H.
    destruct lNotNil.
    auto.
    destruct (idApp_eq a a2).
    inversion H.
    auto.
    inversion H.
    simpl in H.
    destruct H.
    destruct H.
    inversion H.
Qed.

Lemma WitnessStateIsValid : validstate witnessSys.
Proof.
    assert (idappa12:=idAppa1a2Right).
    destruct idappa12 as [proof12 idappa12].
    assert (idappa21:=idAppa2a1Right).
    destruct idappa21 as [proof21 idappa21].
    assert (idappa11:=idAppAALeft a1).
    destruct idappa11 as [proof11 idappa11].
    assert (idappa22:=idAppAALeft a2).
    destruct idappa22 as [proof22 idappa22].

    unfold validstate.
    split.

    unfold allCmpDifferent.
    intros.
    absurd (inApp c1 a1 witnessSys);auto.
    apply noInAppWitnessSts.
    split.

    unfold notRepeatedCmps.
    intros.
    absurd (inApp c a1 witnessSys);auto.
    apply noInAppWitnessSts.

    split.
    unfold notCPrunning.
    intros.
    simpl in H.
    inversion H.

    split.
    unfold delTmpRun.
    intros.
    simpl in H.
    inversion H.

    split.
    unfold cmpRunAppIns.
    simpl.
    intros.
    inversion H.

    split.
    unfold resContAppInst.
    simpl.
    intros.
    inversion H.

    split.
    unfold statesConsistency.
    intros.

    simpl.
    rewrite idappa12.
    assert (idappaAA:=idAppAALeft a).
    destruct idappaAA as [proofAA idappaAA].

    split.
    split;[intro theOrs; destruct theOrs;[idtac|destruct H];try rewrite<-H |intro theExists;destruct theExists;simpl in H;destruct (idApp_eq a a1);[left;auto|(destruct (idApp_eq a a2);[right;left;auto|inversion H])]].
    exists a1Mfst;simpl;rewrite H;rewrite idappaAA;auto.
    exists a2Mfst;simpl;rewrite idappa21;rewrite H;rewrite idappaAA;auto.
    destruct H.

    split.
    split;[intro theOrs; destruct theOrs;[idtac|destruct H];try rewrite<-H |intro theExists;destruct theExists;simpl in H;destruct (idApp_eq a a1);[left;auto|(destruct (idApp_eq a a2);[right;left;auto|inversion H])]].
    exists c;simpl;rewrite H;rewrite idappaAA;auto.
    exists c;simpl;rewrite idappa21;rewrite H;rewrite idappaAA;auto.
    destruct H.

    split.
    split;[intro theOrs; destruct theOrs;[idtac|destruct H];try rewrite<-H |intro theExists;destruct theExists;simpl in H;destruct (idApp_eq a a1);[left;auto|(destruct (idApp_eq a a2);[right;left;auto|inversion H])]].
    exists nil;simpl;rewrite H;rewrite idappaAA;auto.
    exists (witnessPerm::nil);simpl;rewrite idappa21;rewrite H;rewrite idappaAA;auto.
    destruct H.

    split.
    split;[intro theOrs; destruct theOrs;[idtac|destruct H];try rewrite<-H |intro theExists;destruct theExists;simpl in H;destruct (idApp_eq a a1);[left;auto|(destruct (idApp_eq a a2);[left;right;left;auto|inversion H])]].

    exists nil;simpl.
    case_eq (idApp_eq a a1);intros;auto.
    destruct H.
    symmetry in H.
    contradiction.
    destruct H.
    rewrite H.
    destruct (idApp_eq a a);auto.
    contradiction.
    destruct H.
    destruct H.
    destruct H.

    split;[intro theOrs; destruct theOrs;[idtac|destruct H];try rewrite<-H |intro theExists;destruct theExists;simpl in H;destruct (idApp_eq a a1);[left;auto|(destruct (idApp_eq a a2);[left;right;left;auto|inversion H])]].
    exists (witnessPermGrp :: nil);simpl.
    case_eq (idApp_eq a a1);intros;auto.
    destruct H.
    symmetry in H.
    contradiction.
    destruct H.
    rewrite H.
    destruct (idApp_eq a a);auto.
    contradiction.
    destruct H.
    destruct H.
    destruct H.

    split.
    unfold notDupApp.
    intros.
    simpl.
    unfold not;intros.
    destruct H0.
    destruct H0.
    auto.

    split.
    unfold notDupSysApp.
    simpl.
    intros.
    destruct H.
    inversion H.

    split.
    unfold notDupPerm.
    intros.
    assert (l<>nil).
    apply inNotNilExists;exists p;auto.
    assert (l'<>nil).
    apply inNotNilExists;exists p';auto.
    assert (a=a2 /\ l = (witnessPerm::nil)).
    apply (defPermsOnWitnessSys l);auto.
    assert (a'=a2 /\ l' = (witnessPerm::nil)).
    apply (defPermsOnWitnessSys l');auto.
    destruct H6,H7.
    rewrite H6,H7 in *.
    rewrite H8,H9 in *.
    inversion H1.
    inversion H2.
    rewrite H10,H11 in *.
    split;auto.
    inversion H11.
    inversion H10.

    split.
    unfold allMapsCorrect.
    repeat (split;repeat apply addPreservesCorrectness;auto).

    split.
    unfold grantedPermsExist.
    simpl.
    intros.
    rewrite idappa12 in H;simpl in H.
    destruct (idApp_eq a a1);simpl in H.
    inversion H.
    rewrite <-H2 in H0.
    inversion H0.
    destruct (idApp_eq a a2).
    inversion H.
    rewrite <-H2 in H0.
    inversion H0.
    inversion H.


    unfold noDupSentIntents;simpl;intros.
    destruct H.
Qed.

Lemma ExecAutoGrantWithoutIndividualPerms :
    exists (s: System) (p: Perm) (g: idGrp) (a: idApp),
    validstate s /\
    ~ (exists (p': Perm) (permsA: list Perm), 
        map_apply idApp_eq (perms (state s)) a = Value idApp permsA /\
        In p' permsA /\ maybeGrp p' = Some g) /\
    pl p = dangerous /\
    maybeGrp p = Some g /\
    pre_grantAuto p a s.
Proof.
    exists witnessSys, witnessPerm, witnessPermGrp, a1.
    assert (idappa12:=idAppa1a2Right).
    destruct idappa12 as [proof12 idappa12].
    assert (idappa21:=idAppa2a1Right).
    destruct idappa21 as [proof21 idappa21].
    assert (idappa11:=idAppAALeft a1).
    destruct idappa11 as [proof11 idappa11].
    assert (idappa22:=idAppAALeft a2).
    destruct idappa22 as [proof22 idappa22].
    split.
    exact WitnessStateIsValid.
    split.

    unfold not; intros.
    destruct H as [p' [permsA [H1 [H2 H3]]]].
    simpl in H1.
    rewrite idappa12 in H1; simpl in H1.
    rewrite idappa11 in H1; simpl in H1.
    inversion H1.
    rewrite <- H0 in H2.
    destruct H2.

    split; auto.
    split; auto.

    unfold pre_grantAuto.
    split.
  - exists a1Mfst.
    split.
    unfold RuntimePermissions.isManifestOfApp.
    left. simpl.
    rewrite idappa12; simpl.
    rewrite idappa11; simpl.
    auto.
    simpl. auto.
  - split. right.
    unfold usrDefPerm. left.
    exists a2. simpl.
    rewrite idappa12; simpl.
    rewrite idappa21; simpl.
    rewrite idappa22; simpl.
    exists (witnessPerm::nil). split; auto.
    simpl. auto.
    unfold not; intros. split.
    intros.
    destruct H as [lPerm [H1 H2]].
    simpl in H1.
    rewrite idappa12 in H1; simpl in H1.
    rewrite idappa11 in H1; simpl in H1.
    inversion H1. rewrite <- H0 in H2.
    inversion H2.
    split; auto.
    exists witnessPermGrp, (witnessPermGrp::nil).
    split; auto.
    simpl.
    rewrite idappa12; simpl.
    rewrite idappa11; simpl.
    auto.
Qed.

