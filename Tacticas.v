Require Import Classical.
Require Import Coq.Bool.Bool.
Require Import Estado.
Ltac destruct_conj h:=
  match goal with
  | [H: _/\_ |- _] => match H with
                        | h=>let ph0 := fresh "H" in
                             let ph1 := fresh "H" in
                               destruct h as [ph0 ph1]; try destruct_conj ph1 end end.


Ltac destruct_not_conj h:=
  match goal with
  | [H: ~(_/\_) |- _] => match H with
                        | h=>let ph0 := fresh "H" in
                             let ph1 := fresh "H" in
                               apply not_and_or in h;destruct h; try destruct_not_conj h end end.

Ltac dontcare x :=
    let ph0:=fresh "H" in
        elim (classic(x=true));intro ph0;try rewrite not_true_iff_false in ph0;rewrite ph0;auto.


Ltac destructVS h :=
match goal with
  | [H:_ |- _] => match H with
                        | h=>
                             let ph0 := fresh "H" in
                               destruct h as [allCmpDiffVS ph0];
                               destruct ph0 as [notRepCompsVS ph0];
                               destruct ph0 as [notCPRunningVS ph0];
                               destruct ph0 as [delTmpRunVS ph0];
                               destruct ph0 as [cmpRunAppInsVS ph0];
                               destruct ph0 as [resContAppInstVS ph0];
                               destruct ph0 as [statesConsistencyVS ph0];
                               destruct ph0 as [notDupAppVS ph0];
                               destruct ph0 as [notDupSysAppVS ph0];
                               destruct ph0 as [notDupPermVS ph0];
                               destruct ph0 as [allMapsCorrectVS ph0];
                               destruct ph0 as [grantedPermsExistVS sentIntentsCorrectVS]
  end end.

Ltac destructSC h a :=
match goal with
  | [H:_ |- _] => match H with
                        | h=>
                             let ph0 := fresh "H" in
                             destruct (h a) as [mfstSC ph0];
                             destruct ph0 as [certSC ph0];
                             destruct ph0 as [defPermsSC ph0];
                             destruct ph0 as [permsSC grantedPermGroupsSC]
  end end.


Ltac mapcorrect h :=
match goal with
  | [H:_ |- _] => match H with
                        | h=>
                             let ph0 := fresh "H" in
                               destruct h as [allCmpDiffVS ph0];
                               destruct ph0 as [notRepCompsVS ph0];
                               destruct ph0 as [notCPRunningVS ph0];
                               destruct ph0 as [delTmpRunVS ph0];
                               destruct ph0 as [cmpRunAppInsVS ph0];
                               destruct ph0 as [resContAppInstVS ph0];
                               destruct ph0 as [statesConsistencyVS ph0];
                               destruct ph0 as [notDupAppVS ph0];
                               destruct ph0 as [notDupSysAppVS ph0];
                               destruct ph0 as [notDupPermVS ph0];
                               destruct ph0 as [allMapsCorrectVS grantedPermsExistVS];
                               unfold allMapsCorrect in allMapsCorrectVS;
                               destruct_conj allMapsCorrectVS;
                               auto
  end end.

Ltac invertBool h :=
match goal with
  | [H:_ |- _] => match H with
                        | h=>
                        first [ rewrite<- not_true_iff_false in h| rewrite<- not_false_iff_true in h]
                    end end.
