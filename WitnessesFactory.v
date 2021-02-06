(* Here we define witnesses components used in some properties proofs. *)
Require Import Estado.
Require Import DefBasicas.
Require Import Maps.

Parameter a1 a2:idApp.
Axiom asdiff :a1<>a2.

Theorem idAppa1a2Right : exists e, idApp_eq a1 a2 = right e.
Proof.
    destruct (idApp_eq a1 a2).
    destruct asdiff;auto.
    exists n.
    auto.
Qed.

Theorem idAppa2a1Right : exists e, idApp_eq a2 a1 = right e.
Proof.
    destruct (idApp_eq a2 a1).
    destruct asdiff;auto.
    exists n.
    auto.
Qed.

Theorem idAppAALeft : forall a, exists e, idApp_eq a a = left e.
Proof.
    intros.
    destruct (idApp_eq a a).
    exists e;auto.
    destruct n;auto.
Qed.

Parameter c:Cert.

Definition emptyPermGroups := map_empty idApp (list idGrp).

Definition emptyPerms := map_empty idApp (list Perm).

Definition emptyRunning := map_empty iCmp Cmp.

Definition emptyDelPPerms:= map_empty (idApp * CProvider * uri) PType.

Definition emptyDelTPerms:= map_empty (iCmp * CProvider * uri) PType.

Definition emptyResCont:= map_empty (idApp * res) Val.

Definition addAppValue (V:Set) (a:idApp) (v:V) (mp:mapping idApp V) :=
    map_add idApp_eq mp a v.

Parameter witnessPermId : idPerm.
Parameter witnessPermGrp : idGrp.

Definition emptyManifests:= map_empty idApp Manifest.
Definition emptyCerts:= map_empty idApp Cert.
Definition emptyDefPerms:= map_empty idApp (list Perm).

Definition simpleManifest (hisCmps : list Cmp) (permsUsed : list Perm) (permsDeclared : list Perm) :=
    mf hisCmps (Some 23) (Some 23) permsUsed permsDeclared None.

