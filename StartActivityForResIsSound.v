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
Require Import StartActivityIsSound.

Section StartActivityForResult.


Lemma startActivityForResultIsSound : forall (s:System) (i:Intent) (ic:iCmp) (sValid: validstate s) (n:nat),
        exec s (startActivityForResult i n ic) (system (step s (startActivityForResult i n ic))) (response (step s (startActivityForResult i n ic))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    simpl.
    unfold pre_startActivityForResult in *.
    apply startActivityIsSound.
    auto.
Qed.
End StartActivityForResult.
