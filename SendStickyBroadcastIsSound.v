(* En este archivo se demuestra la corrección de la acción sendStickyBroadcast *)
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
Require Import SendBroadcastIsSound.

Section SendStickyBroadcast.

Lemma sendStickyBroadcastIsSound : forall (s:System) (i:Intent) (ic:iCmp) (sValid: validstate s),
        exec s (sendStickyBroadcast i ic) (system (step s (sendStickyBroadcast i ic))) (response (step s (sendStickyBroadcast i ic ))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    simpl.
    unfold pre_sendStickyBroadcast.
    unfold post_sendStickyBroadcast.
    apply sendBroadcastIsSound.
    auto.
Qed.
End SendStickyBroadcast.
