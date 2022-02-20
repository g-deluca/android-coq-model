(* En este archivo se demuestra la corrección de la acción sendOrderedBroadcast *)
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

Section SendOrderedBroadcast.

Lemma sendOrderedBroadcastIsSound : forall (s:System) (i:Intent) (ic:iCmp) (mp:option Perm) (sValid: validstate s),
        exec s (sendOrderedBroadcast i ic mp) (system (step s (sendOrderedBroadcast i ic mp))) (response (step s (sendOrderedBroadcast i ic mp))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    simpl.
    unfold pre_sendOrderedBroadcast.
    unfold post_sendOrderedBroadcast.
    apply sendBroadcastIsSound.
    auto.
Qed.
End SendOrderedBroadcast.
