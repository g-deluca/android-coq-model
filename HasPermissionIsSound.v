Require Export Exec.
Require Export Implementacion.
Require Export AuxFunsCorrect.
Require Import Classical.
Require Import Estado.
Require Import DefBasicas.
Require Import Semantica.
Require Import Operaciones.
Require Import ErrorManagement.
Require Import Maps.
Require Import Tacticas.

Section HasPermission.

Lemma hasPermissionIsSound : forall (s:System) (p:Perm) (c:Cmp),
        validstate s -> exec s (hasPermission p c) (system (step s (hasPermission p c))) (response (step s (hasPermission p c))).
Proof.
    intros.
    unfold exec.
    split.
    auto.
    unfold step;simpl.
    left.
    unfold pre_hasPermission.
    unfold post_hasPermission.
    repeat (split;auto).
    
Qed.
End HasPermission.
