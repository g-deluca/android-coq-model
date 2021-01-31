(* In this file we prove that some basic types are comparable *)
Require Import DefBasicas.
Require Import Maps.

Theorem permLevel_eq : forall (id1 id2 : permLevel), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
Qed.

Theorem option_eq : forall (A:Set) (Aeq: forall (id1 id2:A), {id1 = id2} + {id1 <> id2}) (id1 id2:option A), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
Qed.


Theorem Perm_eq : forall (id1 id2 : Perm), {id1 = id2} + {id1 <> id2}. 
Proof.
    decide equality.
    apply permLevel_eq.
    apply (option_eq idGrp idGrp_eq).
    apply idPerm_eq.
Qed.

Theorem dataType_eq : forall (id1 id2 : dataType), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
Qed.

Theorem Data_eq : forall (id1 id2 : Data), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
    apply dataType_eq.
    apply (option_eq mimeType mimeType_eq).
    apply (option_eq uri uri_eq).
Qed.

Theorem list_eq : forall (A:Set) (Aeq: forall (id1 id2:A), {id1 = id2} + {id1 <> id2}) (id1 id2:list A), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
Qed.

Theorem intentAction_eq : forall (id1 id2 : intentAction), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
Qed.

Theorem bool_eq :  forall (id1 id2 : bool), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
Qed.

Theorem item_eq : forall (A B:Set) (Aeq: forall (id1 id2:A), {id1 = id2} + {id1 <> id2}) (Beq: forall (id1 id2:B), {id1 = id2} + {id1 <> id2}) (id1 id2:item A B), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
Qed.

Theorem map_eq : forall (A B:Set) (Aeq: forall (id1 id2:A), {id1 = id2} + {id1 <> id2}) (Beq: forall (id1 id2:B), {id1 = id2} + {id1 <> id2}) (id1 id2:mapping A B), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
    apply item_eq;auto.
Qed.

Theorem CProvider_eq : forall (id1 id2 : CProvider), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
    apply (list_eq uri uri_eq).
    apply bool_eq.
    apply (option_eq Perm Perm_eq).
    apply (option_eq Perm Perm_eq).
    apply (option_eq Perm Perm_eq).
    apply (option_eq bool bool_eq).
    apply (map_eq uri res uri_eq res_eq).
    apply idCmp_eq.
Qed.

Theorem intentType_eq :  forall (id1 id2 : intentType), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
Qed.

Theorem Intent_eq : forall (id1 id2 : Intent), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
    apply (option_eq Perm Perm_eq).
    apply (option_eq Flag Flag_eq).
    apply (option_eq Extra Extra_eq).
    apply (list_eq Category Category_eq).
    apply Data_eq.
    apply (option_eq intentAction intentAction_eq).
    apply intentType_eq.
    apply (option_eq idCmp idCmp_eq).
    apply idInt_eq.
Qed.


Theorem intentFilter_eq : forall (id1 id2 : intentFilter), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
    apply (list_eq Category Category_eq).
    apply (list_eq Data Data_eq).
    apply (list_eq intentAction intentAction_eq).
Qed.

Theorem Activity_eq : forall (id1 id2 : Activity), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
    apply (list_eq intentFilter intentFilter_eq).
    apply (option_eq Perm Perm_eq).
    apply (option_eq bool bool_eq).
    apply idCmp_eq.
Qed.

Theorem Service_eq : forall (id1 id2 : Service), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
    apply (list_eq intentFilter intentFilter_eq).
    apply (option_eq Perm Perm_eq).
    apply (option_eq bool bool_eq).
    apply idCmp_eq.
Qed.

Theorem nat_eq : forall (id1 id2 : nat), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
Qed.

Theorem BroadReceiver_eq : forall (id1 id2 : BroadReceiver), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
    apply (list_eq intentFilter intentFilter_eq).
    apply (option_eq Perm Perm_eq).
    apply (option_eq bool bool_eq).
    apply idCmp_eq.
Qed.

Theorem Cmp_eq : forall (id1 id2 : Cmp), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
    apply Activity_eq.
    apply Service_eq.
    apply CProvider_eq.
    apply BroadReceiver_eq.
Qed.

Theorem sentIntentsElems_eq : forall (id1 id2 : iCmp*Intent), {id1 = id2} + {id1 <> id2}.
Proof. 
    decide equality.
    apply Intent_eq.
    apply iCmp_eq.
Qed.

Theorem sentintentseq : forall (id1 id2 : (iCmp*Intent)), {id1 = id2} + {id1 <> id2}.
Proof.
    decide equality.
    apply Intent_eq.
    apply iCmp_eq.
Qed.

Section DomEqs.

Theorem delppermsdomeq : forall (id1 id2 : (idApp*CProvider*uri)), {id1 = id2} + {id1 <> id2}. 
Proof.
    decide equality.
    apply uri_eq.
    decide equality.
    apply CProvider_eq.
    apply idApp_eq.
Qed.

Theorem deltpermsdomeq : forall (id1 id2 : (iCmp*CProvider*uri)), {id1 = id2} + {id1 <> id2}. 
Proof.
    decide equality.
    apply uri_eq.
    decide equality.
    apply CProvider_eq.
    apply iCmp_eq.
Qed.

Theorem rescontdomeq : forall (id1 id2 : (idApp*res)), {id1 = id2} + {id1 <> id2}. 
Proof.
    decide equality.
    apply res_eq.
    apply idApp_eq.
Qed.
End DomEqs.
