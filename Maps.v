(* En este archivo se formalizan las funciones parciales. El código del
 * mismo fue tomado del trabajo "Formally verifying isolation and availability in an
 * idealized model of virtualization" de Gilles Barthe et al.                        *)

Require Import List.
Require Import Classical.

Set Implicit Arguments.


Section Exc_Type.

(* The type representing the codomain of the partial function *)
Inductive exc (V E : Set) : Set :=
  | Value : V -> exc V E
  | Error : E -> exc V E.

Variable V1 V2 V3 E1 E2 : Set.

Definition is_Value (e : exc V1 E1) : Prop :=
  match e with
  | Value _ => True
  | Error _ => False
  end.

Definition is_ValueBool (e : exc V1 E1) : bool:=
  match e with
  | Value _ => true
  | Error _ => false
  end.
End Exc_Type.

(* This module describes a naive implementation of a dictionary (maps) using
   association lists. *)
Notation "'If' c1 'then' c2 'else' c3" :=
  match c1 with
  | left _ => c2
  | right _ => c3
  end (at level 200).

Section Mapping_Definition.

(* The type of index for accessing the map *)
Variable index : Set.
Variable index_eq : forall x y : index, {x = y} + {x <> y}.

(* The type of information associated to each index *)
Variable info : Set.

Record item : Set := 
 Item
    (* the index *)
    {item_index : index;
    (* the data associated to the index *)
    item_info : info 
   }.

(* Mappings as lists *)
Definition mapping : Set := list item.

(* Empty map  *)
Definition map_empty : mapping := nil.


(* Map add *)
(* Adding of a new entry in the map. 
   If the key already exists in the map, the info is redefined. *)
Function map_add (mp : mapping) (idx : index) 
  (inf : info) : mapping :=
  let newit := (Item idx inf) in 
  match mp with
  | nil =>  newit :: map_empty
  | it :: mp1 =>
      If index_eq (item_index it) idx
      then newit :: mp1 
      else it :: map_add mp1 idx inf
  end.

(* Map apply *)
Function map_apply (mp : mapping) 
  (idx : index) : exc info index :=
  match mp with
  | nil => Error info idx
  | it :: mp1 =>
      If index_eq idx (item_index it) 
      then Value index (item_info it)
      else map_apply mp1 idx
  end.

(* Map drop *)
Function map_drop (mp : mapping) 
  (idx : index) : mapping :=
  match mp with
  | nil => nil 
  | it :: mp1 =>
      If index_eq idx (item_index it) 
      then map_drop mp1 idx
      else it :: map_drop mp1 idx
  end.
 
(* Several map observers *)

Definition map_valid_index (mp : mapping) (idx : index) : Prop :=
  exists it : _, map_apply mp idx = Value index it.

Fixpoint map_valid_index_fix (mp:mapping) (idx:index) : bool :=
  match mp with
    | nil => false
    | it::mp' =>
      If (index_eq (item_index it) idx) then
        true
      else
        map_valid_index_fix mp' idx
  end.

(* Map size *)
Definition map_size (mp : mapping) : nat := length mp.

Definition map_getKeys (mp : mapping) : list index :=
    map (fun item => item_index item) mp.

Fixpoint map_correct (mp:mapping) : Prop :=
    match mp with
    | nil => True
    | (a::rest) => ~(In (item_index a) (map_getKeys rest)) /\ map_correct rest
    end.

End Mapping_Definition.

Section Mapping_Properties.

Lemma addAndApply : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i:index) (v:values) (mp:mapping index values), Value index v = map_apply indexeq (map_add indexeq mp i v) i.
Proof.
    intros.
    induction mp.
    simpl.
    destruct (indexeq i i).
    auto.
    destruct n.
    auto.
    case(indexeq i (item_index a));intros.
    simpl.
    rewrite<- e.
    destruct (indexeq i i).
    simpl.
    destruct (indexeq i i).
    auto.
    destruct n;auto.
    destruct n;auto.
    simpl.
    destruct (indexeq (item_index a) i).
    simpl.
    destruct (indexeq i i).
    auto.
    destruct n0;auto.
    simpl.
    destruct (indexeq i (item_index a)).
    destruct n0;auto.
    rewrite IHmp.
    auto.
Qed.

Lemma overrideNotEq : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i i':index) (v:values) (mp:mapping index values), i<>i' -> map_apply indexeq (map_add indexeq mp i v) i' = map_apply indexeq mp i'.
Proof.
    intros.
    induction mp.
    simpl.
    destruct indexeq.
    rewrite e in H.
    unfold not in H.
    destruct H.
    auto.
    auto.
    simpl.
    case(indexeq i' (item_index a));intros.
    simpl.
    destruct (indexeq i' (item_index a)).
    rewrite<- e.
    destruct (indexeq i' i).
    unfold not in H.
    destruct H.
    auto.
    simpl.
    rewrite <-e.
    destruct (indexeq i' i').
    auto.
    unfold not in n0.
    destruct n0.
    auto.
    unfold not in n.
    destruct n.
    auto.
    destruct (indexeq (item_index a) i).
    simpl.
    destruct (indexeq i' i).
    rewrite<- IHmp.
    rewrite e0.
    apply (addAndApply).
    auto.
    simpl.
    destruct (indexeq i' (item_index a)).
    destruct n;auto.
    auto.
Qed.

Lemma dropNotExists : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i:index) (mp:mapping index values), ~(exists (it:item index values), In it (map_drop indexeq mp i) /\ item_index it=i).
Proof.
    intros.
    induction mp.
    unfold not;intros.
    destruct H.
    destruct H.
    simpl in H.
    auto.
    
    
    unfold not;intros.
    destruct H.
    destruct H.
    apply IHmp.
    exists x.
    split.
    assert (item_index a<>i).
    unfold not;intros.
    unfold map_drop in H;simpl in H.
    destruct indexeq in H.
    apply IHmp.
    exists x.
    split; auto.
    symmetry in H1.
    contradiction.
    
    unfold map_drop in H;simpl in H.
    destruct indexeq in H.
    auto.
    inversion H.
    rewrite H2 in H1.
    contradiction.
    auto.
    auto.
Qed.


Lemma isValueExists : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i:index) (mp:mapping index values), is_Value (map_apply indexeq mp i) -> (exists (it:item index values), In it mp /\ item_index it=i).
Proof.
    intros.
    case_eq (map_apply indexeq mp i);intros.
    exists (Item i v).
    simpl;split;auto.
    induction mp.
    simpl in H0.
    discriminate H0.
    elim (classic (item_index a=i));intros.
    
    
    left.
    simpl in H0.
    destruct indexeq in H0.
    assert (item_info a=v).
    Focus 2.
    case_eq a;intros.
    f_equal.
    assert (item_index a=item_index0).
    rewrite H3; auto.
    rewrite H4 in H1.
    auto.
    assert (item_info a=item_info0).
    rewrite H3; auto.
    rewrite H4 in H2.
    auto.
    injection H0;auto.
    symmetry in H1.
    contradiction.
    
    right.
    simpl in H0.
    destruct indexeq in H0.
    symmetry in e.
    contradiction.
    apply IHmp.
    rewrite H0.
    simpl;auto.
    auto.
    
    
    rewrite H0 in H.
    simpl in H.
    destruct H.
Qed.

Lemma valueDropNotValue : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i:index) (mp:mapping index values), ~(is_Value (map_apply indexeq (map_drop indexeq mp i) i)).
Proof.
    intros.
    unfold not;intros.
    assert (exists (it:item index values), In it (map_drop indexeq mp i) /\ item_index it=i).
    apply (isValueExists indexeq);auto.
    absurd (exists it : item index values, In it (map_drop indexeq mp i) /\ item_index it = i).
    apply dropNotExists.
    auto.
Qed.

Lemma valueDropDiffImpliesValue : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i i':index) (v:values) (mp:mapping index values), map_apply indexeq (map_drop indexeq mp i) i' = Value index v -> i <> i' -> map_apply indexeq mp i' = Value index v.
Proof.
    intros.
    induction mp.
    simpl in H.
    discriminate H.
    simpl in H;destruct indexeq in H.
    rewrite e in H0.
    simpl.
    destruct (indexeq i' (item_index a)).
    symmetry in e0.
    contradiction.
    apply IHmp;auto.
    simpl in H;destruct indexeq in H.
    simpl;destruct (indexeq i (item_index a)).
    contradiction.
    destruct (indexeq i' (item_index a)).
    auto.
    contradiction.
    simpl.
    destruct (indexeq i' (item_index a)).
    contradiction.
    auto.
Qed.

Lemma valueDropValue : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i i':index) (v:values) (mp:mapping index values), map_apply indexeq (map_drop indexeq mp i) i' = Value index v <-> map_apply indexeq mp i' = Value index v /\ i<>i'.
Proof.
    split;intros.
    assert (i<>i').
    unfold not;intros.
    absurd (is_Value (map_apply indexeq (map_drop indexeq mp i) i')).
    rewrite H0 in *.
    apply (valueDropNotValue).
    rewrite H.
    simpl.
    auto.
    split.
    apply (valueDropDiffImpliesValue indexeq mp H).
    auto.
    auto.
    
    destruct H.
    
    induction mp.
    simpl in H.
    discriminate H.
    simpl in H;destruct indexeq in H.
    rewrite e in H0.
    simpl.
    destruct (indexeq i' (item_index a)).
    destruct (indexeq i (item_index a)).
    symmetry in e0.
    contradiction.
    simpl.
    destruct (indexeq i' (item_index a)).
    auto.
    contradiction.
    contradiction.
    simpl.
    destruct (indexeq i (item_index a)).
    apply IHmp;auto.
    simpl.
    destruct (indexeq i' (item_index a)).
    contradiction.
    auto.
    
    
    
Qed.

Lemma valueIffExists : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i:index) (v:values) (mp:mapping index values) (mpCorrect : map_correct mp), map_apply indexeq mp i = Value index v <-> In (Item i v) mp.
Proof.
    split;intros.
    clear mpCorrect.
    induction mp.
    unfold map_apply in H.
    inversion H.
    simpl in H.
    destruct indexeq in H.
    inversion H.
    rewrite e.
    remember ({| item_index := item_index a; item_info := item_info a |}) as theitem.
    assert (theitem=a).
    case_eq a;intros.
    rewrite H0 in Heqtheitem.
    simpl in Heqtheitem.
    auto.
    rewrite H0.
    apply in_eq.
    
    apply in_cons.
    apply IHmp; auto.
    
    
    induction mp.
    inversion H.
    remember {| item_index := i; item_info := v |} as theItem.
    inversion H.
    simpl.
    rewrite H0.
    rewrite HeqtheItem.
    simpl.
    destruct (indexeq i i).
    auto.
    absurd (i=i);auto.
    assert (item_index a <>i).
    unfold map_correct in mpCorrect.
    unfold not;intros.
    apply mpCorrect.
    unfold map_getKeys.
    rewrite in_map_iff.
    exists theItem.
    split;auto.
    rewrite HeqtheItem.
    simpl.
    auto.
    simpl.
    destruct (indexeq i (item_index a)).
    symmetry in e.
    contradiction.
    apply IHmp.
    unfold map_correct in mpCorrect.
    destruct mpCorrect.
    auto.
    auto.
Qed.

Lemma dropSthElse : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i i':index) (mp:mapping index values), i<>i' -> map_apply indexeq mp i = map_apply indexeq (map_drop indexeq mp i') i.
Proof.
    intros.
    induction mp.
    simpl.
    auto.
    simpl.
    destruct (indexeq i (item_index a)).
    destruct (indexeq i' (item_index a)).
    rewrite <-e in e0.
    symmetry in e0;contradiction.
    simpl.
    destruct (indexeq i (item_index a)).
    auto.
    contradiction.
    destruct (indexeq i' (item_index a)).
    auto.
    simpl.
    destruct (indexeq i (item_index a)).
    contradiction.
    auto.
Qed.

Lemma valueIffInGetKeys : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i:index) (mp:mapping index values) (mpCorrect:map_correct mp), is_Value (map_apply indexeq mp i) <-> In i (map_getKeys mp).
Proof.
    unfold map_getKeys.
    split;intros.
    rewrite in_map_iff.
    case_eq (map_apply indexeq mp i);intros.
    exists{| item_index := i; item_info := v |}.
    rewrite <-valueIffExists.
    split;auto.
    exact H0.
    auto.
    rewrite H0 in H.
    inversion H.
    
    rewrite in_map_iff in H.
    destruct H.
    destruct H.
    case_eq x;intros.
    rewrite H1 in H0.
    assert (map_apply indexeq mp i = Value index item_info0).
    apply valueIffExists; auto.
    rewrite H1 in H.
    simpl in H.
    rewrite <-H.
    auto.
    rewrite H2.
    unfold is_Value.
    auto.
Qed.

Lemma addPreservesCorrectness : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i:index) (v:values) (mp:mapping index values) (mpCorrect:map_correct mp), map_correct (map_add indexeq mp i v).
Proof.
    intros.
    functional induction (map_add indexeq mp i v).
    unfold map_empty.
    unfold map_correct.
    split;auto.
    unfold map_correct in mpCorrect.
    destruct mpCorrect.
    unfold map_correct.
    simpl.
    split;auto.
    assert (map_correct mp1).
    unfold map_correct in mpCorrect.
    destruct mpCorrect.
    auto.
    unfold map_correct.
    specialize (IHm H).
    split.
    rewrite <-(valueIffInGetKeys indexeq);auto.
    unfold not;intros.
    rewrite overrideNotEq in H0.
    unfold map_correct in mpCorrect.
    destruct mpCorrect.
    rewrite (valueIffInGetKeys indexeq) in H0;auto.
    auto.
    unfold map_correct in IHm.
    auto.
Qed.


Lemma dropPreservesCorrectness : forall (index values:Set) (indexeq: forall x y : index, {x = y} + {x <> y}) (i:index) (mp:mapping index values) (mpCorrect:map_correct mp), map_correct (map_drop indexeq mp i).
Proof.
    intros.
    functional induction (map_drop indexeq mp i).
    auto.
    assert (map_correct mp1).
    unfold map_correct in mpCorrect.
    destruct mpCorrect.
    auto.
    specialize (IHm H).
    auto.
    unfold map_correct.
    split.
    
    
    assert (map_correct mp1).
    unfold map_correct in mpCorrect.
    destruct mpCorrect.
    auto.
    specialize (IHm H).
    rewrite <-(valueIffInGetKeys indexeq);auto.
    rewrite<-dropSthElse;auto.
    rewrite (valueIffInGetKeys indexeq);auto.
    unfold map_correct in mpCorrect.
    destruct mpCorrect.
    auto.
    assert (map_correct mp1).
    unfold map_correct in mpCorrect.
    destruct mpCorrect.
    auto.
    specialize (IHm H).
    auto.
Qed.

End Mapping_Properties.
