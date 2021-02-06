(* In this file we show some auxiliary properties about lists *)
Require Import Implementacion.
Require Import DefBasicas.
Require Import Estado.
Require Import Semantica.
Require Import Maps.
Require Import MyList.
Require Import Coq.Lists.List.
Require Import Classical.
Require Import Tacticas.
Require Import RuntimePermissions.

Section ListAuxFuns.
    Context `{A:Set, B:Set}.

Lemma in_concat : forall (l:list (list A))(a:A), In a (concat l) <-> exists x, In x l /\ In a x.
Proof.
    intros.
    assert (l = map id l).
    induction l.
    auto.
    simpl.
    unfold id in *.
    rewrite<- IHl.
    auto.
    rewrite H.
    rewrite<- flat_map_concat_map.
    rewrite in_flat_map.
    rewrite<- H.
    unfold id.
    split;auto.
Qed.

Lemma inGetValues: forall (l:list (exc B A)) (x:B), In x (getValues A B l) -> exists y:exc B A, In y l /\ y = Value A x.
Proof.
    intros.
    induction l.
    compute in H.
    destruct H.
    destruct a;intros.
    simpl in H.
    destruct H.
    exists (Value A b).
    split.
    apply in_eq.
    rewrite H.
    auto.
    specialize (IHl H).
    destruct IHl.
    exists x0.
    destruct H0.
    split.
    apply in_cons.
    auto.
    auto.
    simpl in H.
    specialize (IHl H).
    destruct IHl.
    exists x0.
    destruct H0.
    split.
    apply in_cons.
    auto.
    auto.
Qed.

Lemma inGetValuesBack : forall (l:list (exc B A)) (x:B), (exists y:exc B A, In y l /\ y = Value A x) -> In x (getValues A B l).
Proof.
    intros.
    destruct H.
    destruct H.
    induction l.
    destruct H.
    case_eq a;intros.
    elim (classic (b=x));intros.
    unfold getValues;simpl.
    left.
    auto.
    right.
    inversion H.
    rewrite H3 in H1.
    rewrite H0 in H1.
    inversion H1.
    symmetry in H5.
    contradiction.
    apply IHl.
    auto.
    inversion H.
    rewrite H2 in H1.
    rewrite H0 in H1.
    inversion H1.
    unfold getValues;simpl.
    apply IHl.
    auto.
Qed.

Lemma ifExistsHeadIn : forall (l:list A) (dflt:A), (exists x, In x l) -> In (hd dflt l) l.
Proof.
    intros.
    induction l.
    destruct H.
    inversion H.
    simpl.
    left;auto.
Qed.

Lemma ifExistsFilter : forall (l:list A) (f:A->bool) (dflt:A), (exists x, In x (filter f l)) -> In (hd dflt (filter f l)) l /\ f (hd dflt (filter f l)) =true.
Proof.
    intros.
    destruct H.
    rewrite filter_In in H.
    destruct H.
    induction l.
    destruct H.
    elim (classic (f a=true));intros.
    assert (hd dflt (filter f (a::l))=a).
    simpl.
    rewrite H1.
    simpl.
    auto.
    rewrite H2.
    split;auto.
    apply in_eq.
    destruct H.
    rewrite H in H1.
    contradiction.
    specialize (IHl H).
    assert (hd dflt (filter f (a::l)) = hd dflt (filter f l)).
    rewrite not_true_iff_false in H1.
    simpl.
    rewrite H1.
    auto.
    rewrite H2.
    destruct IHl.
    split.
    apply in_cons.
    auto.
    auto.
    
Qed.

Lemma ifExistsFilterHdError : forall (l:list A) (f:A->bool), (exists x, In x (filter f l)) -> exists x,hd_error (filter f l) = Some x /\ f x=true /\ In x l.
Proof.
    intros.
    destruct H.
    induction l.
    simpl in H.
    destruct H.
    elim (classic (f a=true));intros.
    simpl.
    rewrite H0.
    exists a.
    simpl.
    auto.
    rewrite not_true_iff_false in H0.
    simpl in *.
    rewrite H0 in *.
    specialize (IHl H).
    destruct IHl.
    exists x0.
    destruct_conj H1.
    split;auto.
Qed.

Lemma ifNotNilHdMap : forall (l:list A) (f:A->B) (dfltA:A) (dfltB:B), l<>nil -> hd dfltB (map f l) = f (hd dfltA l).
Proof.
    intros.
    case_eq l;intros.
    contradiction.
    simpl.
    auto.
Qed.

Lemma inNotNilExists : forall (l:list A) , l<>nil <-> exists a:A, In a l.
Proof.
    split;intros.
    case_eq l;intros.
    contradiction.
    exists a.
    apply in_eq.
    destruct H.
    unfold not;intros.
    rewrite H0 in H.
    inversion H.
Qed.


Lemma removeSthElse : forall (A:Set) (l:list A) (a a':A) (aeq : forall x y:A, {x=y}+{x<>y}), a<>a' /\ In a l <-> In a (remove aeq a' l).
Proof.
    split;intros.
    destruct H.
    induction l.
    destruct H0.
    elim (classic (a'=a0));intros.
    destruct H0.
    rewrite<- H0 in H.
    symmetry in H1.
    contradiction.
    simpl.
    destruct (aeq a' a0).
    apply IHl;auto.
    contradiction.
    simpl.
    destruct (aeq a' a0).
    contradiction.
    destruct H0.
    rewrite H0.
    apply in_eq.
    apply in_cons.
    apply IHl;auto.
    
    induction l.
    simpl in H.
    destruct H.
    
    simpl in H.
    destruct aeq in H.
    specialize (IHl H).
    destruct IHl.
    split;auto.
    apply in_cons;auto.
    destruct H.
    rewrite H in *.
    split;auto.
    apply in_eq.
    specialize (IHl H).
    destruct IHl.
    split;auto.
    apply in_cons.
    auto.
    
Qed.

Lemma notInRemove : forall (A:Set) (l:list A) (a a':A) (aeq : forall x y:A, {x=y}+{x<>y}), In a l -> ~In a (remove aeq a' l) -> a=a'.
Proof.
    intros.
    induction l.
    destruct H.
    elim (classic (a0=a));intro.
    simpl in H0.
    destruct aeq in H0.
    rewrite e.
    auto.
    rewrite H1 in H0.
    absurd (In a (a :: remove aeq a' l)).
    auto.
    apply in_eq.
    inversion H.
    contradiction.
    specialize (IHl H2).
    simpl in H0.
    destruct aeq in H0.
    auto.
    assert (~ In a (remove aeq a' l)).
    unfold not;intro.
    assert (In a (a0:: remove aeq a' l)).
    apply in_cons.
    auto.
    contradiction.
    apply IHl.
    auto.
Qed.

Lemma notInRemoveAll : forall (A:Set) (toBeRemoved l:list A) (a:A) (aeq : forall x y:A, {x=y}+{x<>y}), In a l -> ~In a (removeAll aeq toBeRemoved l) -> In a toBeRemoved.
Proof.
  intros.
  induction toBeRemoved.
  simpl in H0. contradiction.
  simpl in *.
  destruct (aeq a a0).
  left. auto.
  rewrite <- removeSthElse in H0.
  right. apply IHtoBeRemoved.
  unfold not. intro.
  apply H0. auto.
Qed.

Lemma inRemoveAll : forall (toBeRemoved l: list A) (a: A) (aeq : forall x y:A, {x=y}+{x<>y}),
  In a (removeAll aeq toBeRemoved l) -> In a l /\ ~ In a toBeRemoved.
Proof.
  intros.
  induction toBeRemoved.
  simpl in *. split; auto.
  simpl in *.
  rewrite <- removeSthElse in H.
  destruct H.
  specialize (IHtoBeRemoved H0).
  destruct IHtoBeRemoved as [H1 H2].
  split; auto.
  unfold not; intros.
  destruct H3.
  symmetry in H3. contradiction.
  contradiction.
Qed.

Lemma lastConsLast : forall (A:Set) (l:list A) (a a1 a2:A), l<>nil -> last (a::l) a1 = last l a2.
Proof.
    intros.
    simpl.
    induction l;intros.
    destruct H.
    auto.
    simpl.
    destruct l.
    auto.
    apply IHl.
    unfold not;intros.
    inversion H0.
Qed.
End ListAuxFuns.
