(* En este archivo se demuestran teoremas que forman parte
* de la librería de Coq en versiones posteriores
* a la utilizada en el presente trabajo *)
Require Import Coq.Lists.List.
Require Import Classical.
Set Reversible Pattern Implicit. 

Section MyConcat.

    Context `{A:Type, B:Type}.
Fixpoint concat (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x l => x ++ concat l
  end.

    Theorem concat_nil : concat nil = nil.
    Proof.
        auto.
    Qed.

    Theorem concat_cons : forall x l, concat (cons x l) = x ++ concat l.
    Proof.
        intros.
        auto.
    Qed.

    Theorem concat_app : forall l1 l2, concat (l1 ++ l2) = concat l1 ++ concat l2.
    Proof.
        intros.
        induction l1.
        auto.
        simpl.
        rewrite IHl1.
        apply app_assoc.
    Qed.

 Definition flat_map (f:A -> list B) :=
    fix flat_map (l:list A) : list B :=
    match l with
      | nil => nil
      | cons x t => (f x)++(flat_map t)
    end.

    Theorem in_flat_map : forall (f:A->list B)(l:list A)(y:B), In y (flat_map f l) <-> exists x, In x l /\ In y (f x).
    Proof.
        intros.
        split;intros.
        induction l; simpl in H.
        destruct H.
        rewrite in_app_iff in H.
        destruct H.
        exists a.
        split;auto.
        apply in_eq.
        specialize (IHl H).
        destruct IHl.
        exists x.
        destruct H0.
        split;auto.
        apply in_cons;auto.
        destruct H.
        destruct H.
        induction l.
        inversion H.
        simpl.
        rewrite in_app_iff.
        inversion H.
        left.
        rewrite H1;auto.
        right.
        apply IHl;auto.
    Qed.
End MyConcat.

Theorem flat_map_concat_map : forall A B (f : A -> list B) l, flat_map f l = concat (map f l).
Proof.
    intros.
    induction l.
    auto.
    simpl.
    rewrite IHl;auto.
Qed.

Theorem In_nth_error :forall (A:Set) (x:A) (l:list A), In x l -> exists n, nth_error l n = Some x.
Proof.
    intros.
    induction l.
    inversion H.
    elim (classic (a=x));intros.
    rewrite H0 in *.
    exists 0.
    auto.
    inversion H.
    contradiction.
    specialize (IHl H1).
    destruct IHl.
    exists (S x0).
    auto.
Qed.

Theorem gen_nth_err_in : forall (A:Set) (x:A) (l:list A), (exists n:nat,nth_error l n = Some x) -> In x l.
Proof.
    intros.
    induction l.
    destruct H.
    destruct x0;simpl in H;discriminate H.
    destruct H.
    destruct x0;simpl in H.
    inversion H.
    apply in_eq.
    apply in_cons.
    apply IHl.
    exists x0;auto.
Qed.


Theorem nth_error_In :forall (A:Set) (x:A) (l:list A) (n:nat), nth_error l n = Some x -> In x l.
Proof.
    intros.
    apply gen_nth_err_in.
    exists n;auto.
Qed.

Theorem map_cons :forall (A B:Set) (f:A->B) (x:A)(l:list A), map f (x::l) = (f x) :: (map f l).
Proof.
    intros.
    auto.
Qed.
