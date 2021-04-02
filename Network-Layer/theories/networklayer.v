From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.
Require Import Omega.

Record regMem (X : Type) := mkMem 
{
    address : nat;
    key : nat;
    value : X
}.

Definition isDesc {X: Type} (a k: nat) (r : regMem X): bool := 
match r with
| {| address := a'; key := k'|} => (eqb a' a) && (eqb k' k)
end.

Definition getAddr {X: Type} (r : regMem X) : nat := 
match r with
| {| address := a'; key := _|} => a'
end.

Definition getKey {X: Type} (r : regMem X) : nat := 
match r with
| {| address := _; key := k'|} => k'
end.

Definition getValue {X: Type} (r : regMem X) : X := 
match r with
| {| value := v|} => v
end.

Definition setValue {X : Type} (v : X) (r : regMem X) : regMem X :=
match r with
| {| address := a; key := k; value := v'|} => mkMem X a k v
end.

Record node (X : Type) := mkNode 
{
    crashed : bool;
    regions : list (regMem X);
    regionUnique : forall (r r' : regMem X) regions, 
        In r regions /\ In r' regions -> (getAddr r = getAddr r' <-> getKey r = getKey r')
}.

Fixpoint inRegMem {X: Type} (a k : nat) (l : list (regMem X)) : option X :=
match l with
| cons x l' => match isDesc a k x with
               | true => Some (getValue x)
               | false => inRegMem a k l'
               end
| nil => None
end.

Fixpoint setRegMem {X: Type} (a k : nat) (v : X) (prev : list (regMem X)) (l : list (regMem X)) : prod (bool) (list (regMem X)) :=
match l with
| cons x l' => match isDesc a k x with
               | true => pair true (prev ++ (cons (setValue v x) l'))
               | false => setRegMem a k v (prev ++ cons x nil) l'
               end
| nil => pair false prev
end.

Definition frst {X Y : Type} (p : prod X Y) : X := 
match p with
| pair x y => x
end.

Definition scnd {X Y : Type} (p : prod X Y) : Y := 
match p with
| pair x y => y
end.

Definition optionToPair {X : Type} (o : option X) (default : X) : prod bool X :=
match o with
| Some x => pair true x
| None => pair false default
end.

Lemma someEq : forall (X: Type) (a b : X), Some a = Some b <-> a = b.
Proof.
    intros; split; intros.
    - injection H. auto.
    - rewrite H. reflexivity.
Qed.

Lemma someNeq : forall (X: Type) (a b : X), Some a <> Some b <-> a <> b.
Proof.
    intros; split; intros; unfold not; intros.
    - intuition. apply H. rewrite H0. reflexivity.
    - intuition. apply H. apply -> someEq in H0. apply H0.
Qed.

Lemma someEq2 : forall (X: Type) (a : X) (o : option X), Some a = o -> (exists b, o = Some b /\ a = b).
Proof.
    intros.
    exists a.
    rewrite H.
    auto.
Qed.

Lemma inRegMemLemma1 : forall (X: Type) (a k: nat) (r : regMem X) (l : list (regMem X)), inRegMem a k (r :: l) = None -> isDesc a k r = false /\ inRegMem a k l = None.
Proof.
    intros.
    split; simpl in H; destruct (isDesc a k r); auto.
    - discriminate H.
    - discriminate H.
Qed.

Lemma applyList : forall (X : Type) (l l' : list X) (x : X),
l ++ x :: l' = l ++ (cons x nil) ++ l'.
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Lemma setRegMemLemma : forall (X: Type) (a k: nat) (v : X) (l l' : list (regMem X)),
setRegMem a k v l' l = pair (frst (setRegMem a k v nil l)) (l' ++ scnd (setRegMem a k v nil l)).
Proof.
    intros.
    generalize l'.
    induction l.
    - simpl. intros. rewrite app_nil_r. reflexivity.
    - simpl. destruct (isDesc a k a0).
      + simpl. reflexivity.
      + simpl. intros.
        assert(setRegMem a k v (a0 :: nil) l = 
        pair (frst (setRegMem a k v (nil) l))
        ((cons a0 nil) ++ scnd (setRegMem a k v (nil) l))
        ). {
            auto.
        }
        rewrite H.
        simpl.
        assert(l'0 ++ a0 :: scnd (setRegMem a k v nil l) = 
        l'0 ++ (a0 :: nil) ++ scnd (setRegMem a k v nil l)).
        { 
            apply applyList.
        }
        rewrite H0.
        rewrite app_assoc.
        apply IHl.
Qed.

Lemma setGetNexistRegMem : forall (X: Type) (a k: nat) (v : X) (l l' : list (regMem X)), 
inRegMem a k l = None -> setRegMem a k v nil l = pair false l.
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - apply inRegMemLemma1 in H. destruct H. simpl. rewrite H.
      apply IHl in H0. rewrite setRegMemLemma. rewrite H0. simpl. reflexivity.
Qed.

Definition qualifiedOption {X: Type} (o : option X) (b: bool) : option X :=
match b with 
| true => o
| false => None
end.

Definition read {X: Type} (address key : nat) (n : node X) 
: prod (option X) (node X) := 
match n with
| {| regions := l; crashed := c |} => pair (qualifiedOption (inRegMem address key l) (negb c)) n
end.

Definition write {X: Type} (address key : nat) (n : node X) 
: option X := 
match n with
| {| regions := l; crashed := c |} => qualifiedOption (inRegMem address key l) (negb c)
end.

Definition isCrashed {X: Type} (node : node X)  : bool := 
match node with
| {|crashed := c|} => c
end.

Definition send {X: Type} (node : node X)  : bool := negb (isCrashed node).
Definition recv {X: Type} (node : node X) : bool := negb (isCrashed node).