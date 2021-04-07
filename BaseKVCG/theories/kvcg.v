From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Structures.Equalities.

(*
Since we have linearizability we can just assume that
operations happen sequentially in real time in a single
thread when proving stuff
*)

Record kvcg := mkKVCG {
    ts : nat;
    cstore : nat -> option nat;
    hotcache : nat -> option nat;
    model : nat -> bool
}.

Definition getTs (k : kvcg) : nat :=
match k with
| {| ts := x |} => x
end.

Definition getCstore (k : kvcg) : nat -> option nat :=
match k with
| {| cstore := x |} => x
end.

Definition getHotcache (k : kvcg) : nat -> option nat :=
match k with
| {| hotcache := x |} => x
end.

Definition getModel (k : kvcg) : nat -> bool :=
match k with
| {| model := x |} => x
end.

Definition add (k v : nat) (f : nat -> option nat) : nat -> option nat :=
(fun x => if eqb x k then Some v else (f x)).

Definition atomicModify (key : nat) (k : kvcg) : kvcg := 
match (getModel k) key with
| true => mkKVCG (S((getTs k))) 
                (getCstore k)
                (add key (S((getTs k))) (getHotcache k))
                (getModel k)
| false => mkKVCG (S((getTs k))) 
          (add key (S((getTs k))) (getCstore k))
          (getHotcache k)
          (getModel k)
end.

Definition optionNatTo0 (n : option nat) : nat :=
match n with
| Some x => x
| None => 0
end.

Definition find (k : nat) (f : nat -> option nat) : option nat :=
f k.

Definition atomicGet (key : nat) (k : kvcg) : nat := 
match (getModel k) key with
| true => optionNatTo0 (find key (getHotcache k))
| false => optionNatTo0 (find key (getCstore k))
end.

Lemma modelConstantAcrossMod : forall (key : nat) (k : kvcg),
getModel (atomicModify key k) = getModel k.
Proof.
    intros.
    unfold atomicModify.
    destruct ((getModel k) key); auto.
Qed.

Lemma nIsN : forall (n: nat), n =? n = true.
Proof.
    intros.
    induction n; try reflexivity.
    - simpl. auto.
Qed.

Lemma findAddLemma : forall (k v : nat) (m : nat -> option nat),
find k (add k v m) = Some v.
Proof.
    intros.
    unfold find.
    unfold add.
    simpl.
    rewrite nIsN.
    auto.
Qed.
    
Lemma findAdd2UniqueLemma1 : forall (k k1 v v1 : nat) (m : nat -> option nat),
k1 <> k -> find k1 (add k1 v1 (add k v m)) = Some v1.
Proof.
    intros.
    unfold find.
    unfold add.
    simpl.
    rewrite nIsN.
    auto.
Qed.

Lemma nIsNotM : forall (n m : nat),
n <> m <-> eqb n m = false.
Proof.
    induction n.
    - destruct m. 
      split; intros; try contradiction; try discriminate.
      split; intros; induction m; try auto.
    - destruct m.
      split; intros; try contradiction; try discriminate; try auto.
      split; intros.
      + simpl. 
        apply IHn. 
        unfold not. 
        unfold not in H. 
        intros.
        apply H.
        lia.
     + unfold not.
       intros.
       apply IHn in H.
       unfold not in H.
       lia.
Qed.

Lemma mIsNotN : forall (n m : nat),
m <> n <-> eqb n m = false.
Proof.
    induction n.
    - destruct m. 
      split; intros; try contradiction; try discriminate.
      split; intros; induction m; try auto.
    - destruct m.
      split; intros; try contradiction; try discriminate; try auto.
      split; intros.
      + simpl. 
        apply IHn. 
        unfold not. 
        unfold not in H. 
        intros.
        apply H.
        lia.
     + unfold not.
       intros.
       apply IHn in H.
       unfold not in H.
       lia.
Qed.


Lemma findAdd2UniqueLemma2 : forall (k k1 v v1 : nat) (m : nat -> option nat),
k1 <> k -> find k (add k1 v1 (add k v m)) = Some v.
Proof.
    intros.
    unfold find.
    unfold add.
    rewrite nIsN.
    rewrite mIsNotN in H.
    rewrite H.
    reflexivity.
Qed.

Lemma immediateGetReturnsLastUpdate : forall (key : nat) (k : kvcg),
atomicGet key (atomicModify key k) = S (getTs k).
Proof.
    intros.
    unfold atomicGet.
    rewrite modelConstantAcrossMod.
    unfold atomicModify.
    destruct ((getModel k) key).
    - simpl. rewrite findAddLemma. auto.
    - simpl. rewrite findAddLemma. auto.
Qed.

Fixpoint doListOfModifcations (l : list nat) (k : kvcg) := 
match l with
| nil => k
| x :: l' => doListOfModifcations l' (atomicModify x k)
end.

Lemma modelConstantAcrossListMod : forall (keys : list nat) (k : kvcg),
getModel (doListOfModifcations keys k) = getModel k.
Proof.
    induction keys.
    - auto.
    - simpl. 
      intros. 
      assert(getModel ((atomicModify a k)) = getModel k).
      {
        apply modelConstantAcrossMod.
      }
      rewrite <- H.
      apply IHkeys. 
Qed.

Fixpoint In (a: nat) (l:list nat) : Prop :=
    match l with
      | nil => False
      | b :: m => b = a \/ In a m
    end.

Lemma getReturnsLastUpdateFrom2 : forall (key key2 ts : nat) (k : kvcg),
(key <> key2) /\ (ts = getTs k) -> atomicGet key (atomicModify key2 (atomicModify key k)) = S (ts).
Proof.
    intros.
    destruct H.
    unfold atomicGet.
    repeat rewrite modelConstantAcrossMod; 
    unfold atomicModify;
    repeat rewrite modelConstantAcrossMod;
    destruct ((getModel k) key); simpl; 
    destruct ((getModel k) key2); simpl;
    try rewrite findAddLemma; auto.
    - unfold find. 
      unfold add.
      assert(key =? key2 = false).
      {
        apply nIsNotM in H.
        assumption.
      }
      rewrite H1.
      rewrite nIsN.
      rewrite H0.
      simpl.
      reflexivity.
    - rewrite H0. reflexivity.
    - rewrite H0. reflexivity.
    - unfold find. 
      unfold add.
      assert(key =? key2 = false).
      {
        apply nIsNotM in H.
        assumption.
      }
      rewrite H1.
      rewrite nIsN.
      rewrite H0.
      simpl.
      reflexivity.
Qed.
