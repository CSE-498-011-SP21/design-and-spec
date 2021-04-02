From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.

Record regMem := mkMem 
{
    address : nat;
    key : nat
}.

Definition isDesc (a k: nat) (r : regMem) : bool := 
match r with
| {| address := a'; key := k'|} => (eqb a' a) && (eqb k' k)
end.

Definition getAddr (r : regMem) : nat := 
match r with
| {| address := a'; key := _|} => a'
end.

Definition getKey (r : regMem) : nat := 
match r with
| {| address := _; key := k'|} => k'
end.


Record node := mkNode 
{
    crashed : bool;
    regions : list regMem;
    regionUnique : forall (r r' : regMem) regions, 
        In r regions /\ In r' regions -> (getAddr r = getAddr r' <-> getKey r = getKey r')
}.

Fixpoint inRegMem (a k : nat) (l : list regMem) : bool :=
match l with
| cons x l' => match isDesc a k x with
               | true => true
               | false => inRegMem a k l'
               end
| nil => false
end.

Definition read (address key : nat) (node : node) 
: bool := 
match node with
| {| regions := l; crashed := c |} => (inRegMem address key l) && negb c
end.

Definition write (address key : nat) (node : node) 
: bool := 
match node with
| {| regions := l; crashed := c |} => (inRegMem address key l) && negb c
end.

Definition isCrashed (node : node)  : bool := 
match node with
| {|crashed := c|} => c
end.

Definition send (node : node)  : bool := negb (isCrashed node).
Definition recv (node : node) : bool := negb (isCrashed node).