Inductive mynat : Type :=
| Zero
| Succ : mynat -> mynat.

Check mynat.
Print mynat.
Check mynat_ind.

Check nat.
About nat.
Print nat.
Check nat_ind.

Check 10.
Compute 10.
Compute 10 + 10.
Eval simpl in (fun x => x + (10 + 10)).
Eval simpl in (fun x => 10 + x + 10).
Compute (fun x => 10 + x + 10).

Lemma twenty_one_times_two_is_fourty_two :
  21 + 21 = 42.
Proof.
  simpl.
  trivial.
Qed.

Inductive prod (A : Type) (B : Type) := Pair : A -> B -> prod A B.

Check prod.
Check prod_ind.

Compute (Pair nat nat (1 + 1) (2 + 2)).

Arguments Pair [A B] _ _.

Compute (Pair (1 + 1) (2 + 2)).

Print bool.
Check bool.
About bool.
Check true.
Check false.

Compute (Pair 1 true).

Definition swap {A : Type} {B : Type} (xy : prod A B) : prod B A :=
  match xy with
  | Pair x y => Pair y x
  end.

Lemma swap_of_swap :
  forall {A B : Type} (xy : prod A B),
  swap (swap xy) = xy.
Proof.
  intros A B xy.
  simpl.
  destruct xy.
  simpl swap at 2.
  simpl swap at 1.
  trivial.
Qed.

Fixpoint is_even (n : nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n) => is_even n
  end.

Lemma fourty_two_is_even : is_even 42 = true.
Proof.
  simpl.
  trivial.
Qed.

Lemma plus_successor : forall (m n : nat), n + S m = S (n + m).
Proof.
  intros m n.
  induction n.
  - simpl.
    trivial.
  - simpl.
    rewrite IHn.
    trivial.
Qed.

Lemma twice_is_even : forall (n : nat), is_even (n + n) = true.
Proof.
  intros n.
  induction n.
  - simpl.
    trivial.
  - simpl in *.
    rewrite (plus_successor n n).
    rewrite IHn.
    trivial.
Qed.

Inductive mylist (A : Type) : Type :=
| Nil : mylist A
| Cons : A -> mylist A -> mylist A.
Arguments Nil [A].
Arguments Cons [A] _ _.

Check mylist.
Check mylist_ind.

Print list.

Require Import Coq.Lists.List.
Import ListNotations.

Compute 1 :: 2 :: 3 :: 4 :: [].
Compute [1;2;3;4].
    
Fixpoint length {A : Type} (xs : list A) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => 1 + length xs'
  end.

Fixpoint append {A : Type} (xs : list A) (ys : list A) : list A :=
  match xs with
  | [] => ys
  | x :: xs' => x :: append xs' ys
  end.
                                       
Fixpoint reverse {A : Type} (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' => append (reverse xs') [x]
  end.

Lemma append_of_nil :
  forall {A} (xs : list A),
  append xs [] = xs.
Proof.
  intros A xs. 
  induction xs.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma append_assoc :
  forall {A} (xs ys zs : list A),
  append (append xs ys) zs = append xs (append ys zs).
Proof.
  intros A xs ys zs.
  induction xs.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma reverse_of_append :
  forall {A} (xs : list A) (ys : list A),
  reverse (append xs ys) = append (reverse ys) (reverse xs).
Proof.
  intros A xs ys.
  induction xs.
  - simpl.
    rewrite (append_of_nil (reverse ys)).
    reflexivity.
  - simpl.
    rewrite <- (append_assoc (reverse ys) (reverse xs) [a]).
    rewrite IHxs.
    reflexivity.
Qed.

Lemma reverse_of_reverse : forall {A} (xs : list A), reverse (reverse xs) = xs.
Proof.
  intros A xs.
  induction xs.
  - simpl.
    reflexivity.
  - simpl.
    rewrite (reverse_of_append (reverse xs) [a]).
    rewrite IHxs.
    simpl.
    reflexivity.
Qed.

Compute (reverse [1;2;3;4]).
Compute (reverse (reverse [1;2;3;4])).
Compute (reverse_of_reverse [1;2;3;4]).

Fixpoint reverse_h {A : Type} (xs : list A) (ys : list A) : list A :=
  match xs with
  | [] => ys
  | x :: xs' => reverse_h xs' (x :: ys)
  end.


Lemma reverse_h_correct :
  forall {A : Type} (xs : list A) (ys : list A),
  reverse_h xs ys = append (reverse xs) ys.
Proof.
  intros A xs.
  induction xs.
  - intros ys.
    simpl.
    reflexivity.
  - intros ys.
    simpl.
    rewrite IHxs.
    rewrite (append_assoc (reverse xs) [a] ys).
    simpl.
    reflexivity.
Qed.

Definition reverse_better {A : Type} (xs : list A) : list A := reverse_h xs [].

Lemma reverse_of_reverse_better :
  forall {A} (xs : list A),
  reverse_better (reverse_better xs) = xs.
Proof.
  intros A xs.
  unfold reverse_better at 1.
  rewrite (reverse_h_correct (reverse_better xs) []).
  rewrite (append_of_nil (reverse (reverse_better xs))).
  unfold reverse_better.
  rewrite (reverse_h_correct xs []).
  rewrite (append_of_nil (reverse xs)).
  rewrite (reverse_of_reverse xs).
  reflexivity.
Qed.

Lemma reverse_of_reverse_h :
  forall {A} (xs ys zs: list A),
  reverse_h (reverse_h xs ys) zs = reverse_h ys (append xs zs).
Proof.
  intros A xs.
  induction xs.
  - intros ys zs.
    simpl.
    reflexivity.
  - intros ys zs.
    simpl.
    rewrite (IHxs (a :: ys) zs).
    simpl.
    reflexivity.
Qed.

Lemma reverse_of_reverse_better_direct :
  forall {A} (xs : list A),
  reverse_better (reverse_better xs) = xs.
Proof.
  intros A xs.
  unfold reverse_better.
  rewrite (reverse_of_reverse_h xs [] []).
  simpl.
  rewrite (append_of_nil xs).
  reflexivity.
Qed. 

Require Extraction.
Recursive Extraction reverse_h.
Extract Inductive list => "list" [ "[]" "(::)" ].
Recursive Extraction reverse_h.

Recursive Extraction length.
Extract Inductive nat => "int" [ "0" "succ" ].
Recursive Extraction length.
Extract Inductive nat => "int" [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Recursive Extraction length.
Extract Inlined Constant Nat.add => "(+)".
Recursive Extraction length.

Require Import Coq.extraction.ExtrOcamlNatInt.
Recursive Extraction length.
