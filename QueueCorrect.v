Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.PeanoNat.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.

(* Optional, but useful configuration *)
Set Printing Parentheses.

(**
  When reasoning about algorithms and datastructure, there's usually two primary goals
  1) Is the algorithm correct
  2) How efficient is it?

  In this section, we're going to focus on solving goal 1, and describe 
  a technique for reasoning about demonstrating a queue is correct.
*)

(* Optional Type to deal with empty lists*)
Inductive Maybe (X: Type) : Type :=
  | None
  | Some (thing : X)
  .

Arguments Some {X}.
Arguments None {X}.

(**
Before we start with queues, let's try the one of simplest data 
structures one can reason about in a functional language: the stack.
When you think about it, a stack is just a list
*)

(*We can push to the top of a stack*)
Definition stack_push {X: Type} (e: X) (l : list X) :=
  cons e l.

(*And we can retrieve the head element*)
Definition stack_head {X: Type} (l : list X) : Maybe X :=
  match l with
  | [] => None
  | h :: t => Some h
  end.

(*We can also remove the top element to get to the next*)
Definition stack_pop {X : Type} (l : list X): list X := 
  match l with
  | nil => []
  | h::t => t
  end.

(*All of these operations can be done in O(1) time, since they all deal with 
the latest constructor
*)
Compute stack_push 1 [1;2;3;4].
Compute stack_head [1;2;3;4].
Compute stack_head [].
Compute stack_pop [].
Compute stack_pop [2;3;4].

(*
But what if we want a First-In-First-Out queue?
Because our end element is wrapped in function calls, we
cannot immediately acces it.
We can try unfolding the list to get to the last element
*)
Fixpoint list_otherhead {X : Type} (l: list X): Maybe X :=
  match l with
  | [] => None
  | h::[] => Some h
  | h::t => list_otherhead t 
  end.

(*However, this is inefficient. Although it returns the answer
 computing the head takes O(N) time! *)
Compute list_otherhead [1;2;3;4].

(*
Author's note: Working with Maybe's wasn't worth the effort, so I drop that notation
moving forward and instead resolve single elements as single-element lists.
*)

(* 
As can be seen above, we'll need to come up with a better way of working with queues.
There exists many implementations of purely functional FIFO queues, and in this exploration
we'll be looking at an implementation from the book 'Purely Functional Datastructures' by 
Chris Okasaki.
His example code is featured in Section 5.2, and is written in OCaml. We will attempt derive his
concepts and define them in Coq.

His implementation works like this:
The inherent problem with using a list to represent a queue is that the head is the first item appended to it.
To address this, instead of having a single list to represent the queue, we can instead create two seperate lists, a 'front'
and a 'back' respectively. The front list is in reverse order, and the rear list is in the same order in which elements 
are appended.

For example, for the list
[1;2;3;4] = ([4;3],[1;2])


We could represent as a queue with
([4;3],[1;2])

We can now take the head of the front list, to return the head in O(1) time. Popping the queue is just removing the head 
which is also O(1)
head([4;3],[1;2]) = 4
tail([4;3],[1;2]) = ([3],[1;2])

For these head and pop calls to work, a non-empty queue _must_ always have at least one element in the front list. Therefore,
We maintain an invariant that says the front list of a valid non-empty queue is never empty. 

The following queue would be invalid because it does not satisfy the invariant
([],[1;2]).

The only time the front can be empty, is if the queue is empty.

When we pop from a queue like ([3],[1;2]) we need to reverse the rear list and move it to the front, like so:

tail([3],[1;2]) = ([2;1], []).
push 1 ([],[]) = ([1],[])
push 2 ([1],[]) = ([1],[2])
push 3 ([1],[2]) = ([1],[3;2])


It is okay for the rear list to be empty. 
*)

(*
Let's try to implement this concept in Coq.
We'll need a new data structure to represent a FIFO queue 
*)
Inductive fifo (X: Type): Type :=
  (* The empty queue *)
  | f_empty
  | Queue (p : list X * list X)
  .

Arguments Queue {X}.
Arguments f_empty {X}.

Check (Queue ([1;2],[4;3])).

(* Querying the head can now be done in O(1) time! *)
Definition fifo_hd {X: Type} (q: fifo X) : list X :=
  match q with
  | Queue (h1::t1, l2) => [h1]
  | _ => nil
  end.

Compute fifo_hd (Queue ([1;2],[4;3])).

(* Pushing a single element onto the Queue is straightforward *)
Definition fifo_push {X: Type} (e: X) (q: fifo X) : fifo X :=
  match q with
  (* The first element pushed onto an empty queue must go in the front to satisfy the invariant *)
  | f_empty => Queue ([e],[])
  | Queue([],[]) => Queue ([e],[])
  (* Otherwise, add it to the rear list *)
  | Queue (l1,l2) => Queue (l1,e::l2)
  end.
 
Compute fifo_push 5 (Queue ([1;2],[4;3])).
Compute fifo_push 3 (fifo_push 2 (fifo_push 1 (f_empty))).

(* 
To pop the head off a queue, we retun the tail.
If we empty the front list, we need to move the rear
list to the front, and reverse it
*)
Definition fifo_tl {X: Type} (q: fifo X) : fifo X :=
  match q with
  | f_empty => f_empty
  | Queue (h1::[], []) => f_empty
  (* Last element of the head reached, reverse rear list *)
  | Queue (h1::[], l2) => Queue (rev l2, [])
  | Queue (h1::t1, l2) => Queue (t1,l2)
  (* 
    Because of invariant, this should never be called 
    but it is required by Coq to exhaustively cover all cases

    Open problem to consider: Perhaps revising the inductive type could fix this?
  *)
  | Queue ([], l2) => Queue([], l2)
  end.

(*Pop an element out of the Queue, O(1)*)
Compute fifo_tl (Queue ([1;2;3],[5;4])).
(*Pop 1 out of the Queue, but do list reversal, O(N)*)
Compute fifo_tl (Queue ([1],[4;3;2])).
(*Iteratively empty the entire Queue*)
Compute fifo_tl (fifo_tl (Queue ([1],[4;3;2]))).
Compute fifo_tl (fifo_tl (fifo_tl (Queue ([1],[4;3;2])))).
Compute fifo_tl (fifo_tl (fifo_tl (fifo_tl (Queue ([1],[4;3;2]))))).

(* 
If we want to push multiple elements to a Queue, that is also easy and we can do so in O(n) 
time for the size of however many element we want to push.
Although tempting to use a fixpoint, definitions make further proofs much easier 
*)
Definition fifo_push_all {X: Type} (l: list X) (q : fifo X) : fifo X :=
  match l with
  | [] => q
  | h::t => match q with
            (* If pushing onto an empty list, take the first item to 
            push and move it to the front list *)
            | f_empty => Queue([h],(rev t))
            (* Otherwise just append each item in the order specified *)
            | Queue(l1,l2) => Queue(l1, (rev l)++l2)
            end
  end.

Compute fifo_push_all [1;2;3;4;5] f_empty.
(* 
Popping all of the elements out is not so straightforward as pushing.
Ideally, we want to be able to just keep calling fifo hd on the next iteration of tail,
 but this fails because Coq cannot determine how the function is decreasing 
 *)
Fail Fixpoint fifo_pop_all_fail {X: Type} (q: fifo X): list X :=
  match q with
  | f_empty => []
  | Queue(l1,nil) => rev l1
  | Queue (l1, _) => (fifo_pop_all_fail (fifo_tl q)) ++ (fifo_hd q)
  end.

(* To deal with this, we can provide a method of countdown by assigning a number 
and decreasing it. This works like fuel, the function will terminate when it runs out.
Note: If you want to see more examples of this concept, Volume 3 has more examples
in Selection.v
*)
Fixpoint fifo_pop_all_fuel {X: Type} (q: fifo X) (fuel: nat): list X :=
  match q with
  | f_empty => []
  (* If we only have the front list, we can just return it *)
  | Queue(l1,nil) => rev l1
  (* Otherwise we need to ensure we handle the tail properly *)
  | Queue (l1, _) => match fuel with
                        | O => []
                        | S(n) =>  (fifo_pop_all_fuel (fifo_tl q) n) ++ (fifo_hd q)
                      end
  end.
(* We know the max number of calls to empty a queue will equal the number of elements, so we can remove that
 parameter and pre-compute it *)
Definition fifo_pop_all {X: Type} (q: fifo X): list X :=
  match q with
  | f_empty => []
  | Queue(l1,l2) => (fifo_pop_all_fuel q (length l1 + length l2))
  end.


Compute fifo_pop_all (Queue ([6;5;4],[1;2;3])).
Compute (fifo_pop_all (Queue([],[]))).

Example push_pop_test: (fifo_pop_all (fifo_push_all ([1;2;3;4;5]) f_empty)) = [5;4;3;2;1].
  Proof.
    simpl.
    reflexivity.
  Qed.

(* We can easily show that pushing a single element leads to that element coming back out *)
Theorem push_pop_single {X: Type}: forall (e : X) , fifo_pop_all (fifo_push e f_empty) = [e]. 
Proof. intros. reflexivity. Qed.


(* 
Author's note:
When writing these proofs I may have stumbled upon the solution and not realized how hard it was.
I really have no idea how many stars to assign to each of these problems. Consider them best guesses 
based on the solution I found.
*)

(** **** Exercise: 1 star
Prove that popping all the elements off the front list of a queue reverses the order
*)
Theorem fifo_pop_all_head_correct {X: Type}: forall l : list X, fifo_pop_all (Queue(l,[])) = rev l.
  Proof.
    intros.
    simpl.
    rewrite Nat.add_0_r.
    destruct l.
    simpl. reflexivity.
    simpl. reflexivity.
  Qed.

(* I couldn't find this lemma in the standard library, but found it useful.*)
Lemma rev_nil_eq {X: Type}: forall l : list X, l = [] <-> (rev l) = [].
Proof.
{
  split.
  intros. rewrite H. reflexivity.
  intros. induction l.
  reflexivity.
  simpl in H. apply app_eq_nil in H. destruct H. apply IHl in H. rewrite H. apply H0.
}
Qed.


(** **** Exercise: 2 stars 
Prove that pushing a list through an empty queue and popping it back out returns the same list but in reverse 
*)
Theorem push_pop_empty_revl {X: Type}: forall l : list X, fifo_pop_all (fifo_push_all l f_empty) = rev l.
  Proof.
    intros.
    induction l.
    {
      simpl.
      reflexivity.
    }
    simpl.
    destruct (rev l) eqn:Erl.
    apply rev_nil_eq in Erl.
    simpl. reflexivity.
    simpl.
    change ((rev l0) ++ [x]) with (rev (x:: l0)).
    rewrite <- Erl.
    rewrite rev_involutive.
    rewrite Erl.
    reflexivity.
  Qed.

(** 
Prove that we can remove the the head of the front list and move it outside of the pop_all
Author's note: this is the only Theorem where I use auto to solve the problem. But since I did,
I'll just give it to you since it gets pretty ugly.
*)
Theorem fifo_pop_one_correct {X: Type}: forall (h : X) (t l2 : list X), 
  length t > 0 -> fifo_pop_all (Queue((h::t),l2)) = (fifo_pop_all (Queue(t,l2)))++[h].
  Proof.
    induction l2.
    intros.
    rewrite fifo_pop_all_head_correct. rewrite fifo_pop_all_head_correct. simpl. reflexivity.
    simpl. destruct t.
    intros. inversion H.
    intros. apply IHl2 in H. auto.
  Qed.
(* 
To prove that the Queue is correct what we really want to verify two things:
First, we want want to verify that popping everything out of a queue comes out correct every time, that is:

fifo_pop_all (Queue(l1,l2)) = l2 ++ rev l1.

Second: adding a list to a queue of any front and rear lists results in the correct unfolding. AKA:

fifo_pop_all(fifo_push_all l3 (Queue(l1,l2))) =  (rev l3) ++ l2 ++ (rev l1).

This turned out to be super difficult, maybe I just missed something and you can solve them here, 
but I kept getting stuck trying all sorts of methods, so I tried a different approach.
 *)
 Theorem fail_fifo_pop_all_correct {X: Type}: forall (l1 l2 : list X), 
  length l1 > 0 -> fifo_pop_all (Queue(l1,l2)) = l2++(rev l1).
  Proof.
    induction l1.
    intros. inversion H.
    destruct l2. simpl. intros. reflexivity.
    intros. simpl.
    intros. change ([] ++ (rev l1)) with (rev l1).
    simpl.
  Abort.

 Theorem fail_fifo_push_pop_all_correct {X: Type}: forall (l1 l2 l3 : list X), 
  length l1 > 0 -> fifo_pop_all(fifo_push_all l3 (Queue(l1,l2))) = l1 ++ (rev l2) ++ l3.
  Proof.
  Abort.



(* 
The first way to try and get around this issue is to redefine the problem.

When popping all the elements from the queue, if we return the head on the other side it will return the reverse list.
This way, rather returning the result, we're actually unfolding the original input using the same methods
provided by the queue.

Not only is this much easier to reason about, the proofs also require less calls to rev everywhere.
*)
Fixpoint fifo_unwrap_fuel {X: Type} (q: fifo X) (fuel: nat): list X :=
match q with
| f_empty => []
(* This time we return the front list in order *)
| Queue(l1,nil) => l1
(* Notice that we moved the head call to the left *)
| Queue (l1, _) => match fuel with
                      | O => []
                      | S(n) => (fifo_hd q) ++ (fifo_unwrap_fuel (fifo_tl q) n)
                    end
end.

(* Since we haven't changed how head and tail work, this requires no modifications. *)
Definition fifo_unwrap {X: Type} (q: fifo X): list X :=
  match q with
  | f_empty => []
  | Queue(l1,l2) => (fifo_unwrap_fuel q (length l1 + length l2))
  end.

(* Now when we calculate this, we get the element in the order in which they were inserted *)
Compute fifo_unwrap (Queue ([1;2;3],[6;5;4])).
Compute (fifo_unwrap (Queue([],[]))).

(** **** Exercise: 1 star
Prove that unwrapping all the elements off the front list of a queue returns the same list
*)
Theorem fifo_unwrap_head_correct {X: Type}: forall l : list X, fifo_unwrap (Queue(l,[])) = l.
  Proof.
    intros.
    simpl.
    rewrite Nat.add_0_r.
    destruct l.
    simpl. reflexivity.
    simpl. reflexivity.
  Qed.
  
(* Prove that pushing a list through an empty queue and unwrapping it returns the same list  *)
Theorem push_unwrap_empty_revl {X: Type}: forall l : list X, fifo_unwrap (fifo_push_all l f_empty) = l.
  Proof.
    intros.
    induction l.
    {
      simpl.
      reflexivity.
    }
    simpl.
    destruct (rev l) eqn:Erl.
    apply rev_nil_eq in Erl.
    simpl. rewrite Erl. reflexivity.
    simpl.
    change ((rev l0) ++ [x]) with (rev (x:: l0)).
    rewrite <- Erl.
    rewrite rev_involutive.
    reflexivity.
  Qed.


(** 
Now when we want to match the head of the front list of the queue, we match the head of the 
input list instead of the tail of the result, which is much easier to solve in Coq
*)
Theorem fifo_unwrap_one_correct {X: Type}: forall (h : X) (t l2 : list X), 
  length t > 0 -> fifo_unwrap (Queue((h::t),l2)) = h::(fifo_unwrap (Queue(t,l2))).
  Proof.
    induction l2.
    rewrite fifo_unwrap_head_correct. rewrite fifo_unwrap_head_correct. reflexivity.
    simpl. destruct t.
    intros. inversion H.
    intros. apply IHl2 in H. auto.
  Qed.

(* Here's a lemma that I couldn't find with search that you may find useful in coming sections. *)
Lemma app_reduce {X: Type}: forall (a: X) (l1 l2: list X), l1 = l2 <-> (a::l1) = (a::l2).
Proof.
  split.
  intros.
  rewrite H.
  reflexivity.
  intros.
  inversion H.
  reflexivity.
Qed.



(** **** Exercise: 2-3 stars
Very very useful, but not until much later, so feel free to skip for now
Prove that if unwrapping all the elements in a queue produces a correct list, then
swapping the two head elements will have the same effect on the resulting list
*)
Theorem fifo_head_swap {X: Type}: forall (x a : X) (l1 l2 : list X),
  (fifo_unwrap (Queue (x :: (a :: l1), l2))) = ((x :: (a :: l1)) ++ (rev l2)) ->
  (fifo_unwrap (Queue (a :: (x :: l1), l2))) = ((a :: (x :: l1)) ++ (rev l2)).
Proof.
  induction l1.
  intros. rewrite fifo_unwrap_one_correct. apply app_reduce.
  destruct l2. simpl. reflexivity.
  simpl. apply app_reduce. reflexivity.
  simpl. lia.
  intros. rewrite fifo_unwrap_one_correct. rewrite <- app_comm_cons. apply app_reduce.
  rewrite fifo_unwrap_one_correct. rewrite <- app_comm_cons. apply app_reduce.
  rewrite fifo_unwrap_one_correct in H. rewrite <- app_comm_cons in H. apply app_reduce in H.
  rewrite fifo_unwrap_one_correct in H. rewrite <- app_comm_cons in H. apply app_reduce in H.
  apply H.
  simpl. lia.
  simpl. lia.
  simpl. lia.
  simpl. lia.
Qed.


(* 
Now to prove that the Queue is correct we want to verify these two things:

fifo_unwrap (Queue(l1,l2)) = l1 ++ rev l2.

fifo_unwrap(fifo_push_all l3 (Queue(l1,l2))) = l1 ++ (rev l2) ++ l3.

This still turned out to be too hard, but looked a lot more reasonable to try and solve
 *)
 Theorem fail_fifo_unwrap_correct {X: Type}: forall (l1 l2 : list X), 
  length l1 > 0 -> fifo_unwrap (Queue(l1,l2)) = l1 ++ rev l2.
  Proof.
    induction l2.
    intros. 
    rewrite app_nil_r.
    apply fifo_unwrap_head_correct.
    intros.
    destruct l1.
    inversion H.
    simpl.
    apply app_reduce.
    apply IHl2 in H.
  Abort.

 Theorem fail_fifo_push_pop_all_correct {X: Type}: forall (l1 l2 l3 : list X), 
  length l1 > 0 -> fifo_unwrap(fifo_push_all l3 (Queue(l1,l2))) = l1 ++ (rev l2) ++ l3.
  Proof.
  Abort.

(*
If IndProp.v has taught me anything (besides not to start homeworks the night they are due), 
it's that when reasoning about Theorems with types fail, try
attacking the problem from a different angle using inductive propositions.

Here we define a relation for unwrapping a fifo
*)
Inductive fifo_rel {X: Type}: list X -> list X -> list X -> Prop :=
| frel_empty : fifo_rel nil nil nil
(* Similar to the Queue(l1,nil) => l1 case in our fixpoint. If you have no elements in the 
    rear list, and the front list matches the list, then they are equal *)
| frel_head l : fifo_rel l nil l
  (* Invariant friendly reduction. If we have no elements in the rear list, then we can safely
  remove matching head elements until we reach the empty queue *)
| frel_reduce_head h t1 t3 : fifo_rel t1 nil t3 -> fifo_rel (h::t1) nil (h::t3)
  (* According to the algorithm, we only move the rear list over when the front list is popping 
    its last element *)
| frel_reduce_swap h1 l2 t3: fifo_rel (rev l2) [] t3 -> 
    fifo_rel [h1] l2 (h1::t3)
(* Because of the invariant, we need to ensure that a Queue with an empty l1 and non-empty l2 
    can never be reached.
    therefore, for the front queue to reduce while elements exist in the rear, the front 
    _must_ have another element *) 
| frel_reduce h1 t1 l2 t3:  
  length t1 > 0 -> 
  fifo_rel t1 l2 t3 ->  fifo_rel (h1::t1) l2 (h1::t3)
(* Same as frel_reduce_swap, but remove an entire list *)
| frel_reduce_app l1 l2 l3: length l1 > 0 -> fifo_rel (rev l2) [] l3 -> 
  fifo_rel l1 l2 (l1 ++ l3) 
  .

Arguments frel_empty {X}.
Arguments frel_head {X}.
Arguments frel_reduce_swap {X}.
Arguments frel_reduce_head {X}.
Arguments frel_reduce {X}.
Arguments frel_reduce_app {X}.

(* Let's verify that this succeeds and fails in ways we expect *)
Example fifo_rel_test: fifo_rel [1;2] [4;3] [1;2;3;4].
  Proof.
    apply frel_reduce.
    simpl. lia.
    apply frel_reduce_swap.
    simpl.
    apply frel_head.
  Qed.

Example fifo_rel_short_fail: fifo_rel [1;2] nil [1;2;3].
Proof.
  apply frel_reduce_head.
  (* We can go no further because of invariant and pattern matching restrictions*)
  apply frel_reduce_head.
  Abort.

Example fifo_rel_order_fail: fifo_rel [1;2] [3;4] [1;2;3;4].
  Proof.
    apply frel_reduce.
    simpl. lia.
    apply frel_reduce_swap.
    simpl.
    Abort.

Example fifo_invariant_fail: fifo_rel [] [4;3;2;1] [1;2;3;4].
  Proof.
  Abort.

(** **** Exercise: 2 stars
Especially useful, prove that if the front list and final list are a FIFO relation, then they are equal
*)
Theorem fifo_rel_head_eq {X: Type}: forall l1 l3 : list X, fifo_rel l1 [] l3 <-> l1 = l3.
Proof.
  split.
  {
    intros.
    generalize dependent l3.
    induction l1.
    intros. inversion H. reflexivity. reflexivity. inversion H0.
    {
      intros. inversion H.
      reflexivity.
      apply IHl1 in H1. rewrite H1. reflexivity.
      simpl in H4. inversion H4. reflexivity. reflexivity. inversion H5.
      apply IHl1 in H5. rewrite H5. reflexivity.
      {
        simpl in H1.  inversion H1.
        rewrite app_nil_r. reflexivity.
        rewrite app_nil_r. reflexivity.
        inversion H5.
      }
    }
  }
  {
    generalize dependent l1.
    induction l3.
    intros. rewrite H. apply frel_empty.
    intros.
    rewrite H. apply frel_head.
  }
Qed.

(** **** Exercise: 2 stars
Prove that if the front, rear, and final list are a FIFO relation, then they can be unfolded
*)
Theorem fifo_rel_list_app_eq {X: Type}: forall l1 l2 l3 : list X, fifo_rel l1 l2 l3 -> (l1 ++ (rev l2)) = l3.
Proof.
  intros.
  induction H.
  reflexivity.
  simpl. rewrite app_nil_r. reflexivity.
  simpl. rewrite app_nil_r. apply fifo_rel_head_eq in H. rewrite H. reflexivity.
  simpl in IHfifo_rel. rewrite app_nil_r in IHfifo_rel. rewrite IHfifo_rel. reflexivity.
  simpl. rewrite IHfifo_rel. reflexivity.
  apply fifo_rel_head_eq in H0. rewrite H0. reflexivity.
Qed.

(** **** Exercise: 2 stars
we can also prove the almost-converse of the above theorem, 
It's an 'almost-converse' because it requires the assumption that l1 is not empty. 
Discussion: Why is this only required in one direction?
*)
Theorem list_app_eq_fifo_rel {X: Type}: forall l1 l2 l3 : list X, length l1 > 0 -> (l1 ++ (rev l2)) = l3 -> fifo_rel l1 l2 l3. 
Proof.
  intros.
  induction l2.
  simpl in H0.
  rewrite app_nil_r in H0.
  rewrite H0.
  apply frel_head.
  rewrite <- H0.
  apply frel_reduce_app.
  apply H.
  apply frel_head.
Qed.

(** **** Exercise: 3 stars
Prove that given the assumption 3 lists are a FIFO relation, then we can move the rear list over.
Author's note: I was able to prove this, but never used it elsewhere
*)
Theorem fifo_rel_swap {X: Type}: forall l1 l2 l3 : list X, fifo_rel l1 l2 l3 -> fifo_rel (l1++(rev l2)) [] l3.
Proof.
    intros.
    generalize dependent l2.
    generalize dependent l3.
    induction l1.
    {
      intros.
      simpl.
      inversion H.
      simpl. apply frel_empty.
      simpl. apply frel_empty.
      simpl in H4. rewrite <- H4. apply H1.
    }
    {
      intros.
      inversion H.
        simpl. apply frel_reduce_head. rewrite app_nil_r. apply frel_head.
        simpl. rewrite app_nil_r. rewrite -> H1. rewrite H3. apply H.
        simpl. apply frel_reduce_head. apply H4.
        apply IHl1 in H5. simpl. apply frel_reduce_head. apply H5.
        simpl. apply frel_reduce_head. apply fifo_rel_head_eq in H1. rewrite H1. apply frel_head.
    }
  Qed.

(* Here's a useful lemma that you may want *)
Lemma two_big_either {X: Type}: forall (a b : X) (l : list X),
  length (a::(b::l)) > 0 -> length (a::l) > 0 /\ length (b::l) > 0.
  Proof.
  intros.
  split.
  {
    simpl. lia.
  }
  {
    simpl. lia.
  }
  Qed.

(** **** Exercise: 4 stars
Very very useful
Prove that given the assumption 3 lists are a FIFO relation, then calling unwrap on the first two yields the third
*)
Theorem fifo_rel_if {X: Type}: forall l1 l2 l3: list X, fifo_rel l1 l2 l3 -> fifo_unwrap (Queue(l1,l2)) = l3.
Proof.
  intros.
  induction H.
  simpl. reflexivity.
  rewrite fifo_unwrap_head_correct. reflexivity.
  simpl. rewrite fifo_unwrap_head_correct in IHfifo_rel.
  rewrite IHfifo_rel. reflexivity.
  {
    simpl.
    destruct l2.
    inversion H.
    reflexivity.
    reflexivity.
    simpl.
    apply fifo_rel_head_eq.
    apply frel_reduce_head.
    simpl in H. apply H.
    apply app_reduce. simpl. apply fifo_rel_head_eq. simpl in H. apply H.
  }
  {
    simpl.
    destruct l2.
    apply fifo_rel_head_eq.
    apply frel_reduce_head.
    apply H0.
    apply app_reduce.
    unfold fifo_unwrap in IHfifo_rel.
    destruct t1.
    inversion H.
    apply IHfifo_rel.
  }
  {
    destruct l1.
    inversion H.
    induction l1.
    simpl. destruct l2. 
    simpl in IHfifo_rel. rewrite <- IHfifo_rel. reflexivity.
    {
    apply app_reduce. simpl in IHfifo_rel. rewrite Nat.add_0_r in IHfifo_rel. 
    change ((rev l2)++[x0]) with (rev (x0 :: l2)) in IHfifo_rel. rewrite <- rev_length. apply IHfifo_rel.
    }
    intros.
    apply two_big_either in H.
    destruct H.
    apply fifo_rel_head_eq in H0.
    rewrite <- H0.
    apply fifo_head_swap.
    rewrite fifo_unwrap_one_correct. rewrite <- app_comm_cons. apply app_reduce.
    apply IHl1 in H.
    rewrite <- H0 in H.
    apply H.
    simpl. lia.
  }
Qed.

(* 
Finally, now with our relation capabilities, prove the queue. 
Hint: I was able to solve this with a combination of fifo_head_swap and fifo_rel_if
*)
Theorem fifo_push_pop_all_correct {X: Type}: forall l1 l2 l3 : list X, 
  length l1 > 0 ->
  fifo_unwrap(fifo_push_all l3 (Queue(l1,l2))) = l1 ++ (rev l2) ++ l3.
  Proof.
  induction l1.
  {
    intros.
    inversion H.
  }
  {
    intros.
    unfold fifo_push_all.
    destruct l3 eqn:El3.
    {
    apply fifo_rel_if.
    rewrite app_nil_r.
    apply frel_reduce_app.
    simpl. lia.
    apply frel_head.
    }
    {
      apply fifo_rel_if.
      rewrite <- El3.
      simpl.
      change ((a :: (l1 ++ ((rev l2) ++ l3)))) with ((a :: l1) ++ ((rev l2) ++ l3)).
      apply frel_reduce_app.
      simpl. lia.
      rewrite rev_app_distr.
      rewrite rev_involutive.
      apply frel_head.
    }
  }
  Qed. 
  (*
  The end :D
  There's a deep dive into optimizing this below, but I was unable to improve any further.
  feel free to take a stab at it, but I can't garauntee it's possible
  *)



  (*
Can we do better? frel_reduce_app can potentially be removed. I got _very_ close to proving it again without it.
*)
Inductive fifo_rel2 {X: Type}: list X -> list X -> list X -> Prop :=
  (* an empty Queue is equivalent to an empty array *)
  | frel2_empty : fifo_rel2 nil nil nil

  (* Similar to the Queue(l1,nil) => l1 case in our fixpoint. If you have no elements in the 
     rear list, and the front list matches the list, then they are equal *)
  | frel2_head l : fifo_rel2 l nil l
  
  (* Invariant friendly reduction. If we have no elements in the rear list, then we can safely
    remove matching head elements until we reach the empty queue *)
  | frel2_reduce_head h t1 t3 : fifo_rel2 t1 nil t3 -> fifo_rel2 (h::t1) nil (h::t3)
  
  (* According to the algorithm, we only move the rear list over when the front list is popping 
     its last element *)
  | frel2_reduce_swap h1 l2 t3: fifo_rel2 (rev l2) [] t3 -> 
      fifo_rel2 [h1] l2 (h1::t3)
  (* Because of the invariant, we need to ensure that a Queue with an empty l1 and non-empty l2 
      can never be reached.
     therefore, for the front queue to reduce while elements exist in the rear, the front 
     _must_ have another element *) 
  | frel2_reduce h1 t1 l2 t3:  
    length t1 > 0 -> 
    fifo_rel2 t1 l2 t3 ->  fifo_rel2 (h1::t1) l2 (h1::t3)
  .

Arguments frel2_empty {X}.
Arguments frel2_head {X}.
Arguments frel2_reduce_swap {X}.
Arguments frel2_reduce_head {X}.
Arguments frel2_reduce {X}.

(* Depending on your approach, you may find you can nearly copy paste these proofs from the last section *)
Theorem fifo_rel2_head_eq {X: Type}: forall l1 l3 : list X, fifo_rel2 l1 [] l3 <-> l1 = l3.
Proof.
  split.
  {
    intros.
    generalize dependent l3.
    induction l1.
    {
      intros.
      inversion H.
      reflexivity.
      reflexivity.
    }
    {
      intros.
      inversion H.
      reflexivity.
      {
        apply IHl1 in H1.
        rewrite H1.
        reflexivity.
      }
      {
        simpl in H4.
        inversion H4.
        reflexivity.
        reflexivity.
      }
      {
        apply IHl1 in H5.
        rewrite H5.
        reflexivity.
      }
    }
  }
  {
    generalize dependent l1.
    induction l3.
    intros. rewrite H. apply frel2_empty.
    intros.
    rewrite H. apply frel2_head.
  }
Qed.

(* Depending on your approach, you may find you can nearly copy paste these proofs from the last section *)
Theorem fifo_rel2_if {X: Type}: forall l1 l2 l3: list X, fifo_rel2 l1 l2 l3 -> fifo_unwrap (Queue(l1,l2)) = l3.
Proof.
  intros.
  induction H.
  simpl. reflexivity.
  rewrite fifo_unwrap_head_correct. reflexivity.
  simpl. apply fifo_rel2_head_eq. apply frel2_reduce_head. apply H.
  {
    simpl.
    destruct l2.
    inversion H.
    reflexivity.
    reflexivity.
    simpl.
    apply fifo_rel2_head_eq.
    apply frel2_reduce_head.
    simpl in H. apply H.
  }
  {
    simpl.
    destruct l2.
    apply fifo_rel2_head_eq.
    apply frel2_reduce_head.
    apply H0.
    apply app_reduce.
    unfold fifo_unwrap in IHfifo_rel2.
    destruct t1.
    inversion H0.
    apply IHfifo_rel2.
  }
Qed.

(* Instead of reduce_head_app, we try providing a fix point to resolve the lists *)
Fixpoint last_list {X: Type} (l: list X): list X :=
match l with
  | [] => []
  | h::[] => [h]
  | h::t => last_list t 
end.

(* Here's where I got stuck, these two 'ttt' theorems I sketched out can be used to prove the queue, but
I was unable to prove them
*)
Theorem ttt {X: Type}: forall (l1 l2 l3: list X), 
  fifo_rel2 (last_list l1) (l2) ((last_list l1) ++ l3) -> fifo_rel2 l1 l2 (l1 ++ l3).
  Admitted.

Theorem ttt2 {X: Type}: forall (l1 l2 l3: list X), 
  length l1 > 0 -> fifo_rel2 (rev l2) [] l3 -> fifo_rel2 (last_list l1) (l2) ((last_list l1) ++ l3).
  Admitted.

(* An even cooler way to prove the queue that the one we already did, provided you can figured out the ttt's *)
Theorem fifo_push_pop_all_correct_better {X: Type}: forall l1 l2 l3 : list X, 
  length l1 > 0 ->
  fifo_unwrap(fifo_push_all l3 (Queue(l1,l2))) = l1 ++ (rev l2) ++ l3.
  Proof.
  induction l1.
  {
    intros.
    inversion H.
  }
  {
    intros.
    unfold fifo_push_all.
    destruct l3 eqn:El3.
    {
    apply fifo_rel2_if.
    rewrite app_nil_r.
    apply ttt.
    apply ttt2.
    apply H.
    apply frel2_head.
    }
    {
      apply fifo_rel2_if.
      rewrite <- El3.
      simpl.
      change ((a :: (l1 ++ ((rev l2) ++ l3)))) with ((a :: l1) ++ ((rev l2) ++ l3)).
      apply ttt.
      apply ttt2.
      apply H.
      rewrite rev_app_distr.
      rewrite rev_involutive.
      apply frel2_head.
    }
  }
  Qed.

