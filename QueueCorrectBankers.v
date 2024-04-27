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


(*
Let's try to implement this concept in Coq.
We'll need a new data structure to represent a FIFO queue 
*)
  
Inductive fifo_am (X: Type): Type :=
  (* The empty queue *)
  | f_empty
  | Queue (l : list X * list X) (points : nat)
  .

Arguments Queue {X}.
Arguments f_empty {X}.

Check (Queue ([1;2],[4;3]) 2).

(* Taking the head does not change anything *)
Definition fifo_am_hd {X: Type} (q: fifo_am X) : list X :=
  match q with
  | Queue (h1::t1, l2) n => [h1]
  | _ => nil
  end.

Compute fifo_am_hd (Queue ([1;2],[4;3]) 1).
Compute fifo_am_hd (Queue ([2],[4;3]) 1).

(* Pushing a single element onto the Queue is straightforward *)
Definition fifo_am_push {X: Type} (e: X) (q: fifo_am X) : fifo_am X :=
  match q with
  (* The first element pushed onto an empty queue must go in the front to satisfy the invariant *)
  | f_empty => Queue ([e],[]) O
  (* Otherwise, add it to the rear list *)
  | Queue (l1,l2) n => Queue (l1,e::l2) (S n)
  end.

Compute fifo_am_push 5 (f_empty).
Compute fifo_am_push 4 (fifo_am_push 5 (f_empty)).
Compute fifo_am_push 3 (fifo_am_push 4 (fifo_am_push 5 (f_empty))).

(* Attempted, couldn't get coq to unpack it in a meaningful manner.
Fixpoint fifo_am_push_all {X: Type} (l : list X) (q: fifo_am X): fifo_am X :=
  match l with
  | nil => q
  | h::t => fifo_am_push_all t (fifo_am_push h q)
  end.
*)

Definition fifo_am_push_all {X: Type} (l: list X) (q : fifo_am X) : fifo_am X :=
  match l with
  | [] => q
  | h::t => match q with
            (* If pushing onto an empty list, take the first item to 
            push and move it to the front list *)
            | f_empty => Queue ([h],(rev t)) (length t)
            (* Otherwise just append each item in the order specified *)
            | Queue(l1,l2) budget => Queue(l1, (rev l)++l2) (budget + length l)
            end
  end.
Compute fifo_am_push_all [1;2;3;4;5] f_empty.


Fixpoint fifo_am_reverse_fuel {X: Type} (q: fifo_am X) (fuel : nat) : fifo_am X :=
  match q with
  | f_empty => f_empty
  | Queue(_, []) _ => q  
  | Queue(l1, h::t) (S budget) => match fuel with
                            | S(n') =>  fifo_am_reverse_fuel (Queue ((l1++[h]), t) budget) n'
                            | O => q
                            end
  | _ => q
  end.

Print fifo_am_reverse_fuel.

Definition fifo_am_reverse {X: Type} (q: fifo_am X) : fifo_am X :=
  match q with
  | f_empty => f_empty
  | Queue(_,_) n => fifo_am_reverse_fuel q n
  end.

(* Just enough *)
Compute fifo_am_reverse (Queue ([], 5 :: (4 :: [3; 2])) 4).
(* Not enough credits *)
Compute fifo_am_reverse (Queue ([], [3; 4]) 1).

Fixpoint rev_fuel {X: Type} (l : list X) (fuel : nat): list X :=
  match fuel with
  | S(n) => match l with
            | h::t => (rev_fuel t n) ++ [h]
            | nil => []
            end
  | O => []
  end.

Compute rev_fuel [1;2;3;4] 4.

Definition fifo_am_tl {X: Type} (q: fifo_am X) : fifo_am X :=
  match q with
  | f_empty => f_empty
  | Queue (h1::[], []) n => f_empty
  (* Last element of the head reached, reverse rear list *)
  | Queue (h1::[], l2) n => Queue ((rev_fuel l2 n),[]) (n-length l2)
  | Queue (h1::t1, l2) n => Queue (t1,l2) n
  | Queue ([], l2) n => Queue([], l2) n
  end.
(*match (rev l2) with 
                            | h::t => fifo_am_reverse_fuel (Queue([h], t) n) n
                            | nil => q
                            end*)
Check (Queue ([6;5;4], [1;2;3]) 3).
Compute fifo_am_tl (Queue ([6;5;4], [1;2;3]) 3).
Compute fifo_am_tl (fifo_am_tl (Queue ([6;5;4], [1;2;3]) 3)).
Compute fifo_am_tl (fifo_am_tl (fifo_am_tl (Queue ([6;5;4], [1;2;3]) 3))).
Compute fifo_am_tl (fifo_am_tl (fifo_am_tl (Queue ([6;5;4], [1;2;3]) 2))).

Fixpoint fifo_am_unwrap_fuel {X: Type} (q: fifo_am X) (fuel: nat): list X :=
  match q with
  | f_empty => []
  (* This time we return the front list in order *)
  | Queue(l1,nil) n => l1
  (* Notice that we moved the head call to the left *)
  | Queue (l1, _) _ => match fuel with
                        | O => []
                        | S(n) => (fifo_am_hd q) ++ (fifo_am_unwrap_fuel (fifo_am_tl q) n)
                      end

  end.

(* Since we haven't changed how head and tail work, this requires no modifications. *)
Definition fifo_am_unwrap {X: Type} (q: fifo_am X): list X :=
  match q with
  | f_empty => []
  | Queue(l1,l2) _ => (fifo_am_unwrap_fuel q (length l1 + length l2))
  end.

Compute fifo_am_unwrap( fifo_am_push_all [1;2;3;4;5] f_empty).
Compute fifo_am_unwrap( Queue ([1], [5; 4; 3; 2]) 3).
Compute fifo_am_unwrap( Queue ([2;3], [1]) 0).


Theorem fifo_am_unwrap_head_correct {X: Type}: forall (l : list X) n, fifo_am_unwrap (Queue(l,[]) n) = l.
  Proof.
    intros.
    simpl.
    rewrite Nat.add_0_r.
    destruct l.
    simpl. reflexivity.
    simpl. reflexivity.
  Qed.

Theorem fifo_am_unwrap_fuel_head_correct {X: Type}: forall (l : list X) n fuel, fifo_am_unwrap_fuel (Queue(l,[]) n) fuel = l.
  Proof.
    intros.
    destruct fuel.
    simpl. reflexivity.
    simpl. reflexivity.
  Qed.

Theorem fifo_am_unwrap_one_correct {X: Type}: forall (h : X) (t l2 : list X) n, 
length t > 0  -> fifo_am_unwrap (Queue((h::t),l2) n) = h::(fifo_am_unwrap (Queue(t,l2) n)).
Proof.
  induction l2.
  intros. rewrite fifo_am_unwrap_head_correct. rewrite fifo_am_unwrap_head_correct. reflexivity.
  destruct t.
  intros. inversion H.
  intros. apply IHl2 with (n := n) in H.
  simpl. destruct n eqn:En.
  reflexivity.
  (* thank you auto for being able to read what was going on in there *)
  auto.
Qed.

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

Lemma len_0_nil {X: Type}: forall l : list X, length l <= 0 -> l = [].
intros.
induction l.
reflexivity.
inversion H.
Qed.

Lemma S_reduce: forall n m, (S n) <= (S m) -> n <= m.
Proof.
  lia.
Qed.

Theorem rev_fuel_sufficient {X: Type}: forall (l: list X) n, 
length l <= n -> rev_fuel l n = rev l.
  Proof.
    induction l.
    intros.
    simpl.
    destruct n.
    reflexivity.
    reflexivity.
    intros.
    simpl.
    destruct n.
    inversion H.
    simpl in H.
    apply S_reduce in H.
    apply IHl in H.
    rewrite H.
    reflexivity.
  Qed.

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

Print rev.
Inductive fifo_rel_am {X: Type}: list X -> list X -> list X -> nat -> Prop :=
  | frel_am_empty n : fifo_rel_am nil nil nil n
  | frel_am_head l n : fifo_rel_am l nil l n
  | frel_am_reduce_head h t1 t3 n : fifo_rel_am t1 nil t3 n -> fifo_rel_am (h::t1) nil (h::t3) n
  | frel_am_reduce_swap h1 l2 t3 n: length l2 <= n -> fifo_rel_am (rev l2) [] t3 (n - (length l2)) -> 
      fifo_rel_am [h1] l2 (h1::t3) n
  | frel_am_reduce h1 t1 l2 t3 n: 
    length t1 > 0 -> 
    fifo_rel_am t1 l2 t3 n ->  fifo_rel_am (h1::t1) l2 (h1::t3) n
  | frel_am_reduce_app l1 l2 l3 n : length l2 <= n -> length l1 > 0 -> fifo_rel_am (rev l2) [] l3 (n-length l2) -> 
    fifo_rel_am l1 l2 (l1 ++ l3) n
  .

Compute fifo_am_push_all [1;2;3;4;5] f_empty.

Theorem test_frel_am1: fifo_rel_am [1] [5;4;3;2] [1;2;3;4;5] 4.
Proof.
apply frel_am_reduce_swap.
simpl. lia.
apply frel_am_head.
Qed.
(* valid proof when using frel_am_reduce_app *)
Theorem fifo_am_rel_head_eq {X: Type}: forall (l1 l3 : list X) n, fifo_rel_am l1 [] l3 n <-> l1 = l3.
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
      reflexivity.
      inversion H1.
    }
      inversion H1.
      intros.
      inversion H.
      reflexivity.
      apply IHl1 in H1. rewrite H1. reflexivity.
      simpl in H6. inversion H6. reflexivity. reflexivity. inversion H8.
      apply IHl1 in H6. rewrite H6. reflexivity.
      {
        simpl in H2. inversion H2.
        rewrite app_nil_r. reflexivity.
        rewrite app_nil_r. reflexivity.
        inversion H8.
      }
  }
  {
    generalize dependent l1.
    induction l3.
    intros. rewrite H. apply frel_am_empty.
    intros.
    rewrite H. apply frel_am_head.
  }
Qed.

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
Theorem fifo_am_head_swap {X: Type}: forall (x a : X) (l1 l2 : list X) n,
  length l2 <= n ->
  (fifo_am_unwrap (Queue (x :: (a :: l1), l2) n)) = ((x :: (a :: l1)) ++ (rev l2)) ->
  (fifo_am_unwrap (Queue (a :: (x :: l1), l2) n)) = ((a :: (x :: l1)) ++ (rev l2)).
Proof.
  induction l1.
  intros. rewrite fifo_am_unwrap_one_correct. apply app_reduce.
  destruct l2. simpl. reflexivity.
  simpl. apply app_reduce.
  destruct n.
  apply len_0_nil in H.
  change ((rev l2) ++ [x0]) with ((rev (x0::l2))).
  rewrite H. reflexivity.
  rewrite rev_fuel_sufficient.
  reflexivity.
  simpl in H.
  apply S_reduce in H.
  apply H.
  simpl. lia.
  intros. rewrite fifo_am_unwrap_one_correct. rewrite <- app_comm_cons. apply app_reduce.
  rewrite fifo_am_unwrap_one_correct. rewrite <- app_comm_cons. apply app_reduce.
  rewrite fifo_am_unwrap_one_correct in H0. rewrite <- app_comm_cons in H0. apply app_reduce in H0.
  rewrite fifo_am_unwrap_one_correct in H0. rewrite <- app_comm_cons in H0. apply app_reduce in H0.
  apply H0.
  simpl. lia.
  simpl. lia.
  simpl. lia.
  simpl. lia.
Qed.

Theorem fifo_am_rel_if {X: Type}: forall (l1 l2 l3: list X) n, fifo_rel_am l1 l2 l3 n -> fifo_am_unwrap (Queue(l1,l2) n) = l3.
Proof.
  intros.
  induction H.
  simpl. reflexivity.
  rewrite fifo_am_unwrap_head_correct. reflexivity.
  simpl. rewrite fifo_am_unwrap_head_correct in IHfifo_rel_am. rewrite IHfifo_rel_am. reflexivity.
  simpl in IHfifo_rel_am.
  destruct l2.
  apply fifo_am_rel_head_eq in H0. rewrite <- H0. reflexivity.
  destruct n.
  inversion H.
  unfold fifo_am_unwrap.
  simpl.
  apply app_reduce.
  rewrite rev_fuel_sufficient.
  apply fifo_am_rel_head_eq in H0.
  rewrite <- H0. simpl. reflexivity.
  simpl in H. apply S_reduce in H.
  apply H.
  rewrite fifo_am_unwrap_one_correct.
  apply app_reduce.
  apply IHfifo_rel_am.
  apply H.
   {
    destruct l1.
    inversion H0.
    
    induction l1.
    simpl. destruct l2. 
    simpl in IHfifo_rel_am. rewrite <- IHfifo_rel_am. reflexivity.
    {
    apply app_reduce. simpl in IHfifo_rel_am. rewrite Nat.add_0_r in IHfifo_rel_am. 
    change ((rev l2)++[x0]) with (rev (x0 :: l2)) in IHfifo_rel_am. 
    rewrite rev_length in IHfifo_rel_am.
    change (Datatypes.length (x0 :: l2)) with (S(Datatypes.length (l2))). 
    change (Datatypes.length (x0 :: l2)) with (S(Datatypes.length (l2))) in IHfifo_rel_am. 
    rewrite rev_fuel_sufficient. 
    apply IHfifo_rel_am.
    apply H.
    }
    intros.
    apply two_big_either in H0.
    destruct H0.
    apply fifo_am_rel_head_eq in H1.
    rewrite <- H1.
    apply fifo_am_head_swap.
    apply H.
    rewrite fifo_am_unwrap_one_correct. rewrite <- app_comm_cons. apply app_reduce.
    apply IHl1 in H0.
    rewrite <- H1 in H0.
    apply H0.
    simpl. lia.
  }
Qed.



Search "length".

Theorem fifo_am_push_unwrap_empty_correct {X: Type}: forall l: list X, 
  fifo_am_unwrap(fifo_am_push_all l f_empty) = l.
  Proof.
    induction l.
    reflexivity.
    unfold fifo_am_push_all.
    apply fifo_am_rel_if.
    apply frel_am_reduce_swap.
    rewrite rev_length. lia.
    rewrite rev_involutive.
    apply frel_am_head.
  Qed.

Theorem fifo_am_push_unwrap_all_correct {X: Type}: forall l1 l2 l3 : list X, 
  length l1 > 0 ->
  fifo_am_unwrap(fifo_am_push_all l3 (Queue(l1,l2) (length l2))) = l1 ++ (rev l2) ++ l3.
  Proof.
  induction l1.
  {
    intros.
    inversion H.
  }
  {
    intros.
    unfold fifo_am_push_all.
    destruct l3 eqn:El3.
    {
    apply fifo_am_rel_if.
    rewrite app_nil_r.
    apply frel_am_reduce_app.
    simpl. lia.
    apply H.
    apply frel_am_head.
    }
    {
      apply fifo_am_rel_if.
      rewrite <- El3.
      simpl.
      change ((a :: (l1 ++ ((rev l2) ++ l3)))) with ((a :: l1) ++ ((rev l2) ++ l3)).
      apply frel_am_reduce_app.
      {
      simpl.
      rewrite app_length.
      rewrite rev_length. lia.
      }
      apply H.
      rewrite rev_app_distr.
      rewrite rev_involutive.
      apply frel_am_head.
    }
  }
  Qed.