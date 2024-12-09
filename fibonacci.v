(*
  Sanjay Adhith
  <sanjay.adhith@u.nus.edu.sg>
  November 2024
  Singapore
 *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Nat Arith Bool.
    
(* *** *)

(* The Fibonacci implementation we want to work with *)

Fixpoint fib (n : nat) : nat :=
  match n with
    0 =>
    0
  | S n' =>
    match n' with
      0 =>
      1
    | S n'' =>
      fib n' + fib n''
    end
  end.

Lemma fold_unfold_fib_O :
  fib O =
    0.
Proof.
  fold_unfold_tactic fib.
Qed.

Lemma fold_unfold_fib_S :
  forall n' : nat,
    fib (S n') =
    match n' with
      0 =>
      1
    | S n'' =>
      fib n' + fib n''
    end.
Proof.
  fold_unfold_tactic fib.
Qed.


Corollary fold_unfold_fib_SO :
  fib 1 = 1.

Proof.
  fold_unfold_tactic fib.
Qed.
  
Corollary fold_unfold_fib_SSS :
  forall n : nat,
    fib (S (S (S n))) = 2 * fib (S n) + fib n.

Proof.
  intros n.
  rewrite ->2 fold_unfold_fib_S.
  ring.
Qed.

  
(* Okay, so I want to find out when F_n is even, and
   when F_n is odd. *)

Compute fib 1.
(* 1 - odd*)
Compute fib 2.
(* 1 - odd*)
Compute fib 3.
(* 2 - even*)
Compute fib 4.
(* 3 - odd*)
Compute fib 5.
(* 5 - odd*)
Compute fib 6.
(* 8 - even*)
Compute fib 7.
(* 13 - odd*)
Compute fib 8.
(* 21 - odd*)
Compute fib 9.
(* 34 - even*)

(*

   Mabye some tabular visualisation will help. Below,
   'o' refers to an odd number while 'e' refers to an
    even number.

        F_n 1  1  2  3  5  8  13 21 34
          n 1  2  3  4  5  6  7  8  9
     parity o  o  e  o  o  e  o  o  e

   Okay. The pattern that is emerging is that if
   n is a multiple of three, then F_n must be even.

   So I would formally state that F_n is even iff
   n is a multiple of three.

   For the backwards implication, I could try to
   first prove the auxillary lemma that

   F_nk is a multiple of F_n by induction and
   then be done with it.

   The forwards implication is not easy.
   and I don't have a proof sketch yet. 
*)

(* General Purpose Lemmas *)

Lemma twice :
  forall x : nat,
    x + x = 2 * x.
Proof.
  intro x.
  ring.
Qed.

Lemma twice_S :
  forall n : nat,
    S (S (2 * n)) = 2 * S n.
Proof.
  intro n.
  ring.
Qed.

Lemma thrice_S :
  forall n : nat,
    S (S (S (3 * n))) = 3 * S n.
Proof.
  intro n.
  ring.
Qed.

Lemma about_sum_of_even_numbers:
  forall a b c : nat,
    2*a + b = 2*c ->
      exists k : nat,
          b = 2 * k.
Proof.
  intros a b.
  induction a as [ | a' IHa']; intros c H_c.

  * rewrite -> Nat.mul_0_r in H_c.
    rewrite -> Nat.add_0_l in H_c.
    rewrite -> H_c.
    exists c.
    reflexivity.

  * case c as [ | c'].

    - rewrite -> Nat.mul_0_r in H_c.
      discriminate.

    - assert (H : forall a b : nat,
                 2 * S a' + b =
                 S (S (2 * a' + b))).
      {
        intros x y.
        ring.
      }
      rewrite -> (H a' b) in H_c.
      clear H.
      assert (H : forall c : nat,
                 2 * S c =
                   S (S (2 * c))).
      {
        intros c.
        ring.
      }
      rewrite -> H in H_c.
      injection H_c.
      intros H_c'.
      exact (IHa' c' H_c').
Qed.

Lemma about_sum_to_odd_numbers:
  forall a b c : nat,
    2*a + b = S(2*c) ->
      exists k : nat,
          b = S(2 * k).

Proof.
  intros a b.
  induction a as [ | a' IHa']; intros c H_c.

  * exists c.
    rewrite <- H_c.
    rewrite -> Nat.mul_0_r.
    rewrite -> Nat.add_0_l.
    reflexivity.

  * case c as [ | c'].

  - rewrite <- twice_S in H_c.
    discriminate H_c.

  - assert (H : forall a b : nat,
                 2 * S a' + b =
                 S (S (2 * a' + b))).
      {
        intros x y.
        ring.
      }
   rewrite -> (H a' b) in H_c.
   injection H_c as H_c.

   rewrite ->2 Nat.add_0_r in H_c.
   rewrite -> twice in H_c.
   assert (J: forall a : nat,
              a + S a = S (2 * a)).
   {
     intros a.
     ring.
   }
   rewrite -> J in H_c.
   exact (IHa' c' H_c).
Qed.
    
Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall k : nat, P k -> P (S k) -> P (S (S k))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  assert (H_both : P n /\ P (S n)).
  { induction n as [ | n' [IHn' IHSn']].
    - Check (conj H_P0 H_P1).
      exact (conj H_P0 H_P1).
    - Check (H_PSS n' IHn' IHSn').
      Check (conj IHSn' (H_PSS n' IHn' IHSn')).
      exact (conj IHSn' (H_PSS n' IHn' IHSn')).
  }
  destruct H_both as [ly _].
  exact ly.
Qed.  

Lemma nat_ind3 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n)) -> P (S (S (S n)))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_P2 H_PSSS n.
  assert (H3 : P n /\ P (S n) /\ P (S (S n))).
  { induction n as [ | n' [IHn' [IHSn' IHSSn']]].
    - exact (conj H_P0 (conj H_P1 H_P2)).
    - Check (H_PSSS n' IHn' IHSn' IHSSn').
      exact (conj IHSn' (conj IHSSn' (H_PSSS n' IHn' IHSn' IHSSn'))).
  }
  destruct H3 as [ly _].
  exact ly.
Qed.

Lemma nat_ind33 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 ->
    (forall n : nat, P n -> P (S (S (S n)))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_P2 H_PSSS n.
  assert (H3 : P n /\ P (S n) /\ P (S (S n))).
  { induction n as [ | n' [IHn' [IHSn' IHSSn']]].
    - exact (conj H_P0 (conj H_P1 H_P2)).
    - Check (H_PSSS n' IHn').
      exact (conj IHSn' (conj IHSSn' (H_PSSS n' IHn'))).
  }
  destruct H3 as [amundo _].
  exact amundo.
Qed.

Lemma nat3_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat,
      P n -> P (S (S (S n)))) ->
      forall n : nat,
        P (3 * n).

Proof.
  intros P H_P0 H_PSSS n.
  - assert (H3 : P (3 * n) /\ P (S (S (S (3 * n))))).
    {
      induction n as [ | n'  IHSSn'].
      rewrite -> Nat.mul_0_r.
      * exact  (conj H_P0
                     (H_PSSS 0 H_P0)).
      * destruct IHSSn' as [_ IHSSn'].
        rewrite -> thrice_S in IHSSn'.
        exact (conj IHSSn'
                    (H_PSSS (3 * S n') IHSSn')).
    }
    destruct H3 as [emente  _].
    exact emente.
Qed.

Lemma periodicity_of_even:
    forall n k2 : nat,
          fib (3*n) = 2 * k2 ->
      (exists k3 : nat,
          fib (S (S (S (3*n)))) = 2 * k3).
Proof.
  intros n k2 H_k2.
  rewrite -> fold_unfold_fib_S.
  rewrite -> fold_unfold_fib_S.
  rewrite -> H_k2.
  Search (_ + _ + _ = _ + _ + _).
  rewrite -> Nat.add_shuffle0.
  rewrite -> twice.
  rewrite <- Nat.mul_add_distr_l.
  exists (fib (S (3 * n)) + k2).
  reflexivity.
Qed.

(* *** *)

(*
  Let me proving something easier,
  if I start with something even, then
  moving three steps down the line
  brings me somewhere even.
*)
     
Lemma shifting_by_threes:
  forall n k2: nat,
    S (S (S n)) = 3 * k2 ->
    (exists k3 : nat,
        n = 3 * k3).

Proof.
  intros n [ | k2'] H_k2.

  - rewrite -> Nat.mul_0_r in H_k2.
    discriminate.

  - rewrite <- thrice_S in H_k2.
    injection H_k2 as H_k2'.
    exists k2'.
    rewrite -> H_k2'.
    ring.
Qed.    
    
Lemma about_the_backwards_implication:
  forall n k3: nat,
      n = 3 * k3 ->
  exists k2 : nat,
      fib n = 2 * k2.
Proof.
  (* First proof but using the refined induction principle *)
  intros n.
  induction n as [ | | | n'' IHn' IHSn'' IHSSn''] using nat_ind3.

  * intros k3 H_O.
    exists 0.
    exact fold_unfold_fib_O.

  * case k3 as [ | k3'].

    - intros H_absurd.
      rewrite -> Nat.mul_0_r in H_absurd.
      discriminate.

    - intros H_absurd.
      rewrite <- thrice_S in H_absurd.
      discriminate.
      
  * case k3 as [ | k3'].

    - intros H_absurd.
      rewrite -> Nat.mul_0_r in H_absurd.
      discriminate.

    - intros H_absurd.
      rewrite <- thrice_S in H_absurd.
      discriminate.

  * rewrite -> fold_unfold_fib_SSS.
    intros k3 H_up_three.
    Check shifting_by_threes.
    pose (shifting_by_threes n'' k3 H_up_three) as H_down_three.
    destruct H_down_three as [k3' H_down_three].
    pose (IHn' k3' H_down_three) as IHn'_down.
    destruct IHn'_down as [k2' IHn'_down].
    rewrite -> IHn'_down.
    exists (fib (S n'') + k2').
    rewrite -> Nat.mul_add_distr_l.
    reflexivity.
  
  Restart.
  (* We can refine the induction principle even further,

     Notice that we only wish to induct upon the set

     {0,3,6,9...}

     As Prof Danvy said in the email exchange, we can proceed
     with the proof even without the induction tactic.

     So we proceed with our own hand-rolled induction.
  *)
   intros n k3 H_n.
   rewrite -> H_n.
   clear n H_n.

   Check (nat3_ind (fun n => exists k2 : nat, fib n = 2 * k2)).
   (* First we want to show that the zero case holds *)
   Check (ex_intro
            (fun k2 : nat => fib 0 = 2 * k2)
            0).
   (* wanted: fib 0 = 2 * 0 *)
   assert (wanted_0 :
              fib 0 = 2 * 0).
   {
     rewrite -> fold_unfold_fib_O.
     simpl (2 * 0).
     reflexivity.
   }
   Check (ex_intro
            (fun k2 : nat => fib 0 = 2 * k2)
            0
            wanted_0).
   (* *** *)
   Check (nat3_ind
            (fun n => exists k2 : nat, fib n = 2 * k2)
            (ex_intro
               (fun k2 : nat => fib 0 = 2 * k2)
               0
               wanted_0)).

   (* Top, so the next thing that we want to show is: *)
   revert k3.
   apply (nat3_ind
            (fun n => exists k2 : nat, fib n = 2 * k2)
            (ex_intro
               (fun k2 : nat => fib 0 = 2 * k2)
               0
               wanted_0)).

  * intros n [k2 H_k2].
    rewrite -> fold_unfold_fib_SSS.
    rewrite -> H_k2.
    rewrite <- Nat.mul_add_distr_l.
    exists (fib (S n) + k2).
    reflexivity.

    (* Second proof with nat_ind2 *)
    Restart.

    intros n m H_m.
    rewrite -> H_m.
    clear n H_m.
    
    induction m as [ | | m'' _[q' IHSm'']] using nat_ind2.

    * exists O.
      exact fold_unfold_fib_O.
      
    * rewrite <- thrice_S.
      rewrite -> fold_unfold_fib_SSS.
      rewrite -> Nat.mul_0_r.
      rewrite -> fold_unfold_fib_O.
      rewrite -> fold_unfold_fib_S.
      rewrite -> Nat.mul_1_r.
      rewrite -> Nat.add_0_r.
      exists 1.
      rewrite -> Nat.mul_1_r.
      reflexivity.

    * rewrite <- thrice_S.
      rewrite -> fold_unfold_fib_SSS.
      rewrite -> IHSm''.
      rewrite <- Nat.mul_add_distr_l.
      exists (fib (S (3 * S m'')) + q').
      reflexivity.
Qed.      
    
Lemma about_the_forwards_implication:
  forall n k2 : nat,
      fib n = 2 * k2 ->
    exists k3 : nat,
      n = 3 * k3.
Proof.
  (* First proof using the cycles by three trick,
     but using the nat_ind33 induction principle.
   *)
  intros n.
  
  induction n as [ | | | n'' IHn' IHSn'' IHSSm''] using nat_ind33;   intros k2 H_k2.

  * exists 0.
    ring.

  * rewrite -> fold_unfold_fib_S in H_k2.
    case k2 as [ | k2'].

   - rewrite -> Nat.mul_0_r in H_k2.
     discriminate H_k2.

   - rewrite <- twice_S in H_k2.
     discriminate H_k2.

  * rewrite ->2 fold_unfold_fib_S in H_k2.
    rewrite -> fold_unfold_fib_O in H_k2.
    rewrite -> Nat.add_0_r in H_k2.
    case k2 as [ | k2'].

   - rewrite -> Nat.mul_0_r in H_k2.
     discriminate H_k2.

   - rewrite <- twice_S in H_k2.
     discriminate H_k2.

  * rewrite ->2 fold_unfold_fib_S in H_k2.
    rewrite -> Nat.add_shuffle0 in H_k2.
    rewrite -> twice in H_k2.
    pose (about_sum_of_even_numbers
             (fib (S n''))
             (fib n'')
             k2
             H_k2
          ) as H_n''.

    destruct H_n'' as [k1 H_n''].
    pose (IHn' k1 H_n'') as H_n''_is_multiple_of_3.
    destruct H_n''_is_multiple_of_3 as [k3' H_n''_is_multiple_of_3].

   - exists (S (k3')).
     rewrite -> H_n''_is_multiple_of_3.
     rewrite -> thrice_S.
     reflexivity.
Qed.     
     
         

(* I used exists on both sides for symmetry of
   the iff, but if this is bad, I will change
   it to a forall *)
     
Theorem parity_of_fibonacci_numbers:
  forall n : nat,
    (exists k2 : nat, fib n = 2 * k2) <-> (exists k3 : nat, n = 3 * k3).
      
Proof.
  intros n.
  split.

  * Check about_the_forwards_implication n.
    intros [k2 H_fib_even].
    exact (about_the_forwards_implication n k2 H_fib_even).
    
  * Check about_the_backwards_implication n.
    intros [k3 H_n_multiple_of_three].
    exact (about_the_backwards_implication n k3 H_n_multiple_of_three).
Qed.

Proposition odd_fibonacci_numbers :
    forall n : nat,
      (exists q : nat, fib n = S (2 * q)) <-> (exists m : nat, n = S (3 * m) \/ n = S (S (3 * m))).

Proof.
  intros n.
  split.

  * induction n as [ | | | n'' IHn' IHSn'' IHSSm''] using nat_ind3; intros [q H_q].

    + discriminate H_q.

    + rewrite -> fold_unfold_fib_S in H_q.
      case q as [ | q'].

      - exists 0.
        left.
        simpl.
        reflexivity.

      - rewrite <- twice_S in H_q.
        discriminate H_q.

    + rewrite -> fold_unfold_fib_S in H_q.
      case q as [ | q'].

      - exists 0.
        right.
        simpl.
        reflexivity.

      - rewrite <- twice_S in H_q.
        discriminate H_q.

    + rewrite -> fold_unfold_fib_SSS in H_q.
      Check (about_sum_to_odd_numbers
               (fib (S n''))
               (fib    n'')
               q
               H_q).
      Check (IHn' (about_sum_to_odd_numbers
                     (fib (S n''))
                     (fib    n'')
                     q
                     H_q)).
      destruct (IHn' (about_sum_to_odd_numbers
                        (fib (S n''))
                        (fib    n'')
                        q
                        H_q))
        as [m [H_m | H_m]].

      - rewrite -> H_m.
        rewrite -> thrice_S.
        exists (S m).
        left.
        reflexivity.

      - rewrite -> H_m.
        rewrite -> thrice_S.
        exists (S m).
        right.
        reflexivity.

  * intros [m H_m].
    destruct H_m as [L | R].
    + rewrite -> L.
      clear n L.
      induction m as [ | | m'' _[q' IHSm'']] using nat_ind2.

      - exists 0.
        simpl.
        reflexivity.

      - exists 1.
        simpl.
        reflexivity.

      - rewrite <- thrice_S.
        rewrite -> fold_unfold_fib_SSS.
        rewrite -> fold_unfold_fib_S.
        rewrite -> IHSm''.
        rewrite <- plus_n_Sm.
        rewrite <- Nat.mul_add_distr_l.
        exists (S (2 * q') + fib (3 * S m'') + q').
        ring.

   + rewrite -> R.
      clear n R.
      induction m as [ | | m'' _[q' IHSm'']] using nat_ind2.

      - exists 0.
        simpl.
        reflexivity.

      - exists 2.
        simpl.
        reflexivity.

      - rewrite <- thrice_S.
        rewrite -> fold_unfold_fib_SSS.
        rewrite -> fold_unfold_fib_S.
        rewrite -> IHSm''.
        rewrite <- plus_n_Sm.
        rewrite <- Nat.mul_add_distr_l.
        exists ((S (2 * q')) + (fib (S (3 * S m''))) + q').
        reflexivity.
Qed.

(* Oral Examination *)

(* but in actuality, we want to induct upon the set {fib 0, fib 3, fib 6, fib 9, ...}. *)

Lemma fib3_ind:
  forall P : nat -> Prop,
    P (fib 0) -> 
    (forall n : nat,
        P (fib n) -> P (fib (S (S (S n))))) ->
        forall n : nat,
          P (fib (3 * n)).

Proof.
  intros P H_P0 H_P n.
  induction n as [ | n' IHn'].
    
  * rewrite -> Nat.mul_0_r.
    exact H_P0.

  * Check thrice_S.
    rewrite <- thrice_S.
    Check (H_P (3 * n')).
    Check (H_P (3 * n') IHn').
    exact (H_P (3 * n') IHn').
Qed.    
  
Proposition foobar :
  forall n : nat,
    exists q : nat,
      fib (3 * n) = 2 * q.  

Proof.
  intros n.
  (* tCPA induction tactic does not play well with this
     custom induction principle. *)

  Check fib3_ind.
  Check (ex_intro
           (fun k2 : nat => fib 0 = 2 * k2)
           0).
  assert (wanted_0 :
           fib (3 * 0) = 2 * 0).
  {
    rewrite ->2 Nat.mul_0_r.
    rewrite -> fold_unfold_fib_O.
    reflexivity.
  }
  Check (ex_intro
           (fun k2 : nat => fib 0 = 2 * k2)
           0
           wanted_0
        ).
  Check (fib3_ind
           (fun n => exists k2 : nat, n = 2 * k2)
           ((ex_intro
               (fun k2 : nat => 0 = 2 * k2)
               0)
              wanted_0)).
  apply (fib3_ind
           (fun n => exists k2 : nat, n = 2 * k2)
           ((ex_intro
               (fun k2 : nat => 0 = 2 * k2)
               0)
              wanted_0)).
  intros m [k H_k].
  rewrite -> fold_unfold_fib_SSS.
  rewrite -> H_k.
  rewrite <- Nat.mul_add_distr_l.
  exists (fib (S m) + k).
  reflexivity.

  Restart.

  intros n.
  revert n.

  Check fib3_ind.
  Check (fib3_ind
           (fun m : nat => exists q : nat, m = 2 * q)).
  assert (wanted_0 :
           exists q : nat, fib 0 = 2 * q).
  {
    exists 0.
    compute.
    reflexivity.
  }
  Check (fib3_ind
           (fun m : nat => exists q : nat, m = 2 * q)
           wanted_0
        ).
  apply (fib3_ind
           (fun m : nat => exists q : nat, m = 2 * q)
           wanted_0
        ).
  intros n [q H_q].
  rewrite -> fold_unfold_fib_SSS.
  rewrite -> H_q.
  rewrite <- Nat.mul_add_distr_l.
  exists (fib (S n) + q).
  reflexivity.
Qed.  

Lemma nat2_ind:
  forall P : nat -> Prop,
    P (2 * 0) ->
    (forall n : nat,
        P (2 * n) -> P (S (S (2 * n)))) ->
    forall n : nat,
      P (2 * n).

Proof.
  intros P H_P0 H_P n.
  induction n as [ | n' IHn'].

  * exact H_P0.

  * rewrite <- twice_S.
    Check (H_P n').
    exact (H_P n' IHn').
Qed.

Lemma natS2_ind:
  forall P : nat -> Prop,
    P (S (2 * 0)) ->
    (forall n : nat,
        P (S (2 * n)) -> P (S (S (S (2 * n))))) ->
    forall n : nat,
      P (S (2 * n)).

Proof.
  intros P H_P0 H_P n.
  induction n as [ | n' IHn'].

  * exact H_P0.
  * rewrite <- twice_S.
    Check (H_P n').
    exact (H_P n' IHn').
Qed.

Proposition barfoo :
  forall n : nat,
    exists q : nat,
      2 * n = fib (3 * q).

Proof.
  Check (nat2_ind
           (fun en : nat => exists q : nat, en = fib (3 * q))
           
        ).
  assert (wanted_0 :
           exists q : nat, 2 * 0 = fib (3 * q)).
  {
    exists 0.
    compute.
    reflexivity.
  }    
  Check (nat2_ind
           (fun en : nat => exists q : nat, en = fib (3 * q))
           wanted_0
        ).
  apply (nat2_ind
           (fun en : nat => exists q : nat, en = fib (3 * q))
           wanted_0
        ).
  intros n [q' H_q'].
  Abort.

Lemma knuth_add:
  forall n m : nat,
    fib (n + (S m)) = fib (S m) * fib (S n) + fib m * fib n.

Proof.
  induction n using nat_ind2; intros m.

  * rewrite -> Nat.add_0_l.
    rewrite -> fold_unfold_fib_S.
    rewrite -> Nat.mul_1_r.
    rewrite -> fold_unfold_fib_O.
    rewrite -> Nat.mul_0_r.
    rewrite -> Nat.add_0_r.
    reflexivity.
    
  * rewrite ->fold_unfold_fib_S.
    simpl (fib 2).
    rewrite ->2 Nat.mul_1_r.
    reflexivity.

  * assert (H : forall n : nat,
               S (S n) + S m = S (S (n + S m))).
    {
      intros j.
      ring.
    }    
    rewrite -> H.
    clear H.
    rewrite -> fold_unfold_fib_S.
    rewrite -> IHn.
    assert (H: forall n : nat,
               S (n + (S m)) = n + (S (S m))).
    {
      intros j.
      ring.
    }
    rewrite -> H.
    rewrite -> IHn.
    rewrite -> fold_unfold_fib_S.
    rewrite -> (fold_unfold_fib_S (S (S n))).
    rewrite -> (fold_unfold_fib_S (S n)).
    ring.
Qed.    
    

Lemma knuth_times:
  forall n k : nat,
    exists m : nat,
    fib ((S n) * (S k)) = m * fib (S n).

Proof.
  intros n k.
  revert n.
  induction k as [ | n' IHn']; intros n.

  * exists 1.
    rewrite -> Nat.mul_1_r.
    rewrite -> Nat.mul_1_l.
    reflexivity.
    
  * assert (H: forall n k : nat,
               (S n * (S (S k)) =
               (S n) * (S k) + (S n))).
    {
      intros a b.
      ring.
    }
    rewrite -> H.
    rewrite -> knuth_add.
    destruct (IHn' n) as [m IHm].
    rewrite -> IHm.
    exists (fib (S (S n * S n')) + fib n * m).
    ring.
Qed.    
    
    
    
(* Polygonal Numbers *)

(* Properties of Sigma. *)

Fixpoint Sigma (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O =>
    f 0
  | S n' =>
    Sigma n' f + f n
  end.

Lemma fold_unfold_Sigma_O :
  forall (f : nat -> nat),
    Sigma 0 f =
      f 0.
Proof.
  fold_unfold_tactic Sigma.
Qed.

Lemma fold_unfold_Sigma_S :
  forall (n' : nat)
         (f : nat -> nat),
    Sigma (S n') f =
    Sigma n' f + f (S n').
Proof.
  fold_unfold_tactic Sigma.
Qed.

(* *** *)

(* Testing the theorem *)

Compute Sigma 2 (fun i : nat => i / 2).
(* 1 *)
Compute Sigma 4 (fun i : nat => i / 2).
(* 4 *)
Compute Sigma 6 (fun i : nat => i / 2).
(* 9 *)
Compute Sigma 8 (fun i : nat => i / 2).
(* 16 *)
Compute Sigma 10 (fun i : nat => i / 2).
(* 25 *)
Compute Sigma 12 (fun i : nat => i / 2).
(* 36 *)

Compute 10 + 10.

Lemma square_floors:
  forall n : nat,
    Sigma (2*n) (fun i : nat => i / 2) = n*n.

Proof.
  intros n.
  induction n as [ | n' IHn'].

  * rewrite -> Nat.mul_0_r.
    rewrite -> fold_unfold_Sigma_O.
    simpl.
    reflexivity.
    
  * rewrite <- twice_S.
    rewrite ->2 fold_unfold_Sigma_S.
    rewrite -> IHn'.

    assert (H: forall n : nat, S (S (2 * n)) = (1 + n)*2).
    {
      intros n.
      ring.
    }
    rewrite -> H.
    Search (_ * ( _) / _).
    rewrite -> (Nat.div_mul (1 + n') 2 (Nat.neq_succ_0 1)).

    Search ((_ + _) / _ ).
    rewrite <- Nat.add_1_l.
    rewrite -> (Nat.mul_comm 2 n').
    Search ((_ + _) / _ ).
    rewrite -> (Nat.div_add 1 n' 2 (Nat.neq_succ_0 1)).
    simpl (1/2).
    ring.
Qed.

Lemma odd_or_even:
  forall n : nat,
  exists m,
    (n = 2*m) \/ (n = S(2*m)).

Proof.
  intros n.
  induction n as [ | n' IHn'].

  * exists 0.
    left.
    ring.

  * destruct IHn' as [m [IHn'_e | IHn'_o]].
  + rewrite -> IHn'_e.
  - exists m.
    right.
    reflexivity.

    + rewrite -> IHn'_o.
      exists (S m).
      left.
      ring.
Qed.

(*
  Formal proof of a tAoCP exercise!
 *)

Lemma tAoCP:
  forall n : nat,
    Sigma n (fun i : nat => i / 2) = n*n / 4.

Proof.
  intros n.
  induction n as [ | n' IHn'].

  * compute.
    reflexivity.

  * destruct (odd_or_even n') as [m' [H_e | H_o]].

    + rewrite -> H_e.
      rewrite -> fold_unfold_Sigma_S.
      rewrite -> (square_floors m').
      rewrite <- Nat.add_1_r.
      assert (H: forall n : nat,
                 (1 + 2 * m') / 2 = m').
      {
        intros n.
        Search ((_ + _*_) / _).
        rewrite -> Nat.mul_comm.
        rewrite -> (Nat.div_add 1 m' 2 (Nat.neq_succ_0 1)).
        simpl (1/2).
        reflexivity.
      }
      rewrite -> (Nat.add_comm (2 * m') 1).
      rewrite -> (H m').
      clear H.
      assert (H : forall n : nat,
                 (1 + 2 * n) * (1 + 2 * n) =
                 1 + (n*n + n)*4).
      {
        intros n.
        ring.
      }
      rewrite -> (H m').
      Check Nat.div_add.
      rewrite -> (Nat.div_add _ _ 4 (Nat.neq_succ_0 3)).
      simpl (1/4).
      reflexivity.
      
    + rewrite -> H_o.
      rewrite -> twice_S.
      rewrite -> (square_floors (S m')).
      (*
        m*m + 2*m + 1 = (4 + 4*m' + 4*m*m) / 4
       *)
      assert (H: forall n : nat,
                 S n * S n = n*n + 2*n + 1).
      {
        intros n.
        ring.
      }
      rewrite -> H.
      clear H.
      assert (H: forall n : nat,
                 2 * S n * (2 * S n) = (n*n + 2*n + 1) * 4).
      {
        intros n.
        ring.
      }
      rewrite -> H.
      Search (_ * _ / _).
      rewrite -> (Nat.div_mul _ 4 (Nat.neq_succ_0 3)).
      reflexivity.
Qed.

Lemma pentagonal_floors:
  forall n : nat,
    Sigma (3*n) (fun i : nat => i / 3) = (3*n*n - n) / 2.

Proof.
  intros n.
  induction n.

  * admit.

  * rewrite <- thrice_S.
    rewrite ->3 fold_unfold_Sigma_S.
    rewrite -> IHn.
    (* Arithmetic. *)
    
    

    
(* Testing the theorem *)

Compute Sigma (3*1) (fun i : nat => i / 3).
(* 1 *)
Compute Sigma (3*2) (fun i : nat => i / 3).
(* 5 *)
Compute Sigma (3*3) (fun i : nat => i / 3).
(* 12 *)
Compute Sigma (3*4) (fun i : nat => i / 3).
(* 22 *)
Compute Sigma (3*5) (fun i : nat => i / 3).
(* 35 *)
Compute Sigma (3*6) (fun i : nat => i / 3).
(* 51 *)
Compute Sigma (3*7) (fun i : nat => i / 3).
(* 70 *)
