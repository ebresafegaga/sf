Inductive day : Type  := 
  | monday
  | tuesday 
  | wednesday
  | thursday
  | friday 
  | saturday 
  | sunday.
  
 Definition next_weekday (d:day) : day := 
   match d with 
   | monday => tuesday
   | tuesday => wednesday
   | wednesday => thursday
   | thursday => friday
   | friday => saturday
   | saturday => monday
   | sunday => monday
   end.   
   
 Compute (next_weekday friday).
 
 Compute (next_weekday (next_weekday saturday)).
 
 Example text_next_weekday: 
   (next_weekday (next_weekday saturday)) = tuesday.
   
   
Proof. simpl. reflexivity. Qed.


(*Inductive bool : Type := 
  | true 
  | false.
*)
  
Definition negb (b:bool) : bool := 
  match b with 
  | true => false 
  | false => true
  end.
  
  
 Definition andb (b1:bool) (b2:bool) : bool := 
   match b1 with 
   | true => b2 
   | false => false
   end.
   
Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true 
  | false => b2
  end.
  
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.
  
  
 Example negb_equal: negb true = negb' true.
Proof. simpl. reflexivity. Qed.


(* Excercise *)

Definition nandb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => negb b2
  | false => true
  end.
  
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.


Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.


Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.



Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := 
  match b1 with 
  | true => andb b2 b3 
  | false => false
  end.
  
  
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.


Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.


Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check negb.


Inductive rgb : Type := 
  | red
  | green 
  | blue. 
  
Inductive color : Type := 
  | black 
  | white 
  | primary (p : rgb).
 
 Check (primary red).
 
 
 Definition monochrome (c : color) : bool := 
   match c with 
   | black => true 
   | white => true 
   | primary p => false 
   end.

Check monochrome.
  
  
Definition isred (c : color) : bool :=
  match c with 
  | black => false  
  | white => false 
  | primary red => true 
  | primary _ => false
  end.
  
Check isred.


Module Playground. 
  Definition myblue : rgb := blue.
End Playground.

Definition myblue : bool := true.

Check Playground.myblue.
Check myblue.


Module TuplePlayground.

Inductive bit : Type := 
  | B0 
  | B1.
  
Inductive nybble : Type := 
  | bits (b0 b1 b2 b3 : bit).
  
  
Check (bits B1 B0 B1 B0)
        : nybble.
        
        
Definition all_zero (nb: nybble) : bool := 
  match nb with 
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.


Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).

End TuplePlayground.


Module NatPlayground.

Inductive nat : Type := 
  | O
  | S (n : nat).
  
Inductive nat' : Type := 
  | stop 
  | tick (n : nat').

End NatPlayground.

Require Import Arith.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat := 
  match n with 
  | O => O
  | S O => O
  | S (S n') => n'
  end.
  
Compute (minustwo 4).

Check S.

Check pred.

Check minustwo.

Fixpoint even (n : nat) : bool := 
 match n with 
 | O => true 
 | S O => false
 | S (S n') => even n'
 end.
 
Compute (even 11).

Definition odd (n : nat) : bool := 
  negb (even n).
  
Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2. 

Fixpoint plus (n : nat) (m : nat) : nat := 
  match n with 
  | O => m 
  | S n' => S (plus n' m)
  end.
  
  
Compute (plus 2 3).

Fixpoint mul (n m : nat) : nat := 
  match n with 
  | O => O
  | S n' => plus m (mul n' m) 
  end.
  
Fixpoint minus (n m : nat) : nat := 
  match n, m with
  | _, O => n
  | O, _ => O
  | S n', S m' => minus n' m'
  end.
  
End NatPlayground2.


Fixpoint factorial (n:nat) : nat := 
  match n with 
  | O => S O 
  | S n' => mult n (factorial n')
  end.
 
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Compute (factorial 5).

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


          
Theorem plus0n: forall n : nat, O + n = n.
Proof. 
  intros n. reflexivity. Qed.

Theorem plus_1_l : forall (n:nat), 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_0_l : forall (n : nat), 0 * n = 0.
Proof. intros m. simpl. reflexivity. Qed.


Theorem plus_id_example: forall (n m : nat), n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity. Qed.


Theorem plus_id_exercise : forall (n m o : nat),
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity. Qed.


Check mult_n_O.

Theorem mult_n_0_m_0 : forall (p q : nat),
    (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.


Theorem mult_n_1 : forall (p : nat),
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl.
  reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall (n : nat),
  (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall (b : bool),
    negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.


Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem andb_true_elim2 : forall (b c : bool),
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + intros H.
      rewrite <- H.
      reflexivity.
  - destruct c.
    + reflexivity.
    + intros H.
      rewrite <- H.
      reflexivity.
   Show Proof.
Qed.
Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  (* Show Proof. *)
Qed.


(* Fixpoint non_term (n : nat) : nat :=
  match n with
  | O => O
  | S k => k + non_term n
  end.
*)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) -> 
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros [].
  - rewrite -> H.
    rewrite -> H.
    reflexivity.
  - rewrite <- H.
    rewrite <- H.
    reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) -> 
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros [].
  - rewrite -> H.
    rewrite -> H.
    simpl.
    reflexivity.
  - rewrite -> H.
    rewrite -> H.
    reflexivity.
Qed.

Lemma l1: forall c, true || c = true.
Proof.
  intros c.
  simpl.
  reflexivity.
Qed.

Lemma l2: forall c, false || c = c. 
Proof.
  intros c.
  simpl.
  reflexivity.
Qed.  

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) -> 
  b = c.
Proof.
  intros b c.
  intros H.
  destruct b.
  - rewrite -> l1 in H.
    rewrite <- H.
    simpl.
    reflexivity.
  - simpl in H.
    rewrite -> H.
    reflexivity.
 Qed.
(*  -  rewrite -> l2 in H.
    rewrite <- H.
    simpl.
    reflexivity.
 Qed.*)

Module LateDays.

  Inductive letter : Type :=
    | A | B | C | D | F.

  Inductive modifier : Type :=
    | Plus | Natural | Minus.

  Inductive grade : Type :=
    Grade (l : letter) (m : modifier).

  Inductive comparison : Set :=
    | Eq : comparison
    | Lt : comparison 
    | Gt : comparison.             

  Definition letter_comparison (l1 l2 : letter) : comparison :=
     match l1, l2 with
     | A, A => Eq
     | A, _ => Gt
     | B, A => Lt
     | B, B => Eq
     | B, _ => Gt
     | C, (A | B) => Lt
     | C, C => Eq
     | C, _ => Gt
     | D, (A | B | C) => Lt
     | D, D => Eq
     | D, _ => Gt
     | F, (A | B | C | D) => Lt
     | F, F => Eq
  end.

  Compute letter_comparison B A.

  Compute letter_comparison D D.

  Compute letter_comparison B F.

  Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
  Proof.
    intros [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Definition modifier_comparison (m1 m2 : modifier) : comparison :=
     match m1, m2 with
     | Plus, Plus => Eq
     | Plus, _ => Gt
     | Natural, Plus => Lt
     | Natural, Natural => Eq
     | Natural, _ => Gt
     | Minus, (Plus | Natural) => Lt
     | Minus, Minus => Eq
  end.

  Definition grade_comparison (g1 g2 : grade) : comparison :=
    match g1, g2 with
    | Grade l1 m1, Grade l2 m2 =>
        match letter_comparison l1 l2 with 
        | Eq => modifier_comparison m1 m2
        | Gt => Gt
        | Lt => Lt
        end
    end.

  Example test_grade_comparison1:
    (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
  Proof.  
    reflexivity.
  Qed.

  Example test_grade_comparison2 :
    (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
  Proof.
    simpl.
    reflexivity.
  Qed.


  Example test_grade_comparison4 :
      (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Definition lower_letter (l : letter) : letter :=
    match l with
    | A => B
    | B => C
    | C => D
    | D => F
    | F => F
    end.

  Theorem lower_letter_lowers: forall (l : letter),
      letter_comparison (lower_letter l) l = Lt.
  Proof.
    intros l.
    destruct l.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      Abort. (* Can't prove it *)

  Theorem lower_letter_F_is_F:
    lower_letter F = F.
  Proof.
    simpl. reflexivity.
  Qed.

  Theorem lower_letter_lowers:
     forall (l : letter),
        letter_comparison F l = Lt -> 
        letter_comparison (lower_letter l) l = Lt.
  Proof.
    intros l.
    intros H.
    destruct l.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - rewrite <- H. simpl. reflexivity.
  Qed.

  Definition lower_grade (g : grade) : grade :=
    match g with
    | Grade l Plus => Grade l Natural
    | Grade l Natural => Grade l Minus
    | Grade F Minus => Grade F Minus
    | Grade l Minus => Grade (lower_letter l) Plus
    end.

  Example lower_grade_A_Plus :
    lower_grade (Grade A Plus) = (Grade A Natural).
  Proof.
    simpl. reflexivity.
  Qed.

  Example lower_grade_A_Natural :
    lower_grade (Grade A Natural) = (Grade A Minus).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example lower_grade_A_Minus :
    lower_grade (Grade A Minus) = (Grade B Plus).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example lower_grade_B_Plus :
    lower_grade (Grade B Plus) = (Grade B Natural).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example lower_grade_F_Natural :
    lower_grade (Grade F Natural) = (Grade F Minus).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example lower_grade_twice :
    lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example lower_grade_thrice :
    lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem lower_grade_lowers :
     forall (g : grade),
      grade_comparison (Grade F Minus) g = Lt ->
      grade_comparison (lower_grade g) g = Lt.
  Proof.
    intros g.
    intros H.
    destruct g. destruct m.
    - simpl. destruct l.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
    - simpl. destruct l.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
    - simpl. destruct l.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + rewrite -> H. reflexivity.
  Qed.

  Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
    if late_days <? 9 then g
    else if late_days <? 17 then lower_grade g
    else if late_days <? 21 then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g)).

  Theorem apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).
  Proof.
    intros. reflexivity.
  Qed.

  Theorem no_penalty_for_mostly_on_time :
    forall (late_days : nat) (g : grade),
      (late_days <? 9 = true) ->
      apply_late_policy late_days g = g.
  Proof.
    intros late_days.
    intros g.
    intros H.
    rewrite -> apply_late_policy_unfold.
    rewrite -> H.
    reflexivity.
  Qed.

  Theorem grade_lowered_once :
    forall (late_days : nat) (g : grade),
      (late_days <? 9 = false) ->
      (late_days <? 17 = true) ->
      (grade_comparison (Grade F Minus) g = Lt) ->
      (apply_late_policy late_days g) = (lower_grade g).
  Proof.
    intros late_days g H G I.
    rewrite -> apply_late_policy_unfold.
    rewrite -> H.
    rewrite -> G.
    reflexivity.
  Qed.
End LateDays.

Inductive bin : Type :=
  | Z 
  | B0 (n : bin)
  | B1 (n : bin).


Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B1 b => B0 (incr b)
  | B0 b => B1 b
  end.

Fixpoint bin_to_nat' (m:bin) (i:nat): nat :=
  match m with
  | Z => O
  | B1 n => 2^i + bin_to_nat' n (S i)
  | B0 n => bin_to_nat' n (S i)
  end.                      

(* Definition bin_to_nat (m: bin) : nat := bin_to_nat' m O. *)

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => O
  | B0 n => 2 * bin_to_nat n
  | B1 n => 1 + 2 * bin_to_nat n
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof.
  reflexivity.
Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
  reflexivity.
Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr5 :
  bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr6 :
  bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof.
  reflexivity.
Qed.
