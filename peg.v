Section PEG.
  Require Import String.
  Require Import Ascii.
  Require Import Finite_sets.
  Require Import Lt.
  Require Import Omega.
  Require Import Peano.
  
  Definition Q (P : nat -> Prop) (n : nat) := forall k, k < n -> P k.
  
  Theorem strong_induction:
    forall P : nat -> Prop,
      (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
      forall n : nat, P n.
  Proof.
    intros.
    assert (Q_n_all: Q P n).
    { induction n. unfold Q. intros. inversion H0.
      unfold Q. intros. unfold Q in IHn.
      unfold lt in H0. apply le_lt_or_eq in H0.
      elim H0.
      - intros. apply lt_S_n in H1. auto.
      - intros. inversion H1. auto.
    }
    unfold Q in Q_n_all. apply H in Q_n_all. auto.
  Qed.
    
  Variable NonTerminalType : Set.
  
  Inductive ParsingExpression : Set :=
  | empty
  | terminal (c : ascii)
  | nonTerminal (c : NonTerminalType)
  | sequence (e1 e2 : ParsingExpression)
  | choice (e1 e2 : ParsingExpression)
  | star (e : ParsingExpression)
  | isnt (e : ParsingExpression).

  Variable Rule : NonTerminalType -> ParsingExpression.
  Check prod ParsingExpression string.
  Check not ("a"%char = "b"%char).
  Inductive Interp : ParsingExpression * string -> nat * option string -> Prop :=
  | Empty :
      forall (xs : string), Interp (empty, xs) (1, None)
  | TerminalSuccess :
      forall (a : ascii) (xs : string),
        Interp (terminal a, String a xs) (1, Some (String a EmptyString))
  | TerminalFailure1 :
      forall (a b : ascii) (xs : string),
        not (a = b) ->
        Interp (terminal a, String b xs) (1, None)
  | TerminalFailure2 :
      forall (a : ascii),
        Interp (terminal a, EmptyString) (1, None)
  | NonTerminal :
      forall (c : NonTerminalType) (xs o : string) (n : nat),
        Interp (Rule c, xs) (n, Some o) ->
        Interp (nonTerminal c, xs) (n + 1, Some o)
  | SequenceSuccess :
      forall (e1 e2 : ParsingExpression) (x1 x2 y : string) (n1 n2 : nat),
        (Interp (e1, append (append x1 x2) y) (n1, Some x1)) ->
        (Interp (e2, append x2 y) (n2, Some x2)) ->
        Interp (sequence e1 e2, append (append x1 x2) y) (n1 + n2 + 1, Some (append x1 x2))
  | SequenceFailure1 :
      forall (e1 e2 : ParsingExpression) (x : string) (n : nat),
        Interp (e1, x) (n, None) ->
        Interp (sequence e1 e2, x) (n + 1, None)
  | SequenceFailure2 :
      forall (e1 e2 : ParsingExpression) (x y : string) (n1 n2 : nat),
        Interp (e1, append x y) (n1, Some x) ->
        Interp (e2, y) (n2, None) ->
        Interp (sequence e1 e2, append x y) (n1 + n2 + 1, None)
  | Choice1 :
      forall (e1 e2 : ParsingExpression) (x y : string) (n : nat),
        Interp (e1, append x y) (n, Some x) ->
        Interp (choice e1 e2, append x y) (n + 1, Some x)
  | Choice2 :
      forall (e1 e2 : ParsingExpression) (x o : string) (n1 n2 : nat),
        Interp (e1, x) (n1, None) ->
        Interp (e2, x) (n2, Some o) ->
        Interp (choice e1 e2, x) (n1 + n2 + 1, Some o)
  | StarRepitition :
      forall (e : ParsingExpression) (x1 x2 y : string) (n1 n2 : nat),
        Interp (e, append (append x1 x2) y) (n1, Some x1) ->
        Interp (star e, append x2 y) (n2, Some x2) ->
        Interp (star e, append (append x1 x2) y) (n1 + n2 + 1, Some (append x1 x2))
  | StarTermination :
      forall (e : ParsingExpression) (x : string) (n : nat),
        Interp (e, x) (n, None) ->
        Interp (star e, x) (n + 1, Some EmptyString)
  | Isnt1 :
      forall (e : ParsingExpression) (x y : string) (n : nat),
        Interp (e, append x y) (n, Some x) ->
        Interp (isnt e, append x y) (n + 1, None)
  | Isnt2 :
      forall (e : ParsingExpression) (x y : string) (n : nat),
        Interp (e, append x y) (n, None) ->
        Interp (isnt e, append x y) (n + 1, Some EmptyString).
  Check Interp_ind.
  
  Lemma interp_empty : forall n xs y, Interp (empty, xs) (n, y) -> n = 1 /\ y = None.
  Proof.
    intros.
    inversion H.
    split; auto.
  Qed.
  
  Lemma interp_steps : forall e xs n y, Interp (e, xs) (n, y) -> n > 0.
  Proof.
    intros e xs n y interp.
    induction e; (inversion interp; omega).
  Qed.

  Lemma empty_string_prefix : forall x, prefix "" x = true.
  Proof.
    intros.
    induction x; reflexivity.
  Qed.
  
  Lemma char_prefix :
    forall (a : ascii) (xs : string), prefix (String a "") (String a xs) = true.
  Proof.
    intros. simpl.
    destruct (ascii_dec a a) as [ Heq | C ].
    { apply empty_string_prefix. }
    { unfold not in C. elimtype False. apply C. reflexivity. }
  Qed.

  Lemma prefix_append : forall x y, prefix x (x ++ y) = true.
  Proof.
    intros.
    induction x.
    - simpl. induction y; reflexivity.
    - simpl. destruct (ascii_dec a a) as [ Heq | C ].
      + apply IHx.
      + unfold not in C. elimtype False. apply C. reflexivity.
  Qed.
    
  Theorem interp_prefix : forall n x y e, Interp (e, x) (n, Some y) -> (prefix y x) = true.
  Proof.
    induction n using strong_induction.
    - intros x y e interp.
      (* Most cases follow from basic facts about [prefix] *)
      inversion interp; repeat(apply char_prefix ||
                               apply prefix_append ||
                               apply empty_string_prefix).
      + assert(n0_lt_n: n0 < n). { omega. }
        specialize (H n0). apply H in H1; auto.
      + assert(n2_lt_n: n2 < n). { omega. }
        specialize (H n2).
        apply H in H5; auto.
  Qed.

  Lemma append_assoc : forall s1 s2 s3, (s1 ++ (s2 ++ s3))%string = ((s1 ++ s2) ++ s3)%string.
  Proof.
    intros.
    induction s1.
    - reflexivity.
    - simpl. rewrite -> IHs1. reflexivity.
  Qed.

  Lemma solve_append : forall x y z, (x ++ y = x ++ z)%string -> y = z.
  Proof.
    intros.
    induction x.
    - auto.
    - apply IHx. simpl in H. inversion H. reflexivity.
  Qed.
  
  Theorem interp_is_a_function : forall n1 n2 o1 o2 e x, Interp (e, x) (n1, o1) -> Interp (e, x) (n2, o2) -> n1 = n2 /\ o1 = o2.
  Proof.
    induction n1 using strong_induction.
    - induction n2 using strong_induction.
      intros o1 o2 e x interp1 interp2.
      destruct e.
      { (* empty *)
        inversion interp1.
        inversion interp2.
        auto.
      }
      { (* terminal c *)
        inversion interp1; auto.
        inversion interp2; auto.
        {
          rewrite <- H7 in H3.
          inversion H3.
          absurd(c = b); auto.
        }
        {
          rewrite <- H7 in H3.
          inversion H3.
        }
        + inversion interp2; auto. rewrite <- H8 in H3. inversion H3. absurd(b = c); auto.
        + inversion interp2; auto. rewrite <- H7 in H3. inversion H3.
      }
      { (* nonTerminal c *)
        inversion interp1.
        inversion interp2.
        subst x n1 n2. (* clean up inversion's mess *)
        assert(n_lt_n_p_1: n < n + 1).
        { omega. }
        specialize (H n n_lt_n_p_1 n0 (Some o) (Some o0) (Rule c) xs).
        apply H in H2.
        split.
        + assert(K: n = n0 -> n + 1 = n0 + 1).
          { omega. }
          apply K.
          apply H2.
        + apply H2.
        + apply H7.
      }
      { (* sequence e1 e2 *)
        inversion interp1.
        inversion interp2.
        {
          subst x n1 n2 e0 e3 e4 e5.
          rewrite H11 in H10.
          assert(goal1: n0 = n4 /\ Some x1 = Some x0).
          {
            assert(n0_small: n0 < n0 + n3 + 1).
            { omega. }
            specialize (H n0 n0_small n4 (Some x1) (Some x0) e1 ((x1 ++ x2) ++ y)%string).
            apply H in H3.
            apply H3.
            apply H10.
          }

          assert(goal2: n3 = n5 /\ Some x2 = Some x3).
          {
            (* need x2 = x3 /\ n3 = n5 by... *)
            (* showing x3 ++ y0 = x2 ++ y *)
            rewrite <- append_assoc in H11.
            rewrite <- append_assoc in H11.
            assert(x0_eq_x1: x0 = x1).
            { inversion goal1. inversion H2. reflexivity. }
            rewrite x0_eq_x1 in H11.
            apply solve_append in H11.
            rewrite H11 in H14.
            
            (* applying H to H7 *)
            assert(n3_small: n3 < n0 + n3 + 1).
            { omega. }
            specialize (H n3 n3_small n5 (Some x2) (Some x3) e2 (x2 ++ y)%string).
            apply H in H7.
            apply H7.
            apply H14.
          }
          
          elim goal1. intros.
          elim goal2. intros.
          rewrite H1.
          rewrite H4.
          inversion H2.
          inversion H5.
          rewrite <- H9.
          split; reflexivity.
        }
        {
          specialize(H n0).
          assert(n0_lt_n1: n0 < n1).
          { omega. }
          specialize(H n0_lt_n1 n (Some x1) None e1 ((x1 ++ x2) ++ y)%string).
          subst x.
          apply H in H3.
          elim H3. intros _ some_x1_eq_none.
          inversion some_x1_eq_none.
          apply H9.
        }
        {
          subst e4 e5 e0 e3 o1 o2 x n1 n2.
          assert(goal1: n0 = n4 /\ Some x1 = Some x0).
          {
            specialize(H n0).
            assert(n0_small: n0 < n0 + n3 + 1).
            { omega. }
            specialize(H n0_small n4 (Some x1) (Some x0) e1 ((x1 ++ x2) ++ y)%string).
            apply H in H3.
            apply H3.
            rewrite <- H11.
            apply H10.
          }
          assert(goal2: y0 = (x2 ++ y)%string).
          {
            elim goal1. intros _ some_x1_eq_some_x2.
            inversion some_x1_eq_some_x2.
            rewrite H2 in H11.
            rewrite <- append_assoc in H11.
            apply solve_append in H11.
            apply H11.
          }
          assert(n3 = n5 /\ Some x2 = None).
          {
            clear H3 H10.
            rewrite goal2 in H14.
            specialize (H n3).
            assert(n3_small: n3 < n0 + n3 + 1).
            { omega. }
            specialize (H n3_small n5 (Some x2) None e2 (x2 ++ y)%string H7 H14).
            auto.
          }
          inversion H1. inversion H4.
        }
        {
          assert(n_small: n < n + 1).
          { omega. }
          subst x n1 e0 e3 o1.
          inversion interp2.
          {
            subst e0 e3.
            rewrite H5 in H4.
            clear H8 H0 interp1 interp2.
            
            specialize (H n n_small n1 None (Some x1) e1 x0 H2 H4).
            inversion H. inversion H1.
          }
          {
            specialize (H n n_small n0 None None e1 x0 H2 H3).
            inversion H.
            split.
            + omega.
            + reflexivity.
          }
          {
            clear interp1 interp2 H8.
            subst x0.
            specialize (H n n_small n1 None (Some x) e1 (x ++ y)%string H2 H4).
            inversion H. inversion H8.
          }
        }
        {
          inversion interp1.
          {
            clear interp1 interp2 H0.
            subst e0 e3 e4 e5 o1 x n1.
            rewrite H11 in H10.

            assert(goal1: n0 = n4 /\ Some x0 = Some x1).
            {
              assert(n0_small: n0 < n0 + n3 + 1).
              { omega. }
              clear H7 H14.
              specialize (H n0 n0_small n4 (Some x0) (Some x1) e1 (x0 ++ y)%string).
              auto.
            }
            assert(goal2: y = (x2 ++ y0)%string).
            {
              clear H3 H10.
              rewrite <- append_assoc in H11.
              inversion goal1. inversion H1.
              rewrite H3 in H11.
              apply solve_append in H11.
              auto.
            }
            clear H3 H10.
            rewrite goal2 in H7.
            assert(n3_small: n3 < n0 + n3 + 1).
            { omega. }

            specialize (H n3 n3_small n5 None (Some x2) e2 (x2 ++ y0)%string H7 H14).
            inversion H. inversion H1.
          }
          {
            assert(n0_small: n0 < n1).
            { omega. }
            clear H7 H0 interp1 interp2.
            subst e4 e5 e0 e3 o1 x.
            specialize (H n0 n0_small n (Some x0) None e1 (x0 ++ y)%string H3 H9).
            inversion H. inversion H1.
          }
          {
            inversion interp2.
            subst e0 e3 e4 e5 e6 e7.
            clear interp1 interp2.
            {
              assert(goal1: n0 = n4 /\ Some x0 = Some x1).
              {
                rewrite H4 in H3. rewrite H11 in H10.
                assert(n0_small: n0 < n1).
                { omega. }
                specialize (H n0 n0_small n4 (Some x0) (Some x1) e1 x H3 H10).
                apply H.
              }
              assert(goal2: x1 = x2).
              {
                rewrite H18 in H17. rewrite H11 in H10.
                assert(n4_small: n4 < n1).
                { omega. }
                specialize (H n4 n4_small n6 (Some x1) (Some x2) e1 x H10 H17).
                inversion H. inversion H2. reflexivity.
              }
              assert(goal3: y0 = (x3 ++ y1)%string).
              {
                rewrite goal2 in H11.
                rewrite <- H11 in H18.
                rewrite <- append_assoc in H18.
                apply solve_append in H18.
                symmetry.
                apply H18.
              }

              rewrite goal3 in H14.
              assert(n5_small: n5 < n1).
              { omega. }
              specialize (H n5 n5_small n7 None (Some x3) e2 (x3 ++ y1)%string H14 H21).
              inversion H. inversion H2.
            }
            {
              rewrite H11 in H10. rewrite H4 in H3.
              assert(n4_small: n4 < n1).
              { omega. }
              specialize (H n4 n4_small n (Some x1) None e1 x H10 H16).
              inversion H. inversion H22.
            }
            {
              assert(goal1: n0 = n6 /\ Some x0 = Some x2).
              {
                rewrite H4 in H3. rewrite H18 in H17.
                assert(n0_small: n0 < n1).
                { omega. }
                specialize (H n0 n0_small n6 (Some x0) (Some x2) e1 x H3 H17).
                apply H.
              }
              assert(goal2: y = y1).
              {
                inversion goal1. inversion H23.
                rewrite H25 in H4.
                rewrite <- H18 in H4.
                apply solve_append in H4.
                apply H4.
              }

              assert(goal3: n3 = n7 /\ (None : option string) = None).
              {
                rewrite goal2 in H7.
                assert(n3_small: n3 < n1).
                { omega. }
                specialize (H n3 n3_small n7 None None e2 y1 H7 H21).
                apply H.
              }
              
              inversion goal1. inversion goal3.
              rewrite H22. rewrite H24.
              split; reflexivity.
            }
          }        
        }
      }
      
      { (* choice e1 e2 *)
        inversion interp1.
        {
          inversion interp2.
          {
            rewrite H4 in H2. rewrite H10 in H8.
            assert(n_small: n < n1).
            { omega. }
            specialize (H n n_small n0 (Some x0) (Some x1) e1 x H2 H8).
            inversion H.
            split; auto.
          }
          {
            rewrite H4 in H2.
            assert(n_small: n < n1).
            { omega. }
            specialize (H n n_small n0 (Some x0) None e1 x H2 H9).
            inversion H. inversion H15.
          }
        }
        { (* choice e1 e2 *)
          inversion interp2.
          {
            subst e0 e3 x0 e4 e5.
            rewrite H11 in H9.
            assert(n0_small: n0 < n1).
            { omega. }
            specialize (H n0 n0_small n None (Some x1) e1 x H3 H9).
            inversion H. inversion H2.
          }
          {
            assert(goal1: n0 = n4).
            {
              assert(n0_small: n0 < n1).
              { omega. }
              specialize (H n0 n0_small n4 None None e1 x H3 H10).
              inversion H.
              apply H15.
            }
            assert(goal2: n3 = n5 /\ Some o = Some o0).
            {
              assert(n3_small: n3 < n1).
              { omega. }
              specialize (H n3 n3_small n5 (Some o) (Some o0) e2 x H7 H14).
              apply H.
            }
            inversion goal1. inversion goal2.
            rewrite <- H15. rewrite <- H16.
            split.
            + omega.
            + apply H17.
          }
        }
      }
      
      { (* star e *)
        inversion interp1. clear interp1.
        {
          inversion interp2. clear interp2.
          {
            assert(goal1: n0 = n4 /\ Some x1 = Some x0).
            {
              rewrite H2 in H4. rewrite H8 in H10.
              assert(n0_small: n0 < n1).
              { omega. }
              specialize (H n0 n0_small n4 (Some x1) (Some x0) e x H4 H10).
              apply H.
            }
            clear H4 H10.
            assert(goal2: (x2 ++ y)%string = (x3 ++ y0)%string).
            {
              inversion goal1. inversion H10.
              rewrite <- H14 in H8.
              rewrite <- H2 in H8.
              rewrite <- append_assoc in H8. rewrite <- append_assoc in H8.
              apply solve_append in H8.
              symmetry.
              apply H8.
            }
            assert(goal3: n3 = n5 /\ Some x2 = Some x3).
            {
              assert(n3_small: n3 < n1).
              { omega. }
              rewrite goal2 in H6.
              specialize (H n3 n3_small n5 (Some x2) (Some x3) (star e) (x3 ++ y0)%string H6 H12).
              apply H.
            }
            
            inversion goal1.
            inversion goal3.
            split.
            + rewrite H4.
              rewrite H13.
              reflexivity.
            + inversion H10.
              inversion H14.
              rewrite <- H16.
              reflexivity.
          }
          {
            rewrite H2 in H4.
            assert(n0_small: n0 < n1).
            { omega. }
            specialize (H n0 n0_small n (Some x1) None e x H4 H8).
            inversion H.
            inversion H13.
          }
        }
        {
          inversion interp2. clear interp2.
          {
            rewrite H7 in H9.
            assert(n_small: n < n1).
            { omega. }
            specialize (H n n_small n0 None (Some x1) e x H2 H9).
            inversion H.
            inversion H13.
          }
          {
            assert(n_small: n < n1).
            { omega. }
            specialize (H n n_small n0 None None e x H2 H7).
            inversion H.
            rewrite H11.
            split; reflexivity.
          }
        }
      }
      { (* isnt e *)
        inversion interp1; clear interp1.
        {
          assert(n_small: n < n1).
          { omega. }
          inversion interp2; clear interp2.
          {
            rewrite H3 in H2. rewrite H8 in H7.
            specialize (H n n_small n0 (Some x0) (Some x1) e x H2 H7).
            inversion H.
            rewrite H11.
            split; reflexivity.
          }
          {
            rewrite H3 in H2. rewrite H8 in H7.
            specialize(H n n_small n0 (Some x0) None e x H2 H7).
            inversion H. inversion H12.
          }
        }
        {
          assert(n_small: n < n1).
          { omega. }
          inversion interp2; clear interp2.
          {
            rewrite H3 in H2. rewrite H8 in H7.
            specialize (H n n_small n0 None (Some x1) e x H2 H7).
            inversion H. inversion H12.
          }
          {
            rewrite H3 in H2. rewrite H8 in H7.
            specialize (H n n_small n0 None None e x H2 H7).
            inversion H.
            rewrite H11.
            split; reflexivity.
          }
        }
      }
  Qed.
  