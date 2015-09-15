Require Image.
Require Import Program Arith Omega.

Definition revapply {A B:Type} x (f: A -> B) := f x.
Infix "|>" := revapply (at level 60).
Definition andThen {A B C:Type} (f:A->B)(g:B->C) := fun x => g (f x).
Infix ">>>" := andThen (at level 60).

Infix "=?" := Peano_dec.eq_nat_dec (at level 70) : nat_scope.

Notation "x && y" := (Sumbool.sumbool_and _ _ _ _ x y): sumbool_scope.
Delimit Scope sumbool_scope with sumbool.

Definition not_dec {A:Type}{P:A->Prop}(P_dec: forall x,{P x}+{~P x}): forall x,{~P x}+{P x} :=
  fun x => match P_dec x with
           | left H => right H
           | right H => left H
           end.

Definition not_dec' {A:Type}{P:A->Prop}(P_dec: forall x,{P x}+{~P x}): forall x,{~P x}+{~~P x}.
  refine (fun x => match P_dec x with
           | left H => right _
           | right H => left H
           end).
 - intro. elim H0. exact H.
Defined.

(** * リストモジュールの拡張 *)
Module List.
  Require Export List.
  
  Section List_index_of.
  Context {A : Type}.
  Variable eq_dec : forall (x y:A), {x=y}+{x<>y}.

  Fixpoint _index_of_loop a xs i :=
    match xs with
    | nil => None
    | x::xs => if eq_dec x a then Some i else _index_of_loop a xs (S i)
    end.
  Definition index_of a xs :=
    _index_of_loop a xs 0.

  Lemma _index_of_loop_plus : forall a xs p i l m,
    _index_of_loop a xs (p+l) = Some (i+l) -> _index_of_loop a xs (p+m) = Some (i+m).
  Proof.
  induction xs; intros.
   simpl in H; inversion H.
   simpl in *.
    destruct eq_dec with a0 a.
     f_equal; injection H; omega.
    rewrite <- plus_Sn_m; rewrite <- plus_Sn_m in H.
     apply IHxs with l.
      exact H.
  Qed.

  Lemma _index_of_loop_ge_p : forall a xs p i,
    _index_of_loop a xs p = Some i -> p <= i.
  Proof.
  induction xs; intros; simpl in H.
   inversion H.
   destruct eq_dec with a0 a.
    inversion H; auto.
    apply IHxs in H.
     apply le_trans with (S p); auto.
  Qed.

  Lemma index_of_hd : forall (x:A) xs,
    index_of x (x::xs) = Some 0.
  Proof.
   intros x xs. unfold index_of. simpl. destruct (eq_dec x x);[auto|].
   now elim n.
  Qed.

  Lemma _index_of_loop_nth_Some : forall a xs p i,
    _index_of_loop a xs p = Some i -> (forall dummy, nth (i-p) xs dummy = a).
  Proof.
  intros a xs p i; revert xs p; induction i.
   intros; simpl.
    destruct xs; simpl in H.
     inversion H.
     destruct eq_dec with a0 a.
      inversion H; subst; simpl.
       reflexivity.
       apply _index_of_loop_ge_p in H.
        omega.
   intros; simpl.
    destruct xs; simpl in H.
     inversion H.
     destruct eq_dec with a0 a.
      injection H; intro; subst.
       rewrite minus_diag; simpl; auto.
      destruct p.
       simpl.
        rewrite minus_n_O with i.
         apply IHi.
         assert (X:=_index_of_loop_plus a xs 0 i 1 0).
          repeat (rewrite <- plus_n_O in X); apply X.
           simpl; rewrite H; f_equal; omega.
       apply IHi.
        simpl; destruct eq_dec with a0 a.
         elim n; now auto.
         assert (X:=_index_of_loop_plus a xs (S p) i 1 0).
          repeat (rewrite <- plus_n_O in X); apply X.
           rewrite plus_comm; simpl; rewrite H.
            f_equal; omega.
  Qed.

  Lemma index_of_nth_Some : forall a xs i,
    index_of a xs = Some i -> (forall dummy, nth i xs dummy = a).
  Proof.
    unfold index_of.
    intros a xs i H; assert (H':=_index_of_loop_nth_Some a xs 0 i H).
    rewrite <- minus_n_O in H'; exact H'.
  Qed.

  Lemma _index_of_loop_nth_None : forall a xs p i,
    _index_of_loop a xs p = None -> forall dummy, a <> dummy -> nth i xs dummy <> a.
  Proof.
  induction xs; intros; simpl in *.
  +destruct i; now auto.
  +destruct eq_dec with a0 a.
    inversion H.
    destruct i.
     now auto.
     apply IHxs with (S p).
      exact H.
      exact H0.
  Qed.

  Lemma index_of_nth_None : forall a xs i,
    index_of a xs = None -> forall dummy, a <> dummy -> nth i xs dummy <> a.
  Proof.
  intros a xs i.
  unfold index_of; now apply _index_of_loop_nth_None.
  Qed.

  Lemma index_of_tl_Some : forall (a x:A) xs i,
    a <> x -> index_of a xs = Some i ->
    index_of a (x::xs) = Some (S i).
  Proof.
   (*induction xs?*)
  Admitted.

  Lemma index_of_tl_None : forall(a x:A) xs,
    a <> x -> index_of a xs = None ->
    index_of a (x::xs) = None.
  Proof.
   (*induction xs?*)
  Admitted.

  Lemma _index_of_loop_In_Some : forall a xs p i,
    _index_of_loop a xs p = Some i -> In a xs.
  Proof.
  induction xs; intros; simpl in H.
   inversion H.
   destruct eq_dec with a0 a.
    subst; left; now auto.
    right; apply IHxs with (S p) i; now auto.
  Qed.

  Lemma index_of_In_Some : forall a xs i,
    index_of a xs = Some i -> In a xs.
  Proof.
  intros ? ? ?; unfold index_of; apply _index_of_loop_In_Some.
  Qed.

  Lemma _index_of_loop_In_None : forall a xs p,
    _index_of_loop a xs p = None -> ~In a xs.
  Proof.
  induction xs; intros; intro.
   exact H0.
   destruct H0.
    simpl in H.
     destruct eq_dec with a0 a.
      inversion H.
      elim n; now auto.
    apply IHxs with (S p).
     simpl in H.
      destruct eq_dec with a0 a.
       inversion H.
       exact H.
     exact H0.
  Qed.

  Lemma index_of_In_None : forall a xs,
    index_of a xs = None -> ~In a xs.
  Proof.
  intros a xs; unfold index_of; apply _index_of_loop_In_None.
  Qed.

  Lemma index_of_nth_iff : forall (a:A) xs i,
    NoDup xs ->
    (index_of a xs = Some i <-> nth_error xs i = Some a).
  Proof.
  Admitted.

  End List_index_of.

  Lemma combine_nth_error: forall (A B : Type) (l : list A) (l' : list B)
                                  (n : nat) (x : A) (y : B),
    length l = length l' ->
    (List.nth_error (List.combine l l') n = Some (x, y)
    <-> List.nth_error l n = Some x /\ List.nth_error l' n = Some y).
  Proof.
   induction l.
   - simpl. split; now destruct n.
   - intros l' n x y Hlen. destruct l' as [| b l']; [discriminate Hlen|].
     simpl. destruct n.
     + simpl. split.
       * intro H. injection H. intros eq1 eq2. now rewrite eq1, eq2.
       * intro H. destruct H. injection H. injection H0. intros eq1 eq2. now subst.
     + simpl. rewrite IHl; [|now injection Hlen]. reflexivity.
  Qed.

       
  Fixpoint Forall_dec {A:Type}{P:A -> Prop} (P_dec : forall x, {P x}+{~P x}) (xs : list A) : {Forall P xs} + {~Forall P xs}.
  refine (
    match xs with
    | nil => left _
    | x::xs => if P_dec x then _
               else right _
    end).
   - constructor.
   - destruct (Forall_dec A P P_dec xs0) as [tlTrue|tlFalse].
     + apply left. now constructor.
     + apply right. intro. inversion H. contradiction.
   - intro. inversion H. contradiction.
  Defined.

  Fixpoint Forall_dec' {A:Type}{P:A -> Prop} (P_dec : forall x, {P x}+{~P x}) (xs : list A) : {Forall P xs} + {Exists (fun x => ~ P x) xs}.
  refine (
    match xs with
    | nil => left _
    | x::xs => if P_dec x then _
               else right _
    end).
    - constructor.
    - destruct (Forall_dec' A P P_dec xs0) as [tlTrue|tlFalse].
      + apply left. now constructor.
      + apply right. now apply Exists_cons_tl. 
    - now apply Exists_cons_hd.
  Defined.

  Section filter.
  Context {A : Type}.
  Context {P Q: A -> Prop}.
  Variable P_dec : forall x, {P x}+{~P x}.
          

  (* sumbool版リストfilter *)
  Fixpoint filter' (xs: list A) : list A :=
    match xs with
    | nil => nil
    | x::xs => if P_dec x then x :: filter' xs
               else filter' xs
    end.
  Lemma filter'_In : forall (x:A) l,
    In x (filter' l) <-> In x l /\ P x.
  Proof.
   intros x l. split.
   - revert x; induction l; intros; simpl in *.
     elim H.
     destruct P_dec with a.
     + destruct H; subst; [now split; auto|].
       split; destruct IHl with x; now auto.
     + split; destruct IHl with x; now auto.
   - revert x. induction l.
     + now simpl.
     + simpl. intros x Hx. destruct Hx as [Hx1 Hx2].
       destruct (P_dec a); intros.
       * simpl. destruct Hx1; [now left|right]. apply IHl. now split.
       * destruct Hx1; [now rewrite H in n|]. apply IHl. now split.
Qed.

  Lemma filter'_length : forall(l:list A),
    length (filter' l) <= length l.
  Proof.
   induction l.
   - now auto.
   - simpl. destruct (P_dec a); simpl.
     + now apply le_n_S.
     + now apply le_S.
  Qed.

  End filter.

  Section remove_all.
  Context {A : Type}.
  Variable eq_dec : forall x y:A, {x=y}+{x<>y}.

  Lemma remove_In : forall x l a,
    In a (List.remove eq_dec x l) <-> In a l /\ a <> x.
  Proof.
    intros; split; intro; induction l; simpl in *.
  +elim H.
  +destruct eq_dec with x a0.
    destruct (IHl H).
     split; now auto.
    destruct H.
     split.
      now auto.
      subst; intro; subst; apply n; now auto.
     destruct (IHl H).
      split; now auto.
  +destruct H as [[] _].
  +destruct eq_dec with x a0.
    subst; apply IHl.
     destruct H as [[? | ?] ?]; split; auto.
      elim H0; subst; now auto.
    destruct H as [[? | ?] ?].
     left; now auto.
     right; apply IHl; split; now auto.
  Qed.

  (* lからxsのすべての要素を削除する *)
  Definition remove_all xs l :=
    List.fold_left (fun accl x => remove eq_dec x accl) xs l.

  Lemma remove_all_In : forall xs l y,
    In y (remove_all xs l) <-> In y l /\ ~In y xs.
  Proof.
   induction xs.
   - simpl. tauto.
   - intros l y. split.
     + simpl. intro H.
       destruct (IHxs (remove eq_dec a l) y) as [HH _].
       set (HH H) as H0. destruct H0 as [In_y_rem notIn_y].
       apply remove_In in In_y_rem.
       destruct In_y_rem; split.
        now auto.
        intro H'; destruct H'.
         subst; now auto.
         now auto.
     + simpl; intro H.
       destruct H as [Hl Hr].
       assert (In y l /\ y <> a) as Hy.
       {
        split.
         now auto.
         intro; apply Hr; left; now auto.
       }
       apply remove_In in Hy.
       apply IHxs.
       split.
        exact Hy.
        intro; apply Hr; right; now auto.
  Qed.

  End remove_all.

  Fixpoint remove_i {A:Type} i (xs:list A) :=
    match i, xs with
    | O, x::xs => xs
    | S p, x::xs => x :: remove_i p xs
    | _, nil => nil
    end.

  Lemma remove_i_le_length : forall (A:Type) i (xs:list A),
    length xs <= i -> remove_i i xs = xs.
  Proof.
  induction i; intros.
  +destruct xs.
    simpl; now auto.
    simpl in H; omega.
  +destruct xs.
    simpl; now auto.
    simpl.
     f_equal.
      apply IHi; simpl in H; omega.
  Qed.

  Fixpoint insert_i {A:Type} i (y:A) (xs:list A) :=
    match i, xs with
    | O, _ => y::xs
    | S p, x::xs => x :: insert_i p y xs
    | S p, nil => nil (* indexに到達しないときは追加しない *)
    end.

  Lemma le_length_remove_i : forall A i (xs : list A),
    remove_i i xs = xs -> length xs <= i.
  Proof.
  induction i; intros.
  +destruct xs.
    simpl; now auto.
    simpl in H.
     elimtype False.
      revert a H; induction xs; intros.
       inversion H.
       injection H.
        intros.
         apply IHxs with a; now auto.
  +destruct xs.
    simpl; omega.
    simpl in *; apply le_n_S.
     injection H; now apply IHi.
  Qed.

  Lemma remove_i_insert_i : forall (A:Type) i (y:A) xs,
    remove_i i (insert_i i y xs) = xs.
  Proof.
   induction i.
   - now simpl.
   - intros y xs. simpl. destruct xs; [reflexivity| ]. now rewrite IHi.
  Qed.

  Lemma length_remove_i : forall {A B:Type} i (xs: list A) (ys: list B),
    length xs = length ys -> length (remove_i i xs) = length (remove_i i ys).
  Proof.
   induction i.
   - intros xs ys. destruct xs, ys; simpl.
     + reflexivity.
     + discriminate.
     + discriminate.
     + intro H. now injection H.
   - intros xs ys.
     simpl. destruct xs, ys; simpl.
     + reflexivity.
     + discriminate.
     + discriminate.
     + intros eqlen. f_equal. apply IHi. now injection eqlen.
   Qed.

  Lemma index_loop_le : forall (A:Type) (eq_dec:forall(x y:A), {x=y}+{x<>y})
    j (y:A) xs i,
    _index_of_loop eq_dec y xs i = Some j -> i <= j.
  Proof.
   induction xs.
    simpl. discriminate.

    simpl. intros i. destruct (eq_dec a y).
     intro Heq. injection Heq. intro Heq2. rewrite Heq2. now apply le_refl.

     intro Heq. eapply le_trans with (m := S i); [now auto with arith | ].
     now apply IHxs.
   Qed.

  Lemma insert_i_remove_i_aux : forall (A:Type) (eq_dec:forall(x y:A), {x=y}+{x<>y}) xs k i (y:A),
    _index_of_loop eq_dec y xs k = Some i -> (insert_i (i-k) y (remove_i (i-k) xs)) = xs.
  Proof.
   induction xs.
    intros k i y. simpl. discriminate.

    intros k i y. simpl. destruct (eq_dec a y).
     intro Heq. injection Heq. clear Heq. intro Heq.
     rewrite Heq. rewrite minus_diag. simpl. now rewrite e.

     intro Heq. simpl.
     case_eq (i-k). simpl.
      set (index_loop_le _ eq_dec i y xs (S k) Heq). omega.

      intro m. simpl. intro Heqm. f_equal.
      replace m with (i - (S k)); [|omega].
      apply IHxs. now apply Heq.
  Qed.
    
  Lemma insert_i_remove_i : forall (A:Type) (eq_dec:forall(x y:A), {x=y}+{x<>y}) i (y:A) xs,
    index_of eq_dec y xs = Some i -> (insert_i i y (remove_i i xs)) = xs.
  Proof.
   intros A eq_dec i y xs. unfold index_of. intro H.
   rewrite (minus_n_O i).
   now apply (insert_i_remove_i_aux _ eq_dec).
  Qed.

  Lemma length_insert_i : forall (A B:Type) i (xs: list A)(ys : list B) (a : A)(b:B),
    length xs = length ys -> length (insert_i i a xs) = length (insert_i i b ys).
  Proof.
   induction i; intros.
    destruct xs,ys; [reflexivity|discriminate|discriminate| ].
    simpl. simpl in H. now rewrite H.

    destruct xs,ys; [reflexivity|discriminate|discriminate| ].
    simpl. rewrite (IHi xs ys a b); [reflexivity|].
    simpl in H. now injection H.
  Qed.

  Fixpoint replace_i {A:Type} i (y:A) xs :=
    match i, xs with
    | _, nil => nil (*置き換えない*)
    | 0, x::xs => y::xs
    | S p, x::xs => x :: replace_i p y xs
    end.

(*
  (* 未解決問題9:誤り *)
  Lemma remove_i_replace_i' : forall (A:Type) dummy i (xs ys:list A),
    remove_i i xs = remove_i i ys ->
    replace_i i (nth i ys dummy) xs = ys.
  Proof.
   (* counter-example : xs = [], ys = [a], i = 0. *)
   (* To show a counter-example, we continue a proof without "information lost" by case splitting. *)
   intros.
   destruct i.
   destruct xs.
   destruct ys.
   simpl; now auto.
   (* Here is the case *)
   simpl in *.
    destruct ys.
    (* Presumption H is true, but conclusion is false. *)
   (* More generally : ys = xs ++ [a], i = length xs. *)
  Abort.
*)

  Lemma remove_i_replace_i : forall (A:Type) dummy i (xs ys:list A),
    length xs = length ys ->
    remove_i i xs = remove_i i ys ->
    replace_i i (nth i ys dummy) xs = ys.
  Proof.
  induction i; intros; simpl.
  +destruct xs; simpl.
    destruct ys; [ now auto | simpl in H; now inversion H ].
    destruct ys; simpl.
     simpl in H; now inversion H.
     simpl in H0; f_equal; now auto.
  +destruct xs.
    destruct ys; [ now auto | simpl in H; now inversion H ].
    destruct ys; simpl in H0.
     now inversion H0.
     injection H0; intros; subst.
      simpl; f_equal.
       apply IHi.
        simpl in H; injection H; now auto.
        injection H0; now auto.
  Qed.


  Lemma map_eq : forall (A:Type) (f:A -> A) xs,
    (forall x, In x xs -> f x = x) -> map f xs = xs.
  Proof.
   induction xs.
   - now simpl.
   - intros H. simpl. f_equal.
     + apply H. now left.
     + apply IHxs. intros x HIn. apply H. now right.
  Qed.    

  Lemma map_remove_i : forall (A B:Type) (f:A->B) i xs,
    map f (remove_i i xs) = remove_i i (map f xs).
  Proof.
  intros A B f i xs; revert i; induction xs; intros; simpl in *.
  +destruct i; simpl; now auto.
  +destruct i; simpl.
    now auto.
    f_equal.
     now apply IHxs.
  Qed.

  Lemma replace_i_invaliant : forall (A:Type) i (xs:list A)(nonempty:A),
    exists a, replace_i i a xs = xs.
  Proof.
  (*induction i? はみ出る場合は何でもOK、そうでないならnthに相当するもの*)
  Admitted.

  Lemma map_f_g_eq : forall (A B:Type) (f g: A -> B)(xs: list A),
    (forall x, In x xs -> f x = g x) ->
    map f xs = map g xs.
  Proof.
   intros A B f g xs H. induction xs.
   - reflexivity.
   - simpl. rewrite (H a); [| now left]. f_equal.
     apply IHxs. intros x Hx. apply (H x). now right.
  Qed.

  Require Import Recdef.
  Function nub {A:Type}(eq_dec: forall x y:A, {x=y}+{x<>y}) (xs:list A) {measure length xs} : list A :=
    match xs with
    | nil => nil
    | x::xs => x :: @nub A eq_dec (List.filter' (not_dec' (eq_dec x)) xs)
    end.
   intros A eq_dec xs hd tl Heq. subst. simpl. apply le_lt_n_Sm.
   now apply filter'_length.
  Defined.

  Lemma nub_In_iff: forall (A:Type)(eq_dec:forall x y:A,{x=y}+{x<>y})a(xs:list A),
    In a (nub A eq_dec xs) <-> In a xs.
  Proof.
   intros A eq_dec a xs. functional induction (nub A eq_dec xs).
   - reflexivity.
   - simpl. rewrite IHl. destruct (eq_dec x a).
     + split; now left.
     + split; right.
       * destruct H; [now auto|]. now rewrite filter'_In in H.
       * destruct H; [now auto|]. apply filter'_In. now split.
  Qed.

  Definition map2 {A B C:Type}(f: A->B->C)(xs:list A)(ys:list B) :=
    List.map (fun xy => let '(x,y) := xy in f x y) (List.combine xs ys).

  Definition reduce_right {A:Type}(f: A->A->A)(dummy:A)(xs:list A): A :=
    match xs with
    | nil => dummy
    | x::xs => List.fold_right f x xs
    end.

  (* 改良版map_ext より強力*)
  Lemma map_ext' :forall (A B:Type)(f g:A->B) xs,
    (forall x, In x xs -> f x = g x) -> map f xs = map g xs.
  Proof.
   induction xs; [reflexivity|].
   intro H. simpl. f_equal.
   - apply H. now left.
   - apply IHxs. intros x Hin. apply H. now right.
  Qed.

  Lemma in_map_injective : forall (A B:Type) (f: A ->B)x (xs:list A),
    Image.injective _ _ f -> (In x xs <-> In (f x) (List.map f xs)).
  Proof.
   intros A B f x xs inj. induction xs.
   - now simpl.
   - simpl. rewrite <- IHxs. apply or_iff_compat_r. split.
     + intro eq. now rewrite eq.
     + now apply inj.
  Qed.   

  Lemma NoDup_map_injective : forall (A B:Type) (f: A ->B)(xs:list A),
    Image.injective _ _ f -> NoDup xs -> NoDup (List.map f xs).
  Proof.
   induction xs.
   - simpl. now constructor.
   - simpl. intros inj nodup. inversion nodup. subst. constructor.
     + now rewrite <- (in_map_injective).
     + now apply IHxs.
  Qed.

  Lemma nth_in_iff : forall (A:Type) (a:A) xs,
    In a xs <-> (exists i, nth_error xs i = Some a).
  Proof.
   induction xs as [|x xs].
   - split; [contradiction|]. intros H. destruct H as [i Hi]. now destruct i.
   - simpl. split.
     + intro Hl. destruct Hl.
       * exists 0. now rewrite H.
       * rewrite IHxs in H. destruct H as [i Hi]. now exists (S i).
     + intros Hr. destruct Hr as [i Hi]. destruct i; [left|right].
       * now injection Hi.
       * simpl in Hi. apply IHxs. now exists i.
  Qed.

  Lemma nth_error_in : forall (A : Type) (n : nat) (l : list A),
    n < length l -> exists x, List.nth_error l n = Some x.
  Proof.
   induction n.
   - destruct l; [now intros Hl|].
     intros Hl. now exists a.
   - destruct l; [now intros Hl|].
     simpl. intro Hl. apply IHn. now auto with arith.
  Qed.

  Lemma nth_error_in_iff : forall (A : Type) (n : nat) (l : list A),
    n < length l <-> exists x, List.nth_error l n = Some x.
  Proof.
   intros A n. split; [now apply nth_error_in|].
   revert l. induction n.
   - destruct l.
     + simpl. intro Hl. now destruct Hl.
     + simpl. intro Hl. now auto with arith.
   - destruct l.
     + simpl. intro Hl. now destruct Hl.
     + simpl. intro Hl. now auto with arith.
  Qed.

  Lemma Forall2_combine : forall (A B:Type)(P:A->B->Prop) xs ys,

    length xs = length ys ->
    (Forall2 P xs ys <-> Forall (fun xy => P (fst xy) (snd xy)) (combine xs ys)).
  Proof.
   intros A B P xs ys Hlen. split.
   - intro H. induction H.
     + now constructor.
     + constructor; [assumption|]. apply IHForall2. now injection Hlen.
   - remember(combine _ _) as xys. intro H. revert xs ys Hlen Heqxys. induction H as [|xy xys].
     + intros xs ys Hlen Heqxys. destruct xs as [|x xs], ys as [|y ys];
         try discriminate Heqxys; try discriminate Hlen.
       now constructor.
     + intros xs ys Hlen Heqxys. destruct xs as [|x xs], ys as [|y ys];
         try discriminate Heqxys; try discriminate Hlen.
       simpl in Heqxys. injection Heqxys. intros. subst.
       constructor; [assumption|].
       injection Hlen. intros. now apply IHForall.
  Qed.

End List.

Module Option.

  Definition get_or_else {A:Type}(dummy:A) (opt:option A) :=
    match opt with
    | None => dummy
    | Some x => x
    end.

  Definition eq_dec {A:Type}(a_eq_dec: forall a b:A, {a=b}+{a<>b}) (x y:option A) :  {x=y}+{x<>y}.
    refine (match x, y with
            | None, None => in_left
            | Some a, None => in_right
            | None, Some b => in_right
            | Some a, Some b =>
              if a_eq_dec a b then in_left else in_right
            end).
    - rewrite _H. reflexivity.
    - intro Heq. injection Heq. now auto.
    - discriminate.
    - discriminate.
    - reflexivity.
  Defined.

End Option.
