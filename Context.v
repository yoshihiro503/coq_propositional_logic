Require Import Lang.
Require Var.

Definition T :=  Var.T -> bool.

Definition update a (b:bool) ctx :=
  fun x => if Var.eq_dec x a then b else ctx x.

Definition Equal (x y: T) :=
  forall v, x v = y v.

Module Op.
  Infix "==" := Equal (at level 70, right associativity).
End Op.
Import Op.

Lemma update_eq : forall a b ctx,
  (update a b ctx) a = b.
Proof.
 intros a b ctx. unfold update. destruct (Var.eq_dec a a); [now idtac| now elim n].
Qed.
Lemma update_neq : forall a b ctx x,
  x<>a -> (update a b ctx) x = ctx x.
Proof.
 intros a b ctx x Hneq. unfold update. now destruct (Var.eq_dec x a).
Qed.

Lemma map_update_notincl : forall x b ctx vs,
  ~ List.In x vs ->
  List.map (update x b ctx) vs = List.map ctx vs.
Proof.
 induction vs.
 - simpl. reflexivity.
 - simpl. intros Hnincl. destruct (Decidable.not_or _ _ Hnincl) as [neq notin].
   rewrite update_neq; [|now apply neq]. f_equal. now apply IHvs.
Qed.

Lemma map_update_replace_i : forall a y ctx xs idx,
  List.index_of Var.eq_dec a xs = Some idx ->
  List.NoDup xs ->
  List.map (update a y ctx) xs = List.replace_i idx y (List.map ctx xs).
Proof.
 induction xs.
 (*nil*)
 - simpl. intros idx HidxOf HNoDup. now destruct idx.

 (*cons*)
 - intros idx HidxOf HNoDup. simpl. rename a0 into x.
   destruct (Var.eq_dec a x) as [Heq|Hneq].
   (* a = x *)
   + rewrite Heq in HidxOf. rewrite Heq. rewrite List.index_of_hd in HidxOf.
     injection HidxOf as Hidx. rewrite<- Hidx. simpl.
     unfold update at 1. destruct (Var.eq_dec x x) as [Hxx|Hxx]; [|now elim Hxx].
     f_equal. apply map_update_notincl. now inversion HNoDup.

  (* a <> x *)
   + remember (List.index_of Var.eq_dec a xs) as idxopt.
     destruct idxopt as [idx'|].
     (*Some idx'*)
     * unfold update at 1. destruct (Var.eq_dec x a) as [Hxa|_]; [now elim Hneq|].
       rewrite (List.index_of_tl_Some _ _ _ _ idx' Hneq) in HidxOf; [|now auto].
       injection HidxOf as Hidx. rewrite <- Hidx.
       simpl. f_equal. apply IHxs; [reflexivity|]. now inversion HNoDup.

     (*None*)
     * rewrite List.index_of_tl_None in HidxOf; [discriminate| now idtac| now idtac].
Qed.

Definition to_key (vs:list Var.T)(ctx : T) : list bool :=
  List.map ctx vs.

Definition from_key (vs:list Var.T)(key : list bool) : T :=
  let dummy := false in
  fun v => match List.index_of Var.eq_dec v vs with
  | None => dummy
  | Some i => List.nth i key dummy
  end.

Lemma from_key_to_key : forall (vs: list Var.T) (ctx : T) v,
  List.In v vs ->
  from_key vs (to_key vs ctx) v = ctx v.
Proof.
 induction vs.
 - simpl. contradiction.
 - simpl. intros ctx v Hor. unfold from_key. destruct (Var.eq_dec a v).
   + rewrite e. rewrite List.index_of_hd. reflexivity.
   + simpl. rewrite <- (IHvs ctx v); [|now destruct Hor].
     unfold from_key. case_eq (List.index_of Var.eq_dec v vs).
     * intros i Hi. rewrite (List.index_of_tl_Some _ _ _ _ i); now auto.
     * intros Heq. rewrite List.index_of_tl_None; now auto.
Qed.

Lemma to_key_same : forall vs ctx ctx',
  (forall v, List.In v vs -> ctx v = ctx' v) ->
  to_key vs ctx = to_key vs ctx'.
Proof.
 unfold to_key. intros vs ctx ctx' H. now apply List.map_ext'.
Qed.

Lemma map_from_key : forall key vs,
  List.NoDup vs -> length key = length vs ->
  List.map (from_key vs key) vs = key.
Proof.
 intros key vs. revert key.
 induction vs.
  simpl. now destruct key.

  simpl. unfold from_key at 1. simpl. rewrite List.index_of_hd.
  intro key. destruct key as [|b key']; [now auto|].
  intros HNoDup Hlen. injection Hlen. intro Hlen'. simpl. f_equal.
  unfold from_key. inversion HNoDup. subst.
  rewrite <- IHvs; [ |assumption |assumption].
  apply List.map_f_g_eq. intros v Hv. unfold from_key.
  destruct (Var.eq_dec v a) as [Heq|Hneq]; [rewrite Heq in Hv; contradiction| ].
  remember (List.index_of Var.eq_dec v vs) as opt.
  destruct opt as [idx|].
   rewrite (List.index_of_tl_Some) with (i := idx); [ |assumption|now rewrite Heqopt].
   simpl. reflexivity.
   
   now rewrite (List.index_of_tl_None Var.eq_dec _ _ _ Hneq).
Qed.

Lemma from_key_combine : forall vs key v b,
  List.NoDup vs -> length key = length vs ->
  List.In (v, b) (List.combine vs key) ->
  (from_key vs key) v = b.
Proof.
 intros vs key v b Hnodup Hlen Hin.
 rewrite  List.nth_in_iff in Hin. destruct Hin as [i Hi].
 unfold from_key. 
 rewrite (List.combine_nth_error) in Hi; [| now rewrite Hlen].
 destruct Hi as [Hi1 Hi2].
 destruct (List.index_of_nth_iff Var.eq_dec v vs i Hnodup)as [_ Hr].
 rewrite (Hr Hi1). rewrite <- List.nth_default_eq. unfold List.nth_default.
 now rewrite Hi2.
Qed.

Lemma to_key_length : forall vars key,
  length (to_key vars key) = length vars.
Proof.
 intros. now apply List.map_length.
Qed.