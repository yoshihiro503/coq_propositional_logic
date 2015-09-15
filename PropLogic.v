Require Import Program.
Require Import Lang.
Require Var Context.
Open Scope list_scope.

Inductive Term :=
| Var(v : Var.T)
| Neg(t : Term)
| And(t1: Term)(t2: Term)
| Or(t1: Term)(t2: Term)
| Impl(t1: Term)(t2: Term)
| TRUE | FALSE
.

Fixpoint eval ctx t : bool :=
  match t with
  | Var v => ctx v
  | Neg t => negb (eval ctx t)
  | And t1 t2 => andb (eval ctx t1) (eval ctx t2)
  | Or t1 t2 => orb (eval ctx t1) (eval ctx t2)
  | Impl t1 t2 => implb (eval ctx t1)(eval ctx t2)
  | TRUE => true
  | FALSE => false
  end.


Definition Equiv (P Q: Term) := forall context,
  eval context P = eval context Q.


Fixpoint collectVars t :=
  match t with
  | Var v => [v]
  | Neg t => collectVars t
  | And t1 t2 => collectVars t1 ++ collectVars t2
  | Or t1 t2 => collectVars t1 ++ collectVars t2
  | Impl t1 t2 => collectVars t1 ++ collectVars t2
  | TRUE => []
  | FALSE => []
  end.

Lemma eval_ctx : forall ctx ctx' t,
  (forall v, List.In v (collectVars t) -> ctx v = ctx' v) ->
  eval ctx t = eval ctx' t.
Proof.
 intros ctx ctx'.
 induction t; simpl.
 - intro H. apply H. now left.
 - intros H. f_equal. now apply IHt.
 - intros H. f_equal.
   + apply IHt1. intros v Hin. apply H. rewrite List.in_app_iff. now left.
   + apply IHt2. intros v Hin. apply H. rewrite List.in_app_iff. now right.
 - intros H. f_equal.
   + apply IHt1. intros v Hin. apply H. rewrite List.in_app_iff. now left.
   + apply IHt2. intros v Hin. apply H. rewrite List.in_app_iff. now right.
 - intros H. f_equal.
   + apply IHt1. intros v Hin. apply H. rewrite List.in_app_iff. now left.
   + apply IHt2. intros v Hin. apply H. rewrite List.in_app_iff. now right.
 - reflexivity.
 - reflexivity.
Qed.     


Lemma eval_ctx_from_key : forall ctx vs t key,
  key = Context.to_key vs ctx ->
  (forall v, List.In v (collectVars t) -> List.In v vs) ->
  eval ctx t = eval (Context.from_key vs key) t.
Proof.
 intros ctx vs t key Heq Hin. apply eval_ctx. intros v Hv.
 rewrite Heq. rewrite Context.from_key_to_key; [reflexivity|]. now apply Hin.
Qed.

(** * 真理値表への変換*)
Require TruthTable.
Import TruthTable.Op.
Module Map := TruthTable.Map.
Module MapProp := TruthTable.MapProp.
Require Mergesort Permutation.
Module VarSort := Mergesort.Sort Var.VarOrder.

(** ** 真理値表へ変換する *)

Require Import Sorting.
Definition sort vs := VarSort.sort vs.

Definition toVars (t:Term) :=
  sort (List.nub Var.T Var.eq_dec (collectVars t)).

Lemma Sorted_toVars : forall t, Sorted Var.lt (toVars t).
Admitted.

Lemma sort_in_iff : forall vs v,
  List.In v (VarSort.sort vs) <-> List.In v vs.
Proof.
 intros vs v. split.
 - apply Permutation.Permutation_in. apply Permutation.Permutation_sym.
   apply VarSort.Permuted_sort.
 - apply Permutation.Permutation_in.
   apply VarSort.Permuted_sort.
Qed.

Lemma toVars_in : forall t v,
  List.In v (toVars t) <-> List.In v (collectVars t).
Proof.
 intros t v. unfold toVars. rewrite sort_in_iff. now rewrite List.nub_In_iff.
Qed.

Definition toMap (t:Term) :=
  let vs := toVars t in
  List.map (fun key => (key, eval (Context.from_key vs key) t)) (TruthTable.allKeys (length vs))
  |> @MapProp.P.of_list bool.

Lemma toMap_In : forall key val t,
  Map.MapsTo key val (toMap t) ->
  length key = length (toVars t).
Proof.
 intros key val t Hmap. unfold toMap, revapply in Hmap.
(* rewrite MapProp.P.of_list_1 in Hmap.
Print TruthTable.Map.eq_key_elt.
Print Map.Raw.PX.eqke.
 rewrite TruthTable.InA_In in Hmap.

Print SetoidList.InA.
 apply Map.elements_1 in Hmap.
Check MapProp.P.of_list_2.
rewrite <- MapProp.P.of_list_2 in Hmap.
Print Module MapProp.P.*)
Admitted.

Lemma toMap_In_inv : forall key t,
  length key = length (toVars t) ->
  exists val,
    Map.MapsTo key val (toMap t).
Proof.
Admitted.


Definition toTable (t:Term) : TruthTable.T.
  refine (
    {|
      TruthTable.vars := toVars t
      ; TruthTable.map := toMap t
    |}
 ).
 (* Condition1: sorted vs *)
  apply Sorted_toVars.

 (* Condition2: length と HasContents *)
  intros key. split.
   intros HasCont. destruct HasCont as [v Hv].
   apply (toMap_In key v t). now apply Map.find_2.

   intros Hlen. destruct (toMap_In_inv _ _ Hlen) as [v Hv]. exists v.
   now apply Map.find_1.
Defined.

Lemma toTable_vars : forall t,
  (toTable t).(TruthTable.vars) = toVars t.
Proof.
 now unfold toTable.
Qed.
                       
Lemma toTable_map : forall t,
  (toTable t).(TruthTable.map) = toMap t.
Proof.
 now unfold toTable.
Qed.

(** ** 真理値表から変換する *)
Definition literal v (b:bool) :=
  if b then Var v else Neg(Var v).

Definition ofTable (table : TruthTable.T) : Term :=
  Map.elements table.(TruthTable.map) |> List.filter snd
  |> List.map fst
  |> List.map (fun bs => List.map2 literal table.(TruthTable.vars) bs)
  |> List.map (List.fold_right (And) TRUE)
  |> List.fold_right (Or) FALSE.

Lemma InA_In_elements : forall kv elems,
   SetoidList.InA (TruthTable.Map.eq_key_elt (elt:=bool)) kv elems <-> List.In kv elems.
Proof.
 intros kv elems. rewrite TruthTable.InA_In; [reflexivity|].
 apply TruthTable.eq_key_elt_leibniz.
Qed.

Lemma InA_eq_key_iff : forall k v kvs,
  SetoidList.InA (Map.eq_key (elt:=bool)) (k,v) kvs <-> List.In k (List.map fst kvs).
Proof.
 induction kvs.
 - simpl. now apply SetoidList.InA_nil.
 - simpl. rewrite SetoidList.InA_cons. rewrite IHkvs. apply or_iff_compat_r.
   unfold Map.eq_key. unfold Map.Raw.PX.eqk.
   now rewrite TruthTable.eqlistA_leibniz.
Qed.

Lemma keys_NoDup_with_eq_key : forall f keys,
  List.NoDup keys ->
  SetoidList.NoDupA (TruthTable.Map.eq_key (elt:=bool))
    (List.map (fun key => (key, f key)) keys).
Proof.
 intros f keys nodup. induction keys.
 - simpl. now constructor.
 - simpl. inversion nodup. subst. constructor.
   + rewrite InA_eq_key_iff. rewrite List.map_map. simpl.
     now rewrite List.map_id .
   + now apply IHkeys.
Qed.

(** ** 安全性のチェック *)

(** *** toTableの安全性 *)
Lemma safe_toTable : forall context term,
  Some (eval context term) = TruthTable.eval context (toTable term).
Proof.
 intros ctx t. unfold TruthTable.eval, revapply. apply eq_sym.
 apply MapProp.P.F.find_mapsto_iff. rewrite toTable_map, toTable_vars.
 unfold toMap, revapply.
 apply MapProp.P.of_list_1.
 (* NoDupの証明 *) - apply keys_NoDup_with_eq_key. apply TruthTable.allKeys_NoDup.
 (* Inの証明: 証明のメインストリーム *)
 - rewrite InA_In_elements.
   remember (toVars t) as vars. remember (Context.to_key vars ctx) as key. 
   remember (fun k => (k, eval (Context.from_key vars k) t)) as f.
(*   assert ((key, eval ctx t) = f key).*)
   assert (pair key (eval ctx t) = f key).
   + rewrite Heqf.
     replace (Context.from_key vars key) with
     (Context.from_key vars (Context.to_key vars ctx)); [|now rewrite Heqkey].
     f_equal. apply eval_ctx. intros v Hin.
     rewrite Context.from_key_to_key; [reflexivity|].
     rewrite Heqvars. now apply toVars_in.
   + set (List.in_map f (TruthTable.allKeys (length vars)) key) as in_map.
     rewrite <- H in in_map. apply in_map. rewrite <- TruthTable.allKeys_all.
     rewrite Heqkey. unfold Context.to_key. now apply List.map_length.
Qed.

(** *** ofTableの安全性 *)

Lemma in_literal_collectVars' : forall term ctx vars v,
  List.In term (List.map2 literal vars (Context.to_key vars ctx)) ->
  List.In v (collectVars term) -> List.In v vars.
Proof.
 induction vars.
 - now simpl.
 - simpl. intros v Hterm Hv. destruct Hterm as[Hhd|Htl].
   + left. unfold literal in Hhd. cut(collectVars term = [a]).
     * intro Hcoll. rewrite Hcoll in Hv. now destruct Hv.
     * destruct (ctx a); now rewrite <- Hhd.
   + right. apply IHvars; [|assumption]. now unfold List.map2.
Qed.

Lemma in_literal_collectVars : forall term vars key v,
  length key = length vars ->
  List.In term (List.map2 literal vars key) ->
  List.In v (collectVars term) -> List.In v vars.
Proof.
 induction vars.
 - now simpl.
 - intros key v Hlen. destruct key as [|b bs]; [discriminate Hlen|].
   simpl. intros Hterm Hv. destruct Hterm as [Hhd|Htl].
   + left. unfold literal in Hhd. cut(collectVars term = [a]).
     * intro Hcoll. rewrite Hcoll in Hv. now destruct Hv.
     * destruct b; now rewrite <- Hhd.
   + right. apply (IHvars bs); [| |assumption].
     * now injection Hlen.
     * now unfold List.map2.
Qed.

Lemma eval_literal_true : forall vars key term,
  List.NoDup vars -> length key = length vars ->
  List.In term (List.map2 literal vars key) ->
    eval (Context.from_key vars key) term = true.
Proof.
 intros vars key term Hnodup Hlen Hin. unfold List.map2 in Hin.
 rewrite List.in_map_iff in Hin. destruct Hin as [vb Hvb].
 destruct vb as [v b]. destruct Hvb as [Hvb1 Hvb2]. rewrite <- Hvb1.
 destruct b.
 - simpl. now apply Context.from_key_combine.
 - simpl. now rewrite (Context.from_key_combine _ _ _ false).
Qed.

Lemma eval_literal_false_aux : forall vars v b key b' key',
  List.NoDup vars -> length key = length vars -> length key' = length vars ->
  b <> b' -> List.In (v, b) (List.combine vars key) ->
  List.In (v, b') (List.combine vars key') ->
  exists term,
  List.In term (List.map2 literal vars key) /\
    eval (Context.from_key vars key') term = false.
Proof.
 intros vars v b key b' key' Hnodup Hlen Hlen' Hneq Hin Hin'.
 exists (literal v b). split.
 - unfold List.map2.
   set (List.in_map (fun xy => let '(x,y):=xy in literal x y) (List.combine vars key) (v, b) Hin) as Hin_map.
   now simpl in Hin_map.
 - destruct b, b'; simpl; try (elim Hneq; reflexivity).
   + now apply Context.from_key_combine.
   + now rewrite (Context.from_key_combine _ _ _ true).
Qed.

Lemma eval_literal_false : forall vars key key',
  List.NoDup vars -> length key = length vars -> length key' = length vars ->
  key <> key' -> exists term,
  List.In term (List.map2 literal vars key) /\
    eval (Context.from_key vars key') term = false.
Proof.
 intros vars key key' Hnodup Hlen Hlen' Hneq.
 rewrite <- TruthTable.eqlistA_leibniz in Hneq; [| reflexivity].
 rewrite SetoidList.eqlistA_altdef in Hneq.
 rewrite List.Forall2_combine in Hneq; [|now rewrite Hlen, Hlen'].
 destruct(List.Forall_dec' (fun xy => Bool.bool_dec (fst xy)(snd xy))(List.combine key key')).
 - contradiction.
 - rewrite List.Exists_exists in e. destruct e as [bb' Hbb'].
   destruct bb' as [b b']. destruct Hbb' as [Hbb'1 Hbb'2].
   rewrite List.nth_in_iff in Hbb'1. destruct Hbb'1 as [i Hi].
   rewrite List.combine_nth_error in Hi; [|now rewrite Hlen, Hlen'].
   destruct Hi as [Hi1 Hi2].
   destruct (List.nth_error_in _ i vars) as [v Hv];
     [rewrite <- Hlen; apply List.nth_error_in_iff; now exists b|].
   apply (eval_literal_false_aux vars v b key b' key'); try assumption.
   + apply List.nth_in_iff. exists i.
     now apply List.combine_nth_error; [now rewrite Hlen|split].
   + apply List.nth_in_iff. exists i.
     now apply List.combine_nth_error; [now rewrite Hlen'|split].
Qed.

Lemma eval_fold_Or_true : forall ctx terms,
  (exists tm, List.In tm terms /\ eval ctx tm = true) <->
  eval ctx (List.fold_right Or FALSE terms) = true.
Proof.
 intros ctx terms. induction terms.
 - simpl. now split; [intro Htm; destruct Htm|].
 - simpl. split.
   + intro Htm. destruct Htm as [tm Htm]. destruct Htm as [Htm1 Htm2].
     destruct Htm1; [now rewrite H, Htm2|]. destruct IHterms as [IH1 _].
     rewrite IH1; [now apply Bool.orb_true_r | ]. exists tm. now split.
   + case_eq (eval ctx a).
     * intros Ha _. exists a. now split; [left|].
     * intros _ Heval. rewrite Bool.orb_false_l in Heval.
       destruct IHterms as [_ IH2]. destruct (IH2 Heval) as [tm Htm].
       destruct Htm as [Htm1 Htm2]. exists tm. now split; [right|].
Qed.

Lemma eval_fold_Or_false : forall ctx terms,
  (forall tm, List.In tm terms -> eval ctx tm = false) <->
  eval ctx (List.fold_right Or FALSE terms) = false.
Proof. Admitted.

Lemma eval_fold_And_true : forall ctx terms,
  (forall tm, List.In tm terms -> eval ctx tm = true) <->
  eval ctx (List.fold_right And TRUE terms) = true.
Proof. Admitted.

Lemma eval_fold_And_false : forall ctx terms,
  (exists tm, List.In tm terms /\ eval ctx tm = false) <->
  eval ctx (List.fold_right And TRUE terms) = false.
Proof. Admitted.

Lemma TruthTable_NoDup_vars : forall tbl, List.NoDup tbl.(TruthTable.vars).
Proof.
 intro tbl. rewrite <- TruthTable.NoDupA_NoDup.
 now apply (TruthTable.OrderedTypeVarList.Sort_NoDup tbl.(TruthTable.Condition1)).
Qed.

Lemma TruthTable_key_length : forall key val tbl,
  List.In (key, val) (Map.elements tbl.(TruthTable.map)) ->
  length key = length tbl.(TruthTable.vars).
Proof.
 intros key val tbl Hin. apply (tbl.(TruthTable.Condition2) key).
 unfold TruthTable.Map_HasContents. exists val.
 apply MapProp.P.F.find_mapsto_iff. apply Map.elements_2.
 now apply InA_In_elements.
Qed.

Lemma safe_ofTable : forall context table,
  TruthTable.eval context table = Some (eval context (ofTable table)).
Proof.
 intros ctx tbl.
 remember(TruthTable.eval ctx tbl) as result.
 remember (Context.to_key (TruthTable.vars tbl) ctx) as key.  destruct (result).
 remember (TruthTable.vars tbl) as vars.
 (* T.eval ctx tbl = Some b のとき *)
 - f_equal. unfold ofTable, revapply. apply eq_sym. destruct b.
   (* b = true  のとき *)
   + apply eval_fold_Or_true.
     exists(List.fold_right And TRUE (List.map2 literal vars key)).
     split.
      (* Inを示す *)
      * rewrite <- Heqvars.
        apply List.in_map. apply List.in_map. rewrite List.in_map_iff.
        exists (key, true). split; [reflexivity|]. rewrite List.filter_In.
        split; [|reflexivity]. apply InA_In_elements. apply Map.elements_1.
        apply MapProp.P.F.find_mapsto_iff.
        unfold TruthTable.eval in Heqresult. rewrite Heqkey. now rewrite Heqvars.
      (* eval ctx (fold And ...) = true をしめす *)
      * {
          apply eval_fold_And_true. intros tm Htm.
          rewrite (eval_ctx_from_key _ (vars) _ key); [|assumption|].
          - apply eval_literal_true; [| | assumption].
            + rewrite Heqvars. now apply TruthTable_NoDup_vars.
            + rewrite Heqkey. now apply Context.to_key_length.
          - intros v Hv.
            apply (in_literal_collectVars tm _ key); [| assumption|assumption].
            rewrite Heqkey. unfold Context.to_key. now apply List.map_length.
        }
   (* b = false のとき *)
   + apply eval_fold_Or_false. intros tm Htm.
     rewrite List.in_map_iff in Htm. destruct Htm as [tms Htms].
     destruct Htms as [Htms1 Htms2]. rewrite <- Htms1.
     apply eval_fold_And_false.
     rewrite List.in_map_iff in Htms2. destruct Htms2 as [key' Hkey'].
     destruct Hkey' as [Hkey'1 Hkey'2]. rewrite <- Hkey'1.
     destruct (eval_literal_false vars key' key) as [tm' Htm'].
     * rewrite Heqvars. now apply TruthTable_NoDup_vars.
     * rewrite Heqvars. rewrite List.in_map_iff in Hkey'2.
       destruct Hkey'2 as [kb Hkb]. destruct kb as [k' val].
       destruct Hkb as [Hkb1 Hkb2]. apply TruthTable_key_length with (val:=val).
       subst. now rewrite List.filter_In in Hkb2.
     * rewrite Heqkey. now apply Context.to_key_length.
     * rewrite List.in_map_iff in Hkey'2. destruct Hkey'2 as [k'v Hk'v].
       destruct k'v as [k' v]. simpl in Hk'v. destruct Hk'v as [Hk'v1 Hk'v2].
       subst k'. rewrite List.filter_In in Hk'v2. simpl in Hk'v2.
       destruct Hk'v2 as [H1 H2]. subst v.
       rewrite<- InA_In_elements in H1. apply Map.elements_2 in H1.
       rewrite MapProp.P.F.find_mapsto_iff in H1.
       unfold TruthTable.eval in Heqresult. intro Heq. rewrite Heq in H1.
       revert Heqresult. rewrite <- Heqvars. rewrite<- Heqkey.
       rewrite H1. discriminate.
     * {
         exists tm'. destruct Htm' as [Htm'1 Htm'2]. split.
         - now rewrite <- Heqvars.
         - rewrite (eval_ctx_from_key _ vars _ key Heqkey); [assumption |].
           intros v Hv.
           apply (in_literal_collectVars tm' vars key');
             [|assumption|assumption].
           rewrite Heqvars.
           rewrite List.in_map_iff in Hkey'2. destruct Hkey'2 as [k'v Hk'v].
           destruct k'v as [k' val]. simpl in Hk'v. destruct Hk'v as [H1 H2].
           subst k'. rewrite List.filter_In in H2.
           now apply TruthTable_key_length with (val:=val).
       }
 (* T.eval ctx tbl = None のとき -> 矛盾 *)
 - unfold TruthTable.eval in Heqresult. rewrite <- Heqkey in Heqresult.
   set (tbl.(TruthTable.Condition2) key) as Hcond.
   destruct Hcond as [_ Hcondr].
   destruct Hcondr.
   + rewrite Heqkey. now apply Context.to_key_length.
   + rewrite H in Heqresult. now apply eq_sym in Heqresult.
Qed.

Lemma lem_ofTable : forall table1 table2,
  table1 == table2 -> ofTable table1 = ofTable table2.
Proof.
 intros table1 table2 H.
 destruct H as [EqVars EqualMap].
 apply TruthTable.Map_EquivEq in EqualMap.
 unfold TruthTable.MapProp.P.to_list in EqualMap.
 (*elementsの結果が等しいことが得られた。 ofTableはelementsを使ってゴニョゴニョするのでOK*)
 unfold ofTable. do 2 f_equal. rewrite EqualMap. do 2 f_equal.
 rewrite EqVars. reflexivity.
Qed.


(** * 標準形にする関数の定義 *)
Definition nf (t : Term) : Term :=
  toTable t
  |> TruthTable.elimVars
  |> ofTable.

(** * 3.1の証明 *)
Theorem soundness_nf : forall t, Equiv t (nf t).
Proof.
 intros t. unfold Equiv. intros ctx. unfold nf, revapply.
 assert (Some (eval ctx t) = Some (eval ctx (ofTable (TruthTable.elimVars (toTable t))))).
 - rewrite <- safe_ofTable. rewrite <- TruthTable.soundness.
   now apply safe_toTable.
 - now injection H.
Qed.

(** * 3.2の証明
   PとQが同値であればnf(P)とnf(Q)は形が全く等しい命題論理式である
 *)
Theorem main : forall P Q: Term, Equiv P Q -> nf P = nf Q.
Proof.
 intros. unfold nf, revapply.
 apply lem_ofTable.
 apply (TruthTable.uniqueness (toTable P) (toTable Q)).
 intro context. do 2 rewrite <- safe_toTable.
 unfold Equiv in H. now rewrite H.
Qed.  



Module Sample.
(*
  Notation P := (Var 0).
  Notation Q := (Var 1).

  Definition term' := And P (Neg Q).
  Definition term := Or P (Neg Q).

  Definition map := (toMap term).
  Definition vars := toVars term.

  Compute collectVars term.
  Definition ctx := (fun v => match v with 0 => true | 1 => false | _ => false end).
  Compute eval ctx term.
  Compute TruthTable.allKeys 3.
  Definition key := List.nth 0 (TruthTable.allKeys 2) [].
  Compute eval (Context.from_key vars key) term.
  Compute toMap term.
  Definition tbl := toTable term.

  Compute (TruthTable.elimVars (toTable (Or P (Neg P)))). (*恒真*)
  Compute (TruthTable.elimVars (toTable (And P (Neg P)))). (*恒偽*)
  Compute (nf (Or P (Neg P))). (*恒真*)
  Compute (nf (And P (Neg P))). (*恒偽*)
*)
End Sample.
