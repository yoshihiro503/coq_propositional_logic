Require Import Sorted Lang Program.
Import Lang.List.
Require Import FMapList OrderedType FMapFacts.
Require Var Context BoolOrderedType ListOrderedType.

Module BO <: OrderedType := BoolOrderedType.
Module BoolListOrdered <: OrderedType := ListOrderedType.Make BO.
Module KOTnat := OrdersLists.KeyOrderedType NPeano.Nat.
Module OrderedTypeVarList := OrdersLists.OrderedTypeLists Var.OT.

Module Map := FMapList.Make BoolListOrdered.
Module MapProp := FMapFacts.OrdProperties Map.

(** * Utils *)
Definition Map_HasContents bs map : Prop :=
  exists b:bool, Map.find bs map = Some b.

(* Map のkeyを変換する *)
Definition Map_mapKeys {V:Type}(f : list bool -> list bool)(map : Map.t V) :=
  Map.elements map
  |> List.map (fun kv => let '(key, val) := kv in (f key, val))
  |> @MapProp.P.of_list V.

Lemma Map_mapKeys_HasContents : forall key map f,
  Map_HasContents key map <-> Map_HasContents (f key) (Map_mapKeys f map).
Proof.
 intros key map f.
 unfold Map_mapKeys.
 unfold revapply.
 (*がんばればできる？ 補題elements_HasContents, of_list_HasContentsが必要? *)
Admitted.

Lemma Map_In_elements_HasContents : forall key val map,
  In (key, val) (Map.elements map) -> Map_HasContents key map.
Proof.
 intros.
 unfold Map_HasContents. exists val.
 unfold Map.find, Map.Raw.find.
 apply Map.find_1.
 apply Map.elements_2.
 apply In_InA; [|assumption].
 apply MapProp.P.eqke_equiv.
Qed.

Lemma Map_mapKeys_Equal : forall map f,
  (forall key, Map_HasContents key map -> f key = key) ->
  Map.Equal (Map_mapKeys f map) map.
Proof.
 intros map f H. unfold Map.Equal. intro key.
 unfold Map_mapKeys. unfold revapply.
 rewrite map_eq.
  set (MapProp.P.of_list_3 map) as Hequal.
  now rewrite Hequal.

  intros key_value HIn. destruct key_value as [k v].
  rewrite H; [reflexivity|].
  now apply Map_In_elements_HasContents with (val := v).
Qed.

Lemma Map_Equal_HasContents_iff : forall map1 map2,
  Map.Equal map1 map2 ->
  forall key, Map_HasContents key map1 <-> Map_HasContents key map2.
Proof.
  intros map1 map2 Hequal key. unfold Map_HasContents. now rewrite (Hequal key).
Qed.

Lemma Map_find_mapKeys: forall (V:Type) (f:Map.key -> Map.key) key' (v:V) map,
  Map.find key' (Map_mapKeys f map) = Some v ->
  exists key, key' = f key /\ Map.find key map = Some v.
Proof.
 intros V f key' v map Hfind.
 (*TODOがんばるぞぉ Map_mapKeys_HasContentsと似てる？ *)
Admitted.

Lemma InA_In : forall (A:Type) equiv (x:A)(xs:list A),
  (forall x y:A, equiv x y <-> x = y) ->
  (InA equiv x xs <-> In x xs).
Proof.
 split.
 - intro HH. induction HH.
   + rewrite H in H0. rewrite H0. now constructor.
   + now right.
 - intro HH. induction xs; [inversion HH|].
   destruct HH.
   + rewrite H0. constructor. now apply H.
   + apply InA_cons_tl. now apply IHxs.
Qed.

Lemma InA_In_eq : forall (A:Type) (x:A)(xs:list A),
  InA eq x xs <-> In x xs.
Proof.
 intros A x xs. now apply InA_In.
Qed. 

Lemma eqlistA_leibniz : forall (A:Type) (xs ys:list A) equiv,
  (forall (x y:A), equiv x y <-> x = y) ->
  (eqlistA equiv xs ys <-> xs = ys).
Proof.
 intros A xs ys equiv H. rewrite eqlistA_altdef. split.
 (* -> *)
 - revert ys. induction xs as [|x xs]; intros ys HH; [now inversion HH|].
   destruct ys as[|y ys]; [now inversion HH|].
   inversion HH. subst. rewrite H in H3. rewrite H3. f_equal. now apply IHxs.
 (* <- *)
 - revert ys. induction xs.
   + intros ys Heq. rewrite <- Heq. now constructor.
   + intros ys Heq. rewrite <- Heq. constructor; [now apply H|]. now apply IHxs.
Qed.

Lemma eq_key_elt_leibniz : forall kv kv',
  Map.eq_key_elt (elt:=bool) kv kv' <-> kv = kv'.
Proof.
 intros kv kv'.
 unfold Map.eq_key_elt. unfold Map.Raw.PX.eqke.
 rewrite eqlistA_leibniz.
 - destruct kv, kv'. simpl. split.
   + intro H. destruct H. now subst.
   + intro H. injection H. now auto.
 - reflexivity.
Qed.

Lemma NoDupA_NoDup : forall (A:Type) (xs:list A),
  NoDupA eq xs <-> NoDup xs.
Proof.
 split.
  intro H. induction H; [now constructor|].
  apply NoDup_cons; [|assumption].
  now rewrite InA_In in H.

  intro H. induction H; [now constructor|].
  apply NoDupA_cons; [|assumption].
  now rewrite InA_In.
Qed.

Lemma remove_i_HdRel : forall (A:Type) (lt:A->A->Prop) i xs a,
  StrictOrder lt ->
  Sorted lt xs -> HdRel lt a xs -> HdRel lt a (remove_i i xs).
Proof.
 destruct i.
 - simpl. destruct xs; [auto|]. intros b strict sorted Hb. inversion Hb. subst.
   inversion sorted. subst.
   now apply (InfA_ltA strict H0 H3).

 - intros xs a strict sorted Ha. simpl. destruct xs; [auto|].
   constructor. now inversion Ha.
Qed.

Lemma remove_i_sorted : forall (A:Type) (lt:A->A->Prop) i xs,
  StrictOrder lt -> Sorted lt xs -> Sorted lt (remove_i i xs).
Proof.
 induction i.
 (* i = 0のとき *)
 - simpl. destruct xs; [auto|].
   intros strict sorted. now inversion sorted.
 (* i = S kのとき *)
 - simpl. destruct xs; [auto|].
   intros strict sorted. inversion sorted. subst.
   constructor.
   + now apply IHi.
   + now apply remove_i_HdRel.
Qed.

(* 真偽値表 *)

Record T : Type := {
  vars : list Var.T
  ; map : Map.t bool (* list bool |-> bool の有限map *)
  ; Condition1 : Sorted Var.lt vars
  ; Condition2 : forall bs, Map_HasContents bs map <-> length bs = length vars
}.

Definition eval context table :=
  let key := Context.to_key table.(vars) context in
  Map.find key table.(map).

Lemma eval_ctx : forall ctx ctx' tbl,
  (forall v, In v tbl.(vars) -> ctx v = ctx' v) ->
  eval ctx tbl = eval ctx' tbl.
Proof.
 intros ctx ctx' tbl H.
 unfold eval. f_equal. now apply Context.to_key_same.
Qed.

Lemma eval_update_notincl : forall tbl v b ctx,
  ~ In v tbl.(vars) ->
  eval (Context.update v b ctx) tbl = eval ctx tbl.
Proof.
 intros tbl v b ctx Notincl.
 unfold eval, revapply. (*List.mapが変わらないことを使えばできそう*)
 f_equal. unfold Context.to_key. now rewrite Context.map_update_notincl.
Qed.

Definition Equal x y :=
  x.(vars) = y.(vars) /\ Map.Equal x.(map) y.(map).

Module Op.
  Infix "==" := Equal (at level 70, right associativity).
End Op.
Import Op.

Definition sameSemantics (x y: T) := forall context, 
  eval context x = eval context y.

Lemma refl_sameSemantics : forall x, sameSemantics x x.
Proof.
 now auto.
Qed.

Lemma symm_sameSemantics : forall x y,
  sameSemantics x y -> sameSemantics y x.
Proof.
 intros x y. unfold sameSemantics. intros H ctx. now rewrite H.
Qed.

Lemma trans_sameSemantics : forall x y z,
  sameSemantics x y -> sameSemantics y z -> sameSemantics x z.
Proof.
 unfold sameSemantics. intros x y z H1 H2 ctx. now rewrite H1.
Qed.

Fixpoint allKeys n :=
  match n with
  | 0 => nil::nil
  | S p => List.map (cons true) (allKeys p)
           ++ List.map (cons false) (allKeys p)
  end.
Lemma allKeys_all : forall bs n, length bs = n <-> In bs (allKeys n).
Proof.
 split.
  (*->*)
  revert bs. induction n.
   destruct bs; [now left|discriminate].

   simpl. destruct bs; [discriminate|]. simpl. intro Hlen. injection Hlen as Hlen'.
   rewrite in_app_iff. destruct b; [left | right].
    apply in_map. now apply IHn.

    apply in_map. now apply IHn.
  (*<-*)
  revert bs. induction n.
   destruct bs; [reflexivity| ].
   simpl. intro H. destruct H; [discriminate|contradiction].

   destruct bs.
    simpl. intro H_In. rewrite in_app_iff in H_In. destruct H_In.
     rewrite in_map_iff in H. destruct H. destruct H. discriminate H.

     rewrite in_map_iff in H. destruct H. destruct H. discriminate H.

    simpl. rewrite in_app_iff. intros H_In. f_equal. apply IHn.
    destruct H_In.
     rewrite in_map_iff in H. destruct H as [bs']. destruct H as [Hbs1 Hbs2].
     injection Hbs1 as eqbs _. now rewrite eqbs in Hbs2.

     rewrite in_map_iff in H. destruct H as [bs']. destruct H as [Hbs1 Hbs2].
     injection Hbs1 as eqbs _. now rewrite eqbs in Hbs2.
Qed.    

Lemma allKeys_NoDup : forall n, NoDup (allKeys n).
Proof.
 (* なぜかList.NoDupよりも SetoidList.NoDupAの方が補題が充実しているのでそっちで。 *)
 intro n. rewrite <- NoDupA_NoDup. induction n.
 - simpl. apply NoDupA_singleton.
 - simpl. apply NoDupA_app; [now auto| | |].
   + inversion IHn; [now constructor|]. rewrite NoDupA_NoDup.
     apply List.NoDup_map_injective.
     * intros xs ys. intro HH. now injection HH.
     * constructor; [|now apply NoDupA_NoDup]. intro Hin. elim H0. now apply InA_In.
   + inversion IHn; [now constructor|]. rewrite NoDupA_NoDup.
     apply List.NoDup_map_injective.
     * intros xs ys. intro HH. now injection HH.
     * constructor; [|now apply NoDupA_NoDup]. intro Hin. elim H0. now apply InA_In.
   + intros key. do 2 rewrite InA_In_eq. do 2 rewrite in_map_iff.
     intros Hl Hr. destruct Hl as [xs Hxs]. destruct Hr as [ys Hys].
     destruct Hxs, Hys. rewrite <- H in H1. discriminate H1.
Qed.

Definition RedundantVar v tbl :=
  forall b ctx, eval (Context.update v b ctx) tbl = eval ctx tbl.
Definition redundantVar_dec : forall v tbl,
  {RedundantVar v tbl} + {~RedundantVar v tbl}.
 intros v tbl.
 remember ((index_of Var.eq_dec v tbl.(vars)) |> (Option.get_or_else (length tbl.(vars)))) as idx'.
 remember (length tbl.(vars)) as len.
 refine (if
   List.Forall_dec' (fun key =>
     Option.eq_dec BO.eq_dec 
       (Map.find (replace_i idx' true  key) tbl.(map))
       (Map.find (replace_i idx' false key) tbl.(map))
   ) (allKeys len)
   then in_left
   else _).

 (*left*)
 remember (List.index_of Var.eq_dec v (vars tbl)) as idxOf.
 destruct idxOf as [idx|].
  (*index_of ... = Some idx*)
  unfold revapply in Heqidx'. simpl in Heqidx'. subst idx'.
  set (OrderedTypeVarList.Sort_NoDup tbl.(Condition1)) as HNoDup.
  rewrite NoDupA_NoDup in HNoDup.
  unfold RedundantVar. intros b ctx. unfold eval, revapply.
  unfold Context.to_key.
  rewrite (Context.map_update_replace_i _ _ _ _ idx); [|now idtac |assumption].
  remember (List.map ctx (vars tbl)) as key.
  destruct (List.replace_i_invaliant _ idx key true).
  rewrite Forall_forall in _H. assert (In key (allKeys len)).
   apply allKeys_all. rewrite Heqkey. now rewrite map_length.

   set (_H key H0). rewrite <- H at 2. now destruct b, x.

  (*index_of ... = None*)
  unfold revapply in Heqidx'. simpl in Heqidx'.
  unfold RedundantVar. intros b ctx. apply eval_update_notincl.
  now apply (index_of_In_None Var.eq_dec).

 (*right*)
 remember (List.index_of Var.eq_dec v (vars tbl)) as idxOf.
 destruct idxOf as [idx|].
  (*index_of ... = Some idx*)
  apply right.
  unfold revapply in Heqidx'. simpl in Heqidx'. subst idx'.

  set (OrderedTypeVarList.Sort_NoDup tbl.(Condition1)) as HNoDup.
  rewrite NoDupA_NoDup in HNoDup.

  rewrite Exists_exists in _H. destruct _H as [key]. destruct H as[HKey1 HKey2].
  unfold RedundantVar, eval, revapply.
  destruct (tbl.(Condition2) key) as[_ HasCont].
  rewrite allKeys_all in HasCont. rewrite <- Heqlen in HasCont.
  destruct (List.replace_i_invaliant _ idx key true) as [x Hx].
  remember (Context.from_key tbl.(vars) key) as ctx.
  intro RV. set (RV (negb x) ctx) as RVkey.
  unfold Context.to_key in RVkey.
  rewrite (Context.map_update_replace_i _ _ _ _ idx) in RVkey; [|now idtac|assumption].
  rewrite Heqctx in RVkey.
  rewrite Context.map_from_key in RVkey.
   rewrite <- Hx in RVkey at 2.
   elim HKey2. now destruct x.
   rewrite <- NoDupA_NoDup.
   apply (OrderedTypeVarList.Sort_NoDup tbl.(Condition1)).

   rewrite allKeys_all. now rewrite <- Heqlen.

  (*index_of ... = None*)
  apply left.
  unfold revapply in Heqidx'. simpl in Heqidx'.
  unfold RedundantVar. intros b ctx. apply eval_update_notincl.
  now apply (index_of_In_None Var.eq_dec).
Defined.

Lemma redundant_same : forall tbl1 tbl2,
  sameSemantics tbl1 tbl2 -> forall v, RedundantVar v tbl1 <-> RedundantVar v tbl2.
Proof.
 intros tbl1 tbl2 same v.
 unfold RedundantVar.
 split; intros H b ctx; [now do 2 rewrite <- same | now do 2 rewrite same].
Qed.
(*
Definition remove_var_ (v : Var.T) (tbl:T)(idx:nat)(eqidx : index_of Var.eq_dec v tbl.(vars) = Some idx) : T.
  refine ({|
      vars := List.remove_i idx tbl.(vars)
      ; map := Map_mapKeys (fun bs => List.remove_i idx bs) tbl.(map)
    |}).
    (* Cond1: Sortedなことの証明 *)
    apply remove_i_sorted; [now apply Var.OT.lt_strorder|].
    now apply tbl.(Condition1).
   
    (* Cond2: lengthが等しいことの証明 *)
    remember (Map_mapKeys _ _) as tbl'. intros bs'.
    remember (List.insert_i idx true bs') as bs.
    rewrite <- (List.remove_i_insert_i _ idx true bs').
    rewrite <- Heqbs. rewrite Heqtbl'.
    rewrite <- Map_mapKeys_HasContents.
    rewrite tbl.(Condition2).
    split; [apply List.length_remove_i|].

    remember (remove_i idx (vars tbl)) as vs'.
    remember (List.insert_i idx v vs') as vs.
    rewrite Heqbs.
    rewrite remove_i_insert_i.
    rewrite<- (insert_i_remove_i Var.T Var.eq_dec idx v (vars tbl) eqidx).
    rewrite <- Heqvs'.
    now apply List.length_insert_i.
Defined.
*)
Definition remove_var (v : Var.T) (tbl:T) : T.
 remember ((index_of Var.eq_dec v tbl.(vars)) |> (Option.get_or_else (length tbl.(vars)))) as idx.
 refine ({|
      vars := List.remove_i idx tbl.(vars)
      ; map := Map_mapKeys (fun bs => List.remove_i idx bs) tbl.(map)
    |}).
    (* Cond1: Sortedなことの証明 *)
    apply remove_i_sorted; [now apply Var.OT.lt_strorder|].
    now apply tbl.(Condition1).
   
    (* Cond2: lengthが等しいことの証明 *)
    revert Heqidx. unfold revapply. case_eq (index_of Var.eq_dec v (vars tbl)).
     simpl. intros idx' Heqidx' Heqidx. subst.
     remember (Map_mapKeys _ _) as tbl'. intros bs'.
     remember (List.insert_i idx' true bs') as bs.
     rewrite <- (List.remove_i_insert_i _ idx' true bs').
     rewrite <- Heqbs. rewrite Heqtbl'.
     rewrite <- Map_mapKeys_HasContents.
     rewrite tbl.(Condition2).
     split; [apply List.length_remove_i|].

     remember (remove_i idx' (vars tbl)) as vs'.
     remember (List.insert_i idx' v vs') as vs.
     rewrite Heqbs.
     rewrite remove_i_insert_i.
     rewrite<- (insert_i_remove_i Var.T Var.eq_dec idx' v (vars tbl) Heqidx').
     rewrite <- Heqvs'.
     now apply List.length_insert_i.

     (* v がtbl.(vars)にない場合は適当 *)
     simpl. (*idx = len vars なのでremove_i idx vars = vars 変わらない。*)
     intros Hidx Heqidx bs.
     rewrite remove_i_le_length; [|rewrite Heqidx; auto with arith].
     rewrite <- tbl.(Condition2).
     apply Map_Equal_HasContents_iff.
     apply Map_mapKeys_Equal.
     intro key. rewrite Heqidx. intro HasCont.
     destruct (tbl.(Condition2) key) as [Hlen _].
     rewrite <- (Hlen HasCont).
     now apply remove_i_le_length.
Defined.
(*
Definition remove_var (v : Var.T) (tbl:T) : T.
  case_eq (List.index_of Var.eq_dec v tbl.(vars)).
   (* Some idx のとき *)
   intros idx eqidx. refine ({|
      vars := List.remove_i idx tbl.(vars)
      ; map := Map_mapKeys (fun bs => List.remove_i idx bs) tbl.(map)
    |}).
    (* Cond1: Sortedなことの証明 *)
    apply remove_i_sorted; [now apply Var.OT.lt_strorder|].
    now apply tbl.(Condition1).
   
    (* Cond2: lengthが等しいことの証明 *)
    remember (Map_mapKeys _ _) as tbl'. intros bs'.
    remember (List.insert_i idx true bs') as bs.
    rewrite <- (List.remove_i_insert_i _ idx true bs').
    rewrite <- Heqbs. rewrite Heqtbl'.
    rewrite <- Map_mapKeys_HasContents.
    rewrite tbl.(Condition2).
    split; [apply List.length_remove_i|].

    remember (remove_i idx (vars tbl)) as vs'.
    remember (List.insert_i idx v vs') as vs.
    rewrite Heqbs.
    rewrite remove_i_insert_i.
    rewrite<- (insert_i_remove_i Var.T Var.eq_dec idx v (vars tbl) eqidx).
    rewrite <- Heqvs'.
    now apply List.length_insert_i.

   (* None のとき *)
   exact (fun _ => tbl).
Defined.
*)
Definition remove_vars (vs : list Var.T) tbl :=
  List.fold_left (fun acc_tbl v => remove_var v acc_tbl) vs tbl.

Lemma remove_var_vars : forall v tbl idx,
  index_of Var.eq_dec v tbl.(vars) = Some idx ->
  (remove_var v tbl).(vars) = List.remove_i idx tbl.(vars).
Proof.
 intros. simpl. rewrite H. now unfold revapply.
Qed.
Lemma remove_var_map : forall v tbl idx,
  index_of Var.eq_dec v tbl.(vars) = Some idx ->
  (remove_var v tbl).(map) = Map_mapKeys (List.remove_i idx) tbl.(map).
Proof.
 intros. simpl. rewrite H. now unfold revapply.
Qed.
(*Lemma remove_var_notincl : forall v tbl,
  index_of Var.eq_dec v tbl.(vars) = None ->
  (remove_var v tbl).(vars) = tbl.(vars) /\ (remove_var v tbl).(map) = tbl.(map).
Proof.
 intros v tbl Heq. simpl. rewrite Heq. unfold revapply. simpl. split.
  now apply remove_i_le_length.

  apply Map_mapKeys_eq. intros key HasCont.
  destruct (tbl.(Condition2) key) as [Hlen _].
  rewrite <- (Hlen HasCont).
  now apply remove_i_le_length.
Qed.
*)
Lemma remove_var_notincl : forall v tbl,
  index_of Var.eq_dec v tbl.(vars) = None ->
  (remove_var v tbl).(vars) = tbl.(vars) /\ Map.Equal (remove_var v tbl).(map) tbl.(map).
Proof.
 intros v tbl Heq. simpl. rewrite Heq. unfold revapply. simpl. split.
  now apply remove_i_le_length.

  apply Map_mapKeys_Equal. intros key HasCont.
  destruct (tbl.(Condition2) key) as [Hlen _].
  rewrite <- (Hlen HasCont).
  now apply remove_i_le_length.
Qed.
Lemma remove_var_update : forall v tbl ctx,
  exists b, eval (Context.update v b ctx) tbl =
    eval ctx (remove_var v tbl).
Proof.
 intros v tbl ctx.
 case_eq (index_of Var.eq_dec v (vars tbl)).
 - intros idx Heqidx.
   set (remove_var_vars _ _ _ Heqidx) as Hvars.
   set (remove_var_map _ _ _ Heqidx) as Hmap.
   generalize Hvars Hmap. clear Hvars Hmap. remember(remove_var v tbl) as tbl'.
   unfold eval, revapply. intros Hvars Hmap.
   remember (List.map ctx (remove_i idx tbl.(vars))) as key'.
   destruct (tbl'.(Condition2) key') as [_ HasCont].
   destruct HasCont as [val Hfind].
   + rewrite Heqkey'. rewrite map_length. now rewrite <- Hvars.
   + rewrite Hmap in Hfind.
     destruct(Map_find_mapKeys bool (remove_i idx) key' val tbl.(map) Hfind) as [key Hkey].
     destruct Hkey as [key1 key2].
     remember true as dummy. remember (List.nth idx key dummy) as b. exists b.
     unfold Context.to_key.
     rewrite Hmap, Hvars. rewrite <- Heqkey'. rewrite Hfind. rewrite <- key2.
     set (OrderedTypeVarList.Sort_NoDup tbl.(Condition1)) as HNoDup.
     rewrite NoDupA_NoDup in HNoDup.
     rewrite Context.map_update_replace_i with (idx:=idx); [|now apply Heqidx|now apply HNoDup].
     rewrite Heqb.
     rewrite remove_i_replace_i; [reflexivity| |].
     * rewrite map_length. apply eq_sym. apply tbl.(Condition2).
       unfold Map_HasContents. now exists val.
     * rewrite <- key1. rewrite Heqkey'.
       now rewrite map_remove_i.
 - intro Heqi. exists true. rewrite eval_update_notincl.
   + unfold eval. destruct (remove_var_notincl v tbl Heqi) as [Heqvars Heqmap].
     now rewrite Heqvars, Heqmap.
   + now apply (index_of_In_None Var.eq_dec).
Qed.
Lemma remove_var_same : forall v tbl,
  RedundantVar v tbl -> sameSemantics tbl (remove_var v tbl).
Proof.
 intros v tbl RV ctx. destruct (remove_var_update v tbl ctx).
 rewrite <- H. now rewrite RV.
Qed.
Lemma remove_vars_same : forall vs tbl,
  (forall v, In v vs -> RedundantVar v tbl) ->
    sameSemantics tbl (remove_vars vs tbl).
Proof.
 induction vs.
 - simpl. intros. apply refl_sameSemantics.
 - intros tbl Hrv. simpl.
   apply trans_sameSemantics with (y:=remove_var a tbl).
   + apply remove_var_same. apply Hrv. simpl. now left.
   + apply IHvs. intros v In_v.
     rewrite (redundant_same (remove_var a tbl) tbl).
     * apply Hrv. simpl. now right.
     * apply symm_sameSemantics.
       apply remove_var_same. apply Hrv. now left.
Qed.

Definition elimVars (tbl : T) : T :=
  let vs := List.filter' (fun v => redundantVar_dec v tbl) tbl.(vars) in
  remove_vars vs tbl.

Definition MinimumTable tbl : Prop := forall v, In v tbl.(vars) ->
  ~ RedundantVar v tbl.


(** * elimVarsの健全性: elimVarで意味が変わらない *)

Theorem soundness : forall (x : T), sameSemantics x (elimVars x).
Proof.
 intros x.
 unfold elimVars. remember (filter' _ _) as vs.
 apply remove_vars_same.
 (* ここからは vsのすべての要素がRedundantであることを示す *)
 intros v In_v.
 rewrite Heqvs in In_v.
 now rewrite filter'_In in In_v.
Qed.


(** * elimVarsの結果がMinimumになることの証明 *)

Lemma remove_vars_remove_all : forall vs tbl,
  (remove_vars vs tbl).(vars) = List.remove_all Var.eq_dec vs tbl.(vars).
Proof.
(*むずいかも*)
Admitted.

Lemma dec_In : forall (var:Var.T) vs, Decidable.decidable (In var vs).
Proof.
 intros var vs. now destruct (In_dec Var.eq_dec var vs); [left | right].
Qed.

Lemma minimum_elimVars : forall (tbl : T),
  MinimumTable (elimVars tbl).
Proof.
 intros tbl. set (soundness tbl) as sound. generalize sound. clear sound. (*revert?*)
 unfold elimVars.
 remember (filter' _ _) as vs. intros sound.
 unfold MinimumTable. intros v In_v.
 intro RV.
 rewrite remove_vars_remove_all in In_v.
 rewrite remove_all_In in In_v. destruct In_v as [In_v not_In_v].
 rewrite Heqvs, filter'_In in not_In_v. 
 apply (Decidable.not_and (In v (vars tbl)) (RedundantVar v tbl)) in not_In_v; [|now apply dec_In].
 destruct not_In_v; [contradiction|].
 elim H.
 (* ここからさきは remove_vars_sameで tblと(remvoe_vars vs tbl)のevalが同じになることを使ってRV->goalを示す*)
 eapply redundant_same; [| now apply RV].
 assumption.
Qed.

(** * 同じ意味の真理値表の一意性 *)

Definition contextForKey (vars: list Var.T)(key : list bool) : Context.T :=
  let dummy := true in
  fun v =>
    if (length vars =? length key) then
      match List.index_of Var.eq_dec v vars with
      | None => dummy
      | Some i => nth i key dummy
      end
    else dummy.

Lemma contextForKeySpec : forall (vs: list Var.T) (key : list bool),
  length vs = length key -> List.map (contextForKey vs key) vs = key.
Proof.
 (*TODO 示せそう*)
Admitted.

Lemma list_map_updated_not_in : forall x b vs ctx,
  ~In x vs -> List.map (Context.update x b ctx) vs = List.map ctx vs.
Proof.
 induction vs.
 - reflexivity.
 - simpl. intros ctx notin.
   destruct (Decidable.not_or _ _ notin) as [neq_hd notin_tl].
   unfold Context.update at 1. destruct (Var.eq_dec a x); [now idtac|]. f_equal.
   now apply IHvs.
Qed.

Lemma eval_updated_not_in : forall var b tbl ctx,
  ~In var tbl.(vars) -> eval (Context.update var b ctx) tbl = eval ctx tbl.
Proof.
 intros var b tbl ctx notin.
 unfold eval, revapply, Context.to_key.
 now rewrite list_map_updated_not_in.
Qed.
                      
Lemma minimum_in_vars : forall (x y: T), MinimumTable x ->
  MinimumTable y -> sameSemantics x y -> forall v, In v x.(vars) -> In v y.(vars).
Proof.
 (*In_decを使って背理法*)
 intros x y minx miny same v inx.
 destruct(In_dec Var.eq_dec v (vars y)); [assumption|]. (*背理法*)
 unfold sameSemantics in same.
 destruct (minx v inx). unfold RedundantVar. intros b ctx.
 rewrite same.
 now rewrite eval_updated_not_in.
Qed.

Lemma SortInEq : forall (xs ys: list Var.T),
  Sorted Var.lt xs -> Sorted Var.lt ys ->
  (forall a, In a xs <-> In a ys) -> xs = ys.
Proof.
 induction xs as [|x xs].
 - simpl.
   destruct ys; [reflexivity|]. intros _ _ H. destruct (H t) as [_ NIn]. elim NIn.
   simpl. now left.
 - intros ys SortedXs SortedYs inXsYs.
   destruct ys as [|y ys].
   + set (inXsYs x). simpl in i. destruct i as [H _]. elim H. now left.
   + set (OrderedTypeVarList.Sort_NoDup SortedXs) as NoDupXs.
     set (OrderedTypeVarList.Sort_NoDup SortedYs) as NoDupYs.
     destruct (Var.eq_dec x y) as [eq_xy|neq_xy].
     (* 先頭要素 x = y のとき *)
     * rewrite eq_xy. f_equal.
       apply IHxs.
         now inversion SortedXs.

         now inversion SortedYs.

         intro a.
         inversion NoDupXs. subst.
         (* NoDupを使って、 aが後ろの列xs ysに含まれることを証明 *)
         destruct (inXsYs a) as [In1 In2].
         simpl in In1. simpl in In2.
         split.
          intro InXs. inversion NoDupXs. subst.
          destruct In1; [now right| | assumption].
          rewrite <- H in InXs. elim H3. now apply OrderedTypeVarList.ListIn_In.

          intro InYs. inversion NoDupYs. subst.
          destruct In2; [now right | |assumption].
          rewrite <- H in InYs. elim H3. now apply OrderedTypeVarList.ListIn_In.
     (* 先頭要素 x <> y のとき *)
     * destruct (Var.neq_lt_gt_dec x y neq_xy).
         (* x < y *)
         destruct (Var.lt_irrefl x).
         apply (@OrderedTypeVarList.Sort_Inf_In (y::ys) x x SortedYs).
           now constructor.

           apply OrderedTypeVarList.ListIn_In.
           apply (inXsYs x). simpl. now left.
         (* x > y *)
         destruct (Var.lt_irrefl y).
         apply (@OrderedTypeVarList.Sort_Inf_In (x::xs) y y SortedXs).
           now constructor.

           apply OrderedTypeVarList.ListIn_In.
           apply (inXsYs y). simpl. now left.
Qed.

Lemma minimum_unique_vars : forall (x y: T), MinimumTable x ->
  MinimumTable y -> sameSemantics x y -> x.(vars) = y.(vars).
Proof.
 intros x y minx miny Same.
 apply SortInEq.
 - apply x.(Condition1).
 - apply y.(Condition1).
 - intro v. (*ここから本題*)
   split.
   + now apply minimum_in_vars.
   + now apply minimum_in_vars.
Qed.

Lemma lift_sameSemantics : forall x y, sameSemantics x y ->
  sameSemantics (elimVars x) (elimVars y).
Proof.
 intros x y Same. apply (trans_sameSemantics _ x _).
 - apply symm_sameSemantics. now apply soundness.
 - apply (trans_sameSemantics _ y _); [assumption|].
   apply soundness.
Qed.

Theorem unique_vars : forall (x y: T), sameSemantics x y -> (elimVars x).(vars) = (elimVars y).(vars).
Proof.
 intros x y Same.
 apply minimum_unique_vars.
 - now apply minimum_elimVars.
 - now apply minimum_elimVars.
 - now apply lift_sameSemantics.
Qed.

Lemma map_find_None : forall tbl bs,
  length bs <> length tbl.(vars) -> Map.find bs tbl.(map) = None.
Proof.
 (*ganbaru*)
Admitted.

Theorem uniqueness : forall (x y: T), sameSemantics x y -> elimVars x == elimVars y.
Proof.
 intros x y Same.
 set (unique_vars x y Same) as UniqueVars.
 split.
 (* x.(vars) = y.(vars) *)
 - now apply UniqueVars.
 (* mapが等しい *)
 - unfold Map.Equal. intro bs.
   destruct (length bs =? length (elimVars x).(vars)).
   (* bsの長さがvarsと等しい時 *)
   + assert (sameSemantics (elimVars x) (elimVars y)) as Same'; [now apply lift_sameSemantics|].
     unfold sameSemantics in Same'.
     set (contextForKey (elimVars x).(vars) bs) as ctx.
     unfold eval, revapply in Same'.
     set(Same' ctx) as SameCtx.
     rewrite <- UniqueVars in SameCtx. clear UniqueVars Same.
     unfold ctx, Context.to_key in SameCtx.
     now rewrite contextForKeySpec in SameCtx.
   + (* bsの長さがvarと等しくない時はMap.find がそれぞれNoneになる *)
     rewrite (map_find_None _ _ n).
     rewrite UniqueVars in n.
     rewrite (map_find_None _ _ n).
     reflexivity.
Qed.


(** * その他有用なもの *)

Lemma listForallEq : forall (A:Type) (xs ys : list A),
  List.Forall2 (fun x y => x = y) xs ys -> xs = ys.
Proof.
 intros A xs ys allEq.
 induction allEq.
 - reflexivity.
 - now rewrite H, IHallEq.
Qed.

Lemma BoolListEqLeibniz : forall key key',
  BoolListOrdered.eq key key' -> key = key'.
Proof.
 intros key key' Eq.
 unfold BoolListOrdered.eq in Eq.
 rewrite eqlistA_altdef in Eq.
 apply listForallEq.
 apply Eq.
Qed.

Definition ElemSorted elems := Sorted (Map.Raw.PX.ltk (elt:=bool)) elems.



Lemma Map_EquivEq_aux : forall (xs ys: list (list bool * bool)),
  ElemSorted xs -> ElemSorted ys ->
  Map.Raw.equal eqb xs ys = true -> xs = ys.
Proof.
 induction xs.
 - destruct ys; [reflexivity| discriminate].
 - destruct a as [key value].
   intros ys SortedXs SortedYs.
   destruct ys; [discriminate|].
   destruct p as [key' value']. simpl.
   case_eq (BoolListOrdered.compare key key');[discriminate| |discriminate].
   intros eq comp andb.
   destruct (andb_prop _ _ andb) as [ValEq TailEq].
   rewrite <- (BoolListEqLeibniz _ _ eq).
   rewrite <- (eqb_prop _ _ ValEq).
   f_equal. clear eq comp andb ValEq.
   apply IHxs.
   + now inversion SortedXs.
   + now inversion SortedYs.
   + assumption.
Qed.

Lemma Map_EquivEq : forall (x y: Map.t bool),
  Map.Equal x y -> MapProp.P.to_list x = MapProp.P.to_list y.
Proof.
 intros x y Equal.
 unfold MapProp.P.to_list, Map.elements.
 unfold Map.Raw.elements.
 rewrite (MapProp.P.F.Equal_Equivb eqb_true_iff) in Equal.
 rewrite (MapProp.P.F.equal_iff) in Equal.
 unfold Map.equal in Equal.
 remember (Map.this x) as xs.
 remember (Map.this y) as ys.
 apply Map_EquivEq_aux.
 - rewrite Heqxs. now apply (Map.sorted x).
 - rewrite Heqys. now apply (Map.sorted y).
 - now apply Equal.
Qed.