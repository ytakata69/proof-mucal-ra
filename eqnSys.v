(*
 * Definitions & lemmas on equation systems.
 *)

Require Import ltl.

(* Equation systems *)

Definition eqn_sys := V -> ltl.  (* the type of equation systems *)

(* The transformation from Env to Env *)
Definition F (sigma : eqn_sys) (env : Env) : Env :=
  fun (v : V) (theta : Theta) (w : data_word) =>
  (w, theta |= env, sigma v).

(* power of F *)
Fixpoint Fpow (sigma : eqn_sys) (i : nat) (u : Env) : Env :=
  match i with
    0   => u
  | S n => F sigma (Fpow sigma n u)
  end.
Definition Fpow_emp sigma i := Fpow sigma i empty_env.

Section EqnExample.

Variable b : Sigma.
Let w : data_word :=
  ((b, 2) :: (b, 3) :: (b, 3) :: (b, 4) :: (b, 2) :: nil).
Let sigma : eqn_sys :=
  fun v => match v with
    1 => ↓ 1, X (var 2)
  | 2 => ((X (var 2)) ./\ ~[↑ 1]) .\/ ((X (var 3)) ./\ [↑ 1])
  | 3 => φ [END]
  | _ => φ [tt]
  end.

Let th : Theta :=
  fun r => match r with
    1 => 2
  | _ => 0
  end.

Goal F sigma empty_env 3 th nil.
Proof.
  unfold F.
  unfold sigma.
  apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
Qed.
Goal ~ F sigma empty_env 1 th nil.
Proof.
  unfold F.
  unfold sigma.
  intros H.
  inversion H.
Qed.
Goal forall w' th',
  ~ F sigma empty_env 1 th' w'.
Proof.
  intros w' th'.
  unfold F.
  unfold sigma.
  intros H.
  inversion H
  as [| h t th'' u r psi Hht EQu EQht EQth'' [EQr EQpsi] | | | | | |].
  clear th'' EQth'' u EQu r EQr psi EQpsi.
  inversion Hht
  as [| |h' t' th'' u psi Ht EQu [EQh' EQt'] EQth'' EQpsi| | | | |].
  clear h' EQh' t' EQt' th'' EQth'' u EQu psi EQpsi.
  inversion Ht
  as [| | | | | | |w'' th'' u v He EQu EQw'' EQth'' EQv].
  clear w'' EQw'' th'' EQth'' u EQu v EQv.
  unfold empty_env in He.
  contradiction.
Qed.
Goal forall w' th',
  ~ F sigma empty_env 2 th' w'.
Proof.
  intros w' th'.
  unfold F.
  unfold sigma.
  intros H.
  inversion H
  as [| | | | w'' th'' u psi1 psi2 Ho EQu EQw'' EQth'' [EQp1 EQp2]| | |].
  clear w'' EQw'' th'' EQth'' u EQu psi1 EQp1 psi2 EQp2.
  destruct Ho as [Ho | Ho].
  - inversion Ho
  as [| | |w'' th'' u psi phi Hx Hp EQu EQw'' EQth'' [EQpsi EQphi]| | | |].
  clear w'' EQw'' th'' EQth'' u EQu psi EQpsi phi EQphi.
  inversion Hx
  as [| |h t th'' u psi Ht EQu EQht EQth'' EQpsi | | | | |].
  clear th'' EQth'' u EQu psi EQpsi.
  inversion Ht
  as [| | | | | | |w'' th'' u v He EQu EQw'' EQth'' EQv].
  clear w'' EQw'' th'' EQth'' u EQu v EQv.
  unfold empty_env in He.
  contradiction.
  - inversion Ho
  as [| | |w'' th'' u psi phi Hx Hp EQu EQw'' EQth'' [EQpsi EQphi]| | | |].
  clear w'' EQw'' th'' EQth'' u EQu psi EQpsi phi EQphi.
  inversion Hx
  as [| |h t th'' u psi Ht EQu EQht EQth'' EQpsi | | | | |].
  clear th'' EQth'' u EQu psi EQpsi.
  inversion Ht
  as [| | | | | | |w'' th'' u v He EQu EQw'' EQth'' EQv].
  clear w'' EQw'' th'' EQth'' u EQu v EQv.
  unfold empty_env in He.
  contradiction.
Qed.
Goal (F sigma) ((F sigma) empty_env) 2 th ((b, 2)::nil).
Proof.
  unfold F.
  unfold sigma at 2.
  apply models_OR.
  right.
  apply models_AND.
  - apply models_X.
  apply models_var.
  unfold sigma.
  apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
  - unfold models_phi.
  unfold models_atom.
  unfold snd.
  now unfold th.
Qed.

End EqnExample.

(* F and models *)

Lemma meanings_of_models_var :
  forall (w : data_word) (sigma : eqn_sys)
    (theta : Theta) (u : Env) (v : V),
  (w, theta |= F sigma u, var v) <->
  (w, theta |= u, sigma v).
Proof.
  intros w sigma theta u v.
  split.
  - (* -> *)
  intros H.
  inversion H
  as [| | | | | | |w' th u' v' H' EQu' EQw' EQth EQv'].
  clear w' EQw' th EQth u' EQu' v' EQv'.
  now unfold F in H'.
  - (* <- *)
  intros H.
  apply models_var.
  now unfold F.
Qed.

Lemma meanings_of_models_var_on_lfp :
  forall (w : data_word) (sigma : eqn_sys)
    (theta : Theta) (u : Env) (v : V),
  u = F sigma u ->
  (w, theta |= u, var v) <->
  (w, theta |= u, sigma v).
Proof.
  intros w sigma theta u v.
  intros Hlfp.
  rewrite Hlfp at 1.
  apply meanings_of_models_var.
Qed.

(* monotonicity *)

Section Monotonicity.

Definition env_leq (u1 u2 : Env) : Prop :=
  forall v : V,
  forall (theta : Theta) (w : data_word),
  u1 v theta w -> u2 v theta w.

Lemma models_is_monotonic :
  forall (u1 u2 : Env),
  env_leq u1 u2 ->
  forall (psi : ltl) (theta : Theta) (w : data_word),
  (w, theta |= u1, psi) -> (w, theta |= u2, psi).
Proof.
  intros u1 u2 Hu1u2.
  intros psi.
  induction psi; intros theta w Hm.
  - apply models_var.
  inversion Hm.
  now apply Hu1u2.
  - apply models_OR.
  inversion Hm as [| | | | w' th' u p1 p2 Ho| | |].
  destruct Ho as [Ho | Ho].
  + left; auto.
  + right; auto.
  - apply models_AND.
  inversion Hm; auto.
  inversion Hm; auto.
  - inversion Hm.
  apply models_STORE.
  now apply IHpsi.
  - inversion Hm.
  apply models_X.
  now apply IHpsi.
  - inversion Hm
  as [| | | | | | w' th' u phi psi' Hu EQu EQw'|].
  clear w' EQw'.
  destruct Hu as [w' [Hu1 Hu]].
  apply models_U.
  exists w'.
  split; auto.
  - inversion Hm.
  now apply models_PHI.
  - apply models_G.
  now inversion Hm.
Qed.

Theorem F_is_monotonic :
  forall (sigma : eqn_sys) (u1 u2 : Env),
  env_leq u1 u2 ->
  env_leq (F sigma u1) (F sigma u2).
Proof.
  intros sigma u1 u2 H.
  unfold env_leq.
  unfold F.
  intros v.
  now apply models_is_monotonic.
Qed.

Theorem Fpow_is_monotonic_1 :
  forall (sigma : eqn_sys) (i : nat),
  env_leq (Fpow_emp sigma i) (Fpow_emp sigma (S i)).
Proof.
  intros sigma i.
  induction i.
  { intros v theta w H.
    now unfold Fpow_emp in H. }
  unfold Fpow_emp.
  unfold Fpow.
  now apply F_is_monotonic.
Qed.

Theorem Fpow_is_monotonic_2 :
  forall (sigma : eqn_sys) (i : nat) (Y : Env),
  env_leq (Fpow_emp sigma i) Y ->
  env_leq (Fpow_emp sigma (S i)) (F sigma Y).
Proof.
  intros sigma i Y.
  intros H0.
  unfold Fpow_emp.
  unfold Fpow.
  now apply F_is_monotonic.
Qed.

Theorem least_fixpoint_of_F :
  forall (sigma : eqn_sys) (Y : Env),
  F sigma Y = Y ->
  forall i,
  env_leq (Fpow_emp sigma i) Y.
Proof.
  intros sigma Y HY i.
  induction i;
  intros v theta w H.
  - now unfold Fpow_emp in H.
  - rewrite<- HY.
  now apply (Fpow_is_monotonic_2 sigma i Y IHi).
Qed.

End Monotonicity.


Inductive var_not_appear (v : V)
  : ltl -> Prop :=
  | var_not_appear_VAR (v1 : V) :
      v <> v1 ->
      var_not_appear v (var v1)
  | var_not_appear_OR (p1 p2 : ltl) :
      var_not_appear v p1 ->
      var_not_appear v p2 ->
      var_not_appear v (p1 .\/ p2)
  | var_not_appear_AND (psi : ltl) (phi : ltl_phi) :
      var_not_appear v psi ->
      var_not_appear v (psi ./\ phi)
  | var_not_appear_STORE (r : register) (psi : ltl) :
      var_not_appear v psi ->
      var_not_appear v (↓ r, psi)
  | var_not_appear_X (psi : ltl) :
      var_not_appear v psi ->
      var_not_appear v (X psi)
  | var_not_appear_U (phi : ltl_phi) (psi : ltl) :
      var_not_appear v psi ->
      var_not_appear v (phi U psi)
  | var_not_appear_PHI (phi : ltl_phi) :
      var_not_appear v (φ phi)
  | var_not_appear_G (phi : ltl_phi) :
      var_not_appear v (G phi)
  .

Section UnusedVar.

Variables sigma1 sigma2 : eqn_sys.
Variable vs : list V.
Hypothesis v1_not_in_sigma1 :
  forall v v1, In v1 vs -> var_not_appear v1 (sigma1 v).
Hypothesis sigma_equiv :
  forall v, ~ In v vs -> sigma1 v = sigma2 v.

Lemma unused_var_not_matter :
  forall i theta w,
  forall v, ~ In v vs ->
  Fpow_emp sigma1 i v theta w <-> Fpow_emp sigma2 i v theta w.
Proof.
  induction i; intros theta w v Hv1.
  - (* i = 0 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  reflexivity.
  - (* inductive step on i *)
  unfold Fpow_emp.
  unfold Fpow.
  unfold F at 1.
  unfold F at 2.
  rewrite<- (sigma_equiv v Hv1).
  assert (v1_not_in_sigma1' := v1_not_in_sigma1 v).
  clear v1_not_in_sigma1.
  generalize dependent w.
  generalize dependent theta.
  induction (sigma1 v); intros theta w.
  + (* sigma1 v = var v0 -> ... *)
  assert (Hnv0 : ~ In v0 vs).
  { intros Hv0.
    assert (Hnv1 := v1_not_in_sigma1' v0 Hv0).
    inversion Hnv1 as [v0' Hcon| | | | | | |].
    now apply Hcon. }
  split;
  intros Hx;
  apply models_var;
  apply IHi;
  inversion Hx; trivial.
  + (* sigma1 v = l1 .\/ l2 -> ... *)
  assert (Hnvl1 : forall v1, In v1 vs -> var_not_appear v1 l1).
  { intros v1 Hv1in.
    assert (Hnv1 := v1_not_in_sigma1' v1 Hv1in).
    now inversion Hnv1. }
  assert (Hnvl2 : forall v1, In v1 vs -> var_not_appear v1 l2).
  { intros v1 Hv1in.
    assert (Hnv1 := v1_not_in_sigma1' v1 Hv1in).
    now inversion Hnv1. }
  split;
  intros Hx;
  apply models_OR;
  inversion Hx
  as [| | | |w' th u p1' p2' Ho | | |];
  destruct Ho as [Ho | Ho];
  try (left; now apply IHl1);
  try (right; now apply IHl2).
  + (* sigma1 v = l ./\ l0 -> ... *)
  assert (Hnvl : forall v1, In v1 vs -> var_not_appear v1 l).
  { intros v1 Hv1in.
    assert (Hnv1 := v1_not_in_sigma1' v1 Hv1in).
    now inversion Hnv1. }
  split;
  intros Hx;
  inversion Hx;
  apply models_AND;
  try apply IHl;
  auto.
  + (* sigma1 v = ↓ r, l -> ... *)
  assert (Hnvl : forall v1, In v1 vs -> var_not_appear v1 l).
  { intros v1 Hv1in.
    assert (Hnv1 := v1_not_in_sigma1' v1 Hv1in).
    now inversion Hnv1. }
  split;
  intros Hx;
  inversion Hx;
  apply models_STORE;
  now apply IHl.
  + (* sigma1 v = X l -> ... *)
  assert (Hnvl : forall v1, In v1 vs -> var_not_appear v1 l).
  { intros v1 Hv1in.
    assert (Hnv1 := v1_not_in_sigma1' v1 Hv1in).
    now inversion Hnv1. }
  split;
  intros Hx;
  inversion Hx;
  apply models_X;
  now apply IHl.
  + (* sigma1 v = l U l0 -> ... *)
  assert (Hnvl : forall v1, In v1 vs -> var_not_appear v1 l0).
  { intros v1 Hv1in.
    assert (Hnv1 := v1_not_in_sigma1' v1 Hv1in).
    now inversion Hnv1. }
  split;
  intros Hx;
  inversion Hx
  as [| | | | | | w' th u l' l0' Hx' EQu EQw'|];
  clear w' EQw';
  destruct Hx' as [w' [Hx' Hsuf]];
  apply models_U;
  exists w';
  split;
  try apply IHl; auto.
  + (* sigma1 v = φ l -> ... *)
  split;
  intros Hx;
  inversion Hx;
  now apply models_PHI.
  + (* sigma1 v = G l -> ... *)
  split;
  intros Hx;
  inversion Hx;
  now apply models_G.
Qed.

End UnusedVar.

Section Normalization.

Hypothesis Var_eq_dec :
  forall v1 v2 : V, {v1 = v2} + {v1 <> v2}.

Section NormalizeOr.

Variables sigma1 sigma2 : eqn_sys.
Variables v1 v2 v3 : V.
Hypothesis sigma_equiv :
  forall v, v <> v3 -> sigma1 v = sigma2 v.
Hypothesis v1_neq_v3 : v1 <> v3.
Hypothesis v2_neq_v3 : v2 <> v3.
Hypothesis EQv3_1 : sigma1 v3 = ((sigma1 v1) .\/ (sigma1 v2)).
Hypothesis EQv3_2 : sigma2 v3 = ((var v1) .\/ (var v2)).

Theorem normalize_or_1 :
  forall l,
  env_leq (Fpow_emp sigma2 l) (Fpow_emp sigma1 l).
Proof.
  induction l as [| l IHl].
  - (* l = 0 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  now unfold env_leq.
  - (* inductive step on l *)
  unfold Fpow_emp.
  unfold Fpow.
  unfold F at 1.
  unfold F at 2.
  unfold env_leq.
  intros v theta w.
  destruct (Var_eq_dec v v3)
  as [v_eq_v3 | v_neq_v3].
  + (* v = v3 -> ... *)
  rewrite v_eq_v3.
  rewrite EQv3_1.
  rewrite EQv3_2.
  intros Hx.
  apply models_OR.
  inversion Hx
  as [| | | |w' th u p1' p2' Ho EQu EQw' EQth [EQp1' EQp2']| | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  destruct Ho as [Ho | Ho];
  [left | right];
  inversion Ho as [| | | | | |
  | w'' th' u' v' Hf EQu' EQw'' EQth' EQv'];
  clear w'' EQw'' th' EQth' u' EQu' v' EQv';
  apply IHl in Hf;
  unfold Fpow_emp in Hf;
  apply Fpow_is_monotonic_1 in Hf;
  unfold Fpow_emp in Hf;
  unfold Fpow in Hf;
  unfold F at 1 in Hf;
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l);
  auto;
  now unfold env_leq.
  + (* v <> v3 -> ... *)
  assert (EQsv := sigma_equiv v v_neq_v3).
  rewrite<- EQsv.
  apply models_is_monotonic.
  apply IHl.
Qed.

Theorem normalize_or_2 :
  forall l,
  env_leq (Fpow_emp sigma1 l) (Fpow_emp sigma2 (2 * l)).
Proof.
  intros l.
  simpl.
  rewrite<- (plus_n_O l).
  induction l as [| l IHl].
  - (* l = 0 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  now unfold env_leq.
  - (* inductive step on l *)
  simpl.
  unfold Fpow_emp.
  unfold Fpow.
  unfold F at 1.
  unfold F at 2.
  unfold env_leq.
  rewrite<- (plus_n_Sm l l).
  intros v theta w.
  destruct (Var_eq_dec v v3)
  as [v_eq_v3 | v_neq_v3].
  + (* v = v3 -> ... *)
  rewrite v_eq_v3.
  rewrite EQv3_1.
  rewrite EQv3_2.
  intros Hx.
  apply models_OR.
  inversion Hx
  as [| | | |w' th u p1' p2' Ho EQu EQw' EQth [EQp1' EQp2']| | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  destruct Ho as [Ho | Ho];
  [left | right];
  apply models_is_monotonic with (u1 := Fpow_emp sigma2 (S (l+l)));
  (unfold Fpow_emp; unfold Fpow);
  try (apply models_var; unfold F at 1);
  try now unfold env_leq.
  * rewrite<- (sigma_equiv v1 v1_neq_v3).
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l);
  try apply IHl.
  apply Ho.
  * rewrite<- (sigma_equiv v2 v2_neq_v3).
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l);
  try apply IHl.
  apply Ho.
  + (* v <> v3 -> ... *)
  assert (EQsv := sigma_equiv v v_neq_v3).
  rewrite<- EQsv.
  intros Hx.
  apply models_is_monotonic with (u1 := Fpow_emp sigma2 (l + l));
  try apply Fpow_is_monotonic_1.
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l);
  try apply IHl.
  apply Hx.
Qed.

End NormalizeOr.

Section NormalizeStoreX.

Variables sigma1 sigma2 : eqn_sys.
Variables v1 v3 : V.
Hypothesis sigma_equiv :
  forall v, v <> v3 -> sigma1 v = sigma2 v.
Hypothesis v1_neq_v3 : v1 <> v3.
Variable r : register.
Variable phi1 : ltl_phi.
Hypothesis EQv3_1 : sigma1 v3 = ((↓ r, X (sigma1 v1)) ./\ phi1).
Hypothesis EQv3_2 : sigma2 v3 = ((↓ r, X (var v1)) ./\ phi1).

Theorem normalize_store_X_1 :
  forall l,
  env_leq (Fpow_emp sigma2 l) (Fpow_emp sigma1 l).
Proof.
  induction l as [| l IHl].
  - (* l = 0 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  now unfold env_leq.
  - (* l > 0 -> ... *)
  destruct l as [| l].
  + (* l = 1 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  unfold F.
  unfold env_leq.
  intros v theta w.
  destruct (Var_eq_dec v v3)
  as [v_eq_v3 | v_neq_v3].
  * (* v = v3 -> ... *)
  rewrite v_eq_v3.
  rewrite EQv3_2.
  intros Hx.
  inversion Hx
  as [| | | w' th u p1' p2' Hsx Hp1 EQu EQw' EQth [EQp1' EQp2']| | | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  inversion Hsx
  as [|h t th u r' p1' Hxv1 EQu EQht EQth [EQr' EQp1']| | | | | |].
  clear th EQth u EQu r' EQr' p1' EQp1'.
  inversion Hxv1
  as [| |h' t' th u p1' Hv1 EQu [EQh' EQt'] EQth EQp1'| | | | |].
  clear h' EQh' t' EQt' th EQth u EQu p1' EQp1'.
  now inversion Hv1.
  * (* v <> v3 -> ... *)
  assert (EQsv := sigma_equiv v v_neq_v3).
  now rewrite<- EQsv.

  + (* l > 1 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  unfold F at 1.
  unfold F at 3.
  unfold env_leq.
  intros v theta w.
  destruct (Var_eq_dec v v3)
  as [v_eq_v3 | v_neq_v3].
  * (* v = v3 -> ... *)
  rewrite v_eq_v3.
  rewrite EQv3_1.
  rewrite EQv3_2.
  intros Hx.
  inversion Hx
  as [| | | w' th u p1' p2' Hsx Hp1 EQu EQw' EQth [EQp1' EQp2']| | | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  inversion Hsx
  as [|h t th u r' p1' Hxv1 EQu EQht EQth [EQr' EQp1']| | | | | |].
  clear th EQth u EQu r' EQr' p1' EQp1'.
  inversion Hxv1
  as [| |h' t' th u p1' Hv1 EQu [EQh' EQt'] EQth EQp1'| | | | |].
  clear h' EQh' t' EQt' th EQth u EQu p1' EQp1'.
  rewrite<- EQht in Hp1.
  apply models_AND; auto.
  clear Hx Hsx Hxv1 Hp1 w EQht.
  apply models_STORE.
  apply models_X.
  inversion Hv1
  as [| | | | | | |t' th u v' Hf EQu EQt' EQth EQv'].
  clear t' EQt' th EQth u EQu v' EQv'.
  unfold F in Hf.
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l).
  try apply Fpow_is_monotonic_1.
  apply IHl.
  unfold Fpow_emp.
  unfold Fpow.
  unfold F at 1.
  apply Hf.
  * (* v <> v3 -> ... *)
  assert (EQsv := sigma_equiv v v_neq_v3).
  rewrite<- EQsv.
  apply models_is_monotonic.
  apply IHl.
Qed.

Theorem normalize_store_X_2 :
  forall l,
  env_leq (Fpow_emp sigma1 l) (Fpow_emp sigma2 (2 * l)).
Proof.
  intros l.
  simpl.
  rewrite<- (plus_n_O l).
  induction l as [| l IHl].
  - (* l = 0 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  now unfold env_leq.
  - (* inductive step on l *)
  simpl.
  unfold Fpow_emp.
  unfold Fpow.
  unfold F at 1.
  unfold F at 2.
  unfold env_leq.
  rewrite<- (plus_n_Sm l l).
  intros v theta w.
  destruct (Var_eq_dec v v3)
  as [v_eq_v3 | v_neq_v3].
  + (* v = v3 -> ... *)
  rewrite v_eq_v3.
  rewrite EQv3_1.
  rewrite EQv3_2.
  intros Hx.
  inversion Hx
  as [| | | w' th u p1' p2' Hsx Hp1 EQu EQw' EQth [EQp1' EQp2']| | | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  inversion Hsx
  as [|h t th u r' p1' Hxv1 EQu EQht EQth [EQr' EQp1']| | | | | |].
  clear th EQth u EQu r' EQr' p1' EQp1'.
  inversion Hxv1
  as [| |h' t' th u p1' Hv1 EQu [EQh' EQt'] EQth EQp1'| | | | |].
  clear h' EQh' t' EQt' th EQth u EQu p1' EQp1'.
  rewrite<- EQht in Hp1.
  apply models_AND; auto.
  clear Hx Hsx Hxv1 Hp1 w EQht.
  apply models_STORE.
  apply models_X.
  apply models_var.
  unfold F at 1.
  rewrite<- (sigma_equiv v1 v1_neq_v3).
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l);
  try apply IHl.
  apply Hv1.
  + (* v <> v3 -> ... *)
  assert (EQsv := sigma_equiv v v_neq_v3).
  rewrite<- EQsv.
  intros Hx.
  apply models_is_monotonic with (u1 := Fpow_emp sigma2 (l + l));
  try apply Fpow_is_monotonic_1.
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l);
  try apply IHl.
  apply Hx.
Qed.

End NormalizeStoreX.

Section NormalizeU.

Variables sigma1 sigma2 : eqn_sys.
Variables v1 v2 v3 : V.
Hypothesis sigma_equiv :
  forall v, v <> v3 -> sigma1 v = sigma2 v.
Hypothesis v1_neq_v3 : v1 <> v3.
Hypothesis v2_neq_v3 : v2 <> v3.
Variable phi1 : ltl_phi.
Hypothesis EQv3_1 : sigma1 v3 = (phi1 U (sigma1 v1)).
Hypothesis EQv3_2 : sigma2 v3 = ((var v1) .\/ (var v2)).
Hypothesis EQv2_2 : sigma2 v2 = (X (var v3) ./\ phi1).

Theorem normalize_U_1 :
  forall l,
  env_leq (Fpow_emp sigma2 l) (Fpow_emp sigma1 l).
Proof.
  induction l as [| l IHl].
  - (* l = 0 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  now unfold env_leq.
  - (* l > 0 -> ... *)
  destruct l as [| l].
  + (* l = 1 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  unfold F.
  unfold env_leq.
  intros v theta w.
  destruct (Var_eq_dec v v3)
  as [v_eq_v3 | v_neq_v3].
  * (* v = v3 -> ... *)
  rewrite v_eq_v3.
  rewrite EQv3_2.
  rewrite EQv3_1.
  rewrite U_equals_psi_or_phi_and_XU.
  intros Hx.
  apply models_OR.
  inversion Hx
  as [| | | | w' th u p1' p2' Ho EQu EQw' EQth [EQp1' EQp2']| | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  destruct Ho as [Ho | Ho];
  [left | right];
  try now inversion Ho.
  * (* v <> v3 -> ... *)
  assert (EQsv := sigma_equiv v v_neq_v3).
  now rewrite<- EQsv.

  + (* l > 1 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  unfold F at 1.
  unfold F at 3.
  unfold env_leq.
  intros v theta w.
  destruct (Var_eq_dec v v3)
  as [v_eq_v3 | v_neq_v3].
  * (* v = v3 -> ... *)
  rewrite v_eq_v3.
  rewrite EQv3_1.
  rewrite EQv3_2.
  rewrite U_equals_psi_or_phi_and_XU.
  intros Hx.
  apply models_OR.
  inversion Hx
  as [| | | | w' th u p1' p2' Ho EQu EQw' EQth [EQp1' EQp2']| | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  destruct Ho as [Ho | Ho];
  [left | right].
  -- apply models_is_monotonic with (u1 := Fpow_emp sigma1 (S l)).
  now unfold env_leq.
  apply models_is_monotonic with (u1 := Fpow_emp sigma2 (S l));
  try apply IHl.
  inversion Ho
  as [| | | | | | |w' th u v' Hf].
  unfold F in Hf.
  rewrite (sigma_equiv v1 v1_neq_v3).
  apply models_is_monotonic with (u1 := Fpow_emp sigma2 l);
  try apply Hf.
  apply Fpow_is_monotonic_1.

  -- inversion Ho
  as [| | | | | | |w' th u v' Hf EQu EQw' EQth EQv'].
  clear w' EQw' th EQth u EQu v' EQv'.
  unfold F in Hf.
  rewrite EQv2_2 in Hf.
  inversion Hf
  as [| | |w' th u p1' p2' Hxv1 Hp1 EQu EQw' EQth [EQp1' EQp2']| | | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  apply models_AND; auto.
  inversion Hxv1
  as [| |h t th u p1' Hv1 EQu EQht EQth EQp1'| | | | |].
  clear th EQth u EQu p1' EQp1'.
  clear Hx Ho Hf Hxv1 Hp1 w EQht.
  apply models_X.
  rewrite<- EQv3_1.
  apply models_is_monotonic with (u2 := Fpow_emp sigma2 (S l)) in Hv1;
  try apply Fpow_is_monotonic_1.
  apply models_is_monotonic with (u2 := Fpow_emp sigma1 (S l)) in Hv1;
  try apply IHl.
  inversion Hv1
  as [| | | | | | |w' th u v' Hf].
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l).
  try apply Fpow_is_monotonic_1.
  apply Hf.

  * (* v <> v3 -> ... *)
  assert (EQsv := sigma_equiv v v_neq_v3).
  rewrite<- EQsv.
  apply models_is_monotonic.
  apply IHl.
Qed.

Variable fpF_2 : Env.
Hypothesis fpF_is_fixpoint :
  F sigma2 fpF_2 = fpF_2.

Theorem normalize_U_2 :
  forall l,
  env_leq (Fpow_emp sigma1 l) fpF_2.
Proof.
  intros l.
  induction l as [| l IHl].
  - (* l = 0 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  now unfold env_leq.
  - (* inductive step on l *)
  unfold env_leq.
  intros v theta w.
  unfold Fpow_emp.
  unfold Fpow.
  rewrite<- fpF_is_fixpoint.
  unfold F.
  destruct (Var_eq_dec v v3)
  as [v_eq_v3 | v_neq_v3].
  + (* v = v3 -> ... *)
  rewrite v_eq_v3.
  rewrite EQv3_1.
  rewrite EQv3_2.
  rewrite U_equals_psi_or_phi_and_XU.
  intros Hx.
  apply models_OR.
  inversion Hx
  as [| | | | w' th u p1' p2' Ho EQu EQw' EQth [EQp1' EQp2']| | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  destruct Ho as [Ho | Ho];
  [left | right];
  rewrite<- fpF_is_fixpoint;
  apply models_var;
  unfold F.
  * rewrite<- (sigma_equiv v1 v1_neq_v3).
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l);
  auto.
  * rewrite EQv2_2.
  inversion Ho
  as [| | | w' th u p1' p2' Hxv1 Hp1 EQu EQw' EQth [EQp1' EQp2']| | | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  apply models_AND; auto.
  inversion Hxv1
  as [| |h t th u p1' Hv1 EQu EQht EQth EQp1'| | | | |].
  clear th EQth u EQu p1' EQp1'.
  apply models_X.
  clear Hx Ho Hxv1 Hp1 w h EQht.

  induction t as [| a t IHt].
  -- (* t = nil -> ... *)
  inversion Hv1
  as [| | | | | |w th u p1' p2' Hu EQu EQw EQth [EQp1' EQp2']|].
  clear w EQw th EQth u EQu p1' EQp1' p2' EQp2'.
  destruct Hu as [w' [Hu Hsf]].
  inversion Hsf as [p ls EQp EQls EQw'|].
  clear p EQp ls EQls.
  rewrite EQw' in Hu.
  rewrite<- fpF_is_fixpoint.
  apply models_var.
  unfold F.
  rewrite EQv3_2.
  apply models_OR.
  left.
  rewrite<- fpF_is_fixpoint.
  apply models_var.
  unfold F.
  rewrite<- (sigma_equiv v1 v1_neq_v3).
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l);
  auto.
  -- (* t = a::t -> ... *)
  rewrite U_equals_psi_or_phi_and_XU in Hv1.
  inversion Hv1
  as [| | | | w' th u p1' p2' Ho EQu EQw' EQth [EQp1' EQp2']| | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  destruct Ho as [Ho | Ho].
  ++ (* (a::t, theta |= Fpow_emp sigma1 l, psi1) -> ... *)
  rewrite<- fpF_is_fixpoint.
  apply models_var.
  unfold F.
  rewrite EQv3_2.
  apply models_OR.
  left.
  rewrite<- fpF_is_fixpoint.
  apply models_var.
  unfold F.
  rewrite<- (sigma_equiv v1 v1_neq_v3).
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l);
  auto.
  ++ (* (a::t, theta |= Fpow_emp sigma1 l, X (phi1 U psi1) ./\ phi1) -> ... *)
  inversion Ho
  as [| | | w' th u p1' p2' Hxv1 Hp1 EQu EQw' EQth [EQp1' EQp2']| | | |].
  clear w' EQw' th EQth u EQu p1' EQp1' p2' EQp2'.
  inversion Hxv1
  as [| |h t' th u p1' Hu EQu [EQh EQt'] EQth EQp1'| | | | |].
  clear h EQh t' EQt' th EQth u EQu p1' EQp1'.
  rewrite<- fpF_is_fixpoint.
  apply models_var.
  unfold F.
  rewrite EQv3_2.
  apply models_OR.
  right.
  rewrite<- fpF_is_fixpoint.
  apply models_var.
  unfold F.
  rewrite EQv2_2.
  apply models_AND; auto.
  apply models_X.
  now apply IHt.

  + (* v <> v3 -> ... *)
  assert (EQsv := sigma_equiv v v_neq_v3).
  rewrite<- EQsv.
  intros Hx.
  apply models_is_monotonic with (u1 := Fpow_emp sigma1 l);
  try apply IHl.
  apply Hx.
Qed.

End NormalizeU.

End Normalization.
