Require Import ltl.
Require Import eqnSys.

(* The set of normalized LTL formulas *)

Inductive ra_ltl : ltl -> Prop :=
  | ra_ltl_OR :
      forall v v' : V,
      ra_ltl (var v .\/ var v')
  | ra_ltl_X :
      forall (v : V) (phi : ltl_phi),
      ra_ltl (X (var v) ./\ phi)
  | ra_ltl_STORE_X :
      forall r (v : V) (phi : ltl_phi),
      ra_ltl ((↓ r, X (var v)) ./\ phi)
  | ra_ltl_PHI :
      forall (phi : ltl_phi),
      ra_ltl (φ phi)
  .

(* Transition rules *)

Inductive SigmaE :=
  | epsilon
  | Σφ (phi : ltl_phi)
  .
Inductive regSet :=
  | reg_empty
  | reg (r : register)
  .
Inductive ruleA (sigma : eqn_sys)
  : ltl -> SigmaE -> regSet -> ltl -> Prop :=
  | ruleA_PHI :
    forall phi : ltl_phi,
    ruleA sigma (φ phi) (Σφ phi) reg_empty (φ [tt])
  | ruleA_OR_left :
    forall v1 v2 : V,
    ruleA sigma (var v1 .\/ var v2) epsilon reg_empty (sigma v1)
  | ruleA_OR_right :
    forall v1 v2 : V,
    ruleA sigma (var v1 .\/ var v2) epsilon reg_empty (sigma v2)
  | ruleA_X :
    forall (v : V) (phi : ltl_phi),
    ruleA sigma (X (var v) ./\ phi) (Σφ phi) reg_empty (sigma v)
  | ruleA_STORE_X :
    forall r (v : V) (phi : ltl_phi),
    ruleA sigma ((↓ r, X (var v)) ./\ phi) (Σφ phi) (reg r) (sigma v)
  .

Definition Config := (ltl * Theta * data_word)%type.

Inductive moveA (sigma : eqn_sys)
  : Config -> Config -> Prop :=
  | moveA_epsilon :
    forall q1 q2 theta w,
    ruleA sigma q1 epsilon reg_empty q2 ->
    moveA sigma (q1, theta, w) (q2, theta, w)
  | moveA_not_update :
    forall q1 q2 phi theta h t,
    ruleA sigma q1 (Σφ phi) reg_empty q2 ->
    models_phi (h::t) theta phi ->
    moveA sigma (q1, theta, h::t) (q2, theta, t)
  | moveA_update :
    forall q1 q2 phi r theta a t,
    ruleA sigma q1 (Σφ phi) (reg r) q2 ->
    models_phi (a::t) theta phi ->
    moveA sigma (q1, theta, a::t) (q2, update theta r (snd a), t)
  .

Inductive moveA_star (sigma : eqn_sys)
  : Config -> Config -> Prop :=
  | moveA_star_ref :
    forall q1,
    moveA_star sigma q1 q1
  | moveA_star_trans :
    forall q1 q2 q3,
    moveA sigma q1 q2 -> moveA_star sigma q2 q3 ->
    moveA_star sigma q1 q3
  .

Inductive finalA
  : ltl -> Prop :=
  | finalA_tt  : finalA (φ [tt])
  | finalA_END : finalA (φ [END])
  | finalA_not_p : forall a, finalA (φ ~[p a])
  | finalA_not_MATCH : forall r, finalA (φ ~[↑ r])
  | finalA_and : forall p1 p2,
    finalA (φ p1) -> finalA (φ p2) -> finalA (φ p1 ../\ p2)
  .

Lemma moveA_star_is_transitive :
  forall sigma c1 c2 c3,
  moveA_star sigma c1 c2 ->
  moveA_star sigma c2 c3 ->
  moveA_star sigma c1 c3.
Proof.
  intros sigma c1 c2 c3.
  intros H12 H23.
  induction H12 as [| c1 c2 c3' H12 H23' IH];
  auto.
  apply moveA_star_trans with c2;
  now try apply IH.
Qed.

Lemma moveA_star_is_transitive_at_last :
  forall sigma c1 c2 c3,
  moveA_star sigma c1 c2 ->
  moveA sigma c2 c3 ->
  moveA_star sigma c1 c3.
Proof.
  intros sigma c1 c2 c3 H12 H23.
  apply moveA_star_is_transitive with c2; auto.
  apply moveA_star_trans with c3;
  try apply moveA_star_ref.
  apply H23.
Qed.

Lemma tt_loop_exists :
  forall sigma theta w,
  moveA_star sigma (φ [tt], theta, w) (φ [tt], theta, nil).
Proof.
  intros sigma theta w.
  induction w.
  - apply moveA_star_ref.
  - apply (moveA_star_trans sigma _ (φ [tt], theta, w)).
  + apply moveA_not_update with (phi := [tt]).
  * apply ruleA_PHI.
  * now unfold models_phi.
  + trivial.
Qed.

Lemma satisfied_at_end_is_finalA :
  forall phi theta,
  models_phi nil theta phi <-> finalA (φ phi).
Proof.
  intros phi theta.
  split.
  - intros Hmo.
  induction phi as [l | l | p1 IHp1 p2 IHp2].
  + destruct l;
  try now unfold models_phi in Hmo.
  * apply finalA_tt.
  * apply finalA_END.
  + destruct l;
  try unfold models_phi in Hmo;
  try now unfold models_atom in Hmo.
  * apply finalA_not_MATCH.
  * apply finalA_not_p.
  + unfold models_phi in Hmo.
  destruct Hmo as [Hp1 Hp2].
  apply IHp1 in Hp1.
  apply IHp2 in Hp2.
  now apply finalA_and.

  - induction phi as [l | l | p1 IHp1 p2 IHp2];
  intros Hf;
  try (inversion Hf; now unfold models_phi).
  inversion Hf as [| | | | p1' p2' Hf1 Hf2 [EQp1' EQp2']].
  unfold models_phi.
  split; [apply IHp1 | apply IHp2]; trivial.
Qed.

Section CorrectnessOfConversionToRA.

Variable sigma : eqn_sys.
Hypothesis Hra :
  forall v : V, ra_ltl (sigma v).

Variable ell : nat.
Definition lfpF := Fpow_emp sigma ell.
Hypothesis HlfpF : lfpF = F sigma lfpF.

Theorem A_is_equivalent_to_sigma_1 :
  forall w v theta,
  (w, theta |= lfpF, sigma v) ->
  exists theta' qF,
  finalA qF /\
  moveA_star sigma (sigma v, theta, w) (qF, theta', nil).
Proof.
  unfold lfpF.
  induction ell as [| l IHl].
  - (* ell = 0 -> ... *)
  intros w v theta Hw.
  assert (Hra' := Hra v).
  inversion Hw
  as [w' th u phi Hmo EQu EQw' EQth EQphi
     | h t th u r psi Hmo EQu [EQh EQt] EQth EQpsi
     | h t th u psi Hmo EQu [EQh EQt] EQth EQpsi 
     | w' th u psi phi Hpsi Hmo EQu EQw' EQth EQpsi
     | w' th u psi1 psi2 Hmo EQu EQw' EQth EQpsi
     | w' th u psi Hmo EQu EQw' EQth EQpsi
     | w' th u phi psi Hmo EQu EQw' EQth EQpsi
     | w' th u v' Hmo EQu EQw' EQth EQpsi].
  * (* sigma v = φ phi -> ... *)
  exists theta.
  destruct w as [| a w].
  -- (* w = nil -> ... *)
  exists (φ phi).
  destruct phi;
  split;
  try apply moveA_star_ref;
  now apply satisfied_at_end_is_finalA with theta.
  -- (* w' = a :: w -> ... *)
  exists (φ [tt]).
  destruct phi as [l0 | l0 | p1 p2];
  split;
  try apply finalA_tt;
  apply moveA_star_trans with (q2 := (φ [tt], theta, w));
  try apply tt_loop_exists.
  ++ (* sigma v = φ [l0] -> ... *)
  apply moveA_not_update with (phi := [l0]);
  try apply Hmo; apply ruleA_PHI.
  ++ (* sigma v = φ ~[l] -> ... *)
  apply moveA_not_update with (phi := ~[l0]);
  try apply Hmo; apply ruleA_PHI.
  ++ (* sigma v = φ p1 ../\ p2 -> ... *)
  apply moveA_not_update with (phi := p1 ../\ p2);
  try apply Hmo; apply ruleA_PHI.

  * (* sigma v = ↓ r, psi -> ... *)
  rewrite <- EQpsi in Hra';
  inversion Hra'.
  * (* sigma v = X psi -> ... *)
  rewrite <- EQpsi in Hra';
  inversion Hra'.

  * (* sigma v = psi ./\ phi -> ... *)
  rewrite <- EQpsi in Hra'.
  inversion Hra'
  as [| v0 phi0 [EQv0 EQphi0]| r v0 phi0 [EQv0 EQphi0]|].
  -- (* sigma v = X (var v0) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi
  as [| | h t th' u' psi' Hmo' EQu' [EQh EQt] EQth' EQpsi'| | | | |].
  clear th' EQth' u' EQu' psi' EQpsi'.
  inversion Hmo'
  as [| | | | | | |w'' th' u' v1 Hf EQu' EQw'' EQth' EQv1].
  now unfold Fpow_emp in Hf.
  -- (* sigma v = (↓ r, X (var v0)) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi
  as [| h t th' u' r' psi' Hmo' EQu' [EQh EQt] EQth' [EQr' EQpsi'] | | | | | |].
  clear th' EQth' u' EQu' r' EQr' psi' EQpsi'.
  inversion Hmo'
  as [| | h' t' th' u' psi' Hmo'' EQu' [EQh' EQt'] EQth' EQpsi'| | | | |].
  clear h' EQh' t' EQt' th' EQth' u' EQu' psi' EQpsi'.
  inversion Hmo''
  as [| | | | | | |w'' th' u' v1 Hf EQu' EQw'' EQth' EQv1].
  now unfold Fpow_emp in Hf.

  * (* sigma v = psi1 .\/ psi2 -> ... *)
  rewrite <- EQpsi in Hra'.
  inversion Hra' as [v1 v2 [EQpsi1 EQpsi2]| | |].
  (* sigma v = var v1 .\/ var v2 -> ... *)
  rewrite <- EQpsi1 in Hmo.
  rewrite <- EQpsi2 in Hmo.
  unfold Fpow_emp in Hmo.
  unfold Fpow in Hmo.
  destruct Hmo as [Hmo | Hmo].
  -- (* (nil, theta |= empty_env, var v1) -> ... *)
  inversion Hmo as [| | | | | | |w'' th' u' v' H].
  now unfold empty_env in H.
  -- (* (nil, theta |= empty_env, var v2) -> ... *)
  inversion Hmo as [| | | | | | |w'' th' u' v' H].
  now unfold empty_env in H.

  * (* sigma v = G psi -> ... *)
  rewrite <- EQpsi in Hra';
  inversion Hra'.
  * (* sigma v = phi U psi -> ... *)
  rewrite <- EQpsi in Hra';
  inversion Hra'.
  * (* sigma v = var v' -> ... *)
  rewrite <- EQpsi in Hra';
  inversion Hra'.

  - (* inductive step on ell *)
  intros w v theta Hw.
  assert (Hra' := Hra v).
  inversion Hw
  as [w' th u phi Hmo EQu EQw' EQth EQphi
     | h t th u r psi Hmo EQu [EQh EQt] EQth EQpsi
     | h t th u psi Hmo EQu [EQh EQt] EQth EQpsi 
     | w' th u psi phi Hpsi Hmo EQu EQw' EQth EQpsi
     | w' th u psi1 psi2 Hmo EQu EQw' EQth EQpsi
     | w' th u psi Hmo EQu EQw' EQth EQpsi
     | w' th u phi psi Hmo EQu EQw' EQth EQpsi
     | w' th u v' Hmo EQu EQw' EQth EQpsi].
  * (* sigma v = φ phi -> ... *)
  exists theta.
  destruct w as [| a w].
  -- (* w = nil -> ... *)
  exists (φ phi).
  destruct phi;
  split;
  try apply moveA_star_ref;
  now apply satisfied_at_end_is_finalA with theta.

  -- (* w' = a :: w -> ... *)
  exists (φ [tt]).
  destruct phi as [l0 | l0 | p1 p2];
  split;
  try apply finalA_tt;
  apply moveA_star_trans with (q2 := (φ [tt], theta, w));
  try apply tt_loop_exists.
  ++ (* sigma v = φ [l0] -> ... *)
  apply moveA_not_update with (phi := [l0]);
  try apply Hmo; apply ruleA_PHI.
  ++ (* sigma v = φ ~[l] -> ... *)
  apply moveA_not_update with (phi := ~[l0]);
  try apply Hmo; apply ruleA_PHI.
  ++ (* sigma v = φ p1 ../\ p2 -> ... *)
  apply moveA_not_update with (phi := p1 ../\ p2);
  try apply Hmo; apply ruleA_PHI.

  * (* sigma v = ↓ r, psi -> ... *)
  rewrite <- EQpsi in Hra';
  inversion Hra'.
  * (* sigma v = X psi -> ... *)
  rewrite <- EQpsi in Hra';
  inversion Hra'.

  * (* sigma v = psi ./\ phi -> ... *)
  rewrite <- EQpsi in Hra'.
  inversion Hra'
  as [| v0 phi0 [EQv0 EQphi0]| r v0 phi0 [EQv0 EQphi0]|].
  -- (* sigma v = X (var v0) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi
  as [| | h t th' u' psi' Hmo' EQu' [EQh EQt] EQth' EQpsi'| | | | |].
  clear th' EQth' u' EQu' psi' EQpsi'.
  rewrite<- EQh in Hmo.
  inversion Hmo'
  as [| | | | | | |w'' th' u' v1 Hf EQu' EQw'' EQth' EQv1].
  clear w'' EQw'' th' EQth' u' EQu' v1 EQv1.
  assert (IHl' := IHl t v0 theta Hf).
  destruct IHl' as [theta' [qF [Hfin Hmv]]].
  exists theta'.
  exists qF.
  split; auto.
  apply (moveA_star_trans _ _ (sigma v0, theta, t));
  auto.
  apply moveA_not_update with (phi := phi);
  auto.
  apply ruleA_X.
  -- (* sigma v = (↓ r, X (var v0)) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi
  as [| h t th' u' r' psi' Hmo' EQu' [EQh EQt] EQth' [EQr' EQpsi'] | | | | | |].
  clear th' EQth' u' EQu' r' EQr' psi' EQpsi'.
  rewrite<- EQh in Hmo.
  inversion Hmo'
  as [| | h' t' th' u' psi' Hmo'' EQu' [EQh' EQt'] EQth' EQpsi'| | | | |].
  clear h' EQh' t' EQt' th' EQth' u' EQu' psi' EQpsi'.
  inversion Hmo''
  as [| | | | | | |w'' th' u' v1 Hf EQu' EQw'' EQth' EQv1].
  assert (IHl' := IHl t v0 (update theta r (snd h)) Hf).
  destruct IHl' as [theta' [qF [Hfin Hmv]]].
  exists theta'.
  exists qF.
  split; auto.
  apply (moveA_star_trans _ _ (sigma v0, (update theta r (snd h)), t));
  auto.
  apply moveA_update with (phi := phi);
  auto.
  apply ruleA_STORE_X.

  * (* sigma v = psi1 .\/ psi2 -> ... *)
  rewrite <- EQpsi in Hra'.
  inversion Hra' as [v1 v2 [EQpsi1 EQpsi2]| | |].
  (* sigma v = var v1 .\/ var v2 -> ... *)
  rewrite <- EQpsi1 in Hmo.
  rewrite <- EQpsi2 in Hmo.
  unfold Fpow_emp in Hmo.
  unfold Fpow in Hmo.
  clear w' EQw' th EQth u EQu.
  destruct Hmo as [Hmo | Hmo].
  -- (* (w, theta |= Fpow sigma (S l), var v1) -> ... *)
  inversion Hmo as [| | | | | | |w' th' u' v' H EQu' EQw' EQth' EQv'].
  clear w' EQw' th' EQth' u' EQu' v' EQv'.
  assert (IHl' := IHl w v1 theta H).
  destruct IHl' as [theta' [qF [Hfin Hmv]]].
  exists theta'.
  exists qF.
  split; auto.
  apply (moveA_star_trans _ _ (sigma v1, theta, w));
  auto.
  apply moveA_epsilon.
  apply ruleA_OR_left.
  -- (* (w, theta |= Fpow sigma (S l), var v2) -> ... *)
  inversion Hmo as [| | | | | | |w' th' u' v' H EQu' EQw' EQth' EQv'].
  clear w' EQw' th' EQth' u' EQu' v' EQv'.
  assert (IHl' := IHl w v2 theta H).
  destruct IHl' as [theta' [qF [Hfin Hmv]]].
  exists theta'.
  exists qF.
  split; auto.
  apply (moveA_star_trans _ _ (sigma v2, theta, w));
  auto.
  apply moveA_epsilon.
  apply ruleA_OR_right.

  * (* sigma v = G psi -> ... *)
  rewrite <- EQpsi in Hra';
  inversion Hra'.
  * (* sigma v = phi U psi -> ... *)
  rewrite <- EQpsi in Hra';
  inversion Hra'.
  * (* sigma v = var v' -> ... *)
  rewrite <- EQpsi in Hra';
  inversion Hra'.
Qed.

Theorem A_is_equivalent_to_sigma_2 :
  forall w v theta,
  (exists theta' qF,
   finalA qF /\
   moveA_star sigma (sigma v, theta, w) (qF, theta', nil)) ->
  (w, theta |= lfpF, sigma v).
Proof.
  intros w v theta.
  intros [theta' [qF [Hfin Hmo]]].
  remember (sigma v, theta, w) as x.
  remember (qF, theta', nil) as y.
  generalize dependent theta.
  generalize dependent v.
  generalize dependent w.
  induction Hmo as [| c1 c2 c3 Hmo1 Hmo IH];
  intros w v theta Heqx.
  - (* qF = sigma v -> ... *)
  rewrite Heqy in Heqx.
  injection Heqx;
  intros EQw EQtheta' EQqF.
  rewrite EQqF in Hfin.
  rewrite<- EQw.
  inversion Hfin as [| | | |p1 p2 Hf1 Hf2 EQp1p2];
  apply models_PHI; try now auto.
  apply satisfied_at_end_is_finalA.
  now rewrite EQp1p2.
  - (* inductive step *)
  assert (IH' := IH Heqy).
  clear IH.
  rewrite Heqx in Hmo1.
  assert (Hra' := Hra v).
  inversion Hra'
  as [v1 v2 Hpsi| v1 phi Hpsi | r v1 phi Hpsi| phi Hpsi].
  + (* sigma v = var v1 .\/ var v2 -> ... *)
  apply models_OR.
  rewrite<- Hpsi in Hmo1.
  inversion Hmo1
  as [q1 q2 th w' Hru [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hru
     |q1 q2 phi r th h t Hru ].
  * clear q1 EQq1 th EQth w' EQw'.
  inversion Hru
  as [|v1' v2' [EQv1' EQv2'] EQeps EQreg EQq2'
      |v1' v2' [EQv1' EQv2'] EQeps EQreg EQq2'| |].
  -- (* q2 = sigma v1 -> ... *)
  clear v1' EQv1' v2' EQv2' EQeps EQreg.
  rewrite<- EQq2' in EQq2; clear EQq2'.
  symmetry in EQq2.
  left.
  apply models_var.
  rewrite HlfpF.
  unfold F.
  now apply IH'.
  -- (* q2 = sigma v2 -> ... *)
  clear v1' EQv1' v2' EQv2' EQeps EQreg.
  rewrite<- EQq2' in EQq2; clear EQq2'.
  symmetry in EQq2.
  right.
  apply models_var.
  rewrite HlfpF.
  unfold F.
  now apply IH'.
  * inversion Hru.
  * inversion Hru.
  + (* sigma v = X (var v1) ./\ phi -> ... *)
  rewrite<- Hpsi in Hmo1.
  inversion Hmo1
  as [q1 q2 th w' Hru [EQq1 EQth EQw'] EQq2
     |q1 q2 phi' th h t Hru Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi' r th h t Hru ].
  * inversion Hru.
  * clear q1 EQq1 th EQth.
  inversion Hru
  as [| | | v1' phi'' [EQv1' EQphi''] EQphi EQreg EQq2'|].
  clear v1' EQv1' phi'' EQphi'' EQreg.
  rewrite<- EQq2' in EQq2; clear EQq2'.
  symmetry in EQq2.
  apply models_AND; auto.
  apply models_X.
  apply models_var.
  rewrite HlfpF.
  unfold F.
  now apply IH'.
  * inversion Hru.
  + (* sigma v = (↓ r, X (var v1)) ./\ phi -> ... *)
  rewrite<- Hpsi in Hmo1.
  inversion Hmo1
  as [q1 q2 th w' Hru [EQq1 EQth EQw'] EQq2
     |q1 q2 phi' th h t Hru Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi' r' th h t Hru Hphi [EQq1 EQth EQht] EQq2].
  * inversion Hru.
  * inversion Hru.
  * clear q1 EQq1 th EQth.
  inversion Hru
  as [| | | |r'' v1' phi'' [EQr'' EQv1' EQphi''] EQphi EQr EQq2'].
  clear r'' EQr'' v1' EQv1' phi'' EQphi''.
  rewrite<- EQq2' in EQq2; clear EQq2'.
  symmetry in EQq2.
  apply models_AND; auto.
  apply models_STORE.
  apply models_X.
  apply models_var.
  rewrite HlfpF.
  unfold F.
  now apply IH'.
  + (* sigma v = φ phi -> ... *)
  rewrite<- Hpsi in Hmo1.
  inversion Hmo1
  as [q1 q2 th w' Hru [EQq1 EQth EQw'] EQq2
     |q1 q2 phi' th h t Hru Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi' r' th h t Hru Hphi [EQq1 EQth EQht] EQq2].
  * inversion Hru.
  * clear q1 EQq1 th EQth.
  inversion Hru
  as [phi'' EQphi'' EQphi EQreg EQq2'| | | |].
  now apply models_PHI.
  * inversion Hru.
Qed.

End CorrectnessOfConversionToRA.
