(*
 * mu-calculus for data words (of finite length)
 *)

Require Export Nat Arith.
Require Export List.

(* data words *)

Definition D := nat.
Definition At := nat.
Definition Sigma := At -> bool.
Definition data_word := list (Sigma * D)%type.

(* LTL syntax *)

Definition register := nat.
Definition V := nat.

Inductive ltl_atom :=
  | tt : ltl_atom
  | MATCH : register -> ltl_atom
  | p : At -> ltl_atom  (* an atomic proposition *)
  | END : ltl_atom
  .

Inductive ltl_phi :=
  | pos : ltl_atom -> ltl_phi  (* a positive literal *)
  | neg : ltl_atom -> ltl_phi  (* a negative literal *)
  | AND_phi : ltl_phi -> ltl_phi -> ltl_phi
  .

Inductive ltl :=
  | var : V -> ltl
  | OR  : ltl -> ltl -> ltl
  | AND : ltl -> ltl_phi -> ltl
  | STORE : register -> ltl -> ltl
  | X : ltl -> ltl
  | until : ltl_phi -> ltl -> ltl
  | PHI : ltl_phi -> ltl
  | G : ltl_phi -> ltl
  .

Notation "'↑' r" := (MATCH r) (at level 75).
Notation "a '.\/' b" := (OR   a b) (at level 85, right associativity).
Notation "a './\' b" := (AND  a b) (at level 75, right associativity).
Notation "a '../\' b" := (AND_phi a b) (at level 75, right associativity).
Notation  "'[' a ']'" := (pos a).
Notation "'~[' a ']'" := (neg a).
Notation "'φ' p" := (PHI p) (at level 78).
Notation "a 'U' b" := (until a b) (at level 73, right associativity).
Notation "'↓' r ',' psi" := (STORE r psi) (at level 200).

(*
Check (AND (STORE 1 (X (OR (PHI (neg (p 1))) (PHI (pos (p 2)))))) (pos (↑ 1))).
Check ((↓1, X ((φ ~[p 1]) .\/ (φ [p 2]))) ./\ [↑1]).
*)

(* utilities *)

(* Forall_suffix_until p "cd" "abcd" <-> p "abcd" /\ p "bcd" *)
Inductive Forall_suffix_until {A : Type} :
  (list A -> Prop) -> list A -> list A -> Prop :=
  | Forall_sfx_until_eq : forall p l, Forall_suffix_until p l l
  | Forall_sfx_until : forall p s x l,
      Forall_suffix_until p s l -> p (x::l) ->
      Forall_suffix_until p s (x::l)
  .
Definition Forall_nonnil_suffix {A : Type}
  (p : list A -> Prop) (l : list A) : Prop :=
  Forall_suffix_until p nil l.

(* LTL semantics *)

Definition Theta := register -> D.

Definition update
  (theta : Theta) (i : register) (d : D) : Theta :=
  fun (r : register) => if r =? i then d else theta r.

Definition theta_bot : Theta :=
  fun (r : register) => 0.

Definition Env := V -> Theta -> data_word -> Prop.

Definition empty_env : Env :=
  fun (v : V) (theta : Theta) (w : data_word) => False.

Definition models_atom
  (w : data_word) (theta : Theta) (atom : ltl_atom)
  : Prop :=
  match w, atom with
  | _, tt => True
  | h::t, p a => fst h a = true
  | h::t, ↑ r => snd h = theta r
  | nil, END => True
  | _, _ => False
  end.

Fixpoint models_phi
  (w : data_word) (theta : Theta) (phi : ltl_phi)
  : Prop :=
  match phi with
  | pos atom =>   models_atom w theta atom
  | neg atom => ~ models_atom w theta atom
  | AND_phi p1 p2 =>
      models_phi w theta p1 /\ models_phi w theta p2
  end.

(*
Fixpoint models
  (u : Env) (w : data_word) (theta : Theta) (psi : ltl)
  : Prop :=
  match psi, w with
  | φ phi, _ => models_phi w theta phi
  | (↓ r, psi'), h::t => models u w (update theta r (snd h)) psi'
  | X psi', h::t => models u t theta psi'
  | psi' ./\ phi,  _ => models u w theta psi' /\ models_phi w theta phi
  | psi1 .\/ psi2, _ => models u w theta psi1 \/ models u w theta psi2
  | G phi, _ => Forall_nonnil_suffix (fun t => models_phi t theta phi) w
  | phi U psi', _ => exists w',
        models u w' theta psi' /\
        Forall_mid_suffix (fun t => models_phi t theta phi) w' w
  | var v, _ => In (w, theta) (u v)
  | _, nil => False
  end.
*)

Inductive models :
  Env -> data_word -> Theta -> ltl -> Prop :=
  | models_PHI : forall w theta u phi,
      models_phi w theta phi ->
      models u w theta (φ phi)
  | models_STORE : forall h t theta u r psi,
      models u (h::t) (update theta r (snd h)) psi ->
      models u (h::t) theta (↓ r, psi)
  | models_X : forall h t theta u psi,
      models u t theta psi ->
      models u (h::t) theta (X psi)
  | models_AND : forall w theta u psi phi,
      models u w theta psi ->
      models_phi w theta phi ->
      models u w theta (AND psi phi)
  | models_OR : forall w theta u psi1 psi2,
      models u w theta psi1 \/
      models u w theta psi2 ->
      models u w theta (OR psi1 psi2)
  | models_G : forall w theta u phi,
      Forall_nonnil_suffix (fun t => models_phi t theta phi) w ->
      models u w theta (G phi)
  | models_U : forall w theta u phi psi,
      (exists w',
       models u w' theta psi /\
       Forall_suffix_until (fun t => models_phi t theta phi) w' w) ->
      models u w theta (phi U psi)
  | models_var : forall w theta (u : Env) v,
      u v theta w ->
      models u w theta (var v)
  .

Notation "'(' w ',' theta '|=' u ',' psi ')'"
  := (models u w theta psi).

(* Equality of two ltl formulas *)

Axiom ltl_extensionality :
  forall psi1 psi2 : ltl,
    (forall w theta u, (w, theta |= u, psi1) <-> (w, theta |= u, psi2))
    -> psi1 = psi2.

Axiom Theta_extensionality :
  forall theta1 theta2 : Theta,
    (forall r, theta1 r = theta2 r) -> theta1 = theta2.

(* distribution over OR *)

Lemma distr_X_over_OR :
  forall psi1 psi2,
    (X (psi1 .\/ psi2)) = (X psi1 .\/ X psi2).
Proof.
  intros psi1 psi2.
  apply ltl_extensionality.
  intros w theta.
  split.
  - intros H.
  apply models_OR.
  inversion H
  as [| | h t th u' psi Hor EQu' EQht EQth EQpsi | | | | |].
  clear th EQth u' EQu' psi EQpsi.
  inversion Hor
  as [| | | | w' th u' p1 p2 Hor' EQu' EQw' EQth [EQp1 EQp2] | | |].
  clear w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  destruct Hor' as [Hor' | Hor'].
  + left. now apply models_X.
  + right. now apply models_X.
  - intros H.
  inversion H
  as [| | | | w' th u' p1 p2 Hor EQu' EQw' EQth [EQp1 EQp2] | | |].
  clear w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  destruct Hor as [Hor | Hor];
  inversion Hor
  as [| | h t th u' psi Hor' EQu' EQht EQth EQpsi | | | | |];
  clear th EQth u' EQu' psi EQpsi;
  apply models_X;
  apply models_OR.
  + now left.
  + now right.
Qed.

Lemma G_equals_phi_U_end :
  forall phi,
    (G phi) = (phi U (φ [END])).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros w theta.
  split.
  - intros H.
  inversion H
  as [| | | | | w' th u' p Hsuf EQu' EQw' EQth EQp | |].
  clear w' EQw' th EQth u' EQu' p EQp.
  apply models_U.
  exists nil.
  split.
  + apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
  + apply Hsuf.
  - intros H.
  inversion H
  as [| | | | | | w' th u' p1 p2 Hu EQu' EQw' EQth [EQp1 EQp2]|].
  clear w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  destruct Hu as [w' [Hw' Hsuf]].
  inversion Hw'
  as [w'' th u' p Hend EQu' EQw'' EQth EQp | | | | | | |].
  clear w'' EQw'' th EQth u' EQu' p EQp.
  unfold models_phi in Hend.
  unfold models_atom in Hend.
  destruct w'.
  + now apply models_G.
  + contradiction.
Qed.

Lemma U_equals_psi_or_phi_and_XU :
  forall phi psi,
    (phi U psi) = (psi .\/ X (phi U psi) ./\ phi).
Proof.
  intros phi psi.
  apply ltl_extensionality.
  intros w theta.
  split.
  - intros H.
  apply models_OR.
  inversion H
  as [| | | | | | w' th u' p1 p2 Hsuf EQu' EQw' EQth [EQp1 EQp2]|].
  clear H w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  destruct Hsuf as [w' [Hw' Hsuf]].
  destruct w as [| h t].
  + inversion Hsuf as [p l EQp EQl EQw' |].
  rewrite EQw' in Hw'.
  now left.
  + inversion Hsuf
  as [p l EQp EQl EQw'| p s x l Hsuf' Hp EQp EQs [EQx EQl]].
  * rewrite EQw' in Hw'.
  now left.
  * clear p EQp s EQs x EQx l EQl.
  right.
  apply models_AND; auto.
  apply models_X.
  apply models_U.
  now exists w'.
  - intros H.
  inversion H
  as [| | | | w' th u' p1 p2 Hor EQu' EQw' EQth [EQp1 EQp2] | | |].
  clear H w' EQw' th u' EQu' EQth p1 EQp1 p2 EQp2.
  apply models_U.
  destruct Hor as [H | H].
  + exists w.
  split; auto.
  apply Forall_sfx_until_eq.
  + inversion H
  as [| | | w' th u' p1 p2 Hw Hp EQu' EQw' EQth [EQp1 EQp2]| | | |].
  clear w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  inversion Hw
  as [| |h t th u' p1 Ht EQu' EQht EQth EQp1| | | | |].
  clear th EQth u' EQu' p1 EQp1.
  inversion Ht
  as [| | | | | | w' th u' p1 p2 Hsuf EQu' EQw' EQth [EQp1 EQp2]|].
  clear H w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  destruct Hsuf as [w' [Hw' Hsuf]].
  exists w'.
  rewrite <- EQht in Hp.
  split; auto.
  apply Forall_sfx_until; auto.
Qed.

Section GandU.

Variable phi : ltl_phi.
Variable theta : Theta.
Variable u : Env.

Lemma nil_satisfies_U_end :
  (nil, theta |= u, phi U (φ [END])).
Proof.
  apply models_U.
  exists nil.
  split.
  - apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
  - apply Forall_sfx_until_eq.
Qed.

Lemma nil_satisfies_G_any :
  (nil, theta |= u, G phi).
Proof.
  rewrite G_equals_phi_U_end.
  apply nil_satisfies_U_end.
Qed.

End GandU.

Section GandF.

Variable phi : ltl_atom.
Variable theta : Theta.
Variable u : Env.

Lemma F_equals_not_G_not_1 :
  ~ (nil, theta |= u, φ [phi]) ->
  forall w, (w, theta |= u, [tt] U (φ [phi])) -> ~ (w, theta |= u, G ~[phi]).
Proof.
  intros Hphi.
  intros w.

  intros Hf Hg.
  inversion Hf
  as [| | | | | | w' th u' phi' psi Hu EQu' EQw' EQth [EQphi' EQpsi]|].
  clear w' EQw' th EQth u' EQu' phi' EQphi' psi EQpsi.
  destruct Hu as [w' [Hf1 Hf2]].
  inversion Hg
  as [| | | | |w'' th u' phi' Hg' EQu' EQw'' EQth EQphi'| |].
  clear w'' EQw'' th EQth u' EQu' phi' EQphi'.
  destruct phi.
  + (* phi = tt -> ... *)
  apply Hphi.
  apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
  + (* phi = ↑ r -> ... *)
  clear Hf Hg.
  unfold Forall_nonnil_suffix in Hg'.
  induction Hf2
  as [p l | p s x l Hf2 IH Hp].
  * destruct l as [| x l].
  -- inversion Hf1
  as [w1 th1 u1 phi' Hm EQu1 EQw1 EQth1 EQphi'| | | | | | |].
  clear w1 EQw1 th1 EQth1 u1 EQu1 phi' EQphi'.
  unfold models_phi in Hm.
  now unfold models_atom in Hm.
  -- inversion Hf1
  as [w1 th1 u1 phi' Hm EQu1 EQw1 EQth1 EQphi'| | | | | | |].
  clear w1 EQw1 th1 EQth1 u1 EQu1 phi' EQphi'.
  inversion Hg'
  as [| p' s x' l' Hsl Hml EQp' EQs [EQx' EQl']].
  clear p' EQp' s EQs x' EQx' l' EQl'.
  unfold models_phi in Hm.
  unfold models_phi in Hml.
  now apply Hml in Hm.
  * apply (IH Hf1).
  inversion Hg'
  as [| p' s' x' l' Hsl Hml EQp' EQs' [EQx' EQl']].
  clear p' EQp' s' EQs' x' EQx' l' EQl'.
  apply Hsl.
  + (* phi = p a -> ... *)
  clear Hf Hg.
  unfold Forall_nonnil_suffix in Hg'.
  induction Hf2
  as [p l | p s x l Hf2 IH Hp].
  * destruct l as [| x l].
  -- inversion Hf1
  as [w1 th1 u1 phi' Hm EQu1 EQw1 EQth1 EQphi'| | | | | | |].
  clear w1 EQw1 th1 EQth1 u1 EQu1 phi' EQphi'.
  unfold models_phi in Hm.
  now unfold models_atom in Hm.
  -- inversion Hf1
  as [w1 th1 u1 phi' Hm EQu1 EQw1 EQth1 EQphi'| | | | | | |].
  clear w1 EQw1 th1 EQth1 u1 EQu1 phi' EQphi'.
  inversion Hg'
  as [| p' s x' l' Hsl Hml EQp' EQs [EQx' EQl']].
  clear p' EQp' s EQs x' EQx' l' EQl'.
  unfold models_phi in Hm.
  unfold models_phi in Hml.
  now apply Hml in Hm.
  * apply (IH Hf1).
  inversion Hg'
  as [| p' s' x' l' Hsl Hml EQp' EQs' [EQx' EQl']].
  clear p' EQp' s' EQs' x' EQx' l' EQl'.
  apply Hsl.
  + (* phi = END -> ... *)
  apply Hphi.
  apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
Qed.

Lemma F_equals_not_G_not_2 :
  ~ (nil, theta |= u, φ ~[phi]) ->
  forall w, (w, theta |= u, [tt] U (φ ~[phi])) -> ~ (w, theta |= u, G [phi]).
Proof.
  intros Hphi.
  intros w.

  intros Hf Hg.
  inversion Hf
  as [| | | | | | w' th u' phi' psi Hu EQu' EQw' EQth [EQphi' EQpsi]|].
  clear w' EQw' th EQth u' EQu' phi' EQphi' psi EQpsi.
  destruct Hu as [w' [Hf1 Hf2]].
  inversion Hg
  as [| | | | |w'' th u' phi' Hg' EQu' EQw'' EQth EQphi'| |].
  clear w'' EQw'' th EQth u' EQu' phi' EQphi'.
  destruct phi.
  + (* phi = tt -> ... *)
  clear Hf Hg.
  unfold Forall_nonnil_suffix in Hg'.
  induction Hf2
  as [p l | p s x l Hf2 IH Hp].
  * destruct l as [| x l].
  -- inversion Hf1
  as [w1 th1 u1 phi' Hm EQu1 EQw1 EQth1 EQphi'| | | | | | |].
  clear w1 EQw1 th1 EQth1 u1 EQu1 phi' EQphi'.
  unfold models_phi in Hm.
  now unfold models_atom in Hm.
  -- inversion Hf1
  as [w1 th1 u1 phi' Hm EQu1 EQw1 EQth1 EQphi'| | | | | | |].
  clear w1 EQw1 th1 EQth1 u1 EQu1 phi' EQphi'.
  inversion Hg'
  as [| p' s x' l' Hsl Hml EQp' EQs [EQx' EQl']].
  clear p' EQp' s EQs x' EQx' l' EQl'.
  unfold models_phi in Hm.
  apply Hm.
  now unfold models_atom.
  * apply (IH Hf1).
  inversion Hg'
  as [| p' s' x' l' Hsl Hml EQp' EQs' [EQx' EQl']].
  clear p' EQp' s' EQs' x' EQx' l' EQl'.
  apply Hsl.
  + (* phi = ↑ r -> ... *)
  apply Hphi.
  apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
  + (* phi = p a -> ... *)
  apply Hphi.
  apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
  + (* phi = END -> ... *)
  clear Hf Hg.
  unfold Forall_nonnil_suffix in Hg'.
  induction Hf2
  as [p l | p s x l Hf2 IH Hp].
  * destruct l as [| x l].
  -- inversion Hf1
  as [w1 th1 u1 phi' Hm EQu1 EQw1 EQth1 EQphi'| | | | | | |].
  clear w1 EQw1 th1 EQth1 u1 EQu1 phi EQphi'.
  unfold models_phi in Hm.
  now unfold models_atom in Hm.
  -- inversion Hf1
  as [w1 th1 u1 phi' Hm EQu1 EQw1 EQth1 EQphi'| | | | | | |].
  clear w1 EQw1 th1 EQth1 u1 EQu1 phi EQphi'.
  inversion Hg'
  as [| p' s x' l' Hsl Hml EQp' EQs [EQx' EQl']].
  clear p' EQp' s EQs x' EQx' l' EQl'.
  unfold models_phi in Hm.
  unfold models_phi in Hml.
  now apply Hm in Hml.
  * apply (IH Hf1).
  inversion Hg'
  as [| p' s' x' l' Hsl Hml EQp' EQs' [EQx' EQl']].
  clear p' EQp' s' EQs' x' EQx' l' EQl'.
  apply Hsl.
Qed.

Lemma F_equals_not_G_not_3 :
  forall w, ~ (w, theta |= u, [tt] U (φ [phi])) -> (w, theta |= u, G ~[phi]).
Proof.
  intros w.
  intros Hnf.
  apply models_G.
  unfold Forall_nonnil_suffix.
  induction w as [| x l IH].
  - apply Forall_sfx_until_eq.
  - apply Forall_sfx_until.
  + apply IH.
  intros Hl.
  apply Hnf.
  inversion Hl
  as [| | | | | | w' th u' phi' psi Hu EQu' EQw' EQth [EQphi' EQpsi]|].
  clear w' EQw' th EQth u' EQu' phi' EQphi' psi EQpsi.
  destruct Hu as [w' [Hf1 Hf2]].
  apply models_U.
  exists w'.
  split; auto.
  apply Forall_sfx_until; auto.
  unfold models_phi.
  now unfold models_atom.
  + unfold models_phi.
  intros Hxl.
  apply Hnf.
  apply models_U.
  exists (x :: l).
  split.
  * apply models_PHI.
  apply Hxl.
  * apply Forall_sfx_until_eq.
Qed.

Hypothesis classic : forall P, ~~P -> P.

Lemma F_equals_not_G_not_4 :
  forall w, ~ (w, theta |= u, [tt] U (φ ~[phi])) -> (w, theta |= u, G [phi]).
Proof.
  intros w.
  intros Hnf.
  apply models_G.
  unfold Forall_nonnil_suffix.
  induction w as [| x l IH].
  - apply Forall_sfx_until_eq.
  - apply Forall_sfx_until.
  + apply IH.
  intros Hl.
  apply Hnf.
  inversion Hl
  as [| | | | | | w' th u' phi' psi Hu EQu' EQw' EQth [EQphi' EQpsi]|].
  clear w' EQw' th EQth u' EQu' phi' EQphi' psi EQpsi.
  destruct Hu as [w' [Hf1 Hf2]].
  apply models_U.
  exists w'.
  split; auto.
  apply Forall_sfx_until; auto.
  unfold models_phi.
  now unfold models_atom.
  + unfold models_phi.
  apply classic.
  intros Hnxl.
  apply Hnf.
  apply models_U.
  exists (x :: l).
  split.
  * apply models_PHI.
  apply Hnxl.
  * apply Forall_sfx_until_eq.
Qed.

End GandF.

Lemma ff_neq_end :
  (φ ~[tt]) <> φ [END].
Proof.
  intros H.
  assert (H1 : ~ (nil, theta_bot |= empty_env, φ ~[tt])).
  { intros Hff.
  inversion Hff as [w th u' phi Hphi EQu' EQw EQth EQphi| | | | | | |].
  unfold models_phi in Hphi.
  now unfold models_atom in Hphi. }
  assert (H2 : (nil, theta_bot |= empty_env, φ [END])).
  { apply models_PHI.
  unfold models_phi.
  now unfold models_atom. }
  rewrite <- H in H2.
  now apply H1 in H2.
Qed.
