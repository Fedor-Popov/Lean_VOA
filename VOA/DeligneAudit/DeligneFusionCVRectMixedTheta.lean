import VOA.DeligneAudit.DeligneFusionCVRectMixedTwo

/-!
# Actual highest-weight theta strings for two opposite rectangles

The hypotheses are the two actual simple-root CV single-part relations and
the current highest-weight data. Higher theta truncation and all transported
highest-weight facts are derived. No theta-string dimension, filtration span,
or fusion-product identification is assumed.
-/

namespace VOA.DeligneAudit.A2.CVRectMixedTheta

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CLNormal VOA.DeligneAudit.CLFilt
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVRectMixedTwo

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The two genuine single-part simple-root presentations. -/
structure TwoRectRel (R : CurrentModule bracketTable V) (w : V) (k l : ℕ) : Prop where
  raising : ∀ (e : Fin 8), e.val < 3 → ∀ r, R.op e r w = 0
  cartan_pos : ∀ (h : Fin 8), 6 ≤ h.val → ∀ r, 1 ≤ r → R.op h r w = 0
  cartan_first : R.op 6 0 w = (k : ℂ) • w
  cartan_second : R.op 7 0 w = (l : ℂ) • w
  first : CVRel (R.op 3) [k] w
  second : CVRel (R.op 4) [l] w

variable {R : CurrentModule bracketTable V} {w : V} {k l : ℕ}

def thetaDesc (R : CurrentModule bracketTable V) (w : V) (d : ℕ) : V :=
  (R.op 5 1 ^ d) w

private theorem comm_kill_power (D Y : Module.End ℂ V) (v : V)
    (hDY : Commute D Y) (hD : D v = 0) (d : ℕ) : D ((Y ^ d) v) = 0 := by
  rw [← Module.End.mul_apply, (hDY.pow_right d).eq, Module.End.mul_apply, hD, map_zero]

private theorem add_comm_kill_power (D Y Z : Module.End ℂ V) (v : V)
    (hDY : D * Y = Y * D + Z) (hD : D v = 0)
    (hZ : ∀ d : ℕ, Z ((Y ^ d) v) = 0) : ∀ d : ℕ, D ((Y ^ d) v) = 0 := by
  intro d
  induction d with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hD
  | succ d ih =>
      rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply D Y, hDY,
        LinearMap.add_apply, Module.End.mul_apply, ih, map_zero, hZ d, add_zero]

private theorem weight_power (H Y : Module.End ℂ V) (v : V) (μ γ : ℂ)
    (hHY : H * Y = Y * H + γ • Y) (hH : H v = μ • v) :
    ∀ d : ℕ, H ((Y ^ d) v) = (μ + d * γ) • (Y ^ d) v := by
  intro d
  induction d with
  | zero => simpa using hH
  | succ d ih =>
      rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply H Y, hHY,
        LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
        ih, map_smul]
      push_cast
      module

theorem first_pos (h : TwoRectRel R w k l) (r : ℕ) (hr : 1 ≤ r) : R.op 3 r w = 0 :=
  trunc_of_cvrel h.first r (by simpa using hr)

theorem second_pos (h : TwoRectRel R w k l) (r : ℕ) (hr : 1 ≤ r) : R.op 4 r w = 0 :=
  trunc_of_cvrel h.second r (by simpa using hr)

/-- Higher theta truncation follows from the two simple-root truncations. -/
theorem theta_high (h : TwoRectRel R w k l) (r : ℕ) (hr : 2 ≤ r) : R.op 5 r w = 0 := by
  have hc := congrArg (fun T : Module.End ℂ V => T w) (c_f4f3 R (r - 1) 1)
  simp only [Module.End.mul_apply, LinearMap.add_apply,
    first_pos h 1 le_rfl, second_pos h (r - 1) (by omega), map_zero, zero_add] at hc
  simpa only [show r - 1 + 1 = r by omega] using hc.symm

theorem first_pos_desc (h : TwoRectRel R w k l) (d r : ℕ) (hr : 1 ≤ r) :
    R.op 3 r (thetaDesc R w d) = 0 :=
  comm_kill_power _ _ _ (c_f1f5 R r 1) (first_pos h r hr) d

theorem second_pos_desc (h : TwoRectRel R w k l) (d r : ℕ) (hr : 1 ≤ r) :
    R.op 4 r (thetaDesc R w d) = 0 :=
  comm_kill_power _ _ _ (c_f4f5 R r 1) (second_pos h r hr) d

theorem theta_high_desc (h : TwoRectRel R w k l) (d r : ℕ) (hr : 2 ≤ r) :
    R.op 5 r (thetaDesc R w d) = 0 :=
  comm_kill_power _ _ _ ((CVRoots.sl2_highest R).hFF r 1) (theta_high h r hr) d

theorem cartan_pos_desc (h : TwoRectRel R w k l) (d : ℕ)
    (hh : Fin 8) (hhh : 6 ≤ hh.val) (r : ℕ) (hr : 1 ≤ r) :
    R.op hh r (thetaDesc R w d) = 0 := by
  have hh' : hh = 6 ∨ hh = 7 := by omega
  rcases hh' with rfl | rfl
  · apply add_comm_kill_power _ _ ((-1 : ℂ) • R.op 5 (r + 1)) w
      (c_h1 R r 1).2.1 (h.cartan_pos 6 (by decide) r hr) _ d
    intro q
    simp only [LinearMap.smul_apply]
    change (-1 : ℂ) • R.op 5 (r + 1) (thetaDesc R w q) = 0
    rw [theta_high_desc h q (r + 1) (by omega), smul_zero]
  · apply add_comm_kill_power _ _ ((-1 : ℂ) • R.op 5 (r + 1)) w
      (c_h2 R r 1).2.1 (h.cartan_pos 7 (by decide) r hr) _ d
    intro q
    simp only [LinearMap.smul_apply]
    change (-1 : ℂ) • R.op 5 (r + 1) (thetaDesc R w q) = 0
    rw [theta_high_desc h q (r + 1) (by omega), smul_zero]

theorem raising_desc (h : TwoRectRel R w k l) (d : ℕ)
    (e : Fin 8) (he : e.val < 3) (r : ℕ) : R.op e r (thetaDesc R w d) = 0 := by
  have he' : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  rcases he' with rfl | rfl | rfl
  · apply add_comm_kill_power _ _ ((-1 : ℂ) • R.op 4 (r + 1)) w
      (c_e1f5 R r 1) (h.raising 0 (by decide) r) _ d
    intro q
    simp only [LinearMap.smul_apply]
    change (-1 : ℂ) • R.op 4 (r + 1) (thetaDesc R w q) = 0
    rw [second_pos_desc h q (r + 1) (by omega), smul_zero]
  · apply add_comm_kill_power _ _ (R.op 3 (r + 1)) w
      (c_e2f5 R r 1) (h.raising 1 (by decide) r) _ d
    intro q
    exact first_pos_desc h q (r + 1) (by omega)
  · apply add_comm_kill_power _ _ (R.op 6 (r + 1) + R.op 7 (r + 1)) w
      (c_eθf5 R r 1) (h.raising 2 (by decide) r) _ d
    intro q
    simp only [LinearMap.add_apply]
    change R.op 6 (r + 1) (thetaDesc R w q) +
      R.op 7 (r + 1) (thetaDesc R w q) = 0
    rw [cartan_pos_desc h q 6 (by decide) (r + 1) (by omega),
      cartan_pos_desc h q 7 (by decide) (r + 1) (by omega), add_zero]

theorem first_weight_desc (h : TwoRectRel R w k l) (d : ℕ) :
    R.op 6 0 (thetaDesc R w d) = ((k : ℂ) - d) • thetaDesc R w d := by
  have hh := weight_power (R.op 6 0) (R.op 5 1) w (k : ℂ) (-1)
    (c_h1 R 0 1).2.1 h.cartan_first d
  simpa only [mul_neg, mul_one, sub_eq_add_neg] using hh

theorem second_weight_desc (h : TwoRectRel R w k l) (d : ℕ) :
    R.op 7 0 (thetaDesc R w d) = ((l : ℂ) - d) • thetaDesc R w d := by
  have hh := weight_power (R.op 7 0) (R.op 5 1) w (l : ℂ) (-1)
    (c_h2 R 0 1).2.1 h.cartan_second d
  simpa only [mul_neg, mul_one, sub_eq_add_neg] using hh

theorem first_nil (h : TwoRectRel R w k l) : (R.op 3 0 ^ (k + 1)) w = 0 := by
  have hn := h.first (k + 1) 0 0 (by omega) (by simp [T]; omega)
  simpa only [Q_s_zero] using hn

theorem second_nil (h : TwoRectRel R w k l) : (R.op 4 0 ^ (l + 1)) w = 0 := by
  have hn := h.second (l + 1) 0 0 (by omega) (by simp [T]; omega)
  simpa only [Q_s_zero] using hn

theorem first_local_nil_desc (h : TwoRectRel R w k l) (d : ℕ) :
    (R.op 3 0 ^ (k + 1)) (thetaDesc R w d) = 0 :=
  comm_kill_power _ _ _ ((show Commute (R.op 3 0) (R.op 5 1)
    from c_f1f5 R 0 1).pow_left (k + 1)) (first_nil h) d

theorem second_local_nil_desc (h : TwoRectRel R w k l) (d : ℕ) :
    (R.op 4 0 ^ (l + 1)) (thetaDesc R w d) = 0 :=
  comm_kill_power _ _ _ ((show Commute (R.op 4 0) (R.op 5 1)
    from c_f4f5 R 0 1).pow_left (l + 1)) (second_nil h) d

private theorem sharp_nil_of_local (E F H : Module.End ℂ V) (u : V) (m K : ℕ)
    (hEF : ∀ x, E (F x) - F (E x) = H x)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x)
    (hE : E u = 0) (hH : H u = (m : ℂ) • u) (hN : (F ^ K) u = 0) :
    (F ^ (m + 1)) u = 0 := by
  have hH' : H u = (((m : ℕ) : ℤ) : ℂ) • u := by simpa using hH
  rw [Module.End.pow_apply] at hN ⊢
  have hs := (hw_pow E F H hEF hHF hE hH' K hN).2 (by omega)
  simpa only [Int.toNat_natCast] using hs

theorem first_sharp_nil_desc (h : TwoRectRel R w k l) (d : ℕ) (hd : d ≤ k) :
    (R.op 3 0 ^ (k - d + 1)) (thetaDesc R w d) = 0 := by
  apply sharp_nil_of_local (R.op 0 0) (R.op 3 0) (R.op 6 0)
    (thetaDesc R w d) (k - d) (k + 1)
  · intro v
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, Nat.zero_add] using
      congrArg (fun T : Module.End ℂ V => T v) ((CVRoots.sl2_first R).hEF 0 0)
  · intro v
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Nat.zero_add] using
      congrArg (fun T : Module.End ℂ V => T v) ((CVRoots.sl2_first R).hHF 0 0)
  · exact raising_desc h d 0 (by decide) 0
  · rw [Nat.cast_sub hd]
    exact first_weight_desc h d
  · exact first_local_nil_desc h d

theorem second_sharp_nil_desc (h : TwoRectRel R w k l) (d : ℕ) (hd : d ≤ l) :
    (R.op 4 0 ^ (l - d + 1)) (thetaDesc R w d) = 0 := by
  apply sharp_nil_of_local (R.op 1 0) (R.op 4 0) (R.op 7 0)
    (thetaDesc R w d) (l - d) (l + 1)
  · intro v
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, Nat.zero_add] using
      congrArg (fun T : Module.End ℂ V => T v) ((CVRoots.sl2_second R).hEF 0 0)
  · intro v
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Nat.zero_add] using
      congrArg (fun T : Module.End ℂ V => T v) ((CVRoots.sl2_second R).hHF 0 0)
  · exact raising_desc h d 1 (by decide) 0
  · rw [Nat.cast_sub hd]
    exact second_weight_desc h d
  · exact second_local_nil_desc h d

/-- The actual theta descendant has the sharp classical cyclic-piece bound. -/
theorem desc_cycDeg_zero_bound (h : TwoRectRel R w k l) (d : ℕ)
    (hd : d ≤ min k l) :
    FiniteDimensional ℂ (cycDeg R (thetaDesc R w d) 0) ∧
      Module.finrank ℂ (cycDeg R (thetaDesc R w d) 0) ≤
        Fintype.card (CVRectMixedClassical.ClassicalIndex (k - d) (l - d)) := by
  apply cycDeg_zero_bound (raising_desc h d) (cartan_pos_desc h d)
  · rw [Nat.cast_sub (hd.trans (min_le_left _ _))]
    exact first_weight_desc h d
  · rw [Nat.cast_sub (hd.trans (min_le_right _ _))]
    exact second_weight_desc h d
  · exact first_sharp_nil_desc h d (hd.trans (min_le_left _ _))
  · exact second_sharp_nil_desc h d (hd.trans (min_le_right _ _))

private theorem root_negative_kills (E H F : ℕ → Module.End ℂ V) (hS : SL2 E H F)
    (u : V) (μ : ℤ) (hμ : μ < 0) (hEu : E 0 u = 0)
    (hHu : H 0 u = (μ : ℂ) • u) (K : ℕ) (hN : (F 0 ^ K) u = 0) : u = 0 := by
  have hEF : ∀ v, E 0 (F 0 v) - F 0 (E 0 v) = H 0 v := by
    intro v
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, Nat.zero_add] using
      congrArg (fun T : Module.End ℂ V => T v) (hS.hEF 0 0)
  have hHF : ∀ v, H 0 (F 0 v) - F 0 (H 0 v) = (-2 : ℂ) • F 0 v := by
    intro v
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Nat.zero_add] using congrArg (fun T : Module.End ℂ V => T v) (hS.hHF 0 0)
  rw [Module.End.pow_apply] at hN
  exact (hw_pow (E 0) (F 0) (H 0) hEF hHF hEu hHu K hN).1 hμ

/-- The theta string stops at the smaller rectangle size, derived from the
negative highest weight and actual local nilpotence of a simple root. -/
theorem thetaDesc_eq_zero (h : TwoRectRel R w k l) (d : ℕ) (hd : min k l < d) :
    thetaDesc R w d = 0 := by
  by_cases hk : k < d
  · apply root_negative_kills (R.op 0) (R.op 6) (R.op 3) (CVRoots.sl2_first R)
      (thetaDesc R w d) ((k : ℤ) - d) (by omega)
      (raising_desc h d 0 (by decide) 0) _ (k + 1) (first_local_nil_desc h d)
    push_cast
    exact first_weight_desc h d
  · have hl : l < d := by omega
    apply root_negative_kills (R.op 1) (R.op 7) (R.op 4) (CVRoots.sl2_second R)
      (thetaDesc R w d) ((l : ℤ) - d) (by omega)
      (raising_desc h d 1 (by decide) 0) _ (l + 1) (second_local_nil_desc h d)
    push_cast
    exact second_weight_desc h d

end

end VOA.DeligneAudit.A2.CVRectMixedTheta

#print axioms VOA.DeligneAudit.A2.CVRectMixedTheta.theta_high
#print axioms VOA.DeligneAudit.A2.CVRectMixedTheta.raising_desc
#print axioms VOA.DeligneAudit.A2.CVRectMixedTheta.first_weight_desc
#print axioms VOA.DeligneAudit.A2.CVRectMixedTheta.desc_cycDeg_zero_bound
#print axioms VOA.DeligneAudit.A2.CVRectMixedTheta.thetaDesc_eq_zero
