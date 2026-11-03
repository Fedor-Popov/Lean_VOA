import VOA.Huang.DLNSchur4Symbols

/-! # Mixed-root rewriting for the lower transition -/

namespace VOA.Huang.DLNSchur

section Basic
variable {R E : Type*} [CommRing R] [Group E]

@[simp] theorem rootHom_neg (X : Multiplicative R →* E) (t : R) :
    X (Multiplicative.ofAdd (-t)) = (X (Multiplicative.ofAdd t))⁻¹ :=
  X.map_inv _

@[simp] theorem weylWord_neg (X Y : Multiplicative R →* E) (u : Rˣ) :
    weylWord X Y (-u) = (weylWord X Y u)⁻¹ := by
  simp [weylWord, mul_inv_rev, mul_assoc]

end Basic

section Charts
variable {R E : Type*} [CommRing R] [Group E]

/-- Evaluating the top-left chart with a specified unit rather than a chosen witness. -/
theorem gaussLift_of_unit_top_left (X Y : Multiplicative R →* E)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (u : Rˣ) (hu : g 0 0 = u) :
    gaussLift X Y g = Y (Multiplicative.ofAdd (g 1 0 * (↑u⁻¹ : R))) *
      torusWord X Y u * X (Multiplicative.ofAdd (g 0 1 * (↑u⁻¹ : R))) := by
  have ha : IsUnit (g 0 0) := hu ▸ u.isUnit
  have he : ha.unit = u := Units.ext ((IsUnit.unit_spec ha).trans hu)
  simp only [gaussLift, dif_pos ha, he]

/-- The top-left chart recovers its own normal-form word. -/
theorem gaussLift_lower_torus_upper (X Y : Multiplicative R →* E)
    (r s : R) (u : Rˣ) :
    gaussLift X Y (lowerRoot r * torus u * upperRoot s) =
      Y (Multiplicative.ofAdd r) * torusWord X Y u * X (Multiplicative.ofAdd s) := by
  rw [gaussLift_of_unit_top_left X Y _ u (by
    simp [lowerRoot, torus, upperRoot, Matrix.mul_apply, Fin.sum_univ_two])]
  simp [lowerRoot, torus, upperRoot, Matrix.mul_apply, Fin.sum_univ_two,
    mul_assoc, mul_comm]

/-- Matrix lower transition while the top-left pivot remains a unit. -/
theorem lower_torus_upper_mul_lower_one (r s : R) (u v : Rˣ)
    (hv : (v : R) = 1 + s) :
    (lowerRoot r * torus u * upperRoot s) * lowerRoot 1 =
      lowerRoot (r + (↑u⁻¹ : R) ^ 2 * (↑v⁻¹ : R)) * torus (u * v) *
        upperRoot (s * (↑v⁻¹ : R)) := by
  have hs : s = (v : R) - 1 := by rw [hv]; ring
  rw [hs]
  have he : (u : R) * ((v : R) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * (↑v⁻¹ : R)))) =
      (↑u⁻¹ : R) := by
    calc
      _ = (↑u⁻¹ : R) * ((u : R) * (↑u⁻¹ : R)) * ((v : R) * (↑v⁻¹ : R)) := by ring
      _ = _ := by simp
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerRoot, torus, upperRoot, Matrix.mul_apply, Fin.sum_univ_two,
      pow_two, sub_eq_add_neg, mul_add, mul_assoc, mul_comm, he, add_comm, add_left_comm, add_assoc]

end Charts

section Normalized

variable {n : ℕ} {E : Type*} [Group E]
variable (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
variable (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
variable (hs : Function.Surjective π)
variable (X Y : Multiplicative (ZMod n) →* E)
variable (hX : ∀ t, π (X t) = upperRoot t.toAdd)
variable (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
variable (hn : RootNormalization h2 π X Y)

include h3 hs hX hY hn

/-- The alternate three-root expression for a normalized Weyl word. -/
theorem weylWord_eq_lower_upper_lower (u : (ZMod n)ˣ) :
    weylWord X Y u =
      Y (Multiplicative.ofAdd (-(↑u⁻¹ : ZMod n))) *
      X (Multiplicative.ofAdd (u : ZMod n)) *
      Y (Multiplicative.ofAdd (-(↑u⁻¹ : ZMod n))) := by
  have h := weylWord_upper_conj h2 h3 π hs X Y hX hY hn u (-(u : ZMod n))
  have he : -((↑u⁻¹ : ZMod n) ^ 2 * -(u : ZMod n)) = (↑u⁻¹ : ZMod n) := by
    simp [pow_two, mul_assoc]
  rw [he, rootHom_neg] at h
  have h' : X (Multiplicative.ofAdd (u : ZMod n)) *
      Y (Multiplicative.ofAdd (-(↑u⁻¹ : ZMod n))) =
      Y (Multiplicative.ofAdd (↑u⁻¹ : ZMod n)) * weylWord X Y u := by
    calc
      _ = weylWord X Y u * (X (Multiplicative.ofAdd (u : ZMod n)))⁻¹ := by
        unfold weylWord; group
      _ = _ := by rw [← h]; group
  rw [rootHom_neg]
  apply (mul_left_cancel (a := Y (Multiplicative.ofAdd (↑u⁻¹ : ZMod n))))
  calc
    _ = X (Multiplicative.ofAdd (u : ZMod n)) *
        Y (Multiplicative.ofAdd (-(↑u⁻¹ : ZMod n))) := h'.symm
    _ = _ := by rw [rootHom_neg]; group

/-- The mixed-root Gauss relation with lower parameter one needs no symbol hypothesis. -/
theorem upper_mul_lower_one (s : ZMod n) (v : (ZMod n)ˣ)
    (hv : (v : ZMod n) = 1 + s) :
    X (Multiplicative.ofAdd s) * Y (Multiplicative.ofAdd 1) =
      Y (Multiplicative.ofAdd (↑v⁻¹ : ZMod n)) * torusWord X Y v *
        X (Multiplicative.ofAdd (s * (↑v⁻¹ : ZMod n))) := by
  have hw := weylWord_eq_lower_upper_lower h2 h3 π hs X Y hX hY hn v
  have hx : X (Multiplicative.ofAdd (v : ZMod n)) =
      Y (Multiplicative.ofAdd (↑v⁻¹ : ZMod n)) * weylWord X Y v *
        Y (Multiplicative.ofAdd (↑v⁻¹ : ZMod n)) := by
    rw [hw, rootHom_neg]; group
  have hc := weylWord_lower_conj h2 h3 π hs X Y hX hY hn 1 (↑v⁻¹ : ZMod n)
  simp only [Units.val_one, one_pow, one_mul] at hc
  have ht : -(↑v⁻¹ : ZMod n) + 1 = s * (↑v⁻¹ : ZMod n) := by
    have hm := Units.mul_inv v
    rw [hv] at hm
    linear_combination -hm
  calc
    _ = X (Multiplicative.ofAdd (v : ZMod n)) * weylWord X Y (-1) *
        X (Multiplicative.ofAdd (1 : ZMod n)) := by
      rw [hv, rootHom_add]
      simp only [weylWord, Units.val_neg, Units.val_one, inv_neg, inv_one, neg_neg,
        rootHom_neg]
      have hcX : Commute (X (Multiplicative.ofAdd 1)) (X (Multiplicative.ofAdd s)) :=
        (Commute.all _ _).map X
      rw [hcX.eq]; group
    _ = Y (Multiplicative.ofAdd (↑v⁻¹ : ZMod n)) * weylWord X Y v *
        (weylWord X Y 1)⁻¹ * X (Multiplicative.ofAdd (-(↑v⁻¹ : ZMod n))) *
        X (Multiplicative.ofAdd 1) := by
      rw [hx, weylWord_neg, ← hc]; group
    _ = _ := by
      simp only [torusWord, mul_assoc]
      rw [← rootHom_add, ht]

/-- On the top-left chart, the lower transition is exactly one torus defect. -/
theorem gaussLift_mul_lower_one_top_iff (r s : ZMod n) (u v : (ZMod n)ˣ)
    (hv : (v : ZMod n) = 1 + s) :
    gaussLift X Y ((lowerRoot r * torus u * upperRoot s) * lowerRoot 1) =
        gaussLift X Y (lowerRoot r * torus u * upperRoot s) * Y (Multiplicative.ofAdd 1) ↔
      torusDefect X Y u v = 1 := by
  rw [lower_torus_upper_mul_lower_one r s u v hv,
    gaussLift_lower_torus_upper, gaussLift_lower_torus_upper]
  have hy := normalized_torus_lower_conj h2 h3 π hs X Y hn
    (torusWord X Y u) u (map_torusWord π X Y hX hY u) (↑v⁻¹ : ZMod n)
  have he : Y (Multiplicative.ofAdd r) * torusWord X Y u *
      X (Multiplicative.ofAdd s) * Y (Multiplicative.ofAdd 1) =
      Y (Multiplicative.ofAdd (r + (↑u⁻¹ : ZMod n) ^ 2 * (↑v⁻¹ : ZMod n))) *
        (torusWord X Y u * torusWord X Y v) *
        X (Multiplicative.ofAdd (s * (↑v⁻¹ : ZMod n))) := by
    calc
      _ = Y (Multiplicative.ofAdd r) * torusWord X Y u *
          (X (Multiplicative.ofAdd s) * Y (Multiplicative.ofAdd 1)) := by group
      _ = _ := by
        rw [upper_mul_lower_one h2 h3 π hs X Y hX hY hn s v hv, rootHom_add,
          ← hy]
        group
  rw [he, mul_right_cancel_iff, mul_left_cancel_iff, torusDefect]
  exact eq_comm.trans mul_inv_eq_one.symm

/-- The same exact obstruction, stated for a matrix and its two unit pivots. -/
theorem gaussLift_mul_lower_one_iff_of_unit_pivots
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) (u v : (ZMod n)ˣ)
    (hu : g 0 0 = u) (hv : (v : ZMod n) = 1 + g 0 1 * (↑u⁻¹ : ZMod n)) :
    gaussLift X Y (g * lowerRoot 1) = gaussLift X Y g * Y (Multiplicative.ofAdd 1) ↔
      torusDefect X Y u v = 1 := by
  have hg := gauss_of_unit_top_left g u hu
  have ht := gaussLift_mul_lower_one_top_iff h2 h3 π hs X Y hX hY hn
    (g 1 0 * (↑u⁻¹ : ZMod n)) (g 0 1 * (↑u⁻¹ : ZMod n)) u v hv
  rwa [← hg] at ht

/-- All top-to-top transitions follow from vanishing of the torus defects. -/
theorem gaussLift_mul_lower_one_of_unit_pivots
    (hz : ∀ u v : (ZMod n)ˣ, torusDefect X Y u v = 1)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (ha : IsUnit (g 0 0))
    (hb : IsUnit ((g * lowerRoot 1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) 0 0)) :
    gaussLift X Y (g * lowerRoot 1) = gaussLift X Y g * Y (Multiplicative.ofAdd 1) := by
  let u := ha.unit
  let v := u⁻¹ * hb.unit
  have hu : g 0 0 = (u : ZMod n) := (IsUnit.unit_spec ha).symm
  have hb' : (hb.unit : ZMod n) = g 0 0 + g 0 1 := by
    rw [IsUnit.unit_spec]
    simp [lowerRoot, Matrix.mul_apply, Fin.sum_univ_two]
  have hv : (v : ZMod n) = 1 + g 0 1 * (↑u⁻¹ : ZMod n) := by
    simp only [v, Units.val_mul, hb', hu, mul_add, Units.mul_inv, mul_comm]
  exact (gaussLift_mul_lower_one_iff_of_unit_pivots h2 h3 π hs X Y hX hY hn
    g u v hu hv).mpr (hz u v)

end Normalized

/-- An unconditional lower transition whenever the top-left parameter is a square. -/
theorem gaussLift_mul_lower_one_top_square {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {E : Type*} [Group E]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k)))
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    (X Y : Multiplicative (ZMod (p ^ k)) →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
    (hn : RootNormalization (primePower_coprime_two_three hp hp5).1 π X Y)
    (r s : ZMod (p ^ k)) (u v : (ZMod (p ^ k))ˣ)
    (hv : (v : ZMod (p ^ k)) = 1 + s) :
    gaussLift X Y ((lowerRoot r * torus (u ^ 2) * upperRoot s) * lowerRoot 1) =
      gaussLift X Y (lowerRoot r * torus (u ^ 2) * upperRoot s) *
        Y (Multiplicative.ofAdd 1) :=
  (gaussLift_mul_lower_one_top_iff (primePower_coprime_two_three hp hp5).1
    (primePower_coprime_two_three hp hp5).2 π hs X Y hX hY hn r s (u ^ 2) v hv).mpr
    (torusDefect_square_primePower hp hp5 π hs hc X Y hX hY hn u v)

end VOA.Huang.DLNSchur
