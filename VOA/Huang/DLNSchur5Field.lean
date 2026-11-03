import VOA.Huang.DLNSchur5Symbols

/-! # Weyl chart transitions over a field

These arguments keep the torus-multiplicativity hypothesis explicit.
-/

namespace VOA.Huang.DLNSchur

section Words
variable {R E : Type*} [CommRing R] [Group E]
variable (X Y : Multiplicative R →* E)
variable (hz : ∀ u v : Rˣ, torusDefect X Y u v = 1)

include hz

theorem torusWord_mul_of_defect_eq_one (u v : Rˣ) :
    torusWord X Y u * torusWord X Y v = torusWord X Y (u * v) :=
  mul_inv_eq_one.mp (hz u v)

theorem weylWord_one_sq_of_defect_eq_one :
    weylWord X Y 1 * weylWord X Y 1 = torusWord X Y (-1) := by
  have h := torusWord_mul_of_defect_eq_one X Y hz (-1) (-1)
  simp only [neg_mul_neg, one_mul, torusWord_one] at h
  have hi := eq_inv_of_mul_eq_one_left h
  calc
    _ = (torusWord X Y (-1))⁻¹ := by simp [torusWord]
    _ = _ := hi.symm

theorem weylWord_mul_one_of_defect_eq_one (u : Rˣ) :
    weylWord X Y u * weylWord X Y 1 = torusWord X Y (-u) := by
  calc
    _ = torusWord X Y u * (weylWord X Y 1 * weylWord X Y 1) := by
      unfold torusWord; group
    _ = _ := by
      rw [weylWord_one_sq_of_defect_eq_one X Y hz,
        torusWord_mul_of_defect_eq_one X Y hz]
      simp

end Words

section Matrices
variable {R E : Type*} [CommRing R] [Group E]

theorem lower_torus_upper_unit_mul_weyl (r : R) (u v : Rˣ) :
    (lowerRoot r * torus u * upperRoot (v : R)) * weyl 1 =
      lowerRoot (r + (↑u⁻¹ : R) ^ 2 * (↑v⁻¹ : R)) * torus (-(u * v)) *
        upperRoot (-(↑v⁻¹ : R)) := by
  have he : (u : R) * ((v : R) * ((↑u⁻¹ : R) * ((↑u⁻¹ : R) * (↑v⁻¹ : R)))) =
      (↑u⁻¹ : R) := by
    calc
      _ = (↑u⁻¹ : R) * ((u : R) * (↑u⁻¹ : R)) * ((v : R) * (↑v⁻¹ : R)) := by ring
      _ = _ := by simp
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerRoot, torus, upperRoot, weyl, Matrix.mul_apply, Fin.sum_univ_two,
      pow_two, mul_add, mul_assoc, mul_comm, he, add_comm]

theorem lower_torus_mul_weyl (r : R) (u : Rˣ) :
    (lowerRoot r * torus u) * weyl 1 =
      weyl u * upperRoot (-((u : R) ^ 2 * r)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerRoot, torus, upperRoot, weyl, Matrix.mul_apply, Fin.sum_univ_two,
      pow_two, mul_assoc, mul_comm]

theorem weyl_upper_mul_weyl (u : Rˣ) (t : R) :
    (weyl u * upperRoot t) * weyl 1 =
      lowerRoot (-((↑u⁻¹ : R) ^ 2 * t)) * torus (-u) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerRoot, torus, upperRoot, weyl, Matrix.mul_apply, Fin.sum_univ_two,
      pow_two, mul_assoc, mul_comm, mul_left_comm]

/-- Evaluation of the lower chart at a matrix whose top-left entry is zero. -/
theorem gaussLift_weyl_upper [Nontrivial R] (X Y : Multiplicative R →* E)
    (u : Rˣ) (t : R) :
    gaussLift X Y (weyl u * upperRoot t) =
      weylWord X Y u * X (Multiplicative.ofAdd t) := by
  classical
  have h00 : (weyl u * upperRoot t) 0 0 = 0 := by
    simp [weyl, upperRoot, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : (weyl u * upperRoot t) 1 0 = (-u⁻¹ : Rˣ) := by
    simp [weyl, upperRoot, Matrix.mul_apply, Fin.sum_univ_two]
  have hu : IsUnit ((weyl u * upperRoot t) 1 0) := h10 ▸ (-u⁻¹).isUnit
  have he : hu.unit = -u⁻¹ := Units.ext ((IsUnit.unit_spec hu).trans h10)
  simp only [gaussLift, h00, dif_neg not_isUnit_zero, dif_pos hu, he]
  simp [weyl, upperRoot, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_left_comm]

end Matrices

section Normalized
variable {n : ℕ} {E : Type*} [Group E]
variable (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
variable (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
variable (hs : Function.Surjective π)
variable (X Y : Multiplicative (ZMod n) →* E)
variable (hX : ∀ t, π (X t) = upperRoot t.toAdd)
variable (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
variable (hn : RootNormalization h2 π X Y)
variable (hz : ∀ u v : (ZMod n)ˣ, torusDefect X Y u v = 1)

include h3 hs hX hY hn hz

/-- Right multiplication by a Weyl word when the upper parameter is a unit. -/
theorem upper_unit_mul_weylWord_one (v : (ZMod n)ˣ) :
    X (Multiplicative.ofAdd (v : ZMod n)) * weylWord X Y 1 =
      Y (Multiplicative.ofAdd (↑v⁻¹ : ZMod n)) * torusWord X Y (-v) *
        X (Multiplicative.ofAdd (-(↑v⁻¹ : ZMod n))) := by
  have hw := weylWord_eq_lower_upper_lower h2 h3 π hs X Y hX hY hn v
  have hx : X (Multiplicative.ofAdd (v : ZMod n)) =
      Y (Multiplicative.ofAdd (↑v⁻¹ : ZMod n)) * weylWord X Y v *
        Y (Multiplicative.ofAdd (↑v⁻¹ : ZMod n)) := by
    rw [hw, rootHom_neg]; group
  have hc := weylWord_upper_conj h2 h3 π hs X Y hX hY hn 1
    (-(↑v⁻¹ : ZMod n))
  simp only [inv_one, Units.val_one, one_pow, one_mul, neg_neg] at hc
  calc
    _ = Y (Multiplicative.ofAdd (↑v⁻¹ : ZMod n)) * weylWord X Y v *
        (weylWord X Y 1 * X (Multiplicative.ofAdd (-(↑v⁻¹ : ZMod n))) *
          (weylWord X Y 1)⁻¹) * weylWord X Y 1 := by rw [hc, ← hx]
    _ = _ := by rw [← weylWord_mul_one_of_defect_eq_one X Y hz]; group

theorem gaussLift_lower_torus_upper_unit_mul_weyl (r : ZMod n)
    (u v : (ZMod n)ˣ) :
    gaussLift X Y ((lowerRoot r * torus u * upperRoot (v : ZMod n)) * weyl 1) =
      gaussLift X Y (lowerRoot r * torus u * upperRoot (v : ZMod n)) *
        weylWord X Y 1 := by
  rw [lower_torus_upper_unit_mul_weyl, gaussLift_lower_torus_upper,
    gaussLift_lower_torus_upper]
  have hy := normalized_torus_lower_conj h2 h3 π hs X Y hn
    (torusWord X Y u) u (map_torusWord π X Y hX hY u) (↑v⁻¹ : ZMod n)
  have ht := torusWord_mul_of_defect_eq_one X Y hz u (-v)
  simp only [mul_neg] at ht
  calc
    _ = Y (Multiplicative.ofAdd r) * torusWord X Y u *
        (Y (Multiplicative.ofAdd (↑v⁻¹ : ZMod n)) * torusWord X Y (-v) *
          X (Multiplicative.ofAdd (-(↑v⁻¹ : ZMod n)))) := by
      rw [rootHom_add, ← ht, ← hy]; group
    _ = _ := by rw [← upper_unit_mul_weylWord_one h2 h3 π hs X Y hX hY hn hz]; group

omit hz in
theorem gaussLift_lower_torus_mul_weyl [Nontrivial (ZMod n)]
    (r : ZMod n) (u : (ZMod n)ˣ) :
    gaussLift X Y ((lowerRoot r * torus u) * weyl 1) =
      gaussLift X Y (lowerRoot r * torus u) * weylWord X Y 1 := by
  rw [lower_torus_mul_weyl, gaussLift_weyl_upper]
  have hg : gaussLift X Y (lowerRoot r * torus u) =
      Y (Multiplicative.ofAdd r) * torusWord X Y u := by
    simpa using gaussLift_lower_torus_upper X Y r 0 u
  rw [hg]
  have hc := weylWord_upper_conj h2 h3 π hs X Y hX hY hn u
    (-((u : ZMod n) ^ 2 * r))
  have he : -((↑u⁻¹ : ZMod n) ^ 2 * -((u : ZMod n) ^ 2 * r)) = r := by
    simp [pow_two, mul_assoc, mul_comm]
  rw [he] at hc
  rw [← hc, torusWord]; group

theorem gaussLift_weyl_upper_mul_weyl [Nontrivial (ZMod n)]
    (u : (ZMod n)ˣ) (t : ZMod n) :
    gaussLift X Y ((weyl u * upperRoot t) * weyl 1) =
      gaussLift X Y (weyl u * upperRoot t) * weylWord X Y 1 := by
  rw [weyl_upper_mul_weyl, gaussLift_weyl_upper]
  have hg : gaussLift X Y
      (lowerRoot (-((↑u⁻¹ : ZMod n) ^ 2 * t)) * torus (-u)) =
      Y (Multiplicative.ofAdd (-((↑u⁻¹ : ZMod n) ^ 2 * t))) *
        torusWord X Y (-u) := by
    simpa using gaussLift_lower_torus_upper X Y (-((↑u⁻¹ : ZMod n) ^ 2 * t)) 0 (-u)
  rw [hg, ← weylWord_mul_one_of_defect_eq_one X Y hz,
    ← weylWord_upper_conj h2 h3 π hs X Y hX hY hn u t]
  group

/-- All three Weyl transitions cover the field case. -/
theorem gaussLift_mul_weyl_prime [Fact n.Prime]
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) :
    gaussLift X Y (g * weyl 1) = gaussLift X Y g * weylWord X Y 1 := by
  by_cases ha : g 0 0 = 0
  · have hc : g 1 0 ≠ 0 := by
      intro hc
      have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
        simpa only [Matrix.det_fin_two] using g.2
      simp [ha, hc] at hd
    let u := Units.mk0 (g 1 0) hc
    have hg := gauss_of_unit_lower_left g u rfl
    simp only [ha, zero_mul, upperRoot_zero, one_mul] at hg
    rw [hg]
    exact gaussLift_weyl_upper_mul_weyl h2 h3 π hs X Y hX hY hn hz _ _
  · let u := Units.mk0 (g 0 0) ha
    have hg := gauss_of_unit_top_left g u rfl
    by_cases hb : g 0 1 = 0
    · simp only [hb, zero_mul, upperRoot_zero, mul_one] at hg
      rw [hg]
      exact gaussLift_lower_torus_mul_weyl h2 h3 π hs X Y hX hY hn _ _
    · let v := Units.mk0 (g 0 1 * (↑u⁻¹ : ZMod n))
        (mul_ne_zero hb (Units.ne_zero _))
      rw [hg]
      exact gaussLift_lower_torus_upper_unit_mul_weyl h2 h3 π hs X Y hX hY hn hz _ u v

/-- Weyl covariance and the already proved upper transition give the lower transition. -/
theorem gaussLift_mul_lower_one_prime [Fact n.Prime]
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) :
    gaussLift X Y (g * lowerRoot 1) = gaussLift X Y g * Y (Multiplicative.ofAdd 1) := by
  have hw := gaussLift_mul_weyl_prime h2 h3 π hs X Y hX hY hn hz
  have hwi : ∀ q, gaussLift X Y (q * (weyl (1 : (ZMod n)ˣ))⁻¹) =
      gaussLift X Y q * (weylWord X Y 1)⁻¹ := by
    intro q
    have h := hw (q * (weyl 1)⁻¹)
    simp only [mul_assoc, inv_mul_cancel, mul_one] at h
    rw [h]; group
  have hm : lowerRoot (1 : ZMod n) =
      weyl 1 * upperRoot (-1) * (weyl 1)⁻¹ := by
    simpa using (weyl_upper_conj (1 : (ZMod n)ˣ) (-1)).symm
  have hu : ∀ q : Matrix.SpecialLinearGroup (Fin 2) (ZMod n),
      IsUnit (q 0 0) ∨ IsUnit (q 1 0) := by
    intro q
    by_cases ha : q 0 0 = 0
    · right
      apply isUnit_iff_ne_zero.mpr
      intro hc
      have hd : q 0 0 * q 1 1 - q 0 1 * q 1 0 = 1 := by
        simpa only [Matrix.det_fin_two] using q.2
      simp [ha, hc] at hd
    · exact Or.inl (isUnit_iff_ne_zero.mpr ha)
  have he := weylWord_upper_conj h2 h3 π hs X Y hX hY hn 1 (-1)
  simp only [inv_one, Units.val_one, one_pow, one_mul, neg_neg] at he
  rw [hm, ← mul_assoc, ← mul_assoc, hwi,
    gaussLift_mul_upper X Y _ (hu _) (-1), hw]
  rw [← he]; group

end Normalized

/-- Over a prime field there is no independent boundary residual once the torus is settled. -/
theorem gaussLowerRelations_prime_of_torusGeneratorRelations {p : ℕ} (hp : p.Prime)
    (h2 : Nat.Coprime 2 p) (h3 : Nat.Coprime 3 p)
    (ht : TorusGeneratorRelations p h2) : GaussLowerRelations p h2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro E _ π hs hc X Y hX hY hgen hn g
  obtain ⟨w, hw⟩ := IsCyclic.exists_monoid_generator (α := (ZMod p)ˣ)
  have hw0 := ht E π hs hc X Y hX hY hgen hn w hw
  apply gaussLift_mul_lower_one_prime h2 h3 π hs X Y hX hY hn _ g
  intro u v
  rcases torusDefect_eq_one_or_generator h2 h3 π hs X Y hX hY hn hc w hw u v with h | h
  · exact h
  · exact h.trans hw0

/-- An unconditional prime-field Schur result for `p = 1 mod 4`. -/
theorem schurTrivial_SL_prime_mod_four_one {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hp4 : p % 4 = 1) :
    VOA.Huang.DLNBeyl.SchurTrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  have h2 : Nat.Coprime 2 p := by
    simpa only [pow_one] using (primePower_coprime_two_three (k := 1) hp hp5).1
  have h3 : Nat.Coprime 3 p := by
    simpa only [pow_one] using (primePower_coprime_two_three (k := 1) hp hp5).2
  have ht : TorusGeneratorRelations p h2 := by
    simpa only [pow_one] using torusGeneratorRelations_primePower_mod_four_one
      (k := 1) hp hp5 hp4 (by omega)
  have hl := gaussLowerRelations_prime_of_torusGeneratorRelations hp h2 h3 ht
  convert! schurTrivial_of_gaussLowerRelations hp (k := 1) (by omega)
    (by simpa only [pow_one] using h2) (by simpa only [pow_one] using h3)
    (by simpa only [pow_one] using hl) using 1
  rw [pow_one]

end VOA.Huang.DLNSchur
