import VOA.Huang.DLNSchur2Cyclic

/-! # Torsion root lifts away from two and three

The diagonal unit `2` has square character `4`; the difference `3` is invertible.
This corrects each cyclic root separately. No mixed-root presentation relation is assumed.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

variable {n : ℕ} [NeZero n] {E : Type*} [Group E]

/-- In every central extension, the upper generator has a torsion lift in the derived group. -/
theorem exists_upper_torsion_lift
    (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) :
    ∃ a ∈ commutator E, π a = upperRoot 1 ∧ a ^ n = 1 := by
  let u := ZMod.unitOfCoprime 2 h2
  let v := ZMod.unitOfCoprime 3 h3
  let t : ZMod n := ↑v⁻¹
  have hu : (u : ZMod n) = 2 := by simp [u]
  have ht : (3 : ZMod n) * t = 1 := by
    change (3 : ZMod n) * (↑v⁻¹ : ZMod n) = 1
    have hv : (v : ZMod n) = 3 := by simp [v]
    rw [← hv]; exact Units.mul_inv v
  obtain ⟨h, hh⟩ := hs (torus u)
  obtain ⟨b, hb⟩ := hs (upperRoot t)
  have hconj : π (h * b * h⁻¹) = upperRoot (4 * t) := by
    simp only [map_mul, map_inv, hh, hb, torus_upper_conj, hu]
    norm_num
  have hcomm : Commute (h * b * h⁻¹) b := upper_lifts_commute π hs hc hconj hb
  have hbn : b ^ n ∈ Subgroup.center E := hc (by
    simp [MonoidHom.mem_ker, hb])
  refine ⟨⁅h, b⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top h)
    (Subgroup.mem_top b), ?_, commutator_pow_eq_one_of_commute h b n hcomm hbn⟩
  change π ((h * b * h⁻¹) * b⁻¹) = _
  rw [map_mul, hconj, map_inv, hb]
  have heq : upperRoot (4 * t) = upperRoot (1 : ZMod n) * upperRoot t := by
    rw [← upperRoot_add]
    congr 1
    linear_combination ht
  rw [heq, mul_inv_cancel_right]

/-- The same correction for the lower generator, using the inverse torus. -/
theorem exists_lower_torsion_lift
    (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) :
    ∃ b ∈ commutator E, π b = lowerRoot 1 ∧ b ^ n = 1 := by
  let u := ZMod.unitOfCoprime 2 h2
  let v := ZMod.unitOfCoprime 3 h3
  let t : ZMod n := ↑v⁻¹
  have hu : (u : ZMod n) = 2 := by simp [u]
  have ht : (3 : ZMod n) * t = 1 := by
    change (3 : ZMod n) * (↑v⁻¹ : ZMod n) = 1
    have hv : (v : ZMod n) = 3 := by simp [v]
    rw [← hv]; exact Units.mul_inv v
  obtain ⟨h, hh⟩ := hs (torus u⁻¹)
  obtain ⟨b, hb⟩ := hs (lowerRoot t)
  have hconj : π (h * b * h⁻¹) = lowerRoot (4 * t) := by
    simp only [map_mul, map_inv, hh, hb, torus_lower_conj, inv_inv, hu]
    norm_num
  have hcomm : Commute (h * b * h⁻¹) b := lower_lifts_commute π hs hc hconj hb
  have hbn : b ^ n ∈ Subgroup.center E := hc (by
    simp [MonoidHom.mem_ker, hb])
  refine ⟨⁅h, b⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top h)
    (Subgroup.mem_top b), ?_, commutator_pow_eq_one_of_commute h b n hcomm hbn⟩
  change π ((h * b * h⁻¹) * b⁻¹) = _
  rw [map_mul, hconj, map_inv, hb]
  have heq : lowerRoot (4 * t) = lowerRoot (1 : ZMod n) * lowerRoot t := by
    rw [← lowerRoot_add]
    congr 1
    linear_combination ht
  rw [heq, mul_inv_cancel_right]

/-- The root corrections imply perfectness, without any assertion about the Schur multiplier. -/
theorem commutator_SL_eq_top (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n) :
    commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) = ⊤ := by
  have hc : (MonoidHom.id (Matrix.SpecialLinearGroup (Fin 2) (ZMod n))).ker ≤
      Subgroup.center _ := by simp
  obtain ⟨a, ha, hpa, _⟩ := exists_upper_torsion_lift h2 h3 (MonoidHom.id _)
    Function.surjective_id hc
  obtain ⟨b, hb, hpb, _⟩ := exists_lower_torsion_lift h2 h3 (MonoidHom.id _)
    Function.surjective_id hc
  apply top_unique
  rw [← root_generators n, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · simpa only [MonoidHom.id_apply] using hpa ▸ ha
  · simpa only [MonoidHom.id_apply] using hpb ▸ hb

/-- Arithmetic hypotheses for every prime at least five, at every exponent. -/
theorem primePower_coprime_two_three {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.Coprime 2 (p ^ k) ∧ Nat.Coprime 3 (p ^ k) := by
  constructor
  · apply Nat.Coprime.pow_right
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
  · apply Nat.Coprime.pow_right
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm

/-- Unconditional perfectness for the prime powers at least five. -/
theorem commutator_SL_primePower_eq_top {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k))) = ⊤ := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact commutator_SL_eq_top (primePower_coprime_two_three hp hp5).1
    (primePower_coprime_two_three hp hp5).2

end VOA.Huang.DLNSchur
