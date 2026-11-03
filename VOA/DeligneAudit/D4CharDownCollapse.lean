import VOA.DeligneAudit.D4CharDownHomogeneous

/-! Finite homogeneous substitution in two formal variables is a ring homomorphism. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

/-- The two orders of summation in the product of homogeneous bivariate slices. -/
theorem gtSum_antidiagonal_grid {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ℕ → ℕ → ℕ → ℕ → A) :
    (∑ p ∈ Finset.antidiagonal n, ∑ b ∈ Finset.antidiagonal p.2,
      ∑ a ∈ Finset.antidiagonal p.1, f a.1 b.1 a.2 b.2) =
      ∑ p ∈ Finset.antidiagonal n, ∑ a ∈ Finset.antidiagonal p.1,
        ∑ b ∈ Finset.antidiagonal p.2, f a.1 a.2 b.1 b.2 := by
  classical
  simp_rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun z _ => ⟨(z.2.2.1 + z.2.1.1, z.2.2.2 + z.2.1.2),
      ⟨(z.2.2.1, z.2.1.1), (z.2.2.2, z.2.1.2)⟩⟩)
    (fun z _ => ⟨(z.2.1.1 + z.2.2.1, z.2.1.2 + z.2.2.2),
      ⟨(z.2.1.2, z.2.2.2), (z.2.1.1, z.2.2.1)⟩⟩) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hz ⊢
    exact ⟨by omega, trivial, trivial⟩
  · intro z hz
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hz ⊢
    exact ⟨by omega, trivial, trivial⟩
  · intro z hz
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hz
    have he : (z.2.2.1 + z.2.2.2, z.2.1.1 + z.2.1.2) = z.1 := by
      apply Prod.ext <;> dsimp <;> omega
    dsimp
    simp only [he]
  · intro z hz
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hz
    have he : (z.2.1.1 + z.2.1.2, z.2.2.1 + z.2.2.2) = z.1 := by
      apply Prod.ext <;> dsimp <;> omega
    dsimp
    simp only [he]
  · intro z _
    rfl

variable {R : Type*} [CommRing R]

/-- Substitute (a*s,b*s), using only a finite sum in each degree. -/
def gtBiCollapse (a b : R) (F : GTBiSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => ∑ p ∈ Finset.antidiagonal n,
    a ^ p.1 * b ^ p.2 * gtBiCoeff p.1 p.2 F

theorem gtBiCollapse_mul (a b : R) (F G : GTBiSeries R) :
    gtBiCollapse a b (F * G) = gtBiCollapse a b F * gtBiCollapse a b G := by
  apply PowerSeries.ext
  intro n
  simp only [gtBiCollapse, coeff_mk, coeff_mul]
  simp_rw [gtBiCoeff_mul, Finset.mul_sum]
  calc
    _ = ∑ p ∈ Finset.antidiagonal n, ∑ v ∈ Finset.antidiagonal p.2,
        ∑ u ∈ Finset.antidiagonal p.1,
          (a ^ u.1 * b ^ v.1 * gtBiCoeff u.1 v.1 F) *
            (a ^ u.2 * b ^ v.2 * gtBiCoeff u.2 v.2 G) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro u hu
      have hv := Finset.mem_antidiagonal.mp hv
      have hu := Finset.mem_antidiagonal.mp hu
      rw [← hu, ← hv, pow_add, pow_add]
      ring
    _ = _ := by
      rw [gtSum_antidiagonal_grid n (fun i j k l =>
        (a ^ i * b ^ j * gtBiCoeff i j F) * (a ^ k * b ^ l * gtBiCoeff k l G))]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm

theorem gtBiCollapse_one (a b : R) : gtBiCollapse a b 1 = 1 := by
  apply PowerSeries.ext
  intro n
  rw [gtBiCollapse, coeff_mk, coeff_one]
  by_cases hn : n = 0
  · subst n
    simp [gtBiCoeff]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro p hp
    have hp := Finset.mem_antidiagonal.mp hp
    by_cases h₁ : p.1 = 0
    · have h₂ : p.2 ≠ 0 := by omega
      simp [gtBiCoeff, coeff_one, h₂]
    · by_cases h₂ : p.2 = 0 <;> simp [gtBiCoeff, coeff_one, h₁, h₂]

/-- Homogeneous substitution preserves products, so it applies to the Euler kernel itself. -/
def gtBiCollapseHom (a b : R) : GTBiSeries R →+* PowerSeries R where
  toFun := gtBiCollapse a b
  map_one' := gtBiCollapse_one a b
  map_mul' := gtBiCollapse_mul a b
  map_zero' := by ext n; simp [gtBiCollapse]
  map_add' F G := by
    apply PowerSeries.ext
    intro n
    simp [gtBiCollapse, mul_add, Finset.sum_add_distrib]

/-- A series in the first variable becomes its ordinary rescaling. -/
theorem gtBiCollapse_C (a b : R) (F : PowerSeries R) :
    gtBiCollapseHom a b (PowerSeries.C F) = rescale a F := by
  apply PowerSeries.ext
  intro n
  change coeff n (gtBiCollapse a b (PowerSeries.C F)) = _
  rw [gtBiCollapse, coeff_mk]
  rw [Finset.sum_eq_single (n, 0)]
  · simp [gtBiCoeff, coeff_zero_eq_constantCoeff, coeff_rescale]
  · intro p hp hn
    have hp := Finset.mem_antidiagonal.mp hp
    have hz : p.2 ≠ 0 := by
      intro hz
      apply hn
      apply Prod.ext <;> dsimp <;> omega
    simp [gtBiCoeff, coeff_C, hz]
  · simp

/-- A series in the second variable becomes its ordinary rescaling. -/
theorem gtBiCollapse_map_C (a b : R) (F : PowerSeries R) :
    gtBiCollapseHom a b (F.map PowerSeries.C) = rescale b F := by
  apply PowerSeries.ext
  intro n
  change coeff n (gtBiCollapse a b (F.map PowerSeries.C)) = _
  rw [gtBiCollapse, coeff_mk]
  rw [Finset.sum_eq_single (0, n)]
  · simp [gtBiCoeff, coeff_map, coeff_zero_eq_constantCoeff, coeff_rescale]
  · intro p hp hn
    have hp := Finset.mem_antidiagonal.mp hp
    have hz : p.1 ≠ 0 := by
      intro hz
      apply hn
      apply Prod.ext <;> dsimp <;> omega
    simp [gtBiCoeff, coeff_map, coeff_C, hz]
  · simp

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtSum_antidiagonal_grid
#print axioms VOA.DeligneAudit.D4Char.gtBiCollapse_mul
#print axioms VOA.DeligneAudit.D4Char.gtBiCollapse_one
#print axioms VOA.DeligneAudit.D4Char.gtBiCollapse_C
#print axioms VOA.DeligneAudit.D4Char.gtBiCollapse_map_C
