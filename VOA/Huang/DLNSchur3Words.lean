import VOA.Huang.DLNSchur3Conjugation
import VOA.Huang.DLNSchur3Gauss

/-! # Explicit words for the unit-pivot charts

The matrix identities give a set-theoretic section in every central extension.
The upper-root transition holds directly. The lower-root transition is a separate
relation problem; it is not inferred from the existence of a section.
-/

namespace VOA.Huang.DLNSchur

section Words

variable {R E : Type*} [CommRing R] [Group E]

/-- The standard Weyl word in a pair of root homomorphisms. -/
def weylWord (X Y : Multiplicative R →* E) (u : Rˣ) : E :=
  X (Multiplicative.ofAdd (u : R)) * Y (Multiplicative.ofAdd (-(↑u⁻¹ : R))) *
    X (Multiplicative.ofAdd (u : R))

/-- The standard torus word. Multiplicativity in `u` is not assumed. -/
def torusWord (X Y : Multiplicative R →* E) (u : Rˣ) : E :=
  weylWord X Y u * (weylWord X Y 1)⁻¹

@[simp] theorem torusWord_one (X Y : Multiplicative R →* E) :
    torusWord X Y 1 = 1 := by simp [torusWord]

theorem map_weylWord (π : E →* Matrix.SpecialLinearGroup (Fin 2) R)
    (X Y : Multiplicative R →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd) (u : Rˣ) :
    π (weylWord X Y u) = weyl u := by
  simp only [weylWord, map_mul, hX, hY, toAdd_ofAdd]
  exact (weyl_eq_roots u).symm

theorem map_torusWord (π : E →* Matrix.SpecialLinearGroup (Fin 2) R)
    (X Y : Multiplicative R →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd) (u : Rˣ) :
    π (torusWord X Y u) = torus u := by
  simp only [torusWord, map_mul, map_inv, map_weylWord π X Y hX hY]
  exact weyl_mul_weyl_one_inv u

/-- Explicit word on either unit-pivot chart. The fallback is excluded for prime powers. -/
noncomputable def gaussLift (X Y : Multiplicative R →* E)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) : E := by
  classical
  exact if ha : IsUnit (g 0 0) then
    Y (Multiplicative.ofAdd (g 1 0 * (↑ha.unit⁻¹ : R))) * torusWord X Y ha.unit *
      X (Multiplicative.ofAdd (g 0 1 * (↑ha.unit⁻¹ : R)))
  else if hc : IsUnit (g 1 0) then
    X (Multiplicative.ofAdd (g 0 0 * (↑hc.unit⁻¹ : R))) * weylWord X Y (-hc.unit⁻¹) *
      X (Multiplicative.ofAdd (g 1 1 * (↑hc.unit⁻¹ : R)))
  else 1

@[simp] theorem gaussLift_one (X Y : Multiplicative R →* E) :
    gaussLift X Y 1 = 1 := by
  classical
  simp [gaussLift]

/-- On either valid chart the explicit word maps to the prescribed matrix. -/
theorem map_gaussLift (π : E →* Matrix.SpecialLinearGroup (Fin 2) R)
    (X Y : Multiplicative R →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
    (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (hg : IsUnit (g 0 0) ∨ IsUnit (g 1 0)) : π (gaussLift X Y g) = g := by
  classical
  unfold gaussLift
  split_ifs with ha hc
  · simpa only [map_mul, hX, hY, toAdd_ofAdd,
      map_torusWord π X Y hX hY] using
      (gauss_of_unit_top_left g ha.unit (IsUnit.unit_spec ha).symm).symm
  · simpa only [map_mul, hX, toAdd_ofAdd,
      map_weylWord π X Y hX hY] using
      (gauss_of_unit_lower_left g hc.unit (IsUnit.unit_spec hc).symm).symm
  · exact False.elim (hg.elim ha hc)

theorem rootHom_add (X : Multiplicative R →* E) (s t : R) :
    X (Multiplicative.ofAdd (s + t)) = X (Multiplicative.ofAdd s) *
      X (Multiplicative.ofAdd t) := X.map_mul _ _

/-- Every Gauss word stays in any subgroup containing the two root ranges. -/
theorem gaussLift_mem (X Y : Multiplicative R →* E) (H : Subgroup E)
    (hX : ∀ t, X t ∈ H) (hY : ∀ t, Y t ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) : gaussLift X Y g ∈ H := by
  have hw : ∀ u, weylWord X Y u ∈ H := fun u =>
    H.mul_mem (H.mul_mem (hX _) (hY _)) (hX _)
  have ht : ∀ u, torusWord X Y u ∈ H := fun u => H.mul_mem (hw u) (H.inv_mem (hw 1))
  unfold gaussLift
  split_ifs
  · exact H.mul_mem (H.mul_mem (hY _) (ht _)) (hX _)
  · exact H.mul_mem (H.mul_mem (hX _) (hw _)) (hX _)
  · exact H.one_mem

/-- Right multiplication by an upper root preserves both unit-pivot charts. -/
theorem gaussLift_mul_upper (X Y : Multiplicative R →* E)
    (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (hg : IsUnit (g 0 0) ∨ IsUnit (g 1 0)) (t : R) :
    gaussLift X Y (g * upperRoot t) = gaussLift X Y g * X (Multiplicative.ofAdd t) := by
  classical
  have h00 : (g * upperRoot t) 0 0 = g 0 0 := by
    simp [upperRoot, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : (g * upperRoot t) 1 0 = g 1 0 := by
    simp [upperRoot, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : (g * upperRoot t) 0 1 = g 0 0 * t + g 0 1 := by
    simp [upperRoot, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (g * upperRoot t) 1 1 = g 1 0 * t + g 1 1 := by
    simp [upperRoot, Matrix.mul_apply, Fin.sum_univ_two]
  unfold gaussLift
  simp only [h00, h10, h01, h11]
  split_ifs with ha hc
  · have ht : (g 0 0 * t + g 0 1) * (↑ha.unit⁻¹ : R) =
        g 0 1 * (↑ha.unit⁻¹ : R) + t := by
      have hz : g 0 0 * (↑ha.unit⁻¹ : R) = 1 := by
        simpa only [IsUnit.unit_spec] using Units.mul_inv ha.unit
      calc
        _ = g 0 1 * (↑ha.unit⁻¹ : R) + (g 0 0 * (↑ha.unit⁻¹ : R)) * t := by ring
        _ = _ := by rw [hz, one_mul]
    rw [ht, rootHom_add]
    simp only [mul_assoc]
  · have ht : (g 1 0 * t + g 1 1) * (↑hc.unit⁻¹ : R) =
        g 1 1 * (↑hc.unit⁻¹ : R) + t := by
      have hz : g 1 0 * (↑hc.unit⁻¹ : R) = 1 := by
        simpa only [IsUnit.unit_spec] using Units.mul_inv hc.unit
      calc
        _ = g 1 1 * (↑hc.unit⁻¹ : R) + (g 1 0 * (↑hc.unit⁻¹ : R)) * t := by ring
        _ = _ := by rw [hz, one_mul]
    rw [ht, rootHom_add]
    simp only [mul_assoc]
  · exact False.elim (hg.elim ha hc)

end Words

end VOA.Huang.DLNSchur
