import VOA.Huang.NgSchauenburgMixedExhaustion
import VOA.Huang.NgSchauenburgTEquivariance

/-! # The exact reach of the T shift

The proved T identity reduces the second index modulo the first index.
It computes multiples of the first index from zero; it does not compute the
other residue classes from zero. All identities below use the actual indicators.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

/-- Iterate T in both directions, including on the zero-degree indicators. -/
theorem generalizedIndicatorAll_add_mul_degree (F : SphericalFusion C) (A : Center C)
    (V : C) {t : ℂ} (ht : t ≠ 0)
    (hj : (F.j A.1).hom = t • centralDrinfeldMorphism A) (m l k : ℤ) :
    generalizedIndicatorAll F A V m (l + k * m) =
      (t⁻¹) ^ k * generalizedIndicatorAll F A V m l := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show l + ((k : ℤ) + 1) * m = (l + k * m) + m by ring,
      generalizedIndicatorAll_add_degree F A V ht hj, ih,
      zpow_add_one₀ (inv_ne_zero ht)]
    ring
  | pred k ih =>
    have h := generalizedIndicatorAll_add_degree F A V ht hj m
      (l + (-(k : ℤ) - 1) * m)
    rw [show l + (-(k : ℤ) - 1) * m + m = l + -(k : ℤ) * m by ring, ih] at h
    rw [zpow_sub_one₀ (inv_ne_zero ht), inv_inv]
    calc
      _ = t * (t⁻¹ * generalizedIndicatorAll F A V m
          (l + (-(k : ℤ) - 1) * m)) := by rw [← mul_assoc, mul_inv_cancel₀ ht, one_mul]
      _ = _ := by rw [← h]; ring

/-- Euclidean reduction leaves one independent second-index residue per degree. -/
theorem generalizedIndicatorAll_emod (F : SphericalFusion C) (A : Center C)
    (V : C) {t : ℂ} (ht : t ≠ 0)
    (hj : (F.j A.1).hom = t • centralDrinfeldMorphism A) (m l : ℤ) :
    generalizedIndicatorAll F A V m l = (t⁻¹) ^ (l / m) *
      generalizedIndicatorAll F A V m (l % m) := by
  have h := generalizedIndicatorAll_add_mul_degree F A V ht hj m (l % m) (l / m)
  rwa [Int.emod_add_ediv_mul] at h

/-- Exactly the zero-residue orbit is determined by the zero-power trace. -/
theorem generalizedIndicatorInt_mul_degree (F : SphericalFusion C) (A : Center C)
    (V : C) (n : ℕ) {t : ℂ} (ht : t ≠ 0)
    (hj : (F.j A.1).hom = t • centralDrinfeldMorphism A) (k : ℤ) :
    generalizedIndicatorInt F.toPivotal A V n (k * (n + 1 : ℕ)) =
      (t⁻¹) ^ k * (Module.finrank ℂ (A.1 ⟶ tensorPower V (n + 1)) : ℂ) := by
  have h := generalizedIndicatorAll_add_mul_degree F A V ht hj (n + 1 : ℕ) 0 k
  have hp : (0 : ℤ) < (n + 1 : ℕ) := by omega
  simpa only [generalizedIndicatorAll, if_pos hp, Int.toNat_natCast,
    Nat.add_sub_cancel, zero_add, generalizedIndicatorInt_zero] using h

/-- From second index zero, T shifts reach precisely the multiples of the degree. -/
theorem tShift_zero_reachable_iff (m l : ℤ) :
    (∃ k : ℤ, l = 0 + k * m) ↔ m ∣ l := by
  simp only [zero_add, mul_comm, dvd_def]

end VOA.Huang.NgSchauenburg
