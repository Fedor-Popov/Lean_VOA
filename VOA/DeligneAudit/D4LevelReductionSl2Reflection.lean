import VOA.DeligneAudit.D4LevelReductionNilpotentExponential
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! A nilpotent sl2 triple gives symmetry of opposite Cartan eigenspaces. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable local instance rationalModuleForReflection
    (X : Type*) [AddCommGroup X] [Module ℂ X] :
    Module ℚ X := Module.restrictScalars ℚ ℂ X

local instance rationalTowerForReflection (X : Type*) [AddCommGroup X] [Module ℂ X] :
    IsScalarTower ℚ ℂ X := IsScalarTower.restrictScalars ℚ ℂ X

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- An adjoint exponential identity is an intertwining identity for actual multiplication. -/
theorem nilpotent_exp_intertwining (x y z : A) (hx : IsNilpotent x)
    (h : IsNilpotent.exp (LieAlgebra.ad ℂ A x) y = z) :
    IsNilpotent.exp x * y = z * IsNilpotent.exp x := by
  rw [nilpotent_exp_ad_apply x y hx] at h
  have he := congrArg (fun a => a * IsNilpotent.exp x) h
  simpa only [mul_assoc, IsNilpotent.exp_neg_mul_exp_self hx, mul_one] using he

/-- The three root exponentials give a unit reversing the Cartan element. -/
theorem sl2_nilpotent_reflection_unit (H E F : A)
    (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = -(2 : ℂ) • F)
    (hE : IsNilpotent E) (hF : IsNilpotent F) :
    ∃ R : A, IsUnit R ∧ R * H = -H * R := by
  have hFH : ⁅F, H⁆ = (2 : ℂ) • F := by rw [← lie_skew F H, hHF]; module
  have hEH : ⁅-E, H⁆ = (2 : ℂ) • E := by rw [neg_lie, lie_skew H E, hHE]
  have hEFneg : ⁅-E, F⁆ = -H := by rw [neg_lie, hEF]
  have hEHneg : ⁅-E, -H⁆ = -(2 : ℂ) • E := by rw [lie_neg, hEH]; module
  have hExpFH : IsNilpotent.exp (LieAlgebra.ad ℂ A F) H = H + (2 : ℂ) • F := by
    rw [nilpotent_exp_ad_apply_of_square_zero F H hF (by simp [hFH]), hFH]
  have hExpFF : IsNilpotent.exp (LieAlgebra.ad ℂ A F) F = F := by
    rw [nilpotent_exp_ad_apply_of_square_zero F F hF (by simp)]
    simp
  have hExpEH : IsNilpotent.exp (LieAlgebra.ad ℂ A (-E)) H = H + (2 : ℂ) • E := by
    rw [nilpotent_exp_ad_apply_of_square_zero (-E) H hE.neg (by simp [hEH]), hEH]
  have hExpEF : IsNilpotent.exp (LieAlgebra.ad ℂ A (-E)) F = F - H - E := by
    rw [nilpotent_exp_ad_apply_of_cube_zero (-E) F hE.neg (by
      rw [hEFneg, hEHneg]; simp), hEFneg, hEHneg]
    module
  have hfirst := nilpotent_exp_intertwining F H (H + (2 : ℂ) • F) hF hExpFH
  have hmiddle := nilpotent_exp_intertwining (-E) (H + (2 : ℂ) • F)
    ((2 : ℂ) • F - H) hE.neg (by
      rw [map_add, map_smul, hExpEH, hExpEF]
      module)
  have hlast := nilpotent_exp_intertwining F ((2 : ℂ) • F - H) (-H) hF (by
    rw [map_sub, map_smul, hExpFF, hExpFH]
    module)
  let R := IsNilpotent.exp F * IsNilpotent.exp (-E) * IsNilpotent.exp F
  refine ⟨R, ((IsNilpotent.isUnit_exp hF).mul (IsNilpotent.isUnit_exp hE.neg)).mul
    (IsNilpotent.isUnit_exp hF), ?_⟩
  calc
    R * H = IsNilpotent.exp F *
        (IsNilpotent.exp (-E) * (IsNilpotent.exp F * H)) := by simp [R, mul_assoc]
    _ = IsNilpotent.exp F *
        ((IsNilpotent.exp (-E) * (H + (2 : ℂ) • F)) * IsNilpotent.exp F) := by
          rw [hfirst, mul_assoc]
    _ = (IsNilpotent.exp F * ((2 : ℂ) • F - H)) *
        (IsNilpotent.exp (-E) * IsNilpotent.exp F) := by rw [hmiddle]; simp [mul_assoc]
    _ = -H * R := by rw [hlast]; simp [R, mul_assoc]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An invertible Cartan-reversing operator equates opposite eigenspace dimensions. -/
theorem eigenspace_finrank_eq_of_anticommuting_unit [FiniteDimensional ℂ V]
    (H R : Module.End ℂ V) (hR : IsUnit R) (hHR : R * H = -H * R) (μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace H μ) =
      Module.finrank ℂ (Module.End.eigenspace H (-μ)) := by
  have hle (c : ℂ) : Module.finrank ℂ (Module.End.eigenspace H c) ≤
      Module.finrank ℂ (Module.End.eigenspace H (-c)) := by
    have hmem (v : V) (hv : v ∈ Module.End.eigenspace H c) :
        R v ∈ Module.End.eigenspace H (-c) := by
      have he := LinearMap.congr_fun hHR v
      have hv' := Module.End.mem_eigenspace_iff.mp hv
      simp only [Module.End.mul_apply, LinearMap.neg_apply, hv', map_smul] at he
      apply Module.End.mem_eigenspace_iff.mpr
      have hn := congrArg Neg.neg he
      simpa only [neg_neg, neg_smul] using hn.symm
    let f : Module.End.eigenspace H c →ₗ[ℂ] Module.End.eigenspace H (-c) :=
      (R.comp (Module.End.eigenspace H c).subtype).codRestrict _
        (fun v => hmem v v.property)
    apply LinearMap.finrank_le_finrank_of_injective (f := f)
    intro v w hvw
    apply Subtype.ext
    exact (Module.End.isUnit_iff R).mp hR |>.injective (congrArg Subtype.val hvw)
  apply le_antisymm (hle μ)
  have hback := hle (-μ)
  rw [show - -μ = μ from neg_neg μ] at hback
  exact hback

/-- Nilpotent raising and lowering operators give Cartan weight symmetry. -/
theorem sl2_nilpotent_eigenspace_finrank_eq [FiniteDimensional ℂ V]
    (H E F : Module.End ℂ V)
    (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = -(2 : ℂ) • F)
    (hE : IsNilpotent E) (hF : IsNilpotent F) (μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace H μ) =
      Module.finrank ℂ (Module.End.eigenspace H (-μ)) := by
  obtain ⟨R, hR, hHR⟩ := sl2_nilpotent_reflection_unit H E F hEF hHE hHF hE hF
  exact eigenspace_finrank_eq_of_anticommuting_unit H R hR hHR μ

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.sl2_nilpotent_reflection_unit
#print axioms VOA.DeligneAudit.D4LevelReduction.eigenspace_finrank_eq_of_anticommuting_unit
#print axioms VOA.DeligneAudit.D4LevelReduction.sl2_nilpotent_eigenspace_finrank_eq
