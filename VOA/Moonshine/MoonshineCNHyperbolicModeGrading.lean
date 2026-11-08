import VOA.Moonshine.MoonshineCNHyperbolicVirasoro
import VOA.Core.DeformationLiftedModes

/-! # Exact degree of all concrete hyperbolic modes -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

theorem hypLevel_eq_sugawara_eigenspace (κ ell : ℂ) (N : ℤ) :
    hypLevel N = Module.End.eigenspace (hypSugawara κ ell 0) (κ * ell + (N : ℂ)) := by
  have h := VOA.Deform.iSup_inf_eq_of_le_independent (p := hypLevel)
    (q := fun Q : ℤ => Module.End.eigenspace (hypSugawara κ ell 0) (κ * ell + (Q : ℂ)))
    (fun Q p hp => Module.End.mem_eigenspace_iff.mpr (hypSugawara_zero_level κ ell Q p hp))
    ((Module.End.eigenspaces_iSupIndep (hypSugawara κ ell 0)).comp
      (fun _ _ h => Int.cast_injective (add_left_cancel h))) N
  simpa only [hypLevel_isInternal.submodule_iSup_eq_top, top_inf_eq] using h.symm

/-- Every signed mode has level degree exactly minus its index. -/
theorem hypSugawara_mem_level (κ ell : ℂ) (n N : ℤ) (p : hypFock)
    (hp : p ∈ hypLevel N) : hypSugawara κ ell n p ∈ hypLevel (N - n) := by
  rw [hypLevel_eq_sugawara_eigenspace κ ell, Module.End.mem_eigenspace_iff]
  have h := LinearMap.congr_fun (hypSugawara_virasoro κ ell 0 n) p
  simp only [Int.cast_zero, zero_pow (by decide : (3 : ℕ) ≠ 0), sub_self, zero_div,
    zero_mul, zero_smul, ite_self, zero_sub, zero_add, add_zero,
    LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [hypSugawara_zero_level κ ell N p hp, map_smul] at h
  calc
    hypSugawara κ ell 0 (hypSugawara κ ell n p) =
        -(n : ℂ) • hypSugawara κ ell n p +
          (κ * ell + (N : ℂ)) • hypSugawara κ ell n p := sub_eq_iff_eq_add.mp h
    _ = (κ * ell + ((N - n : ℤ) : ℂ)) • hypSugawara κ ell n p := by
      rw [← add_smul]
      congr 1
      push_cast
      ring

end VOA.Moonshine.ConwayNorton
