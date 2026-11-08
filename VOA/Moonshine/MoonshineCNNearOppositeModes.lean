import VOA.Moonshine.MoonshineCNNearNilpotence
import Mathlib.Algebra.DirectSum.Decomposition

/-! Opposite modes for a NearVOA with locally nilpotent `L₁`.
The sums are finite by nilpotence, independently of the sign of the weight.
This file does not assert the opposite Jacobi identity. -/

noncomputable section
namespace VOA.NearVOA

open Module (End)
open scoped BigOperators

variable {H : Type*} [AddCommGroup H] [Module ℂ H] (V : NearVOA H)

def oppositeModeTerm (N n : ℤ) (j : ℕ) : H →ₗ[ℂ] End ℂ H where
  toFun u := ((j.factorial : ℂ)⁻¹) • mode (V.Y ((V.L 1 ^ j) u))
    (2 * N - n - 2 - (j : ℤ))
  map_add' u v := by simp only [map_add, mode_add, smul_add]
  map_smul' c u := by simp only [map_smul, mode_smul, smul_comm _ c, RingHom.id_apply]

theorem oppositeModeTerm_finiteSupport (N n : ℤ) {u : H}
    (hu : ∃ k : ℕ, (V.L 1 ^ k) u = 0) :
    (Function.support fun j => V.oppositeModeTerm N n j u).Finite := by
  classical
  obtain ⟨k, hk⟩ := hu
  apply (Finset.range k).finite_toSet.subset
  intro j hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  apply hj
  simp only [oppositeModeTerm, LinearMap.coe_mk, AddHom.coe_mk,
    Module.End.pow_map_zero_of_le (Nat.le_of_not_gt h) hk, map_zero, mode_zero, smul_zero]

/-- The FHL opposite mode at a specified homogeneous weight. -/
def oppositeModeAtWeight (N n : ℤ) (u : H) : End ℂ H :=
  (-1 : ℂ) ^ N • ∑ᶠ j : ℕ, V.oppositeModeTerm N n j u

/-- Any nilpotence cutoff computes the same opposite mode. -/
theorem oppositeModeAtWeight_eq_sum (N n : ℤ) {u : H} (k : ℕ)
    (hk : (V.L 1 ^ k) u = 0) :
    V.oppositeModeAtWeight N n u = (-1 : ℂ) ^ N •
      ∑ j ∈ Finset.range k, ((j.factorial : ℂ)⁻¹) •
        mode (V.Y ((V.L 1 ^ j) u)) (2 * N - n - 2 - (j : ℤ)) := by
  classical
  unfold oppositeModeAtWeight
  rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range k) (by
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hj
    simp only [oppositeModeTerm, LinearMap.coe_mk, AddHom.coe_mk,
      Module.End.pow_map_zero_of_le (Nat.le_of_not_gt h) hk, map_zero, mode_zero, smul_zero])]
  rfl

theorem oppositeModeAtWeight_zero (N n : ℤ) : V.oppositeModeAtWeight N n 0 = 0 := by
  simp [oppositeModeAtWeight]

theorem oppositeModeAtWeight_add (N n : ℤ) {u v : H}
    (hu : ∃ k : ℕ, (V.L 1 ^ k) u = 0) (hv : ∃ k : ℕ, (V.L 1 ^ k) v = 0) :
    V.oppositeModeAtWeight N n (u + v) =
      V.oppositeModeAtWeight N n u + V.oppositeModeAtWeight N n v := by
  simp only [oppositeModeAtWeight, map_add]
  rw [finsum_add_distrib (V.oppositeModeTerm_finiteSupport N n hu)
    (V.oppositeModeTerm_finiteSupport N n hv), smul_add]

theorem oppositeModeAtWeight_smul (N n : ℤ) (c : ℂ) (u : H) :
    V.oppositeModeAtWeight N n (c • u) = c • V.oppositeModeAtWeight N n u := by
  simp only [oppositeModeAtWeight, map_smul]
  rw [← smul_finsum, smul_comm]

def oppositeModeAtWeightLinear (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    (N n : ℤ) : H →ₗ[ℂ] End ℂ H where
  toFun := V.oppositeModeAtWeight N n
  map_add' u v := V.oppositeModeAtWeight_add N n (hNil u) (hNil v)
  map_smul' c u := V.oppositeModeAtWeight_smul N n c u

/-- Assemble homogeneous opposite modes using the given internal weight decomposition. -/
def oppositeModes (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    (n : ℤ) : H →ₗ[ℂ] End ℂ H :=
  letI := V.isInternal.chooseDecomposition
  (DirectSum.toModule ℂ ℤ (End ℂ H) (fun N =>
    (V.oppositeModeAtWeightLinear hNil N n).comp (V.grading N).subtype)).comp
      (DirectSum.decomposeLinearEquiv V.grading).toLinearMap

theorem oppositeModes_homogeneous (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    {N : ℤ} {u : H} (hu : u ∈ V.grading N) (n : ℤ) :
    V.oppositeModes hNil n u = V.oppositeModeAtWeight N n u := by
  letI := V.isInternal.chooseDecomposition
  change (DirectSum.toModule ℂ ℤ (End ℂ H) (fun N =>
    (V.oppositeModeAtWeightLinear hNil N n).comp (V.grading N).subtype))
      (DirectSum.decompose V.grading u) = _
  rw [DirectSum.decompose_of_mem V.grading hu, ← DirectSum.lof_eq_of ℂ,
    DirectSum.toModule_lof]
  rfl

theorem oppositeModeAtWeight_primary (N n : ℤ) {u : H} (hu : V.L 1 u = 0) :
    V.oppositeModeAtWeight N n u = (-1 : ℂ) ^ N • mode (V.Y u) (2 * N - n - 2) := by
  rw [V.oppositeModeAtWeight_eq_sum N n 1 (by simpa using hu)]
  simp

/-- The opposite zero mode of a weight-one primary is minus its ordinary zero mode. -/
theorem oppositeModes_primary (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    {u : H} (hu : u ∈ V.grading 1) (hL : V.L 1 u = 0) :
    V.oppositeModes hNil 0 u = -mode (V.Y u) 0 := by
  rw [V.oppositeModes_homogeneous hNil hu, V.oppositeModeAtWeight_primary 1 0 hL]
  norm_num

/-- Opposite modes truncate in the reverse direction on each vector. -/
theorem oppositeModeAtWeight_eventually_zero (N : ℤ) {u : H}
    (hu : ∃ k : ℕ, (V.L 1 ^ k) u = 0) (x : H) :
    ∃ B : ℤ, ∀ n : ℤ, n ≤ B → V.oppositeModeAtWeight N n u x = 0 := by
  classical
  obtain ⟨k, hk⟩ := hu
  choose K hK using fun j : ℕ => V.regularity ((V.L 1 ^ j) u) x
  obtain ⟨B, hB⟩ := ((Finset.range k).finite_toSet.image
    (fun j => K j + (j : ℤ))).bddAbove
  refine ⟨2 * N - 2 - B, fun n hn => ?_⟩
  rw [V.oppositeModeAtWeight_eq_sum N n k hk, LinearMap.smul_apply,
    LinearMap.sum_apply]
  have hz : ∀ j ∈ Finset.range k,
      (((j.factorial : ℂ)⁻¹) • mode (V.Y ((V.L 1 ^ j) u))
        (2 * N - n - 2 - (j : ℤ))) x = 0 := by
    intro j hj
    have hb : K j + (j : ℤ) ≤ B := hB ⟨j, hj, rfl⟩
    rw [LinearMap.smul_apply, hK j _ (by omega), smul_zero]
  rw [Finset.sum_eq_zero hz, smul_zero]

theorem oppositeModes_eventually_zero (hNil : ∀ u : H, ∃ k : ℕ, (V.L 1 ^ k) u = 0)
    (u x : H) : ∃ B : ℤ, ∀ n : ℤ, n ≤ B → V.oppositeModes hNil n u x = 0 := by
  classical
  letI := V.isInternal.chooseDecomposition
  induction u using DirectSum.Decomposition.inductionOn V.grading with
  | zero => exact ⟨0, fun n _ => by rw [map_zero, LinearMap.zero_apply]⟩
  | homogeneous u =>
      rename_i N
      obtain ⟨B, hB⟩ := V.oppositeModeAtWeight_eventually_zero N (hNil u) x
      exact ⟨B, fun n hn => by rw [V.oppositeModes_homogeneous hNil u.property]; exact hB n hn⟩
  | add u v hu hv =>
      obtain ⟨B, hB⟩ := hu
      obtain ⟨C, hC⟩ := hv
      exact ⟨min B C, fun n hn => by
        rw [map_add, LinearMap.add_apply, hB n (hn.trans (min_le_left _ _)),
          hC n (hn.trans (min_le_right _ _)), add_zero]⟩

end VOA.NearVOA
