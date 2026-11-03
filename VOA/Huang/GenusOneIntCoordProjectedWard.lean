import VOA.Huang.GenusOneIntCoordSquareBound

/-!
# Square projections and the shifted one-point Ward identities

A mode of square degree `d` intertwines projection at `n` with projection at
`n-d`. Fixed square projections are therefore not mode-module endomorphisms.
The integer-indexed extension below makes the shifts, including negative
weights, explicit. This file does not assert an exponential trace-mass bound.
-/

noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open VOA
open scoped BigOperators DirectSum
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

def squarePartLinear (n : ℕ) : V →ₗ[ℂ] V where
  toFun v := squarePart (W := W) v n
  map_add' v w := squarePart_add v w n
  map_smul' c v := by
    classical
    letI := DirectSum.IsInternal.chooseDecomposition _ (sqWeightSpaceNat_isInternal W)
    simp [squarePart, squareParts]
    rfl

theorem squarePart_of_mem_sqWeightSpace {v : V} {n : ℕ}
    (hv : v ∈ sqWeightSpace W (n : ℂ)) : squarePart (W := W) v n = v := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition _ (sqWeightSpaceNat_isInternal W)
  exact DirectSum.decompose_of_mem_same (fun i : ℕ => sqWeightSpace W (i : ℂ)) hv

/-- The canonical square projection, extended by zero at negative indices. -/
def squareProj (n : ℤ) : V →ₗ[ℂ] V :=
  if 0 ≤ n then squarePartLinear (W := W) n.toNat else 0

@[simp] theorem squareProj_nat (n : ℕ) (v : V) :
    squareProj (W := W) (n : ℤ) v = squarePart (W := W) v n := by
  simp [squareProj, squarePartLinear]

theorem squareProj_mem (n : ℤ) (v : V) :
    squareProj (W := W) n v ∈ sqWeightSpace W (n : ℂ) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simpa only [squareProj_nat, Int.cast_natCast] using squarePart_mem (W := W) v k
  · simp [squareProj, hn]

theorem squareProj_of_mem {m : ℤ} {v : V}
    (hv : v ∈ sqWeightSpace W (m : ℂ)) (n : ℤ) :
    squareProj (W := W) n v = if m = n then v else 0 := by
  classical
  by_cases hm : 0 ≤ m
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    by_cases hn : 0 ≤ n
    · obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [squareProj_nat]
      by_cases hkl : k = l
      · subst l
        simpa using squarePart_of_mem_sqWeightSpace hv
      · rw [if_neg (by exact_mod_cast hkl)]
        exact squarePart_eq_zero_of_mem_sqWeightSpace hv hkl
    · simp [squareProj, hn, show (k : ℤ) ≠ n by omega]
  · have hv0 : v = 0 := by
      rw [sqWeightSpace_eq_bot_of_neg W (by omega), Submodule.mem_bot] at hv
      exact hv
    simp [hv0]

/-- Graded covariance, with the necessary shift of projection index. -/
theorem squareProj_comp_of_degree (T : V →ₗ[ℂ] V) (d : ℤ)
    (hT : ∀ (m : ℤ) (v : V), v ∈ sqWeightSpace W (m : ℂ) →
      T v ∈ sqWeightSpace W ((m + d : ℤ) : ℂ)) (n : ℤ) (v : V) :
    squareProj (W := W) n (T v) = T (squareProj (W := W) (n - d) v) := by
  refine sqWeightNat_induction W (P := fun v =>
    squareProj (W := W) n (T v) = T (squareProj (W := W) (n - d) v)) ?_ ?_ ?_ v
  · intro m v hv
    rw [squareProj_of_mem (hT m v hv), squareProj_of_mem hv]
    by_cases he : (m : ℤ) + d = n
    · rw [if_pos he, if_pos (by omega)]
    · rw [if_neg he, if_neg (by omega), map_zero]
  · simp
  · intro v w hv hw
    simp only [map_add, hv, hw]

/-- A square-homogeneous bracket mode shifts the square-component index. -/
theorem squareProj_sqMode {K : ℤ} {a : V}
    (ha : a ∈ sqWeightSpace W (K : ℂ)) (j n : ℤ) (v : V) :
    squareProj (W := W) n (sqMode W j a v) =
      sqMode W j a (squareProj (W := W) (n - K + j + 1) v) := by
  have h := squareProj_comp_of_degree (sqMode W j a) (K - j - 1)
    (fun m v hv => by
      simpa only [show K + m - j - 1 = m + (K - j - 1) by ring] using
        sqMode_mem_sqWeightSpace W ha hv j) n v
  simpa only [show n - (K - j - 1) = n - K + j + 1 by ring] using h

/-- The Virasoro version: `L[j]` shifts the component index by `j`. -/
theorem squareProj_Lsq (j n : ℤ) (v : V) :
    squareProj (W := W) n (Lsq W j v) =
      Lsq W j (squareProj (W := W) (n + j) v) := by
  have h := squareProj_comp_of_degree (Lsq W j) (-j)
    (fun m v hv => by
      simpa only [Int.cast_add, Int.cast_neg, sub_eq_add_neg] using
        Lsq_mem_sqWeightSpace W hv j) n v
  simpa only [sub_neg_eq_add] using h

/-- The fixed-index commutation shortcut already fails on the vacuum at
nonzero central charge. This uses only the square Virasoro relation. -/
theorem squareProj_zero_not_commute_Lsq_negTwo
    (hc : W.centralCharge ≠ 0) (hvac : W.vacuum ≠ 0) :
    squareProj (W := W) 0 (Lsq W (-2) W.vacuum) ≠
      Lsq W (-2) (squareProj (W := W) 0 W.vacuum) := by
  have hv : W.vacuum ∈ sqWeightSpace W ((0 : ℤ) : ℂ) := by
    rw [mem_sqWeightSpace_iff, Lsq_vacuum_eq_zero W (by norm_num)]
    simp
  have hneg : squareProj (W := W) (-2) W.vacuum = 0 := by
    rw [squareProj_of_mem hv]
    norm_num
  rw [squareProj_Lsq, zero_add, hneg, map_zero, squareProj_of_mem hv, if_pos rfl]
  intro he
  have hvir := Lsq_virasoro_apply' W 2 (-2) W.vacuum
  rw [← he, map_zero, Lsq_vacuum_eq_zero W (by norm_num : (-1 : ℤ) ≤ 2),
    map_zero] at hvir
  norm_num [Lsq_vacuum_eq_zero W (by norm_num : (-1 : ℤ) ≤ 0)] at hvir
  exact (smul_ne_zero (mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) hc) hvac)
    hvir.symm

/-- Zhu's vanishing relation survives projection, with its degree shift. -/
theorem squareProj_block_vanish {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    {K : ℤ} {a : V} (ha : a ∈ sqWeightSpace W (K : ℂ)) (n : ℤ) (v : V) :
    F (squareProj (W := W) n (sqMode W 0 a v)) = 0 := by
  rw [squareProj_sqMode ha]
  exact hF.vanish _ _

/-- The projected minus-two relation couples distinct output square weights.
The Eisenstein weight is exactly the difference of these indices. -/
theorem squareProj_block_negTwo {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    {K : ℤ} {a : V} (ha : a ∈ sqWeightSpace W (K : ℂ)) (n : ℤ) (v : V)
    {z : ℂ} (hz : z ∈ imGT 0) :
    F (squareProj (W := W) (K + n + 1) (sqMode W (-2) a v)) z +
      ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ) *
        (zhuGC (m + 2) z * F (squareProj (W := W)
          (K + n - 2 * (m + 2) + 1) (sqMode W (2 * (m + 2) - 2 : ℤ) a v)) z) = 0 := by
  have he : ∀ j : ℤ, squareProj (W := W) (K + n - j - 1) (sqMode W j a v) =
      sqMode W j a (squareProj (W := W) n v) := by
    intro j
    rw [squareProj_sqMode ha, show K + n - j - 1 - K + j + 1 = n by ring]
  have h := hF.negTwo a (squareProj (W := W) n v) z hz
  rw [show K + n + 1 = K + n - (-2) - 1 by ring, he]
  convert h using 2
  apply finsum_congr
  intro m
  unfold sqNegTwoTerm
  rw [show K + n - 2 * (m + 2) + 1 = K + n - (2 * (m + 2) - 2) - 1 by ring, he]

/-- The projected Virasoro recursion. The derivative at index `n` is paired
with the leading output at `n+2`, not at `n`. -/
theorem squareProj_block_omega {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    (n : ℤ) (v : V) {z : ℂ} (hz : z ∈ imGT 0) :
    F (squareProj (W := W) (n + 2) (Lsq W (-2) v)) z =
      serreDerivC n (F (squareProj (W := W) n v)) z +
        ∑ᶠ m : ℕ, zhuGC (m + 2) z * F (squareProj (W := W)
          (n - (2 * (m + 2) - 2)) (Lsq W (2 * (m + 2) - 2 : ℤ) v)) z := by
  simp_rw [squareProj_Lsq, show n + 2 + (-2) = n by ring, sub_add_cancel]
  exact hF.omega n _ (squareProj_mem n v) z hz

universe w
variable {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)

/-- The genuine Zhu traces satisfy the shifted square-component recursion. -/
theorem squareProj_traceBlock_omega (hC2 : C2Cofinite W) (x : ι)
    (n : ℤ) (v : V) {z : ℂ} (hz : z ∈ imGT 0) :
    traceBlock D.Mfam D.h x (squareProj (W := W) (n + 2) (Lsq W (-2) v)) z =
      serreDerivC n (traceBlock D.Mfam D.h x (squareProj (W := W) n v)) z +
        ∑ᶠ m : ℕ, zhuGC (m + 2) z * traceBlock D.Mfam D.h x (squareProj (W := W)
          (n - (2 * (m + 2) - 2)) (Lsq W (2 * (m + 2) - 2 : ℤ) v)) z :=
  squareProj_block_omega
    ((traceBlock_isAnalyticBlock D.Mfam D.h D.hasWeight
      (fun y => onePointSubexp_of_c2 W (D.Mfam y).isMod (D.hasWeight y)
        (vacuumGradeZero_holds W) hC2) x).toSqGradedBlock) n v hz

end VOA.Huang.GenusOne.IntCoord
