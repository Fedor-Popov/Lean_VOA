import VOA.Huang.GenusOneIntCoordProjectedWard

/-!
# Keeping square degree as an independent parameter

`squareDilation (W := W) t` multiplies the square component of degree `n` by `t^n`.
It is a finite algebraic sum for each state. Its one-point minus-two relation
has kernels `t^(2m+4) G_(2m+4)`, rather than the original kernels. No uniform
analytic estimate in the state degree or in `t` is asserted here.
-/

noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open VOA
open scoped BigOperators DirectSum
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Square-weight dilation, as a linear map defined by the internal grading. -/
def squareDilation (t : ℂ) : V →ₗ[ℂ] V := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition _ (sqWeightSpaceNat_isInternal W)
  exact (DFinsupp.lsum ℂ (fun n : ℕ =>
    t ^ n • (sqWeightSpace W (n : ℂ)).subtype)).comp
      (DirectSum.decomposeLinearEquiv (fun n : ℕ => sqWeightSpace W (n : ℂ))).toLinearMap

theorem squareDilation_of_mem_nat (t : ℂ) {n : ℕ} {v : V}
    (hv : v ∈ sqWeightSpace W (n : ℂ)) : squareDilation (W := W) t v = t ^ n • v := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition _ (sqWeightSpaceNat_isInternal W)
  change (DFinsupp.lsum ℂ (fun n : ℕ => t ^ n • (sqWeightSpace W (n : ℂ)).subtype))
    (DirectSum.decompose (fun n : ℕ => sqWeightSpace W (n : ℂ)) v) = _
  rw [DirectSum.decompose_of_mem (fun n : ℕ => sqWeightSpace W (n : ℂ)) hv]
  exact DFinsupp.lsum_single ℂ (fun n : ℕ =>
    t ^ n • (sqWeightSpace W (n : ℂ)).subtype) n ⟨v, hv⟩

theorem squareDilation_of_mem (t : ℂ) {n : ℤ} {v : V}
    (hv : v ∈ sqWeightSpace W (n : ℂ)) : squareDilation (W := W) t v = t ^ n • v := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simpa only [zpow_natCast] using squareDilation_of_mem_nat t hv
  · have hv0 : v = 0 := by
      rw [sqWeightSpace_eq_bot_of_neg W (by omega), Submodule.mem_bot] at hv
      exact hv
    simp [hv0]

theorem squareDilation_eq_sum (t : ℂ) (v : V) :
    squareDilation (W := W) t v =
      ∑ n ∈ squareSupport (W := W) v, t ^ n • squarePart (W := W) v n := by
  conv_lhs => rw [← sum_squarePart (W := W) v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ => squareDilation_of_mem_nat t (squarePart_mem v n)

/-- Homogeneous maps conjugate by the corresponding scalar power. -/
theorem squareDilation_comp_of_degree (T : V →ₗ[ℂ] V) (d : ℤ)
    (hT : ∀ (m : ℤ) (v : V), v ∈ sqWeightSpace W (m : ℂ) →
      T v ∈ sqWeightSpace W ((m + d : ℤ) : ℂ)) {t : ℂ} (ht : t ≠ 0) (v : V) :
    squareDilation (W := W) t (T v) = t ^ d • T (squareDilation (W := W) t v) := by
  refine sqWeightNat_induction W (P := fun v =>
    squareDilation (W := W) t (T v) = t ^ d • T (squareDilation (W := W) t v)) ?_ ?_ ?_ v
  · intro m v hv
    rw [squareDilation_of_mem t (hT m v hv), squareDilation_of_mem_nat t hv,
      map_smul, smul_smul, zpow_add₀ ht, zpow_natCast, mul_comm]
  · simp
  · intro v w hv hw
    simp only [map_add, smul_add, hv, hw]

theorem squareDilation_sqMode {K : ℤ} {a : V}
    (ha : a ∈ sqWeightSpace W (K : ℂ)) (j : ℤ) {t : ℂ} (ht : t ≠ 0) (v : V) :
    squareDilation (W := W) t (sqMode W j a v) =
      t ^ (K - j - 1) • sqMode W j a (squareDilation (W := W) t v) :=
  squareDilation_comp_of_degree (sqMode W j a) (K - j - 1)
    (fun m v hv => by
      simpa only [show K + m - j - 1 = m + (K - j - 1) by ring] using
        sqMode_mem_sqWeightSpace W ha hv j) ht v

theorem squareDilation_Lsq (j : ℤ) {t : ℂ} (ht : t ≠ 0) (v : V) :
    squareDilation (W := W) t (Lsq W j v) = t ^ (-j) • Lsq W j (squareDilation (W := W) t v) :=
  squareDilation_comp_of_degree (Lsq W j) (-j)
    (fun m v hv => by
      simpa only [Int.cast_add, Int.cast_neg, sub_eq_add_neg] using
        Lsq_mem_sqWeightSpace W hv j) ht v

/-- The correct parameter-dependent kernels after keeping square weight.
This is a proved one-point identity, not a `WardBilinear` hypothesis. -/
theorem squareDilation_block_negTwo {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    {K : ℤ} {a : V} (ha : a ∈ sqWeightSpace W (K : ℂ))
    {t : ℂ} (ht : t ≠ 0) (v : V) {z : ℂ} (hz : z ∈ imGT 0) :
    F (squareDilation (W := W) t (sqMode W (-2) a v)) z +
      ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ) *
        (t ^ (2 * (m + 2)) * zhuGC (m + 2) z *
          F (squareDilation (W := W) t (sqMode W (2 * (m + 2) - 2 : ℤ) a v)) z) = 0 := by
  have hterm : ∀ m : ℕ,
      ((2 * (m + 2) - 1 : ℕ) : ℂ) *
        (t ^ (2 * (m + 2)) * zhuGC (m + 2) z *
          F (squareDilation (W := W) t (sqMode W (2 * (m + 2) - 2 : ℤ) a v)) z) =
      t ^ (K + 1) * sqNegTwoTerm W F a (squareDilation (W := W) t v) z m := by
    intro m
    rw [squareDilation_sqMode ha _ ht, hF.smulv]
    have hp : t ^ (2 * (m + 2)) * t ^ (K - (2 * (m + 2) - 2) - 1) = t ^ (K + 1) := by
      rw [← zpow_natCast, ← zpow_add₀ ht]
      congr 1
      push_cast
      ring
    dsimp only [sqNegTwoTerm]
    calc _ = (t ^ (2 * (m + 2)) * t ^ (K - (2 * (m + 2) - 2) - 1)) *
          (((2 * (m + 2) - 1 : ℕ) : ℂ) * (zhuGC (m + 2) z *
            F (sqMode W (2 * (m + 2) - 2 : ℤ) a (squareDilation (W := W) t v)) z)) := by ring
      _ = _ := by rw [hp]
  rw [finsum_congr hterm, ← mul_finsum, squareDilation_sqMode ha _ ht, hF.smulv,
    show K - (-2) - 1 = K + 1 by ring, ← mul_add, hF.negTwo _ _ z hz, mul_zero]

/-- The one-point Euler identity with square degree retained. Both the
derivative and the Eisenstein kernels acquire their prescribed powers of `t`. -/
theorem squareDilation_block_omega {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    {t : ℂ} (ht : t ≠ 0) (v : V) {z : ℂ} (hz : z ∈ imGT 0) :
    F (squareDilation (W := W) t (Lsq W (-2) v)) z =
      t ^ 2 * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        _root_.deriv (F (squareDilation (W := W) t v)) z) +
      ∑ᶠ m : ℕ, t ^ (2 * (m + 1)) * zhuGC (m + 1) z *
        F (squareDilation (W := W) t (Lsq W (2 * (m + 1) - 2 : ℤ) v)) z := by
  have hterm : ∀ m : ℕ,
      t ^ (2 * (m + 1)) * zhuGC (m + 1) z *
        F (squareDilation (W := W) t (Lsq W (2 * (m + 1) - 2 : ℤ) v)) z =
      t ^ 2 * (zhuGC (m + 1) z *
        F (Lsq W (2 * (m + 1) - 2 : ℤ) (squareDilation (W := W) t v)) z) := by
    intro m
    rw [squareDilation_Lsq _ ht, hF.smulv]
    have hp : t ^ (2 * (m + 1)) * t ^ (-(2 * (m + 1) - 2 : ℤ)) = t ^ 2 := by
      rw [← zpow_natCast, ← zpow_add₀ ht]
      convert (zpow_natCast t 2) using 1
      push_cast
      congr 1
      ring
    calc _ = (t ^ (2 * (m + 1)) * t ^ (-(2 * (m + 1) - 2 : ℤ))) *
          (zhuGC (m + 1) z *
            F (Lsq W (2 * (m + 1) - 2 : ℤ) (squareDilation (W := W) t v)) z) := by ring
      _ = _ := by rw [hp]
  rw [finsum_congr hterm, ← mul_finsum, ← mul_add,
    squareDilation_Lsq _ ht, hF.smulv]
  norm_num only [neg_neg, zpow_ofNat]
  rw [hF.toAnalyticBlock.omega _ z hz]

universe w
variable {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)

/-- Evaluation of the square-degree generating polynomial is an actual trace
of a finite algebraic state. No infinite-sum interchange is used. -/
theorem traceFun_squareDilation (hC2 : C2Cofinite W) (t : ℂ) (x : ι)
    (τ : UpperHalfPlane) (v : V) :
    traceFun D.Mfam D.h x (squareDilation (W := W) t v) τ =
      ∑ n ∈ squareSupport (W := W) v,
        t ^ n * traceFun D.Mfam D.h x (squarePart (W := W) v n) τ := by
  change traceFunStateLinear D hC2 x τ (squareDilation (W := W) t v) = _
  rw [squareDilation_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul, traceFunStateLinear, LinearMap.coe_mk,
    AddHom.coe_mk]

end VOA.Huang.GenusOne.IntCoord
