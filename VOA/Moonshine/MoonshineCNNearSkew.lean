import VOA.Moonshine.MoonshineCNNearBorcherds
import VOA.Modules.ZhuVermaAnArchSkewModOnm
import VOA.Modules.ZhuRingResidue

/-! Skew symmetry for every near-VOA, obtained from Jacobi on the vacuum. -/

namespace VOA
open Module (End)
open scoped BigOperators
universe u
namespace NearVOA
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

theorem smul_eq_skew (V : NearVOA 𝒱) (a b : 𝒱) (t : ℤ) :
    V.smul b t a
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) •
          (sgn (-t - 1 - (j : ℤ))) •
            ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b)) := by
  have hJ := V.jacobi a b V.vacuum t (-1) 0
  have hleft :
      (∑ᶠ i : ℤ, (negOnePow i * cbz t i) •
          (V.smul a (t - 1 - i) (V.smul b i V.vacuum)
            - ((1 : ℂ) * negOnePow t) •
                V.smul b (t - i) (V.smul a (-1 + i) V.vacuum)))
        = -((1 : ℂ) * negOnePow t) • V.smul b t a := by
    rw [finsum_eq_single _ 0]
    · simp only [negOnePow, cbz_zero, one_mul, one_smul, if_pos (by norm_num : Even (0 : ℤ))]
      rw [V.smul_vacuum_eq_zero b (by norm_num : (0 : ℤ) ≤ 0),
        smul_zero_right,
        show (-1 : ℤ) + 0 = -1 from by norm_num, V.smul_neg_one_vacuum]
      simp
    · intro i hi
      rcases lt_or_gt_of_ne hi with hi | hi
      · rw [cbz_apply_neg t hi, mul_zero, zero_smul]
      · have hbi : V.smul b i V.vacuum = 0 := V.smul_vacuum_eq_zero b (by omega)
        have hai : V.smul a (-1 + i) V.vacuum = 0 := V.smul_vacuum_eq_zero a (by omega)
        rw [hbi, hai, smul_zero_right, smul_zero_right,
          smul_zero, sub_zero, smul_zero]
  have hright :
      (∑ᶠ i : ℤ, cbz (-1) i • V.smul (V.smul a (t + i) b) (-1 - i) V.vacuum)
        = ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j) •
            (((j.factorial : ℂ)⁻¹) • ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b))) := by
    symm
    apply VertexOperatorAlgebra.finsum_nat_to_int
    · intro i hi
      rw [cbz_apply_neg (-1) hi, zero_smul]
    · intro j
      rw [ZhuRes.cbz_neg_one j,
        show (-1 : ℤ) - (j : ℤ) = -(j : ℤ) - 1 from by ring,
        V.creation_pow, smul_smul]
  simp only [add_zero, zero_add, sub_eq_add_neg] at hJ hleft hright
  rw [hleft, hright] at hJ
  have hsolve : V.smul b t a
      = -((1 : ℂ) * negOnePow t) •
          ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j) •
            (((j.factorial : ℂ)⁻¹) • ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b))) := by
    have hs : -((1 : ℂ) * negOnePow t) * -((1 : ℂ) * negOnePow t) = 1 := by
      simpa only [one_mul, neg_mul_neg] using negOnePow_mul_self t
    rw [← hJ, smul_smul, hs, one_smul]
  rw [hsolve]
  have hfin : (Function.support fun j : ℕ =>
      ((-1 : ℂ) ^ j) • (((j.factorial : ℂ)⁻¹) •
        ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b)))).Finite := by
    obtain ⟨N, hN⟩ := V.regularity a b
    refine Set.Finite.subset (Set.finite_Iio (N - t).toNat) ?_
    intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc
    rw [not_lt] at hc
    exact hj (by
      have hz := hN (t + (j : ℤ)) (by omega)
      change V.smul a (t + (j : ℤ)) b = 0 at hz
      rw [hz, map_zero, smul_zero, smul_zero])
  have hfin' : (Function.support fun j : ℕ =>
      ((j.factorial : ℂ)⁻¹) • (sgn (-t - 1 - (j : ℤ))) •
        ((V.L (-1) ^ j) (V.smul a (t + (j : ℤ)) b))).Finite := by
    obtain ⟨N, hN⟩ := V.regularity a b
    refine Set.Finite.subset (Set.finite_Iio (N - t).toNat) ?_
    intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc
    rw [not_lt] at hc
    exact hj (by
      have hz := hN (t + (j : ℤ)) (by omega)
      change V.smul a (t + (j : ℤ)) b = 0 at hz
      rw [hz, map_zero, smul_zero, smul_zero])
  rw [smul_finsum' _ hfin]
  refine finsum_congr fun j => ?_
  simp only [smul_smul]
  congr 1
  rw [show -t - 1 - (j : ℤ) = -(t + (j : ℤ) + 1) from by ring,
    sgn_neg', show t + (j : ℤ) + 1 = (t + 1) + (j : ℤ) from by ring,
    sgn_add_natCast, sgn_succ]
  have hsgn : sgn t = negOnePow t := rfl
  rw [hsgn]
  ring


end NearVOA
end VOA
