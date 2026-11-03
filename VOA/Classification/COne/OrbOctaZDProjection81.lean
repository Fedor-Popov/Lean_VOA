import VOA.Classification.COne.OrbOctaZDGrade81

/-! The nonzero spin-nine channel gives the third Q24 seed identity. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbOcta OrbC2b
  VOA.LatGen VOA.LatGen.Triplet MvPolynomial OrbOctaZC

noncomputable local instance : Fintype octa :=
  @Fintype.ofFinite _ (Finite.of_equiv (Equiv.Perm (Fin 4)) octa_group.some.symm.toEquiv)

def c3 : ℂ := Complex.I * (-2 * eps1)

theorem c3_sq : c3 * c3 = -4 := by
  calc
    _ = Complex.I ^ 2 * 4 * (eps1 * eps1) := by unfold c3; ring
    _ = -4 := by rw [Complex.I_sq, eps1_sq]; ring

theorem c3_ne_zero : c3 ≠ 0 := by
  intro h
  have he := c3_sq
  rw [h, zero_mul] at he
  norm_num at he

theorem T2_I3I6 : T2 (I3 * I6) = c3 •
    ((2 : ℂ) • wv 9 1 + (-68 : ℂ) • wv 9 5 +
      (68 : ℂ) • wv 9 13 + (-2 : ℂ) • wv 9 17) := by
  have h : psi (I3 * I6) = MvPolynomial.C c3 *
      ((2 : ℂ) • (X 0 ^ 17 * X 1) + (-68 : ℂ) • (X 0 ^ 13 * X 1 ^ 5) +
        (68 : ℂ) • (X 0 ^ 5 * X 1 ^ 13) + (-2 : ℂ) • (X 0 * X 1 ^ 17)) := by
    rw [map_mul, psi_I3, psi_I6]
    simp only [c3, map_mul, smul_eq_C_mul, map_neg, map_ofNat]
    ring
  rw [T2_apply, h, ← smul_eq_C_mul, map_smul, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul]
  simpa only [pow_one] using congrArg (fun v => c3 • v)
    (show (2 : ℂ) • Tb (X 0 ^ 17 * X 1 ^ 1) + (-68 : ℂ) • Tb (X 0 ^ 13 * X 1 ^ 5) +
      (68 : ℂ) • Tb (X 0 ^ 5 * X 1 ^ 13) + (-2 : ℂ) • Tb (X 0 ^ 1 * X 1 ^ 17) = _ by
      rw [Tb_xy 17 1 9 rfl, Tb_xy 13 5 9 rfl, Tb_xy 5 13 9 rfl, Tb_xy 1 17 9 rfl])

set_option maxHeartbeats 1000000 in
-- Nine small first-channel projections, with complex scalars kept explicit.
theorem channel81_ambient :
    V2v.smul (T2 I4) (-30) (T2 (I3 * I3)) - (5304 * c3) • T2 (I3 * I6) ∈
      lowerDesc V2v 81 := by
  let Φ := fun i j : ℕ => V2v.smul (wv 4 i) (-30) (wv 6 j) -
    (lam9 * (8 * (j : ℂ) - 12 * i)) • wv 9 (i + j - 1)
  have hm (i j : ℕ) (h1 : 1 ≤ i + j) (h19 : i + j ≤ 19) (hi : i ≤ 8) (hj : j ≤ 12) :
      Φ i j ∈ lowerDesc V2v 81 := first46 (i + j) i j rfl h1 h19 hi hj
  have hc : (5304 * c3) * c3 = -21216 := by
    rw [mul_assoc, c3_sq]; norm_num
  have he : V2v.smul (T2 I4) (-30) (T2 (I3 * I3)) - (5304 * c3) • T2 (I3 * I6) =
      (-8 : ℂ) • Φ 0 2 + (16 : ℂ) • Φ 0 6 + (-8 : ℂ) • Φ 0 10 +
      (-112 : ℂ) • Φ 4 2 + (224 : ℂ) • Φ 4 6 + (-112 : ℂ) • Φ 4 10 +
      (-8 : ℂ) • Φ 8 2 + (16 : ℂ) • Φ 8 6 + (-8 : ℂ) • Φ 8 10 := by
    rw [T2_I4, T2_I3sq, T2_I3I6, smul_smul, hc]
    simp only [Φ, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
      PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, lam9]
    norm_num
    module
  rw [he]
  repeat' apply Submodule.add_mem
  all_goals exact Submodule.smul_mem _ _ (hm _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num))

theorem channel81 :
    OrbOctaR.W.smul OrbOctaR.X (-30) (octaSeeds 2) - (5304 * c3) • octaSeeds 3 ∈
      lowerDesc OrbOctaR.W 81 := by
  have h := average_lowerDesc octa channel81_ambient
  rw [map_sub, map_smul, average_smul_T2 inv_I4 inv_I3sq] at h
  exact h

/-- Q24 annihilates the weight-81 seed. -/
theorem q24_seed_three :
    Polynomial.aeval (OrbZhu.omegaL OrbOctaR.W) OrbOctaZ.positivePolynomial
      (mk OrbOctaR.W (octaSeeds 3)) = 0 := by
  have h := q24_lowerDesc q24_grading_lt81 channel81
  rw [map_sub, map_smul, map_sub, map_smul] at h
  have hm := q24_XY_negative 29
  norm_num only [Nat.cast_ofNat, Int.reduceAdd, Int.reduceNeg] at hm
  rw [hm, zero_sub, neg_eq_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) c3_ne_zero)

end VOA.Classification.COne.OrbOctaZD
