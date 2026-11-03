import VOA.Classification.COne.OrbOctaZDProjection36

/-! The second non-vacuum Zhu seed is killed by Q24. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbOdd OrbZhu OrbOctaR OrbC2c OrbSpan OrbOctaZC OrbOcta

theorem q24_lowerDesc {N : ℤ}
    (hbelow : ∀ d : ℤ, 0 < d → d < N → ∀ y ∈ W.grading d, q24L (mk W y) = 0)
    {z : (orbifold OrbC2b.octa).carrier} (hz : z ∈ lowerDesc W N) :
    q24L (mk W z) = 0 := by
  change z ∈ zeroKernel
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, y, hy, rfl⟩ := hz
    change q24L (mk W (W.L (-(m : ℤ) - 1) y)) = 0
    rw [show -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) by omega,
      mk_L_neg W hy (m + 1) (by omega)]
    simp only [map_smul, map_add, q24L_omega, smul_zero, zero_add]
    by_cases hneg : N - (m : ℤ) - 1 < 0
    · rw [W.positivity _ hneg, Submodule.mem_bot] at hy
      simp [hy]
    · by_cases hz : N - (m : ℤ) - 1 = 0
      · simp [hz]
      · rw [hbelow _ (by omega) (by omega) y hy, smul_zero, smul_zero]
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

/-- Q24 annihilates the weight-36 seed in the original spanning family. -/
theorem q24_seed_two :
    Polynomial.aeval (omegaL W) OrbOctaZ.positivePolynomial (mk W (octaSeeds 2)) = 0 := by
  have h := q24_lowerDesc (fun _ hp hn _ hy => q24_grading_lt36 hp hn hy) self_channel36
  rw [map_sub, map_smul, map_sub, map_smul] at h
  change q24L (selfMode (-5)) - (1359072 : ℂ) • q24L (mk W (octaSeeds 2)) = 0 at h
  rw [q24_selfMode_neg5, zero_sub, neg_eq_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

end VOA.Classification.COne.OrbOctaZD
