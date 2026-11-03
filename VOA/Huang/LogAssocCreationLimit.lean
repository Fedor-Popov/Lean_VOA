import VOA.Huang.LogAssocCreationEvaluation
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Actual creation power rows have their genuine constant-term limit.
The unrelated finite logarithmic point polynomial is retained and tends
to its true zeroth coefficient at insertion point one. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz Filter Topology
open scoped BigOperators

/-- A genuinely absolutely convergent creation power row tends to its
constant coefficient along positive real coordinates. -/
theorem tendsto_creation_tsum_const (A : ℕ → ℂ)
    (hs : Summable fun j : ℕ => A j*(1/2 : ℂ)^j) :
    Tendsto (fun r : ℝ => ∑' j : ℕ,A j*(r : ℂ)^j) (𝓝[>] 0) (𝓝 (A 0)) := by
  have hb : Summable (fun j : ℕ => ‖A j‖*(1/2 : ℝ)^j) := by
    have hh := hs.norm
    refine hh.congr fun j => ?_
    rw [norm_mul,norm_pow]
    norm_num
  have hpt (j : ℕ) : Tendsto (fun r : ℝ => A j*(r : ℂ)^j) (𝓝[>] 0)
      (𝓝 (A j*(0 : ℂ)^j)) := by
    have hc : Continuous (fun r : ℝ => A j*(r : ℂ)^j) := by fun_prop
    have hh := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa only [Complex.ofReal_zero] using hh
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun (r : ℝ) (j : ℕ) => A j*(r : ℂ)^j) (g := fun j => A j*(0 : ℂ)^j)
    hb hpt (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ)<1/2 by norm_num)] with r hr j
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr.1.le]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1.le hr.2.le j) (norm_nonneg _))
  rwa [tsum_eq_single 0 (fun j hj => by simp [zero_pow hj]),pow_zero,mul_one] at ht

/-- The actual finite logarithmic point polynomial tends to its true
zeroth coefficient as the positive insertion point tends to one. -/
theorem tendsto_logPointPolynomial_oneAdd (K : ℕ) (hK : 0<K) (lam : ℂ) (C : ℕ → ℂ) :
    Tendsto (fun r : ℝ => Complex.exp (Complex.log (1+(r : ℂ))*lam)*
      ∑ k∈Finset.range K,(Complex.log (1+(r : ℂ)))^k*C k)
      (𝓝[>] 0) (𝓝 (C 0)) := by
  have hlog : ContinuousAt (fun r : ℝ => Complex.log (1+(r : ℂ))) 0 := by
    apply ContinuousAt.clog
    · fun_prop
    · norm_num [Complex.slitPlane]
  have hc : ContinuousAt (fun r : ℝ => Complex.exp (Complex.log (1+(r : ℂ))*lam)*
      ∑ k∈Finset.range K,(Complex.log (1+(r : ℂ)))^k*C k) 0 := by
    apply ContinuousAt.mul
    · exact Complex.continuous_exp.continuousAt.comp (hlog.mul continuousAt_const)
    · exact tendsto_finsetSum (Finset.range K) fun k hk =>
        ((hlog.pow k).mul continuousAt_const).tendsto
  have he : Complex.exp (Complex.log (1+(0 : ℂ))*lam)*
      ∑ k∈Finset.range K,(Complex.log (1+(0 : ℂ)))^k*C k=C 0 := by
    simp only [add_zero,Complex.log_one,zero_mul,Complex.exp_zero,one_mul]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      rw [zero_pow hk0,zero_mul]
    · intro h0
      exact (h0 (Finset.mem_range.mpr hK)).elim
  have hh := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simpa only [Complex.ofReal_zero,he] using hh

end VOA.Huang.LogAssocExpansion
