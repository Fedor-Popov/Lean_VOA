import VOA.Huang.LogHuangODEIterPointAnalytic
import VOA.Huang.LogRemovalOps
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! The actual logarithmic multiplier at the collision point is holomorphic
and has a convergent power series. Multiplying by it preserves a finite
log-Frobenius expansion, including all logarithmic coefficients. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA PowerSeries VOA.Huang.FrobeniusLog VOA.Huang.AssocExpansion
open VOA.Huang.HuangODEIterPoint VOA.Huang.LogHuangODEIterPoint
open VOA.Huang.LogRemovalCoeff VOA.Huang.HuangODEAlgebra
open scoped BigOperators

noncomputable def logOneAddSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => (-1 : ℂ)^(n+1)/(n : ℂ)

/-- The Taylor coefficients of log(1+u) are bounded. -/
theorem logOneAddSeries_subexp : logOneAddSeries∈SubexpPS := by
  apply mem_subexpPS.mpr
  apply Subexponential.of_le (b := fun _ => 1) _ (subexponential_const 1)
  intro n
  simp only [logOneAddSeries,coeff_mk,norm_div,norm_pow,norm_neg,norm_one,
    one_pow,norm_natCast]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hh : (1 : ℝ)≤n := by exact_mod_cast hn
  exact (div_le_one (by positivity : (0 : ℝ)<n)).mpr hh

/-- This is the actual principal logarithm on the entire open unit disc. -/
theorem psEval_logOneAddSeries {u : ℂ} (hu : ‖u‖<1) :
    psEval logOneAddSeries u=Complex.log (1+u) := by
  rw [← (Complex.hasSum_taylorSeries_log hu).tsum_eq]
  unfold psEval
  refine tsum_congr fun n => ?_
  simp only [logOneAddSeries,coeff_mk]
  ring

/-- Finite powers of the actual log(1+exp(t)) preserve collision expansions. -/
theorem hasLogExp_logOneAdd_mul {F : ℂ → ℂ} (hF : HasLogExp overlapDomain F) (k : ℕ) :
    HasLogExp overlapDomain (fun t => (Complex.log (1+Complex.exp t))^k*F t) := by
  have hpow := SubexpPS.pow_mem logOneAddSeries_subexp k
  obtain ⟨E,hE⟩ := hasLogExp_psEval_mul overlapDomain_subset hF hpow
  refine ⟨E,fun t ht => ?_⟩
  have hu : ‖Complex.exp t‖<1 := by
    rw [Complex.norm_exp]
    exact Real.exp_lt_one_iff.mpr ht.1
  have he := hE t ht
  dsimp only at he ⊢
  rw [psEval_pow logOneAddSeries_subexp hu,psEval_logOneAddSeries hu] at he
  exact he

/-- Generic convergent collision solutions have honest finite logarithmic expansions. -/
theorem hasLogExp_collision {H : PowerSeries ℂ} (hH : H∈SubexpPS) (κ σ : ℂ)
    (hrel : ∃ (m : ℕ) (r : ℕ → PowerSeries ℂ), (∀ k,r k∈ratRing 0) ∧
      (DOp κ σ)^[m] H=∑ k∈Finset.range m,r k*(DOp κ σ)^[k] H) :
    HasLogExp overlapDomain (Ev κ σ H) := by
  obtain ⟨ι,hi,lam,p,a,hp,he⟩ := collision_frobenius_expansion hH κ σ hrel
  refine ⟨@LogExp.mk ι hi lam (fun j => a j•p j) (fun j => (hp j).smul (a j)),?_⟩
  intro t ht
  rw [he t ht]
  simp only [LogExp.eval,logFun_smul]

end VOA.Huang.LogAssocExpansion
