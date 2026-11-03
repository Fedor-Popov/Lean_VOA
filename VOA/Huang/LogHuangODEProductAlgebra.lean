import VOA.Huang.HuangODEProduct
import VOA.Modularity.SubexpClosure

/-! A genuinely coupled logarithmic derivative chain lies in one finite
regular coefficient module. The upper logarithmic coefficient is retained
at every induction step; no ordinary-intertwiner derivative is assumed. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEProduct
open VOA PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra VOA.Huang.HuangODEProduct
open scoped BigOperators

/-- Linear iterates of the Euler operator preserve subtraction. -/
theorem thetaShift_iterate_sub (μ : ℂ) (i : ℕ) (x y : PowerSeries ℂ) :
    (thetaShift μ)^[i] (x-y) = (thetaShift μ)^[i] x - (thetaShift μ)^[i] y := by
  simp only [← Module.End.pow_apply, map_sub]

/-- All Euler iterates remain in the same module for a coupled derivative
family, including its higher logarithmic coefficients. -/
theorem theta_iter_mem_coupled {ι : Type*} {a : ℂ}
    (NN : Submodule (ratRing a) (PowerSeries ℂ))
    (Q : ι → ℕ → PowerSeries ℂ) (next : ι → ι) (d : ι → ℂ) (lam : ℕ → ℂ)
    (hQ : ∀ t j, Q t (j+1) = thetaShift (lam j) (Q t j) + d t • Q (next t) j)
    (hmem : ∀ t j, Q t j ∈ NN) (μ : ℂ) :
    ∀ i t j, (thetaShift μ)^[i] (Q t j) ∈ NN := by
  intro i
  induction i with
  | zero => intro t j; simpa using hmem t j
  | succ i ih =>
    intro t j
    rw [Function.iterate_succ_apply]
    have he : thetaShift μ (Q t j) =
        Q t (j+1) + (μ-lam j) • Q t j - d t • Q (next t) j := by
      rw [hQ]
      have ht : thetaShift μ (Q t j) =
          thetaShift (lam j) (Q t j) + (μ-lam j) • Q t j := by
        rw [← thetaShift_add, add_sub_cancel]
      rw [ht]
      module
    rw [he, thetaShift_iterate_sub, thetaShift_iterate_add,
      thetaShift_iterate_smul, thetaShift_iterate_smul]
    exact NN.sub_mem (NN.add_mem (ih t (j+1))
      (smul_mem_of_ratRing NN _ (ih t j)))
      (smul_mem_of_ratRing NN _ (ih (next t) j))

/-- Noetherian regular-singular elimination applies to every component of
an actual coupled logarithmic derivative chain. -/
theorem ratFuchsian_of_coupled_fg {ι : Type*} {a : ℂ}
    (NN : Submodule (ratRing a) (PowerSeries ℂ)) (hfg : NN.FG)
    (Q : ι → ℕ → PowerSeries ℂ) (next : ι → ι) (d : ι → ℂ) (lam : ℕ → ℂ)
    (hQ : ∀ t j, Q t (j+1) = thetaShift (lam j) (Q t j) + d t • Q (next t) j)
    (hmem : ∀ t j, Q t j ∈ NN) (t : ι) (ν : ℂ) :
    RatFuchsian a ν (Q t 0) := by
  apply ratFuchsian_of_fg NN hfg (K := 0) (μ := 0)
  intro i
  simpa only [pow_zero, one_mul] using
    theta_iter_mem_coupled NN Q next d lam hQ hmem 0 i t 0

/-- Finite-prefix offsets in the chosen mode coset preserve absolute convergence. -/
theorem summable_shifted_coeff_of_ratFuchsian {a ν : ℂ} (ha : ‖a‖ ≤ 1)
    {Q : PowerSeries ℂ} (hQ : RatFuchsian a ν Q) (K : ℕ)
    {t : ℂ} (ht : ‖t‖ < 1) :
    Summable fun n => ‖coeff (n+K) Q * t^n‖ := by
  have hg := (subexponential_of_ratFuchsian ha hQ).shift K
  have hs := summable_of_subexponential (fun n => norm_nonneg (coeff (n+K) Q))
    hg (norm_nonneg t) ht
  simpa only [norm_mul, norm_pow] using hs

end VOA.Huang.LogHuangODEProduct
