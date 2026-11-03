import VOA.Huang.HuangODEIterPointAlg
import VOA.Huang.LogHuangODEProductAlgebra

/-! Collision differentiation retains the next logarithmic coefficient.
Every iterate stays in the same finite polynomial coefficient module. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEIterPoint
open VOA PowerSeries VOA.Huang.FuchsianODE VOA.Huang.HuangODEAlgebra
open VOA.Huang.HuangODEProduct (mul_mem_of_ratRing smul_mem_of_ratRing)
open VOA.Huang.HuangODEIterPoint (DOp DOp_apply DOp_X_pow_mul exists_dop_relation)
open scoped BigOperators

/-- The true coupled derivative gives five polynomially weighted terms. -/
theorem DOp_X_pow_mul_coupled (κ σ μ d : ℂ) (a n : ℕ)
    {A B C : PowerSeries ℂ}
    (hA : VOA.theta A = B + PowerSeries.C μ * A - d • C) :
    DOp κ σ (X^a * ((1-X)^n * A)) =
      (-(a : ℂ)-μ-κ-σ) • (X^a * ((1-X)^n * A)) +
      ((a : ℂ)+n+μ+κ) • (X^(a+1) * ((1-X)^n * A)) -
      X^a * ((1-X)^(n+1) * B) +
      d • (X^a * ((1-X)^n * C)) -
      d • (X^(a+1) * ((1-X)^n * C)) := by
  have hh : VOA.theta A = (B-d•C)+PowerSeries.C μ*A := by rw [hA]; abel
  rw [DOp_X_pow_mul κ σ μ a n hh]
  simp only [PowerSeries.smul_eq_C_mul,pow_succ]
  ring

/-- The collision operator preserves a joint coupled-log coefficient module. -/
theorem dop_iterate_mem_coupled {ι : Type*}
    (NN : Submodule (ratRing 0) (PowerSeries ℂ)) (κ σ : ℂ) (n₀ : ℕ)
    (A : ι → ℕ → PowerSeries ℂ) (next : ι → ι) (d : ι → ℂ) (μ : ℕ → ℂ)
    (hA : ∀ t j, VOA.theta (A t j) =
      A t (j+1) + PowerSeries.C (μ j)*A t j - d t • A (next t) j)
    (hmem : ∀ t j, (1-X)^(n₀+j)*A t j∈NN) :
    ∀ i a t j, (DOp κ σ)^[i] (X^a*((1-X)^(n₀+j)*A t j)) ∈ NN := by
  intro i
  induction i with
  | zero =>
    intro a t j
    simpa using mul_mem_of_ratRing NN (X_pow_mem 0 a) (hmem t j)
  | succ i ih =>
    intro a t j
    rw [Function.iterate_succ_apply,
      DOp_X_pow_mul_coupled κ σ (μ j) (d t) a (n₀+j) (hA t j),
      show n₀+j+1=n₀+(j+1) by ring]
    have h₁ := ih a t j
    have h₂ := ih (a+1) t j
    have h₃ := ih a t (j+1)
    have h₄ := ih a (next t) j
    have h₅ := ih (a+1) (next t) j
    rw [← Module.End.pow_apply] at h₁ h₂ h₃ h₄ h₅
    rw [← Module.End.pow_apply,map_sub,map_add,map_sub,map_add,
      map_smul,map_smul,map_smul,map_smul]
    exact NN.sub_mem
      (NN.add_mem (NN.sub_mem
        (NN.add_mem (smul_mem_of_ratRing NN _ h₁)
          (smul_mem_of_ratRing NN _ h₂)) h₃)
        (smul_mem_of_ratRing NN _ h₄))
      (smul_mem_of_ratRing NN _ h₅)

/-- Each actual coupled component has a monic collision equation. -/
theorem exists_dop_relation_coupled {ι : Type*}
    (NN : Submodule (ratRing 0) (PowerSeries ℂ)) (hfg : NN.FG)
    (κ σ : ℂ) (n₀ : ℕ) (A : ι → ℕ → PowerSeries ℂ)
    (next : ι → ι) (d : ι → ℂ) (μ : ℕ → ℂ)
    (hA : ∀ t j, VOA.theta (A t j) =
      A t (j+1) + PowerSeries.C (μ j)*A t j - d t • A (next t) j)
    (hmem : ∀ t j, (1-X)^(n₀+j)*A t j∈NN) (t : ι) :
    ∃ (m : ℕ) (r : ℕ → PowerSeries ℂ), (∀ k,r k∈ratRing 0) ∧
      (DOp κ σ)^[m] ((1-X)^n₀*A t 0) =
        ∑ k ∈ Finset.range m,r k*(DOp κ σ)^[k] ((1-X)^n₀*A t 0) := by
  apply exists_dop_relation NN hfg (DOp κ σ)
  intro i
  simpa only [pow_zero,one_mul,add_zero] using
    dop_iterate_mem_coupled NN κ σ n₀ A next d μ hA hmem i 0 t 0

end VOA.Huang.LogHuangODEIterPoint
