import VOA.Classification.COne.QExpThetaNontrivial
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-! # Absolute convergence and divisor regrouping for twisted Lambert sums -/

open Complex Nat
open scoped UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- Positive-index Lambert sum restricted to a residue class. -/
def thetaResidueLambert (N a : ℕ) (u q : ℂ) : ℂ :=
  ∑' t : ℕ+, if (t : ℕ) % N = a then u * q ^ (t : ℕ) / (1 - u * q ^ (t : ℕ)) else 0

/-- The corresponding divisor coefficient. -/
def thetaResidueDivisor (N a : ℕ) (u : ℂ) (n : ℕ) : ℂ :=
  ∑ t ∈ n.divisors, if t % N = a then u ^ (n / t) else 0

/-- Absolute convergence justifying the two-index rearrangement. -/
theorem thetaResidueDouble_summable (N a : ℕ) {u q : ℂ} (hu : ‖u‖ = 1) (hq : ‖q‖ < 1) :
    Summable (fun p : ℕ+ × ℕ+ =>
      if (p.1 : ℕ) % N = a then u ^ (p.2 : ℕ) * q ^ ((p.1 : ℕ) * p.2) else 0) := by
  have hs : Summable (fun p : ℕ+ × ℕ+ => ‖q‖ ^ ((p.1 : ℕ) * p.2)) := by
    simpa using summable_prod_mul_pow (𝕜 := ℝ) 0 (r := ‖q‖) (by simpa using hq)
  apply hs.of_norm_bounded
  intro p
  split_ifs <;> simp [norm_pow, hu]

/-- Expanding each positive-index Lambert summand geometrically. -/
theorem thetaResidueLambert_eq_double (N a : ℕ) {u q : ℂ}
    (hu : ‖u‖ = 1) (hq : ‖q‖ < 1) :
    thetaResidueLambert N a u q = ∑' t : ℕ+, ∑' k : ℕ+,
      if (t : ℕ) % N = a then u ^ (k : ℕ) * q ^ ((t : ℕ) * k) else 0 := by
  apply tsum_congr
  intro t
  by_cases ht : (t : ℕ) % N = a
  · simp only [ht, if_true]
    have hv : ‖u * q ^ (t : ℕ)‖ < 1 := by
      rw [norm_mul, norm_pow, hu, one_mul]
      exact pow_lt_one₀ (norm_nonneg q) hq (by exact t.ne_zero)
    rw [thetaLambert_summand_geometric hv, ← tsum_pnat_eq_tsum_succ]
    apply tsum_congr
    intro k
    rw [mul_pow, ← pow_mul]
  · simp [ht]

set_option maxHeartbeats 800000 in
-- The dependent divisor-antidiagonal reindexing needs extra elaboration heartbeats.
/-- Regrouping the absolutely convergent double series by the product of indices. -/
theorem thetaResidueLambert_eq_divisors (N a : ℕ) {u q : ℂ}
    (hu : ‖u‖ = 1) (hq : ‖q‖ < 1) :
    thetaResidueLambert N a u q =
      ∑' n : ℕ+, thetaResidueDivisor N a u n * q ^ (n : ℕ) := by
  let F : ℕ+ × ℕ+ → ℂ := fun p =>
    if (p.1 : ℕ) % N = a then u ^ (p.2 : ℕ) * q ^ ((p.1 : ℕ) * p.2) else 0
  have hs : Summable F := thetaResidueDouble_summable N a hu hq
  have hσ : Summable (fun s => F (sigmaAntidiagonalEquivProd s)) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hs
  calc
    thetaResidueLambert N a u q = ∑' t : ℕ+, ∑' k : ℕ+, F (t, k) :=
      thetaResidueLambert_eq_double N a hu hq
    _ = ∑' p, F p := hs.tsum_prod.symm
    _ = ∑' s, F (sigmaAntidiagonalEquivProd s) :=
      (sigmaAntidiagonalEquivProd.tsum_eq F).symm
    _ = ∑' n : ℕ+, ∑' d : Nat.divisorsAntidiagonal (n : ℕ),
        F (sigmaAntidiagonalEquivProd ⟨n, d⟩) := hσ.tsum_sigma
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [F, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk, divisorsAntidiagonalFactors,
        thetaResidueDivisor, PNat.mk_coe, tsum_fintype, Finset.univ_eq_attach, Finset.sum_mul]
      rw [(n : ℕ).divisorsAntidiagonal.sum_attach
        (fun p : ℕ × ℕ => if p.1 % N = a then u ^ p.2 * q ^ (p.1 * p.2) else 0)]
      rw [Nat.sum_divisorsAntidiagonal
        (fun d k => if d % N = a then u ^ k * q ^ (d * k) else 0)]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
      split_ifs <;> simp

end VOA.Classification.COne.SSHecke
