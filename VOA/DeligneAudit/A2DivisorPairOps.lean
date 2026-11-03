/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2DivisorReduction

/-!
# Pair operators (step 1 of `PairComparison`)

For a polynomial `P(t)` with coefficients in `P_m`, the `P_m`-combination `Σ_r P_r (x ⊗ t^r)` of loop
operators acts as `Σ_i P(z_i) x^{(i)}` (`polyOp_eq`).  Taking `P` divisible by
`∏_{k ∉ {a,b}} (t - z_k)` isolates the two slots `a, b`.  With `G_a = ∏_{k∉{a,b}}(z_a - z_k)` and the
divided difference `(G_a - G_b)/(z_a - z_b) ∈ P_m`, this gives that `P_m M_m` is stable under

* `S_x = G_a G_b (x^{(a)} + x^{(b)})` (`pairS_mem`), the diagonal action, and
* `A_x = G_a G_b (z_a - z_b) (x^{(a)} - x^{(b)})` (`pairA_mem`), the first-order antisymmetric action,

the two operators of the two-point computation B7 (`g ⊗ ℂ[t]/((t-z_a)(t-z_b))`), with the
coefficient `G_a G_b` that divides `E_{ab}`.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.AffineSl3 VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier

noncomputable section

variable {m : ℕ}

/-- **A polynomial combination of loop operators acts slotwise by evaluation.** -/
theorem polyOp_eq (x : Fin 8) (P : Polynomial (Pm m)) (v : TP m) :
    ∑ r ∈ Finset.range (P.natDegree + 1), P.coeff r • loopOp bracketTable m x r v =
      ∑ i : Fin m, P.eval (zr (K := ℂ) i) • slotOp x i v := by
  simp only [loopOp_eq_sum_slot, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_eq_sum_range]

theorem polyOp_mem (x : Fin 8) (P : Polynomial (Pm m)) {v : TP m} (hv : v ∈ MP m) :
    ∑ i : Fin m, P.eval (zr (K := ℂ) i) • slotOp x i v ∈ MP m := by
  rw [← polyOp_eq]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (loopOp_mem_MP x r hv)

/-- `L_{ab}(t) = ∏_{k ∉ {a,b}} (t - z_k)`. -/
def Lpair (a b : Fin m) : Polynomial (Pm m) :=
  ∏ k : Fin m, if k = a ∨ k = b then 1 else (Polynomial.X - Polynomial.C (zr (K := ℂ) k))

/-- `G_a = L_{ab}(z_a)`. -/
def Gpair (a b : Fin m) (i : Fin m) : Pm m := (Lpair a b).eval (zr (K := ℂ) i)

theorem eval_Lpair_other (a b k : Fin m) (hk : ¬ (k = a ∨ k = b)) :
    (Lpair a b).eval (zr (K := ℂ) k) = 0 := by
  rw [Lpair, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  rw [if_neg hk]
  simp

/-- Isolation of the two slots. -/
theorem polyOp_pair_mem (x : Fin 8) (a b : Fin m) (hab : a ≠ b) (P : Polynomial (Pm m))
    {v : TP m} (hv : v ∈ MP m) :
    (Gpair a b a * P.eval (zr (K := ℂ) a)) • slotOp x a v +
      (Gpair a b b * P.eval (zr (K := ℂ) b)) • slotOp x b v ∈ MP m := by
  classical
  have h := polyOp_mem x (Lpair a b * P) hv
  rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ a) (Finset.mem_univ b) hab] at h
  · simpa only [Polynomial.eval_mul, Gpair] using h
  · intro k _ hk
    rw [Polynomial.eval_mul, eval_Lpair_other a b k (by tauto), zero_mul, zero_smul]

/-- The divided difference `(G_a - G_b)/(z_a - z_b)`. -/
theorem exists_dividedDifference (a b : Fin m) :
    ∃ Q : Pm m, Gpair a b a - Gpair a b b = (zr (K := ℂ) a - zr b) * Q := by
  obtain ⟨Q, hQ⟩ := Polynomial.sub_dvd_eval_sub (zr (K := ℂ) a) (zr (K := ℂ) b) (Lpair a b)
  exact ⟨Q, by rw [Gpair, Gpair, hQ]⟩

/-- **Diagonal pair operator** `S_x = G_a G_b (x^{(a)} + x^{(b)})`. -/
theorem pairS_mem (x : Fin 8) (a b : Fin m) (hab : a ≠ b) {v : TP m} (hv : v ∈ MP m) :
    (Gpair a b a * Gpair a b b) • (slotOp x a v + slotOp x b v) ∈ MP m := by
  obtain ⟨Q, hQ⟩ := exists_dividedDifference a b
  -- `P(t) = G_b - Q (t - z_a)`
  have h := polyOp_pair_mem x a b hab
    (Polynomial.C (Gpair a b b) - Polynomial.C Q * (Polynomial.X - Polynomial.C (zr (K := ℂ) a))) hv
  have ea : Gpair a b a * (Polynomial.C (Gpair a b b) - Polynomial.C Q *
      (Polynomial.X - Polynomial.C (zr (K := ℂ) a))).eval (zr (K := ℂ) a) =
      Gpair a b a * Gpair a b b := by simp
  have eb : Gpair a b b * (Polynomial.C (Gpair a b b) - Polynomial.C Q *
      (Polynomial.X - Polynomial.C (zr (K := ℂ) a))).eval (zr (K := ℂ) b) =
      Gpair a b a * Gpair a b b := by
    simp only [Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X]
    linear_combination (-Gpair a b b) * hQ
  rw [ea, eb, ← smul_add] at h
  exact h

/-- **Antisymmetric pair operator** `A_x = G_a G_b (z_a - z_b)(x^{(a)} - x^{(b)})`. -/
theorem pairA_mem (x : Fin 8) (a b : Fin m) (hab : a ≠ b) {v : TP m} (hv : v ∈ MP m) :
    (Gpair a b a * Gpair a b b * (zr (K := ℂ) a - zr b)) • (slotOp x a v - slotOp x b v) ∈ MP m := by
  obtain ⟨Q, hQ⟩ := exists_dividedDifference a b
  -- `P(t) = (G_b - Q (t - z_a)) (2t - z_a - z_b)`
  have h := polyOp_pair_mem x a b hab
    ((Polynomial.C (Gpair a b b) - Polynomial.C Q * (Polynomial.X - Polynomial.C (zr (K := ℂ) a))) *
      (2 * Polynomial.X - Polynomial.C (zr (K := ℂ) a) - Polynomial.C (zr (K := ℂ) b))) hv
  have ea : Gpair a b a * ((Polynomial.C (Gpair a b b) - Polynomial.C Q *
      (Polynomial.X - Polynomial.C (zr (K := ℂ) a))) *
      (2 * Polynomial.X - Polynomial.C (zr (K := ℂ) a) -
        Polynomial.C (zr (K := ℂ) b))).eval (zr (K := ℂ) a) =
      Gpair a b a * Gpair a b b * (zr (K := ℂ) a - zr b) := by
    simp only [Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  have eb : Gpair a b b * ((Polynomial.C (Gpair a b b) - Polynomial.C Q *
      (Polynomial.X - Polynomial.C (zr (K := ℂ) a))) *
      (2 * Polynomial.X - Polynomial.C (zr (K := ℂ) a) -
        Polynomial.C (zr (K := ℂ) b))).eval (zr (K := ℂ) b) =
      -(Gpair a b a * Gpair a b b * (zr (K := ℂ) a - zr b)) := by
    simp only [Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    linear_combination (Gpair a b b * (zr (K := ℂ) a - zr b)) * hQ
  rw [ea, eb, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h
  exact h

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.polyOp_eq
#print axioms VOA.DeligneAudit.A2.pairS_mem
#print axioms VOA.DeligneAudit.A2.pairA_mem
end AxiomAudit
