/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorChain
import VOA.DeligneAudit.A2DivisorFinal

/-!
# Type-generic divisor comparison: reduction to pairs, and the pair operators

For sector data `S`, the generic versions of the `A2DivisorReduction` and `A2DivisorPairOps`:

* `PairComparisonG S`: for `x ∈ W_m` and `a ≠ b`, some power of `E_{ab}` moves `x` into `P_m M_m`;
* **`divisorComparisonG_of_pair`**: `PairComparisonG S → DivisorComparisonG S` (prime avoidance
  `wS_not_mem`, which is type-free, plus the Reynolds operator);
* `pairS_mem`, `pairA_mem`: `P_m M_m` is stable under the pair operators
  `S_x = G_a G_b (x^{(a)} + x^{(b)})` and `A_x = G_a G_b (z_a - z_b)(x^{(a)} - x^{(b)})`.
-/

namespace VOA.DeligneAudit.DeligneDivisor

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier
open VOA.HeightOneGlobalization VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.A2 (Pm pairE wSum wS wS_not_mem wSum_isSymmetric Lpair Gpair
  eval_Lpair_other exists_dividedDifference)

noncomputable section

variable (S : DeligneSectorData)

/-- **Pairwise local comparison for the type.** -/
structure PairComparisonG : Prop where
  le : ∀ m, ∀ x ∈ currentCarrier S.fullMatrix m 0, ∀ a b : Fin (m + 0), a ≠ b →
    ∃ N : ℕ, (pairE a b) ^ N • x ∈ MP S m

variable {S}

/-- **`DivisorComparisonG` from the pairwise local comparison.** -/
theorem divisorComparisonG_of_pair (h : PairComparisonG S) : DivisorComparisonG S := by
  classical
  refine ⟨fun m x hx p hp => ?_⟩
  let f : Fin (m + 0) × Fin (m + 0) → Pm m := fun ab =>
    if ab.1 = ab.2 then 0 else pairE ab.1 ab.2
  have hN : ∀ ab, ∃ N : ℕ, f ab ^ (N + 1) • x ∈ MP S m := by
    intro ab
    by_cases hab : ab.1 = ab.2
    · refine ⟨0, ?_⟩
      simp only [f, if_pos hab, zero_pow (Nat.succ_ne_zero 0), zero_smul]
      exact Submodule.zero_mem _
    · obtain ⟨N, hN⟩ := h.le m x hx ab.1 ab.2 hab
      refine ⟨N, ?_⟩
      simp only [f, if_neg hab]
      rw [pow_succ, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hN
  choose Nf hNf using hN
  set n := Finset.univ.sup Nf
  have hterm : ∀ ab, f ab ^ (n + 1) • x ∈ MP S m := by
    intro ab
    have hle : Nf ab ≤ n := Finset.le_sup (Finset.mem_univ ab)
    rw [show n + 1 = (n - Nf ab) + (Nf ab + 1) by omega, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hNf ab)
  set K := (Finset.univ : Finset (Fin (m + 0) × Fin (m + 0))).card * n + 1
  have hspan := Ideal.sum_pow_mem_span_pow (Finset.univ : Finset (Fin (m + 0) × Fin (m + 0))) f n
  have hsum : (∑ ab, f ab) = wSum m := by
    rw [VOA.DeligneAudit.A2.wSum, ← Finset.sum_product']
    rfl
  have hwK : (wSum m) ^ K • x ∈ MP S m := by
    rw [← hsum]
    refine Submodule.span_induction (p := fun g _ => g • x ∈ MP S m) ?_ ?_ ?_ ?_ hspan
    · rintro _ ⟨ab, _, rfl⟩
      exact hterm ab
    · show (0 : Pm m) • x ∈ MP S m
      rw [zero_smul]; exact Submodule.zero_mem _
    · intro g g' _ _ hg hg'
      show (g + g') • x ∈ MP S m
      rw [add_smul]; exact Submodule.add_mem _ hg hg'
    · intro r g _ hg
      show (r • g) • x ∈ MP S m
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ _ hg
  have hsym : Symmetric ((wSum m) ^ K • x) :=
    fun e g he t => by
      rw [psmul_apply, psmul_apply, map_mul, hx.1 e g he t]
      congr 1
      rw [map_pow, wSum_isSymmetric m e]
  have hM := mem_Mspace_of_symmetric hwK hsym
  refine ⟨(wS m) ^ K, fun hmem => wS_not_mem p hp (p.isPrime.mem_of_pow_mem K hmem), ?_⟩
  convert hM using 1

/-! ## Pair operators -/

variable {m : ℕ}

/-- **A polynomial combination of loop operators acts slotwise by evaluation.** -/
theorem polyOp_eq (x : Fin S.n) (P : Polynomial (Pm m)) (v : TPs S m) :
    ∑ r ∈ Finset.range (P.natDegree + 1), P.coeff r • loopOp S.f m x r v =
      ∑ i : Fin m, P.eval (zr (K := ℂ) i) • slotOp x i v := by
  simp only [loopOp_eq_sum_slot, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_eq_sum_range]

theorem polyOp_mem (x : Fin S.n) (P : Polynomial (Pm m)) {v : TPs S m} (hv : v ∈ MP S m) :
    ∑ i : Fin m, P.eval (zr (K := ℂ) i) • slotOp x i v ∈ MP S m := by
  rw [← polyOp_eq]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (loopOp_mem_MP x r hv)

/-- Isolation of the two slots. -/
theorem polyOp_pair_mem (x : Fin S.n) (a b : Fin m) (hab : a ≠ b) (P : Polynomial (Pm m))
    {v : TPs S m} (hv : v ∈ MP S m) :
    (Gpair a b a * P.eval (zr (K := ℂ) a)) • slotOp x a v +
      (Gpair a b b * P.eval (zr (K := ℂ) b)) • slotOp x b v ∈ MP S m := by
  classical
  have h := polyOp_mem x (Lpair a b * P) hv
  rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ a) (Finset.mem_univ b) hab] at h
  · simpa only [Polynomial.eval_mul, Gpair] using h
  · intro k _ hk
    rw [Polynomial.eval_mul, eval_Lpair_other a b k (by tauto), zero_mul, zero_smul]

/-- **Diagonal pair operator** `S_x = G_a G_b (x^{(a)} + x^{(b)})`. -/
theorem pairS_mem (x : Fin S.n) (a b : Fin m) (hab : a ≠ b) {v : TPs S m} (hv : v ∈ MP S m) :
    (Gpair a b a * Gpair a b b) • (slotOp x a v + slotOp x b v) ∈ MP S m := by
  obtain ⟨Q, hQ⟩ := exists_dividedDifference a b
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
theorem pairA_mem (x : Fin S.n) (a b : Fin m) (hab : a ≠ b) {v : TPs S m} (hv : v ∈ MP S m) :
    (Gpair a b a * Gpair a b b * (zr (K := ℂ) a - zr b)) • (slotOp x a v - slotOp x b v) ∈
      MP S m := by
  obtain ⟨Q, hQ⟩ := exists_dividedDifference a b
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

end VOA.DeligneAudit.DeligneDivisor

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneDivisor.divisorComparisonG_of_pair
#print axioms VOA.DeligneAudit.DeligneDivisor.pairS_mem
#print axioms VOA.DeligneAudit.DeligneDivisor.pairA_mem
end AxiomAudit
