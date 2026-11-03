/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonDivisor

/-! # Equal-size block symmetry of the Gordon divisor and quotient -/

namespace VOA.GordonSymmetry

open scoped BigOperators
open VOA.GordonFiltration VOA.GordonBlockEquiv VOA.GordonDivisor VOA.GordonCommonFactors

variable {τ : Type*} [LinearOrder τ]

/-- Orient an unordered pair canonically. -/
def orderedPair (u v : τ) (hne : u ≠ v) : IncreasingPair τ :=
  if h : u < v then ⟨(u, v), h⟩ else ⟨(v, u), lt_of_le_of_ne (le_of_not_gt h) hne.symm⟩

theorem orderedPair_swap (u v : τ) (hne : u ≠ v) :
    orderedPair v u hne.symm = orderedPair u v hne := by
  by_cases h : u < v
  · simp [orderedPair, h, not_lt_of_ge h.le]
  · have hh : v < u := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    simp [orderedPair, h, hh]

/-- Relabel an unordered pair and restore its canonical orientation. -/
def pairMap (e : Equiv.Perm τ) (p : IncreasingPair τ) : IncreasingPair τ :=
  orderedPair (e p.val.1) (e p.val.2) (e.injective.ne p.property.ne)

theorem pairMap_orderedPair (e : Equiv.Perm τ) (u v : τ) (hne : u ≠ v) :
    pairMap e (orderedPair u v hne) = orderedPair (e u) (e v) (e.injective.ne hne) := by
  by_cases h : u < v
  · simp [orderedPair, pairMap, h]
  · simp only [orderedPair, dif_neg h, pairMap]
    exact orderedPair_swap (e u) (e v) (e.injective.ne hne)

/-- Permutations act bijectively on unordered pairs. -/
def pairEquiv (e : Equiv.Perm τ) : Equiv.Perm (IncreasingPair τ) where
  toFun := pairMap e
  invFun := pairMap e.symm
  left_inv := by
    intro p
    change pairMap e.symm (orderedPair _ _ _) = p
    rw [pairMap_orderedPair]
    simp [orderedPair, p.property]
  right_inv := by
    intro p
    change pairMap e (orderedPair _ _ _) = p
    rw [pairMap_orderedPair]
    simp [orderedPair, p.property]

noncomputable section
variable {σ K : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [Field K]

/-- The even exponent makes each cluster factor independent of its orientation. -/
theorem factor_orderedPair (w : τ → ℕ) (u v : τ) (hne : u ≠ v) :
    (let p := orderedPair u v hne
     (collisionFactor (K := K) p.val.1 p.val.2) ^ (2 * min (w p.val.1) (w p.val.2))) =
      (MvPolynomial.X u - MvPolynomial.X v) ^ (2 * min (w u) (w v)) := by
  by_cases h : u < v
  · simp [orderedPair, h, collisionFactor]
  · simp only [orderedPair, dif_neg h, collisionFactor, min_comm (w v) (w u)]
    rw [← neg_sub, neg_pow]
    simp

/-- The entire cluster divisor is invariant under every size-preserving block permutation. -/
theorem rename_clusterDivisor (f : σ → τ) (e : Equiv.Perm τ)
    (he : ∀ j, blockSize f (e j) = blockSize f j) :
    MvPolynomial.rename e (clusterDivisor (K := K) f) = clusterDivisor f := by
  rw [clusterDivisor, map_prod]
  calc
    (∏ p : IncreasingPair τ, MvPolynomial.rename e
      (collisionFactor p.val.1 p.val.2 ^ (2 * min (blockSize f p.val.1) (blockSize f p.val.2)))) =
        ∏ p : IncreasingPair τ,
          collisionFactor (pairEquiv e p).val.1 (pairEquiv e p).val.2 ^
            (2 * min (blockSize f (pairEquiv e p).val.1) (blockSize f (pairEquiv e p).val.2)) := by
      apply Finset.prod_congr rfl
      intro p _
      change _ = (let q := orderedPair (e p.val.1) (e p.val.2) (e.injective.ne p.property.ne)
        collisionFactor q.val.1 q.val.2 ^ (2 * min (blockSize f q.val.1) (blockSize f q.val.2)))
      rw [factor_orderedPair]
      simp only [map_pow, collisionFactor, map_sub, MvPolynomial.rename_X, he]
    _ = _ := Equiv.prod_comp (pairEquiv e) (fun p : IncreasingPair τ ↦
      collisionFactor (K := K) p.val.1 p.val.2 ^
        (2 * min (blockSize f p.val.1) (blockSize f p.val.2)))

/-- Symmetry of the source induces symmetry between equal-sized evaluated blocks. -/
theorem rename_blockEval (f : σ → τ) (e : Equiv.Perm τ)
    (he : ∀ j, blockSize f (e j) = blockSize f j)
    (F : MvPolynomial σ K) (hF : F.IsSymmetric) :
    MvPolynomial.rename e (blockEval f F) = blockEval f F := by
  change MvPolynomial.rename e (MvPolynomial.rename f F) = MvPolynomial.rename f F
  rw [MvPolynomial.rename_rename]
  apply blockEval_eq_of_blockSize_eq _ _ F hF
  intro j
  have hh := blockSize_equiv_comp f e (e.symm j)
  simp only [Equiv.apply_symm_apply] at hh
  exact hh.trans (by simpa using (he (e.symm j)).symm)

/-- Division by the nonzero Gordon cluster divisor preserves every equal-size block symmetry. -/
theorem exists_symmetric_quotient [CharZero K] (f : σ → τ)
    (U : Submodule K (MvPolynomial σ K)) (F : MvPolynomial σ K) (hF : F.IsSymmetric)
    (hmem : F ∈ filtration (τ := τ) U (shape f)) :
    ∃ q : MvPolynomial τ K, blockEval f F = clusterDivisor f * q ∧
      ∀ e : Equiv.Perm τ, (∀ j, blockSize f (e j) = blockSize f j) →
        MvPolynomial.rename e q = q := by
  obtain ⟨q, hq⟩ := clusterDivisor_dvd f U F hF hmem
  refine ⟨q, hq, ?_⟩
  intro e he
  apply mul_left_cancel₀ (clusterDivisor_ne_zero (K := K) f)
  calc
    clusterDivisor f * MvPolynomial.rename e q =
        MvPolynomial.rename e (clusterDivisor f * q) := by rw [map_mul, rename_clusterDivisor f e he]
    _ = blockEval f F := by rw [← hq, rename_blockEval f e he F hF]
    _ = clusterDivisor f * q := hq

end
end VOA.GordonSymmetry
