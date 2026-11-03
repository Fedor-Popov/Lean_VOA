/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesKoszulSymbolMaps
import VOA.Examples.TwoSeriesKoszulParity

/-!
# The squeeze input split into an affine invariant count and a PBW count

The general coset-transfer theorem `twoSeries_gradedUnitary_of_affine_hodgeFree` takes, besides
`hA`, the dimension input `SqueezeInput`, whose half (I) bounds the leading BRST cohomology of the
concrete Kähler model.  The level-generic port of the Koszul chain (`TwoSeriesKoszulGr`, …,
`TwoSeriesKoszulSymbolMaps`, `TwoSeriesKoszulParity`) removes every BRST/Kähler object from (I):

* `leadKoszulEmbedding L hA n hp r` — **proved from `hA`**: an injective linear map of the
  leading cohomology `H⁰(Q⁻)_{(2r,0)}(n)` into the invariant tensors
  `(gr_r L_k(sl₂) ⊗ L_1(sl₂))^{g[t]}_n` (Koszul exactness of the actual `d_K` and the two symbol
  maps, ported to every level datum);
* `endpoint_oddZero L hA`, `endpoint_negZero L hA` — **proved**: no ghost-number-zero leading
  cohomology at odd or negative `2R`;
* `affineInvariants L r N` — the invariant space itself: tensors of total conformal weight `N` in
  `gr_r L_k(sl₂) ⊗ L_1(sl₂)` annihilated by every diagonal current mode
  `J^a_m ⊗ 1 + 1 ⊗ J^a_m`, `a ∈ {e, f, h}`, `m ≥ 0`;
* `cosetLevels_gradedUnitary_of_affine_invariants`,
  `twoSeries_gradedUnitary_of_affine_invariants` — **Affine GU ⇒ GU of `M(2, 2n+3)`**, given a
  coefficient `coeff N r` with
  (I) `rank (affineInvariants L r N) ≤ coeff N r` (an affine-algebra statement), and
  (II) `∑_{r ≤ p} coeff N r ≤ dim F_p L(c)_N` (the PBW count of the target, unchanged).

(I) is stated with `Module.rank`, so an infinite-dimensional invariant space makes the hypothesis
false rather than vacuous; `…_finrank` variants take `finrank` plus finite-dimensionality.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.SymbolModel VOA.GradedUnitaryCohomology VirGradedUnitarity
open Sl2CosetConcrete VirGoodFil
open scoped TensorProduct BigOperators

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable (L : CosetLevels)

/-! ### The invariant space -/

/-- **The `g[t]`-invariant tensors of total weight `N` in `gr_r L_k(sl₂) ⊗ L_1(sl₂)`**: the
weight-`N` tensors killed by every diagonal nonnegative current mode
`J^a_m ⊗ 1 + 1 ⊗ J^a_m` (`a = e, f, h`, `m ≥ 0`). Here `gr_r` is the associated graded of the
corrected PBW filtration of the simple affine factor, with its induced mode action. -/
def affineInvariants (r : ℕ) (N : ℤ) : Submodule ℂ (GrA L r ⊗[ℂ] BSpace) :=
  VOA.CyclicEval.tensorWeight (grDeg L r) VOA.CyclicEval.bWeight N ⊓ jointKer (grDiag L r)

theorem mem_affineInvariants (r : ℕ) (N : ℤ) (v : GrA L r ⊗[ℂ] BSpace) :
    v ∈ affineInvariants L r N ↔
      v ∈ VOA.CyclicEval.tensorWeight (grDeg L r) VOA.CyclicEval.bWeight N ∧
        VOA.CyclicEval.IsInv (grRho L r) VOA.CyclicEval.bMode v := by
  rw [affineInvariants, Submodule.mem_inf, mem_jointKer, isInv_iff_grDiag]

/-! ### The leading Koszul embedding, proved at every level -/

variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

/-- **The leading Koszul embedding at every level datum** (proved from `hA`). -/
def leadKoszulEmbedding (n : ℤ) (hp : IsPosOn ((endpointKahler L hA).geometry n).P ⊤) (r : ℕ) :
    GrKoszulEmbedding L ((endpointKahler L hA).model n hp) n r :=
  (endpointGrLeadKoszul_of_residual L hA (koszulResidual_endpoint L hA) n hp r).toGrKoszulEmbedding

/-- **The leading cohomology is no larger than the affine invariant space.** -/
theorem rank_leadCohom_le_affineInvariants (n : ℤ)
    (hp : IsPosOn ((endpointKahler L hA).geometry n).P ⊤) (r : ℕ) :
    Module.rank ℂ (((endpointKahler L hA).model n hp).leadCohom (2 * (r : ℤ), 0)) ≤
      Module.rank ℂ (affineInvariants L r n) := by
  set E := leadKoszulEmbedding L hA n hp r
  let f := E.ι.codRestrict (affineInvariants L r n)
    (fun v => (mem_affineInvariants L r n _).mpr ⟨E.weight v, E.inv v⟩)
  refine LinearMap.rank_le_of_injective f fun x y h => E.injective ?_
  have h' := congrArg (fun z : affineInvariants L r n => (z : GrA L r ⊗[ℂ] BSpace)) h
  exact h'

/-! ### From invariant counts to the squeeze input -/

theorem evenCoeff_two_mul (a : ℤ → ℕ → ℕ) (n : ℤ) (r : ℕ) :
    evenCoeff a n (2 * (r : ℤ)) = a n r := by
  unfold evenCoeff
  rw [if_pos (by omega)]
  congr 1
  omega

theorem evenCoeff_neg (a : ℤ → ℕ → ℕ) (n j : ℤ) (hj : j < 0) : evenCoeff a n j = 0 := by
  unfold evenCoeff
  rw [if_neg (by omega)]

theorem Icc_zero_eq_map (m : ℕ) :
    Finset.Icc (0 : ℤ) (m : ℤ) = (Finset.range (m + 1)).map Nat.castEmbedding := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x.toNat, by omega, by omega⟩
  · rintro ⟨a, ha, rfl⟩
    omega

/-- The Kähler-coordinate sum of `evenCoeff` is the plain PBW-length sum. -/
theorem sum_evenCoeff (a : ℤ → ℕ → ℕ) (n : ℤ) (p : ℕ) :
    ∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), evenCoeff a n j = ∑ r ∈ Finset.range (p + 1), a n r := by
  have h2 : (2 * (p : ℤ)) = ((2 * p : ℕ) : ℤ) := by push_cast; ring
  rw [h2, Icc_zero_eq_map, Finset.sum_map]
  simp only [Nat.castEmbedding_apply]
  induction p with
  | zero =>
    simp only [Nat.mul_zero, zero_add, Finset.sum_range_one, Nat.cast_zero]
    exact evenCoeff_two_mul a n 0
  | succ q ih =>
    rw [show 2 * (q + 1) + 1 = (2 * q + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih (by push_cast; ring)]
    have hodd : evenCoeff a n (((2 * q + 1 : ℕ)) : ℤ) = 0 := by
      have := evenCoeff_odd a n q
      push_cast
      exact this
    have heven : evenCoeff a n (((2 * q + 1 + 1 : ℕ)) : ℤ) = a n (q + 1) := by
      have := evenCoeff_two_mul a n (q + 1)
      rw [← this]
      congr 1
    rw [hodd, heven, add_zero, Finset.sum_range_succ _ (q + 1)]

/-- **Half (I) of the squeeze input from the affine invariant count.** -/
theorem finrank_leadCohom_le_of_invariants (coeff : ℤ → ℕ → ℕ)
    (hinv : ∀ (N : ℤ) (r : ℕ), Module.rank ℂ (affineInvariants L r N) ≤ coeff N r)
    (n : ℤ) (hp : IsPosOn ((endpointKahler L hA).geometry n).P ⊤) (j : ℤ) :
    Module.finrank ℂ (((endpointKahler L hA).model n hp).leadCohom (j, 0)) ≤
      evenCoeff coeff n j := by
  by_cases hj : j < 0
  · rw [endpoint_negZero L hA n hp j hj]; exact Nat.zero_le _
  rcases Int.even_or_odd' j with ⟨r', hr | hr⟩
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, r' = (r : ℤ) := ⟨r'.toNat, by omega⟩
    subst hr
    rw [evenCoeff_two_mul]
    exact Module.finrank_le_of_rank_le
      ((rank_leadCohom_le_affineInvariants L hA n hp r).trans (hinv n r))
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, r' = (r : ℤ) := ⟨r'.toNat, by omega⟩
    subst hr
    rw [endpoint_oddZero L hA n hp r]; exact Nat.zero_le _

/-- **The squeeze input from (I) the affine invariant count and (II) the PBW count.** -/
def squeezeInput_of_invariants (coeff : ℤ → ℕ → ℕ)
    (hinv : ∀ (N : ℤ) (r : ℕ), Module.rank ℂ (affineInvariants L r N) ≤ coeff N r)
    (hpbw : ∀ (N : ℤ) (p : ℕ),
      ∑ r ∈ Finset.range (p + 1), coeff N r ≤ Module.finrank ℂ ((virGradedFlag L.c).pieceIn p N)) :
    SqueezeInput L (brstHodgeInputs L hA).kahler where
  coeff := coeff
  invariantBound n hp j := finrank_leadCohom_le_of_invariants L hA coeff hinv n hp j
  pbwLower n p := by rw [sum_evenCoeff]; exact hpbw n p

/-! ### The endpoint theorems -/

include hA in
/-- **Coset transfer for any level datum, with (I) an affine invariant count.** Graded
unitarity of `L_{kA}(sl₂)`, an upper bound `coeff N r` on the `g[t]`-invariants of total weight
`N` in `gr_r L_{kA}(sl₂) ⊗ L_1(sl₂)`, and the PBW lower bound `∑_{r ≤ p} coeff N r ≤ dim F_p L(c)_N`
imply graded unitarity of the simple Virasoro VOA `L(c)`. -/
theorem cosetLevels_gradedUnitary_of_affine_invariants (coeff : ℤ → ℕ → ℕ)
    (hinv : ∀ (N : ℤ) (r : ℕ), Module.rank ℂ (affineInvariants L r N) ≤ coeff N r)
    (hpbw : ∀ (N : ℤ) (p : ℕ),
      ∑ r ∈ Finset.range (p + 1), coeff N r ≤ Module.finrank ℂ ((virGradedFlag L.c).pieceIn p N)) :
    VirGradedUnitary L.c (targetRealStructure L) :=
  cosetLevels_gradedUnitary_of_affine_hodgeFree L hA
    (squeezeInput_of_invariants L hA coeff hinv hpbw)

/-- `finrank` form of (I), for finite-dimensional invariant spaces. -/
theorem rank_le_of_finrank_le {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {c : ℕ} (h : Module.finrank ℂ V ≤ c) : Module.rank ℂ V ≤ c := by
  rw [← Module.finrank_eq_rank]
  exact_mod_cast h

end

/-- **The `(2, 2n+3)` series with (I) an affine invariant count.** For `k = -2 + 2/(2n+1)`:
graded unitarity of `L_k(sl₂)`, a coefficient `coeff N r` bounding the `g[t]`-invariant tensors of
total weight `N` in `gr_r L_k(sl₂) ⊗ L_1(sl₂)` from above, and the PBW lower bound
`∑_{r ≤ p} coeff N r ≤ dim F_p L(c_{2,2n+3})_N` imply graded unitarity of `M(2, 2n+3)`. -/
theorem twoSeries_gradedUnitary_of_affine_invariants (n : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (coeff : ℤ → ℕ → ℕ)
    (hinv : ∀ (N : ℤ) (r : ℕ),
      Module.rank ℂ (affineInvariants (twoSeriesLevels n) r N) ≤ coeff N r)
    (hpbw : ∀ (N : ℤ) (p : ℕ), ∑ r ∈ Finset.range (p + 1), coeff N r ≤
      Module.finrank ℂ ((virGradedFlag (twoSeriesLevels n).c).pieceIn p N)) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  cosetLevels_gradedUnitary_of_affine_invariants (twoSeriesLevels n) hA coeff hinv hpbw

/-- The same with (I) in `finrank` form, plus finite-dimensionality of the invariant spaces. -/
theorem twoSeries_gradedUnitary_of_affine_invariants_finrank (n : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (coeff : ℤ → ℕ → ℕ)
    (hfin : ∀ (N : ℤ) (r : ℕ), FiniteDimensional ℂ (affineInvariants (twoSeriesLevels n) r N))
    (hinv : ∀ (N : ℤ) (r : ℕ),
      Module.finrank ℂ (affineInvariants (twoSeriesLevels n) r N) ≤ coeff N r)
    (hpbw : ∀ (N : ℤ) (p : ℕ), ∑ r ∈ Finset.range (p + 1), coeff N r ≤
      Module.finrank ℂ ((virGradedFlag (twoSeriesLevels n).c).pieceIn p N)) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_affine_invariants n hA coeff
    (fun N r => haveI := hfin N r; rank_le_of_finrank_le (hinv N r)) hpbw

end VOA.TwoSeries
