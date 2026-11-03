/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergGrading
import VOA.Examples.HeisenbergVirasoro
import VOA.Core.Skew
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# FRONT B — the structural grading axioms + VA4 bilinear extension (Heisenberg VOA)

This file discharges, for the rank-1 Heisenberg (free-boson) Fock space, the structural
PreVertexAlgebra axioms that remained open after `HeisenbergGrading` (VA1, VA5):

* **VA4-GENERAL** `Y_local (k u v) : Local (Y k u) (Y k v)` for ARBITRARY `u v : Fock`.
  `Y k` is `ℂ`-linear (a `Finsupp.linearCombination` over monomials), so `Y k u` is a finite
  sum `∑ a ∈ u.support, (u a) • Ymon k a`.  `Ymon_local` gives locality for each monomial
  pair; `Local.add`/`Local.sum`/`Local.smul'`/`Local.smulR` (Core.Skew / HeisenbergVertex)
  extend it bilinearly.
* **VA1 `isInternal`** `gradingZ_isInternal : DirectSum.IsInternal gradingZ`.  The Fock space
  `MvPolynomial ℕ ℂ` is the internal direct sum of its weighted-homogeneous components
  (`MvPolynomial.weightedDecomposition`); the `ℤ`-extension `gradingZ` (`⊥` below `0`) inherits
  `IsInternal` (the extra `⊥` pieces affect neither independence nor the supremum).
* **finrank** `gradingZ_finrank n : FiniteDimensional ℂ (gradingZ n)`.  Each `gradingW w` is
  spanned by the finitely many monomials of weighted degree `w` (a variable `i` has weight
  `i+1`, so weight-`w` monomials use only variables `< w` with exponents `≤ w`); `gradingZ n = ⊥`
  for `n < 0`.
* **VOA4a `vacuum_grade`** `gradingZ_zero_eq_span_vacuum : gradingZ 0 = ℂ ∙ vacuum` (the weight-0
  component is the constants `ℂ·1`), and **`conformal_mem`** `omega_mem_gradingZ_two : ω k ∈
  gradingZ 2` (`ω = (1/2k) a₋₁a₋₁1`, weight `1+1 = 2`).

## Status
Front B.  Fully axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
-/

namespace VOA

open scoped BigOperators
open MvPolynomial
open Module (End)

universe u

/-! ## §1  VA4-GENERAL — bilinear extension of locality to all of `Fock` -/

/-- A single monomial field `(u a) • Ymon k a` is local with a single monomial field
`(v b) • Ymon k b` — `Ymon_local` scaled on both sides. -/
theorem smul_Ymon_local (k : ℂ) (ca cb : ℂ) (a b : ℕ →₀ ℕ) :
    Local (ca • Ymon k a) (cb • Ymon k b) :=
  Local.smulR cb (VertexOperatorAlgebra.Local.smul' ca (Ymon_local k a b))

/-- `Y k u` as the explicit finite sum of its scaled monomial fields. -/
theorem Y_eq_support_sum (k : ℂ) (u : Fock) :
    Y k u = ∑ a ∈ u.support, (u a) • Ymon k a := by
  rw [show Y k u = Finsupp.linearCombination ℂ (Ymon k) u from rfl,
      Finsupp.linearCombination_apply]
  rfl

/-- A scaled monomial field is local with the full vertex operator `Y k v` (expand `Y k v` as a
finite sum of scaled monomial fields; the sum sits on the right, so assemble via `Local.sum` and
symmetry). -/
theorem smul_Ymon_local_Y (k : ℂ) (ca : ℂ) (a : ℕ →₀ ℕ) (v : Fock) :
    Local (ca • Ymon k a) (Y k v) := by
  classical
  rw [Y_eq_support_sum k v]
  refine (VertexOperatorAlgebra.Local.sum v.support (fun b => (v b) • Ymon k b)
    (fun b _ => ?_)).symm
  exact smul_Ymon_local k (v b) ca b a

/-- **VA4 (locality), general states.**  `Y(u,z)` and `Y(v,z)` are mutually local for ARBITRARY
`u v : Fock`.  `Y k u` is the `ℂ`-linear combination `∑ a ∈ u.support, (u a) • Ymon k a`; each
scaled monomial field is local with the whole `Y k v` (`smul_Ymon_local_Y`), and `Local.sum`
assembles the finite sum. -/
theorem Y_local (k : ℂ) (u v : Fock) : Local (Y k u) (Y k v) := by
  classical
  rw [Y_eq_support_sum k u]
  exact VertexOperatorAlgebra.Local.sum u.support (fun a => (u a) • Ymon k a)
    (fun a _ => smul_Ymon_local_Y k (u a) a v)

/-! ## §2  VA1 `isInternal` — the internal direct-sum decomposition of `Fock`

`MvPolynomial.weightedDecomposition ℂ weightFn` is a `DirectSum.Decomposition` of
`Fock = MvPolynomial ℕ ℂ` into the `ℕ`-indexed weighted-homogeneous submodules `gradingW`.
Its `IsInternal` transports to the `ℤ`-extension `gradingZ` (which is `⊥` below `0`). -/

/-- The Fock grading `gradingW : ℕ → Submodule ℂ Fock` is an internal direct sum (the
weighted-homogeneous decomposition of `MvPolynomial ℕ ℂ`). -/
theorem gradingW_isInternal : DirectSum.IsInternal gradingW :=
  (MvPolynomial.weightedDecomposition ℂ weightFn).isInternal

/-- `iSupIndep gradingW` and `iSup gradingW = ⊤`, the two halves of the ℕ-graded internal
direct sum. -/
theorem gradingW_iSupIndep : iSupIndep gradingW :=
  gradingW_isInternal.submodule_iSupIndep

theorem gradingW_iSup_eq_top : iSup gradingW = ⊤ :=
  gradingW_isInternal.submodule_iSup_eq_top

/-- `gradingZ` restricted to its non-`⊥` indices is a reindexing of `gradingW` by the injective
`Int.toNat` (every non-`⊥` index is `≥ 0`), hence independent. -/
theorem gradingZ_iSupIndep : iSupIndep gradingZ := by
  -- It suffices to prove independence of the non-`⊥` pieces (`iSupIndep_ne_bot`).
  rw [← iSupIndep_ne_bot]
  -- The non-`⊥` pieces inject into `ℕ` via `Int.toNat`, where they coincide with `gradingW`.
  have hfinj : Function.Injective
      (fun i : {n : ℤ // gradingZ n ≠ ⊥} => i.1.toNat) := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩ h
    -- both `m, n ≥ 0` (else the piece is `⊥`), and `toNat` agrees, so `m = n`
    have hm0 : 0 ≤ m := by
      by_contra hlt; exact hm (gradingZ_of_neg (lt_of_not_ge hlt))
    have hn0 : 0 ≤ n := by
      by_contra hlt; exact hn (gradingZ_of_neg (lt_of_not_ge hlt))
    have h' : m.toNat = n.toNat := h
    have hmn : m = n := by
      rw [← Int.toNat_of_nonneg hm0, ← Int.toNat_of_nonneg hn0, h']
    exact Subtype.ext hmn
  have hcomp : (fun i : {n : ℤ // gradingZ n ≠ ⊥} => gradingZ i.1)
      = gradingW ∘ (fun i : {n : ℤ // gradingZ n ≠ ⊥} => i.1.toNat) := by
    funext i
    obtain ⟨n, hn⟩ := i
    have hn0 : 0 ≤ n := by
      by_contra hlt; exact hn (gradingZ_of_neg (lt_of_not_ge hlt))
    simp only [Function.comp_apply]
    exact gradingZ_of_nonneg hn0
  rw [hcomp]
  exact gradingW_iSupIndep.comp hfinj

/-- The supremum of `gradingZ` over all of `ℤ` is `⊤`: it dominates the supremum over the
non-negative indices, which is already `⊤` (the negative pieces are `⊥`). -/
theorem gradingZ_iSup_eq_top : iSup gradingZ = ⊤ := by
  rw [eq_top_iff, ← gradingW_iSup_eq_top]
  refine iSup_le (fun w => ?_)
  -- `gradingW w = gradingZ w ≤ iSup gradingZ`
  have h : gradingW w = gradingZ (w : ℤ) := by
    rw [gradingZ_of_nonneg (by positivity), Int.toNat_natCast]
  rw [h]
  exact le_iSup gradingZ (w : ℤ)

/-- **VA1 `isInternal`.**  The `ℤ`-extended Fock grading `gradingZ` is a genuine internal
direct-sum decomposition `Fock = ⊕ₙ gradingZ n` (with `gradingZ n = ⊥` for `n < 0`). -/
theorem gradingZ_isInternal : DirectSum.IsInternal gradingZ :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    gradingZ_iSupIndep gradingZ_iSup_eq_top

/-! ## §3  finrank — each graded piece is finite-dimensional

A weight-`w` monomial `∏ Xᵢ^{dᵢ}` uses only variables `i` with `i + 1 ≤ w` (weight `i+1`),
each with exponent `dᵢ ≤ w`.  Thus the set of weight-`w` exponent vectors injects into
`Fin w → Fin (w+1)` and is finite; `gradingW w` is the span of the corresponding finitely many
monomials, hence finite-dimensional. -/

/-- The set of weight-`w` exponent vectors (the monomial degrees of weighted degree `w`). -/
def weightDegSet (w : ℕ) : Set (ℕ →₀ ℕ) := {d : ℕ →₀ ℕ | Finsupp.weight weightFn d = w}

/-- A weight-`w` exponent vector has all entries `≤ w`. -/
theorem weightDegSet_entry_le {w : ℕ} {d : ℕ →₀ ℕ} (hd : d ∈ weightDegSet w) (i : ℕ) :
    d i ≤ w := by
  have hle : d i ≤ Finsupp.weight weightFn d :=
    Finsupp.le_weight weightFn (by rw [weightFn_apply]; omega) d
  rw [show Finsupp.weight weightFn d = w from hd] at hle
  exact hle

/-- A weight-`w` exponent vector is supported on variables `< w` (a used variable `i` has weight
`i + 1 ≤ w`). -/
theorem weightDegSet_support_lt {w : ℕ} {d : ℕ →₀ ℕ} (hd : d ∈ weightDegSet w) {i : ℕ}
    (hi : d i ≠ 0) : i < w := by
  have hle : weightFn i ≤ Finsupp.weight weightFn d := Finsupp.le_weight_of_ne_zero' weightFn hi
  rw [show Finsupp.weight weightFn d = w from hd, weightFn_apply] at hle
  omega

/-- **The weight-`w` exponent vectors form a finite set** (inject into `Fin w → Fin (w+1)`). -/
theorem weightDegSet_finite (w : ℕ) : (weightDegSet w).Finite := by
  classical
  rw [← Set.finite_coe_iff]
  -- inject `d ↦ (fun i : Fin w => ⟨d i, _⟩ : Fin w → Fin (w+1))`
  refine Finite.of_injective
    (β := Fin w → Fin (w + 1))
    (fun d i => ⟨d.1 i.1, by
      have := weightDegSet_entry_le d.2 i.1; omega⟩) ?_
  rintro ⟨d, hd⟩ ⟨e, he⟩ h
  refine Subtype.ext (Finsupp.ext fun i => ?_)
  by_cases hiw : i < w
  · -- on the `Fin w` block the images agree
    have := congrFun h ⟨i, hiw⟩
    simpa using congrArg Fin.val this
  · -- outside the block both vanish (support `< w`)
    have hdz : d i = 0 := by
      by_contra hne; exact hiw (weightDegSet_support_lt hd hne)
    have hez : e i = 0 := by
      by_contra hne; exact hiw (weightDegSet_support_lt he hne)
    rw [hdz, hez]

/-- The (finite) set of weight-`w` monomials `monomial d 1`. -/
noncomputable def weightMonSet (w : ℕ) : Set Fock :=
  (fun d => (monomial d 1 : Fock)) '' weightDegSet w

theorem weightMonSet_finite (w : ℕ) : (weightMonSet w).Finite :=
  (weightDegSet_finite w).image _

/-- A weight-`w` homogeneous polynomial is the span of its weight-`w` monomials: every
`p ∈ gradingW w` lies in `span ℂ (weightMonSet w)`. -/
theorem gradingW_le_span (w : ℕ) :
    gradingW w ≤ Submodule.span ℂ (weightMonSet w) := by
  intro p hp
  rw [mem_gradingW] at hp
  -- write `p = ∑ d ∈ p.support, monomial d (coeff d p)`; each `d` has weight `w`
  rw [MvPolynomial.as_sum p]
  refine Submodule.sum_mem _ (fun d hd => ?_)
  -- `monomial d (coeff d p) = (coeff d p) • monomial d 1`
  have hdw : Finsupp.weight weightFn d = w := hp (MvPolynomial.mem_support_iff.mp hd)
  have hmem : (monomial d 1 : Fock) ∈ weightMonSet w :=
    ⟨d, hdw, rfl⟩
  have hscale : (monomial d (MvPolynomial.coeff d p) : Fock)
      = (MvPolynomial.coeff d p) • monomial d 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hscale]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/-- **`gradingW w` is finite-dimensional** (spanned by the finitely many weight-`w` monomials). -/
theorem gradingW_finiteDimensional (w : ℕ) : FiniteDimensional ℂ (gradingW w) := by
  have hspan : FiniteDimensional ℂ (Submodule.span ℂ (weightMonSet w)) :=
    FiniteDimensional.span_of_finite ℂ (weightMonSet_finite w)
  exact Submodule.finiteDimensional_of_le (gradingW_le_span w)

/-- **finrank.**  Each `ℤ`-graded piece `gradingZ n` is finite-dimensional: the weight-`n`
component for `n ≥ 0` (finitely many monomials) and `⊥` for `n < 0`. -/
theorem gradingZ_finrank (n : ℤ) : FiniteDimensional ℂ (gradingZ n) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [gradingZ_of_neg hn]
    infer_instance
  · rw [gradingZ_of_nonneg hn]
    exact gradingW_finiteDimensional n.toNat

/-! ## §4  VOA4a `vacuum_grade` and `conformal_mem` -/

/-- The weight-`0` component is the field of constants: `gradingW 0 = ℂ ∙ 1`. -/
theorem gradingW_zero_eq_span_one : gradingW 0 = ℂ ∙ (1 : Fock) := by
  apply le_antisymm
  · -- a weight-0 homogeneous polynomial is a constant
    intro p hp
    rw [mem_gradingW] at hp
    -- `p = C (coeff 0 p) = (coeff 0 p) • 1`
    have hconst : p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
      apply MvPolynomial.ext
      intro d
      rw [MvPolynomial.coeff_C]
      by_cases hd : d = 0
      · rw [if_pos hd.symm, hd]
      · rw [if_neg (Ne.symm hd)]
        -- if `coeff d p ≠ 0` then `weight d = 0`, forcing `d = 0`
        by_contra hne
        apply hd
        have hdw : Finsupp.weight weightFn d = 0 := hp hne
        -- `weight weightFn d = 0` with `weightFn i = i+1 > 0` forces `d = 0`
        refine Finsupp.ext (fun i => ?_)
        by_contra hdi
        have hle : weightFn i ≤ Finsupp.weight weightFn d :=
          Finsupp.le_weight_of_ne_zero' weightFn hdi
        rw [hdw, weightFn_apply] at hle
        omega
    rw [hconst, show (MvPolynomial.C (MvPolynomial.coeff 0 p) : Fock)
        = (MvPolynomial.coeff 0 p) • 1 from by rw [smul_eq_C_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · -- `ℂ·1 ⊆ gradingW 0`: `1` is weighted-homogeneous of weight `0`
    rw [Submodule.span_singleton_le_iff_mem]
    exact isWeightedHomogeneous_one ℂ weightFn

/-- **VOA4a `vacuum_grade`.**  The weight-0 piece is the line through the vacuum:
`gradingZ 0 = ℂ ∙ vacuum`. -/
theorem gradingZ_zero_eq_span_vacuum : gradingZ 0 = ℂ ∙ vacuum := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, gradingZ_of_nonneg (by norm_num),
      Int.toNat_natCast, gradingW_zero_eq_span_one, vacuum]

/-- **VOA4 `positivity`.**  `gradingZ n = ⊥` for `n < 0` (re-export of `gradingZ_of_neg`). -/
theorem gradingZ_positivity (n : ℤ) (hn : n < 0) : gradingZ n = ⊥ := gradingZ_of_neg hn

/-- The two-fold creation `a₋₁(a₋₁1)` has weight `2`: `osc k (-1)` raises weight by `1`, applied
twice to the weight-0 vacuum. -/
theorem osc_neg_one_sq_mem_gradingW_two (k : ℂ) :
    osc k (-1) (osc k (-1) vacuum) ∈ gradingW 2 := by
  have h1 : osc k (-1) vacuum ∈ gradingW 1 := by
    have := osc_neg_weight k (n := -1) (by norm_num) vacuum_mem_gradingW
    simpa using this
  have h2 := osc_neg_weight k (n := -1) (by norm_num) h1
  simpa using h2

/-- **`conformal_mem`.**  The Virasoro conformal vector `ω k = (1/2k) a₋₁a₋₁1` lies in the
weight-2 piece: `ω k ∈ gradingZ 2`. -/
theorem omega_mem_gradingZ_two (k : ℂ) : ω k ∈ gradingZ 2 := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl]
  apply mem_gradingZ_of_gradingW
  rw [ω]
  exact Submodule.smul_mem _ _ (osc_neg_one_sq_mem_gradingW_two k)

/-! ## §5  Axiom audit -/


end VOA
