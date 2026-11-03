/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchVhatJacobi
import VOA.Core.Borcherds

/-!
# Closing the loop-Jacobi crux `VHat.GenLeibniz`

`ZhuVermaAnArchVhatJacobi.lean` reduced `VHat.VHatLeibniz` (and hence the `LieRing (V̂)` Jacobi
input) to the generator-level predicate `VHat.GenLeibniz`, and further to the single explicit
double-`finsum` identity `VHat.GenLeibniz_iff_explicit` in `V̂`.  This file carries the cross-walk
forward: it isolates the genuine remaining VOA content as a **single per-total-degree generator
identity** `GenJacobiDepth`, proves *unconditionally and axiom-free* that this depth-graded identity
implies the explicit `finsum` identity (and hence `GenLeibniz`, hence `VHatLeibniz`), and records
the precise residual.

## What is proved here

* `genDepthSupportFinite` — each of the three nested OPE double-`finsum`s in
  `GenLeibniz_iff_explicit` has finite support, so it may be regrouped freely.
* `GenJacobiDepth W hD` — the **per-total-degree generator identity**.  For every `a b c : 𝒱`,
  loop degrees `m k l : ℤ` and total OPE depth `s : ℕ`, the depth-`s` graded pieces of the three
  brackets agree in `V̂`:
  `Σ_{i+j=s} gBinom k j · gBinom m i • (a₍ᵢ₎(b₍ⱼ₎c))(m+k+l-s)`
    `= Σ_{i+p=s} gBinom m i · gBinom (m+k-i) p • ((a₍ᵢ₎b)₍ₚ₎c)(m+k+l-s)`
      `+ Σ_{i+p=s} gBinom m i · gBinom k p • (b₍ₚ₎(a₍ᵢ₎c))(m+k+l-s)`.
  Each side is a *finite* `Finset` sum over `Finset.antidiagonal s`, with a common loop degree
  `m+k+l-s`; this is the depth-graded repackaging of the master Borcherds identity
  `Core.Borcherds.jacobi` (5.1.7b) at the `gen`/`Im D` level.
* `GenJacobiDepth_imp_explicit` / `genJacobiDepth_imp_genLeibniz` /
  `VHatLeibniz_of_genJacobiDepth` — the unconditional, axiom-free reduction chain that turns the
  depth-graded identity into `GenLeibniz` and then `VHatLeibniz`.

## Status
Green, `sorry`/axiom-free.  The grading/finiteness/reindexing reduction is proved unconditionally;
`GenJacobiDepth` is recorded as the precise residual VOA identity (a hypothesis, exactly as
`BracketDescends`/`VHatAntisymm` are), not an axiom and not stubbed.  Its content is the
depth-graded slice of `Core.Borcherds.jacobi`, the loop-bracket avatar of Gannon 5.1.7b.

## References
DLM3 §4; Gannon §5.1.3 (5.1.7b), §5.3.2 Thm 5.3.4; `Core.Borcherds.jacobi`; cf.
`Foundations.AffineLie.loop_leibniz`.
-/

namespace VOA

open VertexOperatorAlgebra PreVertexAlgebra
open scoped BigOperators
open Finsupp

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## Finiteness of the three nested OPE double-`finsum`s

Each of `inner`, `outer_left`, `outer_right` is a `finsum` over `ℕ × ℕ` of `gen`-valued terms with
finitely-many nonzero entries (VOA regularity: `a₍ᵢ₎b = 0` for `i ≫ 0`). -/

/-- The inner family `(i,j) ↦ gBinom k j · gBinom m i • (a₍ᵢ₎(b₍ⱼ₎c))(m+(k+l-j)-i)` has finite
support. -/
theorem genInner_support_finite (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) :
    (Function.support fun p : ℕ × ℕ =>
      (gBinom k p.2) • (gBinom m p.1) •
        gen W (W.smul a p.1 (W.smul b p.2 c)) (m + (k + l - p.2) - p.1)).Finite := by
  obtain ⟨Nbc, hNbc⟩ := W.smul_eventually_zero b c
  classical
  -- nonvanishing forces `j < Nbc.toNat` and (for that `j`) `i < N(a, b₍ⱼ₎c)`.  Collect a finite
  -- box as a finite union over `j` of `{(i, j) | i < bound j}`.
  refine Set.Finite.subset
    ((Set.finite_Iio Nbc.toNat).biUnion (fun j _ =>
        ((Set.finite_Iio (Classical.choose (W.smul_eventually_zero a (W.smul b j c))).toNat).image
          (fun i : ℕ => (i, j))))) ?_
  intro p hp
  rw [Function.mem_support] at hp
  -- p.2 < Nbc.toNat
  have hj : p.2 < Nbc.toNat := by
    by_contra hcon
    rw [not_lt] at hcon
    refine hp ?_
    rw [hNbc p.2 (le_trans (Int.self_le_toNat Nbc) (by exact_mod_cast hcon)),
      W.smul_zero_right, gen_zero_left, smul_zero, smul_zero]
  -- for this j, p.1 < N(a, b_{p.2} c)
  have hspec := Classical.choose_spec (W.smul_eventually_zero a (W.smul b p.2 c))
  set Naj := Classical.choose (W.smul_eventually_zero a (W.smul b p.2 c)) with hNaj
  have hi : p.1 < Naj.toNat := by
    by_contra hcon
    rw [not_lt] at hcon
    refine hp ?_
    rw [hspec p.1 (le_trans (Int.self_le_toNat Naj) (by exact_mod_cast hcon)), gen_zero_left,
      smul_zero, smul_zero]
  rw [Set.mem_iUnion]
  refine ⟨p.2, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hj, ?_⟩
  rw [Set.mem_image]
  exact ⟨p.1, by rw [Set.mem_Iio, ← hNaj]; exact hi, by rw [Prod.mk.eta]⟩

/-- The outer-left family `(i,p) ↦ gBinom m i · gBinom (m+k-i) p • ((a₍ᵢ₎b)₍ₚ₎c)(…)` has finite
support. -/
theorem genOuterLeft_support_finite (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) :
    (Function.support fun q : ℕ × ℕ =>
      (gBinom m q.1) • (gBinom (m + k - q.1) q.2) •
        gen W (W.smul (W.smul a q.1 b) q.2 c) (m + k - q.1 + l - q.2)).Finite := by
  obtain ⟨Nab, hNab⟩ := W.smul_eventually_zero a b
  classical
  refine Set.Finite.subset
    ((Set.finite_Iio Nab.toNat).biUnion (fun i _ =>
        ((Set.finite_Iio (Classical.choose (W.smul_eventually_zero (W.smul a i b) c)).toNat).image
          (fun p : ℕ => (i, p))))) ?_
  intro q hq
  rw [Function.mem_support] at hq
  have hi : q.1 < Nab.toNat := by
    by_contra hcon
    rw [not_lt] at hcon
    refine hq ?_
    rw [hNab q.1 (le_trans (Int.self_le_toNat Nab) (by exact_mod_cast hcon)), W.smul_zero_left,
      gen_zero_left, smul_zero, smul_zero]
  have hspec := Classical.choose_spec (W.smul_eventually_zero (W.smul a q.1 b) c)
  set Np := Classical.choose (W.smul_eventually_zero (W.smul a q.1 b) c) with hNp
  have hp : q.2 < Np.toNat := by
    by_contra hcon
    rw [not_lt] at hcon
    refine hq ?_
    rw [hspec q.2 (le_trans (Int.self_le_toNat Np) (by exact_mod_cast hcon)), gen_zero_left,
      smul_zero, smul_zero]
  rw [Set.mem_iUnion]
  refine ⟨q.1, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hi, ?_⟩
  rw [Set.mem_image]
  exact ⟨q.2, by rw [Set.mem_Iio, ← hNp]; exact hp, by rw [Prod.mk.eta]⟩

/-- The outer-right family `(i,p) ↦ gBinom m i · gBinom k p • (b₍ₚ₎(a₍ᵢ₎c))(…)` has finite
support. -/
theorem genOuterRight_support_finite (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) :
    (Function.support fun q : ℕ × ℕ =>
      (gBinom m q.1) • (gBinom k q.2) •
        gen W (W.smul b q.2 (W.smul a q.1 c)) (k + (m + l - q.1) - q.2)).Finite := by
  obtain ⟨Nac, hNac⟩ := W.smul_eventually_zero a c
  classical
  refine Set.Finite.subset
    ((Set.finite_Iio Nac.toNat).biUnion (fun i _ =>
        ((Set.finite_Iio (Classical.choose (W.smul_eventually_zero b (W.smul a i c))).toNat).image
          (fun p : ℕ => (i, p))))) ?_
  intro q hq
  rw [Function.mem_support] at hq
  have hi : q.1 < Nac.toNat := by
    by_contra hcon
    rw [not_lt] at hcon
    refine hq ?_
    rw [hNac q.1 (le_trans (Int.self_le_toNat Nac) (by exact_mod_cast hcon)), W.smul_zero_right,
      gen_zero_left, smul_zero, smul_zero]
  have hspec := Classical.choose_spec (W.smul_eventually_zero b (W.smul a q.1 c))
  set Np := Classical.choose (W.smul_eventually_zero b (W.smul a q.1 c)) with hNp
  have hp : q.2 < Np.toNat := by
    by_contra hcon
    rw [not_lt] at hcon
    refine hq ?_
    rw [hspec q.2 (le_trans (Int.self_le_toNat Np) (by exact_mod_cast hcon)), gen_zero_left,
      smul_zero, smul_zero]
  rw [Set.mem_iUnion]
  refine ⟨q.1, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hi, ?_⟩
  rw [Set.mem_image]
  exact ⟨q.2, by rw [Set.mem_Iio, ← hNp]; exact hp, by rw [Prod.mk.eta]⟩

/-! ## Depth regrouping: a `ℕ × ℕ`-finsum equals the `finsum` of its antidiagonal slices

A finitely-supported `ℕ × ℕ`-`finsum` regroups along the total-degree antidiagonals `i + j = s`:
`∑ᶠ p, f p = ∑ᶠ s : ℕ, ∑ p ∈ antidiagonal s, f p`.  Each antidiagonal slice is a `Finset` sum
(finite, `s`-graded), and the outer `finsum` over `s` is finite by `f`-regularity. -/

/-- General depth-regrouping for finitely-supported `ℕ × ℕ`-`finsum`s. -/
theorem finsum_prod_eq_finsum_antidiagonal {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M)
    (hf : (Function.support f).Finite) :
    (∑ᶠ p : ℕ × ℕ, f p) = ∑ᶠ s : ℕ, ∑ p ∈ Finset.antidiagonal s, f p := by
  classical
  -- a common bounding finset for both sides: every nonzero `p` has `p.1 + p.2 < B`.
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ p ∈ Function.support f, p.1 + p.2 < B := by
    refine ⟨(hf.toFinset.image (fun p => p.1 + p.2)).sup id + 1, fun p hp => ?_⟩
    have : p ∈ hf.toFinset := by rw [Set.Finite.mem_toFinset]; exact hp
    have hle : p.1 + p.2 ≤ (hf.toFinset.image (fun p => p.1 + p.2)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ this)
    omega
  -- LHS = sum over the disjoint biUnion of antidiagonals `s < B`.
  have hbij : (Function.support f) ⊆ ↑((Finset.range B).biUnion Finset.antidiagonal) := by
    intro p hp
    rw [Finset.coe_biUnion]
    rw [Set.mem_iUnion₂]
    exact ⟨p.1 + p.2, by rw [Finset.coe_range, Set.mem_Iio]; exact hB p hp,
      by rw [Finset.mem_coe, Finset.mem_antidiagonal]⟩
  rw [finsum_eq_finsetSum_of_support_subset f hbij,
    Finset.sum_biUnion (by
      intro s _ t _ hst
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hps hpt
      rw [Finset.mem_antidiagonal] at hps hpt
      exact hst (hps.symm.trans hpt))]
  -- RHS: the `s`-indexed slice sums vanish for `s ≥ B`, so the outer finsum is the `range B` sum.
  rw [finsum_eq_finsetSum_of_support_subset
      (fun s : ℕ => ∑ p ∈ Finset.antidiagonal s, f p) (s := Finset.range B) ?_]
  intro s hs
  rw [Function.mem_support] at hs
  by_contra hc
  rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
  refine hs (Finset.sum_eq_zero fun p hp => ?_)
  rw [Finset.mem_antidiagonal] at hp
  by_contra hfp
  exact absurd (hB p hfp) (by omega)

/-! ## Flattening the nested OPE finsums to `ℕ × ℕ`-finsums

Each nested finsum `∑ᶠ x, c x • ∑ᶠ y, d y • gen (…)` in `GenLeibniz_iff_explicit` equals the
flat `ℕ × ℕ`-finsum `∑ᶠ p, c p.? • d p.? • gen (…)`, by pulling the scalar through the inner
finsum and applying `finsum_curry`. -/

/-- Per-`j` finiteness of the inner `i`-sum in the LHS family. -/
theorem genInner_inner_finite (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) (j : ℕ) :
    (Function.support fun i : ℕ =>
      (gBinom m i) • gen W (W.smul a i (W.smul b j c)) (m + (k + l - j) - i)).Finite := by
  obtain ⟨Na, hNa⟩ := W.smul_eventually_zero a (W.smul b j c)
  refine Set.Finite.subset (Set.finite_Iio Na.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  refine hi ?_
  rw [hNa i (le_trans (Int.self_le_toNat Na) (by exact_mod_cast hcon)), gen_zero_left, smul_zero]

/-- Support finiteness of the LHS family in `(j, i)` order. -/
theorem genInner_support_finite_swap (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) :
    (Function.support fun q : ℕ × ℕ =>
      (gBinom k q.1) • (gBinom m q.2) •
        gen W (W.smul a q.2 (W.smul b q.1 c)) (m + (k + l - q.1) - q.2)).Finite := by
  have h := (genInner_support_finite W a b c m k l).preimage
    (f := Prod.swap) (Function.Injective.injOn Prod.swap_injective)
  refine h.subset (fun q hq => ?_)
  rw [Function.mem_support] at hq
  rw [Set.mem_preimage, Function.mem_support, Prod.swap]
  exact hq

/-- The LHS nested finsum as a flat `ℕ × ℕ`-finsum (indices in `(j, i)` order). -/
theorem genInner_flat (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) :
    (∑ᶠ j : ℕ, (gBinom k j) •
        ∑ᶠ i : ℕ, (gBinom m i) • gen W (W.smul a i (W.smul b j c)) (m + (k + l - j) - i))
      = ∑ᶠ q : ℕ × ℕ, (gBinom k q.1) • (gBinom m q.2) •
          gen W (W.smul a q.2 (W.smul b q.1 c)) (m + (k + l - q.1) - q.2) := by
  rw [finsum_curry (fun q : ℕ × ℕ => (gBinom k q.1) • (gBinom m q.2) •
        gen W (W.smul a q.2 (W.smul b q.1 c)) (m + (k + l - q.1) - q.2))
      (genInner_support_finite_swap W a b c m k l)]
  refine finsum_congr fun j => ?_
  rw [smul_finsum' (gBinom k j) (genInner_inner_finite W a b c m k l j)]

/-- Per-`i` finiteness of the inner `p`-sum in the outer-left family. -/
theorem genOuterLeft_inner_finite (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) (i : ℕ) :
    (Function.support fun p : ℕ =>
      (gBinom (m + k - i) p) • gen W (W.smul (W.smul a i b) p c) (m + k - i + l - p)).Finite := by
  obtain ⟨Np, hNp⟩ := W.smul_eventually_zero (W.smul a i b) c
  refine Set.Finite.subset (Set.finite_Iio Np.toNat) ?_
  intro p hp
  rw [Function.mem_support] at hp
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  refine hp ?_
  rw [hNp p (le_trans (Int.self_le_toNat Np) (by exact_mod_cast hcon)), gen_zero_left, smul_zero]

/-- The outer-left nested finsum as a flat `ℕ × ℕ`-finsum. -/
theorem genOuterLeft_flat (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) :
    (∑ᶠ i : ℕ, (gBinom m i) •
        ∑ᶠ p : ℕ, (gBinom (m + k - i) p) • gen W (W.smul (W.smul a i b) p c) (m + k - i + l - p))
      = ∑ᶠ q : ℕ × ℕ, (gBinom m q.1) • (gBinom (m + k - q.1) q.2) •
          gen W (W.smul (W.smul a q.1 b) q.2 c) (m + k - q.1 + l - q.2) := by
  rw [finsum_curry (fun q : ℕ × ℕ => (gBinom m q.1) • (gBinom (m + k - q.1) q.2) •
        gen W (W.smul (W.smul a q.1 b) q.2 c) (m + k - q.1 + l - q.2))
      (genOuterLeft_support_finite W a b c m k l)]
  refine finsum_congr fun i => ?_
  rw [smul_finsum' (gBinom m i) (genOuterLeft_inner_finite W a b c m k l i)]

/-- Per-`i` finiteness of the inner `p`-sum in the outer-right family. -/
theorem genOuterRight_inner_finite (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) (i : ℕ) :
    (Function.support fun p : ℕ =>
      (gBinom k p) • gen W (W.smul b p (W.smul a i c)) (k + (m + l - i) - p)).Finite := by
  obtain ⟨Np, hNp⟩ := W.smul_eventually_zero b (W.smul a i c)
  refine Set.Finite.subset (Set.finite_Iio Np.toNat) ?_
  intro p hp
  rw [Function.mem_support] at hp
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  refine hp ?_
  rw [hNp p (le_trans (Int.self_le_toNat Np) (by exact_mod_cast hcon)), gen_zero_left, smul_zero]

/-- The outer-right nested finsum as a flat `ℕ × ℕ`-finsum. -/
theorem genOuterRight_flat (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) :
    (∑ᶠ i : ℕ, (gBinom m i) •
        ∑ᶠ p : ℕ, (gBinom k p) • gen W (W.smul b p (W.smul a i c)) (k + (m + l - i) - p))
      = ∑ᶠ q : ℕ × ℕ, (gBinom m q.1) • (gBinom k q.2) •
          gen W (W.smul b q.2 (W.smul a q.1 c)) (k + (m + l - q.1) - q.2) := by
  rw [finsum_curry (fun q : ℕ × ℕ => (gBinom m q.1) • (gBinom k q.2) •
        gen W (W.smul b q.2 (W.smul a q.1 c)) (k + (m + l - q.1) - q.2))
      (genOuterRight_support_finite W a b c m k l)]
  refine finsum_congr fun i => ?_
  rw [smul_finsum' (gBinom m i) (genOuterRight_inner_finite W a b c m k l i)]

/-! ## The per-total-degree generator identity `GenJacobiDepth`

The genuine residual VOA content: for each total OPE depth `s`, the depth-`s` graded pieces of the
three brackets (each a finite `Finset.antidiagonal s` sum of `gen`-terms sharing the common loop
degree `m+k+l-s`) agree in `V̂`.  This is the depth-graded repackaging of the master Borcherds
identity `Core.Borcherds.jacobi` (5.1.7b) at the `gen`/`Im D` level.  It is the precise hypothesis
out of which the full loop-Jacobi follows. -/

/-- **The per-total-degree generator Borcherds identity.**  For every `a b c : 𝒱`, loop degrees
`m k l : ℤ` and depth `s : ℕ`, the depth-`s` antidiagonal slices of the three brackets agree:
`Σ_{j+i=s} C(k,j)·C(m,i)·(a₍ᵢ₎(b₍ⱼ₎c))((m+k+l)-s)`
  `= Σ_{i+p=s} C(m,i)·C(m+k-i,p)·((a₍ᵢ₎b)₍ₚ₎c)((m+k+l)-s)`
    `+ Σ_{i+p=s} C(m,i)·C(k,p)·(b₍ₚ₎(a₍ᵢ₎c))((m+k+l)-s)`.
(Recorded as a precise hypothesis, the loop-bracket depth-slice of `Core.Borcherds.jacobi`; not an
axiom and not stubbed, exactly as `BracketDescends`/`VHatAntisymm`.) -/
def GenJacobiDepth (W : VertexOperatorAlgebra 𝒱) (_hD : BracketDescends W) : Prop :=
  ∀ (a b c : 𝒱) (m k l : ℤ) (s : ℕ),
    (∑ q ∈ Finset.antidiagonal s, (gBinom k q.1) • (gBinom m q.2) •
        gen W (W.smul a q.2 (W.smul b q.1 c)) (m + (k + l - q.1) - q.2))
      = (∑ q ∈ Finset.antidiagonal s, (gBinom m q.1) • (gBinom (m + k - q.1) q.2) •
            gen W (W.smul (W.smul a q.1 b) q.2 c) (m + k - q.1 + l - q.2))
        + ∑ q ∈ Finset.antidiagonal s, (gBinom m q.1) • (gBinom k q.2) •
            gen W (W.smul b q.2 (W.smul a q.1 c)) (k + (m + l - q.1) - q.2)

/-- The depth-slice family of a finitely-supported `ℕ × ℕ`-`finsum` is finitely supported in `s`:
nonzero slices force `s` below the total-degree bound of the original support. -/
theorem depthSlice_support_finite {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M)
    (hf : (Function.support f).Finite) :
    (Function.support fun s : ℕ => ∑ p ∈ Finset.antidiagonal s, f p).Finite := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ p ∈ Function.support f, p.1 + p.2 < B := by
    refine ⟨(hf.toFinset.image (fun p => p.1 + p.2)).sup id + 1, fun p hp => ?_⟩
    have : p ∈ hf.toFinset := by rw [Set.Finite.mem_toFinset]; exact hp
    have hle : p.1 + p.2 ≤ (hf.toFinset.image (fun p => p.1 + p.2)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ this)
    omega
  refine Set.Finite.subset (Set.finite_Iio B) (fun s hs => ?_)
  rw [Function.mem_support] at hs
  rw [Set.mem_Iio]
  by_contra hc
  rw [not_lt] at hc
  refine hs (Finset.sum_eq_zero fun p hp => ?_)
  rw [Finset.mem_antidiagonal] at hp
  by_contra hfp
  exact absurd (hB p hfp) (by omega)

/-- **The depth identity implies the explicit `GenLeibniz` identity.**  Regroup all three flat
`ℕ × ℕ`-finsums along total-degree antidiagonals (`finsum_prod_eq_finsum_antidiagonal`) and apply
`GenJacobiDepth` slice-by-slice (the slices add by `finsum_add_distrib`). -/
theorem GenJacobiDepth_imp_explicit (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (hJ : GenJacobiDepth W hD) :
    ∀ (a b c : 𝒱) (m k l : ℤ),
      (∑ᶠ j : ℕ, (gBinom k j) •
          ∑ᶠ i : ℕ, (gBinom m i) • gen W (W.smul a i (W.smul b j c)) (m + (k + l - j) - i))
        = (∑ᶠ i : ℕ, (gBinom m i) •
            ∑ᶠ p : ℕ, (gBinom (m + k - i) p) •
              gen W (W.smul (W.smul a i b) p c) (m + k - i + l - p))
          + ∑ᶠ i : ℕ, (gBinom m i) •
              ∑ᶠ p : ℕ, (gBinom k p) •
                gen W (W.smul b p (W.smul a i c)) (k + (m + l - i) - p) := by
  intro a b c m k l
  rw [genInner_flat W a b c m k l, genOuterLeft_flat W a b c m k l,
    genOuterRight_flat W a b c m k l,
    finsum_prod_eq_finsum_antidiagonal _ (genInner_support_finite_swap W a b c m k l),
    finsum_prod_eq_finsum_antidiagonal _ (genOuterLeft_support_finite W a b c m k l),
    finsum_prod_eq_finsum_antidiagonal _ (genOuterRight_support_finite W a b c m k l),
    ← finsum_add_distrib
      (depthSlice_support_finite _ (genOuterLeft_support_finite W a b c m k l))
      (depthSlice_support_finite _ (genOuterRight_support_finite W a b c m k l))]
  exact finsum_congr fun s => hJ a b c m k l s

/-- **The depth identity implies `GenLeibniz`** (via `GenLeibniz_iff_explicit`). -/
theorem genJacobiDepth_imp_genLeibniz (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (hJ : GenJacobiDepth W hD) : GenLeibniz W hD :=
  (GenLeibniz_iff_explicit W hD).mpr (GenJacobiDepth_imp_explicit W hD hJ)

/-- **`VHatLeibniz` from the depth-graded Borcherds slice.**  This closes the deep loop-Jacobi crux
modulo the single precise residual `GenJacobiDepth` (the depth-graded slice of
`Core.Borcherds.jacobi`): given it, the full quotient Leibniz identity — hence the `LieRing (V̂)`
Jacobi input — holds.  Everything between `GenJacobiDepth` and `VHatLeibniz` is unconditional and
axiom-free. -/
theorem VHatLeibniz_of_genJacobiDepth (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (hJ : GenJacobiDepth W hD) : VHatLeibniz W hD :=
  VHatLeibniz_of_gen W hD (genJacobiDepth_imp_genLeibniz W hD hJ)

end VHat

end VOA
