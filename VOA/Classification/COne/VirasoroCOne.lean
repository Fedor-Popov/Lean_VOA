/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.Inputs
import VOA.Examples.VirasoroScreeningKacRoots
import VOA.Examples.VirasoroVermaQuotientDimensions
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher

/-!
# I1: the `c = 1` Virasoro input `IVirasoro`, as a staged reduction

`IVirasoro` (`Inputs.lean`) says: for every VOA `V` with `c = 1` and `vacuum ≠ 0`,
`eulerSeries · vacuumSeries V = etaVirasoroSum A` for some `A : ℕ → ℕ` with `A 0 = 1`.
This file proves it from two precisely named facts of Virasoro representation theory, and proves
everything else unconditionally.

## What is proved here (no hypotheses)

* `eulerSeries_mul_partitionSeries`: Euler's identity `∏(1 - qⁿ) · Σ p(n) qⁿ = 1`, where `p(n)`
  is the cardinality of the library's actual Verma PBW index set `VermaPartitions n`
  (via Mathlib's `Nat.Partition.hasProd_genFun`).
* `kac_determinant_eval`: the unconditional Kac determinant of the actual Verma Gram matrix at
  every `t ≠ 0` (this composition is spelled out here
  because the library otherwise states only the conditional forms).
* `vermaGramMatrix_one_det_ne_zero`: at `c = 1` and an integer weight `h` that is **not** a perfect
  square, every Verma level is non-degenerate (`c(1) = 1`, Kac weights `(r - s)²/4`).
* `eulerSeries_mul_simpleCharSeries_of_not_sq`: hence `η · ch L(1, h) = q^h` for non-square `h`
  (Verma = irreducible), the non-degenerate half of GR (3.4), **unconditionally**.
* `coeff_eulerSeries_mul_simpleCharSeries_sq_of_lt`: for `h = μ²` the degenerate formula
  `η · ch L(1, μ²) = q^{μ²} - q^{(μ+1)²}` holds coefficientwise below `q^{(μ+1)²}`
  (all Gram levels `< 2μ + 1` are non-degenerate).
* `iVirasoro_of_composition`: the purely formal step — `IVirasoro` follows from
  `VirLocalCompositionSeries` and `VirC1DegenerateCharacters`. `A 0 = 1` is derived from VOA4
  (`𝒱₀ = ℂ𝟙`) and `vacuum ≠ 0`.

## What remains (named, open)

* `VirLocalCompositionSeries` — local composition series / Jordan–Hölder multiplicities for
  positive-energy Virasoro modules with finite-dimensional integer weight spaces, at every `c`
  (Kac–Raina, *Bombay lectures*, Lecture 9; Deodhar–Gabber–Kac 1982, Prop. 3.2). Stated for an
  arbitrary graded module with Virasoro operators, not for VOAs.
* `VirC1DegenerateCharacters` — Feigin–Fuchs (1984) at `c = 1`, `h = μ²`: the maximal proper
  submodule of `M(1, μ²)` has the character of `M(1, (μ+1)²)`, i.e.
  `dim L(1, μ²)_n = p(n) - p(n - 2μ - 1)`. (Upper bound needs the level-`2μ+1` singular vector
  at the real parameter `t = 1`, which the screening construction only gives for `Im t ≠ 0`;
  the lower bound needs a Jantzen-filtration / embedding-diagram argument.)

`L(c, h)` is always the library's actual irreducible quotient `VermaSimple c h` (Verma module
modulo the contravariant radical); its level-`n` dimension is `finrank (vermaSimpleLevel c h n)`.
-/

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

noncomputable section

namespace VOA.Classification.COne

open VOA.InverseDS.VirasoroVerma VOA.VirasoroScreening
-- `VermaPartitions n` has no `DecidableEq` instance; the library's Gram/Kac files use the same.
open scoped Classical

universe u

/-! ## Euler's identity for the actual Verma partition count -/


/-- `Σ_n p(n) qⁿ`, `p(n) = #VermaPartitions n` (the Verma character without `q^h`). -/
noncomputable def partitionSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Fintype.card (VermaPartitions n) : ℤ)

/-- `VermaPartitions n` (creation multisets of energy `n`) is in bijection with `Nat.Partition n`
(shift every mode index by one). -/
theorem card_vermaPartitions_eq (n : ℕ) :
    Fintype.card (VermaPartitions n) = Fintype.card n.Partition := by
  rw [← vermaMultisetPartitions_card]
  refine Fintype.card_congr
    { toFun := fun s => ⟨s.val.map (· + 1), fun {i} hi => by
          obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hi; omega,
          by simpa [vermaMultisetEnergy] using s.property⟩
      invFun := fun p => ⟨p.parts.map (· - 1), by
          rw [vermaMultisetEnergy, Multiset.map_map]
          refine Eq.trans ?_ p.parts_sum
          congr 1
          conv_rhs => rw [← Multiset.map_id p.parts]
          refine Multiset.map_congr rfl fun i hi => ?_
          have := p.parts_pos hi
          simp only [Function.comp_apply, id]; omega⟩
      left_inv := fun s => by
          apply Subtype.ext
          simp [Multiset.map_map]
      right_inv := fun p => by
          apply Nat.Partition.ext
          simp only [Multiset.map_map]
          conv_rhs => rw [← Multiset.map_id p.parts]
          refine Multiset.map_congr rfl fun i hi => ?_
          have := p.parts_pos hi
          simp only [Function.comp_apply, id]; omega }

/-- The partition series as Mathlib's infinite product of geometric series. -/
theorem partitionSeries_eq_tprod :
    partitionSeries = ∏' i, ∑' j : ℕ, (X : PowerSeries ℤ) ^ ((i + 1) * j) := by
  have h := Nat.Partition.powerSeriesMk_card_restricted_eq_tprod ℤ (fun _ => True)
  simp only [if_true] at h
  rw [← h, partitionSeries]
  congr 1; funext n
  rw [card_vermaPartitions_eq]
  simp [Nat.Partition.restricted]

/-- `∏'(1 - X^{i+1}) · Σ p(n) Xⁿ = 1`. -/
theorem tprod_euler_mul_partitionSeries :
    (∏' i, (1 - (X : PowerSeries ℤ) ^ (i + 1))) * partitionSeries = 1 := by
  rw [partitionSeries_eq_tprod, mul_comm,
    ← (Nat.Partition.multipliable_powerSeriesMk_card_restricted ℤ (fun _ => True)
      |>.congr ?_).tprod_mul
      (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ)]
  · simp_rw [pow_mul]
    conv in fun b ↦ _ =>
      ext b
      rw [PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)]
    exact tprod_one
  · intro i; simp


/-- The `N`-th coefficient of `∏_{i<M} (1 - X^{i+1})` does not depend on `M ≥ N`. -/
theorem coeff_prod_range_one_sub_X_pow_stable (N : ℕ) :
    ∀ M, N ≤ M → coeff N (∏ i ∈ range M, (1 - (X : PowerSeries ℤ) ^ (i + 1))) =
      coeff N (∏ i ∈ range N, (1 - (X : PowerSeries ℤ) ^ (i + 1))) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    rw [prod_range_succ, mul_sub, mul_one, map_sub, ih, coeff_mul_X_pow', if_neg (by omega),
      sub_zero]

/-- `eulerSeries` is the infinite product `∏'(1 - X^{i+1})` (pi topology on `ℤ⟦X⟧`). -/
theorem eulerSeries_eq_tprod :
    eulerSeries = ∏' i, (1 - (X : PowerSeries ℤ) ^ (i + 1)) := by
  ext N
  have hP := (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd
  rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at hP
  have hN := hP N
  rw [nhds_discrete, Filter.tendsto_pure] at hN
  have hN' : ∀ᶠ x in (Filter.atTop : Filter (Finset ℕ)),
      coeff N (∏ b ∈ x, (1 - (X : PowerSeries ℤ) ^ (b + 1))) =
      coeff N (∏' b : ℕ, (1 - (X : PowerSeries ℤ) ^ (b + 1))) := by
    simpa using hN
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.mp hN'
  set M := N + s0.sup id + 1
  have hsub : s0 ≤ range M := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    simp only [id] at this
    rw [mem_range]; omega
  rw [← hs0 _ hsub, coeff_prod_range_one_sub_X_pow_stable N M (by omega), eulerSeries, coeff_mk]

/-- **Euler's identity** `∏(1 - qⁿ) · Σ p(n) qⁿ = 1`, with `p(n)` the number of actual Verma
PBW partition indices at level `n`. -/
theorem eulerSeries_mul_partitionSeries : eulerSeries * partitionSeries = 1 := by
  rw [eulerSeries_eq_tprod, tprod_euler_mul_partitionSeries]



/-! ## The Kac determinant at `c = 1` -/

/-- The Kac determinant formula evaluated at `h`, unconditionally for every `t ≠ 0`. -/
theorem kac_determinant_eval (t : ℂ) (ht : t ≠ 0) (h : ℂ) (n : ℕ) :
    (vermaGramMatrix (vermaBSACharge t) h n).det =
      (∏ w : VermaPartitions n, vermaDiagonalContraction w.val) *
        (kacWeightProduct t n).eval h := by
  rw [← vermaWeightDeterminant_eval,
    verma_kac_all_of_nonreal_singular n
      (fun z hz r s hr hs _ => screening_nonreal_kac_singular z hz r s hr hs) t ht n le_rfl,
    Polynomial.eval_mul, Polynomial.eval_C]

/-- `c(t) = 13 - 6t - 6/t` equals `1` at `t = 1`. -/
theorem vermaBSACharge_one : vermaBSACharge 1 = 1 := by
  rw [vermaBSACharge]; norm_num

/-- At `c = 1` (`t = 1`) the Kac weights are `(r - s)²/4`; an integer weight of that form is a
perfect square. -/
theorem isDegenerateWeight_of_eq_fusionKacWeight_one {h u v : ℕ}
    (he : (h : ℂ) = fusionKacWeight (u : ℂ) (v : ℂ) 1) : IsDegenerateWeight h := by
  rw [fusionKacWeight] at he
  have h4 : ((4 * h : ℤ) : ℂ) = ((((u : ℤ) - v) ^ 2 : ℤ) : ℂ) := by
    push_cast; rw [he]; ring
  have h4' : (4 * h : ℤ) = ((u : ℤ) - v) ^ 2 := by exact_mod_cast h4
  set k := ((u : ℤ) - v).natAbs
  have hk : k ^ 2 = 4 * h := by
    have : ((k ^ 2 : ℕ) : ℤ) = ((4 * h : ℕ) : ℤ) := by
      push_cast; rw [Int.natAbs_sq]; exact h4'.symm
    exact_mod_cast this
  obtain ⟨μ, -, rfl⟩ := exists_nat_of_half_sq_eq (k := k) (h := h) (by
    have : ((k : ℚ)) ^ 2 = 4 * h := by exact_mod_cast hk
    rw [div_pow, this]; ring)
  exact isDegenerateWeight_sq μ

/-- **Non-degenerate `c = 1` Gram levels.** For an integer weight `h` that is not a perfect
square, every level of the `c = 1` Verma module has nonzero Gram determinant. -/
theorem vermaGramMatrix_one_det_ne_zero {h : ℕ} (hh : ¬ IsDegenerateWeight h) (n : ℕ) :
    (vermaGramMatrix 1 (h : ℂ) n).det ≠ 0 := by
  rw [← vermaBSACharge_one, kac_determinant_eval 1 one_ne_zero]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun w _ => vermaDiagonalContraction_ne_zero _) ?_
  rw [kacWeightProduct, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  rw [Polynomial.eval_pow]
  refine pow_ne_zero _ ?_
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
  intro he
  apply hh
  exact isDegenerateWeight_of_eq_fusionKacWeight_one (u := i.1.val + 1) (v := i.2.val + 1)
    (by exact_mod_cast he)

/-- At `c = 1`, non-square integer `h`: `dim L(1, h)_n = p(n)`. -/
theorem vermaSimpleLevel_one_finrank_of_not_sq {h : ℕ} (hh : ¬ IsDegenerateWeight h) (n : ℕ) :
    Module.finrank ℂ (vermaSimpleLevel 1 (h : ℂ) n) = Fintype.card (VermaPartitions n) :=
  vermaSimpleLevel_finrank_of_det_ne_zero 1 h n (vermaGramMatrix_one_det_ne_zero hh n)


/-- At `c = 1`, the Kac weight `(u - v)²/4` (`u, v ≥ 1`) equals `μ²` only at level
`u v ≥ 2μ + 1`. -/
theorem le_mul_of_eq_fusionKacWeight_one {μ u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (he : ((μ ^ 2 : ℕ) : ℂ) = fusionKacWeight (u : ℂ) (v : ℂ) 1) :
    2 * μ + 1 ≤ u * v := by
  rw [fusionKacWeight] at he
  have h4 : ((4 * μ ^ 2 : ℤ) : ℂ) = ((((u : ℤ) - v) ^ 2 : ℤ) : ℂ) := by
    push_cast at he ⊢; rw [he]; ring
  have h4' : (4 * μ ^ 2 : ℤ) = ((u : ℤ) - v) ^ 2 := by exact_mod_cast h4
  have hf : ((u : ℤ) - v - 2 * μ) * ((u : ℤ) - v + 2 * μ) = 0 := by linear_combination -h4'
  have hu' : (1 : ℤ) ≤ u := by exact_mod_cast hu
  have hv' : (1 : ℤ) ≤ v := by exact_mod_cast hv
  have hμ : (0 : ℤ) ≤ μ := by positivity
  suffices (2 * μ + 1 : ℤ) ≤ (u : ℤ) * v by exact_mod_cast this
  rcases mul_eq_zero.mp hf with h | h
  · have : (u : ℤ) = v + 2 * μ := by linarith
    rw [this]; nlinarith
  · have : (v : ℤ) = u + 2 * μ := by linarith
    rw [this]; nlinarith

/-- At `c = 1`, `h = μ²`: the Gram levels `n ≤ 2μ` are non-degenerate (the first Kac zero is at
level `2μ + 1`). -/
theorem vermaGramMatrix_one_sq_det_ne_zero (μ : ℕ) {n : ℕ} (hn : n ≤ 2 * μ) :
    (vermaGramMatrix 1 ((μ ^ 2 : ℕ) : ℂ) n).det ≠ 0 := by
  rw [← vermaBSACharge_one, kac_determinant_eval 1 one_ne_zero]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun w _ => vermaDiagonalContraction_ne_zero _) ?_
  rw [kacWeightProduct, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [Polynomial.eval_pow]
  refine pow_ne_zero _ ?_
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
  intro he
  have hle : (i.1.val + 1) * (i.2.val + 1) ≤ n := (Finset.mem_filter.mp hi).2
  have := le_mul_of_eq_fusionKacWeight_one (μ := μ) (u := i.1.val + 1) (v := i.2.val + 1)
    (by omega) (by omega) (by exact_mod_cast he)
  omega

/-! ## Characters of the irreducible `c = 1` Virasoro modules -/

/-- The character of the actual irreducible Virasoro module `L(c, h)` (`h ∈ ℕ`), without the
`q^{-c/24}`: `Σ_N dim L(c,h)_{N} q^N`, where weight `N ≥ h` is Verma level `N - h`. -/
def simpleCharSeries (c : ℂ) (h : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun N =>
    if h ≤ N then (Module.finrank ℂ (vermaSimpleLevel c (h : ℂ) (N - h)) : ℤ) else 0

theorem coeff_simpleCharSeries_of_lt {c : ℂ} {h N : ℕ} (hN : N < h) :
    coeff N (simpleCharSeries c h) = 0 := by
  rw [simpleCharSeries, coeff_mk, if_neg (by omega)]

/-- For non-square `h`, `ch L(1, h) = q^h · Σ p(n) qⁿ` (the Verma character). -/
theorem simpleCharSeries_one_of_not_sq {h : ℕ} (hh : ¬ IsDegenerateWeight h) :
    simpleCharSeries 1 h = X ^ h * partitionSeries := by
  ext N
  rw [coeff_X_pow_mul', simpleCharSeries, coeff_mk]
  split_ifs
  · rw [partitionSeries, coeff_mk, vermaSimpleLevel_one_finrank_of_not_sq hh]
  · rfl

/-- **GR (3.4), non-degenerate case, unconditional.** `η · ch L(1, h) = q^h` for every integer
`h ≥ 0` that is not a perfect square. -/
theorem eulerSeries_mul_simpleCharSeries_of_not_sq {h : ℕ} (hh : ¬ IsDegenerateWeight h) :
    eulerSeries * simpleCharSeries 1 h = etaVirasoroChar h := by
  rw [simpleCharSeries_one_of_not_sq hh, etaVirasoroChar_of_not_sq hh, mul_left_comm,
    eulerSeries_mul_partitionSeries, mul_one]

/-- The `N`-th coefficient of `f * g` only sees the coefficients of `g` of index `≤ N`. -/
theorem coeff_mul_congr_right (f : PowerSeries ℤ) {g g' : PowerSeries ℤ} {N : ℕ}
    (hg : ∀ b ≤ N, coeff b g = coeff b g') : coeff N (f * g) = coeff N (f * g') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hg p.2 (by have := Finset.antidiagonal.snd_le hp; omega)]

/-- **GR (3.4), degenerate case, below the first singular level.** For `h = μ²`,
`η · ch L(1, μ²)` agrees with `q^{μ²} - q^{(μ+1)²}` in every coefficient below `(μ+1)²`. -/
theorem coeff_eulerSeries_mul_simpleCharSeries_sq_of_lt (μ : ℕ) {N : ℕ}
    (hN : N < (μ + 1) ^ 2) :
    coeff N (eulerSeries * simpleCharSeries 1 (μ ^ 2)) = coeff N (etaVirasoroChar (μ ^ 2)) := by
  have hcongr : coeff N (eulerSeries * simpleCharSeries 1 (μ ^ 2)) =
      coeff N (eulerSeries * (X ^ (μ ^ 2) * partitionSeries)) := by
    refine coeff_mul_congr_right _ fun b hb => ?_
    rw [coeff_X_pow_mul', simpleCharSeries, coeff_mk]
    split_ifs with h1
    · rw [partitionSeries, coeff_mk]
      have hlev : b - μ ^ 2 ≤ 2 * μ := by
        have : (μ + 1) ^ 2 = μ ^ 2 + 2 * μ + 1 := by ring
        omega
      have := vermaSimpleLevel_finrank_of_det_ne_zero 1 _ (b - μ ^ 2)
        (vermaGramMatrix_one_sq_det_ne_zero μ hlev)
      push_cast at this ⊢
      rw [this]
    · rfl
  rw [hcongr, mul_left_comm, eulerSeries_mul_partitionSeries, mul_one, etaVirasoroChar_sq,
    map_sub, coeff_X_pow (n := (μ + 1) ^ 2), if_neg (by omega), sub_zero]

/-! ## The named open inputs -/

/-- **Feigin–Fuchs at `c = 1`, degenerate weights (open).** For `h = μ²`,
`η · ch L(1, μ²) = q^{μ²} - q^{(μ+1)²}`, i.e. `dim L(1, μ²)_n = p(n) - p(n - 2μ - 1)`: the maximal
proper submodule of the Verma module `M(1, μ²)` is generated by the singular vector at level
`2μ + 1` and is itself a Verma module `M(1, (μ+1)²)`.

*Source.* B. Feigin and D. Fuchs, *Verma modules over the Virasoro algebra* (LNM 1060, 1984);
Kac–Raina, *Bombay lectures*, and Iohara–Koga, *Representation theory of the Virasoro algebra*,
Thm 5.16 (case III₋⁰ / the `c = 1` chain `M(μ²) ⊃ M((μ+1)²) ⊃ ⋯`).

*Already proved here.* The coefficients below `q^{(μ+1)²}`
(`coeff_eulerSeries_mul_simpleCharSeries_sq_of_lt`); the non-square weights in full
(`eulerSeries_mul_simpleCharSeries_of_not_sq`). -/
def VirC1DegenerateCharacters : Prop :=
  ∀ μ : ℕ, eulerSeries * simpleCharSeries 1 (μ ^ 2) = etaVirasoroChar (μ ^ 2)

/-- Under `VirC1DegenerateCharacters`, GR (3.4) holds for every integer weight. -/
theorem eulerSeries_mul_simpleCharSeries (hdeg : VirC1DegenerateCharacters) (h : ℕ) :
    eulerSeries * simpleCharSeries 1 h = etaVirasoroChar h := by
  by_cases hh : IsDegenerateWeight h
  · rw [← hh]; exact hdeg _
  · exact eulerSeries_mul_simpleCharSeries_of_not_sq hh

/-- **Local composition series / Jordan–Hölder multiplicities (open).** Let `M = ⊕_{n ∈ ℤ} M_n`
carry operators `L_m` satisfying the Virasoro relations with central charge `c`, with `L₀ = n` on
`M_n`, `L_m M_n ⊆ M_{n-m}`, every `M_n` finite-dimensional and `M_n = 0` for `n < 0`. Then there
are multiplicities `A_h = [M : L(c, h)] ∈ ℕ` with `dim M_N = Σ_{h ≤ N} A_h dim L(c, h)_{N-h}`.

*Source.* Deodhar–Gabber–Kac, *Structure of some categories of representations of
infinite-dimensional Lie algebras* (Adv. Math. 45, 1982), Prop. 3.2 (local composition series in
category `O`), as specialised to Virasoro in Kac–Raina, *Bombay lectures*, Lecture 9;
Iohara–Koga, Prop. 2.9.

*Not over-strong.* Any `c`; no rationality, unitarity or semisimplicity. -/
def VirLocalCompositionSeries : Prop :=
  ∀ (c : ℂ) (M : Type u) [AddCommGroup M] [Module ℂ M] (grading : ℤ → Submodule ℂ M)
    (L : ℤ → Module.End ℂ M),
    DirectSum.IsInternal grading →
    (∀ n, FiniteDimensional ℂ (grading n)) →
    (∀ n : ℤ, n < 0 → grading n = ⊥) →
    (∀ (n : ℤ) (v : M), v ∈ grading n → L 0 v = (n : ℂ) • v) →
    (∀ (m n : ℤ) (v : M), v ∈ grading n → L m v ∈ grading (n - m)) →
    (∀ m n : ℤ, ⁅L m, L n⁆ = ((m : ℂ) - n) • L (m + n)
      + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * c) • (1 : Module.End ℂ M) else 0)) →
    ∃ A : ℕ → ℕ, ∀ N : ℕ, Module.finrank ℂ (grading N) =
      ∑ h ∈ range (N + 1), A h * Module.finrank ℂ (vermaSimpleLevel c (h : ℂ) (N - h))

/-! ## The formal step -/

/-- `L_m` maps `V_n` into `V_{n-m}`. -/
theorem VertexOperatorAlgebra.L_mem_grading {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (V : VertexOperatorAlgebra 𝒱) (m n : ℤ) (v : 𝒱) (hv : v ∈ V.grading n) :
    V.L m v ∈ V.grading (n - m) := by
  have := V.grading_mode V.conformalVector V.conformal_mem v hv (m + 1)
  rw [show (2 : ℤ) + n - (m + 1) - 1 = n - m by ring] at this
  exact this

/-- **The formal step of I1.** If a VOA's graded dimension is
`dim V_N = Σ_{h ≤ N} A_h dim L(1, h)_{N-h}` and `η · ch L(1, h) = etaVirasoroChar h` for all `h`,
then `eulerSeries · vacuumSeries V = etaVirasoroSum A`. -/
theorem eulerSeries_mul_vacuumSeries_of_multiplicities {𝒱 : Type u} [AddCommGroup 𝒱]
    [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (A : ℕ → ℕ)
    (hA : ∀ N : ℕ, Module.finrank ℂ (V.grading N) =
      ∑ h ∈ range (N + 1), A h * Module.finrank ℂ (vermaSimpleLevel 1 (h : ℂ) (N - h)))
    (hchar : ∀ h, eulerSeries * simpleCharSeries 1 h = etaVirasoroChar h) :
    eulerSeries * vacuumSeries V = etaVirasoroSum A := by
  ext N
  set T : PowerSeries ℤ :=
    ∑ h ∈ range (N + 1), PowerSeries.C (A h : ℤ) * simpleCharSeries 1 h
  have hT : coeff N (eulerSeries * vacuumSeries V) = coeff N (eulerSeries * T) := by
    refine coeff_mul_congr_right _ fun b hb => ?_
    rw [vacuumSeries, coeff_mk, hA b, map_sum]
    simp only [PowerSeries.coeff_C_mul, simpleCharSeries, coeff_mk, mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hf : (range (N + 1)).filter (fun h => h ≤ b) = range (b + 1) := by
      ext h; simp only [mem_filter, mem_range]; omega
    rw [hf]
    push_cast
    rfl
  rw [hT, mul_sum, map_sum, etaVirasoroSum, coeff_mk]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_left_comm, PowerSeries.coeff_C_mul, hchar]

/-- **I1, staged.** `IVirasoro` follows from the local composition series theorem
(`VirLocalCompositionSeries`) and the Feigin–Fuchs `c = 1` degenerate characters
(`VirC1DegenerateCharacters`). Everything else — Euler's identity, the non-degenerate `c = 1`
characters via the unconditional Kac determinant, `A 0 = 1` from VOA4 — is proved. -/
theorem iVirasoro_of_composition (hJH : VirLocalCompositionSeries.{u})
    (hdeg : VirC1DegenerateCharacters) : IVirasoro.{u} := by
  intro 𝒱 _ _ V hvac hc
  obtain ⟨A, hA⟩ := hJH V.centralCharge 𝒱 V.grading V.L V.isInternal V.finrank V.positivity
    (fun n v hv => V.L_zero_grading v hv) (VertexOperatorAlgebra.L_mem_grading V) V.L_virasoro
  rw [hc] at hA
  refine ⟨A, ?_, eulerSeries_mul_vacuumSeries_of_multiplicities V A hA
    (eulerSeries_mul_simpleCharSeries hdeg)⟩
  have h0 := hA 0
  rw [Nat.cast_zero, V.vacuum_grade, finrank_span_singleton hvac] at h0
  simpa [vermaSimpleLevel_zero_finrank] using h0.symm

end VOA.Classification.COne
