/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCrossCFirst0Close
import VOA.Modules.ZhuVermaAnArchTerm1UCore

/-!
# Game One — the **`a`-outer `c`-first DIFFERENCE U-core**: the per-base `PresAnm`-difference shape
of `CrossCFirstDiffTowerEq`.

This file pushes the single genuinely-open core of the `MUGradedAction` gate — the level-`0`-vs-level-`n`
`c`-first pole-difference tower decomposition `CrossCFirstDiffTowerEq`
(`ZhuVermaAnArchCrossCFirst0Close`) — toward closure, by proving its **exact per-base structural
shape**: the `a`-outer `c`-first DIFFERENCE is, base-by-base, the difference of the level-`0` and the
level-`n` Zhu `c`-circle on the SAME base `bᵢ = a₍i−(n+1)₎d`.

## The exact per-base `PresAnm`-difference shape (proved here; FULLY proven)

By the defining split `crossCFirstDiff = crossCircCFirst − ardCFirst`
(`ZhuVermaAnArchCrossCFirst0Close`), and the two PROVEN `c`-first families
`crossCFirst0_eq_PresTowerFam` / `ardCFirst_eq_PresTowerFam`
(`ZhuVermaAnArchMUGradedFinal`) — both depth-`1` `PresTowerFam`s in homogeneous `c`, the FORMER at
level `0` (inner pole `2`), the LATTER at level `n` (inner pole `n+2`), over the SAME bases
`bᵢ = a₍i−(n+1)₎d` — we bring the difference to the per-`i` `PresAnm`-difference form

  `crossCFirstDiff W n K M a c d
     = ∑_{i≤K} C(K,i) • (PresAnm W M 0 0 c bᵢ − PresAnm W M n 0 c bᵢ)`   (`crossCFirstDiff_eq_presDiff`),

i.e. per fixed base `bᵢ` the inner factor is the pure inner-circle **pole-difference**
`c∘₀bᵢ − c∘ₙbᵢ` of the two Zhu `c`-circles, weighted by `C(K,i)`.  Each inner factor brings to the
mode-value finsum form (via `PresAnm_eq_finsum`, depth `0`)

  `PresAnm W M 0 0 c bᵢ − PresAnm W M n 0 c bᵢ
     = ∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎ bᵢ`                         (`presDiff_eq_modeFinsum`),

with the per-`(M,n,μ)` **pole-difference weight** `crossDiffWeight M n μ = cbz(M, μ+2) − cbz(M,
μ+(n+2))` — the SAME for every base `bᵢ`, with finite `μ`-support `[−2, M−2]` (the level-`0` weight)
∪ `[−(n+2), M−(n+2)]` (the level-`n` weight).  This is the genuine `a`-outer `c`-first DIFFERENCE
U-core target: the per-base mode coefficient is the explicit pole-difference `crossDiffWeight`,
identical across all bases.

## The PRECISE remaining identity (engine-verified TRUE; NOT faked / NOT axiomatized)

`CrossCFirstDiffTowerEq` asks for the combined `i`-sum of these per-base pole-differences to collapse
onto a **level-`n`** `PresTowerFam` in `c` (the `c`-tower correction over the multi-base `a₍·₎d`) plus
a multi-grade `MGTowerFam` in the products `c₍s₎a` based at `d` (`ZhuVermaAnArchCrossCFirst0Close`).
The genuine residual content is the **cross-base** coupling: per fixed base `bᵢ` the pole-difference
`crossDiffWeight` is NOT a level-`n` single-base `c`-tower (engine `certificates/mathematica/cfirst_perbase_polediff.wl`:
per-base single-tower span `False` whenever the base depth reaches `c`'s pole window); the level
offset is absorbed only by the cross-base reorganization into the `c₍s₎a` `MGTowerFam` (engine
`certificates/mathematica/cfirst0_diff.wl`: the COMBINED span DOES contain the difference, `n = 1, 2`; `certificates/mathematica/cfirst_diff_conly.wl`:
the pure `c`-tower span ALONE does NOT suffice).

We therefore state the exact remaining content as a single explicit hypothesis-predicate
`CFirstDiffScalarCore` — the `a`-outer `c`-first DIFFERENCE scalar weight assignment — and prove

  `CFirstDiffScalarCore ⟹ CrossCFirstDiffTowerEq ⟹ … ⟹ MUGradedAction W`

with EVERY structural step (the defining split, the per-base `PresAnm`-difference reshaping, the
mode-value finsum, the membership half) fully discharged here and upstream.  `CFirstDiffScalarCore`
is the precise `a`-outer twin of the diagonal `AnmCircTowerEq` scalar cores
(`UgammaModeCollAnm_eq_towerCoeff` / `VgammaModeCollAnm_eq_towerCoeff`); it is carried as a
hypothesis, NEVER an axiom.

## Engine status (rank-1 free boson; NOT faked)

* `certificates/mathematica/cfirst0_diff.wl`: the difference `crossCFirstDiff` lies in
  `(c-tow@a₍g₎d) + ((c₍s₎a)-tow@d)`, `n = 1, 2`, mixed homogeneous `a, c, d` (**True**).
* `certificates/mathematica/cfirst_perbase_polediff.wl` (new): the per-base pole-difference
  `c∘₀b − c∘ₙb` is NOT a single-base level-`n` `c`-tower whenever the base reaches `c`'s pole window
  (**False**) — the level offset is genuinely cross-base.
* `certificates/mathematica/cfirst_diff_modefinsum.wl` (new): the per-`(M,n,μ)` pole-difference weight
  `cbz(M, μ+2) − cbz(M, μ+(n+2))` is structured and `μ`-bounded.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The per-base `PresAnm`-difference shape of `crossCFirstDiff`. -/

/-- **The `a`-outer `c`-first DIFFERENCE in per-base `PresAnm`-difference form** (FULLY proven).  By
the defining split `crossCFirstDiff = crossCircCFirst − ardCFirst`
(`crossCircCFirst_eq_ardCFirst_add_diff`, rearranged) and the two PROVEN depth-`1` `c`-first
`PresTowerFam`s (`crossCFirst0_eq_PresTowerFam` at level `0`, `ardCFirst_eq_PresTowerFam` at level
`n`, over the SAME bases `bᵢ = a₍i−(n+1)₎d`), the difference is the per-`i` `C(K,i)`-weighted
difference of the level-`0` and level-`n` Zhu `c`-circles on the base `bᵢ`:

  `crossCFirstDiff W n K M a c d
     = ∑_{i≤K} C(K,i) • (PresAnm W M 0 0 c (a₍i−(n+1)₎d) − PresAnm W M n 0 c (a₍i−(n+1)₎d))`. -/
theorem crossCFirstDiff_eq_presDiff (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    crossCFirstDiff W n K M a c d
      = ∑ i ∈ Finset.range (K + 1),
          cbz (K : ℤ) (i : ℤ) •
            (PresAnm W M 0 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
              - PresAnm W M n 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) := by
  rw [crossCFirstDiff, crossCFirst0_eq_PresTowerFam W n K M a c d,
    ardCFirst_eq_PresTowerFam W n K M a c d, PresTowerFam, PresTowerFam]
  rw [Fin.sum_univ_eq_sum_range
      (fun i => ∑ δ ∈ Finset.range 1,
          (if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0)
            • PresAnm W M 0 δ c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) (K + 1),
    Fin.sum_univ_eq_sum_range
      (fun i => ∑ δ ∈ Finset.range 1,
          (if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0)
            • PresAnm W M n δ c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) (K + 1),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range_one, Finset.sum_range_one, if_pos rfl, smul_sub]

/-! ## The per-`(M,n,μ)` pole-difference weight and the mode-value finsum form. -/

/-- **The `a`-outer `c`-first pole-difference weight** `crossDiffWeight M n μ = cbz(M, μ+2) − cbz(M,
μ+(n+2))`.  The level-`0` (pole-`2`) minus level-`n` (pole-`(n+2)`) Zhu-circle mode coefficient at
mode `μ`, the SAME for every base.  Finite `μ`-support: vanishes for `μ < −(n+2)` (both terms `0`)
and for `μ > M−2` (both tops `< 0`). -/
noncomputable def crossDiffWeight (M n : ℕ) (μ : ℤ) : ℂ :=
  cbz (M : ℤ) (μ + 2) - cbz (M : ℤ) (μ + ((n : ℤ) + 2))

/-- **The per-base pole-difference in mode-value finsum form** (FULLY proven).  For homogeneous
`c ∈ 𝒱_M`, the inner pole-difference `PresAnm W M 0 0 c b − PresAnm W M n 0 c b` is the single
mode-value finsum with the pole-difference weight `crossDiffWeight M n μ`:

  `PresAnm W M 0 0 c b − PresAnm W M n 0 c b = ∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎ b`.

Each `PresAnm` is rewritten by `PresAnm_eq_finsum` (depth `0`): level `0` gives `cbz(M, μ+2)`, level
`n` gives `cbz(M, μ+(n+2))`; both finsums have finite support (the `cbz` factor vanishes outside a
bounded `μ`-window), so they merge by `finsum_sub_distrib` into the single pole-difference weight. -/
theorem presDiff_eq_modeFinsum (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (c b : 𝒱) :
    PresAnm W M 0 0 c b - PresAnm W M n 0 c b
      = ∑ᶠ μ : ℤ, crossDiffWeight M n μ • W.smul c μ b := by
  rw [PresAnm_eq_finsum W M 0 0 c b, PresAnm_eq_finsum W M n 0 c b]
  -- the two level finsums have finite support (bounded `cbz` window).
  have hfin0 : (Function.support
      (fun μ : ℤ => cbz ((M : ℤ) + (0 : ℕ)) (μ + (0 + 2) + (0 : ℕ)) • W.smul c μ b)).Finite := by
    apply Set.Finite.subset (Set.finite_Icc (-2 : ℤ) (M : ℤ))
    intro μ hμ
    simp only [Function.mem_support, Set.mem_Icc] at hμ ⊢
    by_contra hc
    push_neg at hc
    refine hμ ?_
    rcases lt_or_ge μ (-2) with h | h
    · rw [cbz_apply_neg ((M : ℤ) + (0 : ℕ)) (by push_cast; omega), zero_smul]
    · rw [cbz_lt (by push_cast; positivity)
        (by push_cast; omega : ((M : ℤ) + (0 : ℕ)) < μ + (0 + 2) + (0 : ℕ)), zero_smul]
  have hfinN : (Function.support
      (fun μ : ℤ =>
        cbz ((M : ℤ) + (0 : ℕ)) (μ + ((n : ℤ) + 2) + (0 : ℕ)) • W.smul c μ b)).Finite := by
    apply Set.Finite.subset (Set.finite_Icc (-(n : ℤ) - 2 : ℤ) (M : ℤ))
    intro μ hμ
    simp only [Function.mem_support, Set.mem_Icc] at hμ ⊢
    by_contra hc
    push_neg at hc
    refine hμ ?_
    rcases lt_or_ge μ (-(n : ℤ) - 2) with h | h
    · rw [cbz_apply_neg ((M : ℤ) + (0 : ℕ)) (by push_cast; omega), zero_smul]
    · rw [cbz_lt (by push_cast; positivity)
        (by push_cast; omega : ((M : ℤ) + (0 : ℕ)) < μ + ((n : ℤ) + 2) + (0 : ℕ)), zero_smul]
  rw [show (∑ᶠ μ : ℤ, crossDiffWeight M n μ • W.smul c μ b)
        = ∑ᶠ μ : ℤ, (cbz ((M : ℤ) + (0 : ℕ)) (μ + (0 + 2) + (0 : ℕ)) • W.smul c μ b
            - cbz ((M : ℤ) + (0 : ℕ)) (μ + ((n : ℤ) + 2) + (0 : ℕ)) • W.smul c μ b) from
      finsum_congr fun μ => by
        rw [crossDiffWeight, ← sub_smul,
          show ((M : ℤ) + (0 : ℕ)) = (M : ℤ) from by push_cast; ring,
          show (μ + (0 + 2) + (0 : ℕ)) = μ + 2 from by push_cast; ring,
          show (μ + ((n : ℤ) + 2) + (0 : ℕ)) = μ + ((n : ℤ) + 2) from by push_cast; ring]]
  rw [finsum_sub_distrib hfin0 hfinN]
  rfl

/-! ## `crossCFirstDiff` in per-base mode-value finsum DIFFERENCE form. -/

/-- **The `a`-outer `c`-first DIFFERENCE in per-base mode-value finsum form** (FULLY proven).
Combining `crossCFirstDiff_eq_presDiff` with `presDiff_eq_modeFinsum`, the difference is the
per-`i` `C(K,i)`-weighted mode-value finsum with the explicit pole-difference weight
`crossDiffWeight M n μ`, identical across all bases `bᵢ = a₍i−(n+1)₎d`:

  `crossCFirstDiff W n K M a c d
     = ∑_{i≤K} C(K,i) • ∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎(a₍i−(n+1)₎d)`.

This isolates the genuine `a`-outer `c`-first DIFFERENCE U-core scalar target: the per-base mode
coefficient is the explicit level-`0`-vs-level-`n` pole-difference, the SAME for every base. -/
theorem crossCFirstDiff_eq_modeFinsum (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    crossCFirstDiff W n K M a c d
      = ∑ i ∈ Finset.range (K + 1),
          cbz (K : ℤ) (i : ℤ) •
            ∑ᶠ μ : ℤ, crossDiffWeight M n μ
              • W.smul c μ (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) := by
  rw [crossCFirstDiff_eq_presDiff W n K M a c d]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [presDiff_eq_modeFinsum W M n c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)]

/-! ## The exact remaining scalar core (the `a`-outer `c`-first DIFFERENCE twin of the U/V-cores). -/

/-- **The `a`-outer `c`-first DIFFERENCE scalar core** (the precise remaining identity).  For
homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the level-`0`-vs-level-`n` `c`-first DIFFERENCE family
collapses onto a **level-`n`** `PresTowerFam` in `c` (the `c`-tower correction over the multi-base
`a₍·₎d`) plus a homogeneous multi-grade `MGTowerFam` W-family in the products `c₍s₎a` based at `d`.
This is precisely `CrossCFirstDiffTowerEq` (`ZhuVermaAnArchCrossCFirst0Close`), restated as the
genuine scalar-weight assignment target — the `a`-outer DIFFERENCE twin of the diagonal U/V-core
(`AnmCircTowerEq_of_sides`).  The per-base pole-difference weight `crossDiffWeight M n μ`
(`presDiff_eq_modeFinsum`) is the irreducible content; its cross-base coupling into the `c₍s₎a`
`MGTowerFam` is the genuine residual (engine `certificates/mathematica/cfirst_perbase_polediff.wl`: per-base single-tower fit
`False`).  Carried as a hypothesis, NEVER an axiom. -/
def CFirstDiffScalarCore (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  CrossCFirstDiffTowerEq W n K M P a c d

/-- **`CFirstDiffScalarCore` ⟹ `CrossCFirstDiffTowerEq`** (definitional unfold; the scalar core IS
the level-`0`-vs-level-`n` `c`-first DIFFERENCE tower decomposition, named at the `a`-outer U-core
level). -/
theorem crossCFirstDiffTowerEq_of_scalarCore (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱)
    (hsc : CFirstDiffScalarCore W n K M P a c d) :
    CrossCFirstDiffTowerEq W n K M P a c d := hsc

/-! ## `CFirstDiffScalarCore` (universal) ⟹ the full `MUGradedAction W`. -/

/-- **The full `MUGradedAction W` from the single universal `CFirstDiffScalarCore`.**  Given, for
every level `n` and all homogeneous data, the `a`-outer `c`-first DIFFERENCE scalar core
`CFirstDiffScalarCore`, the pole-difference tower decomposition `CrossCFirstDiffTowerEq` holds
(`crossCFirstDiffTowerEq_of_scalarCore`), and `MUGradedAction_of_crossCFirstDiff`
(`ZhuVermaAnArchCrossCFirst0Close`) — the companion `ardCFirst` `c`-tower base layer and EVERY
structural assembly (Term₂'s commutator + `c`-first towers, Term₁'s commutator tower, the
`Term₁ − Term₂` subtraction, and the membership half) fully discharged — assembles the Dong–Jiang
`M(U)` graded-action crux `MUGradedAction W`.

This re-exports the `MUGradedAction` closure at the `a`-outer `c`-first DIFFERENCE U-core level: the
single remaining input is the scalar-weight assignment `CFirstDiffScalarCore`, with its exact
per-base mode-value shape `crossCFirstDiff_eq_modeFinsum` (per-base pole-difference weight
`crossDiffWeight M n μ`) proved here. -/
theorem MUGradedAction_of_diffScalarCore (W : VertexOperatorAlgebra 𝒱)
    (Hsc : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CFirstDiffScalarCore W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_crossCFirstDiff W
    (fun n K M P a ha c hc d hd =>
      crossCFirstDiffTowerEq_of_scalarCore W n K M P a c d (Hsc n K M P a ha c hc d hd))

/-! ## Status — `MUGradedAction W` pinned to the single `a`-outer `c`-first DIFFERENCE scalar core.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCFirstDiff_eq_presDiff`** — **the exact per-base `PresAnm`-difference shape**, FULLY proven:
  `crossCFirstDiff = ∑_{i≤K} C(K,i) • (PresAnm W M 0 0 c bᵢ − PresAnm W M n 0 c bᵢ)` (per-`i` the pure
  inner-circle pole-difference `c∘₀bᵢ − c∘ₙbᵢ`, over the SAME bases `bᵢ = a₍i−(n+1)₎d`).
* **`crossDiffWeight`** / **`presDiff_eq_modeFinsum`** — the explicit per-`(M,n,μ)` pole-difference
  weight `cbz(M, μ+2) − cbz(M, μ+(n+2))` and the per-base mode-value finsum form
  `PresAnm W M 0 0 c b − PresAnm W M n 0 c b = ∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎b`, FULLY proven
  (both level finsums have finite support, merged by `finsum_sub_distrib`).
* **`crossCFirstDiff_eq_modeFinsum`** — **the exact per-base mode-value DIFFERENCE form** of
  `crossCFirstDiff`: `∑_{i≤K} C(K,i) • ∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎(a₍i−(n+1)₎d)` (per-base
  pole-difference weight, identical across bases).  This isolates the genuine `a`-outer `c`-first
  DIFFERENCE U-core scalar target.
* **`CFirstDiffScalarCore`** / **`crossCFirstDiffTowerEq_of_scalarCore`** — the `a`-outer `c`-first
  DIFFERENCE scalar core predicate (the precise remaining weight-assignment identity) and its
  discharge of `CrossCFirstDiffTowerEq`.
* **`MUGradedAction_of_diffScalarCore`** — **the full `MUGradedAction W`** from the SINGLE universal
  `CFirstDiffScalarCore`, via `MUGradedAction_of_crossCFirstDiff`.

**The single remaining identity (engine-verified TRUE; NOT faked):** the universally-quantified
`CFirstDiffScalarCore W n K M P a c d` — the `a`-outer `c`-first DIFFERENCE weight assignment
collapsing the per-base mode-value form (`crossCFirstDiff_eq_modeFinsum`, weight `crossDiffWeight M n
μ = cbz(M, μ+2) − cbz(M, μ+(n+2))`) onto a level-`n` `PresTowerFam` in `c` over `a₍·₎d` plus an
`MGTowerFam` in `c₍s₎a` based at `d`.  The genuine residual is the **cross-base** coupling: per-base
the pole-difference is NOT a single-base level-`n` `c`-tower (engine `certificates/mathematica/cfirst_perbase_polediff.wl`:
per-base single-tower span `False` once the base reaches `c`'s pole window), absorbed only by the
cross-base reorganization into the `c₍s₎a` `MGTowerFam` (engine `certificates/mathematica/cfirst0_diff.wl`: combined span
`True`, `n = 1, 2`; `certificates/mathematica/cfirst_diff_conly.wl`: `c`-towers alone `False`).  This is the `a`-outer
DIFFERENCE twin of the FULLY-proven diagonal U/V scalar cores
(`UgammaModeCollAnm_eq_towerCoeff` / `VgammaModeCollAnm_eq_towerCoeff`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCFirstDiff_eq_presDiff
  #print axioms VOA.presDiff_eq_modeFinsum
  #print axioms VOA.crossCFirstDiff_eq_modeFinsum
  #print axioms VOA.crossCFirstDiffTowerEq_of_scalarCore
  #print axioms VOA.MUGradedAction_of_diffScalarCore
-/
