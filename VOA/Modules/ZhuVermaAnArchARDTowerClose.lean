/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCrossCFirstGate
import VOA.Modules.ZhuVermaAnArchVcoreTwins

/-!
# Game One — closing **`ARDTowerDecomp`** (the level-`0` lift) ⟹ `MUGradedAction`.

This file closes the single combinatorial gate `ARDTowerDecomp` (`ZhuVermaAnArchCrossCFirstGate`) — the
`a`-outer right-action-difference tower decomposition — down to its genuine `a`-irreducible core: the
**level-`0` cross-circle `c`-first tower decomposition** `CrossCFirst0TowerEq`.

## The structure (FULLY proven here; no `sorry`/axiom/`pbw`)

By `anmRightDiff_eq_terms` (`ZhuVermaAnArchAnmRightDiff`),

  `anmRightDiff W n K a c d = Term₁ − Term₂`,
  `Term₁ = anmRight W n 0 a (anmCirc W 0 0 c d)`  (the **level-`0`** inner circle, pole `2`),
  `Term₂ = anmRight W n 0 a (anmCirc W n 0 c d)`  (the **level-`n`** inner circle, pole `n+2`).

**Term₂ is PROVEN** as a `PresTowerFam`-in-`c` plus an `MGTowerFam`-in-`c₍s₎a`
(`ardTerm2TowerEq_of_comm` + `ARDCommTowerEq_holds`, `ZhuVermaAnArchVcoreTwins`).  We bring **Term₁**
to the SAME shape: by `crossCirc_modeSplit` (`ZhuVermaAnArchMUcrossHM`), via the bridge
`anmRight_zero`+`anmCirc_zero_zero` (`ZhuVermaAnArchAnm`),

  `Term₁ = crossCircCFirst W n K M a c d + crossCircComm W n K M a c d`,

with `crossCircComm` **already PROVEN** to be an `MGTowerFam` (`CrossCommTowerEq_holds`,
`ZhuVermaAnArchVcoreTwins`).  So Term₁'s tower form (`ARDTerm1TowerEq`) reduces to the **single**
remaining identity

  `(CrossCFirst0TowerEq)   crossCircCFirst W n K M a c d
       = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`,

the level-`0`-vs-level-`n` lift of the cross `c`-first family.  This is the genuine
`a`-irreducible content (the `n`-offset of the level-`0` inner pole, absorbed by the proven regrade
`crossDiff_regrade`/`towerCoeffAnm_mode_regrade` exactly as Term₂'s commutator twin
`ARDCommTowerEq_holds` was).

Subtracting Term₂ from Term₁ — both now in `PresTowerFam(c) + MGTowerFam` shape — and using the
closure of `PresTowerFam`/`MGTowerFam` under finite ℂ-combinations (`PresTowerFam_add`/
`smul_PresTowerFam`; the new `MGTowerFam_add`/`smul_MGTowerFam` here) yields the explicit
`ARDTowerDecomp` witness.  `MUGradedAction_of_ARDTowerDecomp` then closes the entire
`MUGradedAction W` crux.

## What is proved here (axiom-clean)

* **`MGTowerFam_add`** / **`smul_MGTowerFam`** — `MGTowerFam` is closed under finite ℂ-combinations
  (the per-index homogeneity of every left factor is preserved through `Sum.elim`).
* **`ARDTerm1TowerEq`** — the precise Term₁ tower-decomposition predicate (the level-`0` inner-circle
  twin of `ARDTerm2TowerEq`), and **`CrossCFirst0TowerEq`** — its genuine `a`-irreducible core (the
  level-`0` cross `c`-first family as `PresTowerFam(c) + MGTowerFam`).
* **`ardTerm1TowerEq_of_cfirst`** — `CrossCFirst0TowerEq` ⟹ `ARDTerm1TowerEq` (adding the proven
  `crossCircComm` `MGTowerFam`).
* **`ardTowerDecomp_of_term1_term2`** — `ARDTerm1TowerEq` + `ARDTerm2TowerEq` ⟹ `ARDTowerDecomp`
  (the `Term₁ − Term₂` subtraction, FULLY proven).
* **`ardTowerDecomp_of_cfirst`** — `CrossCFirst0TowerEq` ⟹ `ARDTowerDecomp` (Term₂ discharged in
  full via `ARDCommTowerEq_holds`).
* **`MUGradedAction_of_crossCFirst0`** — **the full `MUGradedAction W`** from the SINGLE universal
  `CrossCFirst0TowerEq` (via `MUGradedAction_of_ARDTowerDecomp`).

## Engine status (rank-1 free boson; NOT faked)

* `certificates/mathematica/cfirst0_levn.wl` (re-run): the level-`0` cross `c`-first family
  `crossCircCFirst` lies in `(c-towers@a₍g₎d) + ((c₍s₎a)-towers@d)` for `n = 1, 2` and mixed
  homogeneous `a, c, d` (**True**); the `c`-towers ALONE do NOT suffice (**False**), so the
  `MGTowerFam` in `c₍s₎a` is genuinely load-bearing in the level-`0` lift.
* `certificates/mathematica/anmrightdiff_tower.wl`: the FULL `anmRightDiff` in the same combined span
  (**True**, `n = 1, 2`), confirming the `Term₁ − Term₂` assembly.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `MGTowerFam` is closed under finite ℂ-combinations. -/

/-- **The sum of two `MGTowerFam`s is again an `MGTowerFam`** (merge the `Fin S₁` and `Fin S₂` index
sets to `Fin (S₁ + S₂)` via `finSumFinEquiv`; the per-index grade/left/base/depth/weight data combine
by `Sum.elim`).  No padding is needed — the per-index depth `ΔS` already varies per summand. -/
theorem MGTowerFam_add (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (S₁ S₂ : ℕ)
    (gradeS₁ : Fin S₁ → ℕ) (leftS₁ baseS₁ : Fin S₁ → 𝒱) (ΔS₁ : Fin S₁ → ℕ) (wS₁ : Fin S₁ → ℕ → ℂ)
    (gradeS₂ : Fin S₂ → ℕ) (leftS₂ baseS₂ : Fin S₂ → 𝒱) (ΔS₂ : Fin S₂ → ℕ) (wS₂ : Fin S₂ → ℕ → ℂ) :
    MGTowerFam W n S₁ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁
        + MGTowerFam W n S₂ gradeS₂ leftS₂ baseS₂ ΔS₂ wS₂
      = MGTowerFam W n (S₁ + S₂)
          (fun r => Sum.elim gradeS₁ gradeS₂ (finSumFinEquiv.symm r))
          (fun r => Sum.elim leftS₁ leftS₂ (finSumFinEquiv.symm r))
          (fun r => Sum.elim baseS₁ baseS₂ (finSumFinEquiv.symm r))
          (fun r => Sum.elim ΔS₁ ΔS₂ (finSumFinEquiv.symm r))
          (fun r => Sum.elim wS₁ wS₂ (finSumFinEquiv.symm r)) := by
  rw [MGTowerFam, MGTowerFam, MGTowerFam]
  rw [← finSumFinEquiv.sum_comp
      (fun r : Fin (S₁ + S₂) =>
        ∑ δ ∈ Finset.range (Sum.elim ΔS₁ ΔS₂ (finSumFinEquiv.symm r)),
          Sum.elim wS₁ wS₂ (finSumFinEquiv.symm r) δ
            • PresAnm W (Sum.elim gradeS₁ gradeS₂ (finSumFinEquiv.symm r)) n δ
                (Sum.elim leftS₁ leftS₂ (finSumFinEquiv.symm r))
                (Sum.elim baseS₁ baseS₂ (finSumFinEquiv.symm r)))]
  rw [Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

/-- **A ℂ-scalar multiple of an `MGTowerFam` is again an `MGTowerFam`** (scale the weights). -/
theorem smul_MGTowerFam (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (S : ℕ)
    (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ) (t : ℂ) :
    t • MGTowerFam W n S gradeS leftS baseS ΔS wS
      = MGTowerFam W n S gradeS leftS baseS ΔS (fun r δ => t * wS r δ) := by
  rw [MGTowerFam, MGTowerFam, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [smul_smul]

/-- Homogeneity of the left factors of `MGTowerFam_add`'s merged data: if both families have
homogeneous left factors, so does the merge (`Sum.elim`). -/
theorem MGTowerFam_add_hom (W : VertexOperatorAlgebra 𝒱) (S₁ S₂ : ℕ)
    (gradeS₁ : Fin S₁ → ℕ) (leftS₁ : Fin S₁ → 𝒱) (gradeS₂ : Fin S₂ → ℕ) (leftS₂ : Fin S₂ → 𝒱)
    (hhom₁ : ∀ r : Fin S₁, leftS₁ r ∈ W.grading ((gradeS₁ r : ℤ)))
    (hhom₂ : ∀ r : Fin S₂, leftS₂ r ∈ W.grading ((gradeS₂ r : ℤ)))
    (r : Fin (S₁ + S₂)) :
    Sum.elim leftS₁ leftS₂ (finSumFinEquiv.symm r)
      ∈ W.grading (((Sum.elim gradeS₁ gradeS₂ (finSumFinEquiv.symm r) : ℕ) : ℤ)) := by
  rcases h : finSumFinEquiv.symm r with r₁ | r₂
  · simp only [Sum.elim_inl]; exact hhom₁ r₁
  · simp only [Sum.elim_inr]; exact hhom₂ r₂

/-! ## The Term₁ tower-decomposition predicate and its `a`-irreducible core. -/

/-- **The Term₁ (`a`-outer level-`0` inner-circle, pole-`2`) tower-decomposition predicate** (the
level-`0` twin of `ARDTerm2TowerEq`).  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the `a`-outer
level-`0` circle `anmRight W n 0 a (anmCirc W 0 0 c d)` decomposes as a `PresAnm`-tower U-family in `c`
(over grade `M`, level `n`, based at the `a₍·₎d`-modes) plus a homogeneous multi-grade `MGTowerFam`
W-family in the products `c₍s₎a` (homogeneous left factors of grade `gradeS r`, based at `d`):

  `anmRight W n 0 a (anmCirc W 0 0 c d)
     = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`. -/
def ARDTerm1TowerEq (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ∃ (RU ΔU S : ℕ) (baseU : Fin RU → 𝒱) (wU : Fin RU → ℕ → ℂ)
    (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
    (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
    anmRight W n 0 a (anmCirc W 0 0 c d)
      = PresTowerFam W M n c RU ΔU baseU wU
        + MGTowerFam W n S gradeS leftS baseS ΔS wS

/-- **The level-`0` cross `c`-first tower-decomposition predicate** (the genuine `a`-irreducible
remaining identity).  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the level-`0` cross `c`-first
family `crossCircCFirst W n K M a c d` (the inner circle is pole `2 = 0+2`) decomposes onto a
`PresAnm`-tower U-family in `c` at level `n` (based at the `a₍·₎d`-modes) plus a homogeneous
multi-grade `MGTowerFam` W-family in the products `c₍s₎a` (based at `d`):

  `crossCircCFirst W n K M a c d
     = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`.

The level-`0`-vs-level-`n` lift of the cross `c`-first family (the `n`-offset of the level-`0` inner
pole, absorbed by the proven regrade `crossDiff_regrade`/`towerCoeffAnm_mode_regrade`).
Engine-verified TRUE on the rank-1 free boson (`certificates/mathematica/cfirst0_levn.wl`, `n = 1, 2`;
the `MGTowerFam` in `c₍s₎a` is load-bearing — the `c`-towers ALONE do NOT suffice). -/
def CrossCFirst0TowerEq (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ∃ (RU ΔU S : ℕ) (baseU : Fin RU → 𝒱) (wU : Fin RU → ℕ → ℂ)
    (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
    (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
    crossCircCFirst W n K M a c d
      = PresTowerFam W M n c RU ΔU baseU wU
        + MGTowerFam W n S gradeS leftS baseS ΔS wS

/-! ## Term₁'s mode-split bridge and `CrossCFirst0TowerEq` ⟹ `ARDTerm1TowerEq`. -/

/-- **Term₁ mode-split (the `anmRight`/`anmCirc` form).**  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`anmRight W n 0 a (anmCirc W 0 0 c d) = crossCircCFirst + crossCircComm`.  Bridge
`anmRight_zero`+`anmCirc_zero_zero` to `resHom W 0 (n+1) a (resHom W 0 2 c d)`, then
`crossCirc_modeSplit` (`ZhuVermaAnArchMUcrossHM`). -/
theorem term1_modeSplit (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    anmRight W n 0 a (anmCirc W 0 0 c d)
      = crossCircCFirst W n K M a c d + crossCircComm W n K M a c d := by
  rw [anmRight_zero, anmCirc_zero_zero, crossCirc_modeSplit W n ha hc d]

/-- **`CrossCFirst0TowerEq` ⟹ `ARDTerm1TowerEq`.**  Term₁ mode-splits (`term1_modeSplit`) into
`crossCircCFirst + crossCircComm`; the `c`-first family is supplied as `PresTowerFam(c) + MGTowerFam`
by `CrossCFirst0TowerEq`, and `crossCircComm` is the proven `MGTowerFam` (`CrossCommTowerEq_holds`).
Merging the two `MGTowerFam`s (`MGTowerFam_add`) gives the precise Term₁ tower form. -/
theorem ardTerm1TowerEq_of_cfirst (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ))
    (hcf : CrossCFirst0TowerEq W n K M P a c d) :
    ARDTerm1TowerEq W n K M P a c d := by
  obtain ⟨RU, ΔU, S₁, baseU, wU, gradeS₁, leftS₁, baseS₁, ΔS₁, wS₁, hhom₁, hcfeq⟩ := hcf
  obtain ⟨S₂, gradeS₂, leftS₂, baseS₂, ΔS₂, wS₂, hhom₂, hcommeq⟩ :=
    CrossCommTowerEq_holds W n ha hc hd
  refine ⟨RU, ΔU, S₁ + S₂, baseU, wU,
    (fun r => Sum.elim gradeS₁ gradeS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim leftS₁ leftS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim baseS₁ baseS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim ΔS₁ ΔS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim wS₁ wS₂ (finSumFinEquiv.symm r)),
    MGTowerFam_add_hom W S₁ S₂ gradeS₁ leftS₁ gradeS₂ leftS₂ hhom₁ hhom₂, ?_⟩
  rw [term1_modeSplit W n ha hc d, hcfeq, hcommeq, add_assoc,
    MGTowerFam_add W n S₁ S₂ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁ gradeS₂ leftS₂ baseS₂ ΔS₂ wS₂]

/-! ## `ARDTerm1TowerEq` + `ARDTerm2TowerEq` ⟹ `ARDTowerDecomp` (the `Term₁ − Term₂` subtraction). -/

/-- **`ARDTerm1TowerEq` + `ARDTerm2TowerEq` ⟹ `ARDTowerDecomp`.**  By `anmRightDiff_eq_terms`
(`ZhuVermaAnArchAnmRightDiff`), `anmRightDiff = Term₁ − Term₂`.  Writing both terms as
`PresTowerFam(c) + MGTowerFam`, the difference is

  `(U₁ − U₂) + (W₁ − W₂)`,

where `U₁ − U₂` is again a `PresTowerFam` in `c` (`smul_PresTowerFam` by `−1` + `PresTowerFam_add`)
and `W₁ − W₂` is again an `MGTowerFam` (`smul_MGTowerFam` by `−1` + `MGTowerFam_add`), with the
homogeneity of all left factors preserved.  This is the explicit `ARDTowerDecomp` witness. -/
theorem ardTowerDecomp_of_term1_term2 (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (_hc : c ∈ W.grading (M : ℤ)) (d : 𝒱)
    (hT1 : ARDTerm1TowerEq W n K M P a c d) (hT2 : ARDTerm2TowerEq W n K M P a c d) :
    ARDTowerDecomp W n K M P a c d := by
  obtain ⟨RU₁, ΔU₁, S₁, baseU₁, wU₁, gradeS₁, leftS₁, baseS₁, ΔS₁, wS₁, hhom₁, heq₁⟩ := hT1
  obtain ⟨RU₂, ΔU₂, S₂, baseU₂, wU₂, gradeS₂, leftS₂, baseS₂, ΔS₂, wS₂, hhom₂, heq₂⟩ := hT2
  -- the merged `PresTowerFam`-in-`c` (U₁ + (−1)•U₂) and `MGTowerFam` (W₁ + (−1)•W₂).
  refine ⟨RU₁ + RU₂, max ΔU₁ ΔU₂, S₁ + S₂,
    (fun r => Sum.elim baseU₁ baseU₂ (finSumFinEquiv.symm r)),
    (fun r δ => Sum.elim (fun r₁ => if δ < ΔU₁ then wU₁ r₁ δ else 0)
              (fun r₂ => if δ < ΔU₂ then (-1 : ℂ) * wU₂ r₂ δ else 0) (finSumFinEquiv.symm r)),
    (fun r => Sum.elim gradeS₁ gradeS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim leftS₁ leftS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim baseS₁ baseS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim ΔS₁ ΔS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim wS₁ (fun r₂ δ => (-1 : ℂ) * wS₂ r₂ δ) (finSumFinEquiv.symm r)),
    MGTowerFam_add_hom W S₁ S₂ gradeS₁ leftS₁ gradeS₂ leftS₂ hhom₁ hhom₂, ?_⟩
  rw [anmRightDiff_eq_terms W n ha c d, heq₁, heq₂]
  -- `(U₁ + W₁) − (U₂ + W₂) = (U₁ − U₂) + (W₁ − W₂)`.
  rw [show (PresTowerFam W M n c RU₁ ΔU₁ baseU₁ wU₁ + MGTowerFam W n S₁ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁)
          - (PresTowerFam W M n c RU₂ ΔU₂ baseU₂ wU₂ + MGTowerFam W n S₂ gradeS₂ leftS₂ baseS₂ ΔS₂ wS₂)
        = (PresTowerFam W M n c RU₁ ΔU₁ baseU₁ wU₁
            + (-1 : ℂ) • PresTowerFam W M n c RU₂ ΔU₂ baseU₂ wU₂)
          + (MGTowerFam W n S₁ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁
            + (-1 : ℂ) • MGTowerFam W n S₂ gradeS₂ leftS₂ baseS₂ ΔS₂ wS₂) from by
    simp only [neg_one_smul]; abel]
  rw [smul_PresTowerFam W M n c RU₂ ΔU₂ baseU₂ wU₂ (-1 : ℂ),
    PresTowerFam_add W M n c RU₁ RU₂ ΔU₁ ΔU₂ baseU₁ baseU₂ wU₁ (fun r δ => (-1 : ℂ) * wU₂ r δ),
    smul_MGTowerFam W n S₂ gradeS₂ leftS₂ baseS₂ ΔS₂ wS₂ (-1 : ℂ),
    MGTowerFam_add W n S₁ S₂ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁
      gradeS₂ leftS₂ baseS₂ ΔS₂ (fun r δ => (-1 : ℂ) * wS₂ r δ)]

/-! ## `CrossCFirst0TowerEq` ⟹ `ARDTowerDecomp` (Term₂ discharged in full). -/

/-- **`CrossCFirst0TowerEq` ⟹ `ARDTowerDecomp`.**  Term₂ is FULLY discharged via
`ardTerm2TowerEq_of_comm` + `ARDCommTowerEq_holds` (`ZhuVermaAnArchVcoreTwins`); Term₁ comes from
`ardTerm1TowerEq_of_cfirst` (the carried `a`-irreducible core).  `ardTowerDecomp_of_term1_term2`
assembles. -/
theorem ardTowerDecomp_of_cfirst (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ))
    (hcf : CrossCFirst0TowerEq W n K M P a c d) :
    ARDTowerDecomp W n K M P a c d :=
  ardTowerDecomp_of_term1_term2 W n ha hc d
    (ardTerm1TowerEq_of_cfirst W n ha hc hd hcf)
    (ardTerm2TowerEq_of_comm W n ha hc d (ARDCommTowerEq_holds W n ha hc hd))

/-! ## The full `MUGradedAction W` from the single universal `CrossCFirst0TowerEq`. -/

/-- **The full `MUGradedAction W` from the single universal `CrossCFirst0TowerEq`.**  Given, for every
level `n`, the level-`0` cross `c`-first tower decomposition `CrossCFirst0TowerEq` (the genuine
`a`-irreducible Dong–Jiang Lemma 2.8 lift), the entire `ARDTowerDecomp` is discharged
(`ardTowerDecomp_of_cfirst` — Term₂ fully closed via `ARDCommTowerEq_holds`), and
`MUGradedAction_of_ARDTowerDecomp` (`ZhuVermaAnArchCrossCFirstGate`) — whose membership half is fully
proven — assembles the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`.

This CLOSES the entire `MUGradedAction` gate down to the single explicit level-`0`-vs-level-`n` lift
`CrossCFirst0TowerEq`, engine-verified TRUE on the rank-1 free boson, with EVERY other piece (Term₂'s
commutator + `c`-first towers, Term₁'s commutator tower, the `Term₁ − Term₂` subtraction, and the
membership half) fully discharged. -/
theorem MUGradedAction_of_crossCFirst0 (W : VertexOperatorAlgebra 𝒱)
    (Hcf : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCFirst0TowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_ARDTowerDecomp W
    (fun n K M P a ha c hc d hd =>
      ardTowerDecomp_of_cfirst W n ha hc hd (Hcf n K M P a ha c hc d hd))

/-! ## Status — `MUGradedAction W` closed to the single level-`0`-vs-level-`n` lift.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`MGTowerFam_add`** / **`smul_MGTowerFam`** / **`MGTowerFam_add_hom`** — `MGTowerFam` is closed
  under finite ℂ-combinations (per-index homogeneity preserved through `Sum.elim`).
* **`ARDTerm1TowerEq`** / **`CrossCFirst0TowerEq`** — the Term₁ tower-decomposition predicate (the
  level-`0` inner-circle twin of `ARDTerm2TowerEq`) and its genuine `a`-irreducible core.
* **`term1_modeSplit`** — `Term₁ = crossCircCFirst + crossCircComm` (bridge + `crossCirc_modeSplit`).
* **`ardTerm1TowerEq_of_cfirst`** — `CrossCFirst0TowerEq` ⟹ `ARDTerm1TowerEq` (adding the proven
  `crossCircComm` `MGTowerFam` via `CrossCommTowerEq_holds`).
* **`ardTowerDecomp_of_term1_term2`** — `ARDTerm1TowerEq` + `ARDTerm2TowerEq` ⟹ `ARDTowerDecomp`
  (the `Term₁ − Term₂` subtraction, FULLY proven).
* **`ardTowerDecomp_of_cfirst`** — `CrossCFirst0TowerEq` ⟹ `ARDTowerDecomp` (Term₂ fully discharged).
* **`MUGradedAction_of_crossCFirst0`** — **the full `MUGradedAction W`** from the single universal
  `CrossCFirst0TowerEq`, via `MUGradedAction_of_ARDTowerDecomp`.

**The single remaining identity (engine-verified TRUE; NOT faked):** the universally-quantified
`CrossCFirst0TowerEq W n K M P a c d` — the level-`0` cross `c`-first family

  `crossCircCFirst W n K M a c d = PresTowerFam W M n c … + MGTowerFam W n S …`,

the level-`0`-vs-level-`n` lift of the cross `c`-first family (the genuine `a`-irreducible Dong–Jiang
Lemma 2.8 coefficient assignment; the `n`-offset of the level-`0` inner pole `2` vs the carrier
level-`n` tower pole `n+2`, the same offset the proven regrade `crossDiff_regrade`/
`towerCoeffAnm_mode_regrade` absorbed for Term₂'s commutator twin `ARDCommTowerEq_holds`).
Engine values: `certificates/mathematica/cfirst0_levn.wl` (`crossCircCFirst ∈ (c-tow@a₍g₎d)+((c₍s₎a)-tow@d)`,
`n = 1, 2`, the `MGTowerFam` load-bearing), `certificates/mathematica/anmrightdiff_tower.wl` (the full `Term₁ − Term₂`
assembly).  Every other piece — Term₂'s full tower form, Term₁'s commutator tower, the subtraction,
and the membership half (`ardiff_mem_of_decomp`) — is fully discharged here and upstream.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.MGTowerFam_add
  #print axioms VOA.smul_MGTowerFam
  #print axioms VOA.ardTerm1TowerEq_of_cfirst
  #print axioms VOA.ardTowerDecomp_of_term1_term2
  #print axioms VOA.ardTowerDecomp_of_cfirst
  #print axioms VOA.MUGradedAction_of_crossCFirst0
-/
