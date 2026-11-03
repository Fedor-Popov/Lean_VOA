/-
Copyright (c) 2026 Leonardo Rastelli, Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.LeeYangGram
import VOA.Examples.LeeYangProper
import VOA.Core.BorcherdsIdentity
import VOA.Examples.VirasoroDeformationLow

/-!
# The level-4 Kac determinant of `V(c,0)`, and level-4 null completeness at `c = -22/5`

## What was already there, and what this file adds

`Examples/LeeYangSingular` derives the Lee–Yang central charge and the level-4 singular vector
`s = 5L₋₂²|0⟩ - 3L₋₄|0⟩`.  `Examples/LeeYangProper` proves the submodule it generates is proper,
hence `s ∈ maxIdealVir leeYangC` and `V(-22/5,0)` is not simple.  `Examples/LeeYangGram` computes
the level-4 Gram matrix **at the single value `c = -22/5`**, and does so partly by *solving*
`⟨s,·⟩ = 0` — so it is a consistency audit of the Kac matrix rather than an independent
computation of it, and it says nothing about other central charges.

Two things were therefore missing, and both are supplied here:

1. **the `c`-dependence** — the determinant as a polynomial in the central charge, which is where
   the content of a Kac determinant actually lies;
2. **the converse inclusion** `maxIdeal ∩ 𝒱₄ ⊆ ℂ·s`, which upgrades
   `leeYangSingular_mem_maxIdealVir` from `⊆` to `=` in degree 4.

## §4  The determinant

In the ordered basis `(L₋₂²|0⟩, L₋₄|0⟩)` of `𝒱₄` the Gram matrix of `RigidBridge.shapForm` — the
**top-mode** form `⟨a,b⟩ₖ := ε(a₍₂ₖ₋₁₎b)` — is, for **arbitrary** `c` (`gram4_eq`)

```
S(c) = [[ c²/2 + 40c ,  63c ],
        [    63c     , 105c ]]
```

and (`det_gram4`, `det_gram4_poly`, and `shapForm_level4_det` for the `Matrix`-free form)

```
det S(c)  =  (105/2)·c³ + 231·c²  =  21 · ( c²(5c + 22) / 2 ).
```

**Every entry is derived, none assumed.**

* `105c` is `LeeYangGram.shapForm_L4vac_self`, from `(L₋₄|0⟩)₍₇₎ = 21·L₄` and `L₄L₋₄|0⟩ = 5c|0⟩`.
* `63c` is the same operator identity paired against `L₄L₋₂²|0⟩ = 3c|0⟩` (`Lop_four_L2L2vac`).
* `c²/2 + 40c` is new, and is the only entry that no operator identity in the repository already
  delivers: `L₋₂²|0⟩ = ω₍₋₁₎ω` is **not** a `T`-translate of `ω`, so `smul_Tpow` does not apply and
  the **Borcherds iterate formula** `Core.BorcherdsIdentity.mode_iterate` is needed, at `ℓ = -1`:
  `(ω₍₋₁₎ω)₍₇₎ = ∑ᵢ [ L₋₂₋ᵢL₆₊ᵢ + L₅₋ᵢL_{i-1} ]` (`iterate_summand`).  The first family dies on a
  weight-4 state, and of the second exactly six terms are in range, contributing
  `18c + 12c + 6c + (c+8)(c/2) + 0 + 0 = c²/2 + 40c` (`smul_L2L2vac_seven_self`).

The bracketed factor `c²(5c+22)/2` is precisely the textbook level-4 **vacuum-module** Kac
determinant `det[[(c/2)(c+8), 3c],[3c, 5c]]`; the overall `21` is the top-mode normalisation.

`det_gram4_eq_zero_iff` : the determinant vanishes **iff `c = 0` or `c = -22/5`**.  This strictly
strengthens `LeeYangSingular.exists_level4_singular_iff`, which sees only `-22/5`: that theorem
asks for a weight-4 vector killed by `L₁` *and* `L₂`, whereas the determinant sees the whole
radical.  At `c = 0` the level-4 form is in fact **identically zero**
(`shapForm_level4_eq_zero_at_zero`) — that is the meaning of the double root — because `ω` is
itself null there and `𝒱₄` consists entirely of its descendants.

## ⚠⚠ §5b  `S(c)` is NOT `21 ×` the textbook Kac matrix

`LeeYangGram.shapForm_leeYang_level4_eq_kac` reads, at `c = -22/5`, "the level-4 Gram matrix is
`21 ×` the textbook Kac matrix `G(c) = [[(c/2)(c+8), 3c],[3c, 5c]]`".  **That is a Lee–Yang
accident and must never be generalised to a variable `c`**:

* the second row and column do scale, `63c = 21·3c` and `105c = 21·5c`, at every `c`;
* but `c²/2 + 40c` versus `21·(c/2)(c+8) = 21c²/2 + 84c` differ by `-2c(5c+22)`, which vanishes
  **only** at `c = 0` and `c = -22/5`.

`shapForm_L2L2vac_self_ne_kac_rescaled` proves the disagreement outright for all other `c`, as a
guard rail.  What *is* true uniformly is `det S(c) = 21 · det G(c)`; that is `det_gram4`.

## §6  The rank at `c = -22/5`

`radBil_shapForm_leeYang_eq_span` : the radical of the level-4 form at `c = -22/5` is **exactly**
`ℂ ∙ s`.  The `⊇` half is `LeeYangRigidity.leeYangSingular_mem_radBil`; the `⊆` half is new and is
one line of linear algebra once the general-`c` entries are in hand — pairing an arbitrary
`y = αL₋₂²|0⟩ + βL₋₄|0⟩` against `L₋₄|0⟩` alone forces `β = -3α/5`.

Hence `finrank_radBil_shapForm_leeYang` (`dim rad = 1`) and, with
`VirDefLow.finrank_gradingVir_four` (`dim 𝒱₄ = 2`) and rank–nullity,
`rank_shapForm_leeYang_level4` : **the level-4 Shapovalov form of `V(-22/5,0)` has rank exactly
`1`.**

## §7  Level-4 null completeness — and precisely what it is not

`maxIdealVir_leeYang_inf_grading_four` :

```
    (maxIdeal V(-22/5,0)) ⊓ 𝒱₄  =  ℂ ∙ s .
```

The bridge from "radical of the form" to "maximal ideal" is `mem_radBil_of_mem_properIdeal`, and
it is worth recording that it **does not need Li's theorem** (`maxGradedIdeal = leftRadical B` for
the FHL invariant form), which this repository does not have.  The reason is that `shapForm` is
the *top-mode* form, so `y₍₂ₖ₋₁₎a` is literally a mode of an ideal element and stays in the ideal;
since it equals `⟨y,a⟩ₖ·𝟙`, a nonzero pairing would put the vacuum in a proper ideal.  Only the
FHL-corrected *invariant* form needs the full Li argument, and the level-4 statement never touches
it.

⚠⚠ **THIS IS A LEVEL-4 STATEMENT AND NOTHING MORE.**  It does **not** prove
`maxIdealVir leeYangC = leeYangWordSpan`, i.e. that `s` *generates* the maximal ideal.  That is a
claim about every level `n ≥ 4` at once, and nothing here or anywhere in this repository touches
levels `≥ 5`:

* level 5 would need the Gram matrix of `𝒱₅`;
* level 6 would need `dim 𝒱₆ = 4` — and there is **no basis and no dimension formula for `𝒱ₙ` at
  any `n ≥ 5`** in this repository (`VirasoroSpanning.negWordVir` is indexed by all of `List ℕ`,
  redundantly: five words have energy 6 while `dim 𝒱₆ = 4`);
* the uniform statement is equivalent to the character identity
  `dim (V/⟨s⟩)ₙ = dim L(-22/5,0)ₙ` for all `n`, i.e. to Rocha-Caridi's formula (a
  Rogers–Ramanujan-type identity), which no finite computation produces and which Mathlib does not
  have.

`LeeYangProper` records only `leeYangWordSpan ≤ maxIdealVir leeYangC`; **the reverse inclusion
remains open and this file does not change that.**

## §8  The generic-`c` complement

`radBil_shapForm_eq_bot_of_det_ne_zero` and `maxIdealVir_inf_grading_four_eq_bot` : at every
`c ∉ {0, -22/5}` the level-4 form is nondegenerate and the maximal ideal of `V(c,0)` has **no**
weight-4 part at all.  So level 4 is settled for every central charge except `c = 0`, where
the form vanishes identically and identifying the ideal would need the level-2 null vector `ω`
rather than anything at level 4.

## The forward chain toward the Adamović equivalence

The programme for `L_{-4/3}(𝔰𝔩₂)` is
1. **null completeness**: `maxIdeal = ⟨sing⟩`;
2. `φ(sing) = 0` in the free-field realisation — a finite substitution;
3. `φ ≠ 0 ⟹ ker φ` proper `⟹ ker φ ≤ maxIdeal` — free from the abstract `sSup`;
whence `⟨sing⟩ = ker φ = maxIdeal` and `im φ ≅ L_{-4/3}(𝔰𝔩₂)`.

Honest status of each link, as of this file:

* **(1)** — the hard one.  This file supplies it **at level 4 only**, on the Virasoro side.  The
  affine twin is the same shape and the same cost: `AffineSl2Singular.exists_singular_iff` already
  isolates the factor `3k+4`, which is exactly the Kac–Kazhdan factor of the level-3 charge-`+2`
  determinant, and `AffineSl2Indep` is the analogue of `level4_indep`.  A level-3 statement
  `maxIdeal V^{-4/3}(𝔰𝔩₂) ⊓ (level 3, charge 2) = ℂ·sl2Singular` is reachable by transcribing §6–§7
  of this file.  **All levels is not reachable this way** and needs the character/squeeze route.
* **(3)** — already available: `QuotVOA.le_maxGradedIdeal'`.
* **(2)** — not started; needs the realisation map, which does not exist in the repository yet.

So the chain's third link exists, its first link exists in degree 4 only, and its second link is
unbuilt.  Nothing here licenses the conclusion `im φ ≅ L_{-4/3}(𝔰𝔩₂)`.

## Main results

* `Lop_four_L2L2vac` — `L₄L₋₂²|0⟩ = 3c·|0⟩`, the companion of `L₄L₋₄|0⟩ = 5c·|0⟩`.
* `iterate_summand` — the `ℓ = -1` Borcherds iterate expansion of `(ω₍₋₁₎ω)₍₇₎`, in Virasoro modes.
* `smul_L2L2vac_seven_self`, `shapForm_L2L2vac_self` — `⟨L₋₂²|0⟩,L₋₂²|0⟩⟩₄ = c²/2 + 40c`, for
  arbitrary `c`.  The one genuinely new Gram entry.
* `shapForm_L4vac_L2L2vac` / `shapForm_L2L2vac_L4vac` — `⟨L₋₄|0⟩,L₋₂²|0⟩⟩₄ = 63c`.
* `gram4`, `gram4_eq` — the level-4 Gram matrix for arbitrary `c`.
* `det_gram4`, `det_gram4_poly`, `shapForm_level4_det` — **the level-4 Kac determinant**,
  `21·c²(5c+22)/2 = (105/2)c³ + 231c²`.
* `det_gram4_eq_zero_iff` — it vanishes iff `c = 0` or `c = -22/5`.
* `shapForm_level4_eq_zero_at_zero` — at `c = 0` the level-4 form is identically zero.
* ⚠ `shapForm_L2L2vac_self_ne_kac_rescaled` — the guard rail: `S(c) ≠ 21·G(c)` off `{0, -22/5}`.
* `shapForm_L2L2vac_self_leeYang_agrees`, `shapForm_L2L2vac_L4vac_leeYang_agrees` — the new
  general-`c` entries reproduce, at `c = -22/5`, the two values `LeeYangGram` derived by the
  independent route of solving `⟨s,·⟩ = 0`.  A cross-check on the iterate-formula bookkeeping.
* `exists_level4_coeff` — every weight-4 state is `αL₋₂²|0⟩ + βL₋₄|0⟩`.
* `radBil_shapForm_eq_bot_of_det_ne_zero` — nondegeneracy off the zero set.
* `radBil_shapForm_leeYang_eq_span` — the level-4 radical at `c = -22/5` is exactly `ℂ ∙ s`.
* `finrank_radBil_shapForm_leeYang`, `rank_shapForm_leeYang_level4` — **rank exactly `1`**.
* `mem_radBil_of_mem_properIdeal` — homogeneous elements of a proper ideal lie in the radical
  of the top-mode form of their degree (general VOA statement; belongs in `Core.RigidityBridge`).
* `maxIdealVir_leeYang_inf_grading_four` — **`(maxIdeal) ⊓ 𝒱₄ = ℂ ∙ s`**: level-4 null
  completeness.  ⚠ Level 4 only; see above.
* `finrank_maxIdealVir_leeYang_inf_grading_four`, `mkQ_eq_zero_iff_level_four` — restatements.
* `maxIdealVir_inf_grading_four_eq_bot` — at every `c ∉ {0, -22/5}` the maximal ideal has no
  weight-4 part.

## Status
No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axiom.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on all 37 declarations below, so the
theorem `VOA.pbw` is **not** used.
-/

namespace VOA

open VOA.VirModule
open RigidBridge

namespace LeeYangKac

open LeeYang
open VOA.VirSimple

variable (c : ℂ)

/-! ## §1  The Virasoro modes that the level-4 computation needs

`Examples/LeeYangSingular` already supplies `L₀`, `L₁`, `L₂` on `L₋₂²|0⟩` and `L₋₄|0⟩`.  The
top-mode (Shapovalov) pairing at level `4` uses the mode `(·)₍₇₎`, and unpacking it through the
Borcherds iterate formula reaches `L₃`, `L₄`, `L₅` as well.  Those are computed here, from
`Lop_apply_comm` alone. -/

/-- `Lₙ L₋₂|0⟩ = 0` for `n ≥ 3`: both the boundary term and the central term are out of range
(the central term of `[Lₙ, L₋₂]` needs `n = 2`). -/
theorem Lop_ge_three_L2vac {n : ℤ} (hn : 3 ≤ n) : Lop c n (L2vac c) = 0 := by
  have h := Lop_apply_comm c n (-2) (vacVec c)
  rw [Lop_vacuum c (by omega : (-1 : ℤ) ≤ n), map_zero,
    Lop_vacuum c (by omega : (-1 : ℤ) ≤ n + -2), smul_zero,
    if_neg (by omega : ¬(n + -2 = 0)), zero_smul, add_zero, add_zero] at h
  simpa only [L2vac] using h

/-- `L₃L₋₃|0⟩ = 2c·|0⟩` — the central term `(c/12)(3³-3) = 2c` of `[L₃, L₋₃]`. -/
theorem Lop_three_L3vac : Lop c 3 (L3vac c) = (2 * c) • vacVec c := by
  have h := Lop_apply_comm c 3 (-3) (vacVec c)
  rw [if_pos (by norm_num : (3 : ℤ) + -3 = 0),
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 3), map_zero,
    show (3 : ℤ) + -3 = 0 from by norm_num,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 0), smul_zero] at h
  push_cast at h
  norm_num at h
  simp only [L3vac]
  rw [h]

/-- `L₃L₋₂L₋₂|0⟩ = 0`. -/
theorem Lop_three_L2L2vac : Lop c 3 (L2L2vac c) = 0 := by
  have h := Lop_apply_comm c 3 (-2) (L2vac c)
  rw [Lop_ge_three_L2vac c (le_refl (3 : ℤ)), map_zero,
    if_neg (by norm_num : ¬((3 : ℤ) + -2 = 0)), zero_smul, add_zero,
    show (3 : ℤ) + -2 = 1 from by norm_num, Lop_one_L2vac, smul_zero, add_zero] at h
  simpa only [L2vac, L2L2vac] using h

/-- `L₄L₋₂L₋₂|0⟩ = 3c·|0⟩`.  This is the level-4 companion of `Lop_four_L4vac`
(`L₄L₋₄|0⟩ = 5c·|0⟩`): the two numbers `3c` and `5c` are the whole second row of the textbook
Kac matrix. -/
theorem Lop_four_L2L2vac : Lop c 4 (L2L2vac c) = (3 * c) • vacVec c := by
  have h := Lop_apply_comm c 4 (-2) (L2vac c)
  rw [Lop_ge_three_L2vac c (by norm_num : (3 : ℤ) ≤ 4), map_zero,
    if_neg (by norm_num : ¬((4 : ℤ) + -2 = 0)), zero_smul, add_zero,
    show (4 : ℤ) + -2 = 2 from by norm_num, Lop_two_L2vac, zero_add] at h
  push_cast at h
  simp only [L2vac, L2L2vac] at h ⊢
  rw [h, smul_smul]
  congr 1
  ring

/-- `LₙL₋₂L₋₂|0⟩ = 0` for `n ≥ 5`: level-4 states are annihilated by every mode that lowers the
weight below `0`.  (`n = 4` is the exception computed above.) -/
theorem Lop_ge_five_L2L2vac {n : ℤ} (hn : 5 ≤ n) : Lop c n (L2L2vac c) = 0 := by
  have h := Lop_apply_comm c n (-2) (L2vac c)
  rw [Lop_ge_three_L2vac c (by omega : (3 : ℤ) ≤ n), map_zero,
    Lop_ge_three_L2vac c (by omega : (3 : ℤ) ≤ n + -2), smul_zero,
    if_neg (by omega : ¬(n + -2 = 0)), zero_smul, add_zero, add_zero] at h
  simpa only [L2vac, L2L2vac] using h

/-- `L₅L₋₁ L₋₂²|0⟩ = 18c·|0⟩`: the `i = 0` term of the iterate expansion of `(L₋₂²|0⟩)₍₇₎`.
By `[L₅,L₋₁] = 6L₄` and `L₅L₋₂²|0⟩ = 0` this is `6·L₄L₋₂²|0⟩ = 6·3c·|0⟩`. -/
theorem Lop_five_neg_one_L2L2vac :
    Lop c 5 (Lop c (-1) (L2L2vac c)) = (18 * c) • vacVec c := by
  have h := Lop_apply_comm c 5 (-1) (L2L2vac c)
  rw [Lop_ge_five_L2L2vac c (by norm_num : (5 : ℤ) ≤ 5), map_zero,
    if_neg (by norm_num : ¬((5 : ℤ) + -1 = 0)), zero_smul, add_zero,
    show (5 : ℤ) + -1 = 4 from by norm_num, Lop_four_L2L2vac, zero_add] at h
  push_cast at h
  rw [h, smul_smul]
  congr 1
  ring

/-! ## §2  The second row of the level-4 Gram matrix, for arbitrary `c`

`Examples/LeeYangGram.smul_L4vac_seven` already proves `(L₋₄|0⟩)₍₇₎ = 21·L₄` **as an operator**,
for every `c`.  Pairing it against `L₋₂²|0⟩` therefore costs nothing beyond `Lop_four_L2L2vac`. -/

/-- The top product `(L₋₄|0⟩)₍₇₎(L₋₂²|0⟩) = 21·L₄L₋₂²|0⟩ = 63c·|0⟩`. -/
theorem smul_L4vac_seven_L2L2vac :
    (virasoroVOA c).smul (L4vac c) 7 (L2L2vac c) = (63 * c) • vacVec c := by
  rw [smul_L4vac_seven, Lop_four_L2L2vac, smul_smul]
  congr 1
  ring

/-- **The off-diagonal Gram entry, for arbitrary central charge**:
`⟨L₋₄|0⟩, L₋₂²|0⟩⟩₄ = 63·c`.

⚠ Not `3c`: as with `shapForm_L4vac_self = 105c`, this is the **top-mode** form `ε(a₍₇₎b)`, and
`L₋₄|0⟩` is not quasi-primary.  Here the top-mode value happens to be exactly `21 × 3c`; §3 shows
that the remaining entry is **not** `21 ×` its textbook counterpart. -/
theorem shapForm_L4vac_L2L2vac (hvac : (virasoroVOA c).vacuum ≠ 0) :
    shapForm (virasoroVOA c) hvac 4 (L4vec4 c) (L2L2vec4 c) = 63 * c := by
  rw [shapForm_eq_iff, show (2 * (4 : ℤ) - 1) = 7 from by norm_num]
  exact smul_L4vac_seven_L2L2vac c

/-- The transpose entry, by symmetry of the top-mode form (`shapForm_symm`). -/
theorem shapForm_L2L2vac_L4vac (hvac : (virasoroVOA c).vacuum ≠ 0) :
    shapForm (virasoroVOA c) hvac 4 (L2L2vec4 c) (L4vec4 c) = 63 * c := by
  rw [shapForm_symm hvac 4 (L2L2vec4 c) (L4vec4 c)]
  exact shapForm_L4vac_L2L2vac c hvac

/-! ## §3  The remaining diagonal entry `⟨L₋₂²|0⟩, L₋₂²|0⟩⟩₄`, for arbitrary `c`

This is the one entry that no operator identity in the repository already delivers.  It needs the
**Borcherds iterate formula** `Core.BorcherdsIdentity.mode_iterate` at `ℓ = -1`:

`L₋₂²|0⟩ = ω₍₋₁₎ω`, so `(L₋₂²|0⟩)₍₇₎ = ∑ᵢ [ ω₍₋₁₋ᵢ₎ω₍₇₊ᵢ₎ + ω₍₆₋ᵢ₎ω₍ᵢ₎ ]`

(the coefficient `(-1)ⁱC(-1,i) = 1` and the sign `-(-1)^{-1} = +1`), i.e. in Virasoro modes
`∑ᵢ [ L₋₂₋ᵢ L₆₊ᵢ + L₅₋ᵢ L_{i-1} ]`. -/

/-- The `i`-th term of the `ℓ = -1` iterate expansion of `(ω₍₋₁₎ω)₍₇₎x`, in Virasoro modes.

The generalized binomial collapses (`gBinom (-1) i = (-1)ⁱ`, so the prefactor
`(-1)ⁱ·C(-1,i) = 1`) and the Borcherds sign is `(-1)^{-1} = -1`, turning the difference into a
sum. -/
theorem iterate_summand (x : VirUniv c) (i : ℕ) :
    (((-1 : ℂ) ^ i * gBinom (-1) i) •
        ((virasoroVOA c).smul (omegaVir c) (-1 - (i : ℤ))
            ((virasoroVOA c).smul (omegaVir c) (7 + (i : ℤ)) x)
          - ((-1 : ℂ) ^ (-1 : ℤ)) • (virasoroVOA c).smul (omegaVir c) (-1 + 7 - (i : ℤ))
            ((virasoroVOA c).smul (omegaVir c) (i : ℤ) x)))
      = Lop c (-2 - (i : ℤ)) (Lop c (6 + (i : ℤ)) x)
        + Lop c (5 - (i : ℤ)) (Lop c ((i : ℤ) - 1) x) := by
  rw [gBinom_neg_one, ← pow_add,
    show ((-1 : ℂ) ^ (i + i)) = 1 from Even.neg_one_pow ⟨i, rfl⟩, one_smul]
  simp only [smul_omegaVir]
  rw [show ((-1 : ℂ) ^ (-1 : ℤ)) = -1 from by norm_num, neg_one_smul, sub_neg_eq_add,
    show ((-1 : ℤ) - (i : ℤ) - 1) = -2 - (i : ℤ) from by ring,
    show ((7 : ℤ) + (i : ℤ) - 1) = 6 + (i : ℤ) from by ring,
    show ((-1 : ℤ) + 7 - (i : ℤ) - 1) = 5 - (i : ℤ) from by ring]

/-! ### The six surviving terms

Only `0 ≤ i ≤ 5` can contribute (`L_{i-1}` kills `L₋₂²|0⟩` for `i ≥ 6`), and of those `i = 4, 5`
vanish as well. -/

/-- `i = 1`:  `L₄L₀L₋₂²|0⟩ = 4·L₄L₋₂²|0⟩ = 12c·|0⟩`. -/
theorem Lop_four_zero_L2L2vac : Lop c 4 (Lop c 0 (L2L2vac c)) = (12 * c) • vacVec c := by
  rw [Lop_zero_L2L2vac, map_smul, Lop_four_L2L2vac, smul_smul]
  congr 1
  ring

/-- `i = 2`:  `L₃L₁L₋₂²|0⟩ = 3·L₃L₋₃|0⟩ = 6c·|0⟩`. -/
theorem Lop_three_one_L2L2vac : Lop c 3 (Lop c 1 (L2L2vac c)) = (6 * c) • vacVec c := by
  rw [Lop_one_L2L2vac, map_smul, Lop_three_L3vac, smul_smul]
  congr 1
  ring

/-- `i = 3`:  `L₂L₂L₋₂²|0⟩ = (c+8)·L₂L₋₂|0⟩ = (c+8)(c/2)·|0⟩`.  This is the only term carrying
`c²`, and it is exactly the textbook contravariant entry `⟨L₋₂²|0⟩,L₋₂²|0⟩⟩ = (c/2)(c+8)`. -/
theorem Lop_two_two_L2L2vac :
    Lop c 2 (Lop c 2 (L2L2vac c)) = ((c + 8) * (c / 2)) • vacVec c := by
  rw [Lop_two_L2L2vac, map_smul, Lop_two_L2vac, smul_smul]

/-- `i = 4`:  `L₁L₃L₋₂²|0⟩ = 0`. -/
theorem Lop_one_three_L2L2vac : Lop c 1 (Lop c 3 (L2L2vac c)) = 0 := by
  rw [Lop_three_L2L2vac, map_zero]

/-- `i = 5`:  `L₀L₄L₋₂²|0⟩ = 3c·L₀|0⟩ = 0`. -/
theorem Lop_zero_four_L2L2vac : Lop c 0 (Lop c 4 (L2L2vac c)) = 0 := by
  rw [Lop_four_L2L2vac, map_smul, Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 0), smul_zero]

/-- **The remaining top product, for arbitrary central charge**:
`(L₋₂²|0⟩)₍₇₎(L₋₂²|0⟩) = (c²/2 + 40c)·|0⟩`.

The five nonzero contributions are `18c + 12c + 6c + (c+8)(c/2) + 0 + 0`. -/
theorem smul_L2L2vac_seven_self :
    (virasoroVOA c).smul (L2L2vac c) 7 (L2L2vac c) = (c ^ 2 / 2 + 40 * c) • vacVec c := by
  have hω : (virasoroVOA c).smul (omegaVir c) (-1) (omegaVir c) = L2L2vac c := by
    rw [smul_omegaVir, show ((-1 : ℤ) - 1) = -2 from by norm_num]
    rfl
  have key := VertexOperatorAlgebra.mode_iterate (virasoroVOA c) (omegaVir c) (omegaVir c)
      (-1) 7 (L2L2vac c)
  rw [hω, finsum_congr (fun i => iterate_summand c (L2L2vac c) i)] at key
  -- The `ω₍₋₁₋ᵢ₎ω₍₇₊ᵢ₎` family dies outright: `L₆₊ᵢ` lowers the weight below `0`.
  have hcollapse : ∀ i : ℕ,
      Lop c (-2 - (i : ℤ)) (Lop c (6 + (i : ℤ)) (L2L2vac c))
          + Lop c (5 - (i : ℤ)) (Lop c ((i : ℤ) - 1) (L2L2vac c))
        = Lop c (5 - (i : ℤ)) (Lop c ((i : ℤ) - 1) (L2L2vac c)) := by
    intro i
    rw [Lop_ge_five_L2L2vac c (by omega : (5 : ℤ) ≤ 6 + (i : ℤ)), map_zero, zero_add]
  rw [finsum_congr hcollapse] at key
  -- and the surviving family is supported on `i < 6`.
  have hsupp : (Function.support fun i : ℕ =>
      Lop c (5 - (i : ℤ)) (Lop c ((i : ℤ) - 1) (L2L2vac c))) ⊆ ↑(Finset.range 6) := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    refine hi ?_
    change Lop c (5 - (i : ℤ)) (Lop c ((i : ℤ) - 1) (L2L2vac c)) = 0
    rw [Lop_ge_five_L2L2vac c (by omega : (5 : ℤ) ≤ (i : ℤ) - 1), map_zero]
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp] at key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, zero_add] at key
  norm_num at key
  rw [Lop_five_neg_one_L2L2vac, Lop_four_zero_L2L2vac, Lop_three_one_L2L2vac,
    Lop_two_two_L2L2vac, Lop_one_three_L2L2vac, Lop_zero_four_L2L2vac] at key
  rw [key]
  module

/-- **The remaining diagonal Gram entry, for arbitrary central charge**:
`⟨L₋₂²|0⟩, L₋₂²|0⟩⟩₄ = c²/2 + 40c`.

⚠⚠ **This is NOT `21 ×` the textbook Kac entry.**  The contravariant value is `(c/2)(c+8)`, whose
`21`-fold is `21c²/2 + 84c`; the two differ by `-2c(5c+22)`, i.e. they agree **only** at `c = 0`
and at `c = -22/5`.  `Examples/LeeYangGram.shapForm_leeYang_level4_eq_kac` is therefore true as
stated — it is stated only at `leeYangC` — but it must **never** be generalised by replacing
`leeYangC` with a variable `c`.  See §4 for what *is* true uniformly in `c`. -/
theorem shapForm_L2L2vac_self (hvac : (virasoroVOA c).vacuum ≠ 0) :
    shapForm (virasoroVOA c) hvac 4 (L2L2vec4 c) (L2L2vec4 c) = c ^ 2 / 2 + 40 * c := by
  rw [shapForm_eq_iff, show (2 * (4 : ℤ) - 1) = 7 from by norm_num]
  exact smul_L2L2vac_seven_self c

/-! ## §4  The level-4 Kac determinant, for arbitrary `c`

Assembling §2 and §3, the level-4 Gram matrix of the **top-mode** form in the basis
`(L₋₂²|0⟩, L₋₄|0⟩)` is

`S(c) = [[ c²/2 + 40c , 63c ], [ 63c , 105c ]]`

⚠ It is **not** `21 ×` the textbook contravariant Kac matrix
`G(c) = [[ (c/2)(c+8) , 3c ], [ 3c , 5c ]]`: the two agree in the second row and column
(`63c = 21·3c`, `105c = 21·5c`) but the `(1,1)` entries differ by
`c²/2 + 40c - 21(c/2)(c+8) = -2c(5c+22)`, which vanishes only at `c = 0` and `c = -22/5`.
What *is* true uniformly in `c` is the statement below: `det S(c) = 21·det G(c)`. -/

/-- The level-4 Gram matrix of the top-mode form in the ordered basis
`(L₋₂²|0⟩, L₋₄|0⟩)` of `𝒱₄`. -/
noncomputable def gram4 (hvac : (virasoroVOA c).vacuum ≠ 0) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![shapForm (virasoroVOA c) hvac 4 (L2L2vec4 c) (L2L2vec4 c),
      shapForm (virasoroVOA c) hvac 4 (L2L2vec4 c) (L4vec4 c);
    shapForm (virasoroVOA c) hvac 4 (L4vec4 c) (L2L2vec4 c),
      shapForm (virasoroVOA c) hvac 4 (L4vec4 c) (L4vec4 c)]

/-- **The level-4 Gram matrix, for arbitrary central charge.** -/
theorem gram4_eq (hvac : (virasoroVOA c).vacuum ≠ 0) :
    gram4 c hvac = !![c ^ 2 / 2 + 40 * c, 63 * c; 63 * c, 105 * c] := by
  rw [gram4, shapForm_L2L2vac_self, shapForm_L2L2vac_L4vac, shapForm_L4vac_L2L2vac,
    shapForm_L4vac_self]

/-- **THE LEVEL-4 KAC DETERMINANT, for arbitrary central charge.**

`det S(c) = (c²/2 + 40c)(105c) - (63c)² = (105/2)c³ + 231c² = 21 · c²(5c+22)/2.`

The bracketed factor `c²(5c+22)/2` is exactly the textbook level-4 **vacuum-module** Kac
determinant `det[[(c/2)(c+8), 3c],[3c, 5c]]`; the overall `21` is the square-root-free part of the
top-mode normalisation (`(L₋₄|0⟩)₍₇₎ = 21·L₄`, `LeeYangGram.smul_L4vac_seven`).  So even though
`S(c) ≠ 21·G(c)` entrywise (§4 preamble), the determinants agree up to that constant, **for every
`c`** — and hence so do the two determinants' zero sets. -/
theorem det_gram4 (hvac : (virasoroVOA c).vacuum ≠ 0) :
    (gram4 c hvac).det = 21 * (c ^ 2 * (5 * c + 22) / 2) := by
  rw [gram4_eq, Matrix.det_fin_two_of]
  ring

/-- The same number as an expanded polynomial: `(105/2)c³ + 231c²`. -/
theorem det_gram4_poly (hvac : (virasoroVOA c).vacuum ≠ 0) :
    (gram4 c hvac).det = 105 / 2 * c ^ 3 + 231 * c ^ 2 := by
  rw [det_gram4]; ring

/-- The determinant statement with **no `Matrix` in sight**, purely in terms of the four Shapovalov
pairings — the form in which the result is usable elsewhere. -/
theorem shapForm_level4_det (hvac : (virasoroVOA c).vacuum ≠ 0) :
    shapForm (virasoroVOA c) hvac 4 (L2L2vec4 c) (L2L2vec4 c)
        * shapForm (virasoroVOA c) hvac 4 (L4vec4 c) (L4vec4 c)
      - shapForm (virasoroVOA c) hvac 4 (L2L2vec4 c) (L4vec4 c)
        * shapForm (virasoroVOA c) hvac 4 (L4vec4 c) (L2L2vec4 c)
      = 21 * (c ^ 2 * (5 * c + 22) / 2) := by
  rw [shapForm_L2L2vac_self, shapForm_L2L2vac_L4vac, shapForm_L4vac_L2L2vac, shapForm_L4vac_self]
  ring

/-! ## §5  The zero set: `c = 0` and `c = -22/5`, and nothing else -/

/-- **The level-4 Kac determinant vanishes exactly at `c = 0` and `c = -22/5`.**

`c = 0` is the double root (`Vir^0` is non-simple at level `2` already: `(p,q) = (2,3)` gives
`(p-1)(q-1) = 2`, and by level `4` the descendants of the null `ω` fill a line); `c = -22/5` is
the Lee–Yang root `c_{2,5}`, with `(p-1)(q-1) = 4`.

This **strengthens** `LeeYangSingular.exists_level4_singular_iff`, which sees only `c = -22/5`:
that theorem asks for a vector killed by `L₁` *and* `L₂`, whereas the determinant sees the whole
radical, and at `c = 0` the radical is nonzero without containing a Virasoro-singular vector of
weight `4`. -/
theorem det_gram4_eq_zero_iff (hvac : (virasoroVOA c).vacuum ≠ 0) :
    (gram4 c hvac).det = 0 ↔ c = 0 ∨ c = leeYangC := by
  rw [det_gram4]
  constructor
  · intro h
    have h2 : c ^ 2 * (5 * c + 22) = 0 := by linear_combination (2 / 21 : ℂ) * h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inl (pow_eq_zero_iff (n := 2) (by norm_num)|>.mp h3)
    · refine Or.inr ?_
      rw [leeYangC]
      linear_combination h3 / 5
  · rintro (rfl | rfl)
    · ring
    · rw [leeYangC]; ring

/-! ### Independent cross-check against `Examples/LeeYangGram`

`LeeYangGram` obtained the two entries `⟨L₋₂²|0⟩,L₋₄|0⟩⟩₄ = -1386/5` and
`⟨L₋₂²|0⟩,L₋₂²|0⟩⟩₄ = -4158/25` **not** by a mode computation but by *solving* `⟨s,·⟩ = 0` from
`leeYangSingular_mem_radBil`.  §2–§3 above reach the same two numbers by a completely independent
route (the operator identity `(L₋₄|0⟩)₍₇₎ = 21L₄`, and the Borcherds iterate formula).  The two
routes agreeing is a genuine check on both — in particular it checks the iterate-formula
bookkeeping of §3 against a value the repository derived from the singular vector.

These are stated as theorems rather than left implicit, so that any future divergence breaks the
build. -/

/-- Cross-check: `c²/2 + 40c` at `c = -22/5` is `-4158/25`, the value
`LeeYangGram.shapForm_L2L2vac_self_leeYang` derives from the singular vector. -/
theorem shapForm_L2L2vac_self_leeYang_agrees :
    shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4
        (L2L2vec4 leeYangC) (L2L2vec4 leeYangC) = -4158 / 25 := by
  rw [shapForm_L2L2vac_self, leeYangC]
  norm_num

/-- Cross-check: `63c` at `c = -22/5` is `-1386/5`, the value
`LeeYangGram.shapForm_L2L2vac_L4vac_leeYang` derives from the singular vector. -/
theorem shapForm_L2L2vac_L4vac_leeYang_agrees :
    shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4
        (L2L2vec4 leeYangC) (L4vec4 leeYangC) = -1386 / 5 := by
  rw [shapForm_L2L2vac_L4vac, leeYangC]
  norm_num

/-! ## §5b  The guard rail: `shapForm` is not a rescaled Kac matrix

`LeeYangGram.shapForm_leeYang_level4_eq_kac` reads, at `c = -22/5`, "the level-4 Gram matrix is
`21 ×` the textbook Kac matrix".  That is true **only** because `-22/5` is a root; the theorem
below records that the `(1,1)` entry disagrees at every other `c` except `0`, so the `leeYangC` in
that statement must never be generalised to a variable. -/

/-- ⚠⚠ **`⟨L₋₂²|0⟩, L₋₂²|0⟩⟩₄ ≠ 21·(c/2)(c+8)` for every `c ∉ {0, -22/5}`.**

The difference is `(c²/2 + 40c) - 21(c/2)(c+8) = -2c(5c+22)`.  So the "Gram matrix `= 21 ×` Kac
matrix" reading of `LeeYangGram.shapForm_leeYang_level4_eq_kac` is a Lee–Yang accident, not a
normalisation. -/
theorem shapForm_L2L2vac_self_ne_kac_rescaled (hvac : (virasoroVOA c).vacuum ≠ 0)
    (hc0 : c ≠ 0) (hcLY : c ≠ leeYangC) :
    shapForm (virasoroVOA c) hvac 4 (L2L2vec4 c) (L2L2vec4 c) ≠ 21 * (c / 2 * (c + 8)) := by
  rw [shapForm_L2L2vac_self]
  intro h
  have h2 : c * (5 * c + 22) = 0 := by linear_combination (-1 / 2 : ℂ) * h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hc0 h3
  · exact hcLY (by rw [leeYangC]; linear_combination h3 / 5)

/-- Every weight-4 state is a combination of `L₋₂²|0⟩` and `L₋₄|0⟩` (`gradingVir_four`, transported
to the subtype `𝒱₄`). -/
theorem exists_level4_coeff (y : (virasoroVOA c).grading 4) :
    ∃ α β : ℂ, y = α • L2L2vec4 c + β • L4vec4 c := by
  have hy : (y : VirUniv c) ∈ Submodule.span ℂ {L2L2vac c, L4vac c} := by
    rw [← gradingVir_four]
    exact y.2
  rw [Submodule.mem_span_pair] at hy
  obtain ⟨α, β, hab⟩ := hy
  refine ⟨α, β, Subtype.ext ?_⟩
  simpa using hab.symm

/-! ## §5c  The converse at generic `c`: no level-4 null vectors at all

If the determinant does not vanish the form is nondegenerate on `𝒱₄` — proved here by hand from
the two linear equations, which is cheaper than invoking a matrix-representation theory. -/

/-- **At `c = 0` the level-4 top-mode form vanishes identically.**

This is the meaning of the *double* root of `det S(c)` at `c = 0`: not a line of null vectors but
the whole of `𝒱₄`.  (Consistently: at `c = 0` the conformal vector `ω` is itself null,
`shapForm_omegaVir_self` gives `⟨ω,ω⟩₂ = 0`, and `𝒱₄` is spanned by `L₋₂ω` and `L₋₁²ω/2`.)

So the two roots of the level-4 Kac determinant are of genuinely different type, and only the
Lee–Yang one carries a Virasoro-singular vector of weight 4. -/
theorem shapForm_level4_eq_zero_at_zero (hvac : (virasoroVOA 0).vacuum ≠ 0) :
    shapForm (virasoroVOA 0) hvac 4 = 0 := by
  ext a b
  obtain ⟨α, β, rfl⟩ := exists_level4_coeff 0 a
  obtain ⟨γ, δ, rfl⟩ := exists_level4_coeff 0 b
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    shapForm_L2L2vac_self, shapForm_L2L2vac_L4vac, shapForm_L4vac_L2L2vac, shapForm_L4vac_self,
    LinearMap.zero_apply]
  ring

/-- **`det ≠ 0 ⟹ the level-4 radical is trivial.**  From `⟨y, L₋₂²|0⟩⟩ = ⟨y, L₋₄|0⟩⟩ = 0` and
Cramer, `α·det = β·det = 0`. -/
theorem radBil_shapForm_eq_bot_of_det_ne_zero (hvac : (virasoroVOA c).vacuum ≠ 0)
    (hdet : (gram4 c hvac).det ≠ 0) :
    DefForm.radBil (shapForm (virasoroVOA c) hvac 4) = ⊥ := by
  rw [det_gram4] at hdet
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨α, β, rfl⟩ := exists_level4_coeff c y
  have e1 := DefForm.mem_radBil.mp hy (L2L2vec4 c)
  have e2 := DefForm.mem_radBil.mp hy (L4vec4 c)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    shapForm_L2L2vac_self, shapForm_L2L2vac_L4vac, shapForm_L4vac_L2L2vac,
    shapForm_L4vac_self] at e1 e2
  have hα : α * (21 * (c ^ 2 * (5 * c + 22) / 2)) = 0 := by
    linear_combination (105 * c) * e1 - (63 * c) * e2
  have hβ : β * (21 * (c ^ 2 * (5 * c + 22) / 2)) = 0 := by
    linear_combination (c ^ 2 / 2 + 40 * c) * e2 - (63 * c) * e1
  have hα0 : α = 0 := by
    rcases mul_eq_zero.mp hα with h | h
    · exact h
    · exact absurd h hdet
  have hβ0 : β = 0 := by
    rcases mul_eq_zero.mp hβ with h | h
    · exact h
    · exact absurd h hdet
  rw [Submodule.mem_bot, hα0, hβ0, zero_smul, zero_smul, add_zero]

/-! ## §6  The rank statement at `c = -22/5`

The `(2,2)` entry `105c = -462 ≠ 0` (`LeeYangGram.leeYangGram_L4vac`) already says the matrix is
nonzero; the determinant says it is singular.  A `2×2` matrix that is nonzero and singular has
rank exactly `1`, so its radical is exactly a **line** — and the singular vector is on it. -/

/-- **The radical of the level-4 form at `c = -22/5` is exactly the line through the singular
vector.**

`⊇` is `LeeYangRigidity.leeYangSingular_mem_radBil`.  `⊆` is the new content: pairing an arbitrary
`y = αL₋₂²|0⟩ + βL₋₄|0⟩` against `L₋₄|0⟩` alone gives `-1386α/5 - 462β = 0`, i.e. `β = -3α/5`,
i.e. `y = (α/5)·s`. -/
theorem radBil_shapForm_leeYang_eq_span :
    DefForm.radBil (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4)
      = Submodule.span ℂ {leeYangSing4} := by
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨α, β, rfl⟩ := exists_level4_coeff leeYangC y
    have h := DefForm.mem_radBil.mp hy (L4vec4 leeYangC)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      shapForm_L2L2vac_L4vac_leeYang, leeYangGram_L4vac] at h
    have hβ : β = -3 * α / 5 := by linear_combination (-1 / 462 : ℂ) * h
    subst hβ
    rw [Submodule.mem_span_singleton]
    refine ⟨α / 5, ?_⟩
    rw [leeYangSing4_eq]
    module
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact leeYangSingular_mem_radBil

/-- The radical is one-dimensional. -/
theorem finrank_radBil_shapForm_leeYang :
    Module.finrank ℂ
        (DefForm.radBil (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4)) = 1 := by
  rw [radBil_shapForm_leeYang_eq_span]
  refine finrank_span_singleton ?_
  intro h
  exact leeYangSingular_ne_zero (congrArg Subtype.val h)

/-- **The level-4 Shapovalov form of `V(-22/5,0)` has rank exactly `1`.**

`dim 𝒱₄ = 2` (`finrank_gradingVir_four`) and `dim ker = 1` (`finrank_radBil_shapForm_leeYang`),
so rank-nullity gives `dim (range) = 1`. -/
theorem rank_shapForm_leeYang_level4 :
    Module.finrank ℂ
        (LinearMap.range (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4)) = 1 := by
  haveI : FiniteDimensional ℂ ((virasoroVOA leeYangC).grading 4) :=
    (virasoroVOA leeYangC).toPreVertexAlgebra.finrank 4
  have hrk := LinearMap.finrank_range_add_finrank_ker
    (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4)
  rw [show LinearMap.ker (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4)
      = DefForm.radBil (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4) from rfl,
    finrank_radBil_shapForm_leeYang,
    show Module.finrank ℂ ((virasoroVOA leeYangC).grading 4) = 2 from
      VirDefLow.finrank_gradingVir_four leeYangC] at hrk
  omega

/-! ## §7  The consequence for the maximal ideal

The bridge from "radical of the level-4 form" to "maximal ideal at level 4" costs one short
argument, and — importantly — **does not need Li's theorem** (`maxGradedIdeal = leftRadical B` for
the FHL invariant form), which this repository does not have.  The reason is that
`RigidBridge.shapForm` is the *top-mode* form `ε(a₍₂ₖ₋₁₎b)`, and `a₍₂ₖ₋₁₎b` is literally a mode of
an ideal element, hence in the ideal:

if `a ∈ I ∩ 𝒱ₖ` and `y ∈ 𝒱ₖ` then `y₍₂ₖ₋₁₎a ∈ I` and `y₍₂ₖ₋₁₎a = ⟨y,a⟩ₖ·𝟙`,
so `⟨y,a⟩ₖ ≠ 0` would force `𝟙 ∈ I`.

The general statement is proved first; it is stated for an arbitrary VOA and belongs in
`Core.RigidityBridge`, but this file may not edit that one. -/

section IdealRadical

variable {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲] {W : VertexOperatorAlgebra 𝒲}

/-- **Every homogeneous element of a proper ideal lies in the radical of the top-mode form of
its own degree.**

This is the (easy, top-mode) half of Li's theorem, and it is the only half the level-4
identification needs.  No invariance, no FHL correction, no quasi-primarity: `y₍₂ₖ₋₁₎a` is a mode
of `a`, so it stays in the ideal, and it equals `⟨y,a⟩ₖ·𝟙`.

⚠ The **converse** (`radBil ⊆ maxGradedIdeal`) is *not* proved here and is genuinely harder — it
is what needs Li's theorem for the FHL invariant form.  At level 4 of Lee–Yang the converse is
supplied instead by the explicit singular vector, which is already known to be in the maximal
ideal. -/
theorem mem_radBil_of_mem_properIdeal (hvac : W.vacuum ≠ 0) {I : Submodule ℂ 𝒲}
    (hI : W.IsIdeal I) (hv : W.vacuum ∉ I) {k : ℤ} (a : W.grading k) (ha : (a : 𝒲) ∈ I) :
    a ∈ DefForm.radBil (shapForm W hvac k) := by
  rw [DefForm.mem_radBil]
  intro y
  by_contra hne
  refine hv ?_
  have hmem : W.smul (y : 𝒲) (2 * k - 1) (a : 𝒲) ∈ I := hI (y : 𝒲) (a : 𝒲) (2 * k - 1) ha
  rw [smul_top_mode_eq hvac y a] at hmem
  have hyz : shapForm W hvac k y a ≠ 0 := by
    rw [shapForm_symm hvac k y a]; exact hne
  have hsm := I.smul_mem (shapForm W hvac k y a)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hyz, one_smul] at hsm

end IdealRadical

/-- **LEVEL-4 NULL COMPLETENESS FOR LEE–YANG.**

`(maxIdeal V(-22/5,0)) ∩ 𝒱₄ = ℂ·s`, with `s = 5L₋₂²|0⟩ - 3L₋₄|0⟩`.

Both inclusions:
* `⊇` is `LeeYangProper.leeYangSingular_mem_maxIdealVir` together with
  `LeeYangSingular.leeYangSingular_mem_grading`;
* `⊆` is `mem_radBil_of_mem_properIdeal` (the maximal graded ideal is proper by
  `QuotVOA.vacuum_not_mem_maxGradedIdeal`) followed by `radBil_shapForm_leeYang_eq_span`.

⚠⚠ **THIS IS A LEVEL-4 STATEMENT AND NOTHING MORE.**  It does **not** prove
`maxIdealVir leeYangC = leeYangWordSpan`, i.e. that the singular vector *generates* the maximal
ideal.  That is an assertion about **every** level `n ≥ 4` simultaneously, and nothing in this
file, or anywhere in this repository, touches levels `≥ 5`:

* at level `5` the analogous statement would need the Gram matrix of `𝒱₅` (`dim = 2`);
* at level `6` it would need `dim 𝒱₆ = 4` — and the repository has **no basis and no dimension
  formula for `𝒱ₙ` at any `n ≥ 5`** (`VirasoroSpanning.negWordVir` is indexed by all of
  `List ℕ`, redundantly: five words have energy `6` but `dim 𝒱₆ = 4`);
* the uniform statement is equivalent to the character identity
  `dim (V/⟨s⟩)ₙ = dim L(-22/5,0)ₙ` for all `n`, i.e. to Rocha-Caridi's formula
  (Rogers–Ramanujan), which no finite computation produces.

`LeeYangProper` records only `leeYangWordSpan ≤ maxIdealVir leeYangC`; the reverse inclusion
remains open, and this theorem does not change that. -/
theorem maxIdealVir_leeYang_inf_grading_four :
    maxIdealVir leeYangC ⊓ gradingVir leeYangC 4 = Submodule.span ℂ {leeYangSingular} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨hxI, hx4⟩ := Submodule.mem_inf.mp hx
    have hmem : (⟨x, hx4⟩ : (virasoroVOA leeYangC).grading 4)
        ∈ DefForm.radBil (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4) :=
      mem_radBil_of_mem_properIdeal leeYang_vacuum_ne_zero
        (maxIdealVir_isIdeal leeYangC)
        (QuotVOA.vacuum_not_mem_maxGradedIdeal (virasoroVOA leeYangC) leeYang_vacuum_ne_zero)
        ⟨x, hx4⟩ hxI
    rw [radBil_shapForm_leeYang_eq_span, Submodule.mem_span_singleton] at hmem
    obtain ⟨t, ht⟩ := hmem
    rw [Submodule.mem_span_singleton]
    exact ⟨t, congrArg Subtype.val ht⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.mem_inf.mpr ⟨leeYangSingular_mem_maxIdealVir, leeYangSingular_mem_grading⟩

/-- The same statement one level up in abstraction: the degree-4 part of the maximal ideal is
`1`-dimensional. -/
theorem finrank_maxIdealVir_leeYang_inf_grading_four :
    Module.finrank ℂ ↥(maxIdealVir leeYangC ⊓ gradingVir leeYangC 4) = 1 := by
  rw [maxIdealVir_leeYang_inf_grading_four]
  exact finrank_span_singleton leeYangSingular_ne_zero

/-- A weight-4 state of `V(-22/5,0)` dies in the simple quotient **iff** it is a multiple of the
singular vector.  (Restatement of `maxIdealVir_leeYang_inf_grading_four`; again level 4 only.) -/
theorem mkQ_eq_zero_iff_level_four {x : VirUniv leeYangC} (hx : x ∈ gradingVir leeYangC 4) :
    (maxIdealVir leeYangC).mkQ x = 0 ↔ ∃ t : ℂ, x = t • leeYangSingular := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hxI
    have : x ∈ maxIdealVir leeYangC ⊓ gradingVir leeYangC 4 := Submodule.mem_inf.mpr ⟨hxI, hx⟩
    rw [maxIdealVir_leeYang_inf_grading_four, Submodule.mem_span_singleton] at this
    obtain ⟨t, ht⟩ := this
    exact ⟨t, ht.symm⟩
  · rintro ⟨t, rfl⟩
    exact Submodule.smul_mem _ t leeYangSingular_mem_maxIdealVir

/-! ## §8  The generic-`c` complement: at every other central charge, level 4 is clean -/

/-- **At every `c ∉ {0, -22/5}` the maximal ideal of `V(c,0)` has no weight-4 part at all.**

Together with `maxIdealVir_leeYang_inf_grading_four` this settles level 4 completely, for every
central charge: the degree-4 part of `maxGradedIdeal` is `ℂ·s` at `c = -22/5` and `⊥` otherwise
(the `c = 0` case is left open here — there the determinant vanishes too, and the level-4 radical
is a line, but the null vector is *not* Virasoro-singular, so the identification of the ideal
would need the level-2 null vector `ω` instead). -/
theorem maxIdealVir_inf_grading_four_eq_bot (hc0 : c ≠ 0) (hcLY : c ≠ leeYangC) :
    maxIdealVir c ⊓ gradingVir c 4 = ⊥ := by
  have hvac : (virasoroVOA c).vacuum ≠ 0 := vacVec_ne_zero c
  have hdet : (gram4 c hvac).det ≠ 0 := by
    rw [Ne, det_gram4_eq_zero_iff]
    rintro (h | h)
    · exact hc0 h
    · exact hcLY h
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxI, hx4⟩ := Submodule.mem_inf.mp hx
  have hmem := mem_radBil_of_mem_properIdeal hvac (maxIdealVir_isIdeal c)
    (QuotVOA.vacuum_not_mem_maxGradedIdeal (virasoroVOA c) hvac) ⟨x, hx4⟩ hxI
  rw [radBil_shapForm_eq_bot_of_det_ne_zero c hvac hdet, Submodule.mem_bot] at hmem
  rw [Submodule.mem_bot]
  exact congrArg Subtype.val hmem


end LeeYangKac

end VOA
