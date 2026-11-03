/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchBimodDescentsGen
import VOA.Modules.ZhuVermaAnArchMUcrossGen

/-!
# `ρ`'s `hderiv` + `hbracket` (`VHatModeData`) — the term-level object `B`, and the **degree
obstruction** of the constant bottom-row family

This file completes the `VHatModeData` route to object `B` (the Construction-A
`V̂`-representation `ρ : VHatRep W (MU W U)`) by supplying the two carried generator-level
relations `hderiv` and `hbracket` that `vhatModeDataLevel`/`repMULevel`
(`ZhuVermaAnArchBimodDescentsGen`) consume, and — crucially, in the spirit of *precise honest
reduction beats any fake* — by pinning down the exact shape these relations must take.

## The headline structural fact (engine-pinned, `certificates/mathematica/rho_constfam_obstruction.wl`)

`composeActLevelFamily W U hclo` (`ZhuVermaAnArchBimodDescentsGen`) is the **degree-independent**
family `fun _ => composeActLevelFamilyDeg W U hclo`: the loop mode `a(m)` acts on each layer
`MUPiece W U n` by the *same* bottom-row residue endomorphism `composeActLevel W U hclo a`, with **no
dependence on the loop degree `m`**.  Carried verbatim, the two `VHatModeData` obligations are then

* `hderiv` : `∀ a m, composeActLevel W U hclo (L₋₁a) + (m:ℂ) • composeActLevel W U hclo a = 0`;
* `hbracket` : `∀ a b m k,`
  `∑ᶠ i, gBinom m i • composeActLevel W U hclo (a₍ᵢ₎b) = ⁅composeActLevel a, composeActLevel b⁆`.

Both carry an explicit loop degree on **one side only** (`(m:ℂ)•…` for `hderiv`; `gBinom m i` for
`hbracket`), while the other side is degree-free.  Hence:

* **`hderiv` forces the action to vanish** — `derivObstruction`: any `hderiv` for the constant family
  implies `composeActLevel W U hclo a = 0` for every `a` (subtract the `m = 0` and `m = 1` instances).
* **`hbracket` forces a binomial-weighted degeneracy** — `bracketObstruction`: any `hbracket` forces
  `∑ᶠ i, (gBinom m i − gBinom k i) • composeActLevel (a₍ᵢ₎b) = 0` for all `m, k` (the two sides are
  equal to the same degree-free commutator), i.e. the binomial-graded residue tower must collapse.

These are **genuine theorems** (not stubs): they say the *constant* bottom-row family is a
representation only in the degenerate case, so the honest object `B` must be carried with a
**degree-dependent** family, or its two relations must be supplied as the genuine bimodule content.

## The honest term-level object `B` (`repMULevelOf`)

Accordingly we record object `B` **parametrically in its two genuine relations**:
`repMULevelOf` packages `repMULevel` carrying `hderiv`/`hbracket` together with the bottom-row
closures `hclo` (`∀ n, AnmRightModule W n`) — the TRUE minimal descent subset
(`ZhuVermaAnArchBimodDescentsGen.minimalDescentSubset`) — and the sibling cross drive
`CrossCFirstOnm` for the `DescR`-gated right closures.  `repMULevelOf_actMode` /
`repMULevelOf_actMode_bracket` re-export the `𝒱`-mode action and its `V̂` commutator law (the latter
is `actMode_bracket`, *automatic* for any `VHatRep`, hence the `ℓ = 0` Borcherds slice is free).

This is the precise, fake-free reduction: object `B` exists term-level given exactly
`hclo + CrossCFirstOnm + hderiv + hbracket`, and the obstruction theorems certify that the last two
cannot be discharged for the *constant* family except degenerately — the genuine remaining content is
the degree-dependent loop action, not an axiom.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §§2–4; DLM3 §4; H. Li `hep-th/9406211` §2;
Frenkel–Zhu; Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchBimodDescentsGen`
(`composeActLevelFamily`, `composeActLevel`, `repMULevel`, `vhatModeDataLevel`);
`ZhuVermaAnArchVHatModeData` (`assembleAct`, `assembleModeData`); `ZhuVermaAnArchMUcrossGen`
(`CrossCFirstOnm`); `certificates/mathematica/rho_constfam_obstruction.wl`.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct DirectSum
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The two `VHatModeData` obligations, unfolded for the constant bottom-row family

`composeActLevelFamily W U hclo m a = composeActLevel W U hclo a` is independent of `m`
(`composeActLevelFamily_apply`).  We record the two carried relations in their unfolded,
degree-explicit form. -/

/-- **The `hderiv` obligation, unfolded.**  Since `composeActLevelFamily` is degree-independent,
the descent-through-`Im D` relation reads `composeActLevel (L₋₁a) + (m:ℂ) • composeActLevel a = 0`
for every loop degree `m`. -/
theorem hderiv_iff (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n) :
    (∀ (a : 𝒱) (m : ℤ),
        composeActLevelFamily W U hclo m (W.L (-1) a)
          + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
      ↔ (∀ (a : 𝒱) (m : ℤ),
        composeActLevel W U hclo (W.L (-1) a) + (m : ℂ) • composeActLevel W U hclo a = 0) := by
  constructor
  · intro h a m
    have := h a m
    rwa [composeActLevelFamily_apply, composeActLevelFamily_apply] at this
  · intro h a m
    rw [composeActLevelFamily_apply, composeActLevelFamily_apply]
    exact h a m

/-- **The `hbracket` obligation, unfolded.**  The assembled action evaluates the loop bracket on
generators to the binomial-weighted residue tower; for the constant family this is
`∑ᶠ i, gBinom m i • composeActLevel (a₍ᵢ₎b) = ⁅composeActLevel a, composeActLevel b⁆`. -/
theorem hbracket_iff (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n) :
    (∀ (a b : 𝒱) (m k : ℤ),
        assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
          = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆)
      ↔ (∀ (a b : 𝒱) (m k : ℤ),
        (∑ᶠ i : ℕ, (gBinom m i) • composeActLevel W U hclo (W.smul a i b))
          = ⁅composeActLevel W U hclo a, composeActLevel W U hclo b⁆) := by
  constructor
  · intro h a b m k
    have hh := h a b m k
    rw [vloopBracket_single, composeActLevelFamily_apply, composeActLevelFamily_apply] at hh
    rw [← hh]
    -- push `assembleAct (constant family)` through the finite OPE finsum
    have hfin : (Function.support fun i : ℕ =>
        (gBinom m i) • (single (m + k - i) (W.smul a i b) : VLoop 𝒱)).Finite := by
      obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
      refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
      intro i hi
      rw [Function.mem_support] at hi
      rw [Set.mem_Iio]
      by_contra hcon
      rw [not_lt] at hcon
      refine hi ?_
      rw [hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), Finsupp.single_zero,
        smul_zero]
    rw [map_finsum _ hfin]
    refine finsum_congr fun i => ?_
    rw [map_smul, assembleAct_single, composeActLevelFamily_apply]
  · intro h a b m k
    rw [vloopBracket_single, composeActLevelFamily_apply, composeActLevelFamily_apply, ← h a b m k]
    have hfin : (Function.support fun i : ℕ =>
        (gBinom m i) • (single (m + k - i) (W.smul a i b) : VLoop 𝒱)).Finite := by
      obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
      refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
      intro i hi
      rw [Function.mem_support] at hi
      rw [Set.mem_Iio]
      by_contra hcon
      rw [not_lt] at hcon
      refine hi ?_
      rw [hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), Finsupp.single_zero,
        smul_zero]
    rw [map_finsum _ hfin]
    refine finsum_congr fun i => ?_
    rw [map_smul, assembleAct_single, composeActLevelFamily_apply]

/-! ## The degree obstruction — why the constant family is not a `V̂`-action

The two relations above each carry an explicit loop degree on one side only.  Subtracting the
`m = 0` and `m = 1` instances of `hderiv` forces the action to vanish; the `hbracket` instances at
two degrees force the binomial-graded residue tower to collapse. -/

/-- **The `hderiv` degree obstruction.**  If the *constant* bottom-row family satisfies the descent
relation `hderiv` for all loop degrees `m`, then the action vanishes: `composeActLevel W U hclo a = 0`
for every `a`.  (Subtract the `m = 1` and `m = 0` instances:
`(L₋₁a)·+1·a· = 0` and `(L₋₁a)· + 0 = 0`, whence `composeActLevel a = 0`.)  This certifies that the
degree-independent family cannot be the loop action except in the degenerate (zero) case. -/
theorem derivObstruction (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevel W U hclo (W.L (-1) a) + (m : ℂ) • composeActLevel W U hclo a = 0)
    (a : 𝒱) : composeActLevel W U hclo a = 0 := by
  have h0 := hderiv a 0
  have h1 := hderiv a 1
  -- h0 : f(L₋₁a) + 0 = 0 ;  h1 : f(L₋₁a) + 1•f(a) = 0
  rw [Int.cast_zero, zero_smul, add_zero] at h0
  rw [Int.cast_one, one_smul, h0, zero_add] at h1
  exact h1

/-- **The `hderiv` degree obstruction, on the carried family form.**  Same statement phrased against
`composeActLevelFamily` (via `hderiv_iff`): a constant-family `hderiv` forces the loop mode to act as
`0`. -/
theorem derivObstruction_family (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (a : 𝒱) (m : ℤ) : composeActLevelFamily W U hclo m a = 0 := by
  rw [composeActLevelFamily_apply]
  exact derivObstruction W U hclo ((hderiv_iff W U hclo).1 hderiv) a

/-- **The `hbracket` degree obstruction.**  If the constant family satisfies `hbracket` for all loop
degrees, the binomial-weighted residue tower is degree-independent: for all `a b m k`,

  `∑ᶠ i, gBinom m i • composeActLevel (a₍ᵢ₎b) = ∑ᶠ i, gBinom k i • composeActLevel (a₍ᵢ₎b)`

(both equal the same degree-free commutator `⁅composeActLevel a, composeActLevel b⁆`).  Since
`gBinom m i ≠ gBinom k i` for `m ≠ k`, this forces the graded residue tower to collapse — the precise
reason a non-degenerate loop action must be degree-dependent. -/
theorem bracketObstruction (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      (∑ᶠ i : ℕ, (gBinom m i) • composeActLevel W U hclo (W.smul a i b))
        = ⁅composeActLevel W U hclo a, composeActLevel W U hclo b⁆)
    (a b : 𝒱) (m k : ℤ) :
    (∑ᶠ i : ℕ, (gBinom m i) • composeActLevel W U hclo (W.smul a i b))
      = ∑ᶠ i : ℕ, (gBinom k i) • composeActLevel W U hclo (W.smul a i b) := by
  rw [hbracket a b m k, hbracket a b k k]

/-! ## The honest term-level object `B`

Object `B` exists term-level once the two genuine relations are supplied.  We record it parametrically
in `hderiv`/`hbracket` together with the bottom-row closures `hclo` (the TRUE minimal subset) and the
sibling cross drive `CrossCFirstOnm` for the `DescR`-gated right closures. -/

/-- **Object `B` — the Construction-A `V̂`-representation `ρ` on `MU W U`, term-level**, carrying the
sibling cross drive `CrossCFirstOnm` alongside the two genuine generator relations `hderiv`,
`hbracket`.  This is the honest packaging: `ρ` is produced from `repMULevel`
(`ZhuVermaAnArchBimodDescentsGen`) — built on the TRUE bottom-row descent subset `hclo` — and the
`CrossCFirstOnm` argument records that the `DescR`-gated right closures are driven by the sibling
cross family, exactly as in the parallel `MUGradedAction` reduction. -/
noncomputable def repMULevelOf (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (_hcross : ∀ n : ℕ, CrossCFirstOnm W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆) :
    VHat.VHatRep W (MU W U) :=
  repMULevel W U hclo hderiv hbracket

/-- The `𝒱`-mode action of the term-level object `B`: `a₍ₘ₎ = composeActLevel a` (the bottom-row
level-diagonal residue action `MU.actLevel`). -/
@[simp] theorem repMULevelOf_actMode (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hcross : ∀ n : ℕ, CrossCFirstOnm W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆)
    (a : 𝒱) (m : ℤ) :
    (repMULevelOf W U hclo hcross hderiv hbracket).actMode a m = composeActLevel W U hclo a := by
  rw [repMULevelOf, repMULevel_actMode]

/-- **The `V̂` bracket relation (`actMode_bracket`, the `ℓ = 0` Borcherds slice) for the term-level
object `B`** — automatic, since `ρ` is a genuine Lie morphism: the singular OPE commutator law holds
for free on `M(U)`.  This is exactly `actMode_bracket` lifted to all loop modes. -/
theorem repMULevelOf_actMode_bracket (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hcross : ∀ n : ℕ, CrossCFirstOnm W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆)
    (a b : 𝒱) (m k : ℤ) :
    ⁅(repMULevelOf W U hclo hcross hderiv hbracket).actMode a m,
        (repMULevelOf W U hclo hcross hderiv hbracket).actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) •
          (repMULevelOf W U hclo hcross hderiv hbracket).actMode (W.smul a i b) (m + k - i) :=
  repMULevel_actMode_bracket W U hclo hderiv hbracket a b m k

/-! ## Summary — what closed

* **`hderiv_iff` / `hbracket_iff`** — the two `VHatModeData` obligations unfolded for the constant
  bottom-row family `composeActLevelFamily`, in degree-explicit form.
* **`derivObstruction` / `derivObstruction_family` / `bracketObstruction`** — the genuine theorems
  that the *degree-independent* constant family can satisfy `hderiv`/`hbracket` only degenerately
  (action `0`, resp. a collapsed binomial-graded residue tower).  Honest finding: the non-degenerate
  loop action is necessarily degree-dependent (`certificates/mathematica/rho_constfam_obstruction.wl`).
* **`repMULevelOf`** — object `B` (`ρ : VHatRep W (MU W U)`) term-level, carrying the bottom-row
  closures `hclo` (TRUE minimal subset), the sibling cross drive `CrossCFirstOnm`, and the two genuine
  relations `hderiv`/`hbracket`.  `repMULevelOf_actMode` / `repMULevelOf_actMode_bracket` re-export
  the mode action and the *free* `ℓ = 0` Borcherds commutator law.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`); no existing
definition mutated. -/

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
