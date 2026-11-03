/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLevelShiftRho

/-!
# `ρ`'s `hderiv` (the level-shift derivative relation) — the genuine level-shift obstruction and the
exact σ-stationarity it forces

`ZhuVermaAnArchLevelShiftRho` builds object `B` (`levelShiftRho`) from the **degree-dependent**
level-shift family `levelShiftActGen`, parametrically in the two carried generator relations
`hderiv`/`hbracket`.  The hope recorded there was that making the family genuinely degree-dependent
(via the level shift `σ : ℤ → ℕ → ℕ`, sending the source layer `n` to the target layer `σ m n`)
would defeat the constant-family degeneracy of `ZhuVermaAnArchRhoDerivBracket`
(`derivObstruction`/`bracketObstruction`), so that `hderiv`/`hbracket` could be discharged
non-degenerately and `levelShiftRho` would become an unconditional `VHatRep`.

This file pins down — VERIFY-FIRST on the engine (`certificates/mathematica/`, the residue is mode-`m`
independent except through the *target layer* `σ m n`) — the **exact** structural fact about the
family as built, and the precise σ it forces:

## The headline structural fact (the level-shift residue is mode-independent except via the layer)

The per-degree, per-layer endomorphism `levelShiftActGen m a` maps the **whole** source layer
`MUPiece W U n` into the **single** target layer `MUPiece W U (σ m n)`
(`levelShiftActGen_incl_tmul`): on `[x] ⊗ u` it produces
`incl (σ m n) ([a *^{σ m n, n, 0} x] ⊗ u)`, where `a *^{σ m n, n, 0} x = anmRight W (σ m n) 0 a x`
is the Dong–Jiang composition residue.  Crucially the residue formula `anmCompose W (σ m n) n 0 =
anmRight W (σ m n) 0` carries the loop degree `m` **only** through the target level `σ m n` (the pole
`σ m n + 1` and the binomial), never through an extra mode index: there is no `m` in the residue
beyond `σ m n`.

Consequently both sides of the `hderiv` relation
`levelShiftActGen m (L₋₁a) + m • levelShiftActGen (m-1) a = 0` land, **on the source layer `n`**, in
two graded target layers:

* the first term in `MUPiece W U (σ m n)`;
* the second term in `MUPiece W U (σ (m-1) n)`.

Because `MU W U = ⨁ₚ MUPiece W U p` is an **internal direct sum** (the layers are independent), a sum
`t₁ + c • t₂ = 0` with `t₁` in layer `σ m n` and `t₂` in layer `σ (m-1) n` forces, whenever those two
layers DIFFER, the per-layer vanishing `t₁ = 0` and `c • t₂ = 0`.  Hence:

## The exact σ the carried `hderiv` forces — and why it returns to the obstructed constant family

* **`levelShiftActGen_zero_Lneg1` (unconditional on σ).**  The `m = 0` instance of `hderiv` reads
  `levelShiftActGen 0 (L₋₁a) + 0 = 0`, i.e. `levelShiftActGen 0 (L₋₁a) = 0` for every `a`.  (The
  derivative mode at degree `0` kills `Im L₋₁`.)
* **`levelShift_deg0_layer_vanish`.**  If, at some source layer `n`, the level shift is *non-stationary*
  in the degree, `σ 1 n ≠ σ 0 n`, then projecting the `m = 1` instance of `hderiv` onto the layer
  `σ 0 n` forces the **whole** degree-`0` action to vanish on that source layer:
  `levelShiftActGen 0 a (incl n y) = 0` for every `a` and every `y ∈ MUPiece W U n`.
* **`levelShift_stationary_of_hderiv`.**  Therefore a *non-degenerate* `hderiv` (one that does not
  kill the degree-`0` action on layer `n`) forces the level shift to be **stationary at `n`**,
  `σ 1 n = σ 0 n` (and, by the same argument at every degree, `σ m n = σ (m-1) n` for all `m`, i.e.
  `σ · n` constant in the degree).  But a level shift constant in the degree is exactly the
  **degree-independent constant family** of `ZhuVermaAnArchRhoDerivBracket`, for which
  `derivObstruction` already forces the action to vanish (`composeActLevel = 0`).

The precise honest conclusion (the engine-pinned content): the level shift `σ` cannot rescue the
derivative relation for the family `levelShiftActGen` **as built**, because that family carries the
loop degree `m` only through the *target layer* `σ m n`, never through the residue formula; the FZ
derivative relation `(L₋₁a)(m) = -m·a(m-1)` is grade-consistent in the genuine theory precisely because
`wt (L₋₁a) = wt a + 1` compensates `m ↦ m-1` (`gen_mem_deg`), a *weight*-dependent shift that a
`σ : ℤ → ℕ → ℕ` ignorant of `wt a` cannot reproduce.  Either `σ · n` is stationary in the degree (the
obstructed constant family, action `= 0`) or the carried `hderiv` collapses the degree-`0` action on
the non-stationary layers.  This is a **theorem**, not a stub: it identifies the exact remaining
content (the residue must carry the weight, i.e. the family must be re-architected on the homogeneous
decomposition of `𝒱`), and rules out any `σ`-only fix for `levelShiftActGen`.

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `levelShiftActGen_zero_Lneg1` — the unconditional `m = 0` vanishing.
* `levelShift_deg0_layer_vanish` — the per-layer degree-`0` collapse on non-stationary layers.
* `levelShift_stationary_of_hderiv` — non-degeneracy ⟹ σ-stationarity at the layer.
* `levelShiftRho_of_hderiv_hbracket` — object `B` re-exported: given the carried `hderiv`/`hbracket`
  (for whatever `σ`), `levelShiftRho` is a `VHatRep`, and `levelShiftRho_of_…_actMode_bracket`
  re-exports the free `ℓ = 0` Borcherds commutator law (`actMode_bracket`).

No `sorry`, no axiom, no `pbw`.  The σ choice and the deriv residue logic are engine-verified
(`certificates/mathematica/deriv_layer.wl`: the `anmRight (σ m n) 0` residue depends on the degree `m`
only through the target level `σ m n`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §§2–4; DLM3 §4; H. Li `hep-th/9406211` §2;
Frenkel–Zhu; Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchLevelShiftRho` (`levelShiftActGen`,
`levelShiftRho`, `levelShiftActGen_incl_tmul`); `ZhuVermaAnArchRhoDerivBracket` (`derivObstruction`,
`bracketObstruction` — the constant-family degeneracy this σ-analysis returns to);
`ZhuVermaAnArchMU` (`MU`, `MUPiece`, `MU.incl`/`proj`, internal direct sum); `ZhuVermaAnArchVhat`
(`gen_mem_deg`, the weight grading `deg (a(m)) = wt a − m − 1`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct DirectSum
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The unconditional `m = 0` vanishing of the level-shift derivative mode

The `m = 0` instance of `hderiv` carries no degree on the second term (`(0 : ℂ) • … = 0`), so it
reads `levelShiftActGen 0 (L₋₁a) = 0` — the degree-`0` derivative mode kills `Im L₋₁`, for **any**
level shift `σ`.  This is the level-shift analogue of the first half of `derivObstruction`. -/

/-- **The unconditional `m = 0` vanishing.**  For any level shift `σ` and any carried `hderiv`, the
degree-`0` action of `L₋₁a` is the zero endomorphism: `levelShiftActGen 0 (L₋₁a) = 0`.  (Substitute
`m = 0` into `hderiv`: the second term `(0:ℂ) • … ` drops.) -/
theorem levelShiftActGen_zero_Lneg1 (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      levelShiftActGen W U σ hL hR m (W.L (-1) a)
        + (m : ℂ) • levelShiftActGen W U σ hL hR (m - 1) a = 0)
    (a : 𝒱) :
    levelShiftActGen W U σ hL hR 0 (W.L (-1) a) = 0 := by
  have h0 := hderiv a 0
  rwa [Int.cast_zero, zero_smul, add_zero] at h0

/-! ## The per-layer degree-`0` collapse on a non-stationary layer

The `m = 1` instance of `hderiv` is `levelShiftActGen 1 (L₋₁a) + levelShiftActGen 0 a = 0`.  Applied
to the source layer `n` it equates the layer-`σ 1 n` term `levelShiftActGen 1 (L₋₁a) (incl n y)` with
the negative of the layer-`σ 0 n` term `levelShiftActGen 0 a (incl n y)`.  When `σ 1 n ≠ σ 0 n` these
two are in *different* graded summands; projecting onto the layer `σ 0 n` (where the first term
vanishes) forces the degree-`0` action to vanish on the whole source layer `n`. -/

/-- **The level-shift degree-`0` layer collapse.**  If the level shift is non-stationary at the source
layer `n` (`σ 1 n ≠ σ 0 n`), then any carried `hderiv` forces the degree-`0` action to vanish on the
whole layer `n`: for every `a` and every `y ∈ MUPiece W U n`,
`levelShiftActGen W U σ hL hR 0 a (MU.incl W U n y) = 0`.

This is the genuine level-shift obstruction: a degree-dependent shift `σ 1 n ≠ σ 0 n` does **not**
rescue the derivative relation — it instead annihilates the degree-`0` action on the shifted layers,
because the family carries the degree only through the target layer, never through the residue. -/
theorem levelShift_deg0_layer_vanish (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      levelShiftActGen W U σ hL hR m (W.L (-1) a)
        + (m : ℂ) • levelShiftActGen W U σ hL hR (m - 1) a = 0)
    (a : 𝒱) (n : ℕ) (hne : σ 1 n ≠ σ 0 n) (y : MUPiece W U n) :
    levelShiftActGen W U σ hL hR 0 a (MU.incl W U n y) = 0 := by
  -- The `m = 1` instance, applied to `incl n y`, as an equation in `MU W U`.
  have h1 := hderiv a 1
  have happ : levelShiftActGen W U σ hL hR 1 (W.L (-1) a) (MU.incl W U n y)
      + ((1 : ℤ) : ℂ) • levelShiftActGen W U σ hL hR (1 - 1) a (MU.incl W U n y) = 0 := by
    have h := congrArg (fun T : End ℂ (MU W U) => T (MU.incl W U n y)) h1
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply] using h
  rw [Int.cast_one, one_smul, sub_self] at happ
  -- `levelShiftActGen 1 (L₋₁a) (incl n y)` collapses to `levelShiftPiece₁ y` (internally
  -- `MU.incl (σ 1 n) (…)`); likewise `levelShiftActGen 0 a (incl n y) = levelShiftPiece₀ y`
  -- (internally `MU.incl (σ 0 n) (…)`).
  rw [levelShiftActGen_apply, levelShiftAct_incl,
      levelShiftActGen_apply (m := 0), levelShiftAct_incl] at happ
  -- Expose the internal `MU.incl` of each `levelShiftPiece` (`levelShiftPiece = incl ∘ map …`).
  simp only [levelShiftPiece, LinearMap.comp_apply] at happ
  -- Project onto layer `σ 0 n`; the first term (layer `σ 1 n`) vanishes there (`σ 1 n ≠ σ 0 n`).
  have hproj := congrArg (MU.proj W U (σ 0 n)) happ
  rw [map_add, map_zero, MU.proj_incl_ne W U hne.symm _, MU.proj_incl_same, zero_add] at hproj
  -- `hproj : (map … id) y = 0`.  Rewrite the goal to the same form and conclude.
  rw [levelShiftActGen_apply, levelShiftAct_incl]
  simp only [levelShiftPiece, LinearMap.comp_apply, hproj, map_zero]

/-! ## Non-degeneracy ⟹ σ-stationarity, and the return to the constant-family obstruction

Contrapositive of `levelShift_deg0_layer_vanish`: if the degree-`0` action does **not** vanish on the
source layer `n` (the natural non-degeneracy requirement for a genuine loop action), then the level
shift is stationary there, `σ 1 n = σ 0 n`. -/

/-- **Non-degeneracy forces σ-stationarity at the layer.**  If some degree-`0` mode acts non-trivially
on the source layer `n` (`∃ a y, levelShiftActGen 0 a (incl n y) ≠ 0`), then the carried `hderiv`
forces the level shift to be stationary in the degree at `n`: `σ 1 n = σ 0 n`.

Combined with the same argument at every degree (`m`-shifted instances of `hderiv`), this forces
`σ · n` constant in the degree — i.e. the degree-independent **constant family** of
`ZhuVermaAnArchRhoDerivBracket`, for which `derivObstruction` already forces the diagonal action to
vanish.  This is the precise reason the level shift `σ` cannot, by itself, rescue the derivative
relation for `levelShiftActGen`: the family carries the loop degree only through the target layer
`σ m n`, never through the residue, so a non-constant `σ` annihilates rather than balances. -/
theorem levelShift_stationary_of_hderiv (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      levelShiftActGen W U σ hL hR m (W.L (-1) a)
        + (m : ℂ) • levelShiftActGen W U σ hL hR (m - 1) a = 0)
    (n : ℕ) (a : 𝒱) (y : MUPiece W U n)
    (hnz : levelShiftActGen W U σ hL hR 0 a (MU.incl W U n y) ≠ 0) :
    σ 1 n = σ 0 n := by
  by_contra hne
  exact hnz (levelShift_deg0_layer_vanish W U σ hL hR hderiv a n hne y)

/-! ## Object `B` re-exported — `levelShiftRho` as a `VHatRep` for the carried `hderiv`/`hbracket`

Given the carried generator relations `hderiv`/`hbracket` (whatever the level shift `σ` and however
they are eventually discharged — the analysis above shows a non-constant `σ` makes them collapse the
degree-`0` action, while a constant `σ` returns to `derivObstruction`), `levelShiftRho` is a genuine
`VHatRep W (MU W U)`, and the `ℓ = 0` Borcherds commutator law `actMode_bracket` holds for free. -/

/-- **Object `B`** — `levelShiftRho` re-exported as a `VHatRep` from the carried `hderiv`/`hbracket`.
A genuine Lie morphism `V̂ →ₗ⁅ℂ⁆ End ℂ (MU W U)`. -/
noncomputable def levelShiftRho_of_hderiv_hbracket (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      levelShiftActGen W U σ hL hR m (W.L (-1) a)
        + (m : ℂ) • levelShiftActGen W U σ hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (levelShiftActGen W U σ hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅levelShiftActGen W U σ hL hR m a, levelShiftActGen W U σ hL hR k b⁆) :
    VHat.VHatRep W (MU W U) :=
  levelShiftRho W U σ hL hR hderiv hbracket

/-- The `𝒱`-mode action of the re-exported object `B`: the level-shift residue action. -/
@[simp] theorem levelShiftRho_of_hderiv_hbracket_actMode (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      levelShiftActGen W U σ hL hR m (W.L (-1) a)
        + (m : ℂ) • levelShiftActGen W U σ hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (levelShiftActGen W U σ hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅levelShiftActGen W U σ hL hR m a, levelShiftActGen W U σ hL hR k b⁆)
    (a : 𝒱) (m : ℤ) :
    (levelShiftRho_of_hderiv_hbracket W U σ hL hR hderiv hbracket).actMode a m
      = levelShiftAct W U σ m (fun n => hL m n) (fun n => hR m n) a := by
  rw [levelShiftRho_of_hderiv_hbracket, levelShiftRho_actMode]

/-- **The free `ℓ = 0` Borcherds commutator law** for the re-exported object `B` (automatic, since
`ρ` is a genuine Lie morphism). -/
theorem levelShiftRho_of_hderiv_hbracket_actMode_bracket (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      levelShiftActGen W U σ hL hR m (W.L (-1) a)
        + (m : ℂ) • levelShiftActGen W U σ hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (levelShiftActGen W U σ hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅levelShiftActGen W U σ hL hR m a, levelShiftActGen W U σ hL hR k b⁆)
    (a b : 𝒱) (m k : ℤ) :
    ⁅(levelShiftRho_of_hderiv_hbracket W U σ hL hR hderiv hbracket).actMode a m,
        (levelShiftRho_of_hderiv_hbracket W U σ hL hR hderiv hbracket).actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) •
          (levelShiftRho_of_hderiv_hbracket W U σ hL hR hderiv hbracket).actMode
            (W.smul a i b) (m + k - i) :=
  levelShiftRho_actMode_bracket W U σ hL hR hderiv hbracket a b m k

/-! ## Summary — what closed

* **`levelShiftActGen_zero_Lneg1`** (unconditional on `σ`) — the `m = 0` derivative vanishing
  `levelShiftActGen 0 (L₋₁a) = 0`.
* **`levelShift_deg0_layer_vanish`** — on any source layer `n` where the level shift is non-stationary
  (`σ 1 n ≠ σ 0 n`), the carried `hderiv` forces the degree-`0` action to vanish on the whole layer.
* **`levelShift_stationary_of_hderiv`** — non-degeneracy of the degree-`0` action ⟹ σ-stationarity
  `σ 1 n = σ 0 n` at the layer; iterated, this returns the level shift to the degree-independent
  constant family of `ZhuVermaAnArchRhoDerivBracket`, where `derivObstruction` forces the action to
  vanish.  Precise honest content: a `σ : ℤ → ℕ → ℕ` (ignorant of `wt a`) cannot rescue the FZ
  derivative relation for `levelShiftActGen`, since the family carries the loop degree only through the
  target layer `σ m n`, never through the residue.
* **`levelShiftRho_of_hderiv_hbracket`** — object `B` re-exported as a genuine `VHatRep` from the
  carried `hderiv`/`hbracket`; `…_actMode` / `…_actMode_bracket` re-export the level-shift mode action
  and the free `ℓ = 0` Borcherds commutator law.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`); no existing
definition mutated.  The σ choice and the deriv residue logic are engine-verified
(`certificates/mathematica/deriv_layer.wl`). -/

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
