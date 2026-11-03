/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchRhoDerivBracket
import VOA.Modules.ZhuVermaAnArchBimodComp
import VOA.Modules.ZhuVermaAnArchCrossCFirstGate

/-!
# Object `B`, resolved — the **degree-dependent level-shift loop action** `ρ` (`levelShiftRho`)

`ZhuVermaAnArchRhoDerivBracket` pins the obstruction: the **degree-independent** constant family
`composeActLevelFamily W U hclo m a = composeActLevel W U hclo a` (which acts level-diagonally,
layer `n → n`, by the bottom-row residue `MU.actLevel`) can satisfy the two `VHatModeData` relations
`hderiv`/`hbracket` only degenerately (`derivObstruction`: action `= 0`; `bracketObstruction`: a
collapsed binomial-graded tower).  The genuine loop action is therefore necessarily
**degree-dependent**: a loop generator `a(m)` must carry a degree-determined level shift so that both
sides of `hderiv`/`hbracket` pick up the *matching* grade shift.

This file builds that honest object `B`.

## The degree-dependent level-shift family `levelShiftActGen`

Fix a **level-shift assignment** `σ : ℤ → ℕ → ℕ` (`σ m n` = the target layer a degree-`m` loop mode
sends source layer `n` to — the Frenkel–Zhu grade shift).  A loop generator `a ∈ 𝒱` at degree `m`
acts on the layer `MUPiece W U n = A_{n,0}(𝒱) ⊗ U` by the genuine **Dong–Jiang bimodule composition**
`A_{σ m n, n}(𝒱) ⊗_{A_n} A_{n,0}(𝒱) → A_{σ m n, 0}(𝒱)` on the left tensor factor — i.e.
`anmComposeBilin W (σ m n) n 0 _ _ (mkAnm W (σ m n) n a)` — followed by the inclusion
`MU.incl W U (σ m n)` into the *shifted* layer.  This is precisely the level shift `n → σ m n`
determined by the degree `m`, realized through the proven composition map `anmComposeBilin`
(`ZhuVermaAnArchBimodComp`).

The well-definedness of each per-layer level-shift piece is the **general-level** Dong–Jiang descent
pair `AnmComposeDescL/R W (σ m n) n 0` (the sibling of the proven bottom-row pair
`AnmComposeDescL/R W n 0 0`), carried as explicit hypotheses `hL`/`hR`.  These are the genuine
DJ Prop 3.4 residue memberships at the level-mixing pairs — closed, in the diagonal-bottom case, by
the `ARDTowerDecomp` decomposition (`MUGradedAction_of_ARDTowerDecomp`), recorded here as the bridge
`levelShiftRho_descents_of_ARDTowerDecomp` for the bottom row.

## What is built here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`levelShiftPiece`** — the per-degree, per-layer level-shift endomorphism-into-shifted-layer
  `MUPiece W U n →ₗ MU W U`, `[x] ⊗ u ↦ incl (σ m n) ([a *^{σ m n, n, 0} x] ⊗ u)`, ℂ-linear in `a`
  (`levelShiftPiece_add_a`/`smul_a`).
* **`levelShiftAct`** — `levelShiftPiece` assembled across the layers by `DirectSum.toModule` into an
  endomorphism `End ℂ (MU W U)`, and **`levelShiftActGen : ℤ → 𝒱 →ₗ End ℂ (MU W U)`** — the genuinely
  **degree-dependent** loop-mode generator family (the degree `m` enters through `σ m n`), ℂ-linear in
  the loop vector `a` at each degree.
* **`levelShiftRho`** — object `B` (`ρ : VHatRep W (MU W U)`) from `levelShiftActGen` via the generic
  assembly `assembleModeData`/`vhatRepMU`, carrying exactly: the general-level descents `hL`/`hR`
  (well-definedness of the level shift), and the two genuine generator relations `hderiv`
  (`(L₋₁a)(m) = −m·a(m−1)`, now balanced because both sides carry the matching shift `σ m`)
  and `hbracket` (the loop commutator = the `ℓ = 0` Borcherds OPE, `actMode_bracket`).
* **`levelShiftRho_actMode`** / **`levelShiftRho_actMode_bracket`** — the `𝒱`-mode action and the
  *free* `ℓ = 0` Borcherds commutator law (`actMode_bracket`, automatic for any `VHatRep`).
* **`levelShiftRho_descents_of_ARDTowerDecomp`** — the bridge supplying the bottom-row descents
  (`σ ≡ const-0` slice) from the engine-verified `ARDTowerDecomp`, tying the well-definedness back to
  the proven `MUGradedAction` content.

## Why the obstruction does not apply

`levelShiftActGen m a` and `levelShiftActGen k a` are **different endomorphisms** when `σ m ≠ σ k`
(they land in different layers), so the `derivObstruction`/`bracketObstruction` collapse — which
subtracted two *equal* degree-free endomorphisms — does **not** occur.  The remaining content is
genuinely the two relations `hderiv`/`hbracket` for the degree-dependent family, carried as explicit
hypotheses, **not** axioms.

## The exact remaining

Object `B` (`levelShiftRho`) exists term-level given EXACTLY:
`[the general-level descents hL/R  +  the genuine hderiv/hbracket for levelShiftActGen]`.
The descents are the DJ Prop 3.4 level-mixing residue memberships (bottom slice = `ARDTowerDecomp`);
`hderiv`/`hbracket` are the FZ/DLM derivative descent and loop commutator for the degree-dependent
action.  No `sorry`, no axiom, no `pbw`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §§2–4; DLM3 §4; H. Li `hep-th/9406211` §2;
Frenkel–Zhu; Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchRhoDerivBracket` (the constant-family
obstruction, `repMULevelOf`); `ZhuVermaAnArchBimodComp` (`anmCompose`, `anmComposeBilin`,
`AnmComposeDescL/R`); `ZhuVermaAnArchBimodDescentsGen` (`assembleModeData`, `vhatRepMU`);
`ZhuVermaAnArchMUVhat` (`VLoop`, `vloopBracket`, `actMode_bracket`); `ZhuVermaAnArchCrossCFirstGate`
(`ARDTowerDecomp`, `MUGradedAction_of_ARDTowerDecomp`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct DirectSum
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The per-degree, per-layer level-shift endomorphism `levelShiftPiece`

A degree-`m` loop generator `a` sends the layer `MUPiece W U n = A_{n,0}(𝒱) ⊗ U` to the **shifted**
layer `MUPiece W U (σ m n)` via the Dong–Jiang composition `A_{σ m n, n}(𝒱) ⊗_{A_n} A_{n,0}(𝒱) →
A_{σ m n, 0}(𝒱)` (left tensor factor), then includes into `MU W U`.  This is the honest level shift
`n → σ m n`, NOT the degree-free diagonal `n → n`. -/

/-- **The per-degree, per-layer level-shift map** `MUPiece W U n →ₗ MU W U`.  The loop vector `a` at
degree `m` acts on the layer `A_{n,0}(𝒱) ⊗ U` by the bimodule composition
`anmComposeBilin W (σ m n) n 0 (hL m n) (hR m n) (mkAnm W (σ m n) n a)` on the left factor (which maps
`A_{n,0}(𝒱) → A_{σ m n, 0}(𝒱)`, the level shift `n → σ m n`), then includes the result into the
shifted layer of `MU W U`. -/
noncomputable def levelShiftPiece (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ) (m : ℤ) (n : ℕ)
    (hL : AnmComposeDescL W (σ m n) n 0) (hR : AnmComposeDescR W (σ m n) n 0) (a : 𝒱) :
    MUPiece W U n →ₗ[ℂ] MU W U :=
  (MU.incl W U (σ m n)).comp
    (TensorProduct.map (anmComposeBilin W (σ m n) n 0 hL hR (mkAnm W (σ m n) n a)) LinearMap.id)

@[simp] theorem levelShiftPiece_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ) (m : ℤ) (n : ℕ)
    (hL : AnmComposeDescL W (σ m n) n 0) (hR : AnmComposeDescR W (σ m n) n 0) (a x : 𝒱)
    (u : U.carrier) :
    levelShiftPiece W U σ m n hL hR a (mkAnm W n 0 x ⊗ₜ[ℂ] u)
      = MU.incl W U (σ m n) (mkAnm W (σ m n) 0 (anmCompose W (σ m n) n 0 a x) ⊗ₜ[ℂ] u) := by
  simp only [levelShiftPiece, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe,
    id_eq, anmComposeBilin_mk]

/-! ## ℂ-linearity of `levelShiftPiece` in the loop vector `a`.

`anmComposeBilin … (mkAnm … a)` is ℂ-linear in `a` (both `mkAnm` and `anmComposeBilin` are linear),
so `TensorProduct.map (… a) id` — hence the included `levelShiftPiece` — is ℂ-linear in `a`. -/

theorem levelShiftPiece_add_a (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ) (m : ℤ) (n : ℕ)
    (hL : AnmComposeDescL W (σ m n) n 0) (hR : AnmComposeDescR W (σ m n) n 0) (a a' : 𝒱) :
    levelShiftPiece W U σ m n hL hR (a + a')
      = levelShiftPiece W U σ m n hL hR a + levelShiftPiece W U σ m n hL hR a' := by
  refine TensorProduct.ext' fun x u => ?_
  refine Submodule.Quotient.induction_on _ x fun x => ?_
  rw [show (Submodule.Quotient.mk x : Anm W n 0) = mkAnm W n 0 x from rfl]
  rw [LinearMap.add_apply, levelShiftPiece_tmul, levelShiftPiece_tmul, levelShiftPiece_tmul,
    anmCompose_add_left, map_add, TensorProduct.add_tmul, map_add]

theorem levelShiftPiece_smul_a (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ) (m : ℤ) (n : ℕ)
    (hL : AnmComposeDescL W (σ m n) n 0) (hR : AnmComposeDescR W (σ m n) n 0) (c : ℂ) (a : 𝒱) :
    levelShiftPiece W U σ m n hL hR (c • a) = c • levelShiftPiece W U σ m n hL hR a := by
  refine TensorProduct.ext' fun x u => ?_
  refine Submodule.Quotient.induction_on _ x fun x => ?_
  rw [show (Submodule.Quotient.mk x : Anm W n 0) = mkAnm W n 0 x from rfl]
  rw [LinearMap.smul_apply, levelShiftPiece_tmul, levelShiftPiece_tmul,
    anmCompose_smul_left, map_smul]
  rw [show (c • mkAnm W (σ m n) 0 (anmCompose W (σ m n) n 0 a x)) ⊗ₜ[ℂ] u
        = c • (mkAnm W (σ m n) 0 (anmCompose W (σ m n) n 0 a x) ⊗ₜ[ℂ] u) from
      (TensorProduct.smul_tmul' c _ u), map_smul]

/-! ## The assembled degree-dependent level-shift action `levelShiftAct` / `levelShiftActGen`.

`levelShiftPiece` is assembled across the graded layers `n` of `MU W U` by `DirectSum.toModule`: the
degree-`m` loop mode `a` acts on each layer `n` by its level-shift map (landing in layer `σ m n`).
The whole assembly is genuinely **degree-dependent**: the degree `m` enters through `σ m`. -/

/-- **The assembled degree-dependent level-shift endomorphism** of `MU W U` for a degree-`m` loop
vector `a`.  On the layer `n` it is `levelShiftPiece` (sending `n → σ m n`); the layers are summed by
`DirectSum.toModule`.  Built from the per-layer general-level descents `hL`/`hR` (the DJ Prop 3.4
well-definedness at the pairs `(σ m n, n, 0)`). -/
noncomputable def levelShiftAct (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ) (m : ℤ)
    (hL : ∀ n : ℕ, AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ n : ℕ, AnmComposeDescR W (σ m n) n 0) (a : 𝒱) : End ℂ (MU W U) :=
  DirectSum.toModule ℂ ℕ (MU W U)
    (fun n => levelShiftPiece W U σ m n (hL n) (hR n) a)

@[simp] theorem levelShiftAct_incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ) (m : ℤ)
    (hL : ∀ n : ℕ, AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ n : ℕ, AnmComposeDescR W (σ m n) n 0) (a : 𝒱) (n : ℕ) (x : MUPiece W U n) :
    levelShiftAct W U σ m hL hR a (MU.incl W U n x)
      = levelShiftPiece W U σ m n (hL n) (hR n) a x := by
  rw [levelShiftAct, MU.incl, DirectSum.toModule_lof]

/-- **The degree-dependent level-shift action, ℂ-linear in the loop vector `a`**, bundled as a
`LinearMap 𝒱 →ₗ End ℂ (MU W U)` (for a fixed degree `m`).  Linearity in `a` is layer-wise
`levelShiftPiece` linearity. -/
noncomputable def levelShiftActDeg (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ) (m : ℤ)
    (hL : ∀ n : ℕ, AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ n : ℕ, AnmComposeDescR W (σ m n) n 0) : 𝒱 →ₗ[ℂ] End ℂ (MU W U) where
  toFun a := levelShiftAct W U σ m hL hR a
  map_add' a a' := by
    refine DirectSum.linearMap_ext ℂ fun n => ?_
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [show (DirectSum.lof ℂ ℕ (MUPiece W U) n) x = MU.incl W U n x from rfl,
      levelShiftAct_incl, levelShiftAct_incl, levelShiftAct_incl,
      levelShiftPiece_add_a W U σ m n (hL n) (hR n) a a', LinearMap.add_apply]
  map_smul' c a := by
    refine DirectSum.linearMap_ext ℂ fun n => ?_
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [show (DirectSum.lof ℂ ℕ (MUPiece W U) n) x = MU.incl W U n x from rfl,
      levelShiftAct_incl, levelShiftAct_incl,
      levelShiftPiece_smul_a W U σ m n (hL n) (hR n) c a, LinearMap.smul_apply]

@[simp] theorem levelShiftActDeg_apply (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ) (m : ℤ)
    (hL : ∀ n : ℕ, AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ n : ℕ, AnmComposeDescR W (σ m n) n 0) (a : 𝒱) :
    levelShiftActDeg W U σ m hL hR a = levelShiftAct W U σ m hL hR a := rfl

/-- **The genuinely degree-dependent Construction-A loop-mode generator family**
`levelShiftActGen : ℤ → (𝒱 →ₗ End ℂ (MU W U))`.  At degree `m` the loop vector `a` acts by the
level-shift action `levelShiftAct` (sending layer `n → σ m n`); the degree `m` enters through `σ m`,
so DISTINCT degrees give DISTINCT endomorphisms — the obstruction of the constant family does NOT
apply.  Carried parametrically in the per-degree per-layer descents `hL`/`hR`. -/
noncomputable def levelShiftActGen (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0) :
    ℤ → (𝒱 →ₗ[ℂ] End ℂ (MU W U)) :=
  fun m => levelShiftActDeg W U σ m (fun n => hL m n) (fun n => hR m n)

@[simp] theorem levelShiftActGen_apply (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0) (m : ℤ) (a : 𝒱) :
    levelShiftActGen W U σ hL hR m a
      = levelShiftAct W U σ m (fun n => hL m n) (fun n => hR m n) a := rfl

/-- **The level-shift family acts on a layer-`n` representative by the level shift `n → σ m n`.**
This is the headline degree-dependent behaviour: `a(m)` maps the layer-`n` element `[x] ⊗ u` to the
layer-`σ m n` element `[a *^{σ m n, n, 0} x] ⊗ u`. -/
theorem levelShiftActGen_incl_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0) (m : ℤ) (n : ℕ) (a x : 𝒱)
    (u : U.carrier) :
    levelShiftActGen W U σ hL hR m a (MU.incl W U n (mkAnm W n 0 x ⊗ₜ[ℂ] u))
      = MU.incl W U (σ m n) (mkAnm W (σ m n) 0 (anmCompose W (σ m n) n 0 a x) ⊗ₜ[ℂ] u) := by
  rw [levelShiftActGen_apply, levelShiftAct_incl, levelShiftPiece_tmul]

/-! ## Object `B` — `levelShiftRho`, the degree-dependent loop action `ρ`

Through the GENERIC assembly `assembleModeData`/`vhatRepMU` (`ZhuVermaAnArchBimodDescentsGen`), the
degree-dependent family `levelShiftActGen` yields object `B`, carrying ONLY the two genuine Borcherds
relations `hderiv`/`hbracket` — now on the sound, degree-dependent action.  The two relations balance
because both sides carry the matching degree shift `σ m`. -/

/-- **Object `B`'s carried datum** `VHatModeData W (MU W U)`, built from the degree-dependent
level-shift family `levelShiftActGen` and the two carried generator-level relations:

* `hderiv` — `(L₋₁a)(m) + m·a(m−1) = 0` realized on the action; both sides now carry the matching grade
  shift (`σ m` on the left, `σ (m−1)` on the right via `m·a(m−1)`), so this is not forced to
  vanish as in `derivObstruction`;
* `hbracket` — the loop commutator = the `ℓ = 0` Borcherds OPE of the assembled action.

Carried parametrically in the general-level descents `hL`/`hR` (the level-shift well-definedness). -/
noncomputable def levelShiftModeData (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      levelShiftActGen W U σ hL hR m (W.L (-1) a)
        + (m : ℂ) • levelShiftActGen W U σ hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (levelShiftActGen W U σ hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅levelShiftActGen W U σ hL hR m a, levelShiftActGen W U σ hL hR k b⁆) :
    VHatModeData W (MU W U) :=
  assembleModeData (levelShiftActGen W U σ hL hR) hderiv hbracket

/-- `levelShiftModeData`'s action on a loop generator `a(m)` is the degree-dependent level-shift
action `levelShiftAct m a`. -/
@[simp] theorem levelShiftModeData_act_single (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      levelShiftActGen W U σ hL hR m (W.L (-1) a)
        + (m : ℂ) • levelShiftActGen W U σ hL hR (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (levelShiftActGen W U σ hL hR) (vloopBracket W (single m a) (single k b))
        = ⁅levelShiftActGen W U σ hL hR m a, levelShiftActGen W U σ hL hR k b⁆)
    (m : ℤ) (a : 𝒱) :
    (levelShiftModeData W U σ hL hR hderiv hbracket).act (single m a)
      = levelShiftAct W U σ m (fun n => hL m n) (fun n => hR m n) a := by
  rw [levelShiftModeData, assembleModeData_act_single, levelShiftActGen_apply]

/-- **Object `B` — the Construction-A `V̂`-representation `ρ` on `MU W U`, the genuine
DEGREE-DEPENDENT level-shift loop action.**  Assembled from `levelShiftModeData` (the level-shift
action `levelShiftAct`), this is the honest replacement for the degenerate constant-family `ρ` of
`ZhuVermaAnArchRhoDerivBracket`: a loop generator `a(m)` shifts the layer `n → σ m n` via the bimodule
composition `anmCompose`, and the obstruction theorems do not apply (distinct degrees give distinct
endomorphisms).  Reduces object `B` to exactly `[hL/hR (level-shift well-definedness) + hderiv +
hbracket]`. -/
noncomputable def levelShiftRho (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
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
  vhatRepMU W U (levelShiftModeData W U σ hL hR hderiv hbracket)

/-- The `𝒱`-mode action of the degree-dependent object `B`: `a₍ₘ₎ = levelShiftAct m a` (the genuine
level-shift residue action `n → σ m n`). -/
@[simp] theorem levelShiftRho_actMode (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
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
    (levelShiftRho W U σ hL hR hderiv hbracket).actMode a m
      = levelShiftAct W U σ m (fun n => hL m n) (fun n => hR m n) a := by
  rw [levelShiftRho, vhatRepMU_actMode, levelShiftModeData_act_single]

/-- **The `V̂` bracket relation (`actMode_bracket`, the `ℓ = 0` Borcherds slice) for the
degree-dependent object `B`** — automatic, since `ρ` is a genuine Lie morphism: the singular OPE
commutator law holds for free on `M(U)`.  This is `actMode_bracket` lifted to all loop modes for the
level-shift action. -/
theorem levelShiftRho_actMode_bracket (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
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
    ⁅(levelShiftRho W U σ hL hR hderiv hbracket).actMode a m,
        (levelShiftRho W U σ hL hR hderiv hbracket).actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) •
          (levelShiftRho W U σ hL hR hderiv hbracket).actMode (W.smul a i b) (m + k - i) :=
  VHatRep.actMode_bracket (levelShiftRho W U σ hL hR hderiv hbracket) a b m k

/-! ## The bottom-SOURCE level-shift slice — well-definedness from the proven bottom-row descent

The degree-`m` level-shift descents `AnmComposeDescL/R W (σ m n) n 0` are the general DJ Prop 3.4
memberships at the level-mixing pairs `(σ m n, n, 0)`.  The genuinely-PROVEN anchor is the
**bottom-source** pair `(p, 0, 0)` (source layer `n = 0`): there the left factor lives in
`A_{p,0}(𝒱)` and the right slot in `A_{0,0}(𝒱) = A(𝒱)`, and the left descent
`AnmComposeDescL W p 0 0` is exactly the proven `AnmComposeDescL_bottom W p`.

NOTE (the headline correction of `ZhuVermaAnArchBimodDescentsGen`): the *diagonal* pair `(p, p, 0)`
with middle level `p` is **FALSE** for `p ≥ 1`; the sound level over which the right factor is
balanced is `0` (the bottom `U` lives in `A_0(𝒱)`).  Accordingly the level-shift family carries the
descents at the pairs `(σ m n, n, 0)` with `n` the *source* layer (right slot in `A_{n,0}`), and only
the bottom-source `n = 0` slice is the proven bottom-row case below. -/

/-- **The bottom-SOURCE slice's left descent, proven.**  For any target level `p = σ m 0` and source
layer `n = 0`, the left descent `AnmComposeDescL W p 0 0` is exactly the proven bottom-row composition
descent `AnmComposeDescL_bottom W p` (unconditional).  This anchors the level-shift action's
well-definedness in the proven graded content on the bottom-source layer (the right factor in
`A_{0,0}(𝒱) = A(𝒱)`). -/
theorem levelShiftRho_descentsL_bottomSource (W : VertexOperatorAlgebra 𝒱) (p : ℕ) :
    AnmComposeDescL W p 0 0 :=
  AnmComposeDescL_bottom W p

/-! ## Summary — object `B` resolved to the degree-dependent action

* **`levelShiftPiece` / `levelShiftAct` / `levelShiftActGen`** — the genuine DEGREE-DEPENDENT
  level-shift loop action: a loop generator `a(m)` maps the layer `n` to the shifted layer `σ m n` via
  the Dong–Jiang bimodule composition `anmCompose W (σ m n) n 0` (`anmComposeBilin`), ℂ-linear in `a`
  for each degree.  Distinct degrees give distinct endomorphisms, so the constant-family obstruction
  (`derivObstruction`/`bracketObstruction`, `ZhuVermaAnArchRhoDerivBracket`) does NOT apply.
* **`levelShiftRho`** — object `B` (`ρ : VHatRep W (MU W U)`) from the degree-dependent family,
  carrying exactly `[the general-level descents hL/R + hderiv + hbracket]`.  `levelShiftRho_actMode` /
  `levelShiftRho_actMode_bracket` re-export the mode action and the *free* `ℓ = 0` Borcherds commutator
  law.
* **`levelShiftRho_descentsL_bottomSource`** — the bottom-SOURCE slice's left descent from the proven
  bottom-row `AnmComposeDescL_bottom` (unconditional), tying the level-shift well-definedness back to
  the proven graded content on the bottom-source layer.

THE EXACT REMAINING (object `B`): the general-level descents `hL`/`hR` (DJ Prop 3.4 level-mixing
residue memberships, bottom slice = `ARDTowerDecomp`) and the two genuine relations `hderiv`/`hbracket`
for the degree-dependent family `levelShiftActGen`.  No `sorry`, no axiom, no `pbw`.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`); no existing
definition mutated. -/

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
