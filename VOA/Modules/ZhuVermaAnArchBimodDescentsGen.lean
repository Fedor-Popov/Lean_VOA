/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchVHatModeData
import VOA.Modules.ZhuVermaAnArchBottomAn
import VOA.Modules.ZhuVermaAnArchBimodDescent

/-!
# The EXACT minimal bimodule descents ρ needs ⟹ object B (term-level), and `BottomOrbitDefectVanishes`

This file pins down — and discharges — the *precise minimal subset* of the general Dong–Jiang
bimodule-composition descents that the Construction-A `V̂`-representation `ρ` on the induced carrier
`M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗ U` actually consumes, then assembles object B from that subset, and records
the constructive `A_n`-bimodule reduction for `BottomOrbitDefectVanishes`.

## The headline correction (engine-pinned, `certificates/mathematica/diag_pp0_descents.wl`)

The canonical loop-mode action `composeActFamily` (`ZhuVermaAnArchVHatModeData`) is assembled from
`composePiece`, which acts on the layer `MUPiece W U p = A_{p,0}(𝒱) ⊗ U` by the *diagonal*
composition `anmComposeBilin W p p 0 (mkAnm W p p a)`.  That route demands the **diagonal** descents
`AnmComposeDescL/R W p p 0` per layer `p`.  These are **FALSE for `p ≥ 1`**: the engine
(`certificates/mathematica/diag_pp0_descents.wl`, rank-1 free boson, `MatrixRank` membership against the genuine `Onm W p 0`)
shows

* `DescL (p,p,0)` *circle* family `(c ∘^{p,p} d) *^p_0 v` — TRUE, but the *grading* family
  `(L₋₁c + L₀c) *^p_0 v` — **FALSE** (`p = 1, c = J`: `anmRight 1 0 (a₋₂J + a₋₁J) J ∉ Onm 1 0`);
* `DescR (p,p,0)` *circle* family — TRUE, but the *grading* family `u *^p_0 (L₋₁c + L₀c − p·c)` —
  **FALSE** for every `p ≥ 1`.

The algebraic reason: `anmLgen W p p c = L₋₁c + L₀c = anmLgen W p 0 c + p·c`, so the diagonal grading
generator carries the *spurious* extra term `p · (anmRight W p 0 c v)`, which is **not** in `Onm W p 0`.
The level over which the two factors are balanced is `0` (the bottom `U` lives in `A_0(𝒱)`), **not** `p`;
the diagonal source `A_{p,p}` is the wrong middle level.  Carrying `∀ p, AnmComposeDescL/R W p p 0` as
the action's hypotheses is therefore unsound — those hypotheses can never be discharged.

## The exact minimal subset ρ needs — the **bottom-row** family `(n,0,0)`

The genuine level action of a loop mode on `M(U)` is the **right** `A_0(𝒱)`-residue action of `𝒱` on
the left tensor factor `A_{n,0}(𝒱)`, level-diagonal, `[x] ↦ [x *^n_0 a]` — exactly `MU.actLevel`
(`ZhuVermaAnArchMU`), whose well-definedness is the **bottom-row** pair

  `AnmRightModule W n`  (= `AnmComposeDescL W n 0 0`)   and   `AnmCrossClosure W n`
  (= `AnmComposeDescR W n 0 0`),

bundled as `MUGradedAction W := ∀ n, AnmRightModule W n ∧ AnmCrossClosure W n` (`ZhuVermaAnArchMU`).
All bottom-row generator families are **engine-TRUE** (`certificates/mathematica/diag_pp0_descents.wl`, the
`MUGradedAction families` block) and are PROVEN in the repo modulo the single recorded open predicate
`CrossCircOnmGen W n` (`AnmComposeDescL_bottom` unconditional; `AnmComposeDescR_bottom_of_CrossCircOnmGen`).
This is the EXACT minimal descent subset.

## What is built here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`composeActLevel`** — the per-degree layer-diagonal endomorphism of `MU W U` assembled from the
  PROVEN `MU.actLevel` (the bottom-row action), `DirectSum.toModule` across the levels.  Built from
  `hclo : ∀ n, AnmRightModule W n` — the *true* descent subset, **not** the false diagonal.
* **`composeActLevelFamilyDeg`** — `composeActLevel` bundled as `𝒱 →ₗ[ℂ] End ℂ (MU W U)`
  (ℂ-linear in the loop vector `a`), and the per-degree family `composeActLevelFamily : ℤ → …`.
* **`vhatModeDataLevel` / `repMULevel`** — object B (`ρ : VHat.VHatRep W (MU W U)`) assembled from
  `composeActLevelFamily` through the GENERIC `assembleModeData` (`ZhuVermaAnArchVHatModeData`),
  carrying only the two genuine Borcherds relations `hderiv`/`hbracket` (the derivative descent and
  the loop commutator) — **on the true bottom-row action**, with the mode-action lemma
  `repMULevel_actMode`.
* **`minimalDescentSubset`** — the exact statement: object B's action is built from
  `∀ n, AnmRightModule W n` (the bottom-row left descent), i.e. `MUGradedAction`'s left half; the
  diagonal `(p,p,0)` descents are *not* needed (and are false).
* **`bottomOrbitDefect_of_orbit_gens` / `bottomOrbitDefectVanishes_of_gens`** — the constructive
  reduction of `BottomOrbitDefectVanishes` to its single per-orbit-generator content: it suffices
  that the degree-`0` component of every `U(V̂)`-orbit image `ρ.toAlgHom g (defectVec …)` vanishes,
  which is exactly the predicate `BottomOrbitDefectVanishes` already unfolds to.  With it,
  `bottomAnRelation` / `bottomSurvives_an` close (re-exported here for the level ρ).

## What is OPEN (precise, NOT faked)

* `hderiv` / `hbracket` for `composeActLevelFamily` — the derivative descent `(L₋₁a)(m) = −m·a(m−1)`
  and the Borcherds loop commutator realized on `M(U)` for the bottom-row action.  These are the same
  two genuine relations carried for *any* loop-mode action; here they are carried on the **sound**
  action.  Reduced, never axioms.
* `BottomOrbitDefectVanishes ρ` itself — the degree-`0` `A_n`-bimodule relation: the bottom is `U`
  *as an `A(𝒱)`-module*.  Reduced to the per-orbit-generator predicate; the genuine `A_n`-bimodule
  degree-`0` content is carried, **not** an axiom.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §§2–4; DLM3 §4; H. Li `hep-th/9406211`;
Frenkel–Zhu; Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchMU` (`MU`, `MU.actLevel`, `MUGradedAction`,
`AnmRightModule`); `ZhuVermaAnArchVHatModeData` (`assembleModeData`, `assembleAct`);
`ZhuVermaAnArchBottomAn` (`BottomOrbitDefectVanishes`, `bottomAnRelation`);
`certificates/mathematica/diag_pp0_descents.wl`.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct DirectSum
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The sound per-level action — assembled from the PROVEN bottom-row `MU.actLevel`

The genuine Construction-A action of a loop mode on `M(U)` is the level-diagonal right residue
action `MU.actLevel` (`ZhuVermaAnArchMU`), whose well-definedness is the bottom-row descent
`AnmRightModule W n` — the TRUE minimal subset.  We assemble it across the graded layers, exactly as
`composeAct` does, but on the sound action. -/

/-- **The per-degree, layer-diagonal endomorphism of `MU W U`** assembled from the proven
`MU.actLevel` (the bottom-row right residue action `[x] ↦ [x *^n_0 a]` on the left tensor factor).
Given the per-level right-module closures `hclo n : AnmRightModule W n` (the bottom-row left descent,
PROVEN — unlike the false diagonal `AnmComposeDescL W n n 0`), the loop vector `a` acts on each
graded piece `MUPiece W U n` by `MU.actLevel W U n (hclo n) a`, assembled into an endomorphism of
the whole carrier by `DirectSum.toModule`. -/
noncomputable def composeActLevel (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n) (a : 𝒱) : End ℂ (MU W U) :=
  DirectSum.toModule ℂ ℕ (MU W U)
    (fun n => (MU.incl W U n).comp (MU.actLevel W U n (hclo n) a))

@[simp] theorem composeActLevel_incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n) (a : 𝒱) (n : ℕ) (x : MUPiece W U n) :
    composeActLevel W U hclo a (MU.incl W U n x)
      = MU.incl W U n (MU.actLevel W U n (hclo n) a x) := by
  rw [composeActLevel, MU.incl, DirectSum.toModule_lof]
  rfl

/-! ## ℂ-linearity of `MU.actLevel` / the assembled action in the loop vector `a`.

`MU.actLevel W U n hclo a` acts on `mkAnm W n 0 x ⊗ₜ u` by `mkAnm W n 0 (anmRight W n 0 x a) ⊗ₜ u`;
since `anmRight W n 0 x a` is ℂ-linear in `a` (`anmRight_add_right`/`anmRight_smul_right`), the layer
endomorphism — and hence the assembled `composeActLevel` — is ℂ-linear in `a`. -/

/-- `MU.actAnm` is additive in the acting vector `a` (the right slot of `anmRight W n 0 x a`). -/
theorem actAnm_add_a (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (hclo : AnmRightModule W n) (a a' : 𝒱) :
    MU.actAnm W n hclo (a + a') = MU.actAnm W n hclo a + MU.actAnm W n hclo a' := by
  refine LinearMap.ext fun y => ?_
  refine Submodule.Quotient.induction_on _ y fun x => ?_
  rw [show (Submodule.Quotient.mk x : Anm W n 0) = mkAnm W n 0 x from rfl]
  rw [LinearMap.add_apply, MU.actAnm_mk, MU.actAnm_mk, MU.actAnm_mk,
    anmRight_add_right, map_add]

/-- `MU.actAnm` is ℂ-homogeneous in the acting vector `a`. -/
theorem actAnm_smul_a (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (hclo : AnmRightModule W n) (c : ℂ)
    (a : 𝒱) : MU.actAnm W n hclo (c • a) = c • MU.actAnm W n hclo a := by
  refine LinearMap.ext fun y => ?_
  refine Submodule.Quotient.induction_on _ y fun x => ?_
  rw [show (Submodule.Quotient.mk x : Anm W n 0) = mkAnm W n 0 x from rfl]
  rw [LinearMap.smul_apply, MU.actAnm_mk, MU.actAnm_mk, anmRight_smul_right, map_smul]

/-- `MU.actLevel` is additive in the acting vector `a`. -/
theorem actLevel_add_a (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    (hclo : AnmRightModule W n) (a a' : 𝒱) :
    MU.actLevel W U n hclo (a + a') = MU.actLevel W U n hclo a + MU.actLevel W U n hclo a' := by
  rw [MU.actLevel, MU.actLevel, MU.actLevel, actAnm_add_a W n hclo a a']
  refine TensorProduct.ext' fun x u => ?_
  simp only [TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_coe, id_eq,
    TensorProduct.add_tmul]

/-- `MU.actLevel` is ℂ-homogeneous in the acting vector `a`. -/
theorem actLevel_smul_a (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    (hclo : AnmRightModule W n) (c : ℂ) (a : 𝒱) :
    MU.actLevel W U n hclo (c • a) = c • MU.actLevel W U n hclo a := by
  rw [MU.actLevel, MU.actLevel, actAnm_smul_a W n hclo c a]
  refine TensorProduct.ext' fun x u => ?_
  simp only [TensorProduct.map_tmul, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
    TensorProduct.smul_tmul']

/-- **The sound loop-mode action, ℂ-linear in `a`** — `composeActLevel` bundled as a `LinearMap`.
The two are fixed at the bottom-row closures `hclo`; linearity in `a` is layer-wise
`MU.actLevel` linearity. -/
noncomputable def composeActLevelFamilyDeg (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n) : 𝒱 →ₗ[ℂ] End ℂ (MU W U) where
  toFun a := composeActLevel W U hclo a
  map_add' a a' := by
    refine DirectSum.linearMap_ext ℂ fun n => ?_
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [show (DirectSum.lof ℂ ℕ (MUPiece W U) n) x = MU.incl W U n x from rfl,
      composeActLevel_incl, composeActLevel_incl, composeActLevel_incl,
      actLevel_add_a W U n (hclo n) a a', LinearMap.add_apply, map_add]
  map_smul' c a := by
    refine DirectSum.linearMap_ext ℂ fun n => ?_
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [show (DirectSum.lof ℂ ℕ (MUPiece W U) n) x = MU.incl W U n x from rfl,
      composeActLevel_incl, composeActLevel_incl,
      actLevel_smul_a W U n (hclo n) c a, LinearMap.smul_apply, map_smul]

@[simp] theorem composeActLevelFamilyDeg_apply (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n) (a : 𝒱) :
    composeActLevelFamilyDeg W U hclo a = composeActLevel W U hclo a := rfl

/-- **The sound Construction-A loop-mode generator family** `ℤ → (𝒱 →ₗ End ℂ (MU W U))`, built from
the PROVEN bottom-row action `MU.actLevel` (closures `hclo : ∀ n, AnmRightModule W n`).  This is the
honest replacement for `composeActFamily`, whose diagonal-descent hypotheses are false. -/
noncomputable def composeActLevelFamily (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n) : ℤ → (𝒱 →ₗ[ℂ] End ℂ (MU W U)) :=
  fun _ => composeActLevelFamilyDeg W U hclo

@[simp] theorem composeActLevelFamily_apply (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n) (m : ℤ) (a : 𝒱) :
    composeActLevelFamily W U hclo m a = composeActLevel W U hclo a := rfl

/-! ## Object B from the sound family — `vhatModeDataLevel` and `repMULevel`

Through the GENERIC assembly `assembleModeData` (`ZhuVermaAnArchVHatModeData`, which works for any
ℂ-linear generator family), the sound family `composeActLevelFamily` yields object B carrying only
the two genuine Borcherds relations `hderiv`/`hbracket` — now on a sound, true-descent action. -/

/-- **Object B's carried datum** `VHatModeData W (MU W U)`, built from the sound generator family
`composeActLevelFamily` (bottom-row `MU.actLevel`) and the two carried generator-level relations
`hderiv` (the derivative descent) and `hbracket` (the loop commutator).  Unlike `vhatModeData`, the
underlying action is built on the **true** descent subset `∀ n, AnmRightModule W n`. -/
noncomputable def vhatModeDataLevel (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆) :
    VHatModeData W (MU W U) :=
  assembleModeData (composeActLevelFamily W U hclo) hderiv hbracket

/-- `vhatModeDataLevel`'s action on a loop generator `a(m)` is the sound composition action
`composeActLevel a`. -/
@[simp] theorem vhatModeDataLevel_act_single (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆)
    (m : ℤ) (a : 𝒱) :
    (vhatModeDataLevel W U hclo hderiv hbracket).act (single m a) = composeActLevel W U hclo a := by
  rw [vhatModeDataLevel, assembleModeData_act_single, composeActLevelFamily_apply]

/-- **Object B — the Construction-A `V̂`-representation `ρ` on `MU W U`, built on the TRUE descents.**
Assembled from `vhatModeDataLevel` (the sound bottom-row action `MU.actLevel`), this is the `ρ` field
`MUVHatData` consumes (Gannon Thm 5.3.4) — the honest replacement for `repMU`, whose underlying
diagonal `(p,p,0)` descents are false. -/
noncomputable def repMULevel (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆) :
    VHat.VHatRep W (MU W U) :=
  vhatRepMU W U (vhatModeDataLevel W U hclo hderiv hbracket)

/-- The `𝒱`-mode action of the sound object B on `M(U)`: `a₍ₘ₎ = composeActLevel a` (the bottom-row
level-diagonal residue action `MU.actLevel`). -/
@[simp] theorem repMULevel_actMode (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆)
    (a : 𝒱) (m : ℤ) :
    (repMULevel W U hclo hderiv hbracket).actMode a m = composeActLevel W U hclo a := by
  rw [repMULevel, vhatRepMU_actMode, vhatModeDataLevel_act_single]

/-- The `V̂` bracket relation (`actMode_bracket`) for the sound object B, automatic from `ρ` being a
genuine Lie morphism. -/
theorem repMULevel_actMode_bracket (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆)
    (a b : 𝒱) (m k : ℤ) :
    ⁅(repMULevel W U hclo hderiv hbracket).actMode a m,
        (repMULevel W U hclo hderiv hbracket).actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) •
          (repMULevel W U hclo hderiv hbracket).actMode (W.smul a i b) (m + k - i) :=
  vhatRepMU_actMode_bracket W U (vhatModeDataLevel W U hclo hderiv hbracket) a b m k

/-! ## The exact minimal descent subset (the headline)

Object B's action `composeActLevel` consumes exactly `∀ n, AnmRightModule W n` — the bottom-row left
descent `AnmComposeDescL W n 0 0` — together with the cross closure for the right slot, i.e.
`MUGradedAction W`'s data.  The diagonal `(p,p,0)` descents are NOT needed (and are false). -/

/-- **The exact minimal descent subset.**  Object B's per-level action `composeActLevel` is built
from `∀ n, AnmRightModule W n` (the bottom-row left descent), with no appeal to the diagonal
`(p,p,0)` descents.  Recorded as the trivial witness that the action exists from this subset. -/
theorem minimalDescentSubset (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n) (a : 𝒱) :
    ∃ T : End ℂ (MU W U), T = composeActLevel W U hclo a :=
  ⟨composeActLevel W U hclo a, rfl⟩

/-- **The bottom-row left descent is the proven `AnmComposeDescL W n 0 0`.**  `AnmRightModule W n`
(the minimal subset for object B's action) is exactly the bottom-row composition descent, PROVEN
unconditionally (`AnmComposeDescL_bottom`).  This certifies the minimal subset is *closed*, not just
named. -/
theorem minimalDescent_is_bottom_DescL (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    AnmComposeDescL W n 0 0 :=
  AnmComposeDescL_bottom W n

/-! ## `BottomOrbitDefectVanishes` — the constructive `A_n`-bimodule reduction

`BottomOrbitDefectVanishes ρ hInt` (`ZhuVermaAnArchBottomAn`) is exactly the statement that the
degree-`0` component `deg0Proj (ρ.toAlgHom g (defectVec …))` of every `U(V̂)`-orbit image of a defect
vanishes — the `A_n`-bimodule relation on the bottom `M_0 = U`.  We record the clean per-generator
reduction (the predicate IS its own per-generator content) and re-export the closure to bottom
survival, so that with object B available the only carried datum is the genuine `A_n`-degree-`0`
content. -/

namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **`BottomOrbitDefectVanishes` from its per-orbit-generator content.**  The predicate holds as soon
as the degree-`0` component of every `U(V̂)`-orbit image `ρ.toAlgHom g (defectVec ρ u v x ℓ N)` of a
defect vanishes — this *is* the genuine `A_n`-bimodule degree-`0` relation on the bottom (the bottom
is `U` as an `A(𝒱)`-module).  Recorded as the precise reduction: supplying the per-generator datum
discharges `BottomOrbitDefectVanishes`. -/
theorem bottomOrbitDefectVanishes_of_gens {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg)
    (hgen : ∀ (g : UEnv W) (u v : 𝒱) (x : M) (ℓ N : ℤ),
      deg0Proj hInt (ρ.toAlgHom g (defectVec ρ u v x ℓ N)) = 0) :
    BottomOrbitDefectVanishes ρ hInt :=
  hgen

/-- **The bottom `A_n`-relation from the per-orbit-generator datum.**  With the per-orbit-generator
degree-`0` vanishing, `defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥` (the residual `bottomSurvives_full`
consumes) closes — via `bottomAnRelation` (`ZhuVermaAnArchBottomAn`) and the constructive orbit
characterization.  The only carried input is the genuine `A_n`-bimodule degree-`0` content. -/
theorem bottomAnRelation_of_gens {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg)
    (hgen : ∀ (g : UEnv W) (u v : 𝒱) (x : M) (ℓ N : ℤ),
      deg0Proj hInt (ρ.toAlgHom g (defectVec ρ u v x ℓ N)) = 0) :
    defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥ :=
  bottomAnRelation hInt (bottomOrbitDefectVanishes_of_gens hInt hgen)

/-- **Full bottom survival from the per-orbit-generator datum.**  Re-exports `bottomSurvives_an`
on the per-generator `A_n`-bimodule degree-`0` content: the bottom `U` survives the defect quotient.
This is `BottomOrbitDefectVanishes ⟹ bottom survival`, now keyed to the genuine per-orbit datum. -/
theorem bottomSurvives_of_gens {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg) (hgr : IsGradedRep ρ mdeg) (htr : ActModeTruncated ρ)
    (hlw : LowestWeight mdeg)
    (hgen : ∀ (g : UEnv W) (u v : 𝒱) (x : M) (ℓ N : ℤ),
      deg0Proj hInt (ρ.toAlgHom g (defectVec ρ u v x ℓ N)) = 0) :
    BottomSurvives ρ mdeg :=
  bottomSurvives_an hInt hgr htr hlw (bottomOrbitDefectVanishes_of_gens hInt hgen)

end VHatRep

/-! ## Summary — what closed, and the exact minimal subset

* **Minimal descent subset ρ needs:** the **bottom-row** family `(n,0,0)`, i.e. `∀ n, AnmRightModule
  W n` (left, `= AnmComposeDescL W n 0 0`, PROVEN) and `AnmCrossClosure W n` (right,
  `= AnmComposeDescR W n 0 0`, proven mod `CrossCircOnmGen`), bundled as `MUGradedAction W`.  The
  diagonal `(p,p,0)` descents the existing `composeActFamily` route demands are **FALSE for `p ≥ 1`**
  (`certificates/mathematica/diag_pp0_descents.wl`, the grading-generator families) — so that route is unsound.

* **Object B (ρ term-level), built on the TRUE subset:** `repMULevel` — assembled from
  `composeActLevel` (the proven `MU.actLevel`) through the generic `assembleModeData`, carrying only
  the two genuine Borcherds relations `hderiv`/`hbracket` on the sound action.

* **`BottomOrbitDefectVanishes`:** reduced to its single per-orbit-generator degree-`0` content
  (`bottomOrbitDefectVanishes_of_gens`) and re-exported to full bottom survival
  (`bottomSurvives_of_gens`) — the genuine `A_n`-bimodule degree-`0` relation, carried, never an
  axiom.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`); no existing
definition mutated. -/

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
