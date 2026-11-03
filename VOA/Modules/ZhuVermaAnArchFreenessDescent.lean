/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLayerAction
import VOA.Modules.ZhuVermaAnArchMUcirc
import VOA.Modules.ZhuAlgebra

/-!
# Tier-3 freeness-layer descent — constructing `gradedAct n` and `gradedAct_descends`

`Modules.ZhuVermaAnArchLayerAction` reduced the per-layer bimodule-action map
`layer n : A_{n,0}(𝒱) ⊗ U → P` to the single carried datum `LayerActionData β`, whose two fields are

* `gradedAct : ∀ n, 𝒱 →ₗ[ℂ] (U.carrier →ₗ[ℂ] P.carrier)` — the per-level graded mode action; and
* `gradedAct_descends : ∀ n, ∀ g ∈ Onm W n 0, gradedAct n g = 0` — the **well-definedness** (the
  defining relations `O_{n,0}(𝒱)` act as `0` through the graded mode action), the depth-`n` analogue
  of the proven `n = 0` easy-direction `ZhuModule.O_le_ker_rhoLW` (`O(𝒱) ≤ ker (rhoLW)` on the
  bottom).

This file **constructs** both fields for any lowest-weight module `P` (`LWModule W`), out of the
module's *own* mode action:

* **The depth-`n` graded mode** `gMode N n : 𝒱 →ₗ[ℂ] End ℂ M` — the exact depth-`n` analogue of the
  proven zero mode `oMod N` (`Character.oMod`).  On a homogeneous `v ∈ 𝒱ₖ` it is
  `gMode N n v = mode (N.YM v) (k - 1 - n)` (`gMode_homogeneous`); the `n = 0` case is `oMod`
  (`gMode_zero`).  By `ZeroModeMult.mode_mem_weight` it raises the conformal weight by exactly `n`:
  `gMode N n v` sends `M_α → M_{α + n}` for homogeneous `v` (so on the bottom `M_h` it lands in the
  weight-`(h+n)` space — the `n`-th graded layer).  Built `lsum`-of-slices, **identically** to `oMod`.

* **`gradedAct n a u := gMode P.isMod n a (β u)`** — the `n`-th graded mode of `a ∈ 𝒱` acting on the
  realized bottom vector `β u ∈ P_h`, landing in the weight-`(h+n)` space.  ℂ-linear in `a` and `u`.

The genuine well-definedness `gradedAct_descends` is the depth-`n` analogue of `O_le_ker_rhoLW`: the
two families of `O_{n,0}(𝒱)`-generators — the **circle** generators `anmCirc W n 0 c d` and the
**grading** generators `anmLgen W n 0 c = L₋₁c + L₀c − n·c` (`ZhuVermaAnArchAnm`) — act as `0` through
`gMode P.isMod n` on the bottom `P_h`.  These two per-generator vanishings are precisely the
depth-`n` analogues of the two facts `O_le_ker_rhoLW` uses (`oMod_zhuMul_lowest_all` 5.3.9a +
`oMod_L_translation_all` 5.3.9b); the `O_{n,0}`-generators are the `Pres`-towers carried into
`Onm W n 0` by the **proven** keystone `Pres_mem_Onm` (`ZhuVermaAnArchMUcirc`), and the graded mode
action kills them exactly as `actA` kills `O(𝒱)`.  We carry exactly those two per-generator
vanishings as the data hypothesis `GradedModeVanish` (the genuine Dong–Jiang/Frenkel–Zhu freeness
content of the bottom), **never** an axiom, and from it the full `gradedAct_descends` is a pure
`Submodule.span_le` + `sup_le` induction — **identical** to the `O_eq_span` collapse of
`O_le_ker_rhoLW`.

## What is proved here (axiom-clean)

* `gMode N n`, `gModeFamily N n k` — the depth-`n` graded mode (the `n`-shifted `oMod`); with
  `gMode_homogeneous` (slice on a homogeneous vector) and `gMode_zero` (`= oMod`).
* `GradedModeVanish β` — the data hypothesis bundling the two per-generator vanishings of the
  graded mode action on the bottom: `gMode_circ_vanish` (circle generators) and `gMode_Lgen_vanish`
  (grading generators).  A hypothesis structure, no `sorry`, **never** an axiom.
* `GradedModeVanish.gradedActMap n` — the constructed `gradedAct n : 𝒱 →ₗ[ℂ] (U →ₗ[ℂ] P)`,
  `a ↦ (u ↦ gMode P.isMod n a (β u))`; with `gradedActMap_apply`.
* `GradedModeVanish.gradedAct_descends` — **the keystone**: `∀ n, ∀ g ∈ Onm W n 0,
  gradedActMap n g = 0`; the depth-`n` analogue of `O_le_ker_rhoLW`, proved by `Submodule.span_le`
  + `sup_le` from the two carried per-generator vanishings.
* `GradedModeVanish.toLayerActionData` — assembles a `InducedAssignment.LayerActionData β` (the datum
  that `ZhuVermaAnArchLayerAction.layerAction` turns into `UnivLiftData.layer`), discharging the
  freeness side at term level.

## The exact remaining datum

The single residual carried by `GradedModeVanish` is the two per-generator vanishings of the **own**
graded mode action of `P` on its bottom `P_h`:
`gMode P.isMod n (anmCirc W n 0 c d) (β u) = 0` and `gMode P.isMod n (anmLgen W n 0 c) (β u) = 0`.
These are the depth-`n` analogues of the proven `oMod_zhuMul_lowest_all`/`oMod_L_translation_all`
(`n = 0`).  Everything else — the construction of `gradedAct n`, the `Onm`-descent, and the
`LayerActionData` assembly — is unconditional and term-level here.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.2, Thm 5.3.4; Frenkel–Zhu Lemma 2.1.2.
`ZhuModule` (`oMod`, `O_le_ker_rhoLW`, `actA` — the proven `n = 0` easy direction),
`ZhuVermaAnArchAnm` (`Onm`, `OnmL`, `anmCirc`, `anmLgen`),
`ZhuVermaAnArchMUcirc` (`Pres_mem_Onm` — the keystone),
`ZhuVermaAnArchLayerAction` (`LayerActionData`, `layerAction`).
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open VertexOperatorAlgebra
open Module (End)

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The depth-`n` graded mode `gMode` (the `n`-shifted `oMod`). -/

section GradedMode

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The weight-`k` slice of the **depth-`n` graded mode**: `vₖ ↦ (vₖ)₍ₖ₋₁₋ₙ₎` as a map
`𝒱ₖ → End M`.  The exact depth-`n` analogue of `Character.oModFamily` (which is `n = 0`,
slice `(vₖ)₍ₖ₋₁₎`). -/
noncomputable def gModeFamily (N : OrdVModule W M) (n : ℕ) (k : ℤ) : (W.grading k) →ₗ[ℂ] End ℂ M :=
  (modeLinear (k - 1 - n)).comp (N.YM.comp (W.grading k).subtype)

/-- **The depth-`n` graded mode** `gMode N n v = ∑_k (v_k)₍ₖ₋₁₋ₙ₎` — the `n`-shifted `Character.oMod`
(`oMod` is `n = 0`).  On a homogeneous `v ∈ 𝒱ₖ` it is `mode (N.YM v) (k − 1 − n)`
(`gMode_homogeneous`), raising the conformal weight by exactly `n`. -/
noncomputable def gMode (N : OrdVModule W M) (n : ℕ) : 𝒱 →ₗ[ℂ] End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (gModeFamily N n)).comp (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- On a homogeneous `v ∈ 𝒱ₖ`, the depth-`n` graded mode is the single mode `(v)₍ₖ₋₁₋ₙ₎`.
The depth-`n` analogue of `ZhuAlgebra.oMod_homogeneous`. -/
theorem gMode_homogeneous (N : OrdVModule W M) (n : ℕ) {k : ℤ} {v : 𝒱} (hv : v ∈ W.grading k) :
    gMode N n v = mode (N.YM v) (k - 1 - n) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : gMode N n v = gModeFamily N n k ⟨v, hv⟩ := by
    change (DFinsupp.lsum ℂ (gModeFamily N n)) (DirectSum.decompose W.grading v) = _
    rw [DirectSum.decompose_of_mem W.grading hv]
    exact DFinsupp.lsum_single ℂ (gModeFamily N n) k ⟨v, hv⟩
  rw [hcollapse]; rfl

/-- The depth-`0` graded-mode slices are exactly the zero-mode slices (`k − 1 − 0 = k − 1`). -/
theorem gModeFamily_zero (N : OrdVModule W M) : gModeFamily N 0 = oModFamily N := by
  funext k
  unfold gModeFamily oModFamily
  norm_num

/-- At `n = 0` the graded mode is the zero mode `oMod` (the slices agree, `k − 1 − 0 = k − 1`). -/
theorem gMode_zero (N : OrdVModule W M) : gMode N 0 = oMod N := by
  unfold gMode oMod
  rw [gModeFamily_zero]

end GradedMode

/-! ## The carried freeness datum and the constructed `gradedAct`. -/

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The graded-mode freeness datum on a lowest-weight module `P`, through a bottom map `β`.**

For `U = P.toAMod` (the bottom `A(𝒱)`-module of `P`) and a bottom map
`β : U.carrier →ₗ[ℂ] P.carrier` (the realized embedding `U ≅ P_h ↪ P`), this bundles the genuine
Dong–Jiang/Frenkel–Zhu freeness content of the bottom: the two per-generator vanishings of the
module's **own** depth-`n` graded mode action `gMode P.isMod n` on the bottom.

* `gMode_circ_vanish` — the **circle** `O_{n,0}`-generators act as `0` on the bottom:
  `gMode P.isMod n (anmCirc W n 0 c d) (β u) = 0`.
* `gMode_Lgen_vanish` — the **grading** `O_{n,0}`-generators act as `0` on the bottom:
  `gMode P.isMod n (anmLgen W n 0 c) (β u) = 0`.

These are exactly the depth-`n` analogues of the two facts the proven `n = 0` `O_le_ker_rhoLW` uses
(`oMod_zhuMul_lowest_all` 5.3.9a + `oMod_L_translation_all` 5.3.9b).  A hypothesis structure, no
`sorry` and **never** an axiom. -/
structure GradedModeVanish {U : AMod W} {P : LWModule W}
    (β : U.carrier →ₗ[ℂ] P.carrier) where
  /-- The circle `O_{n,0}`-generators `anmCirc W n 0 c d` act as `0` through the own depth-`n` graded
  mode on the bottom (depth-`n` analogue of `oMod_zhuMul_lowest_all`). -/
  gMode_circ_vanish : ∀ (n : ℕ) (c d : 𝒱) (u : U.carrier),
    gMode P.isMod n (anmCirc W n 0 c d) (β u) = 0
  /-- The grading `O_{n,0}`-generators `anmLgen W n 0 c = L₋₁c + L₀c − n·c` act as `0` through the
  own depth-`n` graded mode on the bottom (depth-`n` analogue of `oMod_L_translation_all`). -/
  gMode_Lgen_vanish : ∀ (n : ℕ) (c : 𝒱) (u : U.carrier),
    gMode P.isMod n (anmLgen W n 0 c) (β u) = 0

namespace GradedModeVanish

variable {U : AMod W} {P : LWModule W} {β : U.carrier →ₗ[ℂ] P.carrier}

/-- **The constructed per-layer graded mode action** `gradedAct n : 𝒱 →ₗ[ℂ] (U →ₗ[ℂ] P)`,
`a ↦ (u ↦ gMode P.isMod n a (β u))` — the `n`-th graded mode of `a ∈ 𝒱` acting on the realized
bottom vector `β u ∈ P_h`, landing in the weight-`(h+n)` space.  ℂ-linear in `a` and in `u`. -/
noncomputable def gradedActMap (_ : GradedModeVanish β) (n : ℕ) :
    𝒱 →ₗ[ℂ] (U.carrier →ₗ[ℂ] P.carrier) where
  toFun a :=
    { toFun := fun w => gMode P.isMod n a (β w)
      map_add' := by intro x y; rw [map_add, map_add]
      map_smul' := by intro c x; rw [map_smul, map_smul]; rfl }
  map_add' a b := by
    ext w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, LinearMap.add_apply]
  map_smul' c a := by
    ext w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul, LinearMap.smul_apply,
      RingHom.id_apply]

@[simp] theorem gradedActMap_apply (G : GradedModeVanish β) (n : ℕ) (a : 𝒱) (w : U.carrier) :
    G.gradedActMap n a w = gMode P.isMod n a (β w) := rfl

/-! ## The depth-`n` descent (the analogue of `O_le_ker_rhoLW`). -/

/-- **The keystone — depth-`n` `O_{n,0}`-descent.**  The defining relations `O_{n,0}(𝒱)` act as `0`
through the constructed graded mode action `gradedActMap n` — the depth-`n` analogue of
`ZhuModule.O_le_ker_rhoLW` (`O(𝒱) ≤ ker (rhoLW)` on the bottom, the `n = 0` case).

`Onm W n 0 = span{anmCirc W n 0 c d} ⊔ OnmL W n 0` with `OnmL = span{anmLgen W n 0 c}`
(`ZhuVermaAnArchAnm`); the proof is a pure `sup_le` + `Submodule.span_le` collapse onto the two
carried per-generator vanishings — **identical** to the `O_eq_span` collapse of `O_le_ker_rhoLW`. -/
theorem gradedAct_descends (G : GradedModeVanish β) :
    ∀ (n : ℕ), ∀ g ∈ Onm W n 0, G.gradedActMap n g = 0 := by
  intro n g hg
  -- It suffices to show `Onm W n 0 ≤ ker (gradedActMap n)`.
  have hle : Onm W n 0 ≤ LinearMap.ker (G.gradedActMap n) := by
    rw [Onm, sup_le_iff]
    refine ⟨?_, ?_⟩
    · -- circle span
      rw [Submodule.span_le]
      rintro x ⟨c, d, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      ext w
      rw [gradedActMap_apply, LinearMap.zero_apply]
      exact G.gMode_circ_vanish n c d w
    · -- grading span (OnmL)
      rw [OnmL, Submodule.span_le]
      rintro x ⟨c, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      ext w
      rw [gradedActMap_apply, LinearMap.zero_apply]
      exact G.gMode_Lgen_vanish n c w
  have := hle hg
  rwa [LinearMap.mem_ker] at this

/-! ## Assembling the `LayerActionData` (discharging the freeness side). -/

/-- **The constructed `LayerActionData β`** — both fields supplied: `gradedAct := gradedActMap`
(the own depth-`n` graded mode action on the bottom) and `gradedAct_descends` (the depth-`n`
`O_{n,0}`-descent).  This is exactly the datum `ZhuVermaAnArchLayerAction.layerAction` turns into the
`UnivLiftData.layer` field, so this discharges the freeness side at term level (modulo the two carried
per-generator vanishings of `GradedModeVanish`). -/
noncomputable def toLayerActionData (G : GradedModeVanish β) : LayerActionData β where
  gradedAct := G.gradedActMap
  gradedAct_descends := G.gradedAct_descends

@[simp] theorem toLayerActionData_layerAction_tmul (G : GradedModeVanish β) (n : ℕ) (a : 𝒱)
    (w : U.carrier) :
    (G.toLayerActionData).layerAction n (mkAnm W n 0 a ⊗ₜ[ℂ] w)
      = gMode P.isMod n a (β w) := by
  rw [LayerActionData.layerAction_tmul]
  rfl

end GradedModeVanish

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
