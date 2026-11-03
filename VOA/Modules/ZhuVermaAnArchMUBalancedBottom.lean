/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSdBalancedBottom

/-!
# The `A(𝒱)`-balanced generalized-Verma bottom `M(U)(0) = A(𝒱) ⊗_{A(𝒱)} U ≅ U`

`ZhuVermaAnArchSdBalancedBottom` shows that the ℂ-tensor induced module's level-`0`
weight space is the **ℂ-tensor** cover `MUPiece W U 0 = A_{0,0}(𝒱) ⊗_ℂ U`, which is strictly larger than
the Dong–Jiang bottom `U` whenever `dim A(𝒱) > 1`; the genuine bottom is the `A(𝒱)`-**balanced** tensor
`A_{0,0}(𝒱) ⊗_{A(𝒱)} U ≅ U`.  This file makes that balanced bottom a **first-class standalone object**,
ready to become `MUModuleData`'s level-`0` weight space in the bimodule-balancing re-grading (see the
plan below).  The hard iso is proved upstream.

## Contents (axiom-clean, pbw-free)

* **`MUBalBottom W U`** — the balanced bottom `(A(𝒱) ⊗_ℂ U) ⧸ bottomBalancing`, i.e. the `ℂ`-tensor
  cover modulo the R0 balancing `ker(bottomAct)`.  (`= A_{0,0}(𝒱) ⊗_{A(𝒱)} U` as a `ℂ`-space.)
* **`muBalBottomEquiv W U : MUBalBottom W U ≃ₗ[ℂ] U.carrier`** — the DJ `L(U)(0) ≅ U`, a thin re-export
  of the proved `MUConstruct.bottomBalancedEquiv`.
* **`muBalQuot W U : MUPiece W U 0 →ₗ[ℂ] MUBalBottom W U`** — the bridge from the current ℂ-tensor bottom
  to the balanced bottom: transport `A_{0,0}(𝒱) ≅ A(𝒱)` (`anmZeroEquivA`), then quotient by the
  balancing.  Proven **surjective**, with **kernel the (transported) balancing** — and (for `P.toAMod`)
  the same kernel as the level-`0` layer map, through which `layerAction 0` **factors**
  `layerAction 0 = (β ∘ muBalBottomEquiv) ∘ muBalQuot` — surjection onto the balanced bottom followed by
  an *injection* into `P`.  So `qCanon` on the bottom is injective exactly on `MUBalBottom`.

## The bimodule-balancing plan (pbw-free; the n = 0 brick is this file)

Goal: re-grade `MUModuleData` (`ZhuVermaAnArchMULW.lean`) so its level-`n` weight space is the
**balanced** `A_{n,0}(𝒱) ⊗_{A(𝒱)} U`, making `weight (hU) = MUBalBottom ≅ U` and discharging the
bottom-injectivity leaf.

* **n = 0 (this file).**  Replace the bottom weight space `MUPiece 0 = A(𝒱) ⊗_ℂ U` by `MUBalBottom`
  (`≅ U` via `muBalBottomEquiv`).  The quotient bridge is `muBalQuot`; `qCanon` factors through it with an
  injective tail, so the balanced bottom survives faithfully.
* **n ≥ 1 (the cascade).**  `A_{n,0}(𝒱)` is an `(A(𝒱), A(𝒱))`-bimodule (DLM3/DJ: left action from
  `A_{n,0} = A_{n,0}·A_{0,0}`, right from `A_{0,0}·A_{n,0}`); the balanced piece is
  `MUPieceBal n := A_{n,0}(𝒱) ⊗_{A(𝒱)} U` (balance over the *right* `A(𝒱)`-action on `A_{n,0}`, using
  `instRingA` + `moduleMh` on `U`).  Define `MUBal := ⨁ₙ MUPieceBal n` with the descended graded action
  (the ℂ-tensor action descends because it is `A(𝒱)`-balanced by the DJ associativity `A_{n,0}·A_{0,0} ⊆
  A_{n,0}`), and `MUBal.deg n = range (incl n)` internal as in `MU.isInternal_deg`.
* **Re-target the kernel machinery.**  `toKerStructData` (`ZhuVermaAnArchSdKerReduce.lean:165/170`) hard-
  wires `bottom := weight(hU) = ℂ-tensor` and proves `J ⊓ bottom = ⊥` against it; after re-grading,
  `bottom = MUBalBottom ≅ U`, so `q_inj_on_bottom` becomes `balancedBottom_injective` (a TERM) and
  `ker_eq_J`/`J_maximal` re-close with the balanced bottom.  Then `qInjOnBottomResidual` (re-stated on the
  balanced weight space) is TRUE and the injective half's bottom-injectivity leaf is discharged —
  leaving only `MUGradedAction` (the crossCirc/ARD keystone).  **Bimodule balancing, NOT the PBW
  route.**

`#print axioms` on the three main terms is `[propext, Classical.choice, Quot.sound]`; pbw-free.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.5 / Thm 4.13; Dong–Li–Mason III §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1 (Thm 5.3.4 lifting / R0).
-/

namespace VOA

open scoped BigOperators DirectSum TensorProduct
open VertexOperatorAlgebra InducedAssignment MUConstruct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The balanced bottom object -/

/-- **The `A(𝒱)`-balanced generalized-Verma bottom** `M(U)(0) = A_{0,0}(𝒱) ⊗_{A(𝒱)} U`, realized as the
`ℂ`-tensor cover `A(𝒱) ⊗_ℂ U` modulo the R0 balancing `bottomBalancing = ker(bottomAct)`. -/
abbrev MUBalBottom (W : VertexOperatorAlgebra 𝒱) (U : AMod W) : Type u :=
  TensorProduct ℂ (A W) U.carrier ⧸ MUConstruct.bottomBalancing W U

/-- **`M(U)(0) ≅ U`.**  The balanced bottom is `ℂ`-linearly isomorphic to `U` — the Dong–Jiang statement
`L(U)(0) ≅ U`.  Thin re-export of the proved `MUConstruct.bottomBalancedEquiv`. -/
noncomputable def muBalBottomEquiv (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    MUBalBottom W U ≃ₗ[ℂ] U.carrier :=
  MUConstruct.bottomBalancedEquiv W U

@[simp] theorem muBalBottomEquiv_mk (U : AMod W) (a : A W) (u : U.carrier) :
    muBalBottomEquiv W U (Submodule.Quotient.mk (a ⊗ₜ[ℂ] u)) = U.ρ a u :=
  MUConstruct.bottomBalancedEquiv_mk W U a u

/-! ## The bridge `MUPiece 0 ↠ MUBalBottom` -/

/-- **The balancing quotient bridge** `A_{0,0}(𝒱) ⊗_ℂ U = MUPiece W U 0 ↠ MUBalBottom W U`: transport
the level-`0` piece along `A_{0,0}(𝒱) ≅ A(𝒱)` (`anmZeroEquivA`), then take the balancing quotient. -/
noncomputable def muBalQuot (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    MUPiece W U 0 →ₗ[ℂ] MUBalBottom W U :=
  (MUConstruct.bottomBalancing W U).mkQ ∘ₗ
    (TensorProduct.congr (anmZeroEquivA W) (LinearEquiv.refl ℂ U.carrier)).toLinearMap

@[simp] theorem muBalQuot_tmul (U : AMod W) (a : 𝒱) (u : U.carrier) :
    muBalQuot W U (mkAnm W 0 0 a ⊗ₜ[ℂ] u)
      = Submodule.Quotient.mk (_root_.VOA.mk W a ⊗ₜ[ℂ] u) := by
  rw [muBalQuot]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, anmZeroEquivA_mkAnm, Submodule.mkQ_apply]

/-- **The bridge is surjective** (`mkQ` and `anmZeroEquivA ⊗ id` are). -/
theorem muBalQuot_surjective (U : AMod W) : Function.Surjective (muBalQuot W U) := by
  rw [muBalQuot, LinearMap.coe_comp]
  exact (Submodule.mkQ_surjective _).comp
    (TensorProduct.congr (anmZeroEquivA W) (LinearEquiv.refl ℂ U.carrier)).surjective

/-- **The bridge's kernel is exactly the (transported) balancing.**  `ker (muBalQuot) =
comap (anmZeroEquivA ⊗ id) (bottomBalancing)` — the balancing relations pulled back to `MUPiece 0`. -/
theorem muBalQuot_ker (U : AMod W) :
    LinearMap.ker (muBalQuot W U)
      = Submodule.comap (TensorProduct.congr (anmZeroEquivA W)
          (LinearEquiv.refl ℂ U.carrier)).toLinearMap (MUConstruct.bottomBalancing W U) := by
  rw [muBalQuot, LinearMap.ker_comp, Submodule.ker_mkQ]

/-! ## The bridge for `P.toAMod`: same kernel as `layerAction 0`, and the factorization -/

/-- **The bridge has the same kernel as the level-`0` layer map.**  Combined with `bottomKer_eq_balancing`
(`ker (layerAction 0) = comap (anmZeroEquivA ⊗ id) (bottomBalancing)`), the balancing quotient bridge and
`qCanon`-on-the-bottom kill exactly the same vectors. -/
theorem muBalQuot_ker_eq_layerKer (P : LWModule W) :
    LinearMap.ker (muBalQuot W P.toAMod)
      = LinearMap.ker ((GradedModeVanish.ofBottom (betaCanonical P)
          (hbetaCanonical P)).toLayerActionData.layerAction 0) :=
  (muBalQuot_ker P.toAMod).trans (bottomKer_eq_balancing P).symm

/-- **`layerAction 0` factors through the balanced bottom.**
`layerAction 0 = (β ∘ muBalBottomEquiv) ∘ muBalQuot` — a **surjection** onto `MUBalBottom` followed by an
**injection** into `P` (`β ∘ muBalBottomEquiv` is injective: `β` a subtype, `muBalBottomEquiv` an equiv).
So `qCanon` on the ℂ-tensor bottom is injective *exactly* on the balanced quotient `MUBalBottom` — the
precise sense in which `MUBalBottom` is the correct level-`0` weight space for the balanced-bottom keystone. -/
theorem layerAction0_via_muBalQuot (P : LWModule W) :
    (GradedModeVanish.ofBottom (betaCanonical P)
        (hbetaCanonical P)).toLayerActionData.layerAction 0
      = (betaCanonical P ∘ₗ (muBalBottomEquiv W P.toAMod).toLinearMap) ∘ₗ muBalQuot W P.toAMod := by
  apply TensorProduct.ext'
  intro a u
  obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective (Onm W 0 0) a
  show (GradedModeVanish.ofBottom (betaCanonical P)
        (hbetaCanonical P)).toLayerActionData.layerAction 0 (mkAnm W 0 0 a' ⊗ₜ[ℂ] u)
      = ((betaCanonical P ∘ₗ (muBalBottomEquiv W P.toAMod).toLinearMap) ∘ₗ muBalQuot W P.toAMod)
          (mkAnm W 0 0 a' ⊗ₜ[ℂ] u)
  rw [canonicalLayer0_bottomAct_tmul]
  simp only [bottomAct_tmul, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, muBalQuot_tmul,
    muBalBottomEquiv_mk]

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
