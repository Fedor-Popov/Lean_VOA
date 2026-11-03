/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUBalancedBottom

/-!
# The `A(𝒱)`-balanced level-`n` piece `MUPieceBal W U n = A_{n,0}(𝒱) ⊗_{A(𝒱)} U`

`ZhuVermaAnArchMU` builds the Dong–Jiang induced module over the **base field** `ℂ`, whose level-`n`
piece is the ℂ-tensor cover `MUPiece W U n = A_{n,0}(𝒱) ⊗_ℂ U`.  The analysis in `ZhuVermaAnArchSdBalancedBottom`
(`ZhuVermaAnArchSdBalancedBottom`) showed that the genuine Dong–Jiang module
needs the `A(𝒱)`-**balanced** tensor `A_{n,0}(𝒱) ⊗_{A(𝒱)} U`, which at `n = 0` is strictly smaller
than the ℂ-tensor whenever `dim A(𝒱) > 1`.  `ZhuVermaAnArchMUBalancedBottom` made the balanced
**bottom** (`n = 0`) a first-class object.  This file generalizes that to **every** level `n`.

## The construction (pbw-free, hypothesis-free)

The right `A(𝒱)`-action on `A_{n,0}(𝒱)` is the residue product `anmRight` (whose descent to the
quotient `A_{n,0}(𝒱) = 𝒱 ⧸ O_{n,0}` is the open DJ 2.8 keystone — **not** needed here).  We take the
`A(𝒱)`-balancing at the level of **representatives** `x, a ∈ 𝒱`: the balancing submodule is the
`ℂ`-span of the differences

  `[x *^n_0 a] ⊗ u  −  [x] ⊗ ρ(a)·u`   (`x a : 𝒱`, `u : U`),

where `[·]` is the class in `A_{n,0}(𝒱)`, `x *^n_0 a = anmRight W n 0 x a`, and `ρ(a)·u = U.ρ [a] u`
is the left `A(𝒱)`-action on `U` (available for **every** `AMod W`, no ring descent required).  The
balanced piece is the quotient of the ℂ-tensor cover by this span:

  `MUPieceBal W U n := MUPiece W U n ⧸ balancing W U n`   (a `ℂ`-module).

This mirrors the B0 pattern (`MUBalBottom = (A(𝒱) ⊗_ℂ U) ⧸ ker(bottomAct)`): at `n = 0` the balancing
span **equals** the B0 balancing kernel, so `MUPieceBal W U 0 ≃ₗ[ℂ] MUBalBottom W U`
(`muPieceBal0Equiv`), and both are `≅ U` (`muPieceBal0EquivU`).

## Contents (axiom-clean, pbw-free)

* **`balancing W U n`** — the `A(𝒱)`-balancing submodule of the ℂ-tensor cover `MUPiece W U n`.
* **`MUPieceBal W U n`** — the balanced level-`n` piece `A_{n,0}(𝒱) ⊗_{A(𝒱)} U`, a `ℂ`-module.
* **`mkPieceBal_balance`** — the defining relation `[x *^n_0 a] ⊗ u = [x] ⊗ ρ(a)·u` in the quotient.
* **`muPieceBal0EquivU W U : MUPieceBal W U 0 ≃ₗ[ℂ] U.carrier`** and
  **`muPieceBal0Equiv W U : MUPieceBal W U 0 ≃ₗ[ℂ] MUBalBottom W U`** — the `n = 0` match with the
  proved balanced bottom (via `balancing_zero_eq_ker`: the span balancing at `n = 0` IS the B0 kernel).

`#print axioms` on every headline term is `[propext, Classical.choice, Quot.sound]`.  pbw-free.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), §§2–4 (Lemma 2.8, Prop 3.4–3.5, Thm 4.13);
Dong–Li–Mason III §4; H. Li `hep-th/9406211` §2; Gannon §5.3.2.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The `A(𝒱)`-balancing submodule of the ℂ-tensor cover -/

/-- **The balancing generators** at level `n`: the differences `[x *^n_0 a] ⊗ u − [x] ⊗ ρ(a)·u`
(`x a : 𝒱`, `u : U`), the representative-level `A(𝒱)`-balancing relations (right action on
`A_{n,0}(𝒱)` versus left action on `U`). -/
def balancingSet (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    Set (MUPiece W U n) :=
  {z | ∃ (x a : 𝒱) (u : U.carrier),
    z = mkAnm W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] u
        - mkAnm W n 0 x ⊗ₜ[ℂ] U.ρ (mk W a) u}

/-- **The `A(𝒱)`-balancing submodule** of `MUPiece W U n = A_{n,0}(𝒱) ⊗_ℂ U`: the `ℂ`-span of the
balancing generators.  Quotienting by it realizes the balanced tensor `A_{n,0}(𝒱) ⊗_{A(𝒱)} U`. -/
noncomputable def balancing (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    Submodule ℂ (MUPiece W U n) :=
  Submodule.span ℂ (balancingSet W U n)

/-- Each balancing generator `[x *^n_0 a] ⊗ u − [x] ⊗ ρ(a)·u` lies in the balancing submodule. -/
theorem balancing_gen_mem (U : AMod W) (n : ℕ) (x a : 𝒱) (u : U.carrier) :
    mkAnm W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] u - mkAnm W n 0 x ⊗ₜ[ℂ] U.ρ (mk W a) u
      ∈ balancing W U n :=
  Submodule.subset_span ⟨x, a, u, rfl⟩

/-! ## The balanced level-`n` piece -/

/-- **The `A(𝒱)`-balanced level-`n` piece** `A_{n,0}(𝒱) ⊗_{A(𝒱)} U`, realized as the `ℂ`-tensor
cover `MUPiece W U n = A_{n,0}(𝒱) ⊗_ℂ U` modulo the `A(𝒱)`-balancing submodule.  A `ℂ`-module
(quotient `AddCommGroup`/`Module ℂ`).  At `n = 0` this is `MUBalBottom W U` (`muPieceBal0Equiv`). -/
abbrev MUPieceBal (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) : Type u :=
  MUPiece W U n ⧸ balancing W U n

/-- The canonical `ℂ`-linear projection `A_{n,0}(𝒱) ⊗_ℂ U ↠ MUPieceBal W U n`. -/
noncomputable def mkPieceBal (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MUPiece W U n →ₗ[ℂ] MUPieceBal W U n := (balancing W U n).mkQ

theorem mkPieceBal_surjective (U : AMod W) (n : ℕ) :
    Function.Surjective (mkPieceBal W U n) := Submodule.mkQ_surjective _

/-- **The defining balancing relation** in the balanced piece: `[x *^n_0 a] ⊗ u = [x] ⊗ ρ(a)·u`.
This is exactly the `A(𝒱)`-balancing `(x·a) ⊗ u = x ⊗ (a·u)`, now an equation in `MUPieceBal`. -/
theorem mkPieceBal_balance (U : AMod W) (n : ℕ) (x a : 𝒱) (u : U.carrier) :
    mkPieceBal W U n (mkAnm W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] u)
      = mkPieceBal W U n (mkAnm W n 0 x ⊗ₜ[ℂ] U.ρ (mk W a) u) := by
  rw [← sub_eq_zero, mkPieceBal, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact balancing_gen_mem U n x a u

/-! ## The `n = 0` match with the proved balanced bottom `MUBalBottom`

At `n = 0` the balancing span coincides with the B0 balancing kernel `ker(bottomAct)`: transported
along `A_{0,0}(𝒱) ≅ A(𝒱)` (`anmZeroEquivA`), the level-`0` action map
`piece0ToU = muBalBottomEquiv ∘ muBalQuot` sends `[x]₀₀ ⊗ u ↦ ρ([x])·u`, its kernel is the balancing,
and it is surjective.  Hence `MUPieceBal W U 0 ≃ U ≃ MUBalBottom`. -/

/-- **The level-`0` action map** `A_{0,0}(𝒱) ⊗_ℂ U → U`, `[x]₀₀ ⊗ u ↦ ρ([x])·u`, factored through the
proved balancing bridge `muBalQuot` and the DJ bottom iso `muBalBottomEquiv`. -/
noncomputable def piece0ToU (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    MUPiece W U 0 →ₗ[ℂ] U.carrier :=
  (muBalBottomEquiv W U).toLinearMap ∘ₗ muBalQuot W U

@[simp] theorem piece0ToU_tmul (U : AMod W) (a : 𝒱) (u : U.carrier) :
    piece0ToU W U (mkAnm W 0 0 a ⊗ₜ[ℂ] u) = U.ρ (mk W a) u := by
  rw [piece0ToU, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, muBalQuot_tmul,
    muBalBottomEquiv_mk]

theorem piece0ToU_surjective (U : AMod W) : Function.Surjective (piece0ToU W U) := by
  intro y
  obtain ⟨w, hw⟩ := muBalQuot_surjective U ((muBalBottomEquiv W U).symm y)
  exact ⟨w, by
    rw [piece0ToU, LinearMap.comp_apply, hw, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply]⟩

/-- **The balancing span is contained in `ker(piece0ToU)`.**  On a generator,
`ρ([x *^0_0 a])·u = ρ([x])·(ρ([a])·u)` by `anmRight W 0 0 = zhuMul` and multiplicativity `U.ρ_mul`. -/
theorem balancing_le_ker (U : AMod W) :
    balancing W U 0 ≤ LinearMap.ker (piece0ToU W U) := by
  rw [balancing, Submodule.span_le]
  rintro z ⟨x, a, u, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, piece0ToU_tmul, anmRight_zero_zero,
    U.ρ_mul, Module.End.mul_apply, sub_self]

/-- Every vector agrees, modulo the balancing, with `[𝟙] ⊗ (piece0ToU vector)`.  The key step of
`ker(piece0ToU) ≤ balancing`: on `[x] ⊗ u` this is the generator with `x' = 𝟙`, `a = x`
(`𝟙 *^0_0 x = x`, `zhuMul_vacuum_left`). -/
theorem sub_bottom_mem_balancing (U : AMod W) (z : MUPiece W U 0) :
    z - mkAnm W 0 0 W.vacuum ⊗ₜ[ℂ] piece0ToU W U z ∈ balancing W U 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t u =>
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Onm W 0 0) t
      show mkAnm W 0 0 x ⊗ₜ[ℂ] u
            - mkAnm W 0 0 W.vacuum ⊗ₜ[ℂ] piece0ToU W U (mkAnm W 0 0 x ⊗ₜ[ℂ] u)
          ∈ balancing W U 0
      rw [piece0ToU_tmul]
      have hgen := balancing_gen_mem U 0 W.vacuum x u
      rw [anmRight_zero_zero, zhuMul_vacuum_left] at hgen
      exact hgen
  | add z1 z2 h1 h2 =>
      have hsplit : (z1 + z2) - mkAnm W 0 0 W.vacuum ⊗ₜ[ℂ] piece0ToU W U (z1 + z2)
          = (z1 - mkAnm W 0 0 W.vacuum ⊗ₜ[ℂ] piece0ToU W U z1)
            + (z2 - mkAnm W 0 0 W.vacuum ⊗ₜ[ℂ] piece0ToU W U z2) := by
        rw [map_add, TensorProduct.tmul_add]; abel
      rw [hsplit]
      exact Submodule.add_mem _ h1 h2

/-- **At `n = 0` the balancing submodule IS the B0 balancing kernel** `ker(piece0ToU)`.  The span
balancing (this file) and the B0 action-map kernel (`MUBalancedBottom`) agree. -/
theorem balancing_zero_eq_ker (U : AMod W) :
    balancing W U 0 = LinearMap.ker (piece0ToU W U) := by
  refine le_antisymm (balancing_le_ker U) ?_
  intro z hz
  rw [LinearMap.mem_ker] at hz
  have h := sub_bottom_mem_balancing U z
  rwa [hz, TensorProduct.tmul_zero, sub_zero] at h

/-- **`MUPieceBal W U 0 ≅ U`.**  The balanced bottom recovers `U` (the DJ `M(U)(0) ≅ U`), because the
`n = 0` balancing is exactly `ker(piece0ToU)` and `piece0ToU` is surjective. -/
noncomputable def muPieceBal0EquivU (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    MUPieceBal W U 0 ≃ₗ[ℂ] U.carrier :=
  (Submodule.quotEquivOfEq _ _ (balancing_zero_eq_ker U)).trans
    (LinearMap.quotKerEquivOfSurjective (piece0ToU W U) (piece0ToU_surjective U))

/-- **`MUPieceBal W U 0 ≃ MUBalBottom W U`.**  The `n = 0` balanced piece of this file matches the
proved balanced bottom (`ZhuVermaAnArchMUBalancedBottom`), confirming the B0 pattern. -/
noncomputable def muPieceBal0Equiv (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    MUPieceBal W U 0 ≃ₗ[ℂ] MUBalBottom W U :=
  (muPieceBal0EquivU W U).trans (muBalBottomEquiv W U).symm

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
