/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJCarrierIterate
import VOA.Modules.ZhuVermaAnArchDLM3Survive

/-!
# `DJCarrier W U` is a `WeakModule`, and its graded / lowest-weight packaging

`ZhuVermaAnArchDJ48BdryHolds` proved Dong–Jiang Lemma 4.7 (the commutator formula) on the balanced
carrier `M(U) = DJCarrier W U = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U` **unconditionally at base level `0`**
(`djModeZero_commutator_gen`), and `ZhuVermaAnArchDJCarrierIterate` proved the `ℓ < 0` half of
Dong–Jiang Lemma 4.9 there (`djModeZero_iterate_neg`), also unconditionally.  This file supplies
the packaging that turns those two identities into a genuine weak module:

1. the **`L₋₁` translation relation** `(L₋₁a)₍ₘ₎ + m·a₍ₘ₋₁₎ = 0` on `DJCarrier`
   (`djActGen_hderiv`), which is DJ Lemma 2.8's right inclusion applied to the grading generator
   `anmLgen`, exactly as in the `⊗_ℂ` template `muFullActGen_hderiv`;
2. the **Lie-morphism assembly** `V̂ →ₗ⁅ℂ⁆ End ℂ (DJCarrier W U)` (`djRhoZero`), built from 1 and
   `djModeZero_commutator_gen` through `VHat.assembleModeData`;
3. hence the **`ℓ ≥ 0` half of `ModuleIterate` for free** (`moduleIterate_nonneg`, which needs a
   `VHatRep`, which is exactly what item 2 provides), and with the `ℓ < 0` half
   the full `ModuleIterate (djRhoZero W U)`;
4. hence `IsModuleJacobi` (`isModuleJacobi_of_iterate`) and
   **`djCarrierWeak W U : WeakModule W (DJCarrier W U)`** (`weakModuleOfRep`), with
   `#print axioms` `[propext, Classical.choice, Quot.sound]` and **zero carried hypotheses**.

## Contents

### §1–§4 The `V̂`-representation and the weak module (unconditional)
`djActGen`, `djPieceAct_Lgen_zero`, `djActGen_hderiv`, `assembleAct_bracket_eval`,
`djActGen_bracket`, `djModeDataZero`, `djRhoZero`, `djRhoZero_actMode`, `djActModeTruncated`,
`djVacuumCreation`, `moduleIterate_djRhoZero`, `isModuleJacobi_djRhoZero`, `djCarrierWeak`.

### §5 The `ℕ`-grading is a module grading (unconditional)
`DJCarrier.deg` with the proved `DJCarrier.isInternal_deg`; `djCarrierWeak_act_deg_mem` and
`djCarrierWeak_act_deg_eq_zero` record DJ's level shift `a₍ₚ₎ : M(U)(n) → M(U)(wt a − p − 1 + n)`.

### §6 The `ℂ`-weight grading and the lowest-weight packaging
⚠ **`OrdVModule` CANNOT be used here, and this is a mathematical fact, not a gap.**  `OrdVModule`
(`Modules.WeakModule`) carries the field `finrank : ∀ α, FiniteDimensional ℂ (weight α)`.  The
bottom of `M(U)` is `U` (§7), and the module the gate is instantiated at is the **regular**
`A(𝒱)`-module `U = A(𝒱)`, which is infinite-dimensional in general.  So `OrdVModule W (DJCarrier W U)`
is **false** at the scope the bijection needs, and no finite-dimensionality hypothesis is
introduced.  Instead this file defines the finrank-free bundled object

  `GradedLWWeakModule W M h` = `WeakModule` + `weight` + `isInternal` + `L0_weight`
                             + `boundedBelow` + `isLow` + `realized`,

i.e. **`OrdVModule` + `IsLowestWeight` + realizedness, minus `finrank`** — the repo's `LWModule`
with that one field deleted — and builds `djGradedLW`, whose only carried inputs are the grading
scalar `hL0` (`L₀ = h + n` on `M(U)(n)`, a genuine datum about `U`, not about `𝒱`) and the bottom
nonvanishing `hbot` (discharged in §7 from `BottomProjection` plus nontriviality of `U`).

### §7 The bottom `M(U)(0) ≅ U`, conditional on `BottomProjection`
`djCarrierWeak_bottom_equiv` is the proved `djCarrierDegZeroEquivOfPbwDatum`, whose only input is
the explicit assumption `Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))`, carried in
every parameterized signature. The project-level witness is supplied by
`voaPBWBottomProjection`, from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`.
`djCarrier_deg_zero_ne_bot` upgrades it to `M(U)(0) ≠ 0` on the `AModScope`-style scoped
nontriviality `Nontrivial U.carrier` (which is NOT free: `zeroAMod` refutes the unscoped form,
`ZhuVermaAnArchAModScope`).  `djGradedLW_of_pbwDatum` assembles §6 + §7.

## Engine verification

Nothing new is verified numerically here: every scalar/combinatorial identity consumed
(`(★)`, DJ 2.3, DJ 4.7's four regimes, the Vandermonde vacuum coefficient) was engine-checked in
the files that proved it.  This file is
*packaging*: it introduces no new identity, only the translation relation, which is
`anmGen_Lgen_acting_mem` — already proved and already used by the `⊗_ℂ` carrier.

Proof-term audit: `#print axioms` is clean and the declarations do not use `pbw`; §7 is nevertheless
conditional on its explicit `Pr` parameter, which `#print axioms` does not report. The project-level
witness is supplied separately by `voaPBWBottomProjection`, from the generic relative-induction
field of the theorem `VOA.pbw : PBWPrinciple`. `sorry`-free.

## References
Dong–Jiang math/0601626 §4 (Lemmas 4.6–4.9, Thm 4.13); Gannon Def. 5.3.1a–c, Thm 5.3.4;
`ZhuVermaAnArchDJAction` (`djMode`, `djModeZero`, `djPieceAct`, `djPiece_ext`),
`ZhuVermaAnArchDJ48BdryHolds` (`djModeZero_commutator_gen`),
`ZhuVermaAnArchDJCarrierIterate` (`djModeZero_iterate_neg`, `djItRHS`),
`ZhuVermaAnArchVHatModeData` (`assembleAct`, `assembleModeData`),
`ZhuVermaAnArchMUFullRho` (`anmGen_Lgen_acting_mem`, the `hderiv` template),
`ZhuVermaAnArchMUFullBracketClose` (`assembleAct_bracket_apply`, the `hbracket` template),
`ZhuVermaAnArchMUjacobi` (`ActModeTruncated`, `ModuleIterate`, `isModuleJacobi_of_iterate`),
`ZhuVermaAnArchIterateNonneg` (`moduleIterate_nonneg`),
`ZhuVermaAnArchMUModuleDataBuild` (`VacuumCreation`, `weakModuleOfRep`),
`ZhuVermaAnArchDLM3Survive` (`djCarrierDegZeroEquivOfPbwDatum`, the independent regular-module
`BottomProjection` datum),
`ZhuVermaAnArchAModScope` (why `Nontrivial U.carrier` is a genuine scope, not a free fact).
-/

namespace VOA

open VertexOperatorAlgebra
open VHat VHat.VHatRep
open Finsupp
open scoped BigOperators TensorProduct DirectSum

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §0 Extensionality on the graded carrier -/

/-- Two endomorphisms of `M(U) = ⨁ₙ M(U)(n)` agreeing on every graded piece are equal. -/
theorem djCarrier_end_ext {W : VertexOperatorAlgebra 𝒱} {U : AmMod W 0}
    {f g : Module.End ℂ (DJCarrier W U)}
    (h : ∀ (n : ℕ) (x : DJPiece W U n),
      f (DJCarrier.incl W U n x) = g (DJCarrier.incl W U n x)) : f = g := by
  refine DirectSum.linearMap_ext ℂ (fun n => ?_)
  refine LinearMap.ext (fun x => ?_)
  simp only [LinearMap.comp_apply]
  show f (DJCarrier.incl W U n x) = g (DJCarrier.incl W U n x)
  exact h n x

/-! ## §1 The loop-mode generator family on `DJCarrier` -/

/-- **The `M(U)` mode family at base level `0`**, `m ↦ (a ↦ a₍ₘ₎)`, bundled `ℂ`-linearly in the
acting vector — the input of `VHat.assembleModeData`.  The balanced-carrier analogue of
`muFullActGen`. -/
noncomputable def djActGen (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (m : ℤ) :
    𝒱 →ₗ[ℂ] Module.End ℂ (DJCarrier W U) where
  toFun a := djModeZero W U m a
  map_add' a b := djMode_add_acting U (djActionDescent_zero W) m a b
  map_smul' c a := djMode_smul_acting U (djActionDescent_zero W) m c a

@[simp] theorem djActGen_apply (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (m : ℤ) (a : 𝒱) :
    djActGen W U m a = djModeZero W U m a := rfl

/-! ## §2 The translation relation `(L₋₁a)₍ₘ₎ + m·a₍ₘ₋₁₎ = 0` -/

/-- **The grading generator in the acting slot is killed on the balanced piece.**  For `a`
homogeneous of weight `K` and `m = K − N + n`,
`(L₋₁a) ∗^N_{0,n} − + m·(a ∗^N_{0,n} −) = 0` as an operator `M(U)(n) → M(U)(N)`.

This is the representative-level `anmGen_Lgen_acting_mem` (DJ Lemma 2.8's right inclusion applied
to the DJ grading generator `anmLgen`) pushed through the balancing quotient.  Unconditional. -/
theorem djPieceAct_Lgen_zero {W : VertexOperatorAlgebra 𝒱} (U : AmMod W 0) {K : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading K) {N n : ℕ} {m : ℤ} (hm : m = K - (N : ℤ) + (n : ℤ))
    (h : DJLeftSlot W N 0 n) :
    djPieceAct W U N n h (W.L (-1) a) + (m : ℂ) • djPieceAct W U N n h a = 0 := by
  refine djPiece_ext (f := djPieceAct W U N n h (W.L (-1) a)
    + (m : ℂ) • djPieceAct W U N n h a) (g := 0) ?_
  intro g w
  have hz : mkAnmFull W N 0
      (anmGen W N 0 n (W.L (-1) a) g + (m : ℂ) • anmGen W N 0 n a g) = 0 := by
    rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact anmGen_Lgen_acting_mem W ha hm g
  have hrw : mkDJPiece W U N (mkAnmFull W N 0
        (anmGen W N 0 n (W.L (-1) a) g + (m : ℂ) • anmGen W N 0 n a g) ⊗ₜ[ℂ] w)
      = mkDJPiece W U N (mkAnmFull W N 0 (anmGen W N 0 n (W.L (-1) a) g) ⊗ₜ[ℂ] w)
        + (m : ℂ) • mkDJPiece W U N (mkAnmFull W N 0 (anmGen W N 0 n a g) ⊗ₜ[ℂ] w) := by
    rw [map_add, map_smul, TensorProduct.add_tmul, ← TensorProduct.smul_tmul', map_add, map_smul]
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply, djPieceAct_mk,
    djPieceAct_mk, ← hrw, hz, TensorProduct.zero_tmul, map_zero]

/-- **The translation relation on `M(U)`, unconditional** — the `hderiv` input of
`VHat.assembleModeData`: `(L₋₁a)₍ₘ₎ + m·a₍ₘ₋₁₎ = 0` on the balanced Dong–Jiang carrier.  (DJ's
`o_{n,m}(L₋₁v) = −(wt v + m − n)·o_{n,m}(v)` in mode form.) -/
theorem djActGen_hderiv (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (a : 𝒱) (m : ℤ) :
    djActGen W U m (W.L (-1) a) + (m : ℂ) • djActGen W U (m - 1) a = 0 := by
  refine reduce_homogeneous W (P := fun a =>
    djActGen W U m (W.L (-1) a) + (m : ℂ) • djActGen W U (m - 1) a = 0) ?_ ?_ ?_ a
  · intro K a ha
    have haL : W.L (-1) a ∈ W.grading (K + 1) := W.L_neg_one_raise ha
    refine djCarrier_end_ext (fun n x => ?_)
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply, djActGen_apply,
      djActGen_apply, djModeZero, djModeZero, djMode_apply_incl U (djActionDescent_zero W) m haL,
      djMode_apply_incl U (djActionDescent_zero W) (m - 1) ha]
    have hT₁ : muTargetLevel (K + 1) m n = K - m + (n : ℤ) := by
      simp only [muTargetLevel]; ring
    have hT₂ : muTargetLevel K (m - 1) n = K - m + (n : ℤ) := by
      simp only [muTargetLevel]; ring
    by_cases hnn : 0 ≤ K - m + (n : ℤ)
    · obtain ⟨N, hN⟩ : ∃ N : ℕ, K - m + (n : ℤ) = (N : ℤ) :=
        ⟨_, (Int.toNat_of_nonneg hnn).symm⟩
      rw [djLevelIncl_eq_of_target U (djActionDescent_zero W) (by rw [hT₁, hN]) (W.L (-1) a),
        djLevelIncl_eq_of_target U (djActionDescent_zero W) (by rw [hT₂, hN]) a,
        LinearMap.comp_apply, LinearMap.comp_apply, ← map_smul, ← map_add]
      rw [show djPieceAct W U N n (djActionDescent_zero W N n) (W.L (-1) a) x
            + (m : ℂ) • djPieceAct W U N n (djActionDescent_zero W N n) a x = 0 from by
          have hz := djPieceAct_Lgen_zero U ha (show m = K - (N : ℤ) + (n : ℤ) from by omega)
            (djActionDescent_zero W N n)
          have hz' := congrArg (fun f : DJPiece W U n →ₗ[ℂ] DJPiece W U N => f x) hz
          simpa using hz']
      exact map_zero _
    · rw [djLevelIncl_of_neg U (djActionDescent_zero W) (by rw [hT₁]; omega) (W.L (-1) a),
        djLevelIncl_of_neg U (djActionDescent_zero W) (by rw [hT₂]; omega) a]
      simp
  · simp [djModeZero_zero_acting]
  · intro x y hx hy
    rw [map_add, map_add, map_add, smul_add]
    rw [show djActGen W U m (W.L (-1) x) + djActGen W U m (W.L (-1) y)
          + ((m : ℂ) • djActGen W U (m - 1) x + (m : ℂ) • djActGen W U (m - 1) y)
        = (djActGen W U m (W.L (-1) x) + (m : ℂ) • djActGen W U (m - 1) x)
          + (djActGen W U m (W.L (-1) y) + (m : ℂ) • djActGen W U (m - 1) y) from by abel]
    rw [hx, hy, add_zero]

/-! ## §3 The Borcherds loop commutator — the `hbracket` input -/

/-- **The `V̂`-bracket generator, evaluated through an arbitrary assembled mode family.**  For any
`ℂ`-linear per-degree family `actGen`, `assembleAct actGen ([a(m), b(k)])` is the operator OPE tail
`∑ᵢ C(m,i)·(a₍ᵢ₎b)₍ₘ₊ₖ₋ᵢ₎`.  (The carrier-agnostic form of `assembleAct_bracket_apply`.) -/
theorem assembleAct_bracket_eval {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M]
    [Module ℂ M] (actGen : ℤ → (𝒱 →ₗ[ℂ] Module.End ℂ M)) (a b : 𝒱) (m k : ℤ) (y : M) :
    assembleAct actGen (vloopBracket W (single m a) (single k b)) y
      = ∑ᶠ i : ℕ, gBinom m i • actGen (m + k - (i : ℤ)) (W.smul a (i : ℤ) b) y := by
  have hvb : vloopBracket W (single m a) (single k b)
      = ∑ᶠ i : ℕ, brLevel W m i a (single k b) := by
    rw [vloopBracket, Finsupp.lsum_single, bracketLeft_apply]
  have hfin : (Function.support fun i : ℕ => brLevel W m i a (single k b)).Finite :=
    brLevel_support_finite W m a (single k b)
  let ev : Module.End ℂ M →ₗ[ℂ] M :=
    { toFun := fun f => f y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := map_finsum (ev.comp (assembleAct actGen)) hfin
  rw [hvb]
  show ev (assembleAct actGen (∑ᶠ i : ℕ, brLevel W m i a (single k b))) = _
  rw [show ev (assembleAct actGen (∑ᶠ i : ℕ, brLevel W m i a (single k b)))
      = ∑ᶠ i : ℕ, ev (assembleAct actGen (brLevel W m i a (single k b))) from h]
  refine finsum_congr fun i => ?_
  rw [brLevel_single, map_smul, map_smul]
  show gBinom m i • ev (assembleAct actGen (single (m + k - (i : ℤ))
      (W.smul a (i : ℤ) b))) = _
  rw [assembleAct_single]
  rfl

/-- **Dong–Jiang Lemma 4.7 on `M(U)` in the `assembleModeData` form — unconditional.**
`assembleAct (djActGen W U) ([a(m), b(k)]) = ⁅a₍ₘ₎, b₍ₖ₎⁆` on the balanced carrier.  This is the
`hbracket` input; the mathematical content is the proved `djModeZero_commutator_gen`, which needs
no homogeneity and no hypothesis. -/
theorem djActGen_bracket (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (a b : 𝒱) (m k : ℤ) :
    assembleAct (djActGen W U) (vloopBracket W (single m a) (single k b))
      = ⁅djActGen W U m a, djActGen W U k b⁆ := by
  refine LinearMap.ext (fun y => ?_)
  rw [assembleAct_bracket_eval (djActGen W U) a b m k y]
  show _ = (djActGen W U m a * djActGen W U k b - djActGen W U k b * djActGen W U m a) y
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  exact (djModeZero_commutator_gen W U a b m k y).symm

/-! ## §4 The `V̂`-representation and the weak module -/

/-- **The `V̂`-mode data of the balanced carrier `M(U)`** — assembled from the unconditional
translation relation `djActGen_hderiv` and the unconditional commutator `djActGen_bracket`. -/
noncomputable def djModeDataZero (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) :
    VHat.VHatModeData W (DJCarrier W U) :=
  assembleModeData (djActGen W U) (djActGen_hderiv W U) (djActGen_bracket W U)

/-- **`M(U) = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U` as a `V̂`-representation, unconditional.**  The object
whose absence blocked the `ℓ ≥ 0` half of `ModuleIterate` on the balanced carrier. -/
noncomputable def djRhoZero (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) :
    VHat.VHatRep W (DJCarrier W U) :=
  (djModeDataZero W U).toRep

/-- The `𝒱`-modes of `djRhoZero` are exactly Dong–Jiang's modes `djModeZero`. -/
@[simp] theorem djRhoZero_actMode (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (a : 𝒱) (m : ℤ) :
    (djRhoZero W U).actMode a m = djModeZero W U m a := by
  rw [djRhoZero, VHatModeData.toRep_actMode]
  show assembleAct (djActGen W U) (single m a) = _
  rw [assembleAct_single]
  rfl

/-- **DJ Lemma 4.6(1)** in the `ActModeTruncated` interface — unconditional. -/
theorem djActModeTruncated (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) :
    ActModeTruncated (djRhoZero W U) := by
  intro a x
  obtain ⟨N, hN⟩ := djModeZero_truncation W U a x
  exact ⟨N, fun m hm => by rw [djRhoZero_actMode]; exact hN m hm⟩

/-- **DJ Lemma 4.6(2)** in the `VacuumCreation` interface — unconditional. -/
theorem djVacuumCreation (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) :
    VacuumCreation (djRhoZero W U) := by
  intro m
  rw [djRhoZero_actMode]
  exact djModeZero_vacuum W U m

/-- **`ModuleIterate (djRhoZero W U)` — Dong–Jiang Lemma 4.9 on the BALANCED carrier, in full,
unconditional.**  The `ℓ < 0` half is the proved `djModeZero_iterate_neg` (transported from the
pure-`𝒱` theorem `(★)`); the `ℓ ≥ 0` half is free, because `djRhoZero` supplies the `VHatRep`
that `moduleIterate_nonneg` requires. -/
theorem moduleIterate_djRhoZero (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) :
    ModuleIterate (djRhoZero W U) := by
  intro u v x ℓ N
  rcases lt_or_ge ℓ 0 with hneg | hpos
  · have h := djModeZero_iterate_neg W U hneg N u v x
    rw [djItRHS] at h
    simpa only [djRhoZero_actMode] using h
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    exact moduleIterate_nonneg (djRhoZero W U) (djActModeTruncated W U) u v x j N

/-- **The module Jacobi 5.3.1b on the balanced carrier — unconditional.** -/
theorem isModuleJacobi_djRhoZero (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) :
    (djRhoZero W U).IsModuleJacobi :=
  isModuleJacobi_of_iterate (djRhoZero W U) (djActModeTruncated W U) (moduleIterate_djRhoZero W U)

/-- **`M(U) = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U` IS A WEAK `𝒱`-MODULE — unconditionally.**

Dong–Jiang Theorem 4.13's module structure on the **balanced** carrier, with **zero carried
hypotheses**: truncation is DJ 4.6(1), the vacuum normalization DJ 4.6(2), and the Jacobi identity
comes from DJ 4.7 (`djModeZero_commutator_gen`) plus DJ 4.9 (`moduleIterate_djRhoZero`) through
`isModuleJacobi_of_iterate`.  No PBW datum, no `DJAnnEqAn`, no `DJ48Bdry`, no
`LeftGradingResidual` — `DJActionDescent W 0` is the theorem `djActionDescent_zero`. -/
noncomputable def djCarrierWeak (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) :
    WeakModule W (DJCarrier W U) :=
  weakModuleOfRep (djRhoZero W U) (djActModeTruncated W U) (djVacuumCreation W U)
    (isModuleJacobi_djRhoZero W U)

/-- The weak-module action is Dong–Jiang's mode `a₍ₚ₎`. -/
@[simp] theorem djCarrierWeak_act (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (a : 𝒱) (p : ℤ)
    (x : DJCarrier W U) : (djCarrierWeak W U).act a p x = djModeZero W U p a x := by
  rw [djCarrierWeak, weakModuleOfRep_act, djRhoZero_actMode]

/-! ## §5 The `ℕ`-grading is a module grading -/

section Graded

variable {W : VertexOperatorAlgebra 𝒱}

/-- **DJ's level shift.**  For `a` homogeneous of weight `k`, the mode `a₍ₚ₎` maps the level-`n`
piece into level `wt a − p − 1 + n` whenever that is `≥ 0`. -/
theorem djCarrierWeak_act_deg_mem (U : AmMod W 0) {k p : ℤ} {a : 𝒱} (ha : a ∈ W.grading k)
    {n N : ℕ} (hN : muTargetLevel k p n = (N : ℤ)) {x : DJCarrier W U}
    (hx : x ∈ DJCarrier.deg W U n) :
    (djCarrierWeak W U).act a p x ∈ DJCarrier.deg W U N := by
  obtain ⟨y, rfl⟩ := hx
  rw [djCarrierWeak_act, djModeZero, djMode_apply_incl U (djActionDescent_zero W) p ha,
    djLevelIncl_eq_of_target U (djActionDescent_zero W) hN a, LinearMap.comp_apply]
  exact ⟨_, rfl⟩

/-- **DJ's truncation, graded form.**  The mode `a₍ₚ₎` annihilates the level-`n` piece once the
target level `wt a − p − 1 + n` is negative. -/
theorem djCarrierWeak_act_deg_eq_zero (U : AmMod W 0) {k p : ℤ} {a : 𝒱} (ha : a ∈ W.grading k)
    {n : ℕ} (hneg : muTargetLevel k p n < 0) {x : DJCarrier W U}
    (hx : x ∈ DJCarrier.deg W U n) : (djCarrierWeak W U).act a p x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  rw [djCarrierWeak_act, djModeZero, djMode_apply_incl U (djActionDescent_zero W) p ha,
    djLevelIncl_of_neg U (djActionDescent_zero W) hneg a, LinearMap.zero_apply]

end Graded

/-! ## §6 The `ℂ`-weight grading and the finrank-free lowest-weight packaging

⚠ `OrdVModule` is **unusable** here: its `finrank` field asserts that every weight space is
finite-dimensional, and the bottom of `M(U)` is `U` — which for the regular module `U = A(𝒱)` (the
instance the gate and the bijection need) is infinite-dimensional.  The structure below is exactly
`LWModule`'s content with that single field removed. -/

/-- **A `ℂ`-graded, bounded-below, lowest-weight weak module — WITHOUT the finite-dimensionality
field.**  Precisely `OrdVModule` + `IsLowestWeight h` + realizedness, minus `OrdVModule.finrank`.  The
deleted field is a pure conduit (nothing in the Zhu bijection chain consumes it) and it is FALSE
for the bottoms the bijection ranges over, so it is deliberately absent. -/
structure GradedLWWeakModule (W : VertexOperatorAlgebra 𝒱) (M : Type v) [AddCommGroup M]
    [Module ℂ M] (h : ℂ) extends WeakModule W M where
  /-- The complex weight grading `M = ⊕_α M_α`. -/
  weight : ℂ → Submodule ℂ M
  /-- The grading is a genuine internal direct sum. -/
  isInternal : DirectSum.IsInternal weight
  /-- **5.3.1c.** `M_α` is the `L₀`-eigenspace of eigenvalue `α`. -/
  L0_weight : ∀ (α : ℂ) (x : M), x ∈ weight α → mode (YM W.conformalVector) 1 x = α • x
  /-- Bounded below in the real part of the weight. -/
  boundedBelow : ∃ B : ℝ, ∀ α : ℂ, weight α ≠ ⊥ → B ≤ α.re
  /-- `h` is a lowest weight: every nonzero weight space sits at `h + ℕ`. -/
  isLow : ∀ α : ℂ, weight α ≠ ⊥ → ∃ n : ℕ, α = h + n
  /-- The lowest weight is *realized*: the bottom layer is nonzero. -/
  realized : weight h ≠ ⊥

section CWeight

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The `ℂ`-weight grading of `M(U)`**: the level-`n` piece placed at complex weight `h + n`. -/
noncomputable def djCWeight (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (h : ℂ) (α : ℂ) :
    Submodule ℂ (DJCarrier W U) :=
  ⨆ (n : ℕ) (_ : h + n = α), DJCarrier.deg W U n

theorem djCWeight_cast (U : AmMod W 0) (h : ℂ) (m : ℕ) :
    djCWeight W U h (h + m) = DJCarrier.deg W U m := by
  unfold djCWeight
  refine le_antisymm (iSup_le fun n => iSup_le fun hn => ?_)
    (le_iSup_of_le m (le_iSup_of_le rfl le_rfl))
  have hnm : n = m := by
    have hc : (n : ℂ) = (m : ℂ) := by linear_combination hn
    exact_mod_cast hc
  rw [hnm]

theorem djCWeight_eq_bot (U : AmMod W 0) (h : ℂ) {α : ℂ} (hne : ∀ n : ℕ, h + n ≠ α) :
    djCWeight W U h α = ⊥ :=
  iSup_eq_bot.mpr fun n => iSup_eq_bot.mpr fun hn => absurd hn (hne n)

/-- **The `ℂ`-weight grading of `M(U)` is a genuine internal direct-sum decomposition**, off the
proved `DJCarrier.isInternal_deg`.  Unconditional. -/
theorem djCWeight_isInternal (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (h : ℂ) :
    DirectSum.IsInternal (djCWeight W U h) := by
  have hN := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
    (DJCarrier.deg W U)).mp (DJCarrier.isInternal_deg W U)
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · refine iSupIndep_extend (DJCarrier.deg W U) (djCWeight W U h) (fun n => h + n) ?_ ?_ hN.1
    · intro α hα; exact djCWeight_eq_bot U h (fun n hn => hα n hn)
    · intro n; exact djCWeight_cast U h n
  · rw [← hN.2]
    refine le_antisymm (iSup_le fun α => ?_)
      (iSup_le fun n => le_iSup_of_le (h + n) (by rw [djCWeight_cast U h n]))
    unfold djCWeight
    exact iSup_le fun n => iSup_le fun _ => le_iSup (DJCarrier.deg W U) n

/-- Every nonzero `ℂ`-weight space of `M(U)` sits at `h + ℕ`: `h` is a lowest weight. -/
theorem djCWeight_isLow (U : AmMod W 0) (h : ℂ) (α : ℂ) (hα : djCWeight W U h α ≠ ⊥) :
    ∃ n : ℕ, α = h + n := by
  by_cases hcase : ∃ n : ℕ, h + n = α
  · obtain ⟨n, rfl⟩ := hcase; exact ⟨n, rfl⟩
  · exact absurd (djCWeight_eq_bot U h (fun n hn => hcase ⟨n, hn⟩)) hα

/-- The `ℂ`-weight grading of `M(U)` is bounded below by `Re h`. -/
theorem djCWeight_boundedBelow (U : AmMod W 0) (h : ℂ) :
    ∃ B : ℝ, ∀ α : ℂ, djCWeight W U h α ≠ ⊥ → B ≤ α.re := by
  refine ⟨h.re, fun α hα => ?_⟩
  obtain ⟨n, rfl⟩ := djCWeight_isLow U h α hα
  simp only [Complex.add_re, Complex.natCast_re]
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The bottom `ℂ`-weight space of `M(U)` is the level-`0` piece. -/
theorem djCWeight_zero (U : AmMod W 0) (h : ℂ) : djCWeight W U h h = DJCarrier.deg W U 0 := by
  have hc := djCWeight_cast U h 0
  simpa using hc

/-- **`M(U)` as a `ℂ`-graded lowest-weight weak module (finrank-free).**

The only carried inputs are:

* `hL0` — the grading scalar `L₀ = h + n` on `M(U)(n)` (Gannon 5.3.1c).  This is a genuine datum
  about the bottom `U` (it says `[ω]` acts on `U` by the single scalar `h`; cf. `AMod.OmegaScalar`
  in `ZhuVermaAnArchAModScope`, where the unscoped version is refuted), **not** an identity about
  `𝒱`, so it cannot be proved here;
* `hbot` — `M(U)(0) ≠ 0`, discharged in §7 from the independent `BottomProjection` assumption plus
  `Nontrivial U.carrier`.

Everything else — the weak module, the grading, its internality, boundedness below and lowest
weightness — is unconditional. -/
noncomputable def djGradedLW (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (h : ℂ)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W U), x ∈ DJCarrier.deg W U n →
      djModeZero W U 1 W.conformalVector x = (h + n) • x)
    (hbot : DJCarrier.deg W U 0 ≠ ⊥) :
    GradedLWWeakModule W (DJCarrier W U) h where
  toWeakModule := djCarrierWeak W U
  weight := djCWeight W U h
  isInternal := djCWeight_isInternal W U h
  L0_weight := by
    intro α x hx
    by_cases hcase : ∃ n : ℕ, h + n = α
    · obtain ⟨n, rfl⟩ := hcase
      rw [djCWeight_cast U h n] at hx
      show (djCarrierWeak W U).act W.conformalVector 1 x = _
      rw [djCarrierWeak_act]
      exact hL0 n x hx
    · rw [djCWeight_eq_bot U h (fun n hn => hcase ⟨n, hn⟩), Submodule.mem_bot] at hx
      rw [hx, map_zero, smul_zero]
  boundedBelow := djCWeight_boundedBelow U h
  isLow := djCWeight_isLow U h
  realized := by rw [djCWeight_zero U h]; exact hbot

@[simp] theorem djGradedLW_weight (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (h : ℂ)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W U), x ∈ DJCarrier.deg W U n →
      djModeZero W U 1 W.conformalVector x = (h + n) • x)
    (hbot : DJCarrier.deg W U 0 ≠ ⊥) :
    (djGradedLW W U h hL0 hbot).weight = djCWeight W U h := rfl

@[simp] theorem djGradedLW_act (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (h : ℂ)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W U), x ∈ DJCarrier.deg W U n →
      djModeZero W U 1 W.conformalVector x = (h + n) • x)
    (hbot : DJCarrier.deg W U 0 ≠ ⊥) (a : 𝒱) (p : ℤ) (x : DJCarrier W U) :
    (djGradedLW W U h hL0 hbot).toWeakModule.act a p x = djModeZero W U p a x :=
  djCarrierWeak_act W U a p x

end CWeight

/-! ## §7 The bottom `M(U)(0) ≅ U`, conditional on `BottomProjection` -/

section Bottom

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- **`M(U)(0) ≅ U`** on the weak module built above. This is the proved
`djCarrierDegZeroEquivOfPbwDatum`; its **only** input is the independent assumption
`Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))`, displayed explicitly. The route is
`Pr ⟹ gate_of_pbwDatum : O_{0,0}(𝒱) = O(𝒱) ⟹ DJAnnEqAn W 0 ⟹ DJCarrier.degMEquiv`. The project-level
`regularAMod` witness is supplied by `voaPBWBottomProjection`, from the generic relative-induction
field of the theorem `VOA.pbw : PBWPrinciple`. -/
noncomputable def djCarrierWeak_bottom_equiv
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AmMod W 0) :
    DJCarrier.deg W U 0 ≃ₗ[ℂ] U.carrier :=
  djCarrierDegZeroEquivOfPbwDatum Pr U

/-- **`M(U)(0) ≠ 0` on the nontrivial scope.** Carried inputs: the independent
`BottomProjection` assumption `Pr` and the scoped
nontriviality `Nontrivial U.carrier`.  The latter is *not* free — `zeroAMod` is a legal bundled
module with zero carrier, which refutes the unscoped statement (`ZhuVermaAnArchAModScope`). -/
theorem djCarrier_deg_zero_ne_bot
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AmMod W 0)
    (hU : Nontrivial U.carrier) : DJCarrier.deg W U 0 ≠ ⊥ := by
  intro hbot
  obtain ⟨p, q, hpq⟩ := hU.exists_pair_ne
  refine hpq ?_
  set e := djCarrierWeak_bottom_equiv Pr U with he
  have hzero : ∀ z : DJCarrier.deg W U 0, z = 0 := by
    intro z
    have hz : (z : DJCarrier W U) = 0 := (Submodule.eq_bot_iff _).mp hbot _ z.2
    exact Subtype.ext hz
  have hsymm : e.symm p = e.symm q := by rw [hzero (e.symm p), hzero (e.symm q)]
  have := congrArg e hsymm
  rwa [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this

/-- **The full graded lowest-weight packaging of Dong–Jiang's `M(U)`.**

Carried hypotheses, all displayed:

* `Pr` — the explicit assumption `BottomProjection (parabolicRepOfAMod W (regularAMod W))`,
  the sole remaining input of the `(0,0)` gate; the companion
  `voaPBWBottomProjection` supplies this instance from the generic relative-induction field of the
  theorem `VOA.pbw : PBWPrinciple`;
* `hU : Nontrivial U.carrier` — the `AModScope` scoped nontriviality;
* `hL0` — the grading scalar `L₀ = h + n` on `M(U)(n)`.

Everything else, in particular the weak-module structure itself, is unconditional. -/
noncomputable def djGradedLW_of_pbwDatum
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AmMod W 0)
    (hU : Nontrivial U.carrier) (h : ℂ)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W U), x ∈ DJCarrier.deg W U n →
      djModeZero W U 1 W.conformalVector x = (h + n) • x) :
    GradedLWWeakModule W (DJCarrier W U) h :=
  djGradedLW W U h hL0 (djCarrier_deg_zero_ne_bot Pr U hU)

/-- The bottom weight space of the packaged object **is** `U`. -/
noncomputable def djGradedLW_bottom_equiv
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AmMod W 0)
    (hU : Nontrivial U.carrier) (h : ℂ)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W U), x ∈ DJCarrier.deg W U n →
      djModeZero W U 1 W.conformalVector x = (h + n) • x) :
    (djGradedLW_of_pbwDatum Pr U hU h hL0).weight h ≃ₗ[ℂ] U.carrier :=
  (LinearEquiv.ofEq _ _ (djCWeight_zero U h)).trans (djCarrierWeak_bottom_equiv Pr U)

end Bottom

/-! ## §8 The bridge to the proved generation statement

`ZhuVermaAnArchDJGeneration` proves DJ Theorem 4.13's generation sentence for `ℂ`-subspaces stable
under the raw modes (`DJModeStable`).  Since `DJCarrier` is a `WeakModule`, that predicate **is**
`WeakModule.Submodule'` of `djCarrierWeak`, so generation-from-the-bottom is a statement about
genuine weak submodules — the form the `L(U) = M(U)/J(U)` construction of C5 needs. -/

section Generation

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- A weak submodule of `djCarrierWeak W U` is mode-stable in the `DJGeneration` sense. -/
theorem djModeStable_of_weakSubmodule (U : AmMod W 0)
    (S : WeakModule.Submodule' (djCarrierWeak W U)) :
    DJModeStable W U (djActionDescent_zero W) S.carrier := by
  intro p a x hx
  have hmem := S.act_mem a p hx
  rwa [djCarrierWeak_act] at hmem

/-- Conversely, a mode-stable `ℂ`-subspace of `M(U)` is a weak submodule of `djCarrierWeak W U`. -/
noncomputable def weakSubmodule_of_djModeStable (U : AmMod W 0)
    (S : Submodule ℂ (DJCarrier W U)) (hS : DJModeStable W U (djActionDescent_zero W) S) :
    WeakModule.Submodule' (djCarrierWeak W U) where
  carrier := S
  act_mem := by
    intro a p x hx
    rw [djCarrierWeak_act]
    exact hS p a x hx

@[simp] theorem weakSubmodule_of_djModeStable_carrier (U : AmMod W 0)
    (S : Submodule ℂ (DJCarrier W U)) (hS : DJModeStable W U (djActionDescent_zero W) S) :
    (weakSubmodule_of_djModeStable U S hS).carrier = S := rfl

/-- **DJ Theorem 4.13's generation sentence, in weak-submodule form.** A weak submodule of
`M(U)` containing the bottom `M(U)(0) ≅ U` is everything. Carried input: the independent
`BottomProjection` assumption `Pr`
(through the bottom identification only — the weak-module structure itself is unconditional). -/
theorem djCarrierWeak_generated_by_bottom
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (U : AmMod W 0)
    (S : WeakModule.Submodule' (djCarrierWeak W U))
    (hU : ∀ w : U.carrier,
      (((djCarrierWeak_bottom_equiv Pr U).symm w : DJCarrier.deg W U 0) : DJCarrier W U)
        ∈ S.carrier) :
    S.carrier = ⊤ :=
  djCarrier_generated_by_U_of_pbwDatum Pr U (djActionDescent_zero W) S.carrier
    (djModeStable_of_weakSubmodule U S) hU

end Generation

/-! ## §9 The carried-hypothesis ledger

Recorded as a single statement so the exact dependency of this file's headlines is visible in one
place.

* `djCarrierWeak W U : WeakModule W (DJCarrier W U)` — **zero** carried hypotheses.  Likewise
  `djRhoZero`, `djActModeTruncated`, `djVacuumCreation`, `moduleIterate_djRhoZero`,
  `isModuleJacobi_djRhoZero`, `djCWeight_isInternal`, `djCWeight_isLow`, `djCWeight_boundedBelow`,
  `djCarrierWeak_act_deg_mem`, `djCarrierWeak_act_deg_eq_zero`, and the two `DJModeStable` bridges.
* `djGradedLW W U h hL0 hbot` — two carried hypotheses: the grading scalar `hL0` and the bottom
  nonvanishing `hbot`.
* `djGradedLW_of_pbwDatum Pr U hU h hL0` — three: the independent `BottomProjection` assumption
  `Pr`, the scoped nontriviality
  `hU`, and `hL0`.  `hbot` is discharged from `Pr` and `hU`.
* NOT provided, deliberately: `OrdVModule` / `LWModule`, because their `finrank` field is FALSE at the
  scope the bijection needs (see §6). -/
@[simp] theorem djCarrierWeak_mode (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (a : 𝒱)
    (p : ℤ) : mode ((djCarrierWeak W U).YM a) p = djModeZero W U p a :=
  LinearMap.ext fun x => djCarrierWeak_act W U a p x

end VOA

/-
Axiom check: run once, from
`scripts/audit/DJCarrierWeakAxiomAudit.lean` with

  lake env lean -DmaxSynthPendingDepth=3 scripts/audit/DJCarrierWeakAxiomAudit.lean

(a bare `lake env lean` drops the lakefile's `maxSynthPendingDepth` and silently inserts `sorryAx`
on these nested quotient/tensor carriers).  All 33 declarations of this file report exactly
`[propext, Classical.choice, Quot.sound]` — NO `pbw`, NO `sorryAx`, no new axiom.
-/
