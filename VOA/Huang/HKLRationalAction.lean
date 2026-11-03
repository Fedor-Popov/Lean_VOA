/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLNiceMain
import VOA.Huang.RepPackagingSemisimple
import VOA.Huang.BraidRibbonRealization
import VOA.Modules.OrdSubmodule
import VOA.Huang.HKLRationalSeparable
import VOA.Huang.HKLRationalSemisimple

/-!
# HKL rationality, part 1: the `A`-action of an ordinary `W`-module

For the HKL extension `W = extVOA F μ η …` (carrier `A`) and an ordinary `W`-module `N` on `M`:

* `actIntertwiner N` — the module vertex operator `Y_N(a, z)x` restricted to `a ∈ A` is an
  intertwining operator of type `(M; A, M)` of `V`-modules (`M` restricted along `η`,
  `restrictOrd`): truncation and `L₋₁`-derivative from `isIntertwiningOperator_moduleModes`,
  Jacobi for `u ∈ V` = module Jacobi for `η u` (`ext_unit_left_int`);
* `act N : A ⊠ X_N ⟶ X_N` — the induced morphism of `Ordinary V` (universal property of the
  fusion product), `act_intertwiner`;
* `act_unit` — **left unit law** `(η ⊠ 1) ≫ act = λ` (vacuum axiom / restriction);
* `isModeHom_of_linear` — an `A`-linear morphism `X_N ⟶ X_P` of `Ordinary V` intertwines all
  `W`-modes.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Huang.HKLRational

open CategoryTheory MonoidalCategory Limits Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.FusionUnit
  VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon VOA.Huang.HKLExt VOA.Huang.HKLNice

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
variable {F : FusionChoice V} {A : Ordinary V} {m : tensorObj F A A ⟶ A}
  {η : vacuumObject ⟶ A}
  {hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom}
  {hr : tensorHom F (𝟙 A) η ≫ m = (rightUnitor F A).hom} {htw : (twistIso A).hom = 𝟙 A}
  {hloc : ∀ a b : A.carrier, Local (extField F m a) (extField F m b)}
  {hvac : A.isMod.weight 0 = ℂ ∙ η.val V.vacuum}
  {hpos : ∀ k : ℤ, k < 0 → A.isMod.weight (k : ℂ) = ⊥}

/-- On `W`, the adjoint modes of `η u` are the `V`-module modes of `A`. -/
theorem adj_mode_eta (u : 𝒱) (k : ℤ) (a : A.carrier) :
    mode ((adjointModule (extVOA F m η hl hr htw hloc hvac hpos)).YM (η.val u)) k a =
      mode (A.isMod.YM u) k a := by
  change (extVOA F m η hl hr htw hloc hvac hpos).smul (η.val u) k a = _
  rw [extVOA_smul, ext_unit_left_int F m η hl]

/-- **The module vertex operator restricted to `A` is a `V`-intertwining operator** of type
`(M; A, M)`. -/
theorem isIntertwiningOperator_act {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M) :
    IsIntertwiningOperator A.isMod (restrictOrd N) (restrictOrd N) (moduleModes N) := by
  have hW := isIntertwiningOperator_moduleModes N
  refine ⟨hW.truncation, ?_, ?_⟩
  · intro a n
    have hL : A.isMod.Lm1 a =
        (adjointModule (extVOA F m η hl hr htw hloc hvac hpos)).Lm1 a := by
      simp only [OrdVModule.Lm1]
      rw [extVOA_conformalVector, adj_mode_eta]
    rw [hL]
    exact hW.L_neg_one a n
  · intro u a x ℓ k n
    have h := hW.jacobi (η.val u) a x ℓ k n
    convert h using 3
    rw [adj_mode_eta]

/-- The `A`-action intertwiner of an ordinary `W`-module. -/
def actIntertwiner {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M) :
    IntertwiningOperator A.isMod (restrictOrd N) (restrictOrd N) :=
  ⟨moduleModes N, isIntertwiningOperator_act N⟩

/-- The underlying object of `Ordinary V`. -/
abbrev actObj {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M) : Ordinary V :=
  Ordinary.of (restrictOrd N)

/-- **The action morphism** `A ⊠ X_N ⟶ X_N` of an ordinary `W`-module. -/
def act {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M) :
    tensorObj F A (actObj N) ⟶ actObj N :=
  (F A (actObj N)).lift (actObj N).isMod (actIntertwiner N)

@[simp] theorem act_intertwiner {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M) (n : ℂ) (a : A.carrier)
    (x : M) :
    (act N).val ((F A (actObj N)).intertwiner.val n a x) = moduleModes N n a x :=
  congrArg (fun Z : IntertwiningOperator A.isMod (actObj N).isMod (actObj N).isMod => Z.val n a x)
    ((F A (actObj N)).lift_spec _ _)

theorem act_intertwiner_int {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M) (k : ℤ) (a : A.carrier)
    (x : M) :
    (act N).val ((F A (actObj N)).intertwiner.val (k : ℂ) a x) = mode (N.YM a) k x := by
  rw [act_intertwiner, moduleModes_apply_intCast]

/-- The modes of the restricted module along `η`. -/
theorem moduleModes_restrict {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M) (n : ℂ) (v : 𝒱) :
    moduleModes (restrictOrd N) n v = moduleModes N n (η.val v) := by
  unfold moduleModes
  split_ifs <;> rfl

/-- **Left unit law of the action.** -/
theorem act_unit {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M) :
    tensorHom F η (𝟙 (actObj N)) ≫ act N = (leftUnitor F (actObj N)).hom := by
  apply tensor_hom_ext F
  intro n v x
  rw [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply, act_intertwiner,
    leftUnitor_intertwiner]
  change _ = moduleModes (restrictOrd N) n v x
  rw [moduleModes_restrict]

end VOA.Huang.HKLRational
