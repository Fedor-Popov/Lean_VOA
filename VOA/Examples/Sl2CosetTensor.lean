/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteDifferential
import VOA.Examples.Sl2SemiInfiniteGhostEmbeddings

/-!
# Tensor products of translated affine sl2 actions

Diagonal current states on the actual tensor super vertex algebra obey the
full affine commutator at the sum of the two levels. Translation is the sum
of the factor translations. The three-factor specialization assembles matter
at levels `-4/3`, `1`, and `-11/3`, hence at total level `-4`.

The parity compatibility and convolution-grading hypotheses needed by the
existing tensor-SVA construction remain explicit. No affine commutator,
translation, or BRST nilpotency assumption is added to those on the factors.
-/

namespace VOA.Sl2SemiInfinite
open Module (End)
open AffineVOA
open scoped BigOperators TensorProduct
universe u v w
variable {M : Type u} {N : Type v} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup N] [Module ℂ N]
variable {V : SuperVertexAlgebra M} {W : SuperVertexAlgebra N} {k l : ℂ}

/-- The diagonal current is the sum of the two vacuum embeddings. -/
noncomputable def tensorCurrentState (A : AffineSl2Action V k)
    (B : AffineSl2Action W l) (a : Fin 3) : M ⊗[ℂ] N :=
  A.current a ⊗ₜ[ℂ] W.vacuum + V.vacuum ⊗ₜ[ℂ] B.current a

/-- Every total-current mode is the sum of the two factor modes. -/
theorem tensorCurrentMode_tmul (A : AffineSl2Action V k) (B : AffineSl2Action W l)
    (a : Fin 3) (n : ℤ)
    (x : M) (y : N) :
    mode (TensorVA.tenY V W (tensorCurrentState A B a)) n (x ⊗ₜ[ℂ] y) =
      mode (V.Y (A.current a)) n x ⊗ₜ[ℂ] y +
        x ⊗ₜ[ℂ] mode (W.Y (B.current a)) n y := by
  unfold tensorCurrentState
  rw [map_add, mode_add, LinearMap.add_apply]
  change TensorVA.tenY V W (A.current a ⊗ₜ[ℂ] W.vacuum)
      (-n - 1) (x ⊗ₜ[ℂ] y) +
    TensorVA.tenY V W (V.vacuum ⊗ₜ[ℂ] B.current a)
      (-n - 1) (x ⊗ₜ[ℂ] y) = _
  rw [tenY_left_unit, tenY_right_unit_even V W (B.current_even a)]
  rfl

/-- Full diagonal current commutator; the two factor levels add. -/
theorem tensorCurrentMode_commutator (A : AffineSl2Action V k)
    (B : AffineSl2Action W l) (a b : Fin 3) (m n : ℤ) :
    mode (TensorVA.tenY V W (tensorCurrentState A B a)) m *
        mode (TensorVA.tenY V W (tensorCurrentState A B b)) n -
      mode (TensorVA.tenY V W (tensorCurrentState A B b)) n *
        mode (TensorVA.tenY V W (tensorCurrentState A B a)) m =
      (∑ c, fabc a b c •
        mode (TensorVA.tenY V W (tensorCurrentState A B c)) (m + n)) +
      if m + n = 0 then ((m : ℂ) * (k + l) * kappa a b) • LinearMap.id else 0 := by
  apply TensorProduct.ext'
  intro x y
  have hM := congrArg (fun f : End ℂ M => f x) (A.current_comm a b m n)
  have hG := congrArg (fun f : End ℂ N => f y)
    (B.current_comm a b m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at hM hG
  simp only [LinearMap.sub_apply, Module.End.mul_apply, tensorCurrentMode_tmul,
    map_add, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  have heq :
      ((mode (V.Y (A.current a)) m (mode (V.Y (A.current b)) n x) ⊗ₜ[ℂ] y +
          mode (V.Y (A.current b)) n x ⊗ₜ[ℂ] mode (W.Y (B.current a)) m y) +
        (mode (V.Y (A.current a)) m x ⊗ₜ[ℂ] mode (W.Y (B.current b)) n y +
          x ⊗ₜ[ℂ] mode (W.Y (B.current a)) m (mode (W.Y (B.current b)) n y))) -
      ((mode (V.Y (A.current b)) n (mode (V.Y (A.current a)) m x) ⊗ₜ[ℂ] y +
          mode (V.Y (A.current a)) m x ⊗ₜ[ℂ] mode (W.Y (B.current b)) n y) +
        (mode (V.Y (A.current b)) n x ⊗ₜ[ℂ] mode (W.Y (B.current a)) m y +
          x ⊗ₜ[ℂ] mode (W.Y (B.current b)) n (mode (W.Y (B.current a)) m y))) =
      (mode (V.Y (A.current a)) m (mode (V.Y (A.current b)) n x) -
        mode (V.Y (A.current b)) n (mode (V.Y (A.current a)) m x)) ⊗ₜ[ℂ] y +
      x ⊗ₜ[ℂ] (mode (W.Y (B.current a)) m (mode (W.Y (B.current b)) n y) -
        mode (W.Y (B.current b)) n (mode (W.Y (B.current a)) m y)) := by
    simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  rw [heq, hM, hG]
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_add, Finset.sum_add_distrib]
  by_cases hmn : m + n = 0
  · simp only [if_pos hmn, LinearMap.smul_apply, LinearMap.id_apply,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    have hscalar : ((m : ℂ) * k * kappa a b) + ((m : ℂ) * l * kappa a b) =
        (m : ℂ) * (k + l) * kappa a b := by ring
    rw [← hscalar, add_smul, TensorProduct.add_tmul]
    abel
  · simp only [if_neg hmn, LinearMap.zero_apply, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, add_zero]

/-- The diagonal currents define an affine action at the sum of the levels. -/
noncomputable def tensorAffineAction (A : AffineSl2Action V k)
    (B : AffineSl2Action W l)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    AffineSl2Action (TensorVA.tensorSVA V W hV hW hg) (k + l) where
  current := tensorCurrentState A B
  current_weight a := by
    apply Submodule.add_mem
    · simpa only [add_zero] using tmul_mem_tenGrading_add V W
        (A.current_weight a) W.vacuum_mem
    · simpa only [zero_add] using tmul_mem_tenGrading_add V W
        V.vacuum_mem (B.current_weight a)
  current_even a := by
    apply Submodule.add_mem
    · exact TensorVA.tmul_mem_tenParity V W (A.current_even a) W.vacuum_parity
    · exact TensorVA.tmul_mem_tenParity V W V.vacuum_parity (B.current_even a)
  current_comm := tensorCurrentMode_commutator A B

/-- Diagonal affine actions carry the sum of the factor translations. -/
noncomputable def tensorTranslatedAffineAction (A : TranslatedAffineSl2Action V k)
    (B : TranslatedAffineSl2Action W l)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    TranslatedAffineSl2Action (TensorVA.tensorSVA V W hV hW hg) (k + l) where
  toAffineSl2Action := tensorAffineAction A.toAffineSl2Action B.toAffineSl2Action hV hW hg
  translation := translationCovariant_tensorSVA A.translation B.translation hV hW hg

/-- The same diagonal action at a prescribed equal level. The current states
are definitionally unchanged; no transport of the structure is used. -/
noncomputable def tensorTranslatedAffineActionAt (A : TranslatedAffineSl2Action V k)
    (B : TranslatedAffineSl2Action W l)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) (r : ℂ) (hlevel : k + l = r) :
    TranslatedAffineSl2Action (TensorVA.tensorSVA V W hV hW hg) r where
  current := tensorCurrentState A.toAffineSl2Action B.toAffineSl2Action
  current_weight := (tensorAffineAction A.toAffineSl2Action B.toAffineSl2Action
    hV hW hg).current_weight
  current_even := (tensorAffineAction A.toAffineSl2Action B.toAffineSl2Action
    hV hW hg).current_even
  current_comm a b m n := by
    simpa only [hlevel] using
      tensorCurrentMode_commutator A.toAffineSl2Action B.toAffineSl2Action a b m n
  translation := translationCovariant_tensorSVA A.translation B.translation hV hW hg

@[simp] theorem tensorTranslatedAffineActionAt_current
    (A : TranslatedAffineSl2Action V k) (B : TranslatedAffineSl2Action W l)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) (r : ℂ) (hlevel : k + l = r) (a : Fin 3) :
    (tensorTranslatedAffineActionAt A B hV hW hg r hlevel).current a =
      tensorCurrentState A.toAffineSl2Action B.toAffineSl2Action a := rfl

@[simp] theorem tensorTranslatedAffineAction_translation
    (A : TranslatedAffineSl2Action V k) (B : TranslatedAffineSl2Action W l)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    (tensorTranslatedAffineAction A B hV hW hg).translation.T =
      TensorFieldLift.tensorTranslation A.translation.T B.translation.T := rfl

/-- On pure tensors the translation datum is the sum of the factor translations. -/
theorem tensorTranslatedAffineAction_translation_tmul
    (A : TranslatedAffineSl2Action V k) (B : TranslatedAffineSl2Action W l)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) (x : M) (y : N) :
    (tensorTranslatedAffineAction A B hV hW hg).translation.T (x ⊗ₜ[ℂ] y) =
      A.translation.T x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] B.translation.T y := rfl

section ThreeFactors
variable {P : Type w} [AddCommGroup P] [Module ℂ P]
variable {U : SuperVertexAlgebra P} {r : ℂ}

/-- The left-associated three-factor tensor SVA used for the matter algebra. -/
noncomputable def tensorThreeSVA (V : SuperVertexAlgebra M) (W : SuperVertexAlgebra N)
    (U : SuperVertexAlgebra P)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hU : TensorVA.ParityCompatible U) (hVW : TensorVA.TensorGradingHyp V W)
    (hVWU : TensorVA.TensorGradingHyp (TensorVA.tensorSVA V W hV hW hVW) U) :
    SuperVertexAlgebra ((M ⊗[ℂ] N) ⊗[ℂ] P) :=
  TensorVA.tensorSVA (TensorVA.tensorSVA V W hV hW hVW) U
    (parityCompatible_tensorSVA V W hV hW hVW) hU hVWU

/-- Three factor actions give the actual diagonal action with summed translation. -/
noncomputable def tensorThreeTranslatedAffineAction
    (A : TranslatedAffineSl2Action V k) (B : TranslatedAffineSl2Action W l)
    (C : TranslatedAffineSl2Action U r)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hU : TensorVA.ParityCompatible U) (hVW : TensorVA.TensorGradingHyp V W)
    (hVWU : TensorVA.TensorGradingHyp (TensorVA.tensorSVA V W hV hW hVW) U) :
    TranslatedAffineSl2Action (tensorThreeSVA V W U hV hW hU hVW hVWU) (k + l + r) :=
  tensorTranslatedAffineAction (tensorTranslatedAffineAction A B hV hW hVW) C
    (parityCompatible_tensorSVA V W hV hW hVW) hU hVWU

/-- The three-factor action has the expected explicit current states. -/
theorem tensorThreeTranslatedAffineAction_current
    (A : TranslatedAffineSl2Action V k) (B : TranslatedAffineSl2Action W l)
    (C : TranslatedAffineSl2Action U r)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hU : TensorVA.ParityCompatible U) (hVW : TensorVA.TensorGradingHyp V W)
    (hVWU : TensorVA.TensorGradingHyp (TensorVA.tensorSVA V W hV hW hVW) U)
    (a : Fin 3) :
    (tensorThreeTranslatedAffineAction A B C hV hW hU hVW hVWU).current a =
      (A.current a ⊗ₜ[ℂ] W.vacuum) ⊗ₜ[ℂ] U.vacuum +
      (V.vacuum ⊗ₜ[ℂ] B.current a) ⊗ₜ[ℂ] U.vacuum +
      (V.vacuum ⊗ₜ[ℂ] W.vacuum) ⊗ₜ[ℂ] C.current a := by
  change (A.current a ⊗ₜ[ℂ] W.vacuum + V.vacuum ⊗ₜ[ℂ] B.current a) ⊗ₜ[ℂ] U.vacuum +
    (V.vacuum ⊗ₜ[ℂ] W.vacuum) ⊗ₜ[ℂ] C.current a = _
  rw [TensorProduct.add_tmul]

/-- Translation on three matter factors acts in each factor separately. -/
theorem tensorThreeTranslatedAffineAction_translation_tmul
    (A : TranslatedAffineSl2Action V k) (B : TranslatedAffineSl2Action W l)
    (C : TranslatedAffineSl2Action U r)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hU : TensorVA.ParityCompatible U) (hVW : TensorVA.TensorGradingHyp V W)
    (hVWU : TensorVA.TensorGradingHyp (TensorVA.tensorSVA V W hV hW hVW) U)
    (x : M) (y : N) (z : P) :
    (tensorThreeTranslatedAffineAction A B C hV hW hU hVW hVWU).translation.T
        ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) =
      (A.translation.T x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z +
      (x ⊗ₜ[ℂ] B.translation.T y) ⊗ₜ[ℂ] z +
      (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] C.translation.T z := by
  change (A.translation.T x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] B.translation.T y) ⊗ₜ[ℂ] z +
    (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] C.translation.T z = _
  rw [TensorProduct.add_tmul]

/-- The matter levels in the Lee–Yang coset construction cancel the ghost level. -/
theorem leeYangMatter_level : (-4 / 3 : ℂ) + 1 + (-11 / 3) = -4 := by norm_num

/-- The abstract factors at levels `-4/3`, `1`, and `-11/3` supply the level `-4`
translated matter action required by `semiInfiniteBRSTComplex`. -/
noncomputable def leeYangMatterAction
    (A : TranslatedAffineSl2Action V (-4 / 3)) (B : TranslatedAffineSl2Action W 1)
    (C : TranslatedAffineSl2Action U (-11 / 3))
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hU : TensorVA.ParityCompatible U) (hVW : TensorVA.TensorGradingHyp V W)
    (hVWU : TensorVA.TensorGradingHyp (TensorVA.tensorSVA V W hV hW hVW) U) :
    TranslatedAffineSl2Action (tensorThreeSVA V W U hV hW hU hVW hVWU) (-4) where
  current := (tensorThreeTranslatedAffineAction A B C hV hW hU hVW hVWU).current
  current_weight :=
    (tensorThreeTranslatedAffineAction A B C hV hW hU hVW hVWU).current_weight
  current_even := (tensorThreeTranslatedAffineAction A B C hV hW hU hVW hVWU).current_even
  current_comm a b m n := by
    simpa only [leeYangMatter_level] using
      (tensorThreeTranslatedAffineAction A B C hV hW hU hVW hVWU).current_comm a b m n
  translation := (tensorThreeTranslatedAffineAction A B C hV hW hU hVW hVWU).translation

@[simp] theorem leeYangMatterAction_current
    (A : TranslatedAffineSl2Action V (-4 / 3)) (B : TranslatedAffineSl2Action W 1)
    (C : TranslatedAffineSl2Action U (-11 / 3))
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hU : TensorVA.ParityCompatible U) (hVW : TensorVA.TensorGradingHyp V W)
    (hVWU : TensorVA.TensorGradingHyp (TensorVA.tensorSVA V W hV hW hVW) U)
    (a : Fin 3) :
    (leeYangMatterAction A B C hV hW hU hVW hVWU).current a =
      tensorCurrentState
        (tensorAffineAction A.toAffineSl2Action B.toAffineSl2Action hV hW hVW)
        C.toAffineSl2Action a := rfl

end ThreeFactors
end VOA.Sl2SemiInfinite
