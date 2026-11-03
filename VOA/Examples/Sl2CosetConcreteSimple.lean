/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConcreteSupport
import VOA.Examples.Sl2SemiInfiniteDifferential

/-!
# Affine currents on the actual simple quotients

The maximal-ideal quotient carries the images of the universal current states.
Its vertex operators satisfy the full affine commutator, by the quotient
projection, and its translation is the actual conformal mode `L (-1)`.
-/

namespace VOA.Sl2CosetConcrete

open Sl2SemiInfinite AffineVOA
open Module (End)

universe u

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The conformal translation of an ordinary VOA, regarded as an even SVA. -/
noncomputable def voaTranslation (W : VertexOperatorAlgebra M) :
    TranslationCovariant W.toPreVertexAlgebra.toSuper where
  T := W.L (-1)
  vacuum_zero := W.L_neg_one_vacuum
  covariant u s := by
    simpa only [LieRing.of_associative_ring_bracket] using W.L_comm_Ycoeff u s

/-- Affine current actions descend through the actual maximal-ideal projection. -/
noncomputable def maxQuotientAffineAction (W : VertexOperatorAlgebra M) {k : ℂ}
    (A : AffineSl2Action W.toPreVertexAlgebra.toSuper k) :
    AffineSl2Action (QuotVOA.maxQuotientVOA W).toPreVertexAlgebra.toSuper k where
  current a := (QuotVOA.maxGradedIdeal W).mkQ (A.current a)
  current_weight a := by
    have h := A.current_weight a
    change A.current a ∈ W.toPreVertexAlgebra.gradingC 1 at h
    rw [← show ((1 : ℤ) : ℂ) = 1 by norm_num,
      W.toPreVertexAlgebra.gradingC_intCast] at h
    change _ ∈ (QuotVOA.maxQuotientVOA W).toPreVertexAlgebra.gradingC 1
    rw [← show ((1 : ℤ) : ℂ) = 1 by norm_num,
      (QuotVOA.maxQuotientVOA W).toPreVertexAlgebra.gradingC_intCast]
    exact Submodule.mem_map_of_mem h
  current_even a := DSMor.mem_parity_zero_toSuper _ _
  current_comm a b m n := by
    let q := (QuotVOA.maxGradedIdeal W).mkQ
    have descend (x y : M) (r : ℤ) :
        mode ((QuotVOA.maxQuotientVOA W).Y (q x)) r (q y) =
          q (mode (W.Y x) r y) :=
      SimpleQuot.maxQuotientVOA_mkQ_smul W x r y
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := (QuotVOA.maxGradedIdeal W).mkQ_surjective z
    change (mode ((QuotVOA.maxQuotientVOA W).Y (q (A.current a))) m *
        mode ((QuotVOA.maxQuotientVOA W).Y (q (A.current b))) n -
        mode ((QuotVOA.maxQuotientVOA W).Y (q (A.current b))) n *
        mode ((QuotVOA.maxQuotientVOA W).Y (q (A.current a))) m) (q v) =
      ((∑ c, fabc a b c •
          mode ((QuotVOA.maxQuotientVOA W).Y (q (A.current c))) (m + n)) +
        if m + n = 0 then ((m : ℂ) * k * kappa a b) • LinearMap.id else 0 :
          End ℂ (M ⧸ QuotVOA.maxGradedIdeal W)) (q v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, descend]
    have hc0 : mode (W.Y (A.current a)) m * mode (W.Y (A.current b)) n -
        mode (W.Y (A.current b)) n * mode (W.Y (A.current a)) m =
      (∑ c, fabc a b c • mode (W.Y (A.current c)) (m + n)) +
        if m + n = 0 then ((m : ℂ) * k * kappa a b) • LinearMap.id else 0 :=
      A.current_comm a b m n
    have hc := congrArg (fun f : End ℂ M => q (f v)) hc0
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, map_sub, map_add, map_sum, map_smul] at hc
    rw [hc]
    congr 1
    split_ifs <;> simp

/-- The universal affine currents with their actual conformal translation. -/
noncomputable def universalAction (k : ℂ) (hk : k + 2 ≠ 0) :
    TranslatedAffineSl2Action (universalSVA k hk) k where
  toAffineSl2Action := affineAction k hk
  translation := voaTranslation (AffineSl2GeneralRigidity.universal k hk)

/-- The actual simple quotient currents and its Sugawara translation. -/
noncomputable def simpleAction (k : ℂ) (hk : k + 2 ≠ 0) :
    TranslatedAffineSl2Action (simpleSVA k hk) k where
  toAffineSl2Action := maxQuotientAffineAction
    (AffineSl2GeneralRigidity.universal k hk) (affineAction k hk)
  translation := voaTranslation (AffineSl2GeneralRigidity.simple k hk)

/-- The currents are literally the quotient images in the affine colour order. -/
@[simp] theorem simpleAction_current (k : ℂ) (hk : k + 2 ≠ 0) (a : Fin 3) :
    (simpleAction k hk).current a =
      (QuotVOA.maxGradedIdeal (AffineSl2GeneralRigidity.universal k hk)).mkQ
        (J k a (-1) (vacuumA k)) := rfl

/-- Translation is the simple quotient's actual minus-first Virasoro mode. -/
@[simp] theorem simpleAction_translation (k : ℂ) (hk : k + 2 ≠ 0) :
    (simpleAction k hk).translation.T =
      (AffineSl2GeneralRigidity.simple k hk).L (-1) := rfl

/-- Translation is the universal affine VOA's actual minus-first Virasoro mode. -/
@[simp] theorem universalAction_translation (k : ℂ) (hk : k + 2 ≠ 0) :
    (universalAction k hk).translation.T =
      (AffineSl2GeneralRigidity.universal k hk).L (-1) := rfl

end VOA.Sl2CosetConcrete
