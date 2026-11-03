/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteNilpotency
import VOA.Examples.Sl2SemiInfiniteRelativeCharge
import VOA.Examples.Sl2SemiInfiniteRelativeGrading

/-!
# The semi-infinite BRST complex and its relative differential

At matter level `-4`, translated affine matter supplies an actual `BRSTComplex`
on its tensor super vertex algebra with the three ghost pairs. The square-zero
and derivation obligations are proved from the actual charge. Translation,
parity compatibility and finite tensor weight spaces remain visible matter
hypotheses.

The relative carrier is the intersection of total-current and antighost
zero-mode kernels. The actual Cartan identity and nilpotency prove its stability;
the charge restricts to a square-zero endomorphism of ghost degree one.
-/

namespace VOA.Sl2SemiInfinite

open Module (End)
open scoped TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M}

/-- The diagonal semi-infinite BRST complex. The only extra matter data are
ordinary translation and the hypotheses for the tensor SVA, never `Q² = 0`. -/
noncomputable def semiInfiniteBRSTComplex (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    BRST.BRSTComplex (matterGhostSVA V hV hg) where
  ghost := matterGhostGrading M
  ghost_isInternal := matterGhostGrading_isInternal M
  Q := semiInfiniteQ A.toAffineSl2Action
  Q_wt := semiInfiniteQ_weight A.toAffineSl2Action hV
  Q_odd := semiInfiniteQ_odd A.toAffineSl2Action
  Q_ghost := semiInfiniteQ_ghost A.toAffineSl2Action
  Q_sq := semiInfiniteQ_sq A.toAffineSl2Action A.translation hV hg
  Q_deriv := semiInfiniteQ_deriv_of_translation A hV hg

/-- The complex's differential is definitionally the original BRST residue. -/
theorem semiInfiniteBRSTComplex_Q (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    (semiInfiniteBRSTComplex A hV hg).Q = semiInfiniteQ A.toAffineSl2Action := rfl

/-- Total current states are closed at level minus four, by the proved Cartan
state identity and nilpotency. -/
theorem semiInfiniteQ_totalCurrentState (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (a : Fin 3) :
    semiInfiniteQ A.toAffineSl2Action (totalCurrentState A.toAffineSl2Action a) = 0 := by
  rw [← semiInfiniteQ_tensorAntighost A.toAffineSl2Action a]
  exact (semiInfiniteBRSTComplex A hV hg).Q_apply_Q _

/-- The BRST charge preserves the six simultaneous relative kernel conditions. -/
theorem semiInfiniteQ_mem_relativeCarrier (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    {x : M ⊗[ℂ] Sl2GhostSpace} (hx : x ∈ relativeCarrier A.toAffineSl2Action) :
    semiInfiniteQ A.toAffineSl2Action x ∈ relativeCarrier A.toAffineSl2Action :=
  semiInfiniteQ_mem_relativeCarrier_of_translation A hV hg
    (semiInfiniteQ_tensorAntighost A.toAffineSl2Action)
    (semiInfiniteQ_totalCurrentState A hV hg) hx

/-- The restricted differential of the relative subcomplex. -/
noncomputable def relativeQ (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    End ℂ (relativeCarrier A.toAffineSl2Action) :=
  (semiInfiniteQ A.toAffineSl2Action).restrict
    (fun _ hx => semiInfiniteQ_mem_relativeCarrier A hV hg hx)

/-- The inclusion of relative states intertwines the two differentials. -/
theorem relativeQ_coe (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (x : relativeCarrier A.toAffineSl2Action) :
    ((relativeQ A hV hg x : relativeCarrier A.toAffineSl2Action) :
      M ⊗[ℂ] Sl2GhostSpace) = semiInfiniteQ A.toAffineSl2Action x := rfl

/-- The relative differential is square-zero. -/
theorem relativeQ_sq (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    relativeQ A hV hg * relativeQ A hV hg = 0 := by
  ext x
  exact (semiInfiniteBRSTComplex A hV hg).Q_apply_Q x

/-- The relative differential has degree one in the genuine internal ghost grading. -/
theorem relativeQ_ghost (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (g : ℤ) (x : relativeCarrier A.toAffineSl2Action)
    (hx : x ∈ relativeGhostGrading A.toAffineSl2Action g) :
    relativeQ A hV hg x ∈ relativeGhostGrading A.toAffineSl2Action (g + 1) :=
  semiInfiniteQ_ghost A.toAffineSl2Action g x hx

/-- The concrete tensor SVA for the universal affine algebra at level minus four.
All tensor grading and parity conditions are discharged by existing theorems. -/
noncomputable def universalSemiInfiniteSVA :
    SuperVertexAlgebra (AffineVOA.WakModule (-4) ⊗[ℂ] Sl2GhostSpace) :=
  matterGhostSVA (DSsl2.affSVA (-4) (by norm_num))
    (DSMor.parityCompatible_toSuper (AffineVOA.Vir.affineVA (-4) (by norm_num)))
    (DSMor.tensorGradingHyp_of_natSupported _ _
      (DSMor.natSupported_affSVA (-4) (by norm_num)) natSupported_sl2GhostSVA)

/-- A concrete inhabited BRST complex at level minus four, with every matter
translation and tensor grading obligation discharged. -/
noncomputable def universalSemiInfiniteBRSTComplex : BRST.BRSTComplex universalSemiInfiniteSVA :=
  semiInfiniteBRSTComplex (translatedAffineAction (-4) (by norm_num))
    (DSMor.parityCompatible_toSuper (AffineVOA.Vir.affineVA (-4) (by norm_num)))
    (DSMor.tensorGradingHyp_of_natSupported _ _
      (DSMor.natSupported_affSVA (-4) (by norm_num)) natSupported_sl2GhostSVA)

end VOA.Sl2SemiInfinite
