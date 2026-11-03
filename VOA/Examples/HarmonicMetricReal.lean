/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.HarmonicMetricBridge
import VOA.Examples.DSReductionSl2

/-!
# The product conjugation fixes the explicit word representatives

* `rawCoeff_map`, `tenY_map_toSuper` — a tensor product of two mode-compatible antilinear maps is
  compatible with the modes of the tensor product of two (even) vertex algebras;
* `rhoAB_mode` — for `ρ_A ⊗ ρ_B` on `A ⊗ B`;
* `rhoAB_cosetOmega` — `ρ_A ⊗ ρ_B` fixes the coset conformal vector `ω_C`
  (the ambient conformal vectors are fixed, and the diagonal Sugawara vector is fixed because
  compact conjugation sends `J^a ↦ -J^{a*}` and the inverse Killing form is real and
  `*`-invariant);
* `repWordsReal_proved : RepWordsReal`.

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical Sl2Coset
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### Mode compatibility on a tensor product -/

section TensorReal

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

theorem rawCoeff_map (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (σ : A →ₗ⋆[ℂ] A) (τ : B →ₗ⋆[ℂ] B)
    (hσ : ∀ a m x, σ (V.Y a m x) = V.Y (σ a) m (σ x))
    (hτ : ∀ b m y, τ (W.Y b m y) = W.Y (τ b) m (τ y)) (a : A) (b : B) (s : ℤ)
    (z : A ⊗[ℂ] B) :
    TensorProduct.map σ τ (TensorVA.rawCoeff V W a b s z) =
      TensorVA.rawCoeff V W (σ a) (τ b) s (TensorProduct.map σ τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]
  | tmul x y =>
      rw [TensorVA.rawCoeff_tmul, TensorProduct.map_tmul, TensorVA.rawCoeff_tmul]
      have h := (TensorProduct.map σ τ).toAddMonoidHom.map_finsum
        (TensorVA.raw_support V W a b s x y)
      change TensorProduct.map σ τ _ = _ at h
      rw [h]
      refine finsum_congr fun m => ?_
      change TensorProduct.map σ τ (V.Y a m x ⊗ₜ[ℂ] W.Y b (s - m) y) = _
      rw [TensorProduct.map_tmul, hσ, hτ]

theorem tenY_map_toSuper (V : PreVertexAlgebra A) (W : PreVertexAlgebra B)
    (σ : A →ₗ⋆[ℂ] A) (τ : B →ₗ⋆[ℂ] B)
    (hσ : ∀ a m x, σ (V.toSuper.Y a m x) = V.toSuper.Y (σ a) m (σ x))
    (hτ : ∀ b m y, τ (W.toSuper.Y b m y) = W.toSuper.Y (τ b) m (τ y)) (u z : A ⊗[ℂ] B)
    (s : ℤ) :
    TensorProduct.map σ τ (TensorVA.tenY V.toSuper W.toSuper u s z) =
      TensorVA.tenY V.toSuper W.toSuper (TensorProduct.map σ τ u) s (TensorProduct.map σ τ z) := by
  induction u using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero]
      rfl
  | add u u' hu hu' =>
      rw [map_add (TensorVA.tenY _ _) u u', map_add (TensorProduct.map σ τ) u u',
        map_add (TensorVA.tenY _ _)]
      change TensorProduct.map σ τ ((TensorVA.tenY V.toSuper W.toSuper u s +
          TensorVA.tenY V.toSuper W.toSuper u' s) z) =
        (TensorVA.tenY V.toSuper W.toSuper (TensorProduct.map σ τ u) s +
          TensorVA.tenY V.toSuper W.toSuper (TensorProduct.map σ τ u') s)
            (TensorProduct.map σ τ z)
      rw [LinearMap.add_apply, LinearMap.add_apply, map_add, hu, hu']
  | tmul a b =>
      rw [TensorProduct.map_tmul, DSsl2.tenY_tmul_toSuper, DSsl2.tenY_tmul_toSuper]
      exact rawCoeff_map _ _ σ τ hσ hτ a b s z

end TensorReal

/-! ### The conjugation of the two simple affine factors -/

/-- `ρ_A ⊗ ρ_B` on `A ⊗ B`. -/
abbrev rhoAB : ASpace ⊗[ℂ] BSpace →ₗ⋆[ℂ] ASpace ⊗[ℂ] BSpace :=
  TensorProduct.map (rsLin affineRealStructure) (rsLin bRealStructure)

theorem rsLin_Y {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
    (R : RealStructure W) (a : 𝒱) (m : ℤ) (x : 𝒱) :
    rsLin R (W.toPreVertexAlgebra.toSuper.Y a m x) =
      W.toPreVertexAlgebra.toSuper.Y (rsLin R a) m (rsLin R x) := by
  have h := R.map_smul a (-m - 1) x
  rw [PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def, mode_apply, mode_apply,
    show -(-m - 1) - 1 = m by ring] at h
  exact h

theorem rhoAB_mode (u z : ASpace ⊗[ℂ] BSpace) (m : ℤ) :
    rhoAB (mode (abSVA.Y u) m z) = mode (abSVA.Y (rhoAB u)) m (rhoAB z) := by
  rw [mode_apply, mode_apply]
  exact tenY_map_toSuper AVOA.toPreVertexAlgebra BVOA.toPreVertexAlgebra _ _
    (rsLin_Y affineRealStructure) (rsLin_Y bRealStructure) u z _

theorem rhoA_current (a : Fin 3) :
    rsLin affineRealStructure (aAction.current a) =
      -aAction.current (HighestModule.adjointColour a) := by
  have h1 : aAction.current a = aMode a (-1) ASVA.vacuum := (ASVA.creation _).1.symm
  have h2 : aAction.current (HighestModule.adjointColour a) =
      aMode (HighestModule.adjointColour a) (-1) ASVA.vacuum := (ASVA.creation _).1.symm
  rw [h1, h2, rsLin_apply, aMode_rho]
  congr 2
  exact affineRealStructure.map_vacuum

theorem rhoB_current (a : Fin 3) :
    rsLin bRealStructure (bAction.current a) =
      -bAction.current (HighestModule.adjointColour a) := by
  have h1 : bAction.current a = bMode a (-1) BSVA.vacuum := (BSVA.creation _).1.symm
  have h2 : bAction.current (HighestModule.adjointColour a) =
      bMode (HighestModule.adjointColour a) (-1) BSVA.vacuum := (BSVA.creation _).1.symm
  rw [h1, h2, rsLin_apply, bCompactUnitary.rho_mode]
  congr 2
  exact bRealStructure.map_vacuum

theorem rhoAB_diagCurrent (a : Fin 3) :
    rhoAB (diagonalAction.current a) = -diagonalAction.current (HighestModule.adjointColour a) := by
  change rhoAB (aAction.current a ⊗ₜ[ℂ] BSVA.vacuum + ASVA.vacuum ⊗ₜ[ℂ] bAction.current a) =
    -(aAction.current _ ⊗ₜ[ℂ] BSVA.vacuum + ASVA.vacuum ⊗ₜ[ℂ] bAction.current _)
  rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul, rhoA_current, rhoB_current]
  rw [show rsLin bRealStructure BSVA.vacuum = BSVA.vacuum from bRealStructure.map_vacuum,
    show rsLin affineRealStructure ASVA.vacuum = ASVA.vacuum from
      affineRealStructure.map_vacuum]
  rw [TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_add]

theorem rhoAB_diagQuad (b c : Fin 3) :
    rhoAB (mode (abSVA.Y (diagonalAction.current b)) (-1) (diagonalAction.current c)) =
      mode (abSVA.Y (diagonalAction.current (HighestModule.adjointColour b))) (-1)
        (diagonalAction.current (HighestModule.adjointColour c)) := by
  rw [rhoAB_mode, rhoAB_diagCurrent, rhoAB_diagCurrent, mode_apply, mode_apply, map_neg, map_neg]
  set X := abSVA.Y (diagonalAction.current (HighestModule.adjointColour b))
  have e : (-X) (-(-1 : ℤ) - 1) = -(X (-(-1 : ℤ) - 1)) := rfl
  rw [e, LinearMap.neg_apply, neg_neg]

theorem rhoAB_diagonalSugawara : rhoAB diagonalSugawara = diagonalSugawara := by
  have hs : (starRingEnd ℂ) ((2 * ((-4 / 3 : ℂ) + 1 + 2))⁻¹) = (2 * ((-4 / 3 : ℂ) + 1 + 2))⁻¹ := by
    rw [show (2 * ((-4 / 3 : ℂ) + 1 + 2))⁻¹ = ((3 / 10 : ℝ) : ℂ) by push_cast; norm_num,
      Complex.conj_ofReal]
  change rhoAB ((2 * ((-4 / 3 : ℂ) + 1 + 2))⁻¹ • ∑ b : Fin 3, ∑ c : Fin 3,
      kappaInv b c • mode (abSVA.Y (diagonalAction.current b)) (-1)
        (diagonalAction.current c)) = (2 * ((-4 / 3 : ℂ) + 1 + 2))⁻¹ • ∑ b : Fin 3, ∑ c : Fin 3,
      kappaInv b c • mode (abSVA.Y (diagonalAction.current b)) (-1) (diagonalAction.current c)
  rw [LinearMap.map_smulₛₗ, hs]
  congr 1
  have a0 : HighestModule.adjointColour 0 = 1 := rfl
  have a1 : HighestModule.adjointColour 1 = 0 := rfl
  have a2 : HighestModule.adjointColour 2 = 2 := rfl
  have k01 : kappaInv 0 1 = 1 := rfl
  have k10 : kappaInv 1 0 = 1 := rfl
  have k22 : kappaInv 2 2 = 1 / 2 := rfl
  have k00 : kappaInv 0 0 = 0 := rfl
  have k02 : kappaInv 0 2 = 0 := rfl
  have k11 : kappaInv 1 1 = 0 := rfl
  have k12 : kappaInv 1 2 = 0 := rfl
  have k20 : kappaInv 2 0 = 0 := rfl
  have k21 : kappaInv 2 1 = 0 := rfl
  simp only [Fin.sum_univ_three, k00, k01, k02, k10, k11, k12, k20, k21, k22, zero_smul,
    one_smul, add_zero, zero_add, map_add, LinearMap.map_smulₛₗ, rhoAB_diagQuad, a0, a1, a2]
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]]
  abel

theorem rhoAB_ambient : rhoAB ambientConformal = ambientConformal := by
  change rhoAB (AVOA.conformalVector ⊗ₜ[ℂ] BSVA.vacuum + ASVA.vacuum ⊗ₜ[ℂ]
      BVOA.conformalVector) = _
  rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul]
  rw [show rsLin bRealStructure BSVA.vacuum = BSVA.vacuum from bRealStructure.map_vacuum,
    show rsLin affineRealStructure ASVA.vacuum = ASVA.vacuum from
      affineRealStructure.map_vacuum,
    show rsLin affineRealStructure AVOA.conformalVector = AVOA.conformalVector from
      affineRealStructure.map_omega,
    show rsLin bRealStructure BVOA.conformalVector = BVOA.conformalVector from
      bRealStructure.map_omega]
  rfl

/-- **`ρ_A ⊗ ρ_B` fixes the coset conformal vector.** -/
theorem rhoAB_cosetOmega : rhoAB cosetOmega = cosetOmega := by
  rw [cosetOmega, map_sub, rhoAB_ambient, rhoAB_diagonalSugawara]

/-- `ρ_A ⊗ ρ_B` fixes the coset image of every creation word. -/
theorem rhoAB_word (w : List ℕ) :
    rhoAB ((virasoroToCoset (negWordVir leeYangC w) : CosetSpace) : ASpace ⊗[ℂ] BSpace) =
      ((virasoroToCoset (negWordVir leeYangC w) : CosetSpace) : ASpace ⊗[ℂ] BSpace) := by
  induction w with
  | nil =>
      rw [negWordVir_nil, virasoroToCoset_vacuum]
      change rhoAB (ASVA.vacuum ⊗ₜ[ℂ] BSVA.vacuum) = ASVA.vacuum ⊗ₜ[ℂ] BSVA.vacuum
      rw [TensorProduct.map_tmul]
      rw [show rsLin bRealStructure BSVA.vacuum = BSVA.vacuum from bRealStructure.map_vacuum,
        show rsLin affineRealStructure ASVA.vacuum = ASVA.vacuum from
          affineRealStructure.map_vacuum]
  | cons i w ih =>
      rw [negWordVir_cons]
      rw [show virasoroToCoset (Lop leeYangC (-(i : ℤ) - 2) (negWordVir leeYangC w)) =
        cosetVOA.L (-(i : ℤ) - 2) (virasoroToCoset (negWordVir leeYangC w)) from
          conformalEval_L cosetVOA rfl _ _]
      rw [VertexOperatorAlgebra.L_def, ← PreVertexAlgebra.smul_def, cosetVOA_mode, cosetMode_coe]
      change rhoAB (mode (abSVA.Y cosetOmega) _ _) = mode (abSVA.Y cosetOmega) _ _
      rw [rhoAB_mode, rhoAB_cosetOmega, ih]

/-- **`ρ_M ⊗ ρ_G` fixes the explicit representative of every creation word.** -/
theorem repWordsReal_proved : RepWordsReal := by
  intro w
  rw [repVec, cosetToComplex_apply]
  change TensorProduct.map (matterRho bRealStructure) ghostConj _ = _
  rw [TensorProduct.map_tmul, ← gvac_eq, ghostConj_gvac]
  congr 1
  change TensorProduct.map rhoAB (rsLin auxiliaryRealStructure) _ = _
  rw [TensorProduct.map_tmul, rhoAB_word,
    show rsLin auxiliaryRealStructure USVA.vacuum = USVA.vacuum from
      auxiliaryRealStructure.map_vacuum]

end

end VOA.ConcreteHodge
