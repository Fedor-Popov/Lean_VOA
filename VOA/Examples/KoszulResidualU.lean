/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualPBW
import VOA.Examples.KoszulResidualLayers
import VOA.Examples.BRSTGoodnessMatter
import VOA.Examples.ConcreteHodgeAssembly

/-!
# `gr U ≅ ℂ[x]` on the orthogonal PBW layers of the auxiliary factor

`U = V^{-11/3}(sl₂)` carries the interpreted layer grading `uDeg` (the orthogonal layers of the
ordinary PBW flag for the Shapovalov form). This file proves that the **symbol map**

  `PhiU : U ≃ₗ[ℂ] ℂ[x_q : q ∈ LexLetter]`,   `v ↦ (degree-t part of the PBW coordinates of v)`
  on the layer `t`,

is a linear equivalence, sending the layer of `R = t` and weight `m` onto the homogeneous
polynomials of degree `t` and weight `m`, and that it intertwines

* the `R`-raising component of each creation mode `J^a_{-j-1}` with multiplication by
  `x_{(a,j)}` (`PhiU_uP_creation`);
* the `R`-preserving component of each nonnegative mode `J^c_m` with the symbol derivation
  `symDer c m` (`PhiU_uP_nonneg`), and the zero modes exactly (`PhiU_uMode_zero`).

Everything is proved outright.
-/

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete AffineSl2GeneralRigidity AffineSl2BelowCritical AffineVOA AffineVOA.Inst
open VOA.LeeYangTransferAssembly MvPolynomial

noncomputable section

/-! ### The layer grading of `U` -/

theorem uDeg_isInternal : DirectSum.IsInternal uDeg :=
  layerDeg_isInternal auxiliaryForm auxiliaryRealStructure auxiliaryFlag auxiliaryGradedUnitary
    auxiliaryGramRefl

/-- The projection onto a layer of `U`. -/
abbrev uP (i : (ℤ × ℤ) × ℂ) : USpace →ₗ[ℂ] USpace := iproj uDeg_isInternal i

theorem uDeg_le_ordinary (t : ℕ) (m : ℤ) : uDeg (layerIndex t m) ≤ ordinaryPiece (-11 / 3) t :=
  (layerDeg_le_piece auxiliaryForm auxiliaryFlag t m).trans inf_le_left

theorem uDeg_le_grading (t : ℕ) (m : ℤ) :
    uDeg (layerIndex t m) ≤ (universal (-11 / 3) uNoncritical).grading m :=
  (layerDeg_le_piece auxiliaryForm auxiliaryFlag t m).trans inf_le_right

/-- The `R`-degree of an index. -/
def tIdx (i : (ℤ × ℤ) × ℂ) : ℕ := (i.1.1 / 2).toNat

@[simp] theorem tIdx_layerIndex (t : ℕ) (m : ℤ) : tIdx (layerIndex t m) = t := by
  simp [tIdx, layerIndex]

theorem uDeg_eq_bot_of {i : (ℤ × ℤ) × ℂ} (h : ∀ t m, layerIndex t m ≠ i) : uDeg i = ⊥ :=
  layerDeg_eq_bot_of auxiliaryForm auxiliaryFlag h

/-- Lower layers have no top-degree coordinates. -/
theorem homog_eq_zero_of_lower {t : ℕ} {m : ℤ} {y : USpace}
    (hy : y ∈ ⨆ (s : ℕ) (_ : s < t), uDeg (layerIndex s m)) :
    homogeneousComponent t (pbwCoord (-11 / 3) uNoncritical y) = 0 := by
  refine Submodule.iSup_induction _
    (motive := fun y => homogeneousComponent t (pbwCoord (-11 / 3) uNoncritical y) = 0) hy ?_
    (by simp) (fun y y' h h' => by beta_reduce at h h' ⊢; rw [map_add, map_add, h, h', add_zero])
  intro s y hy
  refine Submodule.iSup_induction _
    (motive := fun y => homogeneousComponent t (pbwCoord (-11 / 3) uNoncritical y) = 0) hy ?_
    (by simp) (fun y y' h h' => by beta_reduce at h h' ⊢; rw [map_add, map_add, h, h', add_zero])
  intro hs z hz
  exact homogeneousComponent_eq_zero_of_mem _ uNoncritical hs (uDeg_le_ordinary s m hz)

theorem homog_uP_layer {t : ℕ} {m : ℤ} {w : USpace} (hw : w ∈ auxiliaryFlag.piece t m) :
    homogeneousComponent t (pbwCoord (-11 / 3) uNoncritical (uP (layerIndex t m) w)) =
      homogeneousComponent t (pbwCoord (-11 / 3) uNoncritical w) := by
  have h := sub_iproj_layer_mem auxiliaryForm auxiliaryRealStructure auxiliaryFlag
    auxiliaryGradedUnitary auxiliaryGramRefl t m hw
  have h0 := homog_eq_zero_of_lower h
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0.symm

/-! ### The symbol map -/

/-- The symbol map on each layer: the degree-`t` part of the PBW coordinates. -/
def phiU : USpace →ₗ[ℂ] MvPolynomial LexLetter ℂ :=
  DirectSum.toModule ℂ _ _ (fun i => homogeneousComponent (tIdx i) ∘ₗ
    (pbwCoord (-11 / 3) uNoncritical).toLinearMap ∘ₗ (uDeg i).subtype) ∘ₗ
    (internalEquiv uDeg_isInternal).symm.toLinearMap

theorem phiU_of_mem {i : (ℤ × ℤ) × ℂ} {x : USpace} (hx : x ∈ uDeg i) :
    phiU x = homogeneousComponent (tIdx i) (pbwCoord (-11 / 3) uNoncritical x) := by
  simp only [phiU, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [internalEquiv_symm_of_mem uDeg_isInternal hx, ← DirectSum.lof_eq_of ℂ,
    DirectSum.toModule_lof]
  rfl

/-- The inverse symbol map: `x^μ ↦` the layer component of `e_μ`. -/
def psiU : MvPolynomial LexLetter ℂ →ₗ[ℂ] USpace :=
  (basisMonomials LexLetter ℂ).constr ℂ fun mu =>
    uP (layerIndex mu.degree (enOf mu)) (currentPBWBasis (-11 / 3) uNoncritical mu)

theorem psiU_monomial (mu : CurrentIndex) :
    psiU (monomial mu 1) =
      uP (layerIndex mu.degree (enOf mu)) (currentPBWBasis (-11 / 3) uNoncritical mu) := by
  have h := (basisMonomials LexLetter ℂ).constr_basis ℂ (fun mu =>
    uP (layerIndex mu.degree (enOf mu)) (currentPBWBasis (-11 / 3) uNoncritical mu)) mu
  rw [coe_basisMonomials] at h
  exact h

theorem basis_mem_piece (mu : CurrentIndex) :
    currentPBWBasis (-11 / 3) uNoncritical mu ∈ auxiliaryFlag.piece mu.degree (enOf mu) := by
  refine ⟨?_, basis_mem_grading _ uNoncritical mu⟩
  rw [← pbwSpan_eq_ordinaryPiece _ uNoncritical]
  exact Submodule.subset_span ⟨mu, by simp [pbwLength_eq_degree], rfl⟩

theorem phiU_psiU_monomial (mu : CurrentIndex) : phiU (psiU (monomial mu 1)) = monomial mu 1 := by
  rw [psiU_monomial, phiU_of_mem (iproj_mem _ _ _), tIdx_layerIndex,
    homog_uP_layer (basis_mem_piece mu), pbwCoord_basis,
    homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl), if_pos rfl]

/-- On a vector of weight `m`, `psiU` of its degree-`t` coordinates is the `(t, m)`-layer
component of its degree-`t` part. -/
theorem psiU_homog {m : ℤ} (t : ℕ) {y : USpace}
    (hy : y ∈ (universal (-11 / 3) uNoncritical).grading m) :
    psiU (homogeneousComponent t (pbwCoord (-11 / 3) uNoncritical y)) =
      uP (layerIndex t m) (degPart (-11 / 3) uNoncritical t y) := by
  classical
  have hx' : y = ∑ mu ∈ ((currentPBWBasis (-11 / 3) uNoncritical).repr y).support,
      (currentPBWBasis (-11 / 3) uNoncritical).repr y mu •
        currentPBWBasis (-11 / 3) uNoncritical mu := by
    conv_lhs => rw [← (currentPBWBasis (-11 / 3) uNoncritical).linearCombination_repr y]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hx']
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun mu hmu => ?_
  have hmu' : (enOf mu : ℤ) = m := by
    by_contra hne
    have := coeff_eq_zero_of_mem_grading _ uNoncritical hy hne
    rw [coeff_pbwCoord] at this
    exact (Finsupp.mem_support_iff.mp hmu) this
  congr 1
  rw [pbwCoord_basis, homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl)]
  have hdp : degPart (-11 / 3) uNoncritical t (currentPBWBasis (-11 / 3) uNoncritical mu) =
      if t = mu.degree then currentPBWBasis (-11 / 3) uNoncritical mu else 0 := by
    apply (pbwCoord (-11 / 3) uNoncritical).injective
    rw [pbwCoord_degPart, pbwCoord_basis, homogeneousComponent_of_mem
      (isHomogeneous_monomial _ rfl)]
    split_ifs <;> simp [pbwCoord_basis]
  rw [hdp]
  split_ifs with ht
  · rw [psiU_monomial, ← ht, hmu']
  · rw [map_zero, map_zero]

theorem psiU_phiU_of_mem {i : (ℤ × ℤ) × ℂ} {x : USpace} (hx : x ∈ uDeg i) :
    psiU (phiU x) = x := by
  by_cases hi : ∃ t m, layerIndex t m = i
  · obtain ⟨t, m, rfl⟩ := hi
    have hxm := uDeg_le_grading t m hx
    rw [phiU_of_mem hx, tIdx_layerIndex, psiU_homog t hxm]
    have hxo := uDeg_le_ordinary t m hx
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [degPart_of_mem_zero _ uNoncritical hxo, iproj_of_mem_same _ hx]
    · have hlow : x - degPart (-11 / 3) uNoncritical t x ∈ auxiliaryFlag.piece (t - 1) m :=
        ⟨sub_degPart_mem _ uNoncritical hxo,
          Submodule.sub_mem _ hxm (degPart_mem_grading _ uNoncritical t hxm)⟩
      have h0 : uP (layerIndex t m) (x - degPart (-11 / 3) uNoncritical t x) = 0 := by
        refine iproj_eq_zero_of_mem_iSup uDeg_isInternal
          (fun i => ∃ s ≤ t - 1, layerIndex s m = i) ?_ ?_
        · have h := piece_le_iSup_layerDeg auxiliaryForm auxiliaryRealStructure auxiliaryFlag
            auxiliaryGradedUnitary auxiliaryGramRefl (t - 1) m hlow
          have hle : (⨆ (s : ℕ) (_ : s ≤ t - 1), uDeg (layerIndex s m)) ≤
              ⨆ (i : (ℤ × ℤ) × ℂ) (_ : ∃ s ≤ t - 1, layerIndex s m = i), uDeg i :=
            iSup_le fun s => iSup_le fun hs =>
              le_iSup_of_le (layerIndex s m) (le_iSup_of_le ⟨s, hs, rfl⟩ le_rfl)
          exact hle h
        · rintro ⟨s, hs, he⟩
          have := (layerIndex_injective he).1
          omega
      rw [map_sub, iproj_of_mem_same _ hx, sub_eq_zero] at h0
      exact h0.symm
  · push Not at hi
    rw [uDeg_eq_bot_of hi, Submodule.mem_bot] at hx
    rw [hx, map_zero, map_zero]

/-- **The symbol map `U ≃ ℂ[x]`.** -/
def PhiU : USpace ≃ₗ[ℂ] MvPolynomial LexLetter ℂ :=
  LinearEquiv.ofLinear phiU psiU
    ((basisMonomials LexLetter ℂ).ext fun mu => by
      rw [coe_basisMonomials, LinearMap.comp_apply, phiU_psiU_monomial, LinearMap.id_apply])
    (linearMap_ext_internal uDeg_isInternal fun i x hx => by
      rw [LinearMap.comp_apply, psiU_phiU_of_mem hx, LinearMap.id_apply])

theorem PhiU_apply (x : USpace) : PhiU x = phiU x := rfl

theorem PhiU_of_mem {t : ℕ} {m : ℤ} {x : USpace} (hx : x ∈ uDeg (layerIndex t m)) :
    PhiU x = homogeneousComponent t (pbwCoord (-11 / 3) uNoncritical x) := by
  rw [PhiU_apply, phiU_of_mem hx, tIdx_layerIndex]

theorem PhiU_symm_monomial (mu : CurrentIndex) :
    PhiU.symm (monomial mu 1) =
      uP (layerIndex mu.degree (enOf mu)) (currentPBWBasis (-11 / 3) uNoncritical mu) :=
  psiU_monomial mu

theorem PhiU_symm_monomial_mem (mu : CurrentIndex) (a : ℂ) :
    PhiU.symm (monomial mu a) ∈ uDeg (layerIndex mu.degree (enOf mu)) := by
  rw [show monomial mu a = a • monomial mu 1 by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, PhiU_symm_monomial]
  exact Submodule.smul_mem _ _ (iproj_mem _ _ _)

/-! ### The intertwining properties -/

theorem eN_creation (j : ℕ) : eN (-(j : ℤ) - 1) = 1 := by
  simp [eN]; omega

/-- **The `R`-raising component of a creation mode is multiplication by its variable.** -/
theorem PhiU_uP_creation (q : LexLetter) {t : ℕ} {m : ℤ} {x : USpace}
    (hx : x ∈ uDeg (layerIndex t m)) :
    PhiU (uP (layerIndex (t + 1) (m + letterWt q))
        (uMode (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) x)) = X q * PhiU x := by
  have hw : uMode (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) x ∈
      auxiliaryFlag.piece (t + 1) (m + letterWt q) := by
    have h := uMode_flag (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) t m x
      ((layerDeg_le_piece auxiliaryForm auxiliaryFlag t m) hx)
    rw [eN_creation] at h
    convert h using 2
    push_cast; ring
  rw [PhiU_of_mem (iproj_mem _ _ _), homog_uP_layer hw, uMode_apply,
    homogeneousComponent_J _ uNoncritical q (uDeg_le_ordinary t m hx), PhiU_of_mem hx]

/-- **The `R`-preserving component of a nonnegative mode is the symbol derivation.** -/
theorem PhiU_uP_nonneg (c : Fin 3) (m0 : ℕ) {t : ℕ} {m : ℤ} {x : USpace}
    (hx : x ∈ uDeg (layerIndex t m)) :
    PhiU (uP (layerIndex t (m - m0)) (uMode c m0 x)) = symDer c m0 (PhiU x) := by
  have hw : uMode c m0 x ∈ auxiliaryFlag.piece t (m - m0) := by
    have h := uMode_flag c (m0 : ℤ) t m x ((layerDeg_le_piece auxiliaryForm auxiliaryFlag t m) hx)
    rwa [show eN (m0 : ℤ) = 0 by simp [eN], add_zero] at h
  rw [PhiU_of_mem (iproj_mem _ _ _), homog_uP_layer hw, uMode_apply,
    homogeneousComponent_J_nonneg _ uNoncritical c m0 (uDeg_le_ordinary t m hx), PhiU_of_mem hx]

/-- **The zero modes act on symbols by the adjoint derivation.** -/
theorem PhiU_uMode_zero (c : Fin 3) (x : USpace) : PhiU (uMode c 0 x) = symDer c 0 (PhiU x) := by
  have hpres : ∀ i, ∀ y ∈ uDeg i, uMode c 0 y ∈ uDeg i := fun i y hy =>
    uZeroModesPreserveLayers c i y hy
  have key : (PhiU.toLinearMap ∘ₗ uMode c 0) =
      (symDer c 0).toLinearMap ∘ₗ PhiU.toLinearMap := by
    apply linearMap_ext_internal uDeg_isInternal
    intro i y hy
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    by_cases hi : ∃ t m, layerIndex t m = i
    · obtain ⟨t, m, rfl⟩ := hi
      have h := PhiU_uP_nonneg c 0 hy
      rw [Nat.cast_zero, sub_zero, iproj_of_mem_same _ (hpres _ y hy)] at h
      exact h
    · push Not at hi
      rw [uDeg_eq_bot_of hi, Submodule.mem_bot] at hy
      rw [hy, map_zero, map_zero, map_zero]
  exact LinearMap.congr_fun key x

end

end VOA.KoszulResidual
