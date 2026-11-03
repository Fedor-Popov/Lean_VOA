/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulResidualU
import VOA.Examples.TwoSeriesKoszulEndpoint

/-!
# Level-generic port of `KoszulResidualU`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulResidual VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval
open VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra Sl2CosetConcrete AffineSl2GeneralRigidity
open AffineSl2BelowCritical AffineVOA AffineVOA.Inst VOA.LeeYangTransferAssembly MvPolynomial
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `KoszulResidualU` -/


/-! ### The layer grading of `U` -/

theorem uDeg_isInternal : DirectSum.IsInternal (uDeg L) :=
  layerDeg_isInternal (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L) (auxiliaryGradedUnitary L)
    (auxiliaryGramRefl L)

/-- The projection onto a layer of `U`. -/
abbrev uP (i : (ℤ × ℤ) × ℂ) : (USpace L) →ₗ[ℂ] (USpace L) := iproj (uDeg_isInternal L) i

theorem uDeg_le_ordinary (t : ℕ) (m : ℤ) : (uDeg L) (layerIndex t m) ≤ ordinaryPiece L.kU t :=
  (layerDeg_le_piece (auxiliaryForm L) (auxiliaryFlag L) t m).trans inf_le_left

theorem uDeg_le_grading (t : ℕ) (m : ℤ) :
    (uDeg L) (layerIndex t m) ≤ (universal L.kU L.uNoncritical).grading m :=
  (layerDeg_le_piece (auxiliaryForm L) (auxiliaryFlag L) t m).trans inf_le_right

theorem uDeg_eq_bot_of {i : (ℤ × ℤ) × ℂ} (h : ∀ t m, layerIndex t m ≠ i) : (uDeg L) i = ⊥ :=
  layerDeg_eq_bot_of (auxiliaryForm L) (auxiliaryFlag L) h

/-- Lower layers have no top-degree coordinates. -/
theorem homog_eq_zero_of_lower {t : ℕ} {m : ℤ} {y : (USpace L)}
    (hy : y ∈ ⨆ (s : ℕ) (_ : s < t), (uDeg L) (layerIndex s m)) :
    homogeneousComponent t (pbwCoord L.kU L.uNoncritical y) = 0 := by
  refine Submodule.iSup_induction _
    (motive := fun y => homogeneousComponent t (pbwCoord L.kU L.uNoncritical y) = 0) hy ?_
    (by simp) (fun y y' h h' => by beta_reduce at h h' ⊢; rw [map_add, map_add, h, h', add_zero])
  intro s y hy
  refine Submodule.iSup_induction _
    (motive := fun y => homogeneousComponent t (pbwCoord L.kU L.uNoncritical y) = 0) hy ?_
    (by simp) (fun y y' h h' => by beta_reduce at h h' ⊢; rw [map_add, map_add, h, h', add_zero])
  intro hs z hz
  exact homogeneousComponent_eq_zero_of_mem _ L.uNoncritical hs ((uDeg_le_ordinary L) s m hz)

theorem homog_uP_layer {t : ℕ} {m : ℤ} {w : (USpace L)} (hw : w ∈ (auxiliaryFlag L).piece t m) :
    homogeneousComponent t (pbwCoord L.kU L.uNoncritical ((uP L) (layerIndex t m) w)) =
      homogeneousComponent t (pbwCoord L.kU L.uNoncritical w) := by
  have h := sub_iproj_layer_mem (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L)
    (auxiliaryGradedUnitary L) (auxiliaryGramRefl L) t m hw
  have h0 := (homog_eq_zero_of_lower L) h
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0.symm

/-! ### The symbol map -/

/-- The symbol map on each layer: the degree-`t` part of the PBW coordinates. -/
def phiU : (USpace L) →ₗ[ℂ] MvPolynomial LexLetter ℂ :=
  DirectSum.toModule ℂ _ _ (fun i => homogeneousComponent (tIdx i) ∘ₗ
    (pbwCoord L.kU L.uNoncritical).toLinearMap ∘ₗ ((uDeg L) i).subtype) ∘ₗ
    (internalEquiv (uDeg_isInternal L)).symm.toLinearMap

theorem phiU_of_mem {i : (ℤ × ℤ) × ℂ} {x : (USpace L)} (hx : x ∈ (uDeg L) i) :
    (phiU L) x = homogeneousComponent (tIdx i) (pbwCoord L.kU L.uNoncritical x) := by
  simp only [phiU, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [internalEquiv_symm_of_mem (uDeg_isInternal L) hx, ← DirectSum.lof_eq_of ℂ,
    DirectSum.toModule_lof]
  rfl

/-- The inverse symbol map: `x^μ ↦` the layer component of `e_μ`. -/
def psiU : MvPolynomial LexLetter ℂ →ₗ[ℂ] (USpace L) :=
  (basisMonomials LexLetter ℂ).constr ℂ fun mu =>
    (uP L) (layerIndex mu.degree (enOf mu)) (currentPBWBasis L.kU L.uNoncritical mu)

theorem psiU_monomial (mu : CurrentIndex) :
    (psiU L) (monomial mu 1) =
      (uP L) (layerIndex mu.degree (enOf mu)) (currentPBWBasis L.kU L.uNoncritical mu) := by
  have h := (basisMonomials LexLetter ℂ).constr_basis ℂ (fun mu =>
    (uP L) (layerIndex mu.degree (enOf mu)) (currentPBWBasis L.kU L.uNoncritical mu)) mu
  rw [coe_basisMonomials] at h
  exact h

theorem basis_mem_piece (mu : CurrentIndex) :
    currentPBWBasis L.kU L.uNoncritical mu ∈ (auxiliaryFlag L).piece mu.degree (enOf mu) := by
  refine ⟨?_, basis_mem_grading _ L.uNoncritical mu⟩
  rw [← pbwSpan_eq_ordinaryPiece _ L.uNoncritical]
  exact Submodule.subset_span ⟨mu, by simp [pbwLength_eq_degree], rfl⟩

theorem phiU_psiU_monomial (mu : CurrentIndex) : (phiU L) ((psiU L) (monomial mu 1)) = monomial mu 1 := by
  rw [psiU_monomial, (phiU_of_mem L) (iproj_mem _ _ _), tIdx_layerIndex,
    (homog_uP_layer L) ((basis_mem_piece L) mu), pbwCoord_basis,
    homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl), if_pos rfl]

/-- On a vector of weight `m`, `(psiU L)` of its degree-`t` coordinates is the `(t, m)`-layer
component of its degree-`t` part. -/
theorem psiU_homog {m : ℤ} (t : ℕ) {y : (USpace L)}
    (hy : y ∈ (universal L.kU L.uNoncritical).grading m) :
    (psiU L) (homogeneousComponent t (pbwCoord L.kU L.uNoncritical y)) =
      (uP L) (layerIndex t m) (degPart L.kU L.uNoncritical t y) := by
  classical
  have hx' : y = ∑ mu ∈ ((currentPBWBasis L.kU L.uNoncritical).repr y).support,
      (currentPBWBasis L.kU L.uNoncritical).repr y mu •
        currentPBWBasis L.kU L.uNoncritical mu := by
    conv_lhs => rw [← (currentPBWBasis L.kU L.uNoncritical).linearCombination_repr y]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hx']
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun mu hmu => ?_
  have hmu' : (enOf mu : ℤ) = m := by
    by_contra hne
    have := coeff_eq_zero_of_mem_grading _ L.uNoncritical hy hne
    rw [coeff_pbwCoord] at this
    exact (Finsupp.mem_support_iff.mp hmu) this
  congr 1
  rw [pbwCoord_basis, homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl)]
  have hdp : degPart L.kU L.uNoncritical t (currentPBWBasis L.kU L.uNoncritical mu) =
      if t = mu.degree then currentPBWBasis L.kU L.uNoncritical mu else 0 := by
    apply (pbwCoord L.kU L.uNoncritical).injective
    rw [pbwCoord_degPart, pbwCoord_basis, homogeneousComponent_of_mem
      (isHomogeneous_monomial _ rfl)]
    split_ifs <;> simp [pbwCoord_basis]
  rw [hdp]
  split_ifs with ht
  · rw [psiU_monomial, ← ht, hmu']
  · rw [map_zero, map_zero]

theorem psiU_phiU_of_mem {i : (ℤ × ℤ) × ℂ} {x : (USpace L)} (hx : x ∈ (uDeg L) i) :
    (psiU L) ((phiU L) x) = x := by
  by_cases hi : ∃ t m, layerIndex t m = i
  · obtain ⟨t, m, rfl⟩ := hi
    have hxm := (uDeg_le_grading L) t m hx
    rw [(phiU_of_mem L) hx, tIdx_layerIndex, (psiU_homog L) t hxm]
    have hxo := (uDeg_le_ordinary L) t m hx
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [degPart_of_mem_zero _ L.uNoncritical hxo, iproj_of_mem_same _ hx]
    · have hlow : x - degPart L.kU L.uNoncritical t x ∈ (auxiliaryFlag L).piece (t - 1) m :=
        ⟨sub_degPart_mem _ L.uNoncritical hxo,
          Submodule.sub_mem _ hxm (degPart_mem_grading _ L.uNoncritical t hxm)⟩
      have h0 : (uP L) (layerIndex t m) (x - degPart L.kU L.uNoncritical t x) = 0 := by
        refine iproj_eq_zero_of_mem_iSup (uDeg_isInternal L)
          (fun i => ∃ s ≤ t - 1, layerIndex s m = i) ?_ ?_
        · have h := piece_le_iSup_layerDeg (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L)
            (auxiliaryGradedUnitary L) (auxiliaryGramRefl L) (t - 1) m hlow
          have hle : (⨆ (s : ℕ) (_ : s ≤ t - 1), (uDeg L) (layerIndex s m)) ≤
              ⨆ (i : (ℤ × ℤ) × ℂ) (_ : ∃ s ≤ t - 1, layerIndex s m = i), (uDeg L) i :=
            iSup_le fun s => iSup_le fun hs =>
              le_iSup_of_le (layerIndex s m) (le_iSup_of_le ⟨s, hs, rfl⟩ le_rfl)
          exact hle h
        · rintro ⟨s, hs, he⟩
          have := (layerIndex_injective he).1
          omega
      rw [map_sub, iproj_of_mem_same _ hx, sub_eq_zero] at h0
      exact h0.symm
  · push Not at hi
    rw [(uDeg_eq_bot_of L) hi, Submodule.mem_bot] at hx
    rw [hx, map_zero, map_zero]

/-- **The symbol map `U ≃ ℂ[x]`.** -/
def PhiU : (USpace L) ≃ₗ[ℂ] MvPolynomial LexLetter ℂ :=
  LinearEquiv.ofLinear (phiU L) (psiU L)
    ((basisMonomials LexLetter ℂ).ext fun mu => by
      rw [coe_basisMonomials, LinearMap.comp_apply, phiU_psiU_monomial, LinearMap.id_apply])
    (linearMap_ext_internal (uDeg_isInternal L) fun i x hx => by
      rw [LinearMap.comp_apply, (psiU_phiU_of_mem L) hx, LinearMap.id_apply])

theorem PhiU_apply (x : (USpace L)) : (PhiU L) x = (phiU L) x := rfl

theorem PhiU_of_mem {t : ℕ} {m : ℤ} {x : (USpace L)} (hx : x ∈ (uDeg L) (layerIndex t m)) :
    (PhiU L) x = homogeneousComponent t (pbwCoord L.kU L.uNoncritical x) := by
  rw [PhiU_apply, (phiU_of_mem L) hx, tIdx_layerIndex]

theorem PhiU_symm_monomial (mu : CurrentIndex) :
    (PhiU L).symm (monomial mu 1) =
      (uP L) (layerIndex mu.degree (enOf mu)) (currentPBWBasis L.kU L.uNoncritical mu) :=
  (psiU_monomial L) mu

theorem PhiU_symm_monomial_mem (mu : CurrentIndex) (a : ℂ) :
    (PhiU L).symm (monomial mu a) ∈ (uDeg L) (layerIndex mu.degree (enOf mu)) := by
  rw [show monomial mu a = a • monomial mu 1 by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, PhiU_symm_monomial]
  exact Submodule.smul_mem _ _ (iproj_mem _ _ _)

/-! ### The intertwining properties -/

/-- **The `R`-raising component of a creation mode is multiplication by its variable.** -/
theorem PhiU_uP_creation (q : LexLetter) {t : ℕ} {m : ℤ} {x : (USpace L)}
    (hx : x ∈ (uDeg L) (layerIndex t m)) :
    (PhiU L) ((uP L) (layerIndex (t + 1) (m + letterWt q))
        ((uMode L) (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) x)) = X q * (PhiU L) x := by
  have hw : (uMode L) (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) x ∈
      (auxiliaryFlag L).piece (t + 1) (m + letterWt q) := by
    have h := (uMode_flag L) (ofLex q).1 (-((ofLex q).2 : ℤ) - 1) t m x
      ((layerDeg_le_piece (auxiliaryForm L) (auxiliaryFlag L) t m) hx)
    rw [eN_creation] at h
    convert h using 2
    push_cast; ring
  rw [(PhiU_of_mem L) (iproj_mem _ _ _), (homog_uP_layer L) hw, uMode_apply,
    homogeneousComponent_J _ L.uNoncritical q ((uDeg_le_ordinary L) t m hx), (PhiU_of_mem L) hx]

/-- **The `R`-preserving component of a nonnegative mode is the symbol derivation.** -/
theorem PhiU_uP_nonneg (c : Fin 3) (m0 : ℕ) {t : ℕ} {m : ℤ} {x : (USpace L)}
    (hx : x ∈ (uDeg L) (layerIndex t m)) :
    (PhiU L) ((uP L) (layerIndex t (m - m0)) ((uMode L) c m0 x)) = symDer c m0 ((PhiU L) x) := by
  have hw : (uMode L) c m0 x ∈ (auxiliaryFlag L).piece t (m - m0) := by
    have h := (uMode_flag L) c (m0 : ℤ) t m x ((layerDeg_le_piece (auxiliaryForm L) (auxiliaryFlag L) t m) hx)
    rwa [show eN (m0 : ℤ) = 0 by simp [eN], add_zero] at h
  rw [(PhiU_of_mem L) (iproj_mem _ _ _), (homog_uP_layer L) hw, uMode_apply,
    homogeneousComponent_J_nonneg _ L.uNoncritical c m0 ((uDeg_le_ordinary L) t m hx), (PhiU_of_mem L) hx]

/-- **The zero modes act on symbols by the adjoint derivation.** -/
theorem PhiU_uMode_zero (c : Fin 3) (x : (USpace L)) : (PhiU L) ((uMode L) c 0 x) = symDer c 0 ((PhiU L) x) := by
  have hpres : ∀ i, ∀ y ∈ (uDeg L) i, (uMode L) c 0 y ∈ (uDeg L) i := fun i y hy =>
    (uZeroModesPreserveLayers L) c i y hy
  have key : ((PhiU L).toLinearMap ∘ₗ (uMode L) c 0) =
      (symDer c 0).toLinearMap ∘ₗ (PhiU L).toLinearMap := by
    apply linearMap_ext_internal (uDeg_isInternal L)
    intro i y hy
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    by_cases hi : ∃ t m, layerIndex t m = i
    · obtain ⟨t, m, rfl⟩ := hi
      have h := (PhiU_uP_nonneg L) c 0 hy
      rw [Nat.cast_zero, sub_zero, iproj_of_mem_same _ (hpres _ y hy)] at h
      exact h
    · push Not at hi
      rw [(uDeg_eq_bot_of L) hi, Submodule.mem_bot] at hy
      rw [hy, map_zero, map_zero, map_zero]
  exact LinearMap.congr_fun key x


end

end VOA.TwoSeries
