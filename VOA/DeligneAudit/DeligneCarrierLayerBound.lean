/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierAuxCarrier

/-!
# Type-generic version of `A2CarrierLayerBound`

Mechanically generalized from the A₂ file `A2CarrierLayerBound` to arbitrary type data
`D : DeligneCarrierData` (`Fin 8 ↦ Fin D.n`, `I2ns ↦ D.I`, `casimir ↦ D.Q`, U3 ↦ `D.u3`).
See that file for the mathematical commentary.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open MvPolynomial
open VOA.FiniteJet VOA.QuadraticJetCoefficientPairing VOA.QuadraticCurrentCoefficientReindexing
open VOA.QuadraticCurrentFunctionalCarrier
open DeligneCarrierData

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

variable (D : DeligneCarrierData)
include D


/-! ### Linearity of the pattern restriction -/

/-- `(auxPoly D)` as a linear map. -/
def auxPolyLinear (p m d : ℕ) :
    ((JetVar (AuxVar D) p →₀ ℕ) → ℂ) →ₗ[ℂ] TensorPolynomial (K := ℂ) (σ := Fin D.n) m d where
  toFun := (auxPoly D) p m d
  map_add' F G := by
    funext t
    simp only [auxPoly, tensorPolynomial, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c F := by
    funext t
    simp only [auxPoly, tensorPolynomial, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.smul_sum, smul_monomial]

/-! ### Sorting the Casimir labels to the end -/

theorem weight_auxCnt_coloredExponent {p n : ℕ} (t : Fin n → (AuxVar D)) (a : Fin n → Fin (p + 1)) :
    Finsupp.weight ((auxCnt D) p) (coloredExponent t a) =
      (Finset.univ.filter (fun k => (t k).isRight = true)).card := by
  rw [coloredExponent, map_sum, Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finsupp.weight_single, smul_eq_mul, one_mul]
  rcases t k with x | u <;> simp [auxCnt, auxCount]

theorem exists_perm_pat {m d : ℕ} (t' : Fin (m + d) → (AuxVar D))
    (h : (Finset.univ.filter (fun k => (t' k).isRight = true)).card = d) :
    ∃ (π : Equiv.Perm (Fin (m + d))) (t : Fin m → Fin D.n), t' ∘ π = (pat D) m d t := by
  classical
  let S : Fin (m + d) → Prop := fun k => (t' k).isRight = true
  have hS : Fintype.card {k // S k} = d := by rw [Fintype.card_subtype]; exact h
  have hSc : Fintype.card {k // ¬ S k} = m := by
    rw [Fintype.card_subtype_compl, hS, Fintype.card_fin]; omega
  let e1 := Fintype.equivFinOfCardEq hSc
  let e2 := Fintype.equivFinOfCardEq hS
  let π : Equiv.Perm (Fin (m + d)) := finSumFinEquiv.symm.trans
    ((Equiv.sumCongr e1.symm e2.symm).trans ((Equiv.sumComm _ _).trans (Equiv.sumCompl S)))
  let t : Fin m → Fin D.n := fun i => (t' (e1.symm i).1).getLeft (by
    have h := (e1.symm i).2
    simp only [S] at h
    simpa using h)
  refine ⟨π, t, ?_⟩
  funext k
  simp only [Function.comp, pat]
  by_cases hk : k.val < m
  · rw [dif_pos hk]
    obtain ⟨i, hi⟩ : ∃ i : Fin m, k = Fin.castAdd d i := ⟨⟨k.val, hk⟩, Fin.ext rfl⟩
    have hii : (⟨k.val, hk⟩ : Fin m) = i := by
      apply Fin.ext; change k.val = i.val; rw [hi]; simp
    rw [hii]
    subst hi
    have hπ : π (Fin.castAdd d i) = (e1.symm i).1 := by simp [π]
    rw [hπ]
    exact (Sum.inl_getLeft _ _).symm
  · rw [dif_neg hk]
    obtain ⟨j, rfl⟩ : ∃ j : Fin d, k = Fin.natAdd m j :=
      ⟨⟨k.val - m, by omega⟩, by apply Fin.ext; simp; omega⟩
    have hπ : π (Fin.natAdd m j) = (e2.symm j).1 := by simp [π]
    rw [hπ]
    have hyes := (e2.symm j).2
    rcases hv : t' (e2.symm j).1 with x | u
    · exact absurd hyes (by simp [S, hv])
    · rfl

/-- **Injectivity of the pattern restriction on Casimir count `d`.** -/
theorem eq_zero_of_auxPoly_eq_zero {p m d : ℕ} (F : (JetVar (AuxVar D) p →₀ ℕ) → ℂ)
    (hsupp : SupportedBidegree p (m + d) p F)
    (hcount : ∀ e, F e ≠ 0 → Finsupp.weight ((auxCnt D) p) e = d)
    (h0 : (auxPoly D) p m d F = 0) : F = 0 := by
  funext e
  by_contra he
  obtain ⟨t', a, rfl⟩ := exists_coloredExponent e (hsupp e he).1
  have hc := hcount _ he
  rw [(weight_auxCnt_coloredExponent D)] at hc
  obtain ⟨π, t, hπ⟩ := (exists_perm_pat D) t' hc
  have hrel := coloredExponent_relabel π.symm t' a
  rw [Equiv.symm_symm, hπ] at hrel
  apply he
  rw [← hrel, ← coeff_tensorPolynomial F ((pat D) m d t)]
  change MvPolynomial.coeff _ ((auxPoly D) p m d F t) = 0
  rw [h0]
  simp

/-! ### The layer bound -/

/-- The injective dual map of a Casimir layer into the auxiliary sector carrier. -/
def layerToAux (p N d : ℕ) (hN : p + 2 * d ≤ N) :
    Module.Dual ℂ ((casimirLayer D) p N d) →ₗ[ℂ]
      degreePiece (auxiliaryCarrier D.fullMatrix (N - p - 2 * d) d) p :=
  LinearMap.codRestrict _
    (LinearMap.codRestrict (auxiliaryCarrier D.fullMatrix (N - p - 2 * d) d)
      ((auxPolyLinear D) p (N - p - 2 * d) d ∘ₗ (layerCoeffs D) p N d)
      (fun l => (auxPoly_mem D) ((layerCoeffs_supported D) p N d hN l) ((layerCoeffs_equations D) p N d l)))
    (fun l t => (auxPoly_homogeneous D) ((layerCoeffs_supported D) p N d hN l) t)

theorem layerToAux_injective (p N d : ℕ) (hN : p + 2 * d ≤ N) :
    Function.Injective ((layerToAux D) p N d hN) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro l hl
  apply (layerCoeffs_injective D) p N d
  rw [map_zero]
  apply eq_zero_of_auxPoly_eq_zero D (m := N - p - 2 * d) (d := d) _
    ((layerCoeffs_supported D) p N d hN l) ((layerCoeffs_count D) p N d l)
  have := congrArg (fun x => x.1.1) hl
  exact this

theorem casimirLayer_finiteDimensional (p N d : ℕ) :
    FiniteDimensional ℂ ((casimirLayer D) p N d) := by
  haveI : FiniteDimensional ℂ ((bidegreeImage D) p N) :=
    finiteDimensional_presentedJetLiBidegreeImage (fun _ => 1) (fun _ => Nat.one_pos) p p N D.I
  infer_instance

/-- **B1 core, proved.** -/
theorem casimirLayerBound : (CasimirLayerBound D) := by
  refine ⟨fun p N d => ?_⟩
  haveI := (casimirLayer_finiteDimensional D) p N d
  rw [← Subspace.dual_finrank_eq]
  split_ifs with hN
  · exact LinearMap.finrank_le_finrank_of_injective ((layerToAux_injective D) p N d hN)
  · haveI : Subsingleton (Module.Dual ℂ ((casimirLayer D) p N d)) := ⟨fun l l' => by
      apply (layerCoeffs_injective D) p N d
      rw [(layerCoeffs_eq_zero_of_lt D) p N d (by omega) l,
        (layerCoeffs_eq_zero_of_lt D) p N d (by omega) l']⟩
    rw [Module.finrank_zero_of_subsingleton]

/-- **Step B1 of the Deligne chain for A₂, proved.** -/
theorem casimirAuxiliaryBound : (CasimirAuxiliaryBound D) :=
  (casimirAuxiliaryBound_of_layerBound D) (casimirLayerBound D)

/-- **(Carrier D) side of the A₂ inequality**, conditional only on the sector fusion bound
(B2–B8 with U4, U5) and the mixed fusion recursion (U6). -/
theorem carrierDim_le_demazure_of_sector (F Dem : ℕ → PowerSeries ℚ) (Dz : ℕ → ℕ)
    (hD : ∀ N, (Dz N : ℚ) = VOA.DeligneAudit.CarrierChain.demazureCoeffOf Dem N)
    (hF : (SectorFusionBound D) F) (hU6 : MixedFusionRecursion F Dem) (N : ℕ) :
    (carrierDim D) N ≤ Dz N :=
  (carrierDim_le_demazure D) F Dem Dz hD (casimirAuxiliaryBound D) hF hU6 N

end

end VOA.DeligneAudit.DeligneCarrier
