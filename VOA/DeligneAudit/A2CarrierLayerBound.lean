/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CarrierAuxiliaryCarrier

/-!
# Step B1 for A₂: the Casimir layer bound

Composing the layer coefficients (`layerCoeffs`, injective) with the pattern restriction
(`auxPoly`, injective on Casimir count `d`) gives an injective linear map from the dual of the
`d`-th Casimir layer of the `(p, N)` piece of `Jet(Sym sl₃/I₂ⁿˢ)` into
`degreePiece (auxiliaryCarrier fullMatrix (N - p - 2d) d) p`.  Hence

* **`casimirLayerBound : CasimirLayerBound`** (proved, no hypotheses);
* **`casimirAuxiliaryBound : CasimirAuxiliaryBound`** (step B1 of the Deligne chain, proved);
* `carrierDim_le_demazure_of_sector`: `carrierDim N ≤ D N` from `SectorFusionBound` (B2–B8, U4, U5)
  and `MixedFusionRecursion` (U6) only.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial
open VOA.FiniteJet VOA.QuadraticJetCoefficientPairing VOA.QuadraticCurrentCoefficientReindexing
open VOA.QuadraticCurrentFunctionalCarrier

noncomputable section

/-! ### Linearity of the pattern restriction -/

/-- `auxPoly` as a linear map. -/
def auxPolyLinear (p m d : ℕ) :
    ((JetVar AuxVar p →₀ ℕ) → ℂ) →ₗ[ℂ] TensorPolynomial (K := ℂ) (σ := Fin 8) m d where
  toFun := auxPoly p m d
  map_add' F G := by
    funext t
    simp only [auxPoly, tensorPolynomial, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c F := by
    funext t
    simp only [auxPoly, tensorPolynomial, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.smul_sum, smul_monomial]

/-! ### Sorting the Casimir labels to the end -/

theorem weight_auxCnt_coloredExponent {p n : ℕ} (t : Fin n → AuxVar) (a : Fin n → Fin (p + 1)) :
    Finsupp.weight (auxCnt p) (coloredExponent t a) =
      (Finset.univ.filter (fun k => (t k).isRight = true)).card := by
  rw [coloredExponent, map_sum, Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finsupp.weight_single, smul_eq_mul, one_mul]
  rcases t k with x | u <;> simp [auxCnt, auxCount]

theorem exists_perm_pat {m d : ℕ} (t' : Fin (m + d) → AuxVar)
    (h : (Finset.univ.filter (fun k => (t' k).isRight = true)).card = d) :
    ∃ (π : Equiv.Perm (Fin (m + d))) (t : Fin m → Fin 8), t' ∘ π = pat m d t := by
  classical
  let S : Fin (m + d) → Prop := fun k => (t' k).isRight = true
  have hS : Fintype.card {k // S k} = d := by rw [Fintype.card_subtype]; exact h
  have hSc : Fintype.card {k // ¬ S k} = m := by
    rw [Fintype.card_subtype_compl, hS, Fintype.card_fin]; omega
  let e1 := Fintype.equivFinOfCardEq hSc
  let e2 := Fintype.equivFinOfCardEq hS
  let π : Equiv.Perm (Fin (m + d)) := finSumFinEquiv.symm.trans
    ((Equiv.sumCongr e1.symm e2.symm).trans ((Equiv.sumComm _ _).trans (Equiv.sumCompl S)))
  let t : Fin m → Fin 8 := fun i => Sum.elim id (fun _ => 0) (t' (e1.symm i).1)
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
    have hnot := (e1.symm i).2
    simp only [t]
    rcases hv : t' (e1.symm i).1 with x | u
    · rfl
    · exact absurd (by simp [S, hv]) hnot
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
theorem eq_zero_of_auxPoly_eq_zero {p m d : ℕ} (F : (JetVar AuxVar p →₀ ℕ) → ℂ)
    (hsupp : SupportedBidegree p (m + d) p F)
    (hcount : ∀ e, F e ≠ 0 → Finsupp.weight (auxCnt p) e = d)
    (h0 : auxPoly p m d F = 0) : F = 0 := by
  funext e
  by_contra he
  obtain ⟨t', a, rfl⟩ := exists_coloredExponent e (hsupp e he).1
  have hc := hcount _ he
  rw [weight_auxCnt_coloredExponent] at hc
  obtain ⟨π, t, hπ⟩ := exists_perm_pat t' hc
  have hrel := coloredExponent_relabel π.symm t' a
  rw [Equiv.symm_symm, hπ] at hrel
  apply he
  rw [← hrel, ← coeff_tensorPolynomial F (pat m d t)]
  change MvPolynomial.coeff _ (auxPoly p m d F t) = 0
  rw [h0]
  simp

/-! ### The layer bound -/

/-- The injective dual map of a Casimir layer into the auxiliary sector carrier. -/
def layerToAux (p N d : ℕ) (hN : p + 2 * d ≤ N) :
    Module.Dual ℂ (casimirLayer p N d) →ₗ[ℂ]
      degreePiece (auxiliaryCarrier fullMatrix (N - p - 2 * d) d) p :=
  LinearMap.codRestrict _
    (LinearMap.codRestrict (auxiliaryCarrier fullMatrix (N - p - 2 * d) d)
      (auxPolyLinear p (N - p - 2 * d) d ∘ₗ layerCoeffs p N d)
      (fun l => auxPoly_mem (layerCoeffs_supported p N d hN l) (layerCoeffs_equations p N d l)))
    (fun l t => auxPoly_homogeneous (layerCoeffs_supported p N d hN l) t)

theorem layerToAux_injective (p N d : ℕ) (hN : p + 2 * d ≤ N) :
    Function.Injective (layerToAux p N d hN) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro l hl
  apply layerCoeffs_injective p N d
  rw [map_zero]
  apply eq_zero_of_auxPoly_eq_zero (m := N - p - 2 * d) (d := d) _
    (layerCoeffs_supported p N d hN l) (layerCoeffs_count p N d l)
  have := congrArg (fun x => x.1.1) hl
  exact this

theorem casimirLayer_finiteDimensional (p N d : ℕ) :
    FiniteDimensional ℂ (casimirLayer p N d) := by
  haveI : FiniteDimensional ℂ (bidegreeImage p N) :=
    finiteDimensional_presentedJetLiBidegreeImage (fun _ => 1) (fun _ => Nat.one_pos) p p N I2ns
  infer_instance

/-- **B1 core, proved.** -/
theorem casimirLayerBound : CasimirLayerBound := by
  refine ⟨fun p N d => ?_⟩
  haveI := casimirLayer_finiteDimensional p N d
  rw [← Subspace.dual_finrank_eq]
  split_ifs with hN
  · exact LinearMap.finrank_le_finrank_of_injective (layerToAux_injective p N d hN)
  · haveI : Subsingleton (Module.Dual ℂ (casimirLayer p N d)) := ⟨fun l l' => by
      apply layerCoeffs_injective p N d
      rw [layerCoeffs_eq_zero_of_lt p N d (by omega) l,
        layerCoeffs_eq_zero_of_lt p N d (by omega) l']⟩
    rw [Module.finrank_zero_of_subsingleton]

/-- **Step B1 of the Deligne chain for A₂, proved.** -/
theorem casimirAuxiliaryBound : CasimirAuxiliaryBound :=
  casimirAuxiliaryBound_of_layerBound casimirLayerBound

/-- **Carrier side of the A₂ inequality**, conditional only on the sector fusion bound
(B2–B8 with U4, U5) and the mixed fusion recursion (U6). -/
theorem carrierDim_le_demazure_of_sector (F Dem : ℕ → PowerSeries ℚ) (D : ℕ → ℕ)
    (hD : ∀ N, (D N : ℚ) = VOA.DeligneAudit.CarrierChain.demazureCoeffOf Dem N)
    (hF : SectorFusionBound F) (hU6 : MixedFusionRecursion F Dem) (N : ℕ) :
    carrierDim N ≤ D N :=
  carrierDim_le_demazure F Dem D hD casimirAuxiliaryBound hF hU6 N

end

end VOA.DeligneAudit.A2

section AxiomAudit
open VOA.DeligneAudit.A2
#print axioms exists_perm_pat
#print axioms eq_zero_of_auxPoly_eq_zero
#print axioms layerToAux_injective
#print axioms casimirLayerBound
#print axioms casimirAuxiliaryBound
#print axioms carrierDim_le_demazure_of_sector
end AxiomAudit
