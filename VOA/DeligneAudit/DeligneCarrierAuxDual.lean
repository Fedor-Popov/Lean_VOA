/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierAuxLayer

/-!
# Type-generic version of `A2CarrierAuxiliaryDual`

Mechanically generalized from the A₂ file `A2CarrierAuxiliaryDual` to arbitrary type data
`D : DeligneCarrierData` (`Fin 8 ↦ Fin D.n`, `I2ns ↦ D.I`, `casimir ↦ D.Q`, U3 ↦ `D.u3`).
See that file for the mathematical commentary.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open MvPolynomial
open VOA.FiniteJet VOA.QuadraticJetCoefficientPairing VOA.QuadraticCurrentCoefficientReindexing
open DeligneCarrierData

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

variable (D : DeligneCarrierData)
include D


/-- The auxiliary coefficient family of a layer functional. -/
def layerCoeffs (p N d : ℕ) :
    Module.Dual ℂ ((casimirLayer D) p N d) →ₗ[ℂ] ((JetVar (AuxVar D) p →₀ ℕ) → ℂ) where
  toFun l e := l ((auxToLayer D) p N d (monomial e 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientFunctional_layerCoeffs (p N d : ℕ) (l : Module.Dual ℂ ((casimirLayer D) p N d)) :
    coefficientFunctional ((layerCoeffs D) p N d l) = l ∘ₗ (auxToLayer D) p N d := by
  apply Finsupp.lhom_ext
  intro e c
  change coefficientFunctional ((layerCoeffs D) p N d l) (monomial e c) =
    l ((auxToLayer D) p N d (monomial e c))
  rw [coefficientFunctional_monomial,
    show (monomial e c : JetPoly ℂ (AuxVar D) p) = c • monomial e 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, map_smul, smul_eq_mul]
  rfl

/-- **The layer coefficients satisfy all auxiliary quadratic equations.** -/
theorem layerCoeffs_equations (p N d : ℕ) (l : Module.Dual ℂ ((casimirLayer D) p N d)) :
    CoefficientEquations (auxMatrix D) p ((layerCoeffs D) p N d l) := by
  intro r n e
  rw [← coefficientFunctional_spectator_relationCoeff _ _ n (Nat.lt_succ_iff.mp n.isLt) e,
    (coefficientFunctional_layerCoeffs D), LinearMap.comp_apply,
    (auxToLayer_relation D) p N d r n (Nat.lt_succ_iff.mp n.isLt) e, map_zero]

theorem layerCoeffs_injective (p N d : ℕ) : Function.Injective ((layerCoeffs D) p N d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro l hl
  have h := (coefficientFunctional_layerCoeffs D) p N d l
  rw [hl] at h
  apply LinearMap.ext
  intro y
  obtain ⟨f, rfl⟩ := (auxToLayer_surjective D) p N d y
  have := congrArg (fun φ => φ f) h
  simp only [LinearMap.comp_apply] at this
  rw [← this]
  have h0 : coefficientFunctional (0 : (JetVar (AuxVar D) p →₀ ℕ) → ℂ) = 0 := by
    apply Finsupp.lhom_ext
    intro e c
    change coefficientFunctional 0 (monomial e c) = 0
    rw [coefficientFunctional_monomial]
    simp
  rw [h0]
  rfl

/-! ### Support -/

theorem weight_le_weight {ι : Type*} (w w' : ι → ℕ) (hw : ∀ i, w i ≤ w' i) (e : ι →₀ ℕ) :
    Finsupp.weight w e ≤ Finsupp.weight w' e := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hw i)

/-- Conformal weight = particle number + Casimir count + derivative degree. -/
theorem weight_conformal_split (p : ℕ) (e : JetVar (AuxVar D) p →₀ ℕ) :
    (Finsupp.weight ((auxBideg D) p) e).2 =
      Finsupp.weight (fun _ : JetVar (AuxVar D) p => 1) e + Finsupp.weight ((auxCnt D) p) e +
        Finsupp.weight (fun v : JetVar (AuxVar D) p => v.order.val) e := by
  classical
  rw [(weight_prod_snd D)]
  induction e using Finsupp.induction with
  | zero => simp
  | single_add a n f _ _ ih =>
    simp only [map_add, Finsupp.weight_single, ih, smul_eq_mul]
    rcases a with ⟨g | g, o⟩ <;> simp [auxBideg, auxBase, auxCnt, auxCount] <;> ring

theorem layerCoeffs_ne_zero_imp (p N d : ℕ) (l : Module.Dual ℂ ((casimirLayer D) p N d))
    (e : JetVar (AuxVar D) p →₀ ℕ) (he : (layerCoeffs D) p N d l e ≠ 0) :
    Finsupp.weight ((auxCnt D) p) e = d ∧
      Finsupp.weight (fun v : JetVar (AuxVar D) p => v.order.val) e = p ∧
      Finsupp.weight (fun _ : JetVar (AuxVar D) p => 1) e + d + p = N := by
  have h : Finsupp.weight ((auxCW D) p) e = (d, N) ∧ (Finsupp.weight ((auxBideg D) p) e).1 = p := by
    by_contra hn
    apply he
    change l ((auxToLayer D) p N d (monomial e 1)) = 0
    rw [(auxToLayer_monomial_eq_zero D) p N d e hn, map_zero]
  obtain ⟨hcw, hli⟩ := h
  rw [(weight_auxCW D)] at hcw
  have hc := congrArg Prod.fst hcw
  have hconf := congrArg Prod.snd hcw
  simp only at hc hconf
  rw [(weight_prod_fst D)] at hli
  refine ⟨hc, hli, ?_⟩
  rw [(weight_conformal_split D)] at hconf
  change Finsupp.weight (fun v : JetVar (AuxVar D) p => v.order.val) e = p at hli
  rw [← hconf, hli, hc]

theorem layerCoeffs_count (p N d : ℕ) (l : Module.Dual ℂ ((casimirLayer D) p N d))
    (e : JetVar (AuxVar D) p →₀ ℕ) (he : (layerCoeffs D) p N d l e ≠ 0) :
    Finsupp.weight ((auxCnt D) p) e = d :=
  ((layerCoeffs_ne_zero_imp D) p N d l e he).1

theorem layerCoeffs_supported (p N d : ℕ) (hN : p + 2 * d ≤ N)
    (l : Module.Dual ℂ ((casimirLayer D) p N d)) :
    SupportedBidegree p (N - p - 2 * d + d) p ((layerCoeffs D) p N d l) := by
  intro e he
  obtain ⟨_, hli, hsum⟩ := (layerCoeffs_ne_zero_imp D) p N d l e he
  exact ⟨by omega, hli⟩

/-- Below the diagonal `p + 2d ≤ N` every layer functional has zero coefficients. -/
theorem layerCoeffs_eq_zero_of_lt (p N d : ℕ) (hN : N < p + 2 * d)
    (l : Module.Dual ℂ ((casimirLayer D) p N d)) : (layerCoeffs D) p N d l = 0 := by
  funext e
  by_contra he
  obtain ⟨hc, _, hsum⟩ := (layerCoeffs_ne_zero_imp D) p N d l e he
  have hle := (weight_le_weight D) ((auxCnt D) p) (fun _ : JetVar (AuxVar D) p => 1)
    (fun v => by rcases v with ⟨g | g, o⟩ <;> simp [auxCnt, auxCount]) e
  rw [hc] at hle
  omega

end

end VOA.DeligneAudit.DeligneCarrier
