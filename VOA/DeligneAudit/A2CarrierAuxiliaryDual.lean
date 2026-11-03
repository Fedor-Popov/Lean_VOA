/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CarrierAuxiliaryLayer

/-!
# Dual of a Casimir layer as auxiliary coefficient families (B1, step 3a)

A functional `λ` on the `d`-th Casimir layer in bidegree `(p, N)` gives the coefficient family
`layerCoeffs λ e = λ (auxToLayer (monomial e))` on auxiliary jet monomials.  It satisfies every
auxiliary quadratic coefficient equation (`layerCoeffs_equations`), is supported in particle number
`(N - p - 2d) + d`, derivative degree `p` and Casimir count `d` (`layerCoeffs_supported`,
`layerCoeffs_count`), vanishes identically when `p + 2d > N`, and determines `λ`
(`layerCoeffs_injective`, from `auxToLayer_surjective`).
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial
open VOA.FiniteJet VOA.QuadraticJetCoefficientPairing VOA.QuadraticCurrentCoefficientReindexing

noncomputable section

/-- The auxiliary coefficient family of a layer functional. -/
def layerCoeffs (p N d : ℕ) :
    Module.Dual ℂ (casimirLayer p N d) →ₗ[ℂ] ((JetVar AuxVar p →₀ ℕ) → ℂ) where
  toFun l e := l (auxToLayer p N d (monomial e 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientFunctional_layerCoeffs (p N d : ℕ) (l : Module.Dual ℂ (casimirLayer p N d)) :
    coefficientFunctional (layerCoeffs p N d l) = l ∘ₗ auxToLayer p N d := by
  apply Finsupp.lhom_ext
  intro e c
  change coefficientFunctional (layerCoeffs p N d l) (monomial e c) =
    l (auxToLayer p N d (monomial e c))
  rw [coefficientFunctional_monomial,
    show (monomial e c : JetPoly ℂ AuxVar p) = c • monomial e 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, map_smul, smul_eq_mul]
  rfl

/-- **The layer coefficients satisfy all auxiliary quadratic equations.** -/
theorem layerCoeffs_equations (p N d : ℕ) (l : Module.Dual ℂ (casimirLayer p N d)) :
    CoefficientEquations auxMatrix p (layerCoeffs p N d l) := by
  intro r n e
  rw [← coefficientFunctional_spectator_relationCoeff _ _ n (Nat.lt_succ_iff.mp n.isLt) e,
    coefficientFunctional_layerCoeffs, LinearMap.comp_apply,
    auxToLayer_relation p N d r n (Nat.lt_succ_iff.mp n.isLt) e, map_zero]

theorem layerCoeffs_injective (p N d : ℕ) : Function.Injective (layerCoeffs p N d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro l hl
  have h := coefficientFunctional_layerCoeffs p N d l
  rw [hl] at h
  apply LinearMap.ext
  intro y
  obtain ⟨f, rfl⟩ := auxToLayer_surjective p N d y
  have := congrArg (fun φ => φ f) h
  simp only [LinearMap.comp_apply] at this
  rw [← this]
  have h0 : coefficientFunctional (0 : (JetVar AuxVar p →₀ ℕ) → ℂ) = 0 := by
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
theorem weight_conformal_split (p : ℕ) (e : JetVar AuxVar p →₀ ℕ) :
    (Finsupp.weight (auxBideg p) e).2 =
      Finsupp.weight (fun _ : JetVar AuxVar p => 1) e + Finsupp.weight (auxCnt p) e +
        Finsupp.weight (fun v : JetVar AuxVar p => v.order.val) e := by
  classical
  rw [weight_prod_snd]
  induction e using Finsupp.induction with
  | zero => simp
  | single_add a n f _ _ ih =>
    simp only [map_add, Finsupp.weight_single, ih, smul_eq_mul]
    rcases a with ⟨g | g, o⟩ <;> simp [auxBideg, auxBase, auxCnt, auxCount] <;> ring

theorem layerCoeffs_ne_zero_imp (p N d : ℕ) (l : Module.Dual ℂ (casimirLayer p N d))
    (e : JetVar AuxVar p →₀ ℕ) (he : layerCoeffs p N d l e ≠ 0) :
    Finsupp.weight (auxCnt p) e = d ∧
      Finsupp.weight (fun v : JetVar AuxVar p => v.order.val) e = p ∧
      Finsupp.weight (fun _ : JetVar AuxVar p => 1) e + d + p = N := by
  have h : Finsupp.weight (auxCW p) e = (d, N) ∧ (Finsupp.weight (auxBideg p) e).1 = p := by
    by_contra hn
    apply he
    change l (auxToLayer p N d (monomial e 1)) = 0
    rw [auxToLayer_monomial_eq_zero p N d e hn, map_zero]
  obtain ⟨hcw, hli⟩ := h
  rw [weight_auxCW] at hcw
  have hc := congrArg Prod.fst hcw
  have hconf := congrArg Prod.snd hcw
  simp only at hc hconf
  rw [weight_prod_fst] at hli
  refine ⟨hc, hli, ?_⟩
  rw [weight_conformal_split] at hconf
  change Finsupp.weight (fun v : JetVar AuxVar p => v.order.val) e = p at hli
  rw [← hconf, hli, hc]

theorem layerCoeffs_count (p N d : ℕ) (l : Module.Dual ℂ (casimirLayer p N d))
    (e : JetVar AuxVar p →₀ ℕ) (he : layerCoeffs p N d l e ≠ 0) :
    Finsupp.weight (auxCnt p) e = d :=
  (layerCoeffs_ne_zero_imp p N d l e he).1

theorem layerCoeffs_supported (p N d : ℕ) (hN : p + 2 * d ≤ N)
    (l : Module.Dual ℂ (casimirLayer p N d)) :
    SupportedBidegree p (N - p - 2 * d + d) p (layerCoeffs p N d l) := by
  intro e he
  obtain ⟨_, hli, hsum⟩ := layerCoeffs_ne_zero_imp p N d l e he
  exact ⟨by omega, hli⟩

/-- Below the diagonal `p + 2d ≤ N` every layer functional has zero coefficients. -/
theorem layerCoeffs_eq_zero_of_lt (p N d : ℕ) (hN : N < p + 2 * d)
    (l : Module.Dual ℂ (casimirLayer p N d)) : layerCoeffs p N d l = 0 := by
  funext e
  by_contra he
  obtain ⟨hc, _, hsum⟩ := layerCoeffs_ne_zero_imp p N d l e he
  have hle := weight_le_weight (auxCnt p) (fun _ : JetVar AuxVar p => 1)
    (fun v => by rcases v with ⟨g | g, o⟩ <;> simp [auxCnt, auxCount]) e
  rw [hc] at hle
  omega

end

end VOA.DeligneAudit.A2

section AxiomAudit
open VOA.DeligneAudit.A2
#print axioms layerCoeffs_equations
#print axioms layerCoeffs_injective
#print axioms layerCoeffs_supported
#print axioms layerCoeffs_eq_zero_of_lt
end AxiomAudit
