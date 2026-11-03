/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CarrierAuxiliaryDual

/-!
# Restriction to the current/Casimir label pattern (B1, step 3b)

For an auxiliary coefficient family `F` with `m + d` particles, the tensor polynomial
`tensorPolynomial F` lies in the current carrier of the auxiliary relations (restored theorem
`mem_currentCarrier_iff_coefficientEquations`).  Evaluating it on the label pattern
`pat m d t` (currents `t` on the first `m` slots, the Casimir on the last `d`) gives `auxPoly m d F`,
which lies in the Deligne auxiliary carrier `auxiliaryCarrier fullMatrix m d`:

* symmetry from the simultaneous symmetry of `tensorPolynomial F`;
* the `I₂` current equations from the lifted relations `inl o`;
* mixed and Casimir–Casimir collisions from the relations `x_a c`, `c c`.

On families supported in Casimir count `d`, `F ↦ auxPoly m d F` is injective (every labelling with
exactly `d` Casimir labels is a permutation of the pattern).
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial
open VOA.FiniteJet VOA.QuadraticJetCoefficientPairing VOA.QuadraticCurrentCoefficientReindexing
open VOA.QuadraticCurrentFunctionalCarrier VOA.CollisionCommonFactors
open VOA.DeligneAuxiliaryCollision VOA.QuadraticCurrentCollisionCoefficients

noncomputable section

/-! ### Collisions in either order -/

theorem collisionMap_swap_eq_zero {I : Type*} [DecidableEq I] (i j : I) (h : j ≠ i)
    (f : MvPolynomial I ℂ) (hf : collisionMap (K := ℂ) i j h f = 0) :
    collisionMap (K := ℂ) j i h.symm f = 0 := by
  let g : {a : I // a ≠ i} → {a : I // a ≠ j} := fun a =>
    if ha : a.1 = j then ⟨i, fun hij => h hij.symm⟩ else ⟨a.1, ha⟩
  have hg : g ∘ collisionIndex i j h = collisionIndex j i h.symm := by
    funext a
    simp only [Function.comp, collisionIndex, g]
    by_cases hai : a = i
    · subst hai
      simp
    · by_cases haj : a = j
      · subst haj; simp [hai]
      · simp [hai, haj]
  unfold collisionMap at *
  rw [← hg, ← rename_rename, hf, map_zero]

/-! ### The label pattern -/

/-- Currents `t` on the first `m` slots, the Casimir on the last `d`. -/
def pat (m d : ℕ) (t : Fin m → Fin 8) : Fin (m + d) → AuxVar :=
  fun k => if h : k.val < m then Sum.inl (t ⟨k.val, h⟩) else Sum.inr ()

/-- The auxiliary tensor polynomial on the pattern. -/
def auxPoly (p m d : ℕ) (F : (JetVar AuxVar p →₀ ℕ) → ℂ) :
    TensorPolynomial (K := ℂ) (σ := Fin 8) m d :=
  fun t => tensorPolynomial (m := m + d) F (pat m d t)

/-- Lift a pair of current slots. -/
def liftPair {m : ℕ} (d : ℕ) (ij : IncreasingPair (Fin m)) : IncreasingPair (Fin (m + d)) :=
  ⟨(ij.1.1.castAdd d, ij.1.2.castAdd d), by
    change (ij.1.1.castAdd d).val < (ij.1.2.castAdd d).val
    simp only [Fin.val_castAdd]
    exact ij.2⟩

theorem pat_insertPair {m d : ℕ} (ij : IncreasingPair (Fin m)) (t : Fin m → Fin 8)
    (x y : Fin 8) :
    pat m d (insertPair ij t (x, y)) =
      insertPair (liftPair d ij) (pat m d t) (Sum.inl x, Sum.inl y) := by
  funext k
  simp only [pat, insertPair, liftPair, Function.update_apply]
  by_cases hk : k.val < m
  · simp only [hk, dif_pos]
    have e2 : (k = ij.1.2.castAdd d) ↔ ((⟨k.val, hk⟩ : Fin m) = ij.1.2) := by
      simp [Fin.ext_iff]
    have e1 : (k = ij.1.1.castAdd d) ↔ ((⟨k.val, hk⟩ : Fin m) = ij.1.1) := by
      simp [Fin.ext_iff]
    by_cases h2 : (⟨k.val, hk⟩ : Fin m) = ij.1.2
    · rw [if_pos h2, if_pos (e2.mpr h2)]
    · rw [if_neg h2, if_neg (fun h => h2 (e2.mp h))]
      by_cases h1 : (⟨k.val, hk⟩ : Fin m) = ij.1.1
      · rw [if_pos h1, if_pos (e1.mpr h1)]
      · rw [if_neg h1, if_neg (fun h => h1 (e1.mp h))]
  · have h2 : k ≠ ij.1.2.castAdd d := by
      intro h; apply hk; rw [h]; simp
    have h1 : k ≠ ij.1.1.castAdd d := by
      intro h; apply hk; rw [h]; simp
    simp only [hk, dif_neg, not_false_eq_true, if_neg h2, if_neg h1]

theorem insertPair_self {α : Type*} {n : ℕ} (ij : IncreasingPair (Fin n)) (f : Fin n → α) :
    insertPair ij f (f ij.1.1, f ij.1.2) = f := by
  simp [insertPair]

variable {p m d : ℕ} {F : (JetVar AuxVar p →₀ ℕ) → ℂ}

/-! ### Membership in the auxiliary carrier -/

theorem auxPoly_symmetric (hP : tensorPolynomial (m := m + d) F ∈ currentCarrier auxMatrix (m + d) 0) :
    Symmetric (auxPoly p m d F) := by
  intro e g he t
  have hsym := hP.1 e e (fun _ => rfl) (pat m d t)
  change MvPolynomial.rename e (tensorPolynomial F (pat m d t)) =
    tensorPolynomial F (pat m d (t ∘ g.symm))
  rw [hsym]
  congr 1
  funext k
  have hpres := preserves_current_of_extends e g he
  simp only [Function.comp, pat]
  by_cases hk : k.val < m
  · have hsymm : e.symm k = (g.symm ⟨k.val, hk⟩).castAdd d := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]
      exact Fin.ext rfl
    have hk' : (e.symm k).val < m := by rw [hsymm]; simp
    rw [dif_pos hk', dif_pos hk]
    congr 2
    apply Fin.ext
    change (e.symm k).val = _
    rw [hsymm]
    simp
  · have hk' : ¬ (e.symm k).val < m := by
      intro h
      apply hk
      have := (hpres (e.symm k)).mpr h
      rwa [Equiv.apply_symm_apply] at this
    rw [dif_neg hk', dif_neg hk]

theorem auxPoly_currentEquations
    (hP : tensorPolynomial (m := m + d) F ∈ currentCarrier auxMatrix (m + d) 0) :
    CurrentEquations fullMatrix (auxPoly p m d F) := by
  intro o ij t
  have h := hP.2 (Sum.inl o) (liftPair d ij) (pat m d t)
  unfold currentReadback projectedDiagonal at h ⊢
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type] at h
  simp only [Fintype.sum_sum_type, auxMatrix, map_zero, zero_mul, Finset.sum_const_zero,
    add_zero] at h
  rw [Fintype.sum_prod_type]
  have key : ∀ x y, (fun xy => auxPoly p m d F (insertPair ij t xy)) (x, y) =
      tensorPolynomial F (insertPair (liftPair d ij) (pat m d t) (Sum.inl x, Sum.inl y)) :=
    fun x y => congrArg (tensorPolynomial F) (pat_insertPair ij t x y)
  simp only [key]
  exact h

theorem auxPoly_auxiliary
    (hP : tensorPolynomial (m := m + d) F ∈ currentCarrier auxMatrix (m + d) 0)
    (t : Fin m → Fin 8) (ij : Pair m d) (hj : m ≤ ij.1.2.val) :
    collisionMap (K := ℂ) ij.1.2 ij.1.1 (ne_of_lt ij.2) (auxPoly p m d F t) = 0 := by
  classical
  have hpj : pat m d t ij.1.2 = Sum.inr () := by
    simp only [pat]; rw [dif_neg (by omega)]
  -- the relation testing the pair `ij`
  let r : AuxRel := if hi : ij.1.1.val < m then Sum.inr (Sum.inl (t ⟨ij.1.1.val, hi⟩))
    else Sum.inr (Sum.inr ())
  have hr : ∀ xy, auxMatrix r xy = if xy = (pat m d t ij.1.1, pat m d t ij.1.2) then 1 else 0 := by
    intro xy
    rw [hpj]
    by_cases hi : ij.1.1.val < m
    · have hpi : pat m d t ij.1.1 = Sum.inl (t ⟨ij.1.1.val, hi⟩) := by
        simp only [pat]; rw [dif_pos hi]
      rw [hpi]
      simp only [r, dif_pos hi, auxMatrix]
    · have hpi : pat m d t ij.1.1 = Sum.inr () := by
        simp only [pat]; rw [dif_neg hi]
      rw [hpi]
      simp only [r, dif_neg hi, auxMatrix]
  have h := hP.2 r ij (pat m d t)
  unfold currentReadback projectedDiagonal at h
  simp only [hr] at h
  rw [Finset.sum_eq_single (pat m d t ij.1.1, pat m d t ij.1.2)] at h
  · rw [if_pos rfl, map_one, one_mul, insertPair_self] at h
    exact collisionMap_swap_eq_zero (ij.1.1.castAdd 0) (ij.1.2.castAdd 0) _ _ h
  · intro xy _ hxy
    rw [if_neg hxy, map_zero, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

theorem auxPoly_mem (hsupp : SupportedBidegree p (m + d) p F)
    (heq : CoefficientEquations auxMatrix p F) :
    auxPoly p m d F ∈ auxiliaryCarrier fullMatrix m d := by
  have hP := (mem_currentCarrier_iff_coefficientEquations auxMatrix F hsupp le_rfl).mpr heq
  exact ⟨⟨auxPoly_symmetric hP, auxPoly_currentEquations hP⟩,
    fun t ij hj => auxPoly_auxiliary hP t ij hj⟩

theorem auxPoly_homogeneous (hsupp : SupportedBidegree p (m + d) p F) (t : Fin m → Fin 8) :
    (auxPoly p m d F t).IsWeightedHomogeneous (fun _ => 1) p :=
  tensorPolynomial_homogeneous F hsupp (pat m d t)

end

end VOA.DeligneAudit.A2

section AxiomAudit
open VOA.DeligneAudit.A2
#print axioms collisionMap_swap_eq_zero
#print axioms auxPoly_symmetric
#print axioms auxPoly_currentEquations
#print axioms auxPoly_auxiliary
#print axioms auxPoly_mem
end AxiomAudit
