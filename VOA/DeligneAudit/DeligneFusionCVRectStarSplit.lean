import VOA.DeligneAudit.DeligneFusionCVRectStarBase
import VOA.DeligneAudit.DeligneFusionCVRectIntegrationSeries

/-! # The actual finite variable split for a selected star leaf -/

namespace VOA.DeligneAudit.A2.CVRectStarSplit

open VOA.DeligneAudit.A2.CVRectStarBase
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectIntegrationSeries

noncomputable section

def splitIndex (L N R : ℕ) :
    Fin (L + 1) ⊕ (Fin N ⊕ Fin R) ≃ Option (Fin L ⊕ (Fin N ⊕ Fin R)) where
  toFun
    | Sum.inl i => Fin.cases none (fun j => some (Sum.inl j)) i
    | Sum.inr j => some (Sum.inr j)
  invFun
    | none => Sum.inl 0
    | some (Sum.inl i) => Sum.inl i.succ
    | some (Sum.inr j) => Sum.inr j
  left_inv x := by
    cases x with
    | inl i => exact Fin.cases rfl (fun _ => rfl) i
    | inr j => rfl
  right_inv x := by
    cases x with
    | none => rfl
    | some x => cases x <;> rfl

def splitVars (L N R : ℕ) :
    StarRing (L + 1) N R ≃ₐ[ℂ] Polynomial (StarRing L N R) :=
  (MvPolynomial.renameEquiv ℂ (splitIndex L N R)).trans
    (MvPolynomial.optionEquivLeft ℂ (Fin L ⊕ (Fin N ⊕ Fin R)))

@[simp] theorem splitVars_X_zero (L N R : ℕ) :
    splitVars L N R (MvPolynomial.X (Sum.inl 0)) = Polynomial.X := by
  simp [splitVars, splitIndex, MvPolynomial.renameEquiv_apply]

@[simp] theorem splitVars_X_succ (L N R : ℕ) (i : Fin L) :
    splitVars L N R (MvPolynomial.X (Sum.inl i.succ)) =
      Polynomial.C (MvPolynomial.X (Sum.inl i)) := by
  simp [splitVars, splitIndex, MvPolynomial.renameEquiv_apply]

@[simp] theorem splitVars_Y (L N R : ℕ) (j : Fin N) :
    splitVars L N R (MvPolynomial.X (Sum.inr (Sum.inl j))) =
      Polynomial.C (MvPolynomial.X (Sum.inr (Sum.inl j))) := by
  simp [splitVars, splitIndex, MvPolynomial.renameEquiv_apply]

@[simp] theorem splitVars_Z (L N R : ℕ) (k : Fin R) :
    splitVars L N R (MvPolynomial.X (Sum.inr (Sum.inr k))) =
      Polynomial.C (MvPolynomial.X (Sum.inr (Sum.inr k))) := by
  simp [splitVars, splitIndex, MvPolynomial.renameEquiv_apply]

theorem splitVars_starX (L N R : ℕ) :
    PowerSeries.map (splitVars L N R).toRingHom (starX (L + 1) N R) =
      chosenCurrent L (starX L N R) := by
  have hcoe (a : StarRing (L + 1) N R) :
      (splitVars L N R).toRingHom a = splitVars L N R a := rfl
  unfold starX chosenCurrent constantCurrent
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  rw [Fin.sum_univ_succ]
  simp only [hcoe, splitVars_X_zero, splitVars_X_succ, Fin.val_zero, Fin.val_succ,
    Nat.add_sub_cancel, Nat.sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  omega

theorem splitVars_starY (L N R : ℕ) :
    PowerSeries.map (splitVars L N R).toRingHom (starY (L + 1) N R) =
      constantCurrent (starY L N R) := by
  have hcoe (a : StarRing (L + 1) N R) :
      (splitVars L N R).toRingHom a = splitVars L N R a := rfl
  unfold starY constantCurrent
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    hcoe, splitVars_Y]

theorem splitVars_starZ (L N R : ℕ) :
    PowerSeries.map (splitVars L N R).toRingHom (starZ (L + 1) N R) =
      constantCurrent (starZ L N R) := by
  have hcoe (a : StarRing (L + 1) N R) :
      (splitVars L N R).toRingHom a = splitVars L N R a := rfl
  unfold starZ constantCurrent
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    hcoe, splitVars_Z]

theorem splitCoefficientIdeal_map (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    Ideal.map (splitVars L N R).toRingHom
      (coefficientIdeal3 (starX (L + 1) N R) (starY (L + 1) N R) (starZ (L + 1) N R) μ) =
      coefficientIdeal3 (chosenCurrent L (starX L N R)) (constantCurrent (starY L N R))
        (constantCurrent (starZ L N R)) μ := by
  rw [coefficientIdeal3_map, splitVars_starX, splitVars_starY, splitVars_starZ]

def splitCoefficientQuotientLinearEquiv (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    (StarRing (L + 1) N R ⧸
      (coefficientIdeal3 (starX (L + 1) N R) (starY (L + 1) N R)
        (starZ (L + 1) N R) μ).restrictScalars ℂ) ≃ₗ[ℂ]
      (Polynomial (StarRing L N R) ⧸
        (coefficientIdeal3 (chosenCurrent L (starX L N R)) (constantCurrent (starY L N R))
          (constantCurrent (starZ L N R)) μ).restrictScalars ℂ) :=
  (Ideal.quotientEquivAlg _ _ (splitVars L N R)
    (splitCoefficientIdeal_map L N R μ).symm).toLinearEquiv

end

end VOA.DeligneAudit.A2.CVRectStarSplit

#print axioms VOA.DeligneAudit.A2.CVRectStarSplit.splitVars
#print axioms VOA.DeligneAudit.A2.CVRectStarSplit.splitCoefficientIdeal_map
#print axioms VOA.DeligneAudit.A2.CVRectStarSplit.splitCoefficientQuotientLinearEquiv
