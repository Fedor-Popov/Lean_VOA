import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import VOA.DeligneAudit.DeligneFusionCVRectIntegrationSeries

/-!
# Splitting the first variable of one color

The left-color mode zero becomes the outer polynomial variable. The remaining
left-color modes and every right-color mode become coefficient variables.
The explicit equivalence induces a surjective linear map on any pair of ideal
quotients once the actual forward ideal inclusion is proved.
-/

namespace VOA.DeligneAudit.A2.CVRectSplit

noncomputable section

/-- The variable index equivalence that singles out left-color mode zero. -/
def splitIndex (M N : ℕ) :
    Fin (M + 1) ⊕ Fin N ≃ Option (Fin M ⊕ Fin N) where
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

@[simp] theorem splitIndex_left_zero (M N : ℕ) :
    splitIndex M N (Sum.inl 0) = none := rfl

@[simp] theorem splitIndex_left_succ (M N : ℕ) (i : Fin M) :
    splitIndex M N (Sum.inl i.succ) = some (Sum.inl i) := rfl

@[simp] theorem splitIndex_right (M N : ℕ) (j : Fin N) :
    splitIndex M N (Sum.inr j) = some (Sum.inr j) := rfl

@[simp] theorem splitIndex_symm_none (M N : ℕ) :
    (splitIndex M N).symm none = Sum.inl 0 := rfl

@[simp] theorem splitIndex_symm_left (M N : ℕ) (i : Fin M) :
    (splitIndex M N).symm (some (Sum.inl i)) = Sum.inl i.succ := rfl

@[simp] theorem splitIndex_symm_right (M N : ℕ) (j : Fin N) :
    (splitIndex M N).symm (some (Sum.inr j)) = Sum.inr j := rfl

/-- The canonical split as an algebra equivalence over the original scalar field. -/
def splitVars (M N : ℕ) :
    MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ ≃ₐ[ℂ]
      Polynomial (MvPolynomial (Fin M ⊕ Fin N) ℂ) :=
  (MvPolynomial.renameEquiv ℂ (splitIndex M N)).trans
    (MvPolynomial.optionEquivLeft ℂ (Fin M ⊕ Fin N))

@[simp] theorem splitVars_X_left_zero (M N : ℕ) :
    splitVars M N (MvPolynomial.X (Sum.inl 0)) = Polynomial.X := by
  simp [splitVars, MvPolynomial.renameEquiv_apply]

@[simp] theorem splitVars_X_left_succ (M N : ℕ) (i : Fin M) :
    splitVars M N (MvPolynomial.X (Sum.inl i.succ)) =
      Polynomial.C (MvPolynomial.X (Sum.inl i)) := by
  simp [splitVars, MvPolynomial.renameEquiv_apply]

@[simp] theorem splitVars_X_right (M N : ℕ) (j : Fin N) :
    splitVars M N (MvPolynomial.X (Sum.inr j)) =
      Polynomial.C (MvPolynomial.X (Sum.inr j)) := by
  simp [splitVars, MvPolynomial.renameEquiv_apply]

@[simp] theorem splitVars_C (M N : ℕ) (c : ℂ) :
    splitVars M N (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp [splitVars, MvPolynomial.renameEquiv_apply]

@[simp] theorem splitVars_symm_X (M N : ℕ) :
    (splitVars M N).symm Polynomial.X = MvPolynomial.X (Sum.inl 0) := by
  apply (splitVars M N).injective
  simp

@[simp] theorem splitVars_symm_C_X_left (M N : ℕ) (i : Fin M) :
    (splitVars M N).symm (Polynomial.C (MvPolynomial.X (Sum.inl i))) =
      MvPolynomial.X (Sum.inl i.succ) := by
  apply (splitVars M N).injective
  simp

@[simp] theorem splitVars_symm_C_X_right (M N : ℕ) (j : Fin N) :
    (splitVars M N).symm (Polynomial.C (MvPolynomial.X (Sum.inr j))) =
      MvPolynomial.X (Sum.inr j) := by
  apply (splitVars M N).injective
  simp

@[simp] theorem splitVars_symm_C_C (M N : ℕ) (c : ℂ) :
    (splitVars M N).symm (Polynomial.C (MvPolynomial.C c)) = MvPolynomial.C c := by
  apply (splitVars M N).injective
  simp

/-- The left current, indexed by its distance from the largest retained mode. -/
def reverseLeft (M N : ℕ) : PowerSeries (MvPolynomial (Fin M ⊕ Fin N) ℂ) :=
  ∑ i : Fin M, PowerSeries.C (MvPolynomial.X (Sum.inl i)) *
    PowerSeries.X ^ (M - 1 - i.val)

/-- The right current, with the same reversal convention within its own color. -/
def reverseRight (M N : ℕ) : PowerSeries (MvPolynomial (Fin M ⊕ Fin N) ℂ) :=
  ∑ j : Fin N, PowerSeries.C (MvPolynomial.X (Sum.inr j)) *
    PowerSeries.X ^ (N - 1 - j.val)

@[simp] theorem reverseLeft_zero (N : ℕ) : reverseLeft 0 N = 0 := by
  simp [reverseLeft]

@[simp] theorem reverseRight_zero (M : ℕ) : reverseRight M 0 = 0 := by
  simp [reverseRight]

/-- Splitting the zero-mode isolates exactly the selected term of the reversed left current. -/
theorem splitVars_reverseLeft (M N : ℕ) :
    PowerSeries.map (splitVars M N).toRingHom (reverseLeft (M + 1) N) =
      CVRectIntegrationSeries.chosenCurrent M (reverseLeft M N) := by
  have hcoe (a : MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ) :
      (splitVars M N).toRingHom a = splitVars M N a := rfl
  unfold reverseLeft CVRectIntegrationSeries.chosenCurrent
    CVRectIntegrationSeries.constantCurrent
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  rw [Fin.sum_univ_succ]
  simp only [hcoe,
    splitVars_X_left_zero, splitVars_X_left_succ, Fin.val_zero, Fin.val_succ,
    Nat.add_sub_cancel, Nat.sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  omega

/-- The reversed right current is independent of the selected left zero-mode. -/
theorem splitVars_reverseRight (M N : ℕ) :
    PowerSeries.map (splitVars M N).toRingHom (reverseRight (M + 1) N) =
      CVRectIntegrationSeries.constantCurrent (reverseRight M N) := by
  have hcoe (a : MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ) :
      (splitVars M N).toRingHom a = splitVars M N a := rfl
  unfold reverseRight CVRectIntegrationSeries.constantCurrent
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    hcoe, splitVars_X_right]

/-- The actual split induces a linear map on quotients under a proved ideal inclusion. -/
def splitQuotientMap (M N : ℕ)
    (I : Ideal (MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ))
    (J : Ideal (Polynomial (MvPolynomial (Fin M ⊕ Fin N) ℂ)))
    (hIJ : I ≤ J.comap (splitVars M N).toAlgHom) :
    (MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ ⧸ I) →ₗ[ℂ]
      Polynomial (MvPolynomial (Fin M ⊕ Fin N) ℂ) ⧸ J :=
  (Ideal.quotientMapₐ J (splitVars M N).toAlgHom hIJ).toLinearMap

@[simp] theorem splitQuotientMap_mk (M N : ℕ)
    (I : Ideal (MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ))
    (J : Ideal (Polynomial (MvPolynomial (Fin M ⊕ Fin N) ℂ)))
    (hIJ : I ≤ J.comap (splitVars M N).toAlgHom)
    (p : MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ) :
    splitQuotientMap M N I J hIJ (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk J (splitVars M N p) := rfl

/-- Forward ideal containment suffices for surjectivity, since the split is invertible. -/
theorem splitQuotientMap_surjective (M N : ℕ)
    (I : Ideal (MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ))
    (J : Ideal (Polynomial (MvPolynomial (Fin M ⊕ Fin N) ℂ)))
    (hIJ : I ≤ J.comap (splitVars M N).toAlgHom) :
    Function.Surjective (splitQuotientMap M N I J hIJ) := by
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨Ideal.Quotient.mk I ((splitVars M N).symm p), ?_⟩
  simp

end
end VOA.DeligneAudit.A2.CVRectSplit

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.CVRectSplit.splitVars
#print axioms VOA.DeligneAudit.A2.CVRectSplit.splitVars_X_left_zero
#print axioms VOA.DeligneAudit.A2.CVRectSplit.splitVars_X_left_succ
#print axioms VOA.DeligneAudit.A2.CVRectSplit.splitVars_X_right
#print axioms VOA.DeligneAudit.A2.CVRectSplit.splitQuotientMap_surjective
#print axioms VOA.DeligneAudit.A2.CVRectSplit.splitVars_reverseLeft
#print axioms VOA.DeligneAudit.A2.CVRectSplit.splitVars_reverseRight
end AxiomAudit
