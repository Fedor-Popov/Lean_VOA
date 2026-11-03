import VOA.DeligneAudit.DeligneFusionCVRectSplit
import VOA.DeligneAudit.DeligneFusionCVRectIdealMap

/-!
# Exact ideal-quotient compatibility of the canonical current split

The reversed currents transform by proved series equalities. Functoriality of
the generated coefficient ideal therefore gives its actual image ideal and an
algebra equivalence on quotients, including its underlying linear equivalence.
-/

namespace VOA.DeligneAudit.A2.CVRectSplit

open VOA.DeligneAudit.A2.CVRectIntegrationIdeal
open VOA.DeligneAudit.A2.CVRectIntegrationSeries

noncomputable section

/-- A proved equality of image ideals descends the canonical split invertibly. -/
def splitQuotientEquiv (M N : ℕ)
    (I : Ideal (MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ))
    (J : Ideal (Polynomial (MvPolynomial (Fin M ⊕ Fin N) ℂ)))
    (hIJ : J = I.map (splitVars M N).toRingHom) :
    (MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ ⧸ I) ≃ₐ[ℂ]
      Polynomial (MvPolynomial (Fin M ⊕ Fin N) ℂ) ⧸ J :=
  Ideal.quotientEquivAlg I J (splitVars M N) hIJ

@[simp] theorem splitQuotientEquiv_mk (M N : ℕ)
    (I : Ideal (MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ))
    (J : Ideal (Polynomial (MvPolynomial (Fin M ⊕ Fin N) ℂ)))
    (hIJ : J = I.map (splitVars M N).toRingHom)
    (p : MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ) :
    splitQuotientEquiv M N I J hIJ (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk J (splitVars M N p) := rfl

/-- The canonical reversed-current ideals correspond exactly under the split. -/
theorem splitCoefficientIdeal_map (M N : ℕ) (μ : ℕ → ℕ → ℕ) :
    Ideal.map (splitVars M N).toRingHom
      (coefficientIdeal (reverseLeft (M + 1) N) (reverseRight (M + 1) N) μ) =
      coefficientIdeal (chosenCurrent M (reverseLeft M N))
        (constantCurrent (reverseRight M N)) μ := by
  rw [CVRectIdealMap.coefficientIdeal_map, splitVars_reverseLeft, splitVars_reverseRight]

/-- The coefficient-ideal quotient is preserved as a complex algebra. -/
def splitCoefficientQuotientEquiv (M N : ℕ) (μ : ℕ → ℕ → ℕ) :
    (MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ ⧸
      coefficientIdeal (reverseLeft (M + 1) N) (reverseRight (M + 1) N) μ) ≃ₐ[ℂ]
    (Polynomial (MvPolynomial (Fin M ⊕ Fin N) ℂ) ⧸
      coefficientIdeal (chosenCurrent M (reverseLeft M N))
        (constantCurrent (reverseRight M N)) μ) :=
  splitQuotientEquiv M N _ _ (splitCoefficientIdeal_map M N μ).symm

/-- The same exact equivalence with the scalar-restricted submodule quotient types. -/
def splitCoefficientQuotientLinearEquiv (M N : ℕ) (μ : ℕ → ℕ → ℕ) :
    (MvPolynomial (Fin (M + 1) ⊕ Fin N) ℂ ⧸
      (coefficientIdeal (reverseLeft (M + 1) N) (reverseRight (M + 1) N) μ).restrictScalars ℂ)
        ≃ₗ[ℂ]
    (Polynomial (MvPolynomial (Fin M ⊕ Fin N) ℂ) ⧸
      (coefficientIdeal (chosenCurrent M (reverseLeft M N))
        (constantCurrent (reverseRight M N)) μ).restrictScalars ℂ) :=
  (splitCoefficientQuotientEquiv M N μ).toLinearEquiv

end
end VOA.DeligneAudit.A2.CVRectSplit

#print axioms VOA.DeligneAudit.A2.CVRectSplit.splitCoefficientIdeal_map
#print axioms VOA.DeligneAudit.A2.CVRectSplit.splitCoefficientQuotientEquiv
#print axioms VOA.DeligneAudit.A2.CVRectSplit.splitCoefficientQuotientLinearEquiv
