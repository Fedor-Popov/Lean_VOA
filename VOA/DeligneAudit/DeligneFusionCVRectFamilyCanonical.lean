import VOA.DeligneAudit.DeligneFusionCVRectFamily
import VOA.DeligneAudit.DeligneFusionCVRectPolynomialRelations
import VOA.DeligneAudit.DeligneFusionCVRectBound
import VOA.DeligneAudit.DeligneFusionCVUnivQuotient
import VOA.DeligneAudit.DeligneFusionCVUnivSymmetry

/-! # Identifying the actual canonical rectangular quotient at parts one, two and three -/

namespace VOA.DeligneAudit.A2.CVRectFamilyCanonical

open VOA.DeligneAudit.A2.CVFamily
open VOA.DeligneAudit.A2.CVRectFamily
open VOA.DeligneAudit.A2.CVRectZero
open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectPolynomial
open VOA.DeligneAudit.A2.CVUniv
open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

/-- The exact finite-variable quotient counted by the canonical family
is the quotient which maps onto the genuine CV cyclic submodule. -/
def canonicalFamilyEquiv (r n e : ℕ) :
    Family (parts r n e) [] ≃ₗ[ℂ]
      (MvPolynomial (Fin (r + n + e) ⊕ Fin (r + n + e)) ℂ ⧸
        (canonicalCoefficientIdeal r n e).restrictScalars ℂ) := by
  unfold Family Model ideal
  rw [parts_length, List.length_nil, Nat.add_zero]
  have hμ : familyOrder (parts r n e) [] = canonicalOrder r n e := by
    funext a b
    simp only [familyOrder, canonicalOrder, excess, List.map_nil, List.sum_nil, Nat.add_zero]
  rw [hμ]
  exact LinearEquiv.refl ℂ _

/-- The concrete canonical coefficient quotient has its actual sharp
product upper bound, without a fusion-identification premise. -/
theorem canonical_bound (r n e : ℕ) :
    FiniteDimensional ℂ
      (MvPolynomial (Fin (r + n + e) ⊕ Fin (r + n + e)) ℂ ⧸
        (canonicalCoefficientIdeal r n e).restrictScalars ℂ) ∧
      Module.finrank ℂ
        (MvPolynomial (Fin (r + n + e) ⊕ Fin (r + n + e)) ℂ ⧸
          (canonicalCoefficientIdeal r n e).restrictScalars ℂ) ≤ 3 ^ e * 6 ^ n * 10 ^ r := by
  have hb := CVRectBound.parts_bound r n e
  haveI : FiniteDimensional ℂ (Family (parts r n e) []) := hb.1
  let E := canonicalFamilyEquiv r n e
  exact ⟨E.finiteDimensional, E.finrank_eq.symm.le.trans hb.2⟩

/-- The actual one-orientation CV cyclic span has the genuine rectangular
product upper bound. Every relation transfer and count is proved. -/
theorem one_orientation_bound {V : Type} [AddCommGroup V] [Module ℂ V]
    (R : CurrentModule bracketTable V) (w : V) {e n r : ℕ}
    (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0) :
    FiniteDimensional ℂ (CVRectSingle.cyclicSpan R w) ∧
      Module.finrank ℂ (CVRectSingle.cyclicSpan R w) ≤ 3 ^ e * 6 ^ n * 10 ^ r := by
  have hc := canonical_bound r n e
  haveI := hc.1
  have hb := cyclicSpan_bound_of_canonical R w h
  exact ⟨hb.1, hb.2.trans hc.2⟩

/-- The actual universal one-orientation zero-adjoint base has its
sharp upper bound, with no KR-presentation or dimension input. -/
theorem univ_one_orientation_bound (e n r : ℕ) :
    FiniteDimensional ℂ (CVMod (e, 0) (n, 0) (r, 0) 0) ∧
      Module.finrank ℂ (CVMod (e, 0) (n, 0) (r, 0) 0) ≤ 3 ^ e * 6 ^ n * 10 ^ r := by
  let R := cvUnivRep (e, 0) (n, 0) (r, 0) 0
  let w := cv_wU (e, 0) (n, 0) (r, 0) 0
  have hb := one_orientation_bound R w (cvUniv_rel (e, 0) (n, 0) (r, 0) 0)
  have ht : CVRectSingle.cyclicSpan R w = ⊤ := cv_span_top (e, 0) (n, 0) (r, 0) 0
  rw [ht] at hb
  haveI := hb.1
  refine ⟨(Submodule.topEquiv : (⊤ : Submodule ℂ (CVMod (e, 0) (n, 0) (r, 0) 0))
    ≃ₗ[ℂ] CVMod (e, 0) (n, 0) (r, 0) 0).finiteDimensional, ?_⟩
  simpa only [finrank_top] using hb.2

/-- The actual universal base in the opposite orientation has the same
bound by the checked current-root swap equivalence. -/
theorem univ_other_orientation_bound (e n r : ℕ) :
    FiniteDimensional ℂ (CVMod (0, e) (0, n) (0, r) 0) ∧
      Module.finrank ℂ (CVMod (0, e) (0, n) (0, r) 0) ≤ 3 ^ e * 6 ^ n * 10 ^ r := by
  have hb := univ_one_orientation_bound e n r
  haveI := hb.1
  exact ⟨cvSwap_finiteDimensional (e, 0) (n, 0) (r, 0) 0,
    (cvSwap_finrank (e, 0) (n, 0) (r, 0) 0).symm.le.trans hb.2⟩

end

end VOA.DeligneAudit.A2.CVRectFamilyCanonical

#print axioms VOA.DeligneAudit.A2.CVRectFamilyCanonical.canonicalFamilyEquiv
#print axioms VOA.DeligneAudit.A2.CVRectFamilyCanonical.canonical_bound
#print axioms VOA.DeligneAudit.A2.CVRectFamilyCanonical.one_orientation_bound
#print axioms VOA.DeligneAudit.A2.CVRectFamilyCanonical.univ_one_orientation_bound
#print axioms VOA.DeligneAudit.A2.CVRectFamilyCanonical.univ_other_orientation_bound
