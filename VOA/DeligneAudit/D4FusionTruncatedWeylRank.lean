import VOA.DeligneAudit.D4FusionTruncatedWeyl
import VOA.DeligneAudit.D4FusionContactPolynomialGrDimensionUniversal

/-! Kus–Littelmann route, KL-A: the total-dimension input T for D4 follows from a
rank bound on the universal truncated module `UModG (lwSpec m)` = W(mθ, m)
(m ≥ 1), through the proved universal current-degree projections. KL-F is
named here as the rank bound 29^m on the universal Demazure module
`UModG (ravFam m 0)` = D(1, mθ); it is a literature input (Fourier–Littelmann /
the Demazure character formula), not proved. -/
namespace VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.D4

/-- KL-A target: W(mθ, m) is finite of rank at most 28^m. -/
def UnivTruncatedRank : Prop :=
  ∀ m, 1 ≤ m → FiniteDimensional ℂ (UModG D4sector.f (lwSpec D4sector m)) ∧
    Module.finrank ℂ (UModG D4sector.f (lwSpec D4sector m)) ≤ 28 ^ m

/-- KL-F (literature leaf): D(1, mθ) is finite of rank at most 29^m. -/
def DemazureUnivRank : Prop :=
  ∀ m, 1 ≤ m → FiniteDimensional ℂ (UModG D4sector.f (ravFam D4sector m 0)) ∧
    Module.finrank ℂ (UModG D4sector.f (ravFam D4sector m 0)) ≤ 29 ^ m

/-- **KL-A**: input T from the universal truncated rank bound. -/
theorem fusionTotalDimG_of_univTruncatedRank (h : UnivTruncatedRank) :
    FiniteG.FusionTotalDimG D4sector := by
  intro m V _ _ ρ w hw B
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using D4FusionContact.localWeyl_zero_total_dim hw B
  · obtain ⟨hfd, hrk⟩ := h m hm
    have hs := (localWeylRelG_iff D4sector ρ w m).mp hw
    exact (D4FusionContact.Polynomial.sum_source_cycDeg_le_univ hs B).trans hrk

end VOA.DeligneAudit.UnivG
#print axioms VOA.DeligneAudit.UnivG.fusionTotalDimG_of_univTruncatedRank
