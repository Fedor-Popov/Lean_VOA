import VOA.DeligneAudit.D4FusionContactPolynomialCandidate
import VOA.DeligneAudit.D4FusionContactCurrentBound

/-!
# High PBW word monomials belong to the actual symbol annihilator

The all-m contact cutoff kills every symbol of length greater than 2m.
At m=2 we may therefore add the entire high-word ideal without a degree-five
rank certificate. The remaining polynomial count concerns degrees at most four.
-/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V} {m : ℕ}

theorem source_grWord_high_zero (h : LocalWeylRelG D4sector R w m)
    (l : List CurrentLetter) (hl : 2 * m + 1 ≤ l.length) : grWord R w l = 0 := by
  apply Subtype.ext
  change symbol R w l.length (nword R w l) = 0
  apply symbol_zero_of_mem R w
  apply Pbelow_mono R w hl
  change nword R w l ∈ Ple R w (2 * m)
  rw [Ple_eq_currentPiece]
  exact localWeyl_currentWord_bound h l

/-- All word monomials above the proved source cutoff. No finite
enumeration or assumed polynomial dimension is built into this ideal. -/
def highWordIdeal (m : ℕ) : Ideal (MvPolynomial (Vars m) ℂ) :=
  Ideal.span {p | ∃ l : List (Vars m), 2 * m + 1 ≤ l.length ∧ p = polyWord l}

theorem source_highWordIdeal_le_ann (h : LocalWeylRelG D4sector R w m) :
    highWordIdeal m ≤ annIdeal R w (modeLetter m) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨l,hl,rfl⟩
  change polyEval R w (modeLetter m) (polyWord l) = 0
  rw [polyEval_polyWord]
  exact source_grWord_high_zero h (l.map (modeLetter m)) (by simpa only [List.length_map] using hl)

/-- Concrete finite-count target: the verified differential candidate
plus the source-supplied high-word cutoff. -/
def m2ModelIdeal : Ideal (MvPolynomial (Vars 2) ℂ) := candidateIdeal ⊔ highWordIdeal 2

abbrev M2Model := MvPolynomial (Vars 2) ℂ ⧸ m2ModelIdeal.restrictScalars ℂ

theorem source_m2ModelIdeal_le_ann (h : LocalWeylRelG D4sector R w 2) :
    m2ModelIdeal ≤ annIdeal R w (modeLetter 2) :=
  sup_le (source_candidateIdeal_le_ann h) (source_highWordIdeal_le_ann h)

def m2ModelMap (h : LocalWeylRelG D4sector R w 2) : M2Model →ₗ[ℂ] Gr R w :=
  polyQuotientMap R w (modeLetter 2) m2ModelIdeal (source_m2ModelIdeal_le_ann h)

theorem m2ModelMap_surjective (h : LocalWeylRelG D4sector R w 2) :
    Function.Surjective (m2ModelMap h) := by
  apply polyQuotientMap_surjective
  apply modeLetter_cover
  intro i r hr
  exact localWeyl_high_kills (by decide) h (radIndex i) r hr

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.source_highWordIdeal_le_ann
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.source_m2ModelIdeal_le_ann
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.m2ModelMap_surjective
