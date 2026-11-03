import VOA.DeligneAudit.D4FusionContactPolynomialSource
import VOA.DeligneAudit.D4FusionContactTruncation
import VOA.DeligneAudit.DeligneFusionGarland

/-!
# Whole contact-current coefficient relations for every multiplicity

These are exact source identities, before PBW grading.  The simple-root
partition is `1^m`, and the highest-root partition is `2^m`.  Coefficients
are kept as sums: already at m=3 their summands need not vanish separately.
No finite-dimensionality, polynomial presentation or counting premise occurs.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllM

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4
open PolynomialSource

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V} {m : ℕ}

/-- The actual simple-root zero-mode nilpotence, for every m. -/
theorem simple_nil (h : LocalWeylRelG D4sector R w m) :
    (simpleF R 0 ^ (m + 1)) w = 0 := by
  have hi : D4sector.lowering (18 : Fin 28) := by
    change 16 ≤ (18 : Fin 28).val ∧ (18 : Fin 28).val < 20
    decide
  have he : D4sector.lowExp (18 : Fin 28) = 1 := rfl
  simpa only [he, Nat.mul_one, Module.End.pow_apply] using h.lowering (18 : Fin 28) hi

/-- Every negative-current mode at or above m kills the source generator.
Unlike the all-root convenience theorem, no positivity of m is required. -/
theorem negative_truncation (h : LocalWeylRelG D4sector R w m)
    (c : Fin 28) (hc : 16 ≤ c.val) (q : ℕ) (hq : m ≤ q) : R.op c q w = 0 := by
  obtain ⟨i, rfl⟩ := negativeIndex_covers c hc
  exact negative_high_zero (highestRel_of_localWeyl h)
    (fun j => h.fusion (negativeIndex j) (negativeIndex_range j)) i q hq

theorem simple_linear (h : LocalWeylRelG D4sector R w m)
    (q : ℕ) (hq : m ≤ q) : simpleF R q w = 0 :=
  negative_truncation h 18 (by decide) q hq

theorem center_linear (h : LocalWeylRelG D4sector R w m)
    (q : ℕ) (hq : m ≤ q) : currentCenter R q w = 0 :=
  negative_truncation h 27 (by decide) q hq

/-- The full simple-root coefficient relation, not its separate monomials. -/
theorem simple_coefficient (h : LocalWeylRelG D4sector R w m)
    (r s : ℕ) (hr : 1 ≤ r) (hs : m < r + s) :
    (PowerSeries.coeff s (Garland.Fs (simpleF R) ^ r)) w = 0 := by
  have hw := highestRel_of_localWeyl h
  exact Garland.garland
    (fun k => by simpa only [add_comm 1 k] using simple_EF R 1 k)
    (fun a k => simple_HF R (a + 1) k)
    (simple_FF R) (simple_E_kills hw 1)
    (fun a => simple_H_pos hw (a + 1) (by omega))
    r hr (simple_nil h) s (by omega)

/-- Garland's highest-root coefficient relations in the rectangular region.
For r=1 the sharper actual relation is `center_linear`. -/
theorem center_coefficient (h : LocalWeylRelG D4sector R w m)
    (r s : ℕ) (hr : 1 ≤ r) (hs : 2 * m < r + s) :
    (PowerSeries.coeff s (Garland.Fs (currentCenter R) ^ r)) w = 0 := by
  have hw := highestRel_of_localWeyl h
  exact Garland.garland
    (fun k => by simpa only [add_comm 1 k] using current_highest_EF R 1 k)
    (fun a k => current_highest_HF R (a + 1) k)
    (current_center_comm R) (current_highest_E_kills hw 1)
    (fun a => current_highest_H_pos hw (a + 1) (by omega))
    r hr (localWeyl_current_center_pow h) s (by omega)

end
end VOA.DeligneAudit.D4FusionContact.AllM

#print axioms VOA.DeligneAudit.D4FusionContact.AllM.simple_nil
#print axioms VOA.DeligneAudit.D4FusionContact.AllM.negative_truncation
#print axioms VOA.DeligneAudit.D4FusionContact.AllM.simple_coefficient
#print axioms VOA.DeligneAudit.D4FusionContact.AllM.center_coefficient
