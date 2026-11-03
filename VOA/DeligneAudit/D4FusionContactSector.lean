import VOA.DeligneAudit.D4FusionContactCore
import VOA.DeligneAudit.DeligneSectorD4

/-! # The nine-color contact reduction from the actual D₄ sector relations -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorGraded
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V} {m : ℕ}

/-- Every actual local-Weyl source supplies the exact contact highest
relations; no radical spanning or dimension condition is added. -/
theorem highestRel_of_localWeyl (h : LocalWeylRelG D4sector R w m) :
    HighestRel R w m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he r
    exact h.raising e he r
  · intro c hc r hr
    exact h.cartan_pos c hc r hr
  · intro c hc
    by_cases h1 : c.val = 1
    · simpa only [D4sector, thetaD4, h1, if_true, Nat.mul_one] using h.cartan_zero c hc
    · simpa only [D4sector, thetaD4, h1, if_false, Nat.mul_zero, Nat.cast_zero] using
        h.cartan_zero c hc
  · intro i
    have hi : D4sector.lowering (leviIndex i) := by
      change 16 ≤ (leviIndex i).val ∧ (leviIndex i).val < 20
      fin_cases i <;> decide
    have he : D4sector.lowExp (leviIndex i) = 0 := by fin_cases i <;> rfl
    simpa only [he, Nat.mul_zero, Nat.zero_add, Function.iterate_one] using h.lowering _ hi

/-- The three outer simple negative roots kill the actual source in
every current mode, uniformly in the adjoint multiplicity. -/
theorem localWeyl_levi_all (h : LocalWeylRelG D4sector R w m) (i : Fin 3) (r : ℕ) :
    R.op (leviIndex i) r w = 0 :=
  levi_all (highestRel_of_localWeyl h) i r

/-- The actual D₄ local-Weyl module is spanned in every current degree
by sorted words in the nine contact-radical colors. -/
theorem localWeyl_cycDeg_contact (h : LocalWeylRelG D4sector R w m) (d : ℕ) :
    cycDeg R w d ≤ Submodule.span ℂ {u | ∃ l : List (Fin 28 × ℕ),
      l.IsChain (fun a b => contactKey a ≤ contactKey b) ∧
      (∀ x ∈ l, active x.1) ∧
      VOA.DeligneAudit.SectorGraded.wordDeg l = d ∧ u = wordOp R l w} :=
  cycDeg_le_contact (highestRel_of_localWeyl h) d

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.highestRel_of_localWeyl
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_levi_all
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_cycDeg_contact
