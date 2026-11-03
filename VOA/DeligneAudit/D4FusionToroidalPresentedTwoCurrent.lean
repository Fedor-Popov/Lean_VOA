import VOA.DeligneAudit.D4FusionToroidalPresentedTwoFiltration

/-! The truncated current action on the zero-u-degree quotient. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl

noncomputable section

def twoCurrent : CurrentModule D4sector.f (PTE 2) where
  op c r := if r < 2 then (ρPTE 2).op c 0 r else 0
  comm a b r s v := by
    by_cases hr : r < 2 <;> by_cases hs : s < 2
    · by_cases ht : r + s < 2
      · simpa [hr, hs, ht] using (ρPTE 2).comm a b 0 0 r s v
      · have hz : (∑ e : Fin 28, D4sector.f a b e •
            (if r + s < 2 then (ρPTE 2).op e 0 (r + s) else 0) v) = 0 := by
          simp [ht]
        simpa [hr, hs, hz, ht] using (ρPTE 2).comm a b 0 0 r s v
    · have ht : ¬ r + s < 2 := by omega
      simp [hr, hs, ht]
    · have ht : ¬ r + s < 2 := by omega
      simp [hr, hs, ht]
    · have ht : ¬ r + s < 2 := by omega
      simp [hr, hs, ht]

theorem twoCurrent_inv : ∀ c r, twoN 1 ≤
    (twoN 1).comap (twoCurrent.op c r) := by
  intro c r
  by_cases hr : r ≤ 1
  · simpa [twoCurrent, hr] using twoN_op 1 c 0 r
  · simp [twoCurrent, hr]

abbrev twoZeroQuot := PTE 2 ⧸ twoN 1

def twoZeroCurrent : CurrentModule D4sector.f twoZeroQuot :=
  quotRepG twoCurrent (twoN 1) twoCurrent_inv

def twoZeroGen : twoZeroQuot := (twoN 1).mkQ (pTE 2)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoCurrent_inv
