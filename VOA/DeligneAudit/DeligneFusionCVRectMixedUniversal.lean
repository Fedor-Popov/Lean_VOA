import VOA.DeligneAudit.DeligneFusionCVRectMixedSpanning
import VOA.DeligneAudit.DeligneFusionCVTotal

/-!
# Actual universal mixed two-rectangle bases

The constructive two-factor theorem applies to every opposite pair with
sizes one, two or three. These are actual unconditional universal CV bounds.
Arbitrary mixed products in `SharpRectangularBases` remain a separate problem.
-/

namespace VOA.DeligneAudit.A2.CVRectMixedUniversal

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVUniv
open VOA.DeligneAudit.A2.CVRectMixedTheta VOA.DeligneAudit.A2.CVRectMixedSpanning
open VOA.DeligneAudit.A2.CVRectSingle

noncomputable section

/-- Encode the two size-one sites in the actual auxiliary family. -/
def pairEpsilon (k l : ℕ) : Weight := (if k = 1 then 1 else 0, if l = 1 then 1 else 0)

/-- Encode the two size-two sites in the actual auxiliary family. -/
def pairNu (k l : ℕ) : Weight := (if k = 2 then 1 else 0, if l = 2 then 1 else 0)

/-- Encode the two size-three sites in the actual auxiliary family. -/
def pairRho (k l : ℕ) : Weight := (if k = 3 then 1 else 0, if l = 3 then 1 else 0)

/-- The actual universal vector has the two single-part simple-root relations.
The unused highest-root CV relations remain part of the universal presentation. -/
theorem pair_twoRectRel (k l : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3)
    (hl : 1 ≤ l) (hl3 : l ≤ 3) :
    TwoRectRel (cvUnivRep (pairEpsilon k l) (pairNu k l) (pairRho k l) 0)
      (cv_wU (pairEpsilon k l) (pairNu k l) (pairRho k l) 0) k l := by
  have h := cvUniv_rel (pairEpsilon k l) (pairNu k l) (pairRho k l) 0
  have h1 : (pairEpsilon k l).1 + 2 * (pairNu k l).1 + 3 * (pairRho k l).1 + 0 = k := by
    interval_cases k <;> norm_num [pairEpsilon, pairNu, pairRho]
  have h2 : (pairEpsilon k l).2 + 2 * (pairNu k l).2 + 3 * (pairRho k l).2 + 0 = l := by
    interval_cases l <;> norm_num [pairEpsilon, pairNu, pairRho]
  have hp1 : parts (pairRho k l).1 (pairNu k l).1 ((pairEpsilon k l).1 + 0) = [k] := by
    interval_cases k <;> simp [parts, pairEpsilon, pairNu, pairRho]
  have hp2 : parts (pairRho k l).2 (pairNu k l).2 ((pairEpsilon k l).2 + 0) = [l] := by
    interval_cases l <;> simp [parts, pairEpsilon, pairNu, pairRho]
  refine ⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_⟩
  · simpa only [h1] using h.cartan_first
  · simpa only [h2] using h.cartan_second
  · simpa only [hp1] using h.first
  · simpa only [hp2] using h.second

/-- The actual universal module of an opposite small rectangle pair is finite
and satisfies its sharp product bound. No dimension hypothesis is an input. -/
theorem pair_universal_bound (k l : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3)
    (hl : 1 ≤ l) (hl3 : l ≤ 3) :
    CVBound (pairEpsilon k l) (pairNu k l) (pairRho k l) 0 := by
  let ε := pairEpsilon k l
  let ν := pairNu k l
  let ϱ := pairRho k l
  have htop : cyclicSpan (cvUnivRep ε ν ϱ 0) (cv_wU ε ν ϱ 0) = ⊤ :=
    cv_span_top ε ν ϱ 0
  obtain ⟨hFD, hdim⟩ := two_rectangle_bound (pair_twoRectRel k l hk hk3 hl hl3) hk3 hl3
  haveI : FiniteDimensional ℂ (CVMod ε ν ϱ 0) := by
    refine ⟨?_⟩
    rw [← htop]
    exact Module.Finite.iff_fg.mp hFD
  have hcount : cvCount ε ν ϱ 0 = (k + 2).choose 2 * (l + 2).choose 2 := by
    dsimp only [ε, ν, ϱ]
    interval_cases k <;> interval_cases l <;> decide
  change Module.finrank ℂ (cyclicSpan (cvUnivRep ε ν ϱ 0) (cv_wU ε ν ϱ 0)) ≤ _ at hdim
  rw [htop, finrank_top] at hdim
  exact ⟨inferInstance, hdim.trans_eq hcount.symm⟩

end

end VOA.DeligneAudit.A2.CVRectMixedUniversal

#print axioms VOA.DeligneAudit.A2.CVRectMixedUniversal.pair_twoRectRel
#print axioms VOA.DeligneAudit.A2.CVRectMixedUniversal.pair_universal_bound
