import VOA.DeligneAudit.D4FusionContactAllMWheelsCore
import VOA.DeligneAudit.D4FusionContactAllMWheelsTable
import VOA.DeligneAudit.D4FusionContactAllMCandidate

/-! Actual uniform static triangle wheels in the all-m source ideal.
The opposite-corner nil power is derived along three outer-root strings.
All statements include m=1 and use no dimension or flatness premise. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

abbrev Poly (m : ℕ) := MvPolynomial (Vars m) ℂ

def zeroVar (m : ℕ) (a : Fin 9) : Poly m := modeX m a 0

def zeroDeriv (m : ℕ) (g : Fin 10) : Derivation ℂ (Poly m) (Poly m) := g0Deriv m g 0

theorem action_variable {m : ℕ} (hm : 1 ≤ m) (j : Fin 12) :
    zeroDeriv m (direction j) (zeroVar m (sourceColor j)) =
      (actionCoeff j : ℂ) • zeroVar m (targetColor j) := by
  have h0 : 0 < m := by omega
  have hx : zeroVar m (sourceColor j) = MvPolynomial.X (sourceColor j, ⟨0, h0⟩) := by
    simp only [zeroVar, modeX, dif_pos h0]
  rw [hx]
  change g0Deriv m (direction j) 0 (MvPolynomial.X (sourceColor j, ⟨0, h0⟩)) = _
  rw [g0Deriv, MvPolynomial.mkDerivation_X]
  simp only [g0Image, zero_add, action_rows, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, zeroVar]

theorem zeroDeriv_closed {m : ℕ} (hm : 1 ≤ m) (g : Fin 10) :
    ∀ p ∈ AllM.candidateIdeal m, zeroDeriv m g p ∈ AllM.candidateIdeal m := by
  intro p hp
  exact AllM.candidateIdeal_deriv m (.inl (g, ⟨0, by omega⟩)) hp

theorem top_power_mem_candidate (m : ℕ) :
    zeroVar m 0 ^ (m + 1) ∈ AllM.candidateIdeal m := by
  let j : AllM.SeedIndex m := ⟨(false, m + 1, 0), by
    constructor
    · change 1 ≤ m + 1
      omega
    · change m < m + 1 + 0
      omega⟩
  have h := AllM.seed_mem_candidate m j
  change PowerSeries.coeff 0 (AllM.current m 0 ^ (m + 1)) ∈ AllM.candidateIdeal m at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow] at h
  simpa only [AllM.current, PowerSeries.constantCoeff_mk, zeroVar] using h

/-- Actual transfer of the simple nil power to the opposite cube corner. -/
theorem bottom_power_mem_candidate {m : ℕ} (hm : 1 ≤ m) :
    zeroVar m 7 ^ (m + 1) ∈ AllM.candidateIdeal m := by
  have h0 : zeroDeriv m 7 (zeroVar m 0) = zeroVar m 1 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 0
  have h3 : zeroDeriv m 8 (zeroVar m 1) = -zeroVar m 4 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 3
  have h4 : zeroDeriv m 7 (zeroVar m 1) = 0 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 4
  have h5 : zeroDeriv m 8 (zeroVar m 4) = 0 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 5
  have h6 : zeroDeriv m 9 (zeroVar m 4) = zeroVar m 7 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 6
  have h7 : zeroDeriv m 9 (zeroVar m 7) = 0 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 7
  have hfirst := power_transfer (AllM.candidateIdeal m) (zeroDeriv m 7)
    (zeroDeriv_closed hm 7) (zeroVar m 0) (zeroVar m 1) h0 h4 (m + 1)
    (top_power_mem_candidate m)
  have hnegI : ∀ p ∈ AllM.candidateIdeal m,
      (-zeroDeriv m 8) p ∈ AllM.candidateIdeal m := by
    intro p hp
    simpa only [Derivation.neg_apply] using
      (AllM.candidateIdeal m).neg_mem (zeroDeriv_closed hm 8 p hp)
  have hneg : (-zeroDeriv m 8) (zeroVar m 1) = zeroVar m 4 := by
    rw [Derivation.neg_apply, h3, neg_neg]
  have hneg0 : (-zeroDeriv m 8) (zeroVar m 4) = 0 := by
    rw [Derivation.neg_apply, h5, neg_zero]
  have hsecond := power_transfer (AllM.candidateIdeal m) (-zeroDeriv m 8)
    hnegI (zeroVar m 1) (zeroVar m 4) hneg hneg0 (m + 1) hfirst
  exact power_transfer (AllM.candidateIdeal m) (zeroDeriv m 9)
    (zeroDeriv_closed hm 9) (zeroVar m 4) (zeroVar m 7) h6 h7 (m + 1) hsecond

def frontWheel (m : ℕ) : Poly m :=
  zeroVar m 0 ^ (m - 1) * zeroVar m 1 * zeroVar m 2 * zeroVar m 3

def backWheel (m : ℕ) : Poly m :=
  zeroVar m 7 ^ (m - 1) * zeroVar m 4 * zeroVar m 5 * zeroVar m 6

/-- The front static wheel is an actual ideal relation for every m>=1. -/
theorem frontWheel_mem_candidate {m : ℕ} (hm : 1 ≤ m) :
    frontWheel m ∈ AllM.candidateIdeal m := by
  have h0 : zeroDeriv m 7 (zeroVar m 0) = zeroVar m 1 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 0
  have h1 : zeroDeriv m 8 (zeroVar m 0) = zeroVar m 2 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 1
  have h2 : zeroDeriv m 9 (zeroVar m 0) = -zeroVar m 3 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 2
  have h3 : zeroDeriv m 8 (zeroVar m 1) = -zeroVar m 4 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 3
  have hpow : zeroVar m 0 ^ (m - 1 + 2) ∈ AllM.candidateIdeal m := by
    simpa only [show m - 1 + 2 = m + 1 by omega] using top_power_mem_candidate m
  have ht := triangle_mem (AllM.candidateIdeal m)
    (zeroDeriv m 7) (zeroDeriv m 8) (zeroDeriv m 9)
    (zeroDeriv_closed hm 7) (zeroDeriv_closed hm 8) (zeroDeriv_closed hm 9)
    (zeroVar m 0) (zeroVar m 1) (zeroVar m 2) (-zeroVar m 3) (-zeroVar m 4)
    h0 h1 h2 h3 (m - 1) hpow
  convert (AllM.candidateIdeal m).neg_mem ht using 1
  dsimp only [frontWheel]
  ring

/-- The opposite static wheel uses the proved opposite-corner nil power. -/
theorem backWheel_mem_candidate {m : ℕ} (hm : 1 ≤ m) :
    backWheel m ∈ AllM.candidateIdeal m := by
  have h8 : zeroDeriv m 4 (zeroVar m 7) = -zeroVar m 6 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 8
  have h9 : zeroDeriv m 5 (zeroVar m 7) = -zeroVar m 5 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 9
  have h10 : zeroDeriv m 6 (zeroVar m 7) = zeroVar m 4 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 10
  have h11 : zeroDeriv m 5 (zeroVar m 6) = -zeroVar m 3 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_variable hm 11
  have hmix : zeroDeriv m 5 (-zeroVar m 6) = zeroVar m 3 := by rw [map_neg, h11, neg_neg]
  have hpow : zeroVar m 7 ^ (m - 1 + 2) ∈ AllM.candidateIdeal m := by
    simpa only [show m - 1 + 2 = m + 1 by omega] using bottom_power_mem_candidate hm
  have ht := triangle_mem (AllM.candidateIdeal m)
    (zeroDeriv m 4) (zeroDeriv m 5) (zeroDeriv m 6)
    (zeroDeriv_closed hm 4) (zeroDeriv_closed hm 5) (zeroDeriv_closed hm 6)
    (zeroVar m 7) (-zeroVar m 6) (-zeroVar m 5) (zeroVar m 4) (zeroVar m 3)
    h8 h9 h10 hmix (m - 1) hpow
  convert ht using 1
  dsimp only [backWheel]
  ring

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V} {m : ℕ}

theorem frontWheel_mem_ann (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m) :
    frontWheel m ∈ annIdeal R w (modeLetter m) :=
  AllM.source_candidateIdeal_le_ann hm h (frontWheel_mem_candidate hm)

theorem backWheel_mem_ann (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m) :
    backWheel m ∈ annIdeal R w (modeLetter m) :=
  AllM.source_candidateIdeal_le_ann hm h (backWheel_mem_candidate hm)

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels.bottom_power_mem_candidate
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels.frontWheel_mem_candidate
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels.backWheel_mem_candidate
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels.frontWheel_mem_ann
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels.backWheel_mem_ann
