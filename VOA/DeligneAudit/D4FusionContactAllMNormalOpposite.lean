import VOA.DeligneAudit.D4FusionContactAllMNormalPowerTransport
import VOA.DeligneAudit.D4FusionContactAllMNormalTriangle

/-! Whole opposite-corner coefficient relations for every power.
The factorial transfer is proved, not added as a rootwise CV premise. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

noncomputable section

def oppositePower (m r s : ℕ) : Poly m :=
  ((g0Deriv m 9 0 : Poly m → Poly m)^[r])
    ((((-g0Deriv m 8 0 : Derivation ℂ (Poly m) (Poly m)) : Poly m → Poly m)^[r])
      (((g0Deriv m 7 0 : Poly m → Poly m)^[r])
        (PowerSeries.coeff s (AllM.current m 0 ^ r))))

theorem oppositePower_eq (m r s : ℕ) : oppositePower m r s =
    (r.factorial ^ 3 : ℕ) • PowerSeries.coeff s (AllM.current m 7 ^ r) := by
  have h0 (i : ℕ) : g0Deriv m 7 0 (modeX m 0 i) = modeX m 1 i := by
    simpa [AllMWheels.direction, AllMWheels.sourceColor, AllMWheels.targetColor,
      AllMWheels.actionCoeff] using action_mode m i 0
  have h4 (i : ℕ) : g0Deriv m 7 0 (modeX m 1 i) = 0 := by
    simpa [AllMWheels.direction, AllMWheels.sourceColor, AllMWheels.targetColor,
      AllMWheels.actionCoeff] using action_mode m i 4
  have h3 (i : ℕ) : (-g0Deriv m 8 0) (modeX m 1 i) = modeX m 4 i := by
    have hh : g0Deriv m 8 0 (modeX m 1 i) = -modeX m 4 i := by
      simpa [AllMWheels.direction, AllMWheels.sourceColor, AllMWheels.targetColor,
        AllMWheels.actionCoeff] using action_mode m i 3
    rw [Derivation.neg_apply, hh, neg_neg]
  have h5 (i : ℕ) : (-g0Deriv m 8 0) (modeX m 4 i) = 0 := by
    have hh : g0Deriv m 8 0 (modeX m 4 i) = 0 := by
      simpa [AllMWheels.direction, AllMWheels.sourceColor, AllMWheels.targetColor,
        AllMWheels.actionCoeff] using action_mode m i 5
    rw [Derivation.neg_apply, hh, neg_zero]
  have h6 (i : ℕ) : g0Deriv m 9 0 (modeX m 4 i) = modeX m 7 i := by
    simpa [AllMWheels.direction, AllMWheels.sourceColor, AllMWheels.targetColor,
      AllMWheels.actionCoeff] using action_mode m i 6
  have h7 (i : ℕ) : g0Deriv m 9 0 (modeX m 7 i) = 0 := by
    simpa [AllMWheels.direction, AllMWheels.sourceColor, AllMWheels.targetColor,
      AllMWheels.actionCoeff] using action_mode m i 7
  have hfirst := iterate_deriv_powerCoeff (g0Deriv m 7 0) _ _ h0 h4 r s
  have hsecond := iterate_deriv_powerCoeff (-g0Deriv m 8 0) _ _ h3 h5 r s
  have hthird := iterate_deriv_powerCoeff (g0Deriv m 9 0) _ _ h6 h7 r s
  change ((g0Deriv m 9 0 : Poly m → Poly m)^[r])
    ((((-g0Deriv m 8 0 : Derivation ℂ (Poly m) (Poly m)) : Poly m → Poly m)^[r])
      (((g0Deriv m 7 0 : Poly m → Poly m)^[r])
        (PowerSeries.coeff s (PowerSeries.mk (modeX m 0) ^ r)))) = _
  rw [hfirst, iterate_deriv_nsmul, hsecond, iterate_deriv_nsmul,
    iterate_deriv_nsmul, hthird]
  simp only [smul_smul]
  congr 1
  ring

theorem oppositePower_mem (m r s : ℕ) (hr : 1 ≤ r) (hs : m < r + s) :
    oppositePower m r s ∈ AllM.candidateIdeal m := by
  have hneg : ∀ p ∈ AllM.candidateIdeal m, (-g0Deriv m 8 0) p ∈ AllM.candidateIdeal m := by
    intro p hp
    exact (AllM.candidateIdeal m).neg_mem (g0_closed m 0 8 hp)
  exact iterate_deriv_mem (AllM.candidateIdeal m) (g0Deriv m 9 0)
    (fun p hp => g0_closed m 0 9 hp) r
      (iterate_deriv_mem (AllM.candidateIdeal m) (-g0Deriv m 8 0) hneg r
        (iterate_deriv_mem (AllM.candidateIdeal m) (g0Deriv m 7 0)
          (fun p hp => g0_closed m 0 7 hp) r (simple_coeff_mem m r s hr hs)))

theorem opposite_power_coeff_mem (m r s : ℕ) (hr : 1 ≤ r) (hs : m < r + s) :
    PowerSeries.coeff s (AllM.current m 7 ^ r) ∈ AllM.candidateIdeal m := by
  have hh := oppositePower_mem m r s hr hs
  rw [oppositePower_eq] at hh
  apply AllMWheels.cancel_nat_factor (AllM.candidateIdeal m) (r.factorial ^ 3)
    (pow_ne_zero 3 (Nat.factorial_ne_zero r))
  simpa only [nsmul_eq_mul] using hh

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.oppositePower_eq
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.opposite_power_coeff_mem
