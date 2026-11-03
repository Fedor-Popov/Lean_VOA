import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeTopShiftClosure

/-! Plain highest-color shift words reduce admissible quartic coefficients
modulo the literal top quadratic/cubic ideal. This differentiates actual
polynomials and uses the independently proved ideal preservation. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section

/-- The head mode acts after the recursively applied tail word. -/
def topShiftWord (m : ℕ) : List ℕ → TopPoly m → TopPoly m
  | [],p => p
  | k::ks,p => topShift m k (topShiftWord m ks p)

theorem topShiftWord_mem_topIdeal (m : ℕ) (ks : List ℕ) {p : TopPoly m}
    (hp : p ∈ topQuadraticCubicIdeal m) :
    topShiftWord m ks p ∈ topQuadraticCubicIdeal m := by
  induction ks with
  | nil => exact hp
  | cons k ks ih => exact topQuadraticCubicIdeal_shift_closed m k ih

/-- All plain shifts retain the exact summed mode and the exact Euler factors. -/
theorem topShiftWord_quartic_static_mem_topIdeal (m s : ℕ) (ks : List ℕ)
    (hs : m < 4 + s) :
    topShiftWord m ks (PowerSeries.coeff s (topCurrent m ^ 4)) -
      (4 ^ ks.length) • PowerSeries.coeff (s + ks.sum) (topCurrent m ^ 4) ∈
      topQuadraticCubicIdeal m := by
  induction ks with
  | nil =>
      simp only [topShiftWord,List.length_nil,List.sum_nil,pow_zero,one_nsmul,
        Nat.add_zero,sub_self]
      exact (topQuadraticCubicIdeal m).zero_mem
  | cons k ks ih =>
      let t := s + ks.sum
      let n := 4 ^ ks.length
      have hpres :
          topShift m k (topShiftWord m ks (PowerSeries.coeff s (topCurrent m ^ 4))) -
            n • topShift m k (PowerSeries.coeff t (topCurrent m ^ 4)) ∈
          topQuadraticCubicIdeal m := by
        simpa only [map_sub,map_nsmul] using
          topQuadraticCubicIdeal_shift_closed m k ih
      have hstep := (topQuadraticCubicIdeal m).nsmul_mem
        (topShift_quartic_step_mem_topIdeal m t k (by dsimp [t]; omega)) n
      rw [nsmul_sub,smul_smul] at hstep
      have hsum := (topQuadraticCubicIdeal m).add_mem hpres hstep
      have htel :
          (topShift m k (topShiftWord m ks (PowerSeries.coeff s (topCurrent m ^ 4))) -
              n • topShift m k (PowerSeries.coeff t (topCurrent m ^ 4))) +
            (n • topShift m k (PowerSeries.coeff t (topCurrent m ^ 4)) -
              (n * 4) • PowerSeries.coeff (t + k) (topCurrent m ^ 4)) =
          topShift m k (topShiftWord m ks (PowerSeries.coeff s (topCurrent m ^ 4))) -
            (n * 4) • PowerSeries.coeff (t + k) (topCurrent m ^ 4) := by abel
      rw [htel] at hsum
      simpa only [topShiftWord,List.length_cons,List.sum_cons,pow_succ,t,n,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsum

end
#print axioms topShiftWord_mem_topIdeal
#print axioms topShiftWord_quartic_static_mem_topIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
