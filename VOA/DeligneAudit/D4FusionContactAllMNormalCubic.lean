import VOA.DeligneAudit.D4FusionContactAllMNormalIdeal

/-! Whole cubic coefficient rows for uniform quartic straightening.
The opposite-corner seed is an explicit derivation word, not a new source premise.
No leading-term classification or sharp count is asserted here. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

noncomputable section

def cubic (m s : ℕ) : Poly m := PowerSeries.coeff s (AllM.current m 0 ^ 3)

def frontRow (m s t : ℕ) : Poly m :=
  modeX m 3 t * g0Deriv m 8 0 (g0Deriv m 7 0 (cubic m s)) -
    modeX m 4 t * g0Deriv m 9 0 (cubic m s)

def middleRow (m s t : ℕ) : Poly m :=
  g0Deriv m 9 0 (g0Deriv m 8 0 (g0Deriv m 7 0 (frontRow m s t)))

def oppositeCubic (m s : ℕ) : Poly m :=
  -((fun p => g0Deriv m 9 0 p)^[3])
    (((fun p => g0Deriv m 8 0 p)^[3]) (((fun p => g0Deriv m 7 0 p)^[3]) (cubic m s)))

def backRow (m s t : ℕ) : Poly m :=
  modeX m 4 t * g0Deriv m 5 0 (g0Deriv m 4 0 (oppositeCubic m s)) -
    modeX m 3 t * g0Deriv m 6 0 (oppositeCubic m s)

theorem cubic_mem (m s : ℕ) (hs : m < 3 + s) : cubic m s ∈ AllM.candidateIdeal m := by
  exact AllM.seed_mem_candidate m ⟨(false, 3, s), by
    exact ⟨by change 1 ≤ 3; omega, hs⟩⟩

theorem frontRow_mem (m s t : ℕ) (hs : m < 3 + s) :
    frontRow m s t ∈ AllM.candidateIdeal m := by
  exact (AllM.candidateIdeal m).sub_mem
    ((AllM.candidateIdeal m).mul_mem_left _ (g0_closed m 0 8 (g0_closed m 0 7 (cubic_mem m s hs))))
    ((AllM.candidateIdeal m).mul_mem_left _ (g0_closed m 0 9 (cubic_mem m s hs)))

theorem middleRow_mem (m s t : ℕ) (hs : m < 3 + s) :
    middleRow m s t ∈ AllM.candidateIdeal m :=
  g0_closed m 0 9 (g0_closed m 0 8 (g0_closed m 0 7 (frontRow_mem m s t hs)))

theorem iterate_g0_mem (m : ℕ) (g : Fin 10) (n : ℕ) {p : Poly m}
    (hp : p ∈ AllM.candidateIdeal m) :
    ((fun q => g0Deriv m g 0 q)^[n]) p ∈ AllM.candidateIdeal m := by
  induction n with
  | zero => exact hp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact g0_closed m 0 g ih

theorem oppositeCubic_mem (m s : ℕ) (hs : m < 3 + s) :
    oppositeCubic m s ∈ AllM.candidateIdeal m :=
  (AllM.candidateIdeal m).neg_mem
    (iterate_g0_mem m 9 3 (iterate_g0_mem m 8 3 (iterate_g0_mem m 7 3 (cubic_mem m s hs))))

theorem backRow_mem (m s t : ℕ) (hs : m < 3 + s) :
    backRow m s t ∈ AllM.candidateIdeal m := by
  exact (AllM.candidateIdeal m).sub_mem
    ((AllM.candidateIdeal m).mul_mem_left _
      (g0_closed m 0 5 (g0_closed m 0 4 (oppositeCubic_mem m s hs))))
    ((AllM.candidateIdeal m).mul_mem_left _ (g0_closed m 0 6 (oppositeCubic_mem m s hs)))

/-- The current degree of each tested quartic normal family starts at 2m-4.
Only actual whole coefficient membership is used in this theorem. -/
theorem normal_cubic_rows_mem {m : ℕ} (hm : 2 ≤ m) (t : ℕ) :
    frontRow m (2 * m - 4) t ∈ AllM.candidateIdeal m ∧
      middleRow m (2 * m - 4) t ∈ AllM.candidateIdeal m ∧
      backRow m (2 * m - 4) t ∈ AllM.candidateIdeal m := by
  have hs : m < 3 + (2 * m - 4) := by omega
  exact ⟨frontRow_mem m _ t hs, middleRow_mem m _ t hs, backRow_mem m _ t hs⟩

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.normal_cubic_rows_mem
