import VOA.DeligneAudit.D4LeviKSBoxCountCore
import VOA.DeligneAudit.D4LeviKSPairHeight

/-! The numerical box count attached to an actual D4 radical key. -/

namespace VOA.DeligneAudit.D4Levi

/-- The graded box count is supported on symmetric XYZ keys of depth at most `m`. -/
noncomputable def ksBoxCount (m : ℕ) (k : RadicalKey) : ℕ :=
  if k.e = 0 ∧ k.u = 0 ∧ k.up = 0 ∧ k.y ≤ k.x ∧
      k.x + k.z ≤ m ∧ k.x - k.y ≤ m - k.x - k.z then
    ksGradedBoxCount m (k.x - k.y) k.y k.z k.degree
  else 0

theorem ksBoxCount_pairFinalKey (m a b c d : ℕ)
    (h : a + b + c ≤ m) (ha : a ≤ m - (a + b) - c) :
    ksBoxCount m (pairFinalKey a b c d) = ksGradedBoxCount m a b c d := by
  have hab : a + b - b = a := by omega
  simp [ksBoxCount, pairFinalKey, h, ha, hab, show b ≤ a + b by omega]

theorem ksBoxTriples_card_of_composition (a bp b c : ℕ) :
    (ksBoxTriples (a + bp + b + c) a b c).card =
      Nat.multinomial (Finset.univ : Finset (Fin 4)) ![a, bp, b, c] := by
  have h1 : a + bp + b + c - c - b = a + bp := by omega
  have h2 : a + bp + b + c - c = a + bp + b := by omega
  rw [ksBoxTriples_card (ha := by omega) (hb := by omega) (hc := by omega)]
  rw [ksMultinomial_choose, h1, h2]
  ring

theorem keyOrbitLength_pairFinalKey (a bp b c d : ℕ) :
    keyOrbitLength (a + bp + b + c) (pairFinalKey a b c d) =
      16 ^ a * 6 ^ (bp + b) := by
  let m := a + bp + b + c
  have hneg : ¬ ∃ i : Fin 3, keyLabel m i (pairFinalKey a b c d) < 0 := by
    rintro ⟨i, hi⟩
    fin_cases i <;> simp [keyLabel, pairFinalKey, m] at hi <;> omega
  unfold keyOrbitLength
  split_ifs with hcase
  · exact False.elim (hneg hcase)
  have h0 : keyWeight m (pairFinalKey a b c d) 0 = a := by
    simp [keyWeight, keyLabel, pairFinalKey]
  have h1 : keyWeight m (pairFinalKey a b c d) 1 = bp + b := by
    simp [keyWeight, keyLabel, pairFinalKey, m]
    omega
  have h2 : keyWeight m (pairFinalKey a b c d) 2 = a := by
    simp [keyWeight, keyLabel, pairFinalKey]
  rw [h0, h1, h2]
  calc
    4 ^ a * 6 ^ (bp + b) * 4 ^ a =
        (4 ^ a * 4 ^ a) * 6 ^ (bp + b) := by ac_rfl
    _ = 16 ^ a * 6 ^ (bp + b) := by rw [← mul_pow]; norm_num

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksBoxCount_pairFinalKey
#print axioms VOA.DeligneAudit.D4Levi.ksBoxTriples_card_of_composition
#print axioms VOA.DeligneAudit.D4Levi.keyOrbitLength_pairFinalKey
