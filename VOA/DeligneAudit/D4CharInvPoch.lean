import VOA.DeligneAudit.D4CharQDifference

/-! Integer reciprocal Pochhammer identities, including the zero boundary. -/

namespace VOA.DeligneAudit.D4Char

noncomputable section

variable {R : Type*} [CommRing R]

@[simp] theorem gtInvPoch_nat (q : R) (h : PochhammerUnits q) (n : ℕ) :
    gtInvPoch q h (n : ℤ) = ((gtPochUnit q h n)⁻¹ : Rˣ) := by
  simp [gtInvPoch]

@[simp] theorem gtInvPoch_zero (q : R) (h : PochhammerUnits q) :
    gtInvPoch q h 0 = 1 := by
  simp [gtInvPoch]

theorem gtInvPoch_of_neg (q : R) (h : PochhammerUnits q) {d : ℤ} (hd : d < 0) :
    gtInvPoch q h d = 0 := if_neg (not_le.mpr hd)

theorem gtPoch_mul_invPoch (q : R) (h : PochhammerUnits q) (n : ℕ) :
    CarrierChain.qpochGen q n * gtInvPoch q h n = 1 := by
  rw [gtInvPoch_nat, ← gtPochUnit_val q h n]
  exact Units.mul_inv _

/-- The scalar recurrence, with the factors kept in the integral coefficient ring. -/
theorem gtInvPoch_succ (q : R) (h : PochhammerUnits q) (n : ℕ) :
    gtInvPoch q h n = (1 - q ^ (n + 1)) * gtInvPoch q h (n + 1) := by
  apply (h (n + 1)).mul_left_cancel
  calc
    _ = (CarrierChain.qpochGen q n * gtInvPoch q h n) * (1 - q ^ (n + 1)) := by
      rw [CarrierChain.qpochGen_succ]
      ring
    _ = 1 - q ^ (n + 1) := by rw [gtPoch_mul_invPoch, one_mul]
    _ = _ := by
      have hn : CarrierChain.qpochGen q (n + 1) * gtInvPoch q h (n + 1) = 1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using gtPoch_mul_invPoch q h (n + 1)
      rw [mul_left_comm, hn, mul_one]

/-- Integer lowering, valid also at d = 0 and on the entire negative half-line. -/
theorem gtInvPoch_lower (q : R) (h : PochhammerUnits q) (d : ℤ) :
    gtInvPoch q h (d - 1) = (1 - q ^ d.toNat) * gtInvPoch q h d := by
  by_cases hd : 0 < d
  · have he : d = ((d - 1).toNat : ℤ) + 1 := by omega
    have hn : d.toNat = (d - 1).toNat + 1 := by omega
    have hl : d - 1 = ((d - 1).toNat : ℤ) := by omega
    calc
      _ = gtInvPoch q h ((d - 1).toNat : ℤ) := congrArg (gtInvPoch q h) hl
      _ = (1 - q ^ ((d - 1).toNat + 1)) *
          gtInvPoch q h (((d - 1).toNat : ℤ) + 1) := gtInvPoch_succ q h _
      _ = _ := by rw [← he, ← hn]
  · rw [gtInvPoch_of_neg q h (by omega), Int.toNat_of_nonpos (by omega)]
    simp

/-- The equivalent raising equation needs no nonnegativity hypothesis. -/
theorem gtInvPoch_raise (q : R) (h : PochhammerUnits q) (d : ℤ) :
    (1 - q ^ (d + 1).toNat) * gtInvPoch q h (d + 1) = gtInvPoch q h d := by
  simpa using (gtInvPoch_lower q h (d + 1)).symm

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtPoch_mul_invPoch
#print axioms VOA.DeligneAudit.D4Char.gtInvPoch_succ
#print axioms VOA.DeligneAudit.D4Char.gtInvPoch_lower
#print axioms VOA.DeligneAudit.D4Char.gtInvPoch_raise
