import VOA.DeligneAudit.D4LeviKSSymmetricWordShift

/-! Key-height control for every partial f₃ PAIR transfer. -/

namespace VOA.DeligneAudit.D4Levi

/-- The symmetric target key after all `b` U letters have become Y. -/
def pairFinalKey (a b c d : ℕ) : RadicalKey :=
  ⟨0, a + b, 0, 0, b, c, d⟩

/-- An intermediate key after `nx` X-to-U' and `ny` U-to-Y
    substitutions in an f₃ derivative. -/
def pairPartialKey (a b c d nx ny : ℕ) : RadicalKey :=
  ⟨0, a + b - nx, b - ny, nx, ny, c, d⟩

/-- Every derivative source with fewer than `b` substitutions has strictly
    greater Levi height than the final PAIR key, regardless of their split. -/
theorem pairPartialKey_higher (m a b c d nx ny : ℕ)
    (hnx : nx ≤ a + b) (hstep : nx + ny < b) :
    keyLess m (pairFinalKey a b c d)
      (pairPartialKey a b c d nx ny) := by
  left
  simp only [pairFinalKey, pairPartialKey, keyHeight]
  omega

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairPartialKey_higher
