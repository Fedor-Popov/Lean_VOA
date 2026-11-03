import VOA.DeligneAudit.D4LeviFiniteBox

/-! Simple Levi raising replacements increase the total key order. -/

namespace VOA.DeligneAudit.D4Levi

/-- Remove one radical letter of colour `j`, insert one of colour `t`,
and increase the current degree by `r`. -/
def replaceKey (j t : Fin 6) (r : ℕ) (k : RadicalKey) : RadicalKey :=
  ⟨k.e - (if j = 0 then 1 else 0) + (if t = 0 then 1 else 0),
    k.x - (if j = 1 then 1 else 0) + (if t = 1 then 1 else 0),
    k.u - (if j = 2 then 1 else 0) + (if t = 2 then 1 else 0),
    k.up - (if j = 3 then 1 else 0) + (if t = 3 then 1 else 0),
    k.y - (if j = 4 then 1 else 0) + (if t = 4 then 1 else 0),
    k.z - (if j = 5 then 1 else 0) + (if t = 5 then 1 else 0),
    k.degree + r⟩

def keyCount (j : Fin 6) (k : RadicalKey) : ℕ :=
  if j = 0 then k.e else if j = 1 then k.x else if j = 2 then k.u else
    if j = 3 then k.up else if j = 4 then k.y else k.z

/-- A nonzero simple raising replacement moves strictly above its source key. -/
theorem raise_replace_higher (m : ℕ) (i : Fin 3) (j t : Fin 6)
    (n : ℤ) (r : ℕ) (k : RadicalKey)
    (h : raiseAction i j = some (t, n)) (hj : 0 < keyCount j k) :
    keyLess m k (replaceKey j t r k) := by
  fin_cases i <;> fin_cases j <;> simp [raiseAction] at h
  all_goals
    rcases h with ⟨rfl, rfl⟩
    rcases k with ⟨e, x, u, up, y, z, degree⟩
    simp [keyCount, replaceKey, keyLess, keyHeight] at hj ⊢ <;> omega

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.raise_replace_higher
