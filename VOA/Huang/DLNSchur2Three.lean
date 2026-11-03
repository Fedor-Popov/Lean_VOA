import VOA.Huang.DLNSchur2Lifts

/-! # The obstruction to the invertible square-character argument at three

A square character can differ from one modulo nine, but its difference is never a unit
modulo any positive power of three. Consequently the correction used away from six
cannot be repeated there by merely choosing another diagonal unit.
-/

namespace VOA.Huang.DLNSchur

/-- Every unit modulo three has square one; this finite check is kernel evaluated. -/
theorem unit_sq_three (u : (ZMod 3)ˣ) : (u : ZMod 3) ^ 2 = 1 := by
  revert u
  decide

/-- No diagonal square-character difference is invertible modulo a positive power of three. -/
theorem not_isUnit_sq_sub_one_threePower {k : ℕ} (hk : 0 < k)
    (u : (ZMod (3 ^ k))ˣ) : ¬ IsUnit ((u : ZMod (3 ^ k)) ^ 2 - 1) := by
  let f : ZMod (3 ^ k) →+* ZMod 3 := ZMod.castHom (dvd_pow_self 3 hk.ne') _
  have hu : f (u : ZMod (3 ^ k)) ^ 2 = 1 :=
    unit_sq_three (Units.map f.toMonoidHom u)
  intro h
  have h' := h.map f
  rw [map_sub, map_pow, map_one, hu, sub_self] at h'
  exact not_isUnit_zero h'

end VOA.Huang.DLNSchur
