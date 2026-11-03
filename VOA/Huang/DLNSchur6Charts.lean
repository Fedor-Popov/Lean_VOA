import VOA.Huang.DLNSchur6Torus

/-! # Chart compatibility after torus-defect vanishing -/

namespace VOA.Huang.DLNSchur

section Normalized
variable {n : ℕ} {E : Type*} [Group E]
variable (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
variable (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
variable (hs : Function.Surjective π)
variable (X Y : Multiplicative (ZMod n) →* E)
variable (hX : ∀ t, π (X t) = upperRoot t.toAdd)
variable (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
variable (hn : RootNormalization h2 π X Y)
variable (hz : ∀ u v : (ZMod n)ˣ, torusDefect X Y u v = 1)

include h3 hs hX hY hn hz

theorem weylWord_mul_of_defect_eq_one (u v : (ZMod n)ˣ) :
    weylWord X Y u * weylWord X Y v = torusWord X Y (-(u * v⁻¹)) := by
  have hc := weylWord_conj_weylWord h2 h3 π hs X Y hX hY hn 1 v
  simp only [one_pow, one_mul] at hc
  calc
    _ = torusWord X Y u *
        (weylWord X Y 1 * weylWord X Y v * (weylWord X Y 1)⁻¹) *
        weylWord X Y 1 := by unfold torusWord; group
    _ = _ := by
      rw [hc, mul_assoc, weylWord_mul_one_of_defect_eq_one X Y hz,
        torusWord_mul_of_defect_eq_one X Y hz]
      simp

omit h3 hs hX hY hn in
theorem torusWord_mul_weylWord_of_defect_eq_one (u v : (ZMod n)ˣ) :
    torusWord X Y u * weylWord X Y v = weylWord X Y (u * v) := by
  calc
    _ = (torusWord X Y u * torusWord X Y v) * weylWord X Y 1 := by
      unfold torusWord; group
    _ = _ := by rw [torusWord_mul_of_defect_eq_one X Y hz]; unfold torusWord; group

omit h3 hs hX hY hn in
theorem weylWord_div_of_defect_eq_one (u v : (ZMod n)ˣ) :
    weylWord X Y (u * v) * (weylWord X Y v)⁻¹ = torusWord X Y u := by
  rw [← torusWord_mul_weylWord_of_defect_eq_one X Y hz]
  group

theorem upper_mul_lower_unit_of_defect_eq_one (s : ZMod n) (t v : (ZMod n)ˣ)
    (hv : (v : ZMod n) = 1 + s * (t : ZMod n)) :
    X (Multiplicative.ofAdd s) * Y (Multiplicative.ofAdd (t : ZMod n)) =
      Y (Multiplicative.ofAdd ((t : ZMod n) * (↑v⁻¹ : ZMod n))) *
        torusWord X Y v * X (Multiplicative.ofAdd (s * (↑v⁻¹ : ZMod n))) := by
  rw [upper_mul_lower_unit h2 h3 π hs X Y hX hY hn s t v hv,
    weylWord_div_of_defect_eq_one X Y hz]

/-- The other mixed-root rewrite only requires the upper parameter to be a unit. -/
theorem upper_unit_mul_lower_of_defect_eq_one (s v : (ZMod n)ˣ) (t : ZMod n)
    (hv : (v : ZMod n) = 1 + (s : ZMod n) * t) :
    X (Multiplicative.ofAdd (s : ZMod n)) * Y (Multiplicative.ofAdd t) =
      Y (Multiplicative.ofAdd (t * (↑v⁻¹ : ZMod n))) *
        torusWord X Y v * X (Multiplicative.ofAdd ((s : ZMod n) * (↑v⁻¹ : ZMod n))) := by
  have hw := weylWord_eq_lower_upper_lower h2 h3 π hs X Y hX hY hn s
  have hx : X (Multiplicative.ofAdd (s : ZMod n)) =
      Y (Multiplicative.ofAdd (↑s⁻¹ : ZMod n)) * weylWord X Y s *
        Y (Multiplicative.ofAdd (↑s⁻¹ : ZMod n)) := by
    rw [hw, rootHom_neg]; group
  have he : (↑s⁻¹ : ZMod n) + t = (↑(v * s⁻¹) : ZMod n) := by
    simp only [Units.val_mul, hv, add_mul, one_mul]
    simp [mul_assoc, mul_comm]
  have hy : Y (Multiplicative.ofAdd (↑(v * s⁻¹) : ZMod n)) =
      X (Multiplicative.ofAdd ((s : ZMod n) * (↑v⁻¹ : ZMod n))) *
        weylWord X Y (-(s * v⁻¹)) *
        X (Multiplicative.ofAdd ((s : ZMod n) * (↑v⁻¹ : ZMod n))) := by
    simp only [weylWord, Units.val_neg, Units.val_mul, inv_neg, mul_inv_rev, inv_inv,
      neg_neg, rootHom_neg]
    group
  have hc := weylWord_upper_conj h2 h3 π hs X Y hX hY hn s
    ((s : ZMod n) * (↑v⁻¹ : ZMod n))
  have hc' : -((↑s⁻¹ : ZMod n) ^ 2 * ((s : ZMod n) * (↑v⁻¹ : ZMod n))) =
      -((↑s⁻¹ : ZMod n) * (↑v⁻¹ : ZMod n)) := by simp [pow_two, mul_assoc]
  rw [hc'] at hc
  have ht : (↑s⁻¹ : ZMod n) + -((↑s⁻¹ : ZMod n) * (↑v⁻¹ : ZMod n)) =
      t * (↑v⁻¹ : ZMod n) := by
    have hm := Units.mul_inv v
    rw [hv] at hm
    linear_combination -(↑s⁻¹ : ZMod n) * hm +
      t * (↑v⁻¹ : ZMod n) * Units.mul_inv s
  have hu : -(s * (-(s * v⁻¹))⁻¹) = v := by simp
  calc
    _ = Y (Multiplicative.ofAdd (↑s⁻¹ : ZMod n)) * weylWord X Y s *
        Y (Multiplicative.ofAdd (↑(v * s⁻¹) : ZMod n)) := by
      rw [hx, mul_assoc (Y _ * weylWord X Y s), ← rootHom_add, he]
    _ = Y (Multiplicative.ofAdd (↑s⁻¹ : ZMod n)) *
        Y (Multiplicative.ofAdd (-((↑s⁻¹ : ZMod n) * (↑v⁻¹ : ZMod n)))) *
        (weylWord X Y s * weylWord X Y (-(s * v⁻¹))) *
        X (Multiplicative.ofAdd ((s : ZMod n) * (↑v⁻¹ : ZMod n))) := by
      rw [hy, ← hc]; group
    _ = _ := by
      rw [← rootHom_add, ht, weylWord_mul_of_defect_eq_one h2 h3 π hs X Y hX hY hn hz, hu]

/-- The reversed mixed-root rewrite, with lower parameter one. -/
theorem lower_one_mul_upper_of_defect_eq_one (s : ZMod n) (v : (ZMod n)ˣ)
    (hv : (v : ZMod n) = 1 + s) :
    Y (Multiplicative.ofAdd 1) * X (Multiplicative.ofAdd s) =
      X (Multiplicative.ofAdd (s * (↑v⁻¹ : ZMod n))) *
        torusWord X Y v⁻¹ * Y (Multiplicative.ofAdd (↑v⁻¹ : ZMod n)) := by
  have hm := upper_mul_lower_unit_of_defect_eq_one h2 h3 π hs X Y hX hY hn hz
    (-s) (-1) v (by simpa using hv)
  have ht : (torusWord X Y v)⁻¹ = torusWord X Y v⁻¹ := by
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [torusWord_mul_of_defect_eq_one X Y hz, mul_inv_cancel, torusWord_one]
  have hi := congrArg Inv.inv hm
  simpa [mul_inv_rev, rootHom_neg, ht, mul_assoc] using hi

/-- Compatibility of the lower-pivot word with the upper-pivot word on their overlap. -/
theorem upper_unit_mul_weylWord (r u : (ZMod n)ˣ) (t : ZMod n) :
    X (Multiplicative.ofAdd (r : ZMod n)) * weylWord X Y u * X (Multiplicative.ofAdd t) =
      Y (Multiplicative.ofAdd (↑r⁻¹ : ZMod n)) * torusWord X Y (-(r * u⁻¹)) *
        X (Multiplicative.ofAdd (t - (u : ZMod n) ^ 2 * (↑r⁻¹ : ZMod n))) := by
  have hw := weylWord_eq_lower_upper_lower h2 h3 π hs X Y hX hY hn r
  have hx : X (Multiplicative.ofAdd (r : ZMod n)) =
      Y (Multiplicative.ofAdd (↑r⁻¹ : ZMod n)) * weylWord X Y r *
        Y (Multiplicative.ofAdd (↑r⁻¹ : ZMod n)) := by
    rw [hw, rootHom_neg]; group
  have hc := weylWord_lower_conj h2 h3 π hs X Y hX hY hn (-u) (↑r⁻¹ : ZMod n)
  simp only [weylWord_neg, inv_inv, Units.val_neg, neg_sq] at hc
  calc
    _ = Y (Multiplicative.ofAdd (↑r⁻¹ : ZMod n)) *
        (weylWord X Y r * weylWord X Y u) *
        (X (Multiplicative.ofAdd (-((u : ZMod n) ^ 2 * (↑r⁻¹ : ZMod n)))) *
          X (Multiplicative.ofAdd t)) := by rw [hx, ← hc]; group
    _ = _ := by
      rw [weylWord_mul_of_defect_eq_one h2 h3 π hs X Y hX hY hn hz, ← rootHom_add]
      simp only [sub_eq_add_neg, add_comm]

/-- The lower-pivot expression evaluates correctly even when the upper pivot is also a unit. -/
theorem gaussLift_upper_weyl_upper (r t : ZMod n) (u : (ZMod n)ˣ) :
    gaussLift X Y (upperRoot r * weyl u * upperRoot t) =
      X (Multiplicative.ofAdd r) * weylWord X Y u * X (Multiplicative.ofAdd t) := by
  classical
  by_cases hr : IsUnit r
  · have he := upper_unit_mul_weylWord h2 h3 π hs X Y hX hY hn hz hr.unit u t
    have hm := congrArg π he
    simp only [map_mul, hX, hY, toAdd_ofAdd, map_torusWord π X Y hX hY,
      map_weylWord π X Y hX hY, IsUnit.unit_spec] at hm
    rw [hm, gaussLift_lower_torus_upper]
    simpa only [IsUnit.unit_spec] using he.symm
  · have h00 : (upperRoot r * weyl u * upperRoot t) 0 0 = r * (-u⁻¹ : (ZMod n)ˣ) := by
      simp [upperRoot, weyl, Matrix.mul_apply, Fin.sum_univ_two]
    have h10 : (upperRoot r * weyl u * upperRoot t) 1 0 = (-u⁻¹ : (ZMod n)ˣ) := by
      simp [upperRoot, weyl, Matrix.mul_apply, Fin.sum_univ_two]
    have ha : ¬ IsUnit ((upperRoot r * weyl u * upperRoot t) 0 0) := by
      rw [h00]; exact fun h => hr (isUnit_of_mul_isUnit_left h)
    have hb : IsUnit ((upperRoot r * weyl u * upperRoot t) 1 0) := h10 ▸ (-u⁻¹).isUnit
    have he : hb.unit = -u⁻¹ := Units.ext ((IsUnit.unit_spec hb).trans h10)
    simp only [gaussLift, dif_neg ha, dif_pos hb, he]
    simp [upperRoot, weyl, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, mul_comm,
      mul_left_comm]

end Normalized
end VOA.Huang.DLNSchur
