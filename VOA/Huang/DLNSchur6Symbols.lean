import VOA.Huang.DLNSchur5Relations

/-! # Additive-unit relations for the normalized rank-one symbols -/

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

include h3 hs hX hY hn

/-- Mixed-root rewriting with an arbitrary unit lower parameter. The two Weyl
words are retained, so no torus multiplicativity is assumed. -/
theorem upper_mul_lower_unit (s : ZMod n) (t v : (ZMod n)ˣ)
    (hv : (v : ZMod n) = 1 + s * (t : ZMod n)) :
    X (Multiplicative.ofAdd s) * Y (Multiplicative.ofAdd (t : ZMod n)) =
      Y (Multiplicative.ofAdd ((t : ZMod n) * (↑v⁻¹ : ZMod n))) *
        (weylWord X Y (v * t⁻¹) * (weylWord X Y t⁻¹)⁻¹) *
        X (Multiplicative.ofAdd (s * (↑v⁻¹ : ZMod n))) := by
  have hv' : (↑(v * t⁻¹) : ZMod n) = s + (↑t⁻¹ : ZMod n) := by
    simp only [Units.val_mul, hv, add_mul, one_mul]
    simp [mul_assoc, add_comm]
  have hw := weylWord_eq_lower_upper_lower h2 h3 π hs X Y hX hY hn (v * t⁻¹)
  have hx : X (Multiplicative.ofAdd (↑(v * t⁻¹) : ZMod n)) =
      Y (Multiplicative.ofAdd ((t : ZMod n) * (↑v⁻¹ : ZMod n))) *
        weylWord X Y (v * t⁻¹) *
        Y (Multiplicative.ofAdd ((t : ZMod n) * (↑v⁻¹ : ZMod n))) := by
    rw [hw]
    simp only [mul_inv_rev, inv_inv, Units.val_mul, rootHom_neg]
    group
  have hc := weylWord_lower_conj h2 h3 π hs X Y hX hY hn t⁻¹
    ((t : ZMod n) * (↑v⁻¹ : ZMod n))
  have he : -((↑t⁻¹ : ZMod n) ^ 2 * ((t : ZMod n) * (↑v⁻¹ : ZMod n))) =
      -((↑t⁻¹ : ZMod n) * (↑v⁻¹ : ZMod n)) := by
    simp [pow_two, mul_assoc]
  rw [he] at hc
  have ht : -((↑t⁻¹ : ZMod n) * (↑v⁻¹ : ZMod n)) + (↑t⁻¹ : ZMod n) =
      s * (↑v⁻¹ : ZMod n) := by
    have hm := Units.mul_inv v
    rw [hv] at hm
    have ht := Units.mul_inv t
    linear_combination -(↑t⁻¹ : ZMod n) * hm + s * (↑v⁻¹ : ZMod n) * ht
  calc
    _ = X (Multiplicative.ofAdd (↑(v * t⁻¹) : ZMod n)) *
        weylWord X Y (-t⁻¹) * X (Multiplicative.ofAdd (↑t⁻¹ : ZMod n)) := by
      rw [hv', rootHom_add]
      simp only [weylWord, Units.val_neg, inv_neg, inv_inv, neg_neg, rootHom_neg]
      group
    _ = Y (Multiplicative.ofAdd ((t : ZMod n) * (↑v⁻¹ : ZMod n))) *
        (weylWord X Y (v * t⁻¹) * (weylWord X Y t⁻¹)⁻¹) *
        (X (Multiplicative.ofAdd (-((↑t⁻¹ : ZMod n) * (↑v⁻¹ : ZMod n)))) *
          X (Multiplicative.ofAdd (↑t⁻¹ : ZMod n))) := by
      rw [hx, weylWord_neg, ← hc]
      group
    _ = _ := by rw [← rootHom_add, ht]

/-- The additive-unit Weyl relation, obtained by splitting the middle lower
root in `W(-1)` into parameters whose sum is one. -/
theorem weylWord_additive_unit (u v : (ZMod n)ˣ)
    (huv : (u : ZMod n) + (v : ZMod n) = 1) :
    weylWord X Y (v * u⁻¹) * (weylWord X Y u⁻¹)⁻¹ *
      (weylWord X Y v⁻¹)⁻¹ = (weylWord X Y 1)⁻¹ := by
  have hv : (v : ZMod n) = 1 + (-1) * (u : ZMod n) := by linear_combination huv
  have hm := upper_mul_lower_unit h2 h3 π hs X Y hX hY hn (-1) u v hv
  have he : (↑v⁻¹ : ZMod n) - 1 = (u : ZMod n) * (↑v⁻¹ : ZMod n) := by
    have hh := Units.mul_inv v
    linear_combination -(↑v⁻¹ : ZMod n) * huv + hh
  let q := weylWord X Y (v * u⁻¹) * (weylWord X Y u⁻¹)⁻¹ *
    (weylWord X Y v⁻¹)⁻¹
  have hq : π q = weyl (-1) := by
    simp only [q, map_mul, map_inv, map_weylWord π X Y hX hY]
    have he : (u : ZMod n) * ((v : ZMod n) * ((↑u⁻¹ : ZMod n) * (↑v⁻¹ : ZMod n))) = 1 := by
      calc
        _ = ((u : ZMod n) * (↑u⁻¹ : ZMod n)) * ((v : ZMod n) * (↑v⁻¹ : ZMod n)) := by ring
        _ = 1 := by simp
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [weyl, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, mul_comm, mul_left_comm, he]
  have hc := normalized_weyl_upper_conj h2 h3 π hs X Y hn q (-1) hq
    ((u : ZMod n) * (↑v⁻¹ : ZMod n))
  simp only [inv_neg, inv_one, Units.val_neg, Units.val_one, neg_sq, one_pow, one_mul,
    rootHom_neg] at hc
  have hw : (weylWord X Y 1)⁻¹ =
      Y (Multiplicative.ofAdd ((u : ZMod n) * (↑v⁻¹ : ZMod n))) * q *
        X (Multiplicative.ofAdd ((u : ZMod n) * (↑v⁻¹ : ZMod n))) := by
    calc
      _ = X (Multiplicative.ofAdd (-1 : ZMod n)) *
          Y (Multiplicative.ofAdd (u : ZMod n)) *
          Y (Multiplicative.ofAdd (v : ZMod n)) * X (Multiplicative.ofAdd (-1 : ZMod n)) := by
        rw [← weylWord_neg, weylWord]
        simp only [Units.val_neg, Units.val_one, inv_neg, inv_one, neg_neg]
        rw [← huv, rootHom_add]
        group
      _ = _ := by
        rw [hm]
        simp only [neg_one_mul]
        have hh : X (Multiplicative.ofAdd (-(↑v⁻¹ : ZMod n))) *
            Y (Multiplicative.ofAdd (v : ZMod n)) * X (Multiplicative.ofAdd (-1 : ZMod n)) =
            (weylWord X Y v⁻¹)⁻¹ *
              X (Multiplicative.ofAdd ((u : ZMod n) * (↑v⁻¹ : ZMod n))) := by
          rw [← weylWord_neg, weylWord, ← he]
          simp only [Units.val_neg, inv_neg, inv_inv, neg_neg, sub_eq_add_neg, rootHom_add,
            rootHom_neg]
          group
        dsimp only [q]
        calc
          _ = (Y (Multiplicative.ofAdd ((u : ZMod n) * (↑v⁻¹ : ZMod n))) *
              (weylWord X Y (v * u⁻¹) * (weylWord X Y u⁻¹)⁻¹)) *
              (X (Multiplicative.ofAdd (-(↑v⁻¹ : ZMod n))) *
                Y (Multiplicative.ofAdd (v : ZMod n)) *
                X (Multiplicative.ofAdd (-1 : ZMod n))) := by group
          _ = _ := by rw [hh]; group
  change q = _
  rw [hw]
  symm
  calc
    _ = Y (Multiplicative.ofAdd ((u : ZMod n) * (↑v⁻¹ : ZMod n))) *
        (q * X (Multiplicative.ofAdd ((u : ZMod n) * (↑v⁻¹ : ZMod n))) * q⁻¹) * q := by group
    _ = _ := by rw [hc]; group

/-- The rank-one Steinberg relation for two units whose sum is one. -/
theorem torusDefect_add_eq_one [IsCyclic (ZMod n)ˣ]
    (hc : π.ker ≤ Subgroup.center E) (u v : (ZMod n)ˣ)
    (huv : (u : ZMod n) + (v : ZMod n) = 1) :
    torusDefect X Y u v = 1 := by
  have hw := weylWord_additive_unit h2 h3 π hs X Y hX hY hn u v huv
  have hj := weylWord_conj_weylWord h2 h3 π hs X Y hX hY hn (-1) v⁻¹
  simp only [neg_one_sq, inv_inv, one_mul, weylWord_neg] at hj
  have he : torusWord X Y v * torusWord X Y u⁻¹ = torusWord X Y (v * u⁻¹) := by
    have hh : weylWord X Y (v * u⁻¹) * (weylWord X Y u⁻¹)⁻¹ =
        (weylWord X Y 1)⁻¹ * weylWord X Y v⁻¹ := by
      calc
        _ = (weylWord X Y (v * u⁻¹) * (weylWord X Y u⁻¹)⁻¹ *
            (weylWord X Y v⁻¹)⁻¹) * weylWord X Y v⁻¹ := by group
        _ = _ := by rw [hw]
    have hh' : (weylWord X Y 1)⁻¹ * weylWord X Y v⁻¹ =
        weylWord X Y v * (weylWord X Y 1)⁻¹ := by rw [← hj]; group
    rw [hh'] at hh
    unfold torusWord
    rw [← hh]
    group
  have hz : torusDefect X Y v u⁻¹ = 1 := by
    rw [torusDefect, he, mul_inv_cancel]
  have hh := torusDefect_mul_squares h2 h3 π hs X Y hX hY hn hc 1 u⁻¹ v u
  have hu : (u⁻¹) ^ 2 * u = u⁻¹ := by group
  simp only [one_pow, one_mul, hu] at hh
  rw [hh, torusDefect_symm π hs X Y hX hY hc] at hz
  exact hz

/-- A nonsquare pair represents the remaining generator self-defect. -/
theorem torusDefect_eq_generator_of_nonsquares [IsCyclic (ZMod n)ˣ]
    (hc : π.ker ≤ Subgroup.center E) (w : (ZMod n)ˣ)
    (hw : ∀ t : (ZMod n)ˣ, t ∈ Submonoid.powers w)
    (u v : (ZMod n)ˣ) (hu : ¬ ∃ a, a ^ 2 = u) (hv : ¬ ∃ a, a ^ 2 = v) :
    torusDefect X Y u v = torusDefect X Y w w := by
  obtain ⟨i, rfl⟩ := hw u
  obtain ⟨j, rfl⟩ := hw v
  have hi : i % 2 = 1 := by
    by_contra h
    have he : i / 2 * 2 = i := by omega
    exact hu ⟨w ^ (i / 2), by rw [← pow_mul, he]⟩
  have hj : j % 2 = 1 := by
    by_contra h
    have he : j / 2 * 2 = j := by omega
    exact hv ⟨w ^ (j / 2), by rw [← pow_mul, he]⟩
  have hi' : w ^ i = (w ^ (i / 2)) ^ 2 * w := by
    rw [← pow_mul, ← pow_succ]; congr 1; omega
  have hj' : w ^ j = (w ^ (j / 2)) ^ 2 * w := by
    rw [← pow_mul, ← pow_succ]; congr 1; omega
  dsimp only
  rw [hi', hj', torusDefect_mul_squares h2 h3 π hs X Y hX hY hn hc]

end Normalized
end VOA.Huang.DLNSchur
