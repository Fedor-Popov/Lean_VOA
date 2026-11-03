import VOA.Huang.DLNSchur6Charts

/-! # The local-ring chart transitions

Left multiplication is convenient: an upper root preserves the lower pivot,
and a lower root preserves the upper pivot. Chart compatibility handles the
overlap; the remaining pivot is one plus a nonunit.
-/

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

theorem gaussLift_upper_one_mul_top (r t : ZMod n) (u v : (ZMod n)ˣ)
    (hv : (v : ZMod n) = 1 + r) :
    gaussLift X Y (upperRoot 1 * (lowerRoot r * torus u * upperRoot t)) =
      X (Multiplicative.ofAdd 1) *
        gaussLift X Y (lowerRoot r * torus u * upperRoot t) := by
  have hm := upper_unit_mul_lower_of_defect_eq_one h2 h3 π hs X Y hX hY hn hz
    1 v r (by simpa using hv)
  simp only [Units.val_one, one_mul] at hm
  have hc := torusWord_upper_conj h2 h3 π hs X Y hX hY hn u
    ((↑u⁻¹ : ZMod n) ^ 2 * (↑v⁻¹ : ZMod n))
  have he : (u : ZMod n) ^ 2 * ((↑u⁻¹ : ZMod n) ^ 2 * (↑v⁻¹ : ZMod n)) =
      (↑v⁻¹ : ZMod n) := by simp [pow_two, mul_assoc]
  rw [he] at hc
  have hw : X (Multiplicative.ofAdd 1) *
      (Y (Multiplicative.ofAdd r) * torusWord X Y u * X (Multiplicative.ofAdd t)) =
      Y (Multiplicative.ofAdd (r * (↑v⁻¹ : ZMod n))) * torusWord X Y (v * u) *
        X (Multiplicative.ofAdd ((↑u⁻¹ : ZMod n) ^ 2 * (↑v⁻¹ : ZMod n) + t)) := by
    calc
      _ = (X (Multiplicative.ofAdd 1) * Y (Multiplicative.ofAdd r)) *
          torusWord X Y u * X (Multiplicative.ofAdd t) := by group
      _ = _ := by
        rw [hm, ← hc, rootHom_add, ← torusWord_mul_of_defect_eq_one X Y hz]
        group
  have hg := congrArg π hw
  simp only [map_mul, hX, hY, toAdd_ofAdd, map_torusWord π X Y hX hY] at hg
  rw [hg, gaussLift_lower_torus_upper, gaussLift_lower_torus_upper]
  exact hw.symm

theorem gaussLift_lower_one_mul_bottom (r t : ZMod n) (u v : (ZMod n)ˣ)
    (hv : (v : ZMod n) = 1 + r) :
    gaussLift X Y (lowerRoot 1 * (upperRoot r * weyl u * upperRoot t)) =
      Y (Multiplicative.ofAdd 1) *
        gaussLift X Y (upperRoot r * weyl u * upperRoot t) := by
  have hm := lower_one_mul_upper_of_defect_eq_one h2 h3 π hs X Y hX hY hn hz r v hv
  have hc := weylWord_lower_conj h2 h3 π hs X Y hX hY hn (-u) (↑v⁻¹ : ZMod n)
  simp only [weylWord_neg, inv_inv, Units.val_neg, neg_sq] at hc
  have hw : Y (Multiplicative.ofAdd 1) *
      (X (Multiplicative.ofAdd r) * weylWord X Y u * X (Multiplicative.ofAdd t)) =
      X (Multiplicative.ofAdd (r * (↑v⁻¹ : ZMod n))) * weylWord X Y (v⁻¹ * u) *
        X (Multiplicative.ofAdd (-((u : ZMod n) ^ 2 * (↑v⁻¹ : ZMod n)) + t)) := by
    calc
      _ = (Y (Multiplicative.ofAdd 1) * X (Multiplicative.ofAdd r)) *
          weylWord X Y u * X (Multiplicative.ofAdd t) := by group
      _ = _ := by
        rw [hm, rootHom_add, ← hc, ← torusWord_mul_weylWord_of_defect_eq_one X Y hz]
        group
  have hg := congrArg π hw
  simp only [map_mul, hX, hY, toAdd_ofAdd, map_weylWord π X Y hX hY] at hg
  rw [hg, gaussLift_upper_weyl_upper h2 h3 π hs X Y hX hY hn hz,
    gaussLift_upper_weyl_upper h2 h3 π hs X Y hX hY hn hz]
  exact hw.symm

/-- Left upper covariance uses the lower chart whenever that pivot is a unit. -/
theorem gaussLift_upper_one_mul_of_local
    (hloc : ∀ r : ZMod n, ¬ IsUnit r → IsUnit (1 + r))
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (hg : IsUnit (g 0 0) ∨ IsUnit (g 1 0)) :
    gaussLift X Y (upperRoot 1 * g) = X (Multiplicative.ofAdd 1) * gaussLift X Y g := by
  by_cases hc : IsUnit (g 1 0)
  · have he := gauss_of_unit_lower_left g hc.unit (IsUnit.unit_spec hc).symm
    rw [he]
    have hm : upperRoot (1 : ZMod n) *
        (upperRoot (g 0 0 * (↑hc.unit⁻¹ : ZMod n)) * weyl (-hc.unit⁻¹) *
          upperRoot (g 1 1 * (↑hc.unit⁻¹ : ZMod n))) =
        upperRoot (1 + g 0 0 * (↑hc.unit⁻¹ : ZMod n)) * weyl (-hc.unit⁻¹) *
          upperRoot (g 1 1 * (↑hc.unit⁻¹ : ZMod n)) := by rw [upperRoot_add]; group
    rw [hm, gaussLift_upper_weyl_upper h2 h3 π hs X Y hX hY hn hz,
      gaussLift_upper_weyl_upper h2 h3 π hs X Y hX hY hn hz, rootHom_add]
    group
  · have ha := hg.resolve_right hc
    have hr : ¬ IsUnit (g 1 0 * (↑ha.unit⁻¹ : ZMod n)) :=
      fun h => hc (isUnit_of_mul_isUnit_left h)
    have hv := hloc _ hr
    have he := gauss_of_unit_top_left g ha.unit (IsUnit.unit_spec ha).symm
    rw [he]
    exact gaussLift_upper_one_mul_top h2 h3 π hs X Y hX hY hn hz _ _ ha.unit hv.unit
      (IsUnit.unit_spec hv)

/-- Left lower covariance uses the upper chart whenever that pivot is a unit. -/
theorem gaussLift_lower_one_mul_of_local
    (hloc : ∀ r : ZMod n, ¬ IsUnit r → IsUnit (1 + r))
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
    (hg : IsUnit (g 0 0) ∨ IsUnit (g 1 0)) :
    gaussLift X Y (lowerRoot 1 * g) = Y (Multiplicative.ofAdd 1) * gaussLift X Y g := by
  by_cases ha : IsUnit (g 0 0)
  · have he := gauss_of_unit_top_left g ha.unit (IsUnit.unit_spec ha).symm
    rw [he]
    have hm : lowerRoot (1 : ZMod n) *
        (lowerRoot (g 1 0 * (↑ha.unit⁻¹ : ZMod n)) * torus ha.unit *
          upperRoot (g 0 1 * (↑ha.unit⁻¹ : ZMod n))) =
        lowerRoot (1 + g 1 0 * (↑ha.unit⁻¹ : ZMod n)) * torus ha.unit *
          upperRoot (g 0 1 * (↑ha.unit⁻¹ : ZMod n)) := by rw [lowerRoot_add]; group
    rw [hm, gaussLift_lower_torus_upper, gaussLift_lower_torus_upper, rootHom_add]
    group
  · have hc := hg.resolve_left ha
    have hr : ¬ IsUnit (g 0 0 * (↑hc.unit⁻¹ : ZMod n)) :=
      fun h => ha (isUnit_of_mul_isUnit_left h)
    have hv := hloc _ hr
    have he := gauss_of_unit_lower_left g hc.unit (IsUnit.unit_spec hc).symm
    rw [he]
    exact gaussLift_lower_one_mul_bottom h2 h3 π hs X Y hX hY hn hz _ _ (-hc.unit⁻¹)
      hv.unit (IsUnit.unit_spec hv)

end Normalized

/-- The elementary local-ring fact needed by the chart calculation. -/
theorem isUnit_one_add_of_nonunit_primePower {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (r : ZMod (p ^ k)) (hr : ¬ IsUnit r) : IsUnit (1 + r) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [isUnit_iff_reduction_ne_zero hp hk] at hr ⊢
  have hz := not_not.mp hr
  simp only [map_add, map_one, hz, add_zero, ne_eq, one_ne_zero, not_false_eq_true]

/-- Multiplicativity can equally be checked by left transitions on generators. -/
theorem map_mul_of_left_transitions {G E : Type*} [Group G] [Group E]
    (f : G → E) (hf : f 1 = 1) (S : Set G) (hS : Subgroup.closure S = ⊤)
    (hstep : ∀ s ∈ S, ∀ g, f (s * g) = f s * f g) :
    ∀ g h, f (g * h) = f g * f h := by
  intro g h
  have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
  have hall : ∀ x, f (g * x) = f g * f x := by
    induction hg using Subgroup.closure_induction with
    | mem y hy => exact hstep y hy
    | one => intro x; simp [hf]
    | mul y z _ _ hy hz =>
      intro x
      rw [mul_assoc, hy, hz, hy, mul_assoc]
    | inv y _ hy =>
      intro x
      have hinv : f y * f y⁻¹ = 1 := by simpa [hf] using (hy y⁻¹).symm
      apply mul_left_cancel (a := f y)
      calc
        f y * f (y⁻¹ * x) = f (y * (y⁻¹ * x)) := (hy _).symm
        _ = f x := by simp
        _ = f y * (f y⁻¹ * f x) := by rw [← mul_assoc, hinv, one_mul]
  exact hall h

/-- Vanishing torus defects suffice for every prime-power chart transition. -/
theorem gaussLift_mul_primePower_of_defect_eq_one {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) (h2 : Nat.Coprime 2 (p ^ k)) (h3 : Nat.Coprime 3 (p ^ k))
    {E : Type*} [Group E]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k)))
    (hs : Function.Surjective π) (X Y : Multiplicative (ZMod (p ^ k)) →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
    (hn : RootNormalization h2 π X Y)
    (hz : ∀ u v : (ZMod (p ^ k))ˣ, torusDefect X Y u v = 1) :
    ∀ g h, gaussLift X Y (g * h) = gaussLift X Y g * gaussLift X Y h := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hu := fun g => gaussLift_upper_one_mul_of_local h2 h3 π hs X Y hX hY hn hz
    (isUnit_one_add_of_nonunit_primePower hp hk) g (first_column_unit_primePower hp hk g)
  have hl := fun g => gaussLift_lower_one_mul_of_local h2 h3 π hs X Y hX hY hn hz
    (isUnit_one_add_of_nonunit_primePower hp hk) g (first_column_unit_primePower hp hk g)
  apply map_mul_of_left_transitions _ (gaussLift_one X Y)
    {upperRoot 1, lowerRoot 1} (root_generators _)
  intro s hs g
  rcases hs with rfl | rfl
  · have he := hu 1
    simp only [mul_one, gaussLift_one] at he
    rw [he]; exact hu g
  · have he := hl 1
    simp only [mul_one, gaussLift_one] at he
    rw [he]; exact hl g

end VOA.Huang.DLNSchur
