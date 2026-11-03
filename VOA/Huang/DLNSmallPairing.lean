import VOA.Huang.DLNSmallAverage

/-!
# The commutator pairing of lifts in a central extension

For a central extension `π : E ↠ G` and commuting `a b : G`, the commutator of lifts
`⁅â, b̂⁆` is independent of the lifts and central. On commuting pairs it is bimultiplicative
and invariant under simultaneous conjugation. This file records these facts for the chosen
section `Function.surjInv`.
-/

namespace VOA.Huang.DLNSchur

open scoped commutatorElement

section Pairing

variable {G E : Type*} [Group G] [Group E] (π : E →* G) (hs : Function.Surjective π)

/-- The commutator of the chosen lifts. -/
noncomputable def liftPair (a b : G) : E :=
  ⁅Function.surjInv hs a, Function.surjInv hs b⁆

variable {π hs}

theorem lift_eq_mul_central (hc : π.ker ≤ Subgroup.center E) {x : E} {a : G}
    (hx : π x = a) : ∃ z ∈ Subgroup.center E, x = Function.surjInv hs a * z := by
  refine ⟨(Function.surjInv hs a)⁻¹ * x, hc ?_, by group⟩
  simp [MonoidHom.mem_ker, Function.surjInv_eq hs, hx]

/-- The commutator of lifts does not depend on the lifts. -/
theorem commutator_eq_liftPair (hc : π.ker ≤ Subgroup.center E) {x y : E} {a b : G}
    (hx : π x = a) (hy : π y = b) : ⁅x, y⁆ = liftPair π hs a b := by
  obtain ⟨z, hz, rfl⟩ := lift_eq_mul_central (hs := hs) hc hx
  obtain ⟨w, hw, rfl⟩ := lift_eq_mul_central (hs := hs) hc hy
  unfold liftPair
  set A := Function.surjInv hs a
  set B := Function.surjInv hs b
  have hzc : ∀ g : E, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hz g
  have hwc : ∀ g : E, g * w = w * g := fun g => Subgroup.mem_center_iff.mp hw g
  simp only [commutatorElement_def]
  calc A * z * (B * w) * (A * z)⁻¹ * (B * w)⁻¹
      = A * (z * (B * w)) * z⁻¹ * A⁻¹ * (w⁻¹ * B⁻¹) := by group
    _ = A * ((B * w) * z) * z⁻¹ * A⁻¹ * (w⁻¹ * B⁻¹) := by rw [← hzc]
    _ = A * B * (w * A⁻¹ * w⁻¹) * B⁻¹ := by group
    _ = A * B * A⁻¹ * B⁻¹ := by
      rw [← hwc A⁻¹]; group

theorem map_liftPair (a b : G) : π (liftPair π hs a b) = ⁅a, b⁆ := by
  simp [liftPair, map_commutatorElement, Function.surjInv_eq hs]

theorem liftPair_mem_center (hc : π.ker ≤ Subgroup.center E) {a b : G} (hab : Commute a b) :
    liftPair π hs a b ∈ Subgroup.center E :=
  hc (by rw [MonoidHom.mem_ker, map_liftPair, hab.commutator_eq])

theorem liftPair_mul_right (hc : π.ker ≤ Subgroup.center E) {a b b' : G}
    (hab' : Commute a b') :
    liftPair π hs a (b * b') = liftPair π hs a b * liftPair π hs a b' := by
  set A := Function.surjInv hs a
  set B := Function.surjInv hs b
  set B' := Function.surjInv hs b'
  have h1 : liftPair π hs a (b * b') = ⁅A, B * B'⁆ :=
    (commutator_eq_liftPair hc (Function.surjInv_eq hs a) (by
      simp [B, B', Function.surjInv_eq hs])).symm
  have hcen := liftPair_mem_center (hs := hs) hc hab'
  rw [h1]
  have key : ⁅A, B * B'⁆ = ⁅A, B⁆ * (B * ⁅A, B'⁆ * B⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [key]
  change ⁅A, B⁆ * (B * liftPair π hs a b' * B⁻¹) = _
  rw [Subgroup.mem_center_iff.mp hcen B, mul_inv_cancel_right]
  rfl

theorem liftPair_mul_left (hc : π.ker ≤ Subgroup.center E) {a a' b : G}
    (ha'b : Commute a' b) :
    liftPair π hs (a * a') b = liftPair π hs a b * liftPair π hs a' b := by
  set A := Function.surjInv hs a
  set A' := Function.surjInv hs a'
  set B := Function.surjInv hs b
  have h1 : liftPair π hs (a * a') b = ⁅A * A', B⁆ :=
    (commutator_eq_liftPair hc (by simp [A, A', Function.surjInv_eq hs])
      (Function.surjInv_eq hs b)).symm
  have hcen := liftPair_mem_center (hs := hs) hc ha'b
  rw [h1]
  have key : ⁅A * A', B⁆ = (A * ⁅A', B⁆ * A⁻¹) * ⁅A, B⁆ := by
    simp only [commutatorElement_def]; group
  rw [key]
  change (A * liftPair π hs a' b * A⁻¹) * liftPair π hs a b = _
  rw [Subgroup.mem_center_iff.mp hcen A, mul_inv_cancel_right,
    Subgroup.mem_center_iff.mp hcen]

/-- Simultaneous conjugation invariance. -/
theorem liftPair_conj (hc : π.ker ≤ Subgroup.center E) {a b : G} (hab : Commute a b) (g : G) :
    liftPair π hs (g * a * g⁻¹) (g * b * g⁻¹) = liftPair π hs a b := by
  set A := Function.surjInv hs a
  set B := Function.surjInv hs b
  set C := Function.surjInv hs g
  have hC : π C = g := Function.surjInv_eq hs g
  have h1 : liftPair π hs (g * a * g⁻¹) (g * b * g⁻¹) = ⁅C * A * C⁻¹, C * B * C⁻¹⁆ :=
    (commutator_eq_liftPair hc (by simp [A, hC, Function.surjInv_eq hs])
      (by simp [B, hC, Function.surjInv_eq hs])).symm
  have hcen := liftPair_mem_center (hs := hs) hc hab
  rw [h1]
  have key : ⁅C * A * C⁻¹, C * B * C⁻¹⁆ = C * ⁅A, B⁆ * C⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [key]
  change C * liftPair π hs a b * C⁻¹ = _
  rw [Subgroup.mem_center_iff.mp hcen C, mul_inv_cancel_right]

theorem liftPair_pow_left (hc : π.ker ≤ Subgroup.center E) {a b : G} (hab : Commute a b)
    (m : ℕ) : liftPair π hs (a ^ m) b = liftPair π hs a b ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero]
    have h := commutator_eq_liftPair (hs := hs) hc (x := 1) (y := Function.surjInv hs b)
      (a := 1) (b := b) (by simp) (Function.surjInv_eq hs b)
    rw [← h]; simp
  | succ m ih =>
    rw [pow_succ, liftPair_mul_left hc hab, ih, pow_succ]

theorem liftPair_inv_right (hc : π.ker ≤ Subgroup.center E) {a b : G} (hab : Commute a b) :
    liftPair π hs a b⁻¹ = (liftPair π hs a b)⁻¹ := by
  have h0 : liftPair π hs a (b * b⁻¹) = 1 := by
    rw [mul_inv_cancel]
    have h := commutator_eq_liftPair (hs := hs) hc (x := Function.surjInv hs a) (y := 1)
      (a := a) (b := 1) (Function.surjInv_eq hs a) (by simp)
    rw [← h]; simp
  rw [liftPair_mul_right hc hab.inv_right] at h0
  exact eq_inv_of_mul_eq_one_right h0

theorem liftPair_one_left (hc : π.ker ≤ Subgroup.center E) (b : G) : liftPair π hs 1 b = 1 := by
  have h := commutator_eq_liftPair (hs := hs) hc (x := 1) (y := Function.surjInv hs b)
    (a := 1) (b := b) (by simp) (Function.surjInv_eq hs b)
  rw [← h]; simp

theorem liftPair_one_right (hc : π.ker ≤ Subgroup.center E) (a : G) : liftPair π hs a 1 = 1 := by
  have h := commutator_eq_liftPair (hs := hs) hc (x := Function.surjInv hs a) (y := 1)
    (a := a) (b := 1) (Function.surjInv_eq hs a) (by simp)
  rw [← h]; simp

theorem liftPair_pow_right (hc : π.ker ≤ Subgroup.center E) {a b : G} (hab : Commute a b)
    (m : ℕ) : liftPair π hs a (b ^ m) = liftPair π hs a b ^ m := by
  induction m with
  | zero => simp only [pow_zero]; exact liftPair_one_right hc a
  | succ m ih => rw [pow_succ, liftPair_mul_right hc hab, ih, pow_succ]

theorem liftPair_inv_left (hc : π.ker ≤ Subgroup.center E) {a b : G} (hab : Commute a b) :
    liftPair π hs a⁻¹ b = (liftPair π hs a b)⁻¹ := by
  have h0 : liftPair π hs (a⁻¹ * a) b = 1 := by
    rw [inv_mul_cancel]; exact liftPair_one_left hc b
  rw [liftPair_mul_left hc hab] at h0
  exact eq_inv_of_mul_eq_one_left h0

/-- Vanishing of the pairing means that all lifts commute. -/
theorem commute_of_liftPair_eq_one (hc : π.ker ≤ Subgroup.center E) {a b : G}
    (h : liftPair π hs a b = 1) {x y : E} (hx : π x = a) (hy : π y = b) : Commute x y := by
  have := commutator_eq_liftPair (hs := hs) hc hx hy
  rw [h, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem liftPair_eq_one_of_commute (hc : π.ker ≤ Subgroup.center E) {a b : G} {x y : E}
    (hx : π x = a) (hy : π y = b) (hxy : Commute x y) : liftPair π hs a b = 1 := by
  rw [← commutator_eq_liftPair hc hx hy, hxy.commutator_eq]

end Pairing

end VOA.Huang.DLNSchur
