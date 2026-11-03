import VOA.Huang.DLNSmallThreeLayer

/-!
# Generators of the layer and of the level-one kernel

* `N ≤ ⟨x(3^k), y(3^k), diag(1+3^k, 1-3^k)⟩`;
* `K₁ ≤ ⟨x(3), y(3), diag(4, 4⁻¹)⟩`.

Both use the unit-pivot (Gauss) chart: the top-left entry is a unit on these kernels.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl

theorem one_add_pow_of_mul_self_eq_zero {R : Type*} [CommRing R] (q : R) (hq : q * q = 0)
    (m : ℕ) : (1 + q) ^ m = 1 + (m : R) * q := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination (m : R) * hq

section Gen

variable {k : ℕ}

theorem layerN_le_closure (hk : 1 ≤ k) :
    layerN k ≤ Subgroup.closure {nE k, nF k, nH k} := by
  intro n hn
  set C := Subgroup.closure {nE k, nF k, nH k}
  obtain ⟨W, hW⟩ := (mem_layerN_iff n).mp hn
  set q : ZMod (3 ^ (k + 1)) := 3 ^ k with hqdef
  have hq : q * q = 0 := three_pow_mul_self hk
  have e00 : n 0 0 = 1 + q * W 0 0 := by
    have := congrFun (congrFun hW 0) 0; simpa using this
  have e01 : n 0 1 = q * W 0 1 := by
    have := congrFun (congrFun hW 0) 1; simpa using this
  have e10 : n 1 0 = q * W 1 0 := by
    have := congrFun (congrFun hW 1) 0; simpa using this
  let u0 : (ZMod (3 ^ (k + 1)))ˣ :=
    ⟨1 + q * W 0 0, 1 - q * W 0 0, by linear_combination (-(W 0 0) ^ 2) * hq,
      by linear_combination (-(W 0 0) ^ 2) * hq⟩
  have hu0 : n 0 0 = (u0 : ZMod (3 ^ (k + 1))) := e00
  have hu0inv : ((u0⁻¹ : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))) = 1 - q * W 0 0 := rfl
  have hnE : nE k ∈ C := Subgroup.subset_closure (by simp)
  have hnF : nF k ∈ C := Subgroup.subset_closure (by simp)
  have hnH : nH k ∈ C := Subgroup.subset_closure (by simp)
  rw [gauss_of_unit_top_left n u0 hu0]
  refine C.mul_mem (C.mul_mem ?_ ?_) ?_
  · have : n 1 0 * ((u0⁻¹ : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))) =
        ((W 1 0).val : ZMod (3 ^ (k + 1))) * q := by
      rw [ZMod.natCast_zmod_val, e10, hu0inv]
      linear_combination (-(W 1 0 * W 0 0)) * hq
    rw [this, ← lowerRoot_pow]
    exact C.pow_mem hnF _
  · have : u0 = (fourU k ^ (3 ^ (k - 1))) ^ (W 0 0).val := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, nH_eq_torus_val hk,
        one_add_pow_of_mul_self_eq_zero _ hq, ZMod.natCast_zmod_val]
      change 1 + q * W 0 0 = 1 + W 0 0 * q
      ring
    rw [this, ← torus_pow]
    exact C.pow_mem hnH _
  · have : n 0 1 * ((u0⁻¹ : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))) =
        ((W 0 1).val : ZMod (3 ^ (k + 1))) * q := by
      rw [ZMod.natCast_zmod_val, e01, hu0inv]
      linear_combination (-(W 0 1 * W 0 0)) * hq
    rw [this, ← upperRoot_pow]
    exact C.pow_mem hnE _

/-- Powers of `4⁻¹` modulo nine. -/
theorem inv_four_pow (m : ℕ) : ∃ z : ZMod (3 ^ (k + 1)),
    ((((fourU k)⁻¹ ^ m : (ZMod (3 ^ (k + 1)))ˣ)) : ZMod (3 ^ (k + 1))) =
      1 - 3 * (m : ZMod (3 ^ (k + 1))) + 9 * z := by
  set i : ZMod (3 ^ (k + 1)) := ((((fourU k)⁻¹ : (ZMod (3 ^ (k + 1)))ˣ)) : ZMod (3 ^ (k + 1))) with hi
  have h4i : 4 * i = 1 := by rw [hi, ← fourU_val (k := k)]; simp
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨i + (m : ZMod (3 ^ (k + 1))) * i + z - 3 * z * i, ?_⟩
    rw [pow_succ ((fourU k)⁻¹) m, Units.val_mul, hz, ← hi]
    push_cast
    linear_combination (-2 - 3 * (m : ZMod (3 ^ (k + 1))) + 9 * z) * h4i

theorem levelOne_le_closure (hk : 1 ≤ k) :
    levelOne k ≤ Subgroup.closure {x3 k, y3 k, t4 k} := by
  intro g hg
  set C := Subgroup.closure {x3 k, y3 k, t4 k}
  obtain ⟨V, hV⟩ := (mem_levelOne_iff g).mp hg
  have e00 : g 0 0 = 1 + 3 * V 0 0 := by
    have := congrFun (congrFun hV 0) 0; simpa using this
  have e01 : g 0 1 = 3 * V 0 1 := by
    have := congrFun (congrFun hV 0) 1; simpa using this
  have e10 : g 1 0 = 3 * V 1 0 := by
    have := congrFun (congrFun hV 1) 0; simpa using this
  have hnil : IsNilpotent (3 * V 0 0 : ZMod (3 ^ (k + 1))) :=
    ⟨k + 1, by rw [mul_pow, three_pow_succ_eq_zero, zero_mul]⟩
  obtain ⟨u0, hu0'⟩ := hnil.isUnit_one_add
  have hu0 : g 0 0 = (u0 : ZMod (3 ^ (k + 1))) := by rw [hu0', e00]
  have hx3 : x3 k ∈ C := Subgroup.subset_closure (by simp)
  have hy3 : y3 k ∈ C := Subgroup.subset_closure (by simp)
  have ht4 : t4 k ∈ C := Subgroup.subset_closure (by simp)
  have hup : ∀ w : ZMod (3 ^ (k + 1)), upperRoot (3 * w) ∈ C := by
    intro w
    have : upperRoot (3 * w) = x3 k ^ w.val := by
      rw [upperRoot_pow, ZMod.natCast_zmod_val, mul_comm]
    rw [this]; exact C.pow_mem hx3 _
  have hlow : ∀ w : ZMod (3 ^ (k + 1)), lowerRoot (3 * w) ∈ C := by
    intro w
    have : lowerRoot (3 * w) = y3 k ^ w.val := by
      rw [lowerRoot_pow, ZMod.natCast_zmod_val, mul_comm]
    rw [this]; exact C.pow_mem hy3 _
  rw [gauss_of_unit_top_left g u0 hu0]
  refine C.mul_mem (C.mul_mem ?_ ?_) ?_
  · rw [e10, mul_assoc]; exact hlow _
  · -- Split off a power of `t₄`, leaving a torus element `≡ 1 (mod 9)`.
    set m := (V 0 0).val
    set b : (ZMod (3 ^ (k + 1)))ˣ := u0 * (fourU k)⁻¹ ^ m with hb
    have hsplit : u0 = fourU k ^ m * b := by
      rw [hb, inv_pow, mul_comm u0, ← mul_assoc, mul_inv_cancel, one_mul]
    obtain ⟨z, hz⟩ := inv_four_pow (k := k) m
    have hbval : (b : ZMod (3 ^ (k + 1))) = 1 + 3 * (3 * (z - V 0 0 ^ 2 + 3 * V 0 0 * z)) := by
      rw [hb, Units.val_mul, hz, ← hu0, e00, ZMod.natCast_zmod_val]
      ring
    rw [hsplit, torus_mul, ← torus_pow]
    refine C.mul_mem (C.pow_mem ht4 _) ?_
    rw [torus_eq_four_roots b 3 _ hbval]
    refine C.mul_mem (C.mul_mem (C.mul_mem ?_ ?_) ?_) ?_
    · simpa using hup 1
    · exact hlow _
    · rw [show -3 * ((b⁻¹ : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))) =
        3 * (-((b⁻¹ : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1)))) by ring]
      exact hup _
    · rw [show -(3 * (z - V 0 0 ^ 2 + 3 * V 0 0 * z)) * (b : ZMod (3 ^ (k + 1))) =
        3 * (-(z - V 0 0 ^ 2 + 3 * V 0 0 * z) * (b : ZMod (3 ^ (k + 1)))) by ring]
      exact hlow _
  · rw [e01, mul_assoc]; exact hup _

end Gen

end VOA.Huang.DLNSchur
