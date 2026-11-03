/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.Singular

/-!
# Positive current modes on quadratic states `J^a_{-1} J^b_{-1}|0⟩`

For general Lie data `D`, with `f = structureConstant D` and `κ = formTable D`:

* `J_pos_st1`: `J^x_m J^b_{-1}|0⟩ = [m = 1] k κ(x,b) |0⟩` for `m ≥ 1`;
* `J_zero_st1`: `J^x_0 J^b_{-1}|0⟩ = Σ_c f(x,b,c) J^c_{-1}|0⟩`;
* `J_one_st2`: `J^x_1 J^a_{-1}J^b_{-1}|0⟩ = k κ(x,b) J^a_{-1}|0⟩ + k κ(x,a) J^b_{-1}|0⟩
  + Σ_c f(x,a,c) Σ_g f(c,b,g) J^g_{-1}|0⟩`;
* `J_two_st2`: `J^x_2 J^a_{-1}J^b_{-1}|0⟩ = k Σ_c f(x,a,c) κ(c,b) |0⟩`; `J_ge_st2`: zero for `m ≥ 3`.

`singP_quad`: a combination `t = Σ cᵢ J^{aᵢ}_{-1}J^{bᵢ}_{-1}|0⟩` is `SingP` as soon as two families of scalar sums
vanish, the weight-one coefficients `quadCoef1` and the vacuum coefficients `quadCoef2`. For a concrete
algebra these are finite computations.
-/

namespace VOA.AffineGeneral

open VOA.AffineGeneral.LieData

noncomputable section

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι) (k : ℂ)

/-- `J^a_{-1}|0⟩`. -/
abbrev st1 (a : ι) : Vacuum D k := J D k a (-1) (vacuumA D k)

/-- `J^a_{-1} J^b_{-1}|0⟩`. -/
abbrev st2 (a b : ι) : Vacuum D k := J D k a (-1) (st1 D k b)

theorem J_comm_apply (a b : ι) (m n : ℤ) (v : Vacuum D k) :
    J D k a m (J D k b n v) = J D k b n (J D k a m v) + ∑ c, structureConstant D a b c • J D k c (m + n) v
      + (if m + n = 0 then ((m : ℂ) * k * formTable D a b) • v else 0) := by
  have h := LinearMap.congr_fun (current_comm D k a b m n) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  split_ifs <;> simp [add_comm, add_left_comm]

theorem J_pos_st1 (x b : ι) {m : ℤ} (hm : 1 ≤ m) :
    J D k x m (st1 D k b) = if m = 1 then (k * formTable D x b) • vacuumA D k else 0 := by
  rw [st1, J_comm_apply, J_vacuum_nonneg D k x (by omega), map_zero, zero_add]
  rw [Finset.sum_eq_zero (fun c _ => by rw [J_vacuum_nonneg D k c (by omega), smul_zero]), zero_add]
  by_cases h1 : m = 1
  · subst h1; simp
  · rw [if_neg (by omega), if_neg h1]

theorem J_zero_st1 (x b : ι) : J D k x 0 (st1 D k b) = ∑ c, structureConstant D x b c • st1 D k c := by
  rw [st1, J_comm_apply, J_vacuum_nonneg D k x le_rfl, map_zero, zero_add, if_neg (by norm_num), add_zero]
  simp

theorem J_one_st2 (x a b : ι) :
    J D k x 1 (st2 D k a b) = (k * formTable D x b) • st1 D k a + (k * formTable D x a) • st1 D k b
      + ∑ c, structureConstant D x a c • ∑ g, structureConstant D c b g • st1 D k g := by
  rw [st2, J_comm_apply, J_pos_st1 D k x b le_rfl, if_pos rfl, map_smul, if_pos (by norm_num)]
  simp only [show (1 : ℤ) + -1 = 0 by norm_num, J_zero_st1, Int.cast_one, one_mul]
  abel

theorem J_two_st2 (x a b : ι) :
    J D k x 2 (st2 D k a b) = (k * ∑ c, structureConstant D x a c * formTable D c b) • vacuumA D k := by
  rw [st2, J_comm_apply, J_pos_st1 D k x b (by norm_num), if_neg (by norm_num), map_zero, zero_add,
    if_neg (by norm_num), add_zero, show (2 : ℤ) + -1 = 1 by norm_num]
  simp only [J_pos_st1 D k _ b le_rfl, if_true, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem J_ge_st2 (x a b : ι) {m : ℤ} (hm : 3 ≤ m) : J D k x m (st2 D k a b) = 0 := by
  rw [st2, J_comm_apply, J_pos_st1 D k x b (by omega), if_neg (by omega), map_zero, zero_add,
    if_neg (by omega), add_zero]
  exact Finset.sum_eq_zero fun c _ => by rw [J_pos_st1 D k c b (by omega), if_neg (by omega), smul_zero]

/-! ## Quadratic combinations -/

/-- `t = Σ cᵢ J^{aᵢ}_{-1}J^{bᵢ}_{-1}|0⟩`. -/
def quadState (terms : List (ℂ × ι × ι)) : Vacuum D k :=
  (terms.map fun t => t.1 • st2 D k t.2.1 t.2.2).sum

/-- The weight-one coefficient of `J^x_1 t` at `J^g_{-1}|0⟩`. -/
def quadCoef1 (terms : List (ℂ × ι × ι)) (x g : ι) : ℂ :=
  (terms.map fun t => t.1 * ((if t.2.1 = g then k * formTable D x t.2.2 else 0)
    + (if t.2.2 = g then k * formTable D x t.2.1 else 0)
    + ∑ c, structureConstant D x t.2.1 c * structureConstant D c t.2.2 g)).sum

/-- The vacuum coefficient of `J^x_2 t`. -/
def quadCoef2 (terms : List (ℂ × ι × ι)) (x : ι) : ℂ :=
  (terms.map fun t => t.1 * (k * ∑ c, structureConstant D x t.2.1 c * formTable D c t.2.2)).sum

/-- `J^x_1 J^a_{-1}J^b_{-1}|0⟩` in the coordinates `J^g_{-1}|0⟩`. -/
theorem J_one_st2_coord (x a b : ι) :
    J D k x 1 (st2 D k a b) = ∑ g, ((if a = g then k * formTable D x b else 0)
      + (if b = g then k * formTable D x a else 0)
      + ∑ c, structureConstant D x a c * structureConstant D c b g) • st1 D k g := by
  rw [J_one_st2]
  simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  congr 1
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem J_one_quad (terms : List (ℂ × ι × ι)) (x : ι) :
    J D k x 1 (quadState D k terms) = ∑ g, quadCoef1 D k terms x g • st1 D k g := by
  induction terms with
  | nil => simp [quadState, quadCoef1]
  | cons t terms ih =>
    simp only [quadState, quadCoef1, List.map_cons, List.sum_cons] at ih ⊢
    rw [map_add, map_smul, ih, J_one_st2_coord, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_smul, ← add_smul]

theorem J_two_quad (terms : List (ℂ × ι × ι)) (x : ι) :
    J D k x 2 (quadState D k terms) = quadCoef2 D k terms x • vacuumA D k := by
  induction terms with
  | nil => simp [quadState, quadCoef2]
  | cons t terms ih =>
    simp only [quadState, quadCoef2, List.map_cons, List.sum_cons] at ih ⊢
    rw [map_add, map_smul, ih, J_two_st2, smul_smul, ← add_smul]

theorem J_ge_quad (terms : List (ℂ × ι × ι)) (x : ι) {m : ℤ} (hm : 3 ≤ m) :
    J D k x m (quadState D k terms) = 0 := by
  induction terms with
  | nil => simp [quadState]
  | cons t terms ih =>
    simp only [quadState, List.map_cons, List.sum_cons] at ih ⊢
    rw [map_add, map_smul, ih, J_ge_st2 D k x _ _ hm, smul_zero, add_zero]

/-- **A quadratic state is positive-mode singular** if its two coefficient families vanish. -/
theorem singP_quad (terms : List (ℂ × ι × ι)) (h1 : ∀ x g, quadCoef1 D k terms x g = 0)
    (h2 : ∀ x, quadCoef2 D k terms x = 0) : SingP D k (quadState D k terms) := by
  intro x i hi
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · rw [J_one_quad]; simp [h1]
  · rw [J_two_quad, h2, zero_smul]
  · exact J_ge_quad D k terms x h3

theorem st2_mem (a b : ι) : st2 D k a b ∈ gradingZA D k 2 := by
  rw [show (2 : ℤ) = 1 - (-1) from by ring]
  refine J_mem_gradingZA D k a (-1) 1 ?_
  rw [show (1 : ℤ) = 0 - (-1) from by ring]
  exact J_mem_gradingZA D k b (-1) 0 (vacuumA_mem_gradingZA_zero D k)

theorem quadState_mem (terms : List (ℂ × ι × ι)) : quadState D k terms ∈ gradingZA D k 2 := by
  unfold quadState
  induction terms with
  | nil => exact Submodule.zero_mem _
  | cons t terms ih =>
    rw [List.map_cons, List.sum_cons]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (st2_mem D k _ _)) ih

/-- **A quadratic state with vanishing coefficient families lies in the maximal ideal.** -/
theorem quadState_mem_maxIdeal (hk : k + D.h ≠ 0) (terms : List (ℂ × ι × ι))
    (h1 : ∀ x g, quadCoef1 D k terms x g = 0) (h2 : ∀ x, quadCoef2 D k terms x = 0) :
    quadState D k terms ∈ maxIdeal D k hk :=
  mem_maxIdeal_of_SingP D k hk (singP_quad D k terms h1 h2) (by norm_num) (quadState_mem D k terms)

end

end VOA.AffineGeneral
