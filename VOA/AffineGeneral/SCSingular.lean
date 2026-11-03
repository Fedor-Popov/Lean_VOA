/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SCLieData
import VOA.AffineGeneral.SingularQuad

/-!
# Quadratic singular vectors for structure-constant Lie data

For `LD = lieDataOf …` (a structure-constant algebra with a sparse invariant form `Gm`):

* `ld_sc`, `ld_form`: the structure constants and form table of `LD` are the table entries;
* `ld_sum_sc_form`, `ld_sum_sc_sc`: the two contractions appearing in `quadCoef2`, `quadCoef1`;
* `q1OK`, `q2OK`: Boolean checks (integer level `k`, integer coefficients) with
  **`ld_quadState_mem_maxIdeal`**: if both pass, `Σ cᵢ J^{aᵢ}_{-1}J^{bᵢ}_{-1}|0⟩ ∈ maxIdeal`.
-/

namespace VOA.AffineGeneral.SCLie

open VOA.AffineGeneral VOA.AffineGeneral.LieData

noncomputable section

variable {N : ℕ} {T : Table} (hc : Checks N T)
variable (Gm : List (ℕ × ℕ × ℤ)) (hG : gInRange N Gm = true) (hs : symmPerm Gm = true)
  (hsk : ∀ c : Fin N, Skew hc Gm (basis hc c)) (dl : ℕ → List (ℕ × ℤ)) (D : ℕ → ℤ)
  (hp : pairOK N Gm dl D = true) (L c : ℤ) (hL : L ≠ 0) (hcas : ∀ x : Fin N, casOK T N dl D L c x = true)

theorem lie_basis_vec (a b : Fin N) : ⁅basis hc a, basis hc b⁆ = vec hc (entry T a b) := by
  rw [basis_eq_vec, basis_eq_vec, lie_vec hc (by simp [inRange]) (by simp [inRange])]
  funext k
  simp [vec, brL, coef_scale]

theorem basis_repr_apply (v : Alg N T hc) (g : Fin N) : (basis hc).repr v g = v g :=
  Pi.basisFun_repr (R := ℂ) (η := Fin N) v g

local notation "LD" => lieDataOf hc Gm hG hs hsk dl D hp L c hL hcas

theorem ld_sc (a b g : Fin N) : (LD).structureConstant a b g = (coef (entry T a b) g : ℂ) := by
  show (basis hc).repr ⁅basis hc a, basis hc b⁆ g = _
  rw [basis_repr_apply, lie_basis_vec]
  rfl

theorem ld_form (a b : Fin N) : (LD).formTable a b = (formV Gm [((a : ℕ), 1)] [((b : ℕ), 1)] : ℂ) :=
  formG_basis hc Gm hG a b

theorem ld_sum_sc_form (x a b : Fin N) :
    ∑ e, (LD).structureConstant x a e * (LD).formTable e b
      = (formV Gm (entry T x a) [((b : ℕ), 1)] : ℂ) := by
  have h := congrArg (fun v => formG hc Gm v (basis hc b)) ((LD).generator_bracket x a)
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h
  refine Eq.trans h.symm ?_
  change formG hc Gm ⁅basis hc x, basis hc a⁆ (basis hc b) = _
  rw [lie_basis_vec, basis_eq_vec hc b, formG_vec hc Gm hG]

theorem ld_sum_sc_sc (x a b g : Fin N) (hr : inRange N (entry T x a) = true) :
    ∑ e, (LD).structureConstant x a e * (LD).structureConstant e b g
      = (coef (brL T (entry T x a) [((b : ℕ), 1)]) g : ℂ) := by
  have h := congrArg (fun v => (basis hc).repr ⁅v, basis hc b⁆ g) ((LD).generator_bracket x a)
  simp only [sum_lie, smul_lie, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul] at h
  refine Eq.trans h.symm ?_
  change (basis hc).repr ⁅⁅basis hc x, basis hc a⁆, basis hc b⁆ g = _
  rw [basis_repr_apply, lie_basis_vec, basis_eq_vec hc b, lie_vec hc hr (by simp [inRange])]
  rfl

theorem ld_quadCoef1 (k : ℤ) (tz : List (ℤ × Fin N × Fin N)) (x g : Fin N)
    (hr : ∀ t ∈ tz, inRange N (entry T x t.2.1) = true) :
    quadCoef1 LD (k : ℂ) (termsC tz) x g = (coef (q1Vec T Gm k tz x) g : ℂ) := by
  induction tz with
  | nil => simp [quadCoef1, termsC, q1Vec]
  | cons t tz ih =>
    have ih := ih fun t' ht' => hr t' (List.mem_cons_of_mem _ ht')
    simp only [quadCoef1, termsC, q1Vec, List.map_cons, List.sum_cons, List.flatMap_cons] at ih ⊢
    rw [ih, coef_append, coef_scale, coef_cons, coef_cons, ld_sum_sc_sc hc Gm hG hs hsk dl D hp L c hL hcas
      x _ _ g (hr t List.mem_cons_self), ld_form, ld_form]
    simp only [Fin.val_inj]
    split_ifs <;> push_cast <;> ring

theorem ld_quadCoef2 (k : ℤ) (tz : List (ℤ × Fin N × Fin N)) (x : Fin N) :
    quadCoef2 LD (k : ℂ) (termsC tz) x
      = ((tz.map fun t => t.1 * (k * formV Gm (entry T x t.2.1.val) [(t.2.2.val, 1)])).sum : ℤ) := by
  induction tz with
  | nil => simp [quadCoef2, termsC]
  | cons t tz ih =>
    simp only [quadCoef2, termsC, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, ld_sum_sc_form]
    push_cast; ring

/-- **Quadratic singular vectors of structure-constant Lie data lie in the maximal ideal.** -/
theorem ld_quadState_mem_maxIdeal (k : ℤ) (hk : (k : ℂ) + (LD).h ≠ 0) (tz : List (ℤ × Fin N × Fin N))
    (h1 : q1OK T Gm k tz = true) (h2 : q2OK T Gm k tz = true) :
    quadState LD (k : ℂ) (termsC tz) ∈ maxIdeal LD (k : ℂ) hk := by
  refine quadState_mem_maxIdeal LD (k : ℂ) hk (termsC tz) (fun x g => ?_) (fun x => ?_)
  · have hx := List.all_eq_true.mp h1 x (List.mem_range.mpr x.2)
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hx
    rw [ld_quadCoef1 hc Gm hG hs hsk dl D hp L c hL hcas k tz x g hx.1, hx.2 g g.2, Int.cast_zero]
  · have hx := List.all_eq_true.mp h2 x (List.mem_range.mpr x.2)
    simp only [beq_iff_eq] at hx
    rw [ld_quadCoef2 hc Gm hG hs hsk dl D hp L c hL hcas k tz x, hx, Int.cast_zero]

end

end VOA.AffineGeneral.SCLie
