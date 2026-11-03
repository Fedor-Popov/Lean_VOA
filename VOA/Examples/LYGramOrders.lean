/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.FeiginFuchsLower

/-!
# Orders of the Kac factors at the Lee–Yang point `t = 2/5` of the vacuum curve

Along the `(1,1)` curve `c(t) = 13 - 6t - 6/t`, `h = h_{1,1}(t) = 0` (the BSA curve with `N = 1`)
the Lee–Yang point is `t₀ = 2/5`: `c(2/5) = -22/5`.  This file factors the two Kac products that
enter the quotient-determinant identity `FFLower.curve_identity` (with `N = 1`) as
`(t - 2/5)^{order} × (continuous, nonzero at 2/5)`:

* `factorA` — `h_{1,1}(t) - h_{u,v}(t) = (t - 2/5)^{eA u v} · gA u v t`, where `eA u v` counts the
  conditions `5v = 2u + 3`, `2u = 5v + 3`;
* `factorB` — `h_{1,1}(t) + 1 - h_{u,v}(t) = (t - 2/5)^{eB u v} · gB u v t`, where `eB u v` counts
  `2u = 5v + 7`, `5v = 2u + 7`;
* `kwpRest_eval_LY` / `gram_shift_det_LY` — the two products, with exponents `aLY m`, `bLY m`.

All proved, no hypotheses.
-/

open Finset

noncomputable section

namespace VOA.RRLower.LYGram

open VOA.InverseDS.VirasoroVerma VOA.VirasoroScreening VOA.Classification.COne VOA.Classification.COne.FFLower
open Polynomial
open scoped Classical

/-- The Lee–Yang parameter on the vacuum curve. -/
def t0 : ℂ := 2 / 5

theorem t0_ne : t0 ≠ 0 := by norm_num [t0]

theorem charge_t0 : vermaBSACharge t0 = -22 / 5 := by
  norm_num [vermaBSACharge, t0]

theorem weight_one (t : ℂ) : vermaBSAWeight 1 t = 0 := by
  simp [vermaBSAWeight]

/-- Order of `h_{1,1}(t) - h_{u,v}(t)` at `t₀`. -/
def eA (u v : ℕ) : ℕ := (if 5 * v = 2 * u + 3 then 1 else 0) + (if 2 * u = 5 * v + 3 then 1 else 0)

/-- Reduced factor of `h_{1,1}(t) - h_{u,v}(t)`. -/
def gA (u v : ℕ) (t : ℂ) : ℂ :=
  (if 5 * v = 2 * u + 3 then (1 - (u : ℂ)) else ((1 - (u : ℂ)) * t + ((v : ℂ) - 1))) *
    (if 2 * u = 5 * v + 3 then (1 + (u : ℂ)) else ((1 + (u : ℂ)) * t - ((v : ℂ) + 1))) / (4 * t)

theorem factorA (u v : ℕ) (t : ℂ) (ht : t ≠ 0) :
    vermaBSAWeight 1 t - fusionKacWeight u v t = (t - t0) ^ eA u v * gA u v t := by
  have key : vermaBSAWeight 1 t - fusionKacWeight u v t =
      ((1 - (u : ℂ)) * t + ((v : ℂ) - 1)) * ((1 + (u : ℂ)) * t - ((v : ℂ) + 1)) / (4 * t) := by
    simp only [vermaBSAWeight, fusionKacWeight]; push_cast; field_simp; ring
  rw [key]
  unfold eA gA
  by_cases h1 : 5 * v = 2 * u + 3 <;> by_cases h2 : 2 * u = 5 * v + 3
  · omega
  · have e1 : (5 : ℂ) * v = 2 * u + 3 := by exact_mod_cast h1
    simp only [if_pos h1, if_neg h2, t0]
    rw [mul_div_assoc', pow_one]
    congr 1
    linear_combination ((1 + (u : ℂ)) * t - ((v : ℂ) + 1)) * e1 / 5
  · have e2 : (2 : ℂ) * u = 5 * v + 3 := by exact_mod_cast h2
    simp only [if_neg h1, if_pos h2, t0]
    rw [mul_div_assoc', pow_one]
    congr 1
    linear_combination ((1 - (u : ℂ)) * t + ((v : ℂ) - 1)) * e2 / 5
  · simp only [if_neg h1, if_neg h2]
    ring

theorem gA_cont (u v : ℕ) : ContinuousAt (gA u v) t0 := by
  unfold gA
  refine ContinuousAt.div (ContinuousAt.mul ?_ ?_) (continuousAt_const.mul continuousAt_id)
    (by norm_num [t0])
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).add continuousAt_const
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).sub continuousAt_const

theorem gA_ne (u v : ℕ) (hne : ¬ (u = 1 ∧ v = 1)) : gA u v t0 ≠ 0 := by
  unfold gA
  refine div_ne_zero (mul_ne_zero ?_ ?_) (by norm_num [t0])
  · split_ifs with h1
    · intro h
      have hu : (u : ℂ) = 1 := by linear_combination -h
      have hu' : u = 1 := by exact_mod_cast hu
      exact hne ⟨hu', by omega⟩
    · intro h
      have hv : ((5 * v : ℕ) : ℂ) = ((2 * u + 3 : ℕ) : ℂ) := by
        push_cast; simp only [t0] at h; linear_combination 5 * h
      exact h1 (by exact_mod_cast hv)
  · split_ifs with h2
    · intro h
      have : ((1 + u : ℕ) : ℂ) = 0 := by push_cast; exact h
      have := Nat.cast_eq_zero.mp this
      omega
    · intro h
      have hu : ((2 * u : ℕ) : ℂ) = ((5 * v + 3 : ℕ) : ℂ) := by
        push_cast; simp only [t0] at h; linear_combination 5 * h
      exact h2 (by exact_mod_cast hu)

/-- Order of `h_{1,1}(t) + 1 - h_{u,v}(t)` at `t₀`. -/
def eB (u v : ℕ) : ℕ := (if 2 * u = 5 * v + 7 then 1 else 0) + (if 5 * v = 2 * u + 7 then 1 else 0)

/-- Reduced factor of `h_{1,1}(t) + 1 - h_{u,v}(t)`. -/
def gB (u v : ℕ) (t : ℂ) : ℂ :=
  (if 2 * u = 5 * v + 7 then (1 - (u : ℂ)) else ((1 - (u : ℂ)) * t + (1 + (v : ℂ)))) *
    (if 5 * v = 2 * u + 7 then (1 + (u : ℂ)) else ((1 + (u : ℂ)) * t + (1 - (v : ℂ)))) / (4 * t)

theorem factorB (u v : ℕ) (t : ℂ) (ht : t ≠ 0) :
    vermaBSAWeight 1 t + ((1 : ℕ) : ℂ) - fusionKacWeight u v t = (t - t0) ^ eB u v * gB u v t := by
  have key : vermaBSAWeight 1 t + ((1 : ℕ) : ℂ) - fusionKacWeight u v t =
      ((1 - (u : ℂ)) * t + (1 + (v : ℂ))) * ((1 + (u : ℂ)) * t + (1 - (v : ℂ))) / (4 * t) := by
    simp only [vermaBSAWeight, fusionKacWeight]; push_cast; field_simp; ring
  rw [key]
  unfold eB gB
  by_cases h1 : 2 * u = 5 * v + 7 <;> by_cases h2 : 5 * v = 2 * u + 7
  · omega
  · have e1 : (2 : ℂ) * u = 5 * v + 7 := by exact_mod_cast h1
    simp only [if_pos h1, if_neg h2, t0]
    rw [mul_div_assoc', pow_one]
    congr 1
    linear_combination (-((1 + (u : ℂ)) * t + (1 - (v : ℂ)))) * e1 / 5
  · have e2 : (5 : ℂ) * v = 2 * u + 7 := by exact_mod_cast h2
    simp only [if_neg h1, if_pos h2, t0]
    rw [mul_div_assoc', pow_one]
    congr 1
    linear_combination (-((1 - (u : ℂ)) * t + (1 + (v : ℂ)))) * e2 / 5
  · simp only [if_neg h1, if_neg h2]
    ring

theorem gB_cont (u v : ℕ) : ContinuousAt (gB u v) t0 := by
  unfold gB
  refine ContinuousAt.div (ContinuousAt.mul ?_ ?_) (continuousAt_const.mul continuousAt_id)
    (by norm_num [t0])
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).add continuousAt_const
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).add continuousAt_const

theorem gB_ne (u v : ℕ) : gB u v t0 ≠ 0 := by
  unfold gB
  refine div_ne_zero (mul_ne_zero ?_ ?_) (by norm_num [t0])
  · split_ifs with h1
    · intro h
      have hu : (u : ℂ) = 1 := by linear_combination -h
      have hu' : u = 1 := by exact_mod_cast hu
      omega
    · intro h
      have hv : ((2 * u : ℕ) : ℂ) = ((5 * v + 7 : ℕ) : ℂ) := by
        push_cast; simp only [t0] at h; linear_combination -5 * h
      exact h1 (by exact_mod_cast hv)
  · split_ifs with h2
    · intro h
      have : ((1 + u : ℕ) : ℂ) = 0 := by push_cast; exact h
      have := Nat.cast_eq_zero.mp this
      omega
    · intro h
      have hu : ((5 * v : ℕ) : ℂ) = ((2 * u + 7 : ℕ) : ℂ) := by
        push_cast; simp only [t0] at h; linear_combination -5 * h
      exact h2 (by exact_mod_cast hu)

theorem prod_order0 {α : Type*} (s : Finset α) (F g : α → ℂ) (e k : α → ℕ) (t a : ℂ)
    (hF : ∀ x ∈ s, F x = (t - a) ^ e x * g x) :
    ∏ x ∈ s, F x ^ k x = (t - a) ^ (∑ x ∈ s, k x * e x) * ∏ x ∈ s, g x ^ k x := by
  rw [Finset.prod_congr rfl (fun x hx => by rw [hF x hx, mul_pow, ← pow_mul]),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The exponent of `t - 2/5` in the Kac product at level `1 + m` with the `(1,1)` factor removed. -/
def aLY (m : ℕ) : ℕ :=
  ∑ x ∈ (kacLabels (1 + m)).erase (labOne 1 m (by omega)),
    VOA.Classification.COne.FFLower.pp (1 + m - (x.1.val + 1) * (x.2.val + 1)) * eA (x.1.val + 1) (x.2.val + 1)

/-- The exponent of `t - 2/5` in the shifted Kac product at level `m` (weight `h = 1`). -/
def bLY (m : ℕ) : ℕ :=
  ∑ x ∈ kacLabels m, VOA.Classification.COne.FFLower.pp (m - (x.1.val + 1) * (x.2.val + 1)) * eB (x.1.val + 1) (x.2.val + 1)

/-- The reduced remaining Kac product. -/
def GRly (m : ℕ) (t : ℂ) : ℂ :=
  ∏ x ∈ (kacLabels (1 + m)).erase (labOne 1 m (by omega)),
    gA (x.1.val + 1) (x.2.val + 1) t ^ VOA.Classification.COne.FFLower.pp (1 + m - (x.1.val + 1) * (x.2.val + 1))

/-- The reduced shifted Kac product. -/
def GBly (m : ℕ) (t : ℂ) : ℂ :=
  ∏ x ∈ kacLabels m, gB (x.1.val + 1) (x.2.val + 1) t ^ VOA.Classification.COne.FFLower.pp (m - (x.1.val + 1) * (x.2.val + 1))

theorem kwpRest_eval_LY (m : ℕ) (t : ℂ) (ht : t ≠ 0) :
    (kwpRest t 1 m (by omega)).eval (vermaBSAWeight 1 t) = (t - t0) ^ aLY m * GRly m t := by
  have hpp : ∀ k, Fintype.card (VermaPartitions k) = VOA.Classification.COne.FFLower.pp k := fun _ => rfl
  rw [kwpRest, eval_prod, aLY, GRly]
  simp only [eval_pow, eval_sub, eval_X, eval_C, hpp]
  refine prod_order0 _ _ _ _ _ t t0 (fun x _ => ?_)
  have := factorA (x.1.val + 1) (x.2.val + 1) t ht
  push_cast at this
  exact this

theorem gram_shift_det_LY (m : ℕ) (t : ℂ) (ht : t ≠ 0) :
    (vermaGramMatrix (vermaBSACharge t) (vermaBSAWeight 1 t + ((1 : ℕ) : ℂ)) m).det =
      (∏ w : VermaPartitions m, vermaDiagonalContraction w.val) *
        ((t - t0) ^ bLY m * GBly m t) := by
  have hpp : ∀ k, Fintype.card (VermaPartitions k) = VOA.Classification.COne.FFLower.pp k := fun _ => rfl
  rw [kac_determinant_eval t ht, kacWeightProduct, eval_prod, bLY, GBly]
  simp only [eval_pow, eval_sub, eval_X, eval_C, hpp]
  congr 1
  refine prod_order0 _ _ _ _ _ t t0 (fun x _ => ?_)
  have := factorB (x.1.val + 1) (x.2.val + 1) t ht
  push_cast at this ⊢
  exact this

theorem GRly_cont (m : ℕ) : ContinuousAt (GRly m) t0 := by
  unfold GRly
  exact cAt_prod _ _ _ fun x _ => (gA_cont _ _).pow _

theorem GBly_cont (m : ℕ) : ContinuousAt (GBly m) t0 := by
  unfold GBly
  exact cAt_prod _ _ _ fun x _ => (gB_cont _ _).pow _

theorem GRly_ne (m : ℕ) : GRly m t0 ≠ 0 := by
  unfold GRly
  refine Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero _ (gA_ne _ _ ?_)
  rintro ⟨h1, h2⟩
  apply (Finset.mem_erase.mp hx).1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
  simp only [labOne, Prod.mk.injEq, Fin.mk.injEq]
  simp only at h1 h2
  omega

theorem GBly_ne (m : ℕ) : GBly m t0 ≠ 0 := by
  unfold GBly
  exact Finset.prod_ne_zero_iff.mpr fun x _ => pow_ne_zero _ (gB_ne _ _)

theorem aLY_zero : aLY 0 = 0 := by
  unfold aLY
  refine Finset.sum_eq_zero fun x hx => ?_
  exfalso
  apply (Finset.mem_erase.mp hx).1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
  simp only [labOne, Prod.mk.injEq, Fin.mk.injEq]
  omega

theorem bLY_zero : bLY 0 = 0 := by simp [bLY, kacLabels]

end VOA.RRLower.LYGram
