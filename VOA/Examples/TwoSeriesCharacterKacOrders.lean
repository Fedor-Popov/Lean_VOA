/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.FeiginFuchsLower

/-!
# Orders of the Kac factors at the `(2, 2n+3)` point of the vacuum curve

The generalisation of `LYGramOrders` (the case `n = 1`) to every member of the `(2, 2n+3)`
series.  Along the curve `c(t) = 13 - 6t - 6/t`, `h = h_{1,1}(t) = 0`, the minimal-model point is
`t₀ = 2/(2n+3)`: `c(t₀) = c_{2,2n+3}`.  With `Q = 2n+3`:

* `factorA` — `h_{1,1}(t) - h_{u,v}(t) = (t - t₀)^{eA u v} · gA u v t`, where `eA u v` counts the
  conditions `Qv = 2u + 2n + 1`, `2u = Qv + 2n + 1`;
* `factorB` — `h_{1,1}(t) + 1 - h_{u,v}(t) = (t - t₀)^{eB u v} · gB u v t`, where `eB u v` counts
  `2u = Qv + 2n + 5`, `Qv = 2u + 2n + 5`;
* `kwpRest_eval_q` / `gram_shift_det_q` — the two Kac products, with exponents `aQ n m`,
  `bQ n m`, and reduced factors continuous and nonzero at `t₀`.

All proved, no hypotheses.
-/

open Finset

noncomputable section

namespace VOA.TwoSeriesCharacter.KacGram

open VOA.InverseDS.VirasoroVerma VOA.VirasoroScreening VOA.Classification.COne
open VOA.Classification.COne.FFLower
open Polynomial
open scoped Classical

variable (n : ℕ)

/-- `Q = 2n + 3` in `ℂ`. -/
def QC : ℂ := ((2 * n + 3 : ℕ) : ℂ)

theorem QC_ne : QC n ≠ 0 := by
  unfold QC; exact_mod_cast (by omega : 2 * n + 3 ≠ 0)

/-- The minimal-model parameter on the vacuum curve. -/
def t0 : ℂ := 2 / QC n

theorem t0_ne : t0 n ≠ 0 := div_ne_zero two_ne_zero (QC_ne n)

theorem weight_one (t : ℂ) : vermaBSAWeight 1 t = 0 := by
  simp [vermaBSAWeight]

/-- Order of `h_{1,1}(t) - h_{u,v}(t)` at `t₀`. -/
def eA (u v : ℕ) : ℕ :=
  (if (2 * n + 3) * v = 2 * u + 2 * n + 1 then 1 else 0) +
    (if 2 * u = (2 * n + 3) * v + 2 * n + 1 then 1 else 0)

/-- Reduced factor of `h_{1,1}(t) - h_{u,v}(t)`. -/
def gA (u v : ℕ) (t : ℂ) : ℂ :=
  (if (2 * n + 3) * v = 2 * u + 2 * n + 1 then (1 - (u : ℂ)) else ((1 - (u : ℂ)) * t + ((v : ℂ) - 1))) *
    (if 2 * u = (2 * n + 3) * v + 2 * n + 1 then (1 + (u : ℂ))
      else ((1 + (u : ℂ)) * t - ((v : ℂ) + 1))) / (4 * t)

theorem cast_eq {a b : ℕ} (h : a = b) : (a : ℂ) = (b : ℂ) := by rw [h]

theorem factorA (u v : ℕ) (t : ℂ) (ht : t ≠ 0) :
    vermaBSAWeight 1 t - fusionKacWeight u v t = (t - t0 n) ^ eA n u v * gA n u v t := by
  have hQ := QC_ne n
  have key : vermaBSAWeight 1 t - fusionKacWeight u v t =
      ((1 - (u : ℂ)) * t + ((v : ℂ) - 1)) * ((1 + (u : ℂ)) * t - ((v : ℂ) + 1)) / (4 * t) := by
    simp only [vermaBSAWeight, fusionKacWeight]; push_cast; field_simp; ring
  rw [key]
  unfold eA gA
  by_cases h1 : (2 * n + 3) * v = 2 * u + 2 * n + 1 <;>
    by_cases h2 : 2 * u = (2 * n + 3) * v + 2 * n + 1
  · exfalso
    have : (2 * n + 3) * v + 2 * u = 2 * u + (2 * n + 3) * v := by ring
    omega
  · have e1 := cast_eq h1
    push_cast at e1
    simp only [if_pos h1, if_neg h2]
    rw [mul_div_assoc', pow_one]
    congr 1
    have hfac : ((1 - (u : ℂ)) * t + ((v : ℂ) - 1)) = (t - t0 n) * (1 - (u : ℂ)) := by
      have hQ' : (2 * (n : ℂ) + 3) ≠ 0 := by
        have := QC_ne n; simp only [QC] at this; push_cast at this; exact this
      simp only [t0, QC]; push_cast; field_simp
      first | linear_combination e1 | linear_combination -e1
    rw [hfac]; ring
  · have e2 := cast_eq h2
    push_cast at e2
    simp only [if_neg h1, if_pos h2]
    rw [mul_div_assoc', pow_one]
    congr 1
    have hfac : ((1 + (u : ℂ)) * t - ((v : ℂ) + 1)) = (t - t0 n) * (1 + (u : ℂ)) := by
      have hQ' : (2 * (n : ℂ) + 3) ≠ 0 := by
        have := QC_ne n; simp only [QC] at this; push_cast at this; exact this
      simp only [t0, QC]; push_cast; field_simp
      first | linear_combination e2 | linear_combination -e2
    rw [hfac]; ring
  · simp only [if_neg h1, if_neg h2]
    ring

theorem gA_cont (u v : ℕ) : ContinuousAt (gA n u v) (t0 n) := by
  unfold gA
  refine ContinuousAt.div (ContinuousAt.mul ?_ ?_) (continuousAt_const.mul continuousAt_id)
    (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) (t0_ne n))
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).add continuousAt_const
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).sub continuousAt_const

theorem gA_ne (u v : ℕ) (hne : ¬ (u = 1 ∧ v = 1)) : gA n u v (t0 n) ≠ 0 := by
  have hQ := QC_ne n
  unfold gA
  refine div_ne_zero (mul_ne_zero ?_ ?_) (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) (t0_ne n))
  · split_ifs with h1
    · intro h
      have hu : (u : ℂ) = 1 := by linear_combination -h
      have hu' : u = 1 := by exact_mod_cast hu
      subst hu'
      apply hne ⟨rfl, ?_⟩
      rcases Nat.lt_or_ge v 1 with hv | hv
      · interval_cases v; omega
      · rcases Nat.eq_or_lt_of_le hv with hv | hv
        · exact hv.symm
        · exfalso; nlinarith
    · intro h
      apply h1
      have : (((2 * n + 3) * v : ℕ) : ℂ) = ((2 * u + 2 * n + 1 : ℕ) : ℂ) := by
        simp only [t0, QC] at h hQ
        field_simp at h
        push_cast at h ⊢
        linear_combination h
      exact_mod_cast this
  · split_ifs with h2
    · intro h
      have : ((1 + u : ℕ) : ℂ) = 0 := by push_cast; exact h
      have := Nat.cast_eq_zero.mp this
      omega
    · intro h
      apply h2
      have : ((2 * u : ℕ) : ℂ) = (((2 * n + 3) * v + 2 * n + 1 : ℕ) : ℂ) := by
        simp only [t0, QC] at h hQ
        field_simp at h
        push_cast at h ⊢
        linear_combination h
      exact_mod_cast this

/-- Order of `h_{1,1}(t) + 1 - h_{u,v}(t)` at `t₀`. -/
def eB (u v : ℕ) : ℕ :=
  (if 2 * u = (2 * n + 3) * v + 2 * n + 5 then 1 else 0) +
    (if (2 * n + 3) * v = 2 * u + 2 * n + 5 then 1 else 0)

/-- Reduced factor of `h_{1,1}(t) + 1 - h_{u,v}(t)`. -/
def gB (u v : ℕ) (t : ℂ) : ℂ :=
  (if 2 * u = (2 * n + 3) * v + 2 * n + 5 then (1 - (u : ℂ))
      else ((1 - (u : ℂ)) * t + (1 + (v : ℂ)))) *
    (if (2 * n + 3) * v = 2 * u + 2 * n + 5 then (1 + (u : ℂ))
      else ((1 + (u : ℂ)) * t + (1 - (v : ℂ)))) / (4 * t)

theorem factorB (u v : ℕ) (t : ℂ) (ht : t ≠ 0) :
    vermaBSAWeight 1 t + ((1 : ℕ) : ℂ) - fusionKacWeight u v t =
      (t - t0 n) ^ eB n u v * gB n u v t := by
  have hQ := QC_ne n
  have key : vermaBSAWeight 1 t + ((1 : ℕ) : ℂ) - fusionKacWeight u v t =
      ((1 - (u : ℂ)) * t + (1 + (v : ℂ))) * ((1 + (u : ℂ)) * t + (1 - (v : ℂ))) / (4 * t) := by
    simp only [vermaBSAWeight, fusionKacWeight]; push_cast; field_simp; ring
  rw [key]
  unfold eB gB
  by_cases h1 : 2 * u = (2 * n + 3) * v + 2 * n + 5 <;>
    by_cases h2 : (2 * n + 3) * v = 2 * u + 2 * n + 5
  · omega
  · have e1 := cast_eq h1
    push_cast at e1
    simp only [if_pos h1, if_neg h2]
    rw [mul_div_assoc', pow_one]
    congr 1
    have hfac : ((1 - (u : ℂ)) * t + (1 + (v : ℂ))) = (t - t0 n) * (1 - (u : ℂ)) := by
      have hQ' : (2 * (n : ℂ) + 3) ≠ 0 := by
        have := QC_ne n; simp only [QC] at this; push_cast at this; exact this
      simp only [t0, QC]; push_cast; field_simp
      first | linear_combination e1 | linear_combination -e1
    rw [hfac]; ring
  · have e2 := cast_eq h2
    push_cast at e2
    simp only [if_neg h1, if_pos h2]
    rw [mul_div_assoc', pow_one]
    congr 1
    have hfac : ((1 + (u : ℂ)) * t + (1 - (v : ℂ))) = (t - t0 n) * (1 + (u : ℂ)) := by
      have hQ' : (2 * (n : ℂ) + 3) ≠ 0 := by
        have := QC_ne n; simp only [QC] at this; push_cast at this; exact this
      simp only [t0, QC]; push_cast; field_simp
      first | linear_combination e2 | linear_combination -e2
    rw [hfac]; ring
  · simp only [if_neg h1, if_neg h2]
    ring

theorem gB_cont (u v : ℕ) : ContinuousAt (gB n u v) (t0 n) := by
  unfold gB
  refine ContinuousAt.div (ContinuousAt.mul ?_ ?_) (continuousAt_const.mul continuousAt_id)
    (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) (t0_ne n))
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).add continuousAt_const
  · split_ifs
    · exact continuousAt_const
    · exact (continuousAt_const.mul continuousAt_id).add continuousAt_const

theorem gB_ne (u v : ℕ) : gB n u v (t0 n) ≠ 0 := by
  have hQ := QC_ne n
  unfold gB
  refine div_ne_zero (mul_ne_zero ?_ ?_) (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) (t0_ne n))
  · split_ifs with h1
    · intro h
      have hu : (u : ℂ) = 1 := by linear_combination -h
      have hu' : u = 1 := by exact_mod_cast hu
      omega
    · intro h
      apply h1
      have : ((2 * u : ℕ) : ℂ) = (((2 * n + 3) * v + 2 * n + 5 : ℕ) : ℂ) := by
        simp only [t0, QC] at h hQ
        field_simp at h
        push_cast at h ⊢
        linear_combination -h
      exact_mod_cast this
  · split_ifs with h2
    · intro h
      have : ((1 + u : ℕ) : ℂ) = 0 := by push_cast; exact h
      have := Nat.cast_eq_zero.mp this
      omega
    · intro h
      apply h2
      have : (((2 * n + 3) * v : ℕ) : ℂ) = ((2 * u + 2 * n + 5 : ℕ) : ℂ) := by
        simp only [t0, QC] at h hQ
        field_simp at h
        push_cast at h ⊢
        linear_combination -h
      exact_mod_cast this

theorem prod_order0 {α : Type*} (s : Finset α) (F g : α → ℂ) (e k : α → ℕ) (t a : ℂ)
    (hF : ∀ x ∈ s, F x = (t - a) ^ e x * g x) :
    ∏ x ∈ s, F x ^ k x = (t - a) ^ (∑ x ∈ s, k x * e x) * ∏ x ∈ s, g x ^ k x := by
  rw [Finset.prod_congr rfl (fun x hx => by rw [hF x hx, mul_pow, ← pow_mul]),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The exponent of `t - t₀` in the Kac product at level `1 + m` with the `(1,1)` factor
removed. -/
def aQ (m : ℕ) : ℕ :=
  ∑ x ∈ (kacLabels (1 + m)).erase (labOne 1 m (by omega)),
    VOA.Classification.COne.FFLower.pp (1 + m - (x.1.val + 1) * (x.2.val + 1)) *
      eA n (x.1.val + 1) (x.2.val + 1)

/-- The exponent of `t - t₀` in the shifted Kac product at level `m` (weight `h = 1`). -/
def bQ (m : ℕ) : ℕ :=
  ∑ x ∈ kacLabels m, VOA.Classification.COne.FFLower.pp (m - (x.1.val + 1) * (x.2.val + 1)) *
    eB n (x.1.val + 1) (x.2.val + 1)

/-- The reduced remaining Kac product. -/
def GRq (m : ℕ) (t : ℂ) : ℂ :=
  ∏ x ∈ (kacLabels (1 + m)).erase (labOne 1 m (by omega)),
    gA n (x.1.val + 1) (x.2.val + 1) t ^
      VOA.Classification.COne.FFLower.pp (1 + m - (x.1.val + 1) * (x.2.val + 1))

/-- The reduced shifted Kac product. -/
def GBq (m : ℕ) (t : ℂ) : ℂ :=
  ∏ x ∈ kacLabels m, gB n (x.1.val + 1) (x.2.val + 1) t ^
    VOA.Classification.COne.FFLower.pp (m - (x.1.val + 1) * (x.2.val + 1))

theorem kwpRest_eval_q (m : ℕ) (t : ℂ) (ht : t ≠ 0) :
    (kwpRest t 1 m (by omega)).eval (vermaBSAWeight 1 t) = (t - t0 n) ^ aQ n m * GRq n m t := by
  have hpp : ∀ k, Fintype.card (VermaPartitions k) = VOA.Classification.COne.FFLower.pp k :=
    fun _ => rfl
  rw [kwpRest, eval_prod, aQ, GRq]
  simp only [eval_pow, eval_sub, eval_X, eval_C, hpp]
  refine prod_order0 _ _ _ _ _ t (t0 n) (fun x _ => ?_)
  have := factorA n (x.1.val + 1) (x.2.val + 1) t ht
  push_cast at this
  exact this

theorem gram_shift_det_q (m : ℕ) (t : ℂ) (ht : t ≠ 0) :
    (vermaGramMatrix (vermaBSACharge t) (vermaBSAWeight 1 t + ((1 : ℕ) : ℂ)) m).det =
      (∏ w : VermaPartitions m, vermaDiagonalContraction w.val) *
        ((t - t0 n) ^ bQ n m * GBq n m t) := by
  have hpp : ∀ k, Fintype.card (VermaPartitions k) = VOA.Classification.COne.FFLower.pp k :=
    fun _ => rfl
  rw [kac_determinant_eval t ht, kacWeightProduct, eval_prod, bQ, GBq]
  simp only [eval_pow, eval_sub, eval_X, eval_C, hpp]
  congr 1
  refine prod_order0 _ _ _ _ _ t (t0 n) (fun x _ => ?_)
  have := factorB n (x.1.val + 1) (x.2.val + 1) t ht
  push_cast at this ⊢
  exact this

theorem GRq_cont (m : ℕ) : ContinuousAt (GRq n m) (t0 n) := by
  unfold GRq
  exact cAt_prod _ _ _ fun x _ => (gA_cont n _ _).pow _

theorem GBq_cont (m : ℕ) : ContinuousAt (GBq n m) (t0 n) := by
  unfold GBq
  exact cAt_prod _ _ _ fun x _ => (gB_cont n _ _).pow _

theorem GRq_ne (m : ℕ) : GRq n m (t0 n) ≠ 0 := by
  unfold GRq
  refine Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero _ (gA_ne n _ _ ?_)
  rintro ⟨h1, h2⟩
  apply (Finset.mem_erase.mp hx).1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
  simp only [labOne, Prod.mk.injEq, Fin.mk.injEq]
  simp only at h1 h2
  omega

theorem GBq_ne (m : ℕ) : GBq n m (t0 n) ≠ 0 := by
  unfold GBq
  exact Finset.prod_ne_zero_iff.mpr fun x _ => pow_ne_zero _ (gB_ne n _ _)

theorem aQ_zero : aQ n 0 = 0 := by
  unfold aQ
  refine Finset.sum_eq_zero fun x hx => ?_
  exfalso
  apply (Finset.mem_erase.mp hx).1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
  simp only [labOne, Prod.mk.injEq, Fin.mk.injEq]
  omega

theorem bQ_zero : bQ n 0 = 0 := by simp [bQ, kacLabels]

end VOA.TwoSeriesCharacter.KacGram
