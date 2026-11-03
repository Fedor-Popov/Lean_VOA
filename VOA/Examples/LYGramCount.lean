/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.LYGramOrders
import VOA.Examples.RRLowerPartition

/-!
# The Kac orders at the Lee–Yang point add up to the Rocha-Caridi count

With `n = 1 + m`, the exponents `aLY m` (Kac product at level `n`, `(1,1)` factor removed,
`h = 0`) and `bLY m` (Kac product at level `m`, `h = 1`) of `t - 2/5` satisfy

`rc n = p(n) - p(m) - aLY m + bLY m`,

where `rc n = Σ_k (-1)^k p(n - k(5k+3)/2)`.  Each of the four lines of vanishing Kac factors
(`5v = 2u + 3`, `2u = 5v + 3` at `h = 0`; `2u = 5v + 7`, `5v = 2u + 7` at `h = 1`) is matched
bijectively with one of the four classes of indices `k` (odd negative, odd positive, even
negative, even positive) by `line_sum`.

* `rc_eq_orders` — the identity above, proved outright.
-/

open Finset

noncomputable section

namespace VOA.RRLower.LYGram

open VOA.InverseDS.VirasoroVerma VOA.Classification.COne

/-- `FFLower.pp` (Verma partition count) agrees with `RRLower.pp`. -/
theorem ffpp_eq (k : ℕ) : (VOA.Classification.COne.FFLower.pp k : ℤ) = pp (k : ℤ) := by
  rw [pp_eq_card, VOA.Classification.COne.FFLower.pp, card_vermaPartitions_eq]

theorem ee_le_of_pp_ne {n : ℕ} {k : ℤ} (h : pp ((n : ℤ) - ee k) ≠ 0) : ee k ≤ n := by
  by_contra hc
  exact h (pp_of_neg (by omega))

/-- **Matching a line of Kac labels with a class of Rocha-Caridi indices.** -/
theorem line_sum (L off n : ℕ) (hn : n = L + off) (P : ℕ → ℕ → Prop) [DecidableRel P]
    (Q : ℤ → Prop) [DecidablePred Q] (U V : ℕ → ℕ) (K : ℤ → ℤ) (J : ℕ → ℕ) (Kinv : ℤ → ℕ)
    (hPJ : ∀ u v, P u v → u = U (J v) ∧ v = V (J v)) (hPU : ∀ j, P (U j) (V j))
    (hQK : ∀ k, Q k → k = K (Kinv k)) (hQK' : ∀ j : ℕ, Q (K j))
    (hK : ∀ j j' : ℕ, K j = K j' → j = j') (hVinj : ∀ j j', V j = V j' → j = j')
    (hU : ∀ j, 1 ≤ U j) (hV : ∀ j, 1 ≤ V j)
    (hee : ∀ j : ℕ, ee (K j) = (U j : ℤ) * (V j : ℤ) + off) :
    ∑ x ∈ kacLabels L, (if P (x.1.val + 1) (x.2.val + 1) then
        pp ((L : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) =
      ∑ k ∈ Ico (-(n : ℤ) - 1) ((n : ℤ) + 1), (if Q k then pp ((n : ℤ) - ee k) else 0) := by
  have hcond : ∀ x : Fin L × Fin L, (if P (x.1.val + 1) (x.2.val + 1) then
      pp ((L : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) ≠ 0 →
      P (x.1.val + 1) (x.2.val + 1) := by
    intro x hx
    by_contra hc
    exact hx (if_neg hc)
  refine Finset.sum_bij_ne_zero (fun x _ _ => K (J (x.2.val + 1))) ?_ ?_ ?_ ?_
  · intro x hx hne
    dsimp only
    have hp := hPJ _ _ (hcond x hne)
    have hmem := (Finset.mem_filter.mp hx).2
    have he := hee (J (x.2.val + 1))
    have hab := abs_le_ee (K (J (x.2.val + 1)))
    have huv : ((x.1.val + 1 : ℕ) : ℤ) * ((x.2.val + 1 : ℕ) : ℤ) ≤ L := by exact_mod_cast hmem
    rw [← hp.1, ← hp.2] at he
    rw [Finset.mem_Ico]
    rw [abs_le] at hab
    constructor <;> omega
  · intro x1 hx1 hne1 x2 hx2 hne2 heq
    have h1 := hPJ _ _ (hcond x1 hne1)
    have h2 := hPJ _ _ (hcond x2 hne2)
    have hj := hK _ _ heq
    rw [hj] at h1
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · intro k hk hg
    have hq : Q k := by by_contra hc; exact hg (if_neg hc)
    have hpp : pp ((n : ℤ) - ee k) ≠ 0 := by rwa [if_pos hq] at hg
    have hle := ee_le_of_pp_ne hpp
    set j := Kinv k with hj
    have hkj : k = K j := hQK k hq
    have he := hee j
    rw [← hkj] at he
    have huv : U j * V j ≤ L := by
      have : ((U j * V j : ℕ) : ℤ) ≤ L := by push_cast; omega
      exact_mod_cast this
    have hUL : U j ≤ L := le_trans (Nat.le_mul_of_pos_right _ (hV j)) huv
    have hVL : V j ≤ L := le_trans (Nat.le_mul_of_pos_left _ (hU j)) huv
    have hU1 := hU j
    have hV1 := hV j
    refine ⟨(⟨U j - 1, by omega⟩, ⟨V j - 1, by omega⟩), ?_, ?_, ?_⟩
    · rw [kacLabels, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only
      rw [Nat.sub_add_cancel hU1, Nat.sub_add_cancel hV1]
      exact huv
    · simp only
      rw [Nat.sub_add_cancel hU1, Nat.sub_add_cancel hV1, if_pos (hPU j)]
      have hc1 : (((U j - 1 : ℕ) : ℤ) + 1) = U j := by omega
      have hc2 : (((V j - 1 : ℕ) : ℤ) + 1) = V j := by omega
      rw [hc1, hc2, show (L : ℤ) - (U j : ℤ) * (V j : ℤ) = (n : ℤ) - ee k by rw [he]; push_cast [hn]; ring]
      exact hpp
    · simp only
      rw [Nat.sub_add_cancel hV1, hkj]
      have hp := hPJ _ _ (hPU j)
      exact congrArg K (congrArg Nat.cast (hVinj _ _ hp.2.symm))
  · intro x hx hne
    have hP := hcond x hne
    have hp := hPJ _ _ hP
    rw [if_pos hP, if_pos (hQK' _)]
    congr 1
    have he := hee (J (x.2.val + 1))
    rw [he]
    have e1 : ((x.1.val : ℤ) + 1) = ((U (J (x.2.val + 1)) : ℕ) : ℤ) := by
      have := congrArg (fun z : ℕ => (z : ℤ)) hp.1; push_cast at this; exact this
    have e2 : ((x.2.val : ℤ) + 1) = ((V (J (x.2.val + 1)) : ℕ) : ℤ) := by
      have := congrArg (fun z : ℕ => (z : ℤ)) hp.2; push_cast at this; exact this
    rw [e1, e2, hn]; push_cast; ring

theorem ee_param {k : ℤ} {r : ℤ} (h : 2 * r = k * (5 * k + 3)) : ee k = r := by
  have := two_mul_ee k
  omega

/-- Line `5v = 2u + 3` (level `n`, `h = 0`) ↔ odd `k ≤ -1`. -/
theorem lineA1 (n : ℕ) :
    ∑ x ∈ kacLabels n, (if 5 * (x.2.val + 1) = 2 * (x.1.val + 1) + 3 then
        pp ((n : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) =
      ∑ k ∈ Ico (-(n : ℤ) - 1) ((n : ℤ) + 1),
        (if k % 2 ≠ 0 ∧ k ≤ -1 then pp ((n : ℤ) - ee k) else 0) := by
  refine line_sum n 0 n (by ring) (fun u v => 5 * v = 2 * u + 3) (fun k => k % 2 ≠ 0 ∧ k ≤ -1)
    (fun j => 5 * j + 1) (fun j => 2 * j + 1) (fun j => -(2 * j + 1)) (fun v => v / 2)
    (fun k => ((-k - 1) / 2).toNat) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v h; simp only at h ⊢; omega
  · intro j; simp only; omega
  · intro k hk; simp only at hk ⊢; omega
  · intro j; simp only; omega
  · intro j j' h; simp only at h; omega
  · intro j j' h; simp only at h; omega
  · intro j; simp only; omega
  · intro j; simp only; omega
  · intro j; simp only; push_cast; apply ee_param; ring

/-- Line `2u = 5v + 3` (level `n`, `h = 0`) ↔ odd `k ≥ 1`. -/
theorem lineA2 (n : ℕ) :
    ∑ x ∈ kacLabels n, (if 2 * (x.1.val + 1) = 5 * (x.2.val + 1) + 3 then
        pp ((n : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) =
      ∑ k ∈ Ico (-(n : ℤ) - 1) ((n : ℤ) + 1),
        (if k % 2 ≠ 0 ∧ 1 ≤ k then pp ((n : ℤ) - ee k) else 0) := by
  refine line_sum n 0 n (by ring) (fun u v => 2 * u = 5 * v + 3) (fun k => k % 2 ≠ 0 ∧ 1 ≤ k)
    (fun j => 5 * j + 4) (fun j => 2 * j + 1) (fun j => 2 * j + 1) (fun v => v / 2)
    (fun k => ((k - 1) / 2).toNat) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v h; simp only at h ⊢; omega
  · intro j; simp only; omega
  · intro k hk; simp only at hk ⊢; omega
  · intro j; simp only; omega
  · intro j j' h; simp only at h; omega
  · intro j j' h; simp only at h; omega
  · intro j; simp only; omega
  · intro j; simp only; omega
  · intro j; simp only; push_cast; apply ee_param; ring

/-- Line `2u = 5v + 7` (level `m`, `h = 1`) ↔ even `k ≤ -2`. -/
theorem lineB1 (m : ℕ) :
    ∑ x ∈ kacLabels m, (if 2 * (x.1.val + 1) = 5 * (x.2.val + 1) + 7 then
        pp ((m : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) =
      ∑ k ∈ Ico (-((1 + m : ℕ) : ℤ) - 1) (((1 + m : ℕ) : ℤ) + 1),
        (if k % 2 = 0 ∧ k ≤ -2 then pp (((1 + m : ℕ) : ℤ) - ee k) else 0) := by
  refine line_sum m 1 (1 + m) (by ring) (fun u v => 2 * u = 5 * v + 7)
    (fun k => k % 2 = 0 ∧ k ≤ -2)
    (fun j => 5 * j + 6) (fun j => 2 * j + 1) (fun j => -(2 * j + 2)) (fun v => v / 2)
    (fun k => ((-k - 2) / 2).toNat) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v h; simp only at h ⊢; omega
  · intro j; simp only; omega
  · intro k hk; simp only at hk ⊢; omega
  · intro j; simp only; omega
  · intro j j' h; simp only at h; omega
  · intro j j' h; simp only at h; omega
  · intro j; simp only; omega
  · intro j; simp only; omega
  · intro j; simp only; push_cast; apply ee_param; ring

/-- Line `5v = 2u + 7` (level `m`, `h = 1`) ↔ even `k ≥ 2`. -/
theorem lineB2 (m : ℕ) :
    ∑ x ∈ kacLabels m, (if 5 * (x.2.val + 1) = 2 * (x.1.val + 1) + 7 then
        pp ((m : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) =
      ∑ k ∈ Ico (-((1 + m : ℕ) : ℤ) - 1) (((1 + m : ℕ) : ℤ) + 1),
        (if k % 2 = 0 ∧ 2 ≤ k then pp (((1 + m : ℕ) : ℤ) - ee k) else 0) := by
  refine line_sum m 1 (1 + m) (by ring) (fun u v => 5 * v = 2 * u + 7)
    (fun k => k % 2 = 0 ∧ 2 ≤ k)
    (fun j => 5 * j + 4) (fun j => 2 * j + 3) (fun j => 2 * j + 2) (fun v => (v - 3) / 2)
    (fun k => ((k - 2) / 2).toNat) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v h; simp only at h ⊢; omega
  · intro j; simp only; omega
  · intro k hk; simp only at hk ⊢; omega
  · intro j; simp only; omega
  · intro j j' h; simp only at h; omega
  · intro j j' h; simp only at h; omega
  · intro j; simp only; omega
  · intro j; simp only; omega
  · intro j; simp only; push_cast; apply ee_param; ring

/-- The term of a Kac-label sum, cast to `ℤ`. -/
theorem term_cast (L : ℕ) (x : Fin L × Fin L) (hx : x ∈ kacLabels L) (e : ℕ) :
    ((VOA.Classification.COne.FFLower.pp (L - (x.1.val + 1) * (x.2.val + 1)) * e : ℕ) : ℤ) =
      pp ((L : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) * e := by
  have hmem := (Finset.mem_filter.mp hx).2
  push_cast
  rw [ffpp_eq, Nat.cast_sub hmem]
  push_cast
  ring

theorem aLY_cast (m : ℕ) :
    (aLY m : ℤ) + (VOA.Classification.COne.FFLower.pp m : ℤ) =
      ∑ k ∈ Ico (-((1 + m : ℕ) : ℤ) - 1) (((1 + m : ℕ) : ℤ) + 1),
        ((if k % 2 ≠ 0 ∧ k ≤ -1 then pp (((1 + m : ℕ) : ℤ) - ee k) else 0) +
          (if k % 2 ≠ 0 ∧ 1 ≤ k then pp (((1 + m : ℕ) : ℤ) - ee k) else 0)) := by
  rw [Finset.sum_add_distrib, ← lineA1, ← lineA2, ← Finset.sum_add_distrib]
  have hlab : VOA.Classification.COne.FFLower.pp m =
      VOA.Classification.COne.FFLower.pp (1 + m - ((VOA.Classification.COne.FFLower.labOne 1 m (by omega)).1.val + 1) *
        ((VOA.Classification.COne.FFLower.labOne 1 m (by omega)).2.val + 1)) *
        eA ((VOA.Classification.COne.FFLower.labOne 1 m (by omega)).1.val + 1) ((VOA.Classification.COne.FFLower.labOne 1 m (by omega)).2.val + 1) := by
    simp only [VOA.Classification.COne.FFLower.labOne, eA]
    norm_num
  rw [hlab, aLY]
  push_cast
  rw [Finset.sum_erase_add _ _ (VOA.Classification.COne.FFLower.labOne_mem 1 m (by omega))]
  refine Finset.sum_congr rfl fun x hx => ?_
  have := term_cast (1 + m) x hx (eA (x.1.val + 1) (x.2.val + 1))
  push_cast at this
  rw [this]
  unfold eA
  split_ifs <;> push_cast <;> ring

theorem bLY_cast (m : ℕ) :
    (bLY m : ℤ) =
      ∑ k ∈ Ico (-((1 + m : ℕ) : ℤ) - 1) (((1 + m : ℕ) : ℤ) + 1),
        ((if k % 2 = 0 ∧ k ≤ -2 then pp (((1 + m : ℕ) : ℤ) - ee k) else 0) +
          (if k % 2 = 0 ∧ 2 ≤ k then pp (((1 + m : ℕ) : ℤ) - ee k) else 0)) := by
  rw [Finset.sum_add_distrib, ← lineB1, ← lineB2, ← Finset.sum_add_distrib, bLY]
  push_cast
  refine Finset.sum_congr rfl fun x hx => ?_
  have := term_cast m x hx (eB (x.1.val + 1) (x.2.val + 1))
  push_cast at this
  rw [this]
  unfold eB
  split_ifs <;> push_cast <;> ring

theorem sgn_split (k X : ℤ) :
    sgn k * X = (if k = 0 then X else 0) -
      ((if k % 2 ≠ 0 ∧ k ≤ -1 then X else 0) + (if k % 2 ≠ 0 ∧ 1 ≤ k then X else 0)) +
      ((if k % 2 = 0 ∧ k ≤ -2 then X else 0) + (if k % 2 = 0 ∧ 2 ≤ k then X else 0)) := by
  unfold sgn
  split_ifs <;> omega

/-- **The Kac orders at the Lee–Yang point give the Rocha-Caridi count**:
`rc (1 + m) = p(1 + m) - p(m) - aLY m + bLY m`. -/
theorem rc_eq_orders (m : ℕ) :
    rc (1 + m) = (VOA.Classification.COne.FFLower.pp (1 + m) : ℤ) -
      ((aLY m : ℤ) + (VOA.Classification.COne.FFLower.pp m : ℤ)) + (bLY m : ℤ) := by
  rw [aLY_cast, bLY_cast, rc]
  simp only [sgn_split]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  rw [if_pos (by rw [Finset.mem_Ico]; omega), ffpp_eq]
  simp [ee]

end VOA.RRLower.LYGram
