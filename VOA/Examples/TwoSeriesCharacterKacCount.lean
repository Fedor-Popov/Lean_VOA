/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterKacOrders
import VOA.Examples.LYGramCount

/-!
# The Kac orders at the `(2, 2n+3)` point add up to the Rocha-Caridi count

The generalisation of `LYGramCount` (the case `n = 1`).  With `Q = 2n+3`, the Rocha-Caridi vacuum
character of `M(2, Q)` is `(q)_∞⁻¹ Σ_{k ∈ ℤ} (-1)^k q^{eeq n k}`, `eeq n k = k(Qk + Q - 2)/2`;
its coefficients are

`rcq n N = Σ_k (-1)^k p(N - eeq n k)`.

* `rcq_eq_orders` — `rcq n (1+m) = p(1+m) - p(m) - aQ n m + bQ n m`: each of the four lines of
  vanishing Kac factors is matched with one class of indices `k` (`line_sumQ`).

All proved, no hypotheses.
-/

open Finset

noncomputable section

namespace VOA.TwoSeriesCharacter.KacGram

open VOA.InverseDS.VirasoroVerma VOA.Classification.COne

variable (n : ℕ)

/-- The Rocha-Caridi exponent `k(Qk + Q - 2)/2`, `Q = 2n+3`. -/
def eeq (k : ℤ) : ℤ := k * ((2 * n + 3) * k + (2 * n + 1)) / 2

theorem two_mul_eeq (k : ℤ) : 2 * eeq n k = k * ((2 * n + 3) * k + (2 * n + 1)) := by
  unfold eeq
  have hev : Even (k * ((2 * n + 3) * k + (2 * n + 1))) := by
    have h1 : k * ((2 * n + 3) * k + (2 * n + 1)) =
        k * (k + 1) + 2 * (((n : ℤ) + 1) * k * k + n * k) := by ring
    rw [h1]
    exact (Int.even_mul_succ_self k).add (even_two_mul _)
  exact Int.mul_ediv_cancel' hev.two_dvd

theorem eeq_param {k r : ℤ} (h : 2 * r = k * ((2 * n + 3) * k + (2 * n + 1))) : eeq n k = r := by
  have := two_mul_eeq n k
  omega

theorem abs_le_eeq (k : ℤ) : |k| ≤ eeq n k := by
  have h := two_mul_eeq n k
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  rcases le_or_gt 0 k with hk | hk
  · rw [abs_of_nonneg hk]
    have h1 : k ≤ k * k := by nlinarith
    nlinarith [mul_nonneg hn hk, mul_nonneg (mul_nonneg hn hk) hk]
  · rw [abs_of_neg hk]
    have h1 : 0 ≤ k * (k + 1) := by nlinarith
    nlinarith [mul_nonneg (by positivity : (0 : ℤ) ≤ 2 * n + 3) h1]

/-- The Rocha-Caridi coefficient `Σ_k (-1)^k p(N - eeq n k)` (terms with `|k| > N` vanish). -/
def rcq (N : ℕ) : ℤ := ∑ k ∈ Ico (-(N : ℤ) - 1) ((N : ℤ) + 1), VOA.RRLower.sgn k * VOA.RRLower.pp ((N : ℤ) - eeq n k)

theorem eeq_le_of_pp_ne {N : ℕ} {k : ℤ} (h : VOA.RRLower.pp ((N : ℤ) - eeq n k) ≠ 0) : eeq n k ≤ N := by
  by_contra hc
  exact h (VOA.RRLower.pp_of_neg (by omega))

/-- **Matching a line of Kac labels with a class of Rocha-Caridi indices.** -/
theorem line_sumQ (L off N : ℕ) (hN : N = L + off) (P : ℕ → ℕ → Prop) [DecidableRel P]
    (Qp : ℤ → Prop) [DecidablePred Qp] (U V : ℕ → ℕ) (K : ℤ → ℤ) (J : ℕ → ℕ) (Kinv : ℤ → ℕ)
    (hPJ : ∀ u v, P u v → u = U (J v) ∧ v = V (J v)) (hPU : ∀ j, P (U j) (V j))
    (hQK : ∀ k, Qp k → k = K (Kinv k)) (hQK' : ∀ j : ℕ, Qp (K j))
    (hK : ∀ j j' : ℕ, K j = K j' → j = j') (hVinj : ∀ j j', V j = V j' → j = j')
    (hU : ∀ j, 1 ≤ U j) (hV : ∀ j, 1 ≤ V j)
    (hee : ∀ j : ℕ, eeq n (K j) = (U j : ℤ) * (V j : ℤ) + off) :
    ∑ x ∈ kacLabels L, (if P (x.1.val + 1) (x.2.val + 1) then
        VOA.RRLower.pp ((L : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) =
      ∑ k ∈ Ico (-(N : ℤ) - 1) ((N : ℤ) + 1), (if Qp k then VOA.RRLower.pp ((N : ℤ) - eeq n k) else 0) := by
  have hcond : ∀ x : Fin L × Fin L, (if P (x.1.val + 1) (x.2.val + 1) then
      VOA.RRLower.pp ((L : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) ≠ 0 →
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
    have hab := abs_le_eeq n (K (J (x.2.val + 1)))
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
    have hq : Qp k := by by_contra hc; exact hg (if_neg hc)
    have hpp : VOA.RRLower.pp ((N : ℤ) - eeq n k) ≠ 0 := by rwa [if_pos hq] at hg
    have hle := eeq_le_of_pp_ne n hpp
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
      rw [hc1, hc2, show (L : ℤ) - (U j : ℤ) * (V j : ℤ) = (N : ℤ) - eeq n k by
        rw [he]; push_cast [hN]; ring]
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
    rw [e1, e2, hN]; push_cast; ring

/-- Line `Qv = 2u + 2n + 1` (level `L`, `h = 0`) ↔ odd `k ≤ -1`. -/
theorem lineA1 (L : ℕ) :
    ∑ x ∈ kacLabels L, (if (2 * n + 3) * (x.2.val + 1) = 2 * (x.1.val + 1) + 2 * n + 1 then
        VOA.RRLower.pp ((L : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) =
      ∑ k ∈ Ico (-(L : ℤ) - 1) ((L : ℤ) + 1),
        (if k % 2 ≠ 0 ∧ k ≤ -1 then VOA.RRLower.pp ((L : ℤ) - eeq n k) else 0) := by
  refine line_sumQ n L 0 L (by ring) (fun u v => (2 * n + 3) * v = 2 * u + 2 * n + 1)
    (fun k => k % 2 ≠ 0 ∧ k ≤ -1)
    (fun j => (2 * n + 3) * j + 1) (fun j => 2 * j + 1) (fun j => -(2 * j + 1)) (fun v => v / 2)
    (fun k => ((-k - 1) / 2).toNat) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v h
    simp only at h ⊢
    obtain ⟨w, rfl | rfl⟩ := Nat.even_or_odd' v
    · exfalso; ring_nf at h; omega
    · rw [show (2 * w + 1) / 2 = w by omega]
      exact ⟨by ring_nf at h ⊢; omega, rfl⟩
  · intro j; simp only; ring
  · intro k hk; simp only at hk ⊢; omega
  · intro j; simp only; omega
  · intro j j' h; simp only at h; omega
  · intro j j' h; simp only at h; omega
  · intro j; simp only; omega
  · intro j; simp only; omega
  · intro j; simp only; push_cast; apply eeq_param; ring

/-- Line `2u = Qv + 2n + 1` (level `L`, `h = 0`) ↔ odd `k ≥ 1`. -/
theorem lineA2 (L : ℕ) :
    ∑ x ∈ kacLabels L, (if 2 * (x.1.val + 1) = (2 * n + 3) * (x.2.val + 1) + 2 * n + 1 then
        VOA.RRLower.pp ((L : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) =
      ∑ k ∈ Ico (-(L : ℤ) - 1) ((L : ℤ) + 1),
        (if k % 2 ≠ 0 ∧ 1 ≤ k then VOA.RRLower.pp ((L : ℤ) - eeq n k) else 0) := by
  refine line_sumQ n L 0 L (by ring) (fun u v => 2 * u = (2 * n + 3) * v + 2 * n + 1)
    (fun k => k % 2 ≠ 0 ∧ 1 ≤ k)
    (fun j => (2 * n + 3) * j + 2 * n + 2) (fun j => 2 * j + 1) (fun j => 2 * j + 1)
    (fun v => v / 2) (fun k => ((k - 1) / 2).toNat) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v h
    simp only at h ⊢
    obtain ⟨w, rfl | rfl⟩ := Nat.even_or_odd' v
    · exfalso; ring_nf at h; omega
    · rw [show (2 * w + 1) / 2 = w by omega]
      exact ⟨by ring_nf at h ⊢; omega, rfl⟩
  · intro j; simp only; ring
  · intro k hk; simp only at hk ⊢; omega
  · intro j; simp only; omega
  · intro j j' h; simp only at h; omega
  · intro j j' h; simp only at h; omega
  · intro j; simp only; omega
  · intro j; simp only; omega
  · intro j; simp only; push_cast; apply eeq_param; ring

/-- Line `2u = Qv + 2n + 5` (level `m`, `h = 1`) ↔ even `k ≤ -2`. -/
theorem lineB1 (m : ℕ) :
    ∑ x ∈ kacLabels m, (if 2 * (x.1.val + 1) = (2 * n + 3) * (x.2.val + 1) + 2 * n + 5 then
        VOA.RRLower.pp ((m : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) =
      ∑ k ∈ Ico (-((1 + m : ℕ) : ℤ) - 1) (((1 + m : ℕ) : ℤ) + 1),
        (if k % 2 = 0 ∧ k ≤ -2 then VOA.RRLower.pp (((1 + m : ℕ) : ℤ) - eeq n k) else 0) := by
  refine line_sumQ n m 1 (1 + m) (by ring) (fun u v => 2 * u = (2 * n + 3) * v + 2 * n + 5)
    (fun k => k % 2 = 0 ∧ k ≤ -2)
    (fun j => (2 * n + 3) * j + 2 * n + 4) (fun j => 2 * j + 1) (fun j => -(2 * j + 2))
    (fun v => v / 2) (fun k => ((-k - 2) / 2).toNat) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v h
    simp only at h ⊢
    obtain ⟨w, rfl | rfl⟩ := Nat.even_or_odd' v
    · exfalso; ring_nf at h; omega
    · rw [show (2 * w + 1) / 2 = w by omega]
      exact ⟨by ring_nf at h ⊢; omega, rfl⟩
  · intro j; simp only; ring
  · intro k hk; simp only at hk ⊢; omega
  · intro j; simp only; omega
  · intro j j' h; simp only at h; omega
  · intro j j' h; simp only at h; omega
  · intro j; simp only; omega
  · intro j; simp only; omega
  · intro j; simp only; push_cast; apply eeq_param; ring

/-- Line `Qv = 2u + 2n + 5` (level `m`, `h = 1`) ↔ even `k ≥ 2`. -/
theorem lineB2 (m : ℕ) :
    ∑ x ∈ kacLabels m, (if (2 * n + 3) * (x.2.val + 1) = 2 * (x.1.val + 1) + 2 * n + 5 then
        VOA.RRLower.pp ((m : ℤ) - ((x.1.val : ℤ) + 1) * ((x.2.val : ℤ) + 1)) else 0) =
      ∑ k ∈ Ico (-((1 + m : ℕ) : ℤ) - 1) (((1 + m : ℕ) : ℤ) + 1),
        (if k % 2 = 0 ∧ 2 ≤ k then VOA.RRLower.pp (((1 + m : ℕ) : ℤ) - eeq n k) else 0) := by
  refine line_sumQ n m 1 (1 + m) (by ring) (fun u v => (2 * n + 3) * v = 2 * u + 2 * n + 5)
    (fun k => k % 2 = 0 ∧ 2 ≤ k)
    (fun j => (2 * n + 3) * j + 2 * n + 2) (fun j => 2 * j + 3) (fun j => 2 * j + 2)
    (fun v => (v - 3) / 2) (fun k => ((k - 2) / 2).toNat) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v h
    simp only at h ⊢
    obtain ⟨w, rfl | rfl⟩ := Nat.even_or_odd' v
    · exfalso; ring_nf at h; omega
    · rcases w with _ | w
      · exfalso; ring_nf at h; omega
      · rw [show (2 * (w + 1) + 1 - 3) / 2 = w by omega]
        exact ⟨by ring_nf at h ⊢; omega, by ring⟩
  · intro j; simp only; ring
  · intro k hk; simp only at hk ⊢; omega
  · intro j; simp only; omega
  · intro j j' h; simp only at h; omega
  · intro j j' h; simp only at h; omega
  · intro j; simp only; omega
  · intro j; simp only; omega
  · intro j; simp only; push_cast; apply eeq_param; ring

theorem eA_one_one : eA n 1 1 = 1 := by
  unfold eA
  rw [if_pos (by ring), if_neg (by omega)]

theorem aQ_cast (m : ℕ) :
    (aQ n m : ℤ) + (VOA.Classification.COne.FFLower.pp m : ℤ) =
      ∑ k ∈ Ico (-((1 + m : ℕ) : ℤ) - 1) (((1 + m : ℕ) : ℤ) + 1),
        ((if k % 2 ≠ 0 ∧ k ≤ -1 then VOA.RRLower.pp (((1 + m : ℕ) : ℤ) - eeq n k) else 0) +
          (if k % 2 ≠ 0 ∧ 1 ≤ k then VOA.RRLower.pp (((1 + m : ℕ) : ℤ) - eeq n k) else 0)) := by
  rw [Finset.sum_add_distrib, ← lineA1, ← lineA2, ← Finset.sum_add_distrib]
  have hlab : VOA.Classification.COne.FFLower.pp m =
      VOA.Classification.COne.FFLower.pp (1 + m -
        ((VOA.Classification.COne.FFLower.labOne 1 m (by omega)).1.val + 1) *
        ((VOA.Classification.COne.FFLower.labOne 1 m (by omega)).2.val + 1)) *
        eA n ((VOA.Classification.COne.FFLower.labOne 1 m (by omega)).1.val + 1)
          ((VOA.Classification.COne.FFLower.labOne 1 m (by omega)).2.val + 1) := by
    simp only [VOA.Classification.COne.FFLower.labOne]
    norm_num
    rw [eA_one_one, mul_one]
  rw [hlab, aQ]
  push_cast
  rw [Finset.sum_erase_add _ _ (VOA.Classification.COne.FFLower.labOne_mem 1 m (by omega))]
  refine Finset.sum_congr rfl fun x hx => ?_
  have := VOA.RRLower.LYGram.term_cast (1 + m) x hx (eA n (x.1.val + 1) (x.2.val + 1))
  push_cast at this
  rw [this]
  unfold eA
  split_ifs <;> push_cast <;> ring

theorem bQ_cast (m : ℕ) :
    (bQ n m : ℤ) =
      ∑ k ∈ Ico (-((1 + m : ℕ) : ℤ) - 1) (((1 + m : ℕ) : ℤ) + 1),
        ((if k % 2 = 0 ∧ k ≤ -2 then VOA.RRLower.pp (((1 + m : ℕ) : ℤ) - eeq n k) else 0) +
          (if k % 2 = 0 ∧ 2 ≤ k then VOA.RRLower.pp (((1 + m : ℕ) : ℤ) - eeq n k) else 0)) := by
  rw [Finset.sum_add_distrib, ← lineB1, ← lineB2, ← Finset.sum_add_distrib, bQ]
  push_cast
  refine Finset.sum_congr rfl fun x hx => ?_
  have := VOA.RRLower.LYGram.term_cast m x hx (eB n (x.1.val + 1) (x.2.val + 1))
  push_cast at this
  rw [this]
  unfold eB
  split_ifs <;> push_cast <;> ring

/-- **The Kac orders at `t₀ = 2/(2n+3)` give the Rocha-Caridi count**:
`rcq n (1 + m) = p(1 + m) - p(m) - aQ n m + bQ n m`. -/
theorem rcq_eq_orders (m : ℕ) :
    rcq n (1 + m) = (VOA.Classification.COne.FFLower.pp (1 + m) : ℤ) -
      ((aQ n m : ℤ) + (VOA.Classification.COne.FFLower.pp m : ℤ)) + (bQ n m : ℤ) := by
  rw [aQ_cast, bQ_cast, rcq]
  simp only [VOA.RRLower.LYGram.sgn_split]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  rw [if_pos (by rw [Finset.mem_Ico]; omega), VOA.RRLower.LYGram.ffpp_eq]
  simp [eeq]

end VOA.TwoSeriesCharacter.KacGram
