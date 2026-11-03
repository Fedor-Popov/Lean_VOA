/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesBoxSym

/-!
# Words with balanced bounds and their recursion

For a balanced bound vector `bnd q r = (q+1, …, q+1, q, …, q)` (`r` entries `q+1`, the rest `q`,
on `B` positions) consider the words `x : Fin B → ℕ` with `x_j ≤ bnd q r j` and `Σ x_j = m`,
graded by the statistic

  `statF x = Σ_{i,j} min(x_i, x_j) + inv(x)`         (`Σ_{i,j} min(x_i,x_j) = Σ_{t ≥ 1} c_t²`).

`wcF B q r m D` counts those with `statF x + D = m B`.  The two operations of the fusion
recursion act on words as follows:

* `statF_cons_zero` — prepending a letter `0` does not change the statistic;
* `statF_cons_snoc` — **rotation**: `statF (v :: t) = statF (t ++ [v-1]) + (B+1)` for `v ≥ 1`;
* `wcF_succ` — hence the count recursion
  `wcF (B+1) q r (m+1) D = wcF (B+1) q' r' m D + [D ≥ m+1] · wcF B q'' r'' (m+1) (D-m-1)`
  (`(q', r')`: the rotated bounds; `(q'', r'')`: the first bound removed);
* `wcF_le_socleCount` — for the rectangle `bnd (n-1) 0` the count is at most the socle count.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open VOA.SocleEval

noncomputable section

/-! ### The statistic -/

/-- The balanced bounds: `q + 1` on the first `r` positions, `q` on the others. -/
def bnd (q r : ℕ) {B : ℕ} (j : Fin B) : ℕ := q + if (j : ℕ) < r then 1 else 0

/-- Inversions of a word. -/
def invF {B : ℕ} (x : Fin B → ℕ) : ℕ :=
  (Finset.univ.filter fun p : Fin B × Fin B => p.1 < p.2 ∧ x p.2 < x p.1).card

/-- `Σ_{i,j} min(x_i, x_j)`. -/
def minS {B : ℕ} (x : Fin B → ℕ) : ℕ := ∑ i, ∑ j, min (x i) (x j)

/-- The statistic `Σ_{i,j} min(x_i, x_j) + inv(x)`. -/
def statF {B : ℕ} (x : Fin B → ℕ) : ℕ := minS x + invF x

theorem invF_eq_sum {B : ℕ} (x : Fin B → ℕ) :
    invF x = ∑ i, ∑ j, if i < j ∧ x j < x i then 1 else 0 := by
  rw [invF, Finset.card_filter, Fintype.sum_prod_type]

theorem invF_cons {B : ℕ} (v : ℕ) (t : Fin B → ℕ) :
    invF (Fin.cons v t : Fin (B + 1) → ℕ) =
      invF t + (Finset.univ.filter fun j => t j < v).card := by
  rw [invF_eq_sum, invF_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, lt_irrefl, false_and, if_false,
    Fin.succ_pos, true_and, zero_add]
  rw [Finset.card_filter, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_succ]
  simp

theorem invF_snoc {B : ℕ} (t : Fin B → ℕ) (w : ℕ) :
    invF (Fin.snoc t w : Fin (B + 1) → ℕ) =
      invF t + (Finset.univ.filter fun j => w < t j).card := by
  rw [invF_eq_sum, invF_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hl : ∑ j : Fin (B + 1), (if Fin.last B < j ∧
      (Fin.snoc t w : Fin (B + 1) → ℕ) j < w then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => if_neg fun h => absurd h.1 (not_lt.mpr (Fin.le_last j))
  rw [hl, add_zero, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_lt_castSucc_iff,
    Fin.castSucc_lt_last, true_and]

theorem minS_cons {B : ℕ} (v : ℕ) (t : Fin B → ℕ) :
    minS (Fin.cons v t : Fin (B + 1) → ℕ) = minS t + 2 * ∑ j, min v (t j) + v := by
  rw [minS, minS, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, min_self]
  rw [Finset.sum_add_distrib]
  simp_rw [min_comm (t _) v]
  ring

theorem minS_snoc {B : ℕ} (t : Fin B → ℕ) (w : ℕ) :
    minS (Fin.snoc t w : Fin (B + 1) → ℕ) = minS t + 2 * ∑ j, min w (t j) + w := by
  rw [minS, minS, Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, min_self]
  rw [Finset.sum_add_distrib]
  simp_rw [min_comm (t _) w]
  ring

theorem statF_cons_zero {B : ℕ} (t : Fin B → ℕ) :
    statF (Fin.cons 0 t : Fin (B + 1) → ℕ) = statF t := by
  rw [statF, statF, minS_cons, invF_cons]
  simp

theorem sum_min_succ (v : ℕ) {B : ℕ} (t : Fin B → ℕ) :
    ∑ j, min (v + 1) (t j) = ∑ j, min v (t j) + (Finset.univ.filter fun j => v + 1 ≤ t j).card := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h <;> omega

/-- **Rotation**: `statF (v :: t) = statF (t ++ [v - 1]) + (B + 1)` for `v ≥ 1`. -/
theorem statF_cons_snoc {B : ℕ} (v : ℕ) (t : Fin B → ℕ) :
    statF (Fin.cons (v + 1) t : Fin (B + 1) → ℕ) =
      statF (Fin.snoc t v : Fin (B + 1) → ℕ) + (B + 1) := by
  rw [statF, statF, minS_cons, minS_snoc, invF_cons, invF_snoc, sum_min_succ]
  have hsplit : (Finset.univ.filter fun j => t j < v + 1).card +
      (Finset.univ.filter fun j => ¬ t j < v + 1).card = B := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have h1 : (Finset.univ.filter fun j => ¬ t j < v + 1) =
      (Finset.univ.filter fun j => v + 1 ≤ t j) := by
    ext j; simp
  have h2 : (Finset.univ.filter fun j => v < t j) =
      (Finset.univ.filter fun j => v + 1 ≤ t j) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [h1] at hsplit
  rw [h2]
  omega

/-! ### Words and their count -/

/-- The words with balanced bounds `bnd q r` and letter sum `m`. -/
def wordsF (B q r m : ℕ) : Finset (Fin B → ℕ) :=
  (Fintype.piFinset fun j : Fin B => Finset.range (bnd q r j + 1)).filter fun x => ∑ j, x j = m

/-- The number of words with statistic `m B - D`. -/
def wcF (B q r m D : ℕ) : ℕ := ((wordsF B q r m).filter fun x => statF x + D = m * B).card

theorem mem_wordsF {B q r m : ℕ} {x : Fin B → ℕ} :
    x ∈ wordsF B q r m ↔ (∀ j, x j ≤ bnd q r j) ∧ ∑ j, x j = m := by
  simp only [wordsF, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    Nat.lt_succ_iff]

/-- The statistic is at most `(Σ x) · B`. -/
theorem statF_le {B : ℕ} (x : Fin B → ℕ) : statF x ≤ (∑ j, x j) * B := by
  induction B with
  | zero => simp [statF, minS, invF]
  | succ B ih =>
    have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    rw [hx, statF, minS_cons, invF_cons, Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    have ht := ih (Fin.tail x)
    rw [statF] at ht
    have h1 : 2 * ∑ j, min (x 0) (Fin.tail x j) + (Finset.univ.filter
        fun j => Fin.tail x j < x 0).card ≤ ∑ j, (x 0 + Fin.tail x j) := by
      rw [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with h <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h1
    nlinarith

theorem bnd_succ (q r : ℕ) {B : ℕ} (i : Fin B) :
    bnd q r i.succ = bnd q (r - 1) i := by
  simp only [bnd, Fin.val_succ]
  split_ifs <;> omega

theorem bnd_rot_castSucc (q r : ℕ) {B : ℕ} (_hr : r ≤ B) (hqr : 1 ≤ q ∨ 1 ≤ r) (i : Fin B) :
    bnd (if 1 ≤ r then q else q - 1) (if 1 ≤ r then r - 1 else B) i.castSucc =
      bnd q r i.succ := by
  simp only [bnd, Fin.val_succ, Fin.val_castSucc]
  have := i.2
  split_ifs <;> omega

theorem bnd_rot_last (q r : ℕ) {B : ℕ} (hr : r ≤ B) (hqr : 1 ≤ q ∨ 1 ≤ r) :
    bnd (if 1 ≤ r then q else q - 1) (if 1 ≤ r then r - 1 else B) (Fin.last B) + 1 =
      bnd q r (0 : Fin (B + 1)) := by
  simp only [bnd, Fin.val_last, Fin.val_zero]
  split_ifs <;> omega

/-- **The count recursion** (split by the first letter: `0`, or rotate). -/
theorem wcF_succ (B q r m D : ℕ) (hr : r ≤ B) (hqr : 1 ≤ q ∨ 1 ≤ r) :
    wcF (B + 1) q r (m + 1) D =
      wcF (B + 1) (if 1 ≤ r then q else q - 1) (if 1 ≤ r then r - 1 else B) m D +
        (if m + 1 ≤ D then wcF B q (r - 1) (m + 1) (D - (m + 1)) else 0) := by
  classical
  rw [wcF, ← Finset.card_filter_add_card_filter_not (p := fun x : Fin (B + 1) → ℕ => x 0 = 0),
    add_comm]
  congr 1
  · -- the rotation part
    rw [wcF]
    refine Finset.card_nbij' (fun x => Fin.snoc (Fin.tail x) (x 0 - 1))
      (fun y => Fin.cons (y (Fin.last B) + 1) (Fin.init y)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, mem_wordsF] at hx ⊢
      obtain ⟨⟨⟨hb, hs⟩, hst⟩, h0⟩ := hx
      have hx' : x = Fin.cons (x 0 - 1 + 1) (Fin.tail x) := by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h0)]; exact (Fin.cons_self_tail x).symm
      refine ⟨⟨fun j => ?_, ?_⟩, ?_⟩
      · refine Fin.lastCases ?_ (fun i => ?_) j
        · rw [Fin.snoc_last]
          have := hb 0
          have := bnd_rot_last q r hr hqr
          omega
        · rw [Fin.snoc_castSucc, bnd_rot_castSucc q r hr hqr]
          exact hb i.succ
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [Fin.sum_univ_succ] at hs
        simp only [Fin.tail]
        omega
      · rw [hx', statF_cons_snoc] at hst
        have hmul : (m + 1) * (B + 1) = m * (B + 1) + (B + 1) := by ring
        omega
    · intro y hy
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, mem_wordsF] at hy ⊢
      obtain ⟨⟨hb, hs⟩, hst⟩ := hy
      refine ⟨⟨⟨fun j => ?_, ?_⟩, ?_⟩, by simp⟩
      · refine Fin.cases ?_ (fun i => ?_) j
        · rw [Fin.cons_zero, ← bnd_rot_last q r hr hqr]
          exact Nat.add_le_add_right (hb _) 1
        · rw [Fin.cons_succ, ← bnd_rot_castSucc q r hr hqr]
          exact hb _
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [Fin.sum_univ_castSucc] at hs
        simp only [Fin.init] at *
        omega
      · rw [statF_cons_snoc, Fin.snoc_init_self]
        nlinarith
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hx
      have h0 := hx.2
      simp only [Fin.snoc_last, Fin.init_snoc]
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h0)]
      exact Fin.cons_self_tail x
    · intro y _
      simp only [Fin.cons_zero, Nat.add_sub_cancel, Fin.tail_cons, Fin.snoc_init_self]
  · -- the leading-zero part
    split_ifs with hD
    · rw [wcF]
      refine Finset.card_nbij' (fun x => Fin.tail x) (fun t => Fin.cons 0 t) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, mem_wordsF] at hx ⊢
        obtain ⟨⟨⟨hb, hs⟩, hst⟩, h0⟩ := hx
        have hx' : x = Fin.cons 0 (Fin.tail x) := by rw [← h0]; exact (Fin.cons_self_tail x).symm
        refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
        · rw [← bnd_succ]; exact hb i.succ
        · rw [Fin.sum_univ_succ, h0] at hs
          simpa [Fin.tail] using hs
        · rw [hx', statF_cons_zero] at hst
          have hmul : (m + 1) * (B + 1) = (m + 1) * B + (m + 1) := by ring
          omega
      · intro t ht
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, mem_wordsF] at ht ⊢
        obtain ⟨⟨hb, hs⟩, hst⟩ := ht
        refine ⟨⟨⟨fun j => ?_, ?_⟩, ?_⟩, by simp⟩
        · refine Fin.cases ?_ (fun i => ?_) j
          · simp
          · rw [Fin.cons_succ, bnd_succ]; exact hb i
        · rw [Fin.sum_univ_succ]; simpa using hs
        · rw [statF_cons_zero]
          have hmul : (m + 1) * (B + 1) = (m + 1) * B + (m + 1) := by ring
          omega
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hx
        rw [← hx.2]
        exact Fin.cons_self_tail x
      · intro t _
        exact Fin.tail_cons _ _
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx h0
      rw [Finset.mem_filter, mem_wordsF] at hx
      obtain ⟨⟨-, hs⟩, hst⟩ := hx
      have hx' : x = Fin.cons 0 (Fin.tail x) := by rw [← h0]; exact (Fin.cons_self_tail x).symm
      have hle := statF_le (Fin.tail x)
      rw [hx', statF_cons_zero] at hst
      rw [Fin.sum_univ_succ, h0, zero_add] at hs
      have : ∑ j, Fin.tail x j = m + 1 := hs
      rw [this] at hle
      push Not at hD
      nlinarith

/-! ### The rectangle and the socle words -/

theorem card_Ico_filter_le {n a : ℕ} (ha : a < n) :
    ((Finset.Ico 1 n).filter fun t => t ≤ a).card = a := by
  have : ((Finset.Ico 1 n).filter fun t => t ≤ a) = Finset.Ico 1 (a + 1) := by
    ext t; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]
  omega

theorem sum_clusterAtLeast {n N : ℕ} (w : Fin N → Fin n) :
    ∑ t ∈ Finset.Ico 1 n, clusterAtLeast w t = ∑ j, ((w j : Fin n) : ℕ) := by
  unfold clusterAtLeast
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.card_filter]
  exact card_Ico_filter_le (w j).2

theorem sum_clusterAtLeast_sq {n N : ℕ} (w : Fin N → Fin n) :
    ∑ t ∈ Finset.Ico 1 n, clusterAtLeast w t ^ 2 = minS fun j => ((w j : Fin n) : ℕ) := by
  unfold clusterAtLeast minS
  simp_rw [sq, Finset.card_filter, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ∀ t, ((if t ≤ ((w i : Fin n) : ℕ) then 1 else 0) *
      (if t ≤ ((w j : Fin n) : ℕ) then 1 else 0) : ℕ) =
      if t ≤ min ((w i : Fin n) : ℕ) ((w j : Fin n) : ℕ) then 1 else 0 := by
    intro t; simp only [le_min_iff]; split_ifs <;> simp_all
  simp_rw [this]
  rw [← Finset.card_filter]
  exact card_Ico_filter_le (lt_of_le_of_lt (min_le_left _ _) (w i).2)

theorem inversions_eq_invF {n N : ℕ} (w : Fin N → Fin n) :
    inversions w = invF fun j => ((w j : Fin n) : ℕ) := by
  unfold inversions invF
  congr 1

/-- **The rectangle count is at most the socle count.** -/
theorem wcF_le_socleCount (n N m D : ℕ) (hn : 1 ≤ n) :
    wcF N (n - 1) 0 m D ≤ socleCount n (N + m) (((N + m + m * N : ℕ) : ℤ) - D) N := by
  classical
  set F := (wordsF N (n - 1) 0 m).filter fun x => statF x + D = m * N with hF
  have key : ∀ x ∈ F, (∀ j, x j ≤ n - 1) ∧ ∑ j, x j = m ∧ statF x + D = m * N := by
    intro x hx
    rw [hF, Finset.mem_filter, mem_wordsF] at hx
    refine ⟨fun j => ?_, hx.1.2, hx.2⟩
    have := hx.1.1 j
    simpa [bnd] using this
  let toW : (Fin N → ℕ) → (Fin N → Fin n) := fun x j => ⟨min (x j) (n - 1), by omega⟩
  have hval : ∀ x ∈ F, ∀ j, ((toW x j : Fin n) : ℕ) = x j := by
    intro x hx j
    exact min_eq_left ((key x hx).1 j)
  have hfun : ∀ x ∈ F, (fun j => ((toW x j : Fin n) : ℕ)) = x := fun x hx =>
    funext (hval x hx)
  have hsum : ∀ x ∈ F, ∑ j, (((toW x j : Fin n) : ℕ) + 1) = N + m := by
    intro x hx
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
    simp_rw [hval x hx]
    rw [(key x hx).2.1]
    ring
  have hdeg : ∀ x ∈ F, ((socleDegree (toW x) : ℕ) : ℤ) = (((N + m + m * N : ℕ) : ℤ) - D) := by
    intro x hx
    have h1 : socleDegree (toW x) = N + m + statF x := by
      unfold socleDegree
      rw [Finset.sum_add_distrib, sum_clusterAtLeast_sq, sum_clusterAtLeast,
        inversions_eq_invF, hfun x hx, statF]
      rw [show Finset.univ.sum x = m from (key x hx).2.1]
      ring
    have h2 := (key x hx).2.2
    rw [h1]
    push_cast
    omega
  let g : F → {i : SocleIndex n (N + m) //
      ((socleDegree i.2.1 : ℕ) : ℤ) = (((N + m + m * N : ℕ) : ℤ) - D) ∧ (i.1 : ℕ) = N} :=
    fun x => ⟨⟨⟨N, by omega⟩, ⟨toW x.1, hsum x.1 x.2⟩⟩, hdeg x.1 x.2, rfl⟩
  have ginj : Function.Injective g := by
    intro x y hxy
    have h1 := congrArg (fun i => i.1) hxy
    simp only [g] at h1
    have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h1).2
    have h3 : toW x.1 = toW y.1 := congrArg Subtype.val h2
    apply Subtype.ext
    funext j
    rw [← hval x.1 x.2 j, ← hval y.1 y.2 j, h3]
  rw [socleCount, Nat.card_eq_fintype_card, wcF, ← hF, ← Fintype.card_coe F]
  exact Fintype.card_le_of_injective g ginj

end

end VOA.TwoSeries.StrictModel
