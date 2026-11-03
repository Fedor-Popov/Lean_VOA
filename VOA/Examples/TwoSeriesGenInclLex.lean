/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesJetPoincareVdm
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots

/-!
# Lexicographic leading monomials of polynomials vanishing on a point set

Pure commutative algebra in `ℂ[x_0, …, x_{k-1}]` with the lexicographic order (`x_0` largest).

**The point game.**  For a predicate `P` on points of `ℂ^k` and an exponent vector `e`, `Win k P e`
says that one can choose `e_{k-1} + 1` distinct values of `x_{k-1}`, for each of them `e_{k-2} + 1`
distinct values of `x_{k-2}`, …, and finally `e_0 + 1` distinct values of `x_0`, so that every
resulting point satisfies `P`.  (This is the Cerlienco–Mureddu criterion read backwards.)

* `not_win_of_vanish` — **if `r ≠ 0` vanishes at every point satisfying `P`, then the game is
  lost at the lexicographic leading exponent of `r`**: `¬ Win k P (deg r)`.  Proof: peel `x_0`
  (`finSuccEquiv`); the leading coefficient in `x_0` of a polynomial of `x_0`-degree `a` vanishes
  wherever `a + 1` values of `x_0` are admissible (a nonzero one-variable polynomial of degree `≤ a`
  has at most `a` roots), and the leading exponent of `r` is `(a, deg(leading coefficient))`
  (`lex_degree_cons`).
* `win_succ_snoc` — the game read from the outermost variable `x_{k-1}`.
* **The `n`-equal game.**  `Q n μ x`: some value occurs at least `n` times among the coordinates of
  `x` together with the multiplicities `μ` of values already placed.
* `adversary` — if the `n`-equal game is lost, the adversary's replies to the offers "the
  `e_i + 1` values of highest multiplicity" give a point with all multiplicities `< n`, and its
  *columns* (`c_i` = number of later coordinates equal to `x_i`) satisfy
  `#{j > i : c_j = c_i} ≤ e_i`;
* `exists_blocks_of_not_win` — **a lost `n`-equal game at `e` gives a labelling
  `c : Fin k → Fin (n - 1)` with `#{j > i : c_j = c_i} ≤ e_i` for all `i`**, i.e. `e` dominates the
  lexicographic leading exponent of the block-Vandermonde product of `c`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.GenIncl

open MvPolynomial Finset

noncomputable section

/-! ### The point game -/

/-- `Win k P e`: the prover wins the point game (`x_0` chosen last). -/
def Win : (k : ℕ) → ((Fin k → ℂ) → Prop) → (Fin k → ℕ) → Prop
  | 0, P, _ => P Fin.elim0
  | k + 1, P, e =>
    Win k (fun y => ∃ s : Finset ℂ, s.card = e 0 + 1 ∧ ∀ v ∈ s, P (Fin.cons v y)) (Fin.tail e)

theorem win_zero (P : (Fin 0 → ℂ) → Prop) (e : Fin 0 → ℕ) : Win 0 P e ↔ P Fin.elim0 :=
  Iff.rfl

theorem win_succ {k : ℕ} (P : (Fin (k + 1) → ℂ) → Prop) (e : Fin (k + 1) → ℕ) :
    Win (k + 1) P e ↔
      Win k (fun y => ∃ s : Finset ℂ, s.card = e 0 + 1 ∧ ∀ v ∈ s, P (Fin.cons v y)) (Fin.tail e) :=
  Iff.rfl

theorem win_congr {k : ℕ} {P P' : (Fin k → ℂ) → Prop} (h : ∀ x, P x ↔ P' x) (e : Fin k → ℕ) :
    Win k P e ↔ Win k P' e := by
  have : P = P' := funext fun x => propext (h x)
  rw [this]

/-- The game read from the outermost variable. -/
theorem win_succ_snoc : ∀ (k : ℕ) (P : (Fin (k + 1) → ℂ) → Prop) (e : Fin (k + 1) → ℕ),
    Win (k + 1) P e ↔ ∃ s : Finset ℂ, s.card = e (Fin.last k) + 1 ∧
      ∀ v ∈ s, Win k (fun x => P (Fin.snoc x v)) (Fin.init e)
  | 0, P, e => by
    rw [win_succ, win_zero]
    have h : ∀ v : ℂ, (Fin.cons v Fin.elim0 : Fin 1 → ℂ) = Fin.snoc Fin.elim0 v :=
      fun v => funext fun i => by fin_cases i; rfl
    simp only [h, win_zero]
    rfl
  | k + 1, P, e => by
    rw [win_succ, win_succ_snoc k]
    refine exists_congr fun s => and_congr ?_ (forall₂_congr fun v _ => ?_)
    · simp only [Fin.tail, Fin.succ_last]
    · rw [win_succ, ← Fin.tail_init_eq_init_tail]
      refine win_congr (fun y => ?_) _
      simp only [Fin.cons_snoc_eq_snoc_cons]
      rfl

/-! ### Lexicographic degree and `finSuccEquiv` -/

theorem toLex_cons_le {k : ℕ} (a : ℕ) {m m' : Fin k →₀ ℕ} (h : toLex m ≤ toLex m') :
    toLex (Finsupp.cons a m) ≤ toLex (Finsupp.cons a m') := by
  rcases h.lt_or_eq with h | h
  · apply le_of_lt
    rw [Finsupp.Lex.lt_iff] at h ⊢
    obtain ⟨i, hi, hlt⟩ := h
    refine ⟨i.succ, fun j hj => ?_, ?_⟩
    · induction j using Fin.cases with
      | zero => simp only [ofLex_toLex, Finsupp.cons_zero]
      | succ j' =>
        simp only [ofLex_toLex, Finsupp.cons_succ]
        exact hi j' (Fin.succ_lt_succ_iff.mp hj)
    · simpa only [ofLex_toLex, Finsupp.cons_succ] using hlt
  · rw [toLex_inj.mp h]

theorem toLex_cons_lt {k : ℕ} {a b : ℕ} (hab : a < b) (m m' : Fin k →₀ ℕ) :
    toLex (Finsupp.cons a m) < toLex (Finsupp.cons b m') :=
  Finsupp.Lex.lt_iff.mpr ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by
    simpa only [ofLex_toLex, Finsupp.cons_zero] using hab⟩

/-- **The leading exponent after peeling `x_0`**: `(x_0-degree, leading exponent of the leading
coefficient)`. -/
theorem lex_degree_cons {k : ℕ} {r : MvPolynomial (Fin (k + 1)) ℂ} (hr : r ≠ 0) :
    (MonomialOrder.lex).degree r = Finsupp.cons (finSuccEquiv ℂ k r).natDegree
      ((MonomialOrder.lex).degree (finSuccEquiv ℂ k r).leadingCoeff) := by
  set p := finSuccEquiv ℂ k r with hp
  have hp0 : p ≠ 0 := by
    rw [hp]; exact fun h => hr ((finSuccEquiv ℂ k).injective (by rw [h, map_zero]))
  have hc0 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  set D := Finsupp.cons p.natDegree ((MonomialOrder.lex).degree p.leadingCoeff) with hD
  have hDs : D ∈ r.support := by
    rw [mem_support_iff, hD, ← finSuccEquiv_coeff_coeff, ← hp]
    exact mem_support_iff.mp (MonomialOrder.degree_mem_support hc0)
  have h1 := MonomialOrder.le_degree (m := MonomialOrder.lex) hDs
  have hdm := MonomialOrder.degree_mem_support (m := MonomialOrder.lex) hr
  set E := (MonomialOrder.lex).degree r with hEdef
  have hE : E = Finsupp.cons (E 0) E.tail := (Finsupp.cons_tail E).symm
  have hcoef : coeff E.tail (p.coeff (E 0)) ≠ 0 := by
    rw [hp, finSuccEquiv_coeff_coeff, Finsupp.cons_tail]; exact mem_support_iff.mp hdm
  have hj : E 0 ≤ p.natDegree :=
    Polynomial.le_natDegree_of_ne_zero fun h => hcoef (by rw [h, coeff_zero])
  have h2 : (MonomialOrder.lex).toSyn E ≤ (MonomialOrder.lex).toSyn D := by
    rw [MonomialOrder.lex_le_iff, hE, hD]
    rcases hj.lt_or_eq with hlt | heq
    · exact le_of_lt (toLex_cons_lt hlt _ _)
    · rw [heq]
      apply toLex_cons_le
      rw [← MonomialOrder.lex_le_iff]
      apply MonomialOrder.le_degree
      rw [mem_support_iff]
      rw [heq] at hcoef
      exact hcoef
  exact (MonomialOrder.lex).toSyn.injective (le_antisymm h2 h1)

/-- **Vanishing forces a lost game at the leading exponent.** -/
theorem not_win_of_vanish : ∀ (k : ℕ) (P : (Fin k → ℂ) → Prop) (r : MvPolynomial (Fin k) ℂ),
    r ≠ 0 → (∀ x, P x → eval x r = 0) → ¬ Win k P ⇑((MonomialOrder.lex).degree r)
  | 0, P, r, hr, hv => by
    intro hw
    have h := hv _ hw
    rw [eq_C_of_isEmpty r, eval_C] at h
    exact hr (by rw [eq_C_of_isEmpty r, h, C_0])
  | k + 1, P, r, hr, hv => by
    intro hw
    set p := finSuccEquiv ℂ k r with hp
    have hp0 : p ≠ 0 := by
      rw [hp]; exact fun h => hr ((finSuccEquiv ℂ k).injective (by rw [h, map_zero]))
    have hc0 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
    rw [lex_degree_cons hr, win_succ] at hw
    have h0 : (⇑(Finsupp.cons p.natDegree ((MonomialOrder.lex).degree p.leadingCoeff)) :
        Fin (k + 1) → ℕ) 0 = p.natDegree := Finsupp.cons_zero _ _
    have ht : Fin.tail (⇑(Finsupp.cons p.natDegree ((MonomialOrder.lex).degree p.leadingCoeff)) :
        Fin (k + 1) → ℕ) = ⇑((MonomialOrder.lex).degree p.leadingCoeff) :=
      funext fun i => Finsupp.cons_succ _ _ _
    rw [h0, ht] at hw
    refine not_win_of_vanish k _ p.leadingCoeff hc0 (fun y hy => ?_) hw
    obtain ⟨s, hs, hsv⟩ := hy
    have hq : Polynomial.map (eval y) p = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s (fun v hvs => ?_) ?_
      · rw [hp, ← eval_eq_eval_mv_eval']
        exact hv _ (hsv v hvs)
      · rw [hs]; exact Nat.lt_succ_of_le Polynomial.natDegree_map_le
    have := congrArg (fun q => Polynomial.coeff q p.natDegree) hq
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using this

/-! ### The `n`-equal game -/

/-- Some value occurs at least `n` times among `μ` and the coordinates of `x`. -/
def Q (n : ℕ) {k : ℕ} (μ : ℂ →₀ ℕ) (x : Fin k → ℂ) : Prop :=
  ∃ z, n ≤ μ z + ∑ i, if x i = z then 1 else 0

/-- The number of values of multiplicity `> c` in `μ`. -/
def colCount (μ : ℂ →₀ ℕ) (c : ℕ) : ℕ := #(μ.support.filter fun z => c < μ z)

/-- The number of later coordinates equal to `x_i`. -/
def later {k : ℕ} (x : Fin k → ℂ) (i : Fin k) : ℕ := ∑ j, if i < j ∧ x j = x i then 1 else 0

/-- The column of `x_i`. -/
def col {k : ℕ} (μ : ℂ →₀ ℕ) (x : Fin k → ℂ) (i : Fin k) : ℕ := μ (x i) + later x i

/-- The number of later coordinates in the same column. -/
def laterCol {k : ℕ} {α : Type*} [DecidableEq α] (c : Fin k → α) (i : Fin k) : ℕ :=
  ∑ j, if i < j ∧ c j = c i then 1 else 0

theorem single_one_apply (v z : ℂ) : (Finsupp.single v 1 : ℂ →₀ ℕ) z = if v = z then 1 else 0 := by
  rw [Finsupp.single_apply]

theorem Q_snoc (n : ℕ) {k : ℕ} (μ : ℂ →₀ ℕ) (x : Fin k → ℂ) (v : ℂ) :
    Q n μ (Fin.snoc x v) ↔ Q n (μ + Finsupp.single v 1) x := by
  refine exists_congr fun z => ?_
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Finsupp.coe_add, Pi.add_apply, single_one_apply]
  constructor <;> intro h <;> omega

theorem later_snoc_castSucc {k : ℕ} (x : Fin k → ℂ) (v : ℂ) (i : Fin k) :
    later (Fin.snoc x v : Fin (k + 1) → ℂ) i.castSucc = later x i + if v = x i then 1 else 0 := by
  rw [later, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last,
    true_and, later]

theorem later_last {k : ℕ} (x : Fin (k + 1) → ℂ) : later x (Fin.last k) = 0 := by
  rw [later]
  exact sum_eq_zero fun j _ => if_neg fun h => absurd h.1 (not_lt.mpr (Fin.le_last j))

theorem col_snoc_castSucc {k : ℕ} (μ : ℂ →₀ ℕ) (x : Fin k → ℂ) (v : ℂ) (i : Fin k) :
    col μ (Fin.snoc x v : Fin (k + 1) → ℂ) i.castSucc = col (μ + Finsupp.single v 1) x i := by
  rw [col, col, later_snoc_castSucc, Fin.snoc_castSucc, Finsupp.coe_add, Pi.add_apply,
    single_one_apply]
  ring

theorem col_snoc_last {k : ℕ} (μ : ℂ →₀ ℕ) (x : Fin k → ℂ) (v : ℂ) :
    col μ (Fin.snoc x v : Fin (k + 1) → ℂ) (Fin.last k) = μ v := by
  rw [col, later_last, Fin.snoc_last, add_zero]

theorem laterCol_castSucc {k : ℕ} {α : Type*} [DecidableEq α] (c : Fin (k + 1) → α) (i : Fin k) :
    laterCol c i.castSucc = laterCol (fun j : Fin k => c j.castSucc) i +
      if c (Fin.last k) = c i.castSucc then 1 else 0 := by
  rw [laterCol, Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, true_and, laterCol]

theorem laterCol_last {k : ℕ} {α : Type*} [DecidableEq α] (c : Fin (k + 1) → α) :
    laterCol c (Fin.last k) = 0 := by
  rw [laterCol]
  exact sum_eq_zero fun j _ => if_neg fun h => absurd h.1 (not_lt.mpr (Fin.le_last j))

theorem colCount_eq_sum (μ : ℂ →₀ ℕ) (c : ℕ) {T : Finset ℂ} (hT : μ.support ⊆ T) :
    colCount μ c = ∑ z ∈ T, if c < μ z then 1 else 0 := by
  rw [colCount, card_filter]
  refine sum_subset hT fun z _ hz => ?_
  rw [Finsupp.notMem_support_iff.mp hz]
  simp

theorem colCount_add_single (μ : ℂ →₀ ℕ) (v : ℂ) (c : ℕ) :
    colCount (μ + Finsupp.single v 1) c = colCount μ c + if μ v = c then 1 else 0 := by
  have hT : μ.support ⊆ insert v μ.support := subset_insert _ _
  have hT' : (μ + Finsupp.single v 1 : ℂ →₀ ℕ).support ⊆ insert v μ.support := by
    intro z hz
    rw [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, single_one_apply] at hz
    rw [mem_insert, Finsupp.mem_support_iff]
    by_cases hvz : v = z
    · exact Or.inl hvz.symm
    · rw [if_neg hvz, add_zero] at hz; exact Or.inr hz
  rw [colCount_eq_sum _ _ hT, colCount_eq_sum _ _ hT', ← add_sum_erase _ _ (mem_insert_self v _),
    ← add_sum_erase _ _ (mem_insert_self v _)]
  have hrest : ∑ z ∈ (insert v μ.support).erase v,
      (if c < (μ + Finsupp.single v 1 : ℂ →₀ ℕ) z then 1 else 0) =
      ∑ z ∈ (insert v μ.support).erase v, if c < μ z then 1 else 0 := by
    refine sum_congr rfl fun z hz => ?_
    have hzv : v ≠ z := fun h => (ne_of_mem_erase hz) h.symm
    rw [Finsupp.coe_add, Pi.add_apply, single_one_apply, if_neg hzv, add_zero]
  rw [hrest, Finsupp.coe_add, Pi.add_apply, single_one_apply, if_pos rfl]
  by_cases h1 : c < μ v
  · rw [if_pos h1, if_pos (by omega), if_neg (by omega)]; ring
  · by_cases h2 : μ v = c
    · rw [if_neg h1, if_pos (by omega), if_pos h2]; ring
    · rw [if_neg h1, if_neg (by omega), if_neg h2, add_zero]

/-- The `m` values of highest multiplicity. -/
theorem exists_top (μ : ℂ →₀ ℕ) : ∀ m : ℕ, ∃ s : Finset ℂ, s.card = m ∧ ∀ v ∈ s, ∀ z ∉ s, μ z ≤ μ v
  | 0 => ⟨∅, rfl, by simp⟩
  | m + 1 => by
    obtain ⟨s, hs, htop⟩ := exists_top μ m
    obtain ⟨z0, hz0s, hz0⟩ : ∃ z0, z0 ∉ s ∧ ∀ z ∉ s, μ z ≤ μ z0 := by
      by_cases hne : (μ.support \ s).Nonempty
      · obtain ⟨z0, hz0, hmax⟩ := (μ.support \ s).exists_max_image μ hne
        refine ⟨z0, (mem_sdiff.mp hz0).2, fun z hz => ?_⟩
        by_cases hzs : z ∈ μ.support
        · exact hmax z (mem_sdiff.mpr ⟨hzs, hz⟩)
        · rw [Finsupp.notMem_support_iff.mp hzs]; exact Nat.zero_le _
      · haveI : Infinite ℂ := Infinite.of_injective (Nat.cast : ℕ → ℂ) Nat.cast_injective
        obtain ⟨z0, hz0⟩ := Infinite.exists_notMem_finset (s ∪ μ.support)
        refine ⟨z0, fun h => hz0 (mem_union_left _ h), fun z hz => ?_⟩
        have : z ∉ μ.support := fun hzs => hne ⟨z, mem_sdiff.mpr ⟨hzs, hz⟩⟩
        rw [Finsupp.notMem_support_iff.mp this]; exact Nat.zero_le _
    refine ⟨insert z0 s, by rw [card_insert_of_notMem hz0s, hs], fun v hv z hz => ?_⟩
    rw [mem_insert] at hv
    have hz' : z ∉ s := fun h => hz (mem_insert_of_mem h)
    rcases hv with rfl | hv
    · exact hz0 z hz'
    · exact htop v hv z hz'

theorem colCount_top {μ : ℂ →₀ ℕ} {s : Finset ℂ} (htop : ∀ v ∈ s, ∀ z ∉ s, μ z ≤ μ v) {v : ℂ}
    (hv : v ∈ s) : colCount μ (μ v) + 1 ≤ s.card := by
  have hsub : (μ.support.filter fun z => μ v < μ z) ⊆ s.erase v := by
    intro z hz
    have hlt := (mem_filter.mp hz).2
    refine mem_erase.mpr ⟨fun h => by rw [h] at hlt; exact lt_irrefl _ hlt, ?_⟩
    by_contra hzs
    exact absurd (htop v hv z hzs) (not_le.mpr hlt)
  have := card_le_card hsub
  rw [card_erase_of_mem hv] at this
  rw [colCount]
  have hpos : 0 < s.card := card_pos.mpr ⟨v, hv⟩
  omega

/-- **The adversary's point.** -/
theorem adversary (n : ℕ) : ∀ (k : ℕ) (μ : ℂ →₀ ℕ) (e : Fin k → ℕ), ¬ Win k (Q n μ) e →
    ∃ x : Fin k → ℂ, ¬ Q n μ x ∧ ∀ i, laterCol (col μ x) i + colCount μ (col μ x i) ≤ e i
  | 0, μ, e, h => ⟨Fin.elim0, h, fun i => i.elim0⟩
  | k + 1, μ, e, h => by
    rw [win_succ_snoc] at h
    obtain ⟨s, hs, htop⟩ := exists_top μ (e (Fin.last k) + 1)
    obtain ⟨v, hvs, hv⟩ : ∃ v ∈ s, ¬ Win k (fun x => Q n μ (Fin.snoc x v)) (Fin.init e) := by
      by_contra hc
      push Not at hc
      exact h ⟨s, hs, hc⟩
    rw [win_congr (fun x => Q_snoc n μ x v)] at hv
    obtain ⟨x', hQ, hcol⟩ := adversary n k (μ + Finsupp.single v 1) (Fin.init e) hv
    refine ⟨Fin.snoc x' v, fun hq => hQ ((Q_snoc n μ x' v).mp hq), fun i => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      rw [laterCol_last, col_snoc_last, zero_add]
      have := colCount_top htop hvs
      omega
    | cast i =>
      rw [laterCol_castSucc, col_snoc_last, col_snoc_castSucc]
      have hfun : (fun j : Fin k => col μ (Fin.snoc x' v : Fin (k + 1) → ℂ) j.castSucc) =
          col (μ + Finsupp.single v 1) x' := funext fun j => col_snoc_castSucc μ x' v j
      rw [hfun]
      have h1 := hcol i
      rw [colCount_add_single] at h1
      have h2 : Fin.init e i = e i.castSucc := rfl
      omega

/-- **A lost `n`-equal game gives a block labelling dominated by `e`.** -/
theorem exists_blocks_of_not_win {n k : ℕ} (hn : 2 ≤ n) {e : Fin k → ℕ} (h : ¬ Win k (Q n 0) e) :
    ∃ c : Fin k → Fin (n - 1), ∀ i, laterCol c i ≤ e i := by
  obtain ⟨x, hQ, hcol⟩ := adversary n k 0 e h
  have hlt : ∀ i, later x i < n - 1 := by
    intro i
    have hQi : ¬ n ≤ (0 : ℂ →₀ ℕ) (x i) + ∑ j, if x j = x i then 1 else 0 := fun hh => hQ ⟨x i, hh⟩
    rw [Finsupp.coe_zero, Pi.zero_apply, zero_add, not_le] at hQi
    have hle : later x i + 1 ≤ ∑ j, if x j = x i then 1 else 0 := by
      have hsum : later x i + 1 = ∑ j, ((if i < j ∧ x j = x i then 1 else 0) +
          if j = i then 1 else 0) := by
        rw [sum_add_distrib, sum_ite_eq']; simp [later]
      rw [hsum]
      refine sum_le_sum fun j _ => ?_
      by_cases hji : j = i
      · subst hji; simp
      · rw [if_neg hji, add_zero]
        split_ifs with h1 h2 <;> simp_all
    omega
  refine ⟨fun i => ⟨later x i, hlt i⟩, fun i => ?_⟩
  have h1 := hcol i
  have hc0 : colCount 0 (col 0 x i) = 0 := by simp [colCount]
  have hcolx : col 0 x = later x := funext fun j => by simp [col]
  rw [hc0, add_zero, hcolx] at h1
  have heq : laterCol (fun i => (⟨later x i, hlt i⟩ : Fin (n - 1))) i = laterCol (later x) i := by
    simp only [laterCol, Fin.mk.injEq]
  rw [heq]; exact h1

end

end VOA.TwoSeries.GenIncl
