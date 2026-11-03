/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelSocleLevelOne

/-!
# The membership spaces lie in the span of `T`-monomials of degree `r - N`

Restricting a model word symbol to the line `u = 0`, `v(s) = y` (the evaluation `evV`) kills
every letter except `z₀ = v₀²` (which becomes `-y²`) and the Sugawara letters `(-J)_m + T_m`
(which become the constants `T_m`).  Reading off the coefficient of `y^{2N}` therefore shows:

* `tMonW R t k e` — the `ℂ`-span of the products `t_{m₁} ⋯ t_{m_k}` with `Σ (m_i + 1) = e`;
* `evV_mword_line` — `evV (mword w) = c · y^{2a}` with `a ≤ |w|` and
  `c ∈ tMonW (|w| - a) (wt w - |w|)`;
* `vMem_le_tMonW` — **for `N ≤ r`, every `τ` with `τ · v₀^{2N}` in the degree-`d` piece of
  `S_r` lies in `tMonW (r - N) (d - r)`**: a polynomial of `T`-degree exactly `r - N` and
  weight `d - r` in the `t_m`;
* `vMem_eq_bot_of_lt` — for `N > r` the membership space is zero;
* `modelSocleMembership_of_below` — **the membership bound `ModelSocleMembership n r`
  follows from its cases `N < r` alone** (the cases `N = r` and `N > r` are proved here, for
  every `n ≥ 1`).

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.InvariantSymbol VOA.SocleEval
open VOA.AdamovicSymbol Module
open VOA.AffineVOA.CorrectedR (Generator)

noncomputable section

section Line

variable (R : Type) [CommRing R] [Algebra ℂ R]

/-- `ι` followed by the line evaluation `evV`. -/
def lineR : JetPoly →+* Polynomial R := (evV R).toRingHom.comp (ι R).toRingHom

theorem lineR_apply (P : JetPoly) : lineR R P = evV R (ι R P) := rfl

theorem lineR_X (x : Fin 2 × ℕ) :
    lineR R (X x) = if x = (1, 0) then Polynomial.X else 0 := by
  rw [lineR_apply, evV_ι_X]

theorem map_lineR_colSer_zero : PowerSeries.map (lineR R) (colSer 0) = 0 := by
  refine PowerSeries.ext fun j => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk, lineR_X, map_zero]
  simp

theorem map_lineR_colSer_one :
    PowerSeries.map (lineR R) (colSer 1) = PowerSeries.C (Polynomial.X : Polynomial R) := by
  refine PowerSeries.ext fun j => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk, lineR_X, PowerSeries.coeff_C]
  by_cases hj : j = 0
  · subst hj; simp
  · simp [hj]

theorem map_lineR_dS (f : JetSer) :
    PowerSeries.map (lineR R) (dS f) =
      PowerSeries.derivative (Polynomial R) (PowerSeries.map (lineR R) f) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul]
  congr 1
  rw [map_add, map_natCast, map_one]

theorem lineR_coeff (n : ℕ) (f : JetSer) :
    lineR R (PowerSeries.coeff n f) = PowerSeries.coeff n (PowerSeries.map (lineR R) f) := by
  rw [PowerSeries.coeff_map]

theorem lineR_letterSym_current_zero (m : ℕ) : lineR R (letterSym (.current 0, m)) = 0 := by
  change lineR R (PowerSeries.coeff m xSer) = 0
  rw [lineR_coeff, xSer, map_mul, map_lineR_colSer_zero, zero_mul, map_zero]

theorem lineR_letterSym_current_two (m : ℕ) : lineR R (letterSym (.current 2, m)) = 0 := by
  change lineR R (PowerSeries.coeff m (-(ySer + ySer))) = 0
  rw [lineR_coeff, ySer, map_neg, map_add, map_mul, map_lineR_colSer_zero, zero_mul, add_zero,
    neg_zero, map_zero]

theorem lineR_letterSym_current_one (m : ℕ) :
    lineR R (letterSym (.current 1, m)) = if m = 0 then -(Polynomial.X ^ 2) else 0 := by
  change lineR R (PowerSeries.coeff m (-zSer)) = _
  rw [lineR_coeff, zSer, map_neg, map_mul, map_lineR_colSer_one, ← map_mul, map_neg,
    PowerSeries.coeff_C]
  by_cases hm : m = 0
  · simp [hm, sq]
  · simp [hm]

theorem lineR_letterSym_sugawara (m : ℕ) : lineR R (letterSym (.sugawara, m)) = 0 := by
  change lineR R (PowerSeries.coeff m (-jSer)) = 0
  rw [lineR_coeff, jSer, map_neg, map_sub, map_mul, map_mul, map_lineR_dS, map_lineR_dS,
    map_lineR_colSer_zero, map_zero, zero_mul, zero_mul, sub_zero, neg_zero, map_zero]

/-! ### The `T`-monomial spans -/

/-- The `ℂ`-span of the products `t_{m₁} ⋯ t_{m_k}` of total weight `Σ (m_i + 1) = e`. -/
def tMonW (t : ℕ → R) (k : ℕ) (e : ℤ) : Submodule ℂ R :=
  Submodule.span ℂ
    {x | ∃ l : List ℕ, l.length = k ∧ (((l.map fun m => m + 1).sum : ℕ) : ℤ) = e ∧
      (l.map t).prod = x}

variable {R} in
theorem one_mem_tMonW (t : ℕ → R) : (1 : R) ∈ tMonW R t 0 0 :=
  Submodule.subset_span ⟨[], rfl, by simp, by simp⟩

variable {R} in
theorem mul_mem_tMonW (t : ℕ → R) {k : ℕ} {e : ℤ} {c : R} (hc : c ∈ tMonW R t k e) (m : ℕ) :
    t m * c ∈ tMonW R t (k + 1) (e + m + 1) := by
  have h : tMonW R t k e ≤ (tMonW R t (k + 1) (e + m + 1)).comap (LinearMap.mulLeft ℂ (t m)) := by
    rw [tMonW, Submodule.span_le]
    rintro _ ⟨l, hl, he, rfl⟩
    refine Submodule.subset_span ⟨m :: l, by simp [hl], ?_, by simp⟩
    rw [List.map_cons, List.sum_cons, Nat.cast_add, he]; push_cast; ring
  exact h hc

variable {R} in
/-- In `T`-degree `0` only the weight-`0` constants survive. -/
theorem tMonW_zero_le (t : ℕ → R) (e : ℤ) :
    tMonW R t 0 e ≤ if e = 0 then Submodule.span ℂ {(1 : R)} else ⊥ := by
  rw [tMonW, Submodule.span_le]
  rintro _ ⟨l, hl, he, rfl⟩
  rw [List.length_eq_zero_iff] at hl
  subst hl
  simp only [List.map_nil, List.sum_nil, Nat.cast_zero] at he
  subst he
  simp only [if_true, List.map_nil, List.prod_nil, SetLike.mem_coe]
  exact Submodule.subset_span rfl

/-! ### The line evaluation of the model words -/

variable (t : ℕ → R)

theorem evV_mletter_current (a : Fin 3) (m : ℕ) :
    evV R (mletter R t (.current a, m)) = lineR R (letterSym (.current a, m)) := rfl

theorem evV_mletter_sugawara (m : ℕ) :
    evV R (mletter R t (.sugawara, m)) = Polynomial.C (t m) := by
  change evV R (ι R (letterSym _) + MvPolynomial.C (t m)) = _
  rw [map_add, ← lineR_apply, lineR_letterSym_sugawara, zero_add, evV_C]

theorem wordWt_cons' (l : Generator × ℕ) (w : List (Generator × ℕ)) :
    wordWt (l :: w) = letterWt l + wordWt w := by
  simp [wordWt]

/-- **The line evaluation of a model word** is `c · y^{2a}` with `a ≤ |w|` and `c` a
`T`-polynomial of degree `|w| - a` and weight `wt w - |w|`. -/
theorem evV_mword_line (w : List (Generator × ℕ)) :
    ∃ (a : ℕ) (c : R), a ≤ w.length ∧ c ∈ tMonW R t (w.length - a) (wordWt w - w.length) ∧
      evV R (mword R t w) = Polynomial.C c * Polynomial.X ^ (2 * a) := by
  induction w with
  | nil => exact ⟨0, 1, le_rfl, by simpa [wordWt] using one_mem_tMonW t, by simp⟩
  | cons l w ih =>
    obtain ⟨a, c, ha, hc, he⟩ := ih
    obtain ⟨g, m⟩ := l
    cases g with
    | current b =>
      by_cases hz : b = 1 ∧ m = 0
      · obtain ⟨rfl, rfl⟩ := hz
        refine ⟨a + 1, -c, by simp; omega, ?_, ?_⟩
        · have h1 : (w.length + 1 - (a + 1)) = w.length - a := by omega
          have h2 : wordWt ((Generator.current 1, 0) :: w) - ((w.length + 1 : ℕ) : ℤ) =
              wordWt w - w.length := by
            rw [wordWt_cons']; simp [letterWt]; ring
          rw [List.length_cons, h1, h2]
          exact neg_mem hc
        · rw [mword_cons, map_mul, he, evV_mletter_current, lineR_letterSym_current_one,
            if_pos rfl, map_neg]
          ring
      · refine ⟨0, 0, Nat.zero_le _, zero_mem _, ?_⟩
        rw [mword_cons, map_mul, evV_mletter_current, map_zero, zero_mul]
        have : lineR R (letterSym (.current b, m)) = 0 := by
          have hb : b = 0 ∨ b = 1 ∨ b = 2 := by fin_cases b <;> simp
          rcases hb with rfl | rfl | rfl
          · exact lineR_letterSym_current_zero R m
          · rw [lineR_letterSym_current_one, if_neg (by simpa using hz)]
          · exact lineR_letterSym_current_two R m
        rw [this, zero_mul]
    | sugawara =>
      refine ⟨a, t m * c, by simp; omega, ?_, ?_⟩
      · have h1 : (w.length + 1 - a) = (w.length - a) + 1 := by omega
        have h2 : wordWt ((Generator.sugawara, m) :: w) - ((w.length + 1 : ℕ) : ℤ) =
            (wordWt w - w.length) + m + 1 := by
          rw [wordWt_cons']; simp [letterWt]; ring
        rw [List.length_cons, h1, h2]
        exact mul_mem_tMonW t hc m
      · rw [mword_cons, map_mul, he, evV_mletter_sugawara, map_mul]
        ring

/-- The coefficient of `y^q` in the line evaluation, as a `ℂ`-linear functional. -/
def lineCoeff (q : ℕ) : MPoly R →ₗ[ℂ] R :=
  ((Polynomial.lcoeff R q).restrictScalars ℂ).comp ((evV R).toLinearMap.restrictScalars ℂ)

theorem lineCoeff_apply (q : ℕ) (Q : MPoly R) : lineCoeff R q Q = (evV R Q).coeff q := rfl

theorem lineCoeff_vLift (q : ℕ) (τ : R) : lineCoeff R q (vLift R q τ) = τ := by
  rw [lineCoeff_apply, vLift_apply, map_mul, map_pow, evV_C, evV_X, if_pos rfl,
    Polynomial.coeff_C_mul_X_pow, if_pos rfl]

theorem modelDeg_le_lineCoeff (r N : ℕ) (d : ℤ) :
    modelDeg R t r d ≤ (if N ≤ r then tMonW R t (r - N) (d - r) else ⊥).comap
      (lineCoeff R (2 * N)) := by
  rw [modelDeg, Submodule.span_le]
  rintro _ ⟨w, hw, hd, rfl⟩
  obtain ⟨a, c, ha, hc, he⟩ := evV_mword_line R t w
  rw [SetLike.mem_coe, Submodule.mem_comap, lineCoeff_apply, he, Polynomial.coeff_C_mul_X_pow]
  subst hw hd
  by_cases hNa : N = a
  · subst hNa
    rw [if_pos rfl, if_pos ha]
    exact hc
  · rw [if_neg (show ¬ 2 * N = 2 * a by omega)]
    exact zero_mem _

/-- **The membership space lies in the `T`-polynomials of degree `r - N`, weight `d - r`.** -/
theorem vMem_le_tMonW {r N : ℕ} (hN : N ≤ r) (d : ℤ) :
    vMem R t r d (2 * N) ≤ tMonW R t (r - N) (d - r) := by
  intro τ hτ
  have h := modelDeg_le_lineCoeff R t r N d hτ
  rw [Submodule.mem_comap, lineCoeff_vLift, if_pos hN] at h
  exact h

/-- **For `N > r` the membership space vanishes.** -/
theorem vMem_eq_bot_of_lt {r N : ℕ} (hN : r < N) (d : ℤ) : vMem R t r d (2 * N) = ⊥ := by
  rw [eq_bot_iff]
  intro τ hτ
  have h := modelDeg_le_lineCoeff R t r N d hτ
  rw [Submodule.mem_comap, lineCoeff_vLift, if_neg (by omega)] at h
  exact h

end Line

/-! ### The cases `N ≥ r` of the membership bound -/

/-- The socle label at `N = r`: the all-zero word (every cluster of size one). -/
def zeroLabel {n : ℕ} (hn : 1 ≤ n) (r : ℕ) : SocleIndex n r :=
  ⟨⟨r, Nat.lt_succ_self r⟩, ⟨fun _ => ⟨0, hn⟩, by simp⟩⟩

theorem socleDegree_const_zero {n : ℕ} (hn : 1 ≤ n) (r : ℕ) :
    socleDegree (fun _ : Fin r => (⟨0, hn⟩ : Fin n)) = r := by
  have hc : ∀ t ∈ Finset.Ico 1 n,
      clusterAtLeast (fun _ : Fin r => (⟨0, hn⟩ : Fin n)) t ^ 2 +
        clusterAtLeast (fun _ : Fin r => (⟨0, hn⟩ : Fin n)) t = 0 := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Ico.mp ht).1
    have : clusterAtLeast (fun _ : Fin r => (⟨0, hn⟩ : Fin n)) t = 0 := by
      rw [clusterAtLeast, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _
      simp only [not_le]
      omega
    rw [this]; rfl
  have hi : inversions (fun _ : Fin r => (⟨0, hn⟩ : Fin n)) = 0 := by
    rw [inversions, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _
    simp
  unfold socleDegree
  rw [Finset.sum_eq_zero hc, hi]
  simp

theorem zeroLabel_degree {n : ℕ} (hn : 1 ≤ n) (r : ℕ) : socleDegree (zeroLabel hn r).2.1 = r :=
  socleDegree_const_zero hn r

/-- **The membership bound from its cases `N < r`** (the cases `N ≥ r` are proved). -/
theorem modelSocleMembership_of_below {n r : ℕ} (hn : 1 ≤ n)
    (h : ∀ (d : ℤ) (N : ℕ), N < r → Module.rank ℂ (vMem (Rn n) (tn n) r d (2 * N)) ≤
      Nat.card {i : SocleIndex n r // ((socleDegree i.2.1 : ℕ) : ℤ) = d ∧ (i.1 : ℕ) = N}) :
    ModelSocleMembership n r := by
  intro d N
  rcases lt_trichotomy N r with hlt | rfl | hgt
  · exact h d N hlt
  · have hle0 := vMem_le_tMonW (Rn n) (tn n) (le_refl N) d
    rw [Nat.sub_self] at hle0
    have hle := hle0.trans (tMonW_zero_le (tn n) _)
    by_cases hd : d - (N : ℤ) = 0
    · rw [if_pos hd] at hle
      refine (Submodule.rank_mono hle).trans ?_
      refine (rank_span_le _).trans ?_
      rw [Cardinal.mk_singleton]
      have hpos : 0 < Nat.card {i : SocleIndex n N //
          ((socleDegree i.2.1 : ℕ) : ℤ) = d ∧ (i.1 : ℕ) = N} := by
        haveI : Nonempty {i : SocleIndex n N //
            ((socleDegree i.2.1 : ℕ) : ℤ) = d ∧ (i.1 : ℕ) = N} :=
          ⟨⟨zeroLabel hn N, by rw [zeroLabel_degree]; omega, rfl⟩⟩
        exact Nat.card_pos
      exact_mod_cast hpos
    · rw [if_neg hd, le_bot_iff] at hle
      rw [hle, rank_bot]
      exact zero_le
  · rw [vMem_eq_bot_of_lt (Rn n) (tn n) hgt d, rank_bot]
    exact zero_le

end

end VOA.TwoSeries.StrictModel
