/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Evaluating formal infinite products  (Moonshine step M7d, analytic bridge)

The `q`-expansion identities of M7d need to pass between *formal* infinite products in `ℂ⟦X⟧`
(the generating functions of `LatticeGradedDim.lean`, `TwistedSectorDim.lean`) and *analytic*
infinite products on the unit disc (Mathlib's `Δ(z) = q ∏' (1 - qⁿ⁺¹)^{24}`).  This file proves
the bridge by dominated convergence (Tannery's theorem), with an explicit real majorant.

## Setting
A family `u : ℕ → ℂ⟦X⟧` with `u i ≡ 1 (mod X^{i+1})` has stabilising partial products:
`[Xⁿ] ∏_{i<N} u i = [Xⁿ] ∏_{i<n} u i` for `N ≥ n` (`coeff_prod_range_stable`), and so the
coefficients of any `HasProd` limit are read off a finite product (`coeff_of_hasProd`).  A real
family `v` *dominates* `u` (`Dom`) if `‖[Xⁿ] u i‖ ≤ [Xⁿ] v i`; with `v i` nonnegative,
`[X⁰] v i ≥ 1`, and `∏_{i<N} Σₙ [Xⁿ](v i) rⁿ ≤ C`, we get

  `bridge`: for `‖q‖ ≤ r`, `Σₙ [Xⁿ]F · qⁿ` converges absolutely and is the limit of
  `∏_{i<N} ev (u i) q`, where `ev f q = Σ' [Xⁿ]f · qⁿ`.

## Main declarations
* `coeff_prod_range_stable`, `coeff_of_hasProd` (stabilisation);
* `Nonneg`, `Dom`, `Dom.mul`, `Dom.prod_range`, `coeff_prod_range_mono`;
* `ev`, `evR`, `SumAt`, `ev_mul`, `SumAt.mul`, `evR_mul`, `ev_prod_range`;
* `bridge`, and the specialisations
  `hasProd_ev_one_sub_pow` (`∏(1 - q^{e i})^m`) and `hasProd_ev_geom_pow`
  (`∏(1 - q^{e i})^{-m}`) for exponents `e i ≥ i + 1`.

## Status
All declarations proved, no `sorry`, no new axioms; generic (no VOA content).
-/

set_option linter.style.longLine false

namespace VOA

namespace QBridge

open PowerSeries Filter Topology Finset

/-! ## §1  Stabilisation of partial products -/

section Stab

variable {R : Type*} [CommRing R]

theorem coeff_mul_of_dvd_sub_one {n : ℕ} (f g : R⟦X⟧) (hg : X ^ (n + 1) ∣ g - 1) :
    coeff n (f * g) = coeff n f := by
  obtain ⟨w, hw⟩ := hg
  have : g = 1 + X ^ (n + 1) * w := by rw [← hw]; ring
  rw [this, mul_add, mul_one, map_add, mul_left_comm, coeff_X_pow_mul', if_neg (by omega),
    add_zero]

theorem coeff_prod_range_stable (u : ℕ → R⟦X⟧) (hu : ∀ i, X ^ (i + 1) ∣ u i - 1) {n N : ℕ}
    (hN : n ≤ N) : coeff n (∏ i ∈ range N, u i) = coeff n (∏ i ∈ range n, u i) := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [prod_range_succ, coeff_mul_of_dvd_sub_one _ _
      ((pow_dvd_pow X (by omega : n + 1 ≤ N + 1)).trans (hu N)), ih]

open scoped PowerSeries.WithPiTopology in
theorem coeff_of_hasProd [TopologicalSpace R] [T2Space R] {u : ℕ → R⟦X⟧} {F : R⟦X⟧}
    (h : HasProd u F) (hu : ∀ i, X ^ (i + 1) ∣ u i - 1) (n : ℕ) :
    coeff n F = coeff n (∏ i ∈ range n, u i) := by
  have hc := ((PowerSeries.WithPiTopology.continuous_coeff R n).tendsto F).comp
    h.tendsto_prod_nat
  refine tendsto_nhds_unique hc ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop n] with N hN
  exact (coeff_prod_range_stable u hu hN).symm

theorem dvd_sub_one_mul {k : ℕ} {f g : R⟦X⟧} (hf : X ^ k ∣ f - 1) (hg : X ^ k ∣ g - 1) :
    X ^ k ∣ f * g - 1 := by
  have : f * g - 1 = (f - 1) * g + (g - 1) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left hf _) hg

theorem dvd_sub_one_pow {k : ℕ} {f : R⟦X⟧} (hf : X ^ k ∣ f - 1) (m : ℕ) :
    X ^ k ∣ f ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ]; exact dvd_sub_one_mul ih hf

end Stab

/-! ## §2  Real majorants -/

/-- A real power series with nonnegative coefficients. -/
def Nonneg (g : ℝ⟦X⟧) : Prop := ∀ n, 0 ≤ coeff n g

theorem Nonneg.mul {g h : ℝ⟦X⟧} (hg : Nonneg g) (hh : Nonneg h) : Nonneg (g * h) := fun n => by
  rw [coeff_mul]
  exact sum_nonneg fun p _ => mul_nonneg (hg _) (hh _)

theorem Nonneg.one : Nonneg 1 := fun n => by
  rw [coeff_one]; split_ifs <;> norm_num

theorem Nonneg.pow {g : ℝ⟦X⟧} (hg : Nonneg g) (m : ℕ) : Nonneg (g ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact Nonneg.one
  | succ m ih => rw [pow_succ]; exact ih.mul hg

theorem Nonneg.prod_range {v : ℕ → ℝ⟦X⟧} (hv : ∀ i, Nonneg (v i)) (N : ℕ) :
    Nonneg (∏ i ∈ range N, v i) := by
  induction N with
  | zero => rw [prod_range_zero]; exact Nonneg.one
  | succ N ih => rw [prod_range_succ]; exact ih.mul (hv N)

theorem coeff_le_coeff_mul {g h : ℝ⟦X⟧} (hg : Nonneg g) (hh : Nonneg h) (h0 : 1 ≤ coeff 0 h)
    (n : ℕ) : coeff n g ≤ coeff n (g * h) := by
  rw [coeff_mul]
  calc coeff n g ≤ coeff n g * coeff 0 h := le_mul_of_one_le_right (hg n) h0
    _ ≤ ∑ p ∈ antidiagonal n, coeff p.1 g * coeff p.2 h :=
      single_le_sum (f := fun p : ℕ × ℕ => coeff p.1 g * coeff p.2 h)
        (fun p _ => mul_nonneg (hg _) (hh _))
        (mem_antidiagonal.mpr (add_zero n) : ((n, 0) : ℕ × ℕ) ∈ antidiagonal n)

theorem constantCoeff_ge_one_mul {g h : ℝ⟦X⟧} (hg : 1 ≤ coeff 0 g) (hh : 1 ≤ coeff 0 h) :
    1 ≤ coeff 0 (g * h) := by
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply,
    ← coeff_zero_eq_constantCoeff_apply]
  nlinarith

theorem coeff_prod_range_mono {v : ℕ → ℝ⟦X⟧} (hv : ∀ i, Nonneg (v i))
    (h1 : ∀ i, 1 ≤ coeff 0 (v i)) {N N' : ℕ} (h : N ≤ N') (n : ℕ) :
    coeff n (∏ i ∈ range N, v i) ≤ coeff n (∏ i ∈ range N', v i) := by
  induction N', h using Nat.le_induction with
  | base => exact le_rfl
  | succ N' _ ih =>
    rw [prod_range_succ]
    exact ih.trans (coeff_le_coeff_mul (Nonneg.prod_range hv N') (hv N') (h1 N') n)

/-- `v` dominates `f` coefficientwise. -/
def Dom (f : ℂ⟦X⟧) (g : ℝ⟦X⟧) : Prop := ∀ n, ‖coeff n f‖ ≤ coeff n g

theorem Dom.mul {f f' : ℂ⟦X⟧} {g g' : ℝ⟦X⟧} (hf : Dom f g) (hf' : Dom f' g') (hg : Nonneg g) :
    Dom (f * f') (g * g') := fun n => by
  rw [coeff_mul, coeff_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun p _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hf _) (hf' _) (norm_nonneg _) (hg _)

theorem Dom.one : Dom 1 1 := fun n => by
  rw [coeff_one, coeff_one]; split_ifs <;> simp

theorem Dom.pow {f : ℂ⟦X⟧} {g : ℝ⟦X⟧} (hf : Dom f g) (hg : Nonneg g) (m : ℕ) :
    Dom (f ^ m) (g ^ m) := by
  induction m with
  | zero => simp only [pow_zero]; exact Dom.one
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul hf (hg.pow m)

theorem Dom.prod_range {u : ℕ → ℂ⟦X⟧} {v : ℕ → ℝ⟦X⟧} (hd : ∀ i, Dom (u i) (v i))
    (hv : ∀ i, Nonneg (v i)) (N : ℕ) : Dom (∏ i ∈ range N, u i) (∏ i ∈ range N, v i) := by
  induction N with
  | zero => simp only [prod_range_zero]; exact Dom.one
  | succ N ih => rw [prod_range_succ, prod_range_succ]; exact ih.mul (hd N) (Nonneg.prod_range hv N)

/-! ## §3  Evaluation -/

/-- Evaluation of a complex power series at `q` (a `tsum`; meaningful when it converges). -/
noncomputable def ev (f : ℂ⟦X⟧) (q : ℂ) : ℂ := ∑' n, coeff n f * q ^ n

/-- Evaluation of a real power series at `r`. -/
noncomputable def evR (g : ℝ⟦X⟧) (r : ℝ) : ℝ := ∑' n, coeff n g * r ^ n

/-- The real series `Σ [Xⁿ]g · rⁿ` converges. -/
def SumAt (g : ℝ⟦X⟧) (r : ℝ) : Prop := Summable fun n => coeff n g * r ^ n

theorem coeff_mul_pow_eq_sum {R : Type*} [CommRing R] (f g : R⟦X⟧) (q : R) (n : ℕ) :
    coeff n (f * g) * q ^ n
      = ∑ kl ∈ antidiagonal n, (coeff kl.1 f * q ^ kl.1) * (coeff kl.2 g * q ^ kl.2) := by
  rw [coeff_mul, sum_mul]
  refine sum_congr rfl fun kl hkl => ?_
  rw [mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring

theorem norm_eq_of_nonneg {g : ℝ⟦X⟧} (hg : Nonneg g) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    ‖coeff n g * r ^ n‖ = coeff n g * r ^ n :=
  Real.norm_of_nonneg (mul_nonneg (hg n) (pow_nonneg hr n))

theorem SumAt.mul {g h : ℝ⟦X⟧} (hg : Nonneg g) (hh : Nonneg h) {r : ℝ} (hr : 0 ≤ r)
    (sg : SumAt g r) (sh : SumAt h r) : SumAt (g * h) r := by
  have sg' : Summable fun n => ‖coeff n g * r ^ n‖ := by
    simpa only [norm_eq_of_nonneg hg hr] using sg
  have sh' : Summable fun n => ‖coeff n h * r ^ n‖ := by
    simpa only [norm_eq_of_nonneg hh hr] using sh
  have := summable_norm_sum_mul_antidiagonal_of_summable_norm sg' sh'
  unfold SumAt
  simp_rw [coeff_mul_pow_eq_sum]
  exact this.of_norm

theorem evR_mul {g h : ℝ⟦X⟧} (hg : Nonneg g) (hh : Nonneg h) {r : ℝ} (hr : 0 ≤ r)
    (sg : SumAt g r) (sh : SumAt h r) : evR (g * h) r = evR g r * evR h r := by
  have sg' : Summable fun n => ‖coeff n g * r ^ n‖ := by
    simpa only [norm_eq_of_nonneg hg hr] using sg
  have sh' : Summable fun n => ‖coeff n h * r ^ n‖ := by
    simpa only [norm_eq_of_nonneg hh hr] using sh
  have hm := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm sg' sh'
  unfold evR
  rw [hm]
  exact tsum_congr fun n => coeff_mul_pow_eq_sum g h r n

theorem SumAt.one {r : ℝ} : SumAt 1 r := by
  unfold SumAt
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  rw [coeff_one, if_neg (by simpa using hn), zero_mul]

theorem evR_one {r : ℝ} : evR 1 r = 1 := by
  rw [evR, tsum_eq_single 0 fun n hn => by rw [coeff_one, if_neg hn, zero_mul]]
  simp

theorem sumAt_evR_prod_range {v : ℕ → ℝ⟦X⟧} (hv : ∀ i, Nonneg (v i)) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ i, SumAt (v i) r) (N : ℕ) :
    SumAt (∏ i ∈ range N, v i) r ∧ evR (∏ i ∈ range N, v i) r = ∏ i ∈ range N, evR (v i) r := by
  induction N with
  | zero => simp only [prod_range_zero]; exact ⟨SumAt.one, evR_one⟩
  | succ N ih =>
    rw [prod_range_succ, prod_range_succ]
    exact ⟨ih.1.mul (Nonneg.prod_range hv N) (hv N) hr (hs N),
      by rw [evR_mul (Nonneg.prod_range hv N) (hv N) hr ih.1 (hs N), ih.2]⟩

theorem summable_norm_of_dom {f : ℂ⟦X⟧} {g : ℝ⟦X⟧} (hd : Dom f g) (hg : Nonneg g) {r : ℝ}
    (hs : SumAt g r) {q : ℂ} (hq : ‖q‖ ≤ r) : Summable fun n => ‖coeff n f * q ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  rw [norm_mul, norm_pow]
  exact mul_le_mul (hd n) (pow_le_pow_left₀ (norm_nonneg _) hq n)
    (pow_nonneg (norm_nonneg _) n) (hg n)

theorem summable_norm_mul {f g : ℂ⟦X⟧} {q : ℂ} (hf : Summable fun n => ‖coeff n f * q ^ n‖)
    (hg : Summable fun n => ‖coeff n g * q ^ n‖) :
    Summable fun n => ‖coeff n (f * g) * q ^ n‖ := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm (R := ℂ)
    (f := fun n => coeff n f * q ^ n) (g := fun n => coeff n g * q ^ n) hf hg
  exact h.congr fun n => by rw [coeff_mul_pow_eq_sum]

theorem ev_mul {f g : ℂ⟦X⟧} {q : ℂ} (hf : Summable fun n => ‖coeff n f * q ^ n‖)
    (hg : Summable fun n => ‖coeff n g * q ^ n‖) : ev (f * g) q = ev f q * ev g q := by
  have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (R := ℂ)
    (f := fun n => coeff n f * q ^ n) (g := fun n => coeff n g * q ^ n) hf hg
  unfold ev
  rw [h]
  exact tsum_congr fun n => coeff_mul_pow_eq_sum f g q n

theorem ev_one {q : ℂ} : ev 1 q = 1 := by
  rw [ev, tsum_eq_single 0 fun n hn => by rw [coeff_one, if_neg hn, zero_mul]]
  simp

theorem summable_norm_one {q : ℂ} : Summable fun n => ‖coeff n (1 : ℂ⟦X⟧) * q ^ n‖ := by
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  rw [coeff_one, if_neg (by simpa using hn), zero_mul, norm_zero]

theorem ev_prod_range {u : ℕ → ℂ⟦X⟧} {q : ℂ} (hu : ∀ i, Summable fun n => ‖coeff n (u i) * q ^ n‖)
    (N : ℕ) : (Summable fun n => ‖coeff n (∏ i ∈ range N, u i) * q ^ n‖)
      ∧ ev (∏ i ∈ range N, u i) q = ∏ i ∈ range N, ev (u i) q := by
  induction N with
  | zero => simp only [prod_range_zero]; exact ⟨summable_norm_one, ev_one⟩
  | succ N ih =>
    rw [prod_range_succ, prod_range_succ]
    exact ⟨summable_norm_mul ih.1 (hu N), by rw [ev_mul ih.1 (hu N), ih.2]⟩

/-! ## §4  The bridge -/

/-- **The bridge** (Tannery).  A family `u` with `u i ≡ 1 (mod X^{i+1})`, dominated by a
nonnegative real family `v` (`v i ≡ 1 (mod X^{i+1})`, `[X⁰] v i ≥ 1`) whose evaluations at `r`
have uniformly bounded partial products: then for `‖q‖ ≤ r` and `F` with the stabilised
coefficients of `∏ u i`, the series `Σ [Xⁿ]F qⁿ` converges absolutely and equals
`lim_N ∏_{i<N} ev (u i) q`. -/
theorem bridge (u : ℕ → ℂ⟦X⟧) (v : ℕ → ℝ⟦X⟧) {r C : ℝ} (hr : 0 ≤ r)
    (hdom : ∀ i, Dom (u i) (v i)) (hnn : ∀ i, Nonneg (v i)) (h1 : ∀ i, 1 ≤ coeff 0 (v i))
    (hu : ∀ i, X ^ (i + 1) ∣ u i - 1) (hv : ∀ i, X ^ (i + 1) ∣ v i - 1)
    (hs : ∀ i, SumAt (v i) r) (hC : ∀ N, ∏ i ∈ range N, evR (v i) r ≤ C)
    (F : ℂ⟦X⟧) (hF : ∀ n, coeff n F = coeff n (∏ i ∈ range n, u i)) {q : ℂ} (hq : ‖q‖ ≤ r) :
    (Summable fun n => ‖coeff n F * q ^ n‖)
      ∧ Tendsto (fun N => ∏ i ∈ range N, ev (u i) q) atTop (𝓝 (ev F q)) := by
  set V : ℕ → ℝ⟦X⟧ := fun N => ∏ i ∈ range N, v i with hV
  set G : ℕ → ℂ⟦X⟧ := fun N => ∏ i ∈ range N, u i with hG
  -- the majorant
  have hb : ∀ N n, ‖coeff n (G N)‖ ≤ coeff n (V n) := by
    intro N n
    calc ‖coeff n (G N)‖ ≤ coeff n (V N) := Dom.prod_range hdom hnn N n
      _ ≤ coeff n (V (max N n)) := coeff_prod_range_mono hnn h1 (le_max_left N n) n
      _ = coeff n (V n) := coeff_prod_range_stable v hv (le_max_right N n)
  have hbF : ∀ n, ‖coeff n F‖ ≤ coeff n (V n) := fun n => by rw [hF]; exact hb n n
  have hbsum : Summable fun n => coeff n (V n) * r ^ n := by
    refine summable_of_sum_range_le (c := C)
      (fun n => mul_nonneg (Nonneg.prod_range hnn n n) (pow_nonneg hr n)) fun M => ?_
    have hsM := sumAt_evR_prod_range hnn hr hs M
    calc ∑ n ∈ range M, coeff n (V n) * r ^ n
        = ∑ n ∈ range M, coeff n (V M) * r ^ n := by
          refine sum_congr rfl fun n hn => ?_
          rw [coeff_prod_range_stable v hv (mem_range.mp hn).le]
      _ ≤ evR (V M) r := by
          rw [evR]
          exact hsM.1.sum_le_tsum _ (fun n _ => mul_nonneg (Nonneg.prod_range hnn M n)
            (pow_nonneg hr n))
      _ = ∏ i ∈ range M, evR (v i) r := hsM.2
      _ ≤ C := hC M
  have hbound : ∀ N n, ‖coeff n (G N) * q ^ n‖ ≤ coeff n (V n) * r ^ n := by
    intro N n
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hb N n) (pow_le_pow_left₀ (norm_nonneg _) hq n)
      (pow_nonneg (norm_nonneg _) n) ((norm_nonneg _).trans (hb N n))
  have hsumF : Summable fun n => ‖coeff n F * q ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbsum
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hbF n) (pow_le_pow_left₀ (norm_nonneg _) hq n)
      (pow_nonneg (norm_nonneg _) n) ((norm_nonneg _).trans (hbF n))
  refine ⟨hsumF, ?_⟩
  have hus : ∀ i, Summable fun n => ‖coeff n (u i) * q ^ n‖ := fun i =>
    summable_norm_of_dom (hdom i) (hnn i) (hs i) hq
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun N n => coeff n (G N) * q ^ n) (g := fun n => coeff n F * q ^ n) hbsum
    (fun n => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n] with N hN
      simp only [hG]
      rw [hF, coeff_prod_range_stable u hu hN])
    (Eventually.of_forall fun N n => hbound N n)
  refine hT.congr fun N => ?_
  exact (ev_prod_range hus N).2

/-! ## §5  The two factor shapes -/

section Shapes

/-- The geometric series `Σ_j X^{kj} = (1 - X^k)^{-1}`. -/
noncomputable def geom (R : Type*) [CommRing R] (k : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun n => if k ∣ n then 1 else 0

theorem geom_mul_one_sub (R : Type*) [CommRing R] {k : ℕ} (hk : 0 < k) :
    geom R k * (1 - X ^ k) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, mul_comm, coeff_X_pow_mul', coeff_one, geom, coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos (dvd_zero k), if_neg (by omega), if_pos rfl, sub_zero]
  · rw [if_neg hn.ne']
    by_cases hkn : k ≤ n
    · rw [if_pos hkn, coeff_mk]
      have : k ∣ n ↔ k ∣ n - k := by
        conv_lhs => rw [show n = (n - k) + k by omega]
        exact Nat.dvd_add_self_right
      by_cases h : k ∣ n
      · rw [if_pos h, if_pos (this.mp h), sub_self]
      · rw [if_neg h, if_neg (mt this.mpr h), sub_self]
    · rw [if_neg hkn, if_neg (Nat.not_dvd_of_pos_of_lt hn (by omega)), sub_zero]

theorem geom_eq_one_add (R : Type*) [CommRing R] {k : ℕ} (hk : 0 < k) :
    geom R k = 1 + X ^ k * geom R k := by
  have := geom_mul_one_sub R hk
  linear_combination this

theorem dvd_geom_sub_one (R : Type*) [CommRing R] {k i : ℕ} (hk : i + 1 ≤ k) :
    X ^ (i + 1) ∣ geom R k - 1 := by
  rw [geom_eq_one_add R (by omega), add_sub_cancel_left]
  exact (pow_dvd_pow X hk).trans (dvd_mul_right _ _)

theorem dvd_one_sub_X_pow_sub_one (R : Type*) [CommRing R] {k i : ℕ} (hk : i + 1 ≤ k) :
    X ^ (i + 1) ∣ ((1 : R⟦X⟧) - X ^ k) - 1 := by
  rw [sub_sub_cancel_left]
  exact (dvd_neg).mpr (pow_dvd_pow X hk)

theorem dvd_one_add_X_pow_sub_one (R : Type*) [CommRing R] {k i : ℕ} (hk : i + 1 ≤ k) :
    X ^ (i + 1) ∣ ((1 : R⟦X⟧) + X ^ k) - 1 := by
  rw [add_sub_cancel_left]
  exact pow_dvd_pow X hk

theorem coeff_geom (R : Type*) [CommRing R] (k n : ℕ) :
    coeff n (geom R k) = if k ∣ n then 1 else 0 := by
  rw [geom, coeff_mk]

theorem nonneg_geom (k : ℕ) : Nonneg (geom ℝ k) := fun n => by
  rw [coeff_geom]; split_ifs <;> norm_num

theorem nonneg_one_add_X_pow (k : ℕ) : Nonneg (1 + X ^ k : ℝ⟦X⟧) := fun n => by
  rw [map_add, coeff_one, coeff_X_pow]; split_ifs <;> norm_num

theorem dom_geom (k : ℕ) : Dom (geom ℂ k) (geom ℝ k) := fun n => by
  rw [coeff_geom, coeff_geom]; split_ifs <;> simp

theorem dom_one_sub_X_pow {k : ℕ} (hk : 0 < k) : Dom (1 - X ^ k) (1 + X ^ k) := fun n => by
  rw [map_sub, map_add, coeff_one, coeff_one, coeff_X_pow, coeff_X_pow]
  by_cases h0 : n = 0
  · subst h0; rw [if_pos rfl, if_pos rfl, if_neg (by omega), if_neg (by omega)]; simp
  · rw [if_neg h0, if_neg h0]; split_ifs <;> simp

theorem one_le_coeff_zero_pow {g : ℝ⟦X⟧} (h : 1 ≤ coeff 0 g) (m : ℕ) : 1 ≤ coeff 0 (g ^ m) := by
  rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply]
  exact one_le_pow₀ h

theorem one_le_coeff_zero_geom (k : ℕ) : 1 ≤ coeff 0 (geom ℝ k) := by
  rw [coeff_geom, if_pos (dvd_zero k)]

theorem one_le_coeff_zero_one_add {k : ℕ} (hk : 0 < k) : 1 ≤ coeff 0 (1 + X ^ k : ℝ⟦X⟧) := by
  rw [map_add, coeff_one, coeff_X_pow, if_pos rfl, if_neg (by omega)]; norm_num

theorem sumAt_geom {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (k : ℕ) : SumAt (geom ℝ k) r := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (nonneg_geom k n) (pow_nonneg hr0 n))
    (fun n => ?_) (summable_geometric_of_lt_one hr0 hr)
  rw [coeff_geom]; split_ifs
  · rw [one_mul]
  · rw [zero_mul]; exact pow_nonneg hr0 n

theorem sumAt_one_add_X_pow {r : ℝ} (k : ℕ) : SumAt (1 + X ^ k : ℝ⟦X⟧) r := by
  unfold SumAt
  refine summable_of_ne_finset_zero (s := {0, k}) fun n hn => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  rw [map_add, coeff_one, coeff_X_pow, if_neg hn.1, if_neg hn.2]; simp

theorem sumAt_evR_pow {g : ℝ⟦X⟧} (hg : Nonneg g) {r : ℝ} (hr : 0 ≤ r) (s : SumAt g r) (m : ℕ) :
    SumAt (g ^ m) r ∧ evR (g ^ m) r = evR g r ^ m := by
  induction m with
  | zero => simp only [pow_zero]; exact ⟨SumAt.one, evR_one⟩
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact ⟨ih.1.mul (hg.pow m) hg hr s, by rw [evR_mul (hg.pow m) hg hr ih.1 s, ih.2]⟩

theorem hasSum_geom {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {k : ℕ} (hk : 0 < k) {x : 𝕜} (hx : ‖x‖ < 1) :
    HasSum (fun n => coeff n (geom 𝕜 k) * x ^ n) (1 - x ^ k)⁻¹ := by
  have hinj : Function.Injective fun j : ℕ => k * j := fun a b h => by
    simpa [hk.ne'] using h
  have hxk : ‖x ^ k‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx hk.ne'
  rw [← hinj.hasSum_iff]
  · convert hasSum_geometric_of_norm_lt_one hxk using 1
    funext j
    simp only [Function.comp_apply, coeff_geom, dvd_mul_right, if_true, one_mul, pow_mul]
  · intro n hn
    rw [coeff_geom, if_neg, zero_mul]
    rintro ⟨j, rfl⟩
    exact hn ⟨j, rfl⟩

theorem evR_geom {k : ℕ} (hk : 0 < k) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    evR (geom ℝ k) r = (1 - r ^ k)⁻¹ :=
  (hasSum_geom hk (by rwa [Real.norm_of_nonneg hr0])).tsum_eq

theorem ev_geom {k : ℕ} (hk : 0 < k) {q : ℂ} (hq : ‖q‖ < 1) :
    ev (geom ℂ k) q = (1 - q ^ k)⁻¹ :=
  (hasSum_geom hk hq).tsum_eq

theorem evR_one_add_X_pow {k : ℕ} (hk : 0 < k) (r : ℝ) : evR (1 + X ^ k : ℝ⟦X⟧) r = 1 + r ^ k := by
  rw [evR, tsum_eq_sum (s := {0, k}) fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [map_add, coeff_one, coeff_X_pow, if_neg hn.1, if_neg hn.2]; simp]
  rw [Finset.sum_pair hk.ne]
  simp [coeff_one, hk.ne']

theorem summable_norm_one_sub_X_pow (k : ℕ) (q : ℂ) :
    Summable fun n => ‖coeff n (1 - X ^ k : ℂ⟦X⟧) * q ^ n‖ := by
  refine summable_of_ne_finset_zero (s := {0, k}) fun n hn => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  rw [map_sub, coeff_one, coeff_X_pow, if_neg hn.1, if_neg hn.2]; simp

theorem ev_one_sub_X_pow {k : ℕ} (hk : 0 < k) (q : ℂ) : ev (1 - X ^ k : ℂ⟦X⟧) q = 1 - q ^ k := by
  rw [ev, tsum_eq_sum (s := {0, k}) fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [map_sub, coeff_one, coeff_X_pow, if_neg hn.1, if_neg hn.2]; simp]
  rw [Finset.sum_pair hk.ne]
  simp [coeff_one, hk.ne']
  ring

theorem ev_pow {f : ℂ⟦X⟧} {q : ℂ} (hs : Summable fun n => ‖coeff n f * q ^ n‖) (m : ℕ) :
    (Summable fun n => ‖coeff n (f ^ m) * q ^ n‖) ∧ ev (f ^ m) q = ev f q ^ m := by
  induction m with
  | zero => simp only [pow_zero]; exact ⟨summable_norm_one, ev_one⟩
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact ⟨summable_norm_mul ih.1 hs, by rw [ev_mul ih.1 hs, ih.2]⟩

/-! ### Uniform bounds for the partial products -/

theorem sum_range_pow_exp_le {e : ℕ → ℕ} (he : ∀ i, i + 1 ≤ e i) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) (N : ℕ) : ∑ i ∈ range N, r ^ e i ≤ (1 - r)⁻¹ := by
  calc ∑ i ∈ range N, r ^ e i ≤ ∑ i ∈ range N, r ^ i :=
        sum_le_sum fun i _ => pow_le_pow_of_le_one hr0 hr.le (by have := he i; omega)
    _ ≤ ∑' i, r ^ i := (summable_geometric_of_lt_one hr0 hr).sum_le_tsum _
        (fun i _ => pow_nonneg hr0 i)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr

theorem prod_one_add_pow_le {e : ℕ → ℕ} (he : ∀ i, i + 1 ≤ e i) (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) (N : ℕ) :
    ∏ i ∈ range N, (1 + r ^ e i) ^ m ≤ Real.exp (m * (1 - r)⁻¹) := by
  calc ∏ i ∈ range N, (1 + r ^ e i) ^ m ≤ ∏ i ∈ range N, Real.exp (m * r ^ e i) := by
        refine prod_le_prod (fun i _ => pow_nonneg (by positivity) m) fun i _ => ?_
        rw [Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (r ^ e i)]) m
    _ = Real.exp (m * ∑ i ∈ range N, r ^ e i) := by
        rw [← Real.exp_sum, mul_sum]
    _ ≤ Real.exp (m * (1 - r)⁻¹) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sum_range_pow_exp_le he hr0 hr N)
          (Nat.cast_nonneg m))

theorem inv_one_sub_le_exp {t r : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) (hr : r < 1) :
    (1 - t)⁻¹ ≤ Real.exp (t * (1 - r)⁻¹) := by
  have h1 : 0 < 1 - t := by linarith
  have h2 : 0 < 1 - r := by linarith
  calc (1 - t)⁻¹ = t / (1 - t) + 1 := by field_simp; ring
    _ ≤ Real.exp (t / (1 - t)) := Real.add_one_le_exp _
    _ ≤ Real.exp (t * (1 - r)⁻¹) := by
        rw [Real.exp_le_exp, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ h2 (by linarith)) ht0

theorem prod_geom_pow_le {e : ℕ → ℕ} (he : ∀ i, i + 1 ≤ e i) (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) (N : ℕ) :
    ∏ i ∈ range N, ((1 - r ^ e i)⁻¹) ^ m ≤ Real.exp (m * ((1 - r)⁻¹ * (1 - r)⁻¹)) := by
  have hle : ∀ i, r ^ e i ≤ r := fun i =>
    pow_le_of_le_one hr0 hr.le (by have := he i; omega)
  calc ∏ i ∈ range N, ((1 - r ^ e i)⁻¹) ^ m
        ≤ ∏ i ∈ range N, Real.exp (m * (r ^ e i * (1 - r)⁻¹)) := by
        refine prod_le_prod (fun i _ => pow_nonneg (inv_nonneg.mpr (by linarith [hle i])) m)
          fun i _ => ?_
        rw [Real.exp_nat_mul]
        exact pow_le_pow_left₀ (inv_nonneg.mpr (by linarith [hle i]))
          (inv_one_sub_le_exp (pow_nonneg hr0 _) (hle i) hr) m
    _ = Real.exp (m * ((∑ i ∈ range N, r ^ e i) * (1 - r)⁻¹)) := by
        rw [← Real.exp_sum, sum_mul, mul_sum]
    _ ≤ Real.exp (m * ((1 - r)⁻¹ * (1 - r)⁻¹)) := by
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m))
        exact mul_le_mul_of_nonneg_right (sum_range_pow_exp_le he hr0 hr N)
          (inv_nonneg.mpr (by linarith))

/-! ### The two specialised bridges -/

/-- **Bridge for `∏ (1 - q^{e i})^m`** (`e i ≥ i + 1`). -/
theorem tendsto_ev_one_sub_pow {e : ℕ → ℕ} (he : ∀ i, i + 1 ≤ e i) (m : ℕ) {F : ℂ⟦X⟧}
    (hF : ∀ n, coeff n F = coeff n (∏ i ∈ range n, ((1 : ℂ⟦X⟧) - X ^ e i) ^ m))
    {q : ℂ} (hq : ‖q‖ < 1) :
    (Summable fun n => ‖coeff n F * q ^ n‖)
      ∧ Tendsto (fun N => ∏ i ∈ range N, (1 - q ^ e i) ^ m) atTop (𝓝 (ev F q)) := by
  have hpos : ∀ i, 0 < e i := fun i => by have := he i; omega
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hb := bridge (fun i => ((1 : ℂ⟦X⟧) - X ^ e i) ^ m) (fun i => ((1 : ℝ⟦X⟧) + X ^ e i) ^ m)
    hr0 (C := Real.exp (m * (1 - ‖q‖)⁻¹))
    (fun i => (dom_one_sub_X_pow (hpos i)).pow (nonneg_one_add_X_pow _) m)
    (fun i => (nonneg_one_add_X_pow _).pow m)
    (fun i => one_le_coeff_zero_pow (one_le_coeff_zero_one_add (hpos i)) m)
    (fun i => dvd_sub_one_pow (dvd_one_sub_X_pow_sub_one ℂ (he i)) m)
    (fun i => dvd_sub_one_pow (dvd_one_add_X_pow_sub_one ℝ (he i)) m)
    (fun i => (sumAt_evR_pow (nonneg_one_add_X_pow _) hr0 (sumAt_one_add_X_pow _) m).1)
    (fun N => by
      calc ∏ i ∈ range N, evR ((1 + X ^ e i) ^ m) ‖q‖
          = ∏ i ∈ range N, (1 + ‖q‖ ^ e i) ^ m := by
            refine prod_congr rfl fun i _ => ?_
            rw [(sumAt_evR_pow (nonneg_one_add_X_pow _) hr0 (sumAt_one_add_X_pow _) m).2,
              evR_one_add_X_pow (hpos i)]
        _ ≤ _ := prod_one_add_pow_le he m hr0 hq N)
    F hF le_rfl
  refine ⟨hb.1, hb.2.congr fun N => prod_congr rfl fun i _ => ?_⟩
  rw [(ev_pow (summable_norm_one_sub_X_pow _ q) m).2, ev_one_sub_X_pow (hpos i)]

/-- **Bridge for `∏ (1 - q^{e i})^{-m}`** (`e i ≥ i + 1`), the factors written as geometric
series `geom ℂ (e i) = Σ_j X^{(e i) j}`. -/
theorem tendsto_ev_geom_pow {e : ℕ → ℕ} (he : ∀ i, i + 1 ≤ e i) (m : ℕ) {F : ℂ⟦X⟧}
    (hF : ∀ n, coeff n F = coeff n (∏ i ∈ range n, (geom ℂ (e i)) ^ m))
    {q : ℂ} (hq : ‖q‖ < 1) :
    (Summable fun n => ‖coeff n F * q ^ n‖)
      ∧ Tendsto (fun N => ∏ i ∈ range N, ((1 - q ^ e i)⁻¹) ^ m) atTop (𝓝 (ev F q)) := by
  have hpos : ∀ i, 0 < e i := fun i => by have := he i; omega
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hb := bridge (fun i => (geom ℂ (e i)) ^ m) (fun i => (geom ℝ (e i)) ^ m)
    hr0 (C := Real.exp (m * ((1 - ‖q‖)⁻¹ * (1 - ‖q‖)⁻¹)))
    (fun i => (dom_geom _).pow (nonneg_geom _) m)
    (fun i => (nonneg_geom _).pow m)
    (fun i => one_le_coeff_zero_pow (one_le_coeff_zero_geom _) m)
    (fun i => dvd_sub_one_pow (dvd_geom_sub_one ℂ (he i)) m)
    (fun i => dvd_sub_one_pow (dvd_geom_sub_one ℝ (he i)) m)
    (fun i => (sumAt_evR_pow (nonneg_geom _) hr0 (sumAt_geom hr0 hq _) m).1)
    (fun N => by
      calc ∏ i ∈ range N, evR ((geom ℝ (e i)) ^ m) ‖q‖
          = ∏ i ∈ range N, ((1 - ‖q‖ ^ e i)⁻¹) ^ m := by
            refine prod_congr rfl fun i _ => ?_
            rw [(sumAt_evR_pow (nonneg_geom _) hr0 (sumAt_geom hr0 hq _) m).2,
              evR_geom (hpos i) hr0 hq]
        _ ≤ _ := prod_geom_pow_le he m hr0 hq N)
    F hF le_rfl
  refine ⟨hb.1, hb.2.congr fun N => prod_congr rfl fun i _ => ?_⟩
  have hs : Summable fun n => ‖coeff n (geom ℂ (e i)) * q ^ n‖ :=
    summable_norm_of_dom (dom_geom _) (nonneg_geom _) (sumAt_geom hr0 hq _) le_rfl
  rw [(ev_pow hs m).2, ev_geom (hpos i) hq]

end Shapes

end QBridge

end VOA
