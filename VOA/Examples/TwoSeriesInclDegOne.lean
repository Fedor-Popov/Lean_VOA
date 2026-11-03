/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesBoxFusion

/-!
# The structural half `BoxInclusion` in `T`-degree one

`BoxInclusion n r` asks: a `T`-polynomial of degree `r - N` passing the test (its image
`τ(J + x̃) · v₀^{2N}` lies in the span of products of `r` jets of `u², uv, v²`, modulo the jets of
`(J + x̃)ⁿ`) only involves `T_0, …, T_{N-1}`.  This file proves the slots of `T`-degree one
(`r = N + 1`) for every `n ≥ 2`, and every slot for `n = 1`.

The tool is one explicit specialisation of the jet variables into the dual numbers over `ℂ[s]`,

  `v(t) = √(1 + s t)`,    `u(t) = ε / √(1 + s t)`,    `ε² = 0`,

so that `v² = 1 + s t`, `uv = ε`, `u² = 0`, and `J = u'v - uv' = -ε s / (1 + s t)`.  Every jet of
`u², uv, v²` lands in `W 1`, where `W r` is the space of `a + ε b` with `deg a ≤ r` and
`deg b < r`; the spaces `W r` multiply (`W a · W b ⊆ W (a + b)`), so the products of `r` letters
land in `W r`.  The jets of `(J + x̃)ⁿ` are killed (`(J + x̃)` is a multiple of `ε`, `n ≥ 2`).  But
`T_M ↦ J_M = ε (-s)^{M+1}` and `v₀ ↦ 1`, so the test element of `T_M` has `ε`-part of degree
`M + 1 ≥ N + 1 = r` and is not in `W r`.

* `bSer`, `cSer` — `√(1 + s t)` and `1/√(1 + s t)` (binomial series, rescaled);
* `wSer` — `c' b - c b'`; `coeff_wSer` — its coefficients are `(-s)^{m+1}`;
* `chi` — the specialisation `JetPoly → ℂ[s][ε]`; `chiQ n` — its descent to `TestRing n`
  (`n ≥ 2`);
* `W r` — the filtration; `chiQ_testLetters_pow` — `testLetters n ^ r` lands in `W r`;
* `tn_not_mem_testSp` — `T_M` fails the `(N + 1, N)` test once `M ≥ N`;
* `boxInclusion_degOne` — **the `T`-degree-one slots of `BoxInclusion n r`**, every `n ≥ 2`;
* `boxInclusion_level_one` — **`BoxInclusion 1 r` for every `r`**;
* `boxInclusion_r_one` — **`BoxInclusion n 1` for every `n ≥ 1`**;
* `BoxInclusionHigh n r` — the remaining slots, `T`-degree at least two;
  `boxInclusion_of_high`;
* `twoSeries_gradedUnitary_of_strictModel_inclHigh` — Affine GU ⇒ GU of `M(2, 2n+3)`,
  conditional on `hA`, detection `det` and `BoxInclusionHigh n r` for every `r`;
* `twoSeries_gradedUnitary_of_strictModel_level_one` — for `n = 1` (`M(2,5)`), conditional on
  `hA` and detection `det` only.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.InvariantSymbol VOA.SocleEval
open VOA.AdamovicSymbol Module
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

namespace InclDegOne

/-- `ℂ[s]`. -/
abbrev Pl : Type := Polynomial ℂ

/-- The dual numbers `ℂ[s][ε]`, `ε² = 0`. -/
abbrev DP : Type := DualNumber Pl

/-! ### The two series -/

/-- `√(1 + s t)`. -/
def bSer : PowerSeries Pl :=
  PowerSeries.rescale (Polynomial.X : Pl) (PowerSeries.binomialSeries Pl (1 / 2 : ℂ))

/-- `1 / √(1 + s t)`. -/
def cSer : PowerSeries Pl :=
  PowerSeries.rescale (Polynomial.X : Pl) (PowerSeries.binomialSeries Pl (-(1 / 2) : ℂ))

theorem bSer_mul_bSer :
    bSer * bSer = 1 + PowerSeries.C (Polynomial.X : Pl) * PowerSeries.X := by
  rw [bSer, ← map_mul, ← PowerSeries.binomialSeries_add]
  have h : (1 / 2 : ℂ) + 1 / 2 = ((1 : ℕ) : ℂ) := by norm_num
  rw [h, PowerSeries.binomialSeries_nat, pow_one, map_add, map_one, PowerSeries.rescale_X]

theorem cSer_mul_bSer : cSer * bSer = 1 := by
  rw [cSer, bSer, ← map_mul, ← PowerSeries.binomialSeries_add, neg_add_cancel,
    PowerSeries.binomialSeries_zero, map_one]

theorem coeff_zero_bSer : PowerSeries.coeff 0 bSer = 1 := by
  rw [bSer, PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.binomialSeries_coeff,
    Ring.choose_zero_right, one_smul]

/-- `c' b - c b'` (`'` is `d/dt`). -/
def wSer : PowerSeries Pl :=
  cSer.derivativeFun * bSer - cSer * bSer.derivativeFun

theorem derivativeFun_one_add (a : Pl) :
    (1 + PowerSeries.C a * PowerSeries.X).derivativeFun = PowerSeries.C a := by
  refine PowerSeries.ext fun k => ?_
  rw [PowerSeries.coeff_derivativeFun, map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X, PowerSeries.coeff_C]
  rcases k with _ | k <;> simp

theorem wSer_mul :
    wSer * (1 + PowerSeries.C (Polynomial.X : Pl) * PowerSeries.X) =
      -PowerSeries.C (Polynomial.X : Pl) := by
  have h1 : cSer.derivativeFun * bSer + cSer * bSer.derivativeFun = 0 := by
    have := congrArg PowerSeries.derivativeFun cSer_mul_bSer
    rw [PowerSeries.derivativeFun_mul, PowerSeries.derivativeFun_one, smul_eq_mul,
      smul_eq_mul] at this
    rw [← this]; ring
  have h2 : 2 * bSer * bSer.derivativeFun = PowerSeries.C (Polynomial.X : Pl) := by
    have := congrArg PowerSeries.derivativeFun bSer_mul_bSer
    rw [PowerSeries.derivativeFun_mul, smul_eq_mul, derivativeFun_one_add] at this
    rw [← this]; ring
  rw [← bSer_mul_bSer, wSer]
  linear_combination (bSer * bSer) * h1 - (cSer * bSer) * h2 -
    PowerSeries.C (Polynomial.X : Pl) * cSer_mul_bSer

/-- **The coefficients of `c' b - c b' = -s/(1 + s t)`.** -/
theorem coeff_wSer (m : ℕ) : PowerSeries.coeff m wSer = (-Polynomial.X : Pl) ^ (m + 1) := by
  have key : ∀ k, PowerSeries.coeff k
      (wSer * (1 + PowerSeries.C (Polynomial.X : Pl) * PowerSeries.X)) =
      PowerSeries.coeff k wSer +
        (if k = 0 then 0 else Polynomial.X * PowerSeries.coeff (k - 1) wSer) := by
    intro k
    rw [mul_add, mul_one, map_add, ← mul_assoc, mul_comm wSer, mul_assoc, PowerSeries.coeff_C_mul]
    rcases k with _ | k
    · simp
    · rw [PowerSeries.coeff_succ_mul_X]; simp
  induction m with
  | zero =>
    have := key 0
    rw [wSer_mul, map_neg, PowerSeries.coeff_C] at this
    simp only [if_true] at this
    rw [zero_add, pow_one]
    linear_combination -this
  | succ m ih =>
    have := key (m + 1)
    rw [wSer_mul, map_neg, PowerSeries.coeff_C] at this
    simp only [Nat.add_one_ne_zero, if_false, add_tsub_cancel_right, neg_zero] at this
    rw [ih] at this
    rw [pow_succ]
    linear_combination -this

/-! ### The specialisation -/

/-- The images of the jet variables: `u_j ↦ ε c_j`, `v_j ↦ b_j`. -/
def chiV (x : Fin 2 × ℕ) : DP :=
  if x.1 = 0 then DualNumber.eps * TrivSqZeroExt.inl (PowerSeries.coeff x.2 cSer)
  else TrivSqZeroExt.inl (PowerSeries.coeff x.2 bSer)

/-- The specialisation `JetPoly → ℂ[s][ε]`. -/
def chi : JetPoly →ₐ[ℂ] DP := aeval chiV

/-- The inclusion `ℂ[s] → ℂ[s][ε]`. -/
abbrev inlP : Pl →+* DP := TrivSqZeroExt.inlHom Pl Pl

theorem map_derivative {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (g : PowerSeries A) :
    PowerSeries.map f (PowerSeries.derivative A g) =
      PowerSeries.derivative B (PowerSeries.map f g) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul]
  congr 1
  rw [map_add, map_natCast, map_one]

theorem map_derivativeFun {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (g : PowerSeries A) :
    PowerSeries.map f g.derivativeFun = PowerSeries.derivative B (PowerSeries.map f g) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivativeFun, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul]
  congr 1
  rw [map_add, map_natCast, map_one]

theorem map_chi_colSer_zero :
    PowerSeries.map chi.toRingHom (colSer 0) =
      PowerSeries.C DualNumber.eps * PowerSeries.map inlP cSer := by
  refine PowerSeries.ext fun j => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_map]
  simp [chi, chiV]

theorem map_chi_colSer_one :
    PowerSeries.map chi.toRingHom (colSer 1) = PowerSeries.map inlP bSer := by
  refine PowerSeries.ext fun j => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk, PowerSeries.coeff_map]
  simp [chi, chiV]

theorem derivative_C_mul {B : Type*} [CommRing B] (a : B) (g : PowerSeries B) :
    PowerSeries.derivative B (PowerSeries.C a * g) =
      PowerSeries.C a * PowerSeries.derivative B g := by
  rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul]

theorem map_chi_jSer :
    PowerSeries.map chi.toRingHom jSer =
      PowerSeries.C DualNumber.eps * PowerSeries.map inlP wSer := by
  rw [jSer, map_sub, map_mul, map_mul, map_derivative, map_derivative, map_chi_colSer_zero,
    map_chi_colSer_one, derivative_C_mul, wSer, map_sub, map_mul, map_mul, map_derivativeFun inlP,
    map_derivativeFun inlP]
  ring

theorem map_chi_xSer : PowerSeries.map chi.toRingHom xSer = 0 := by
  rw [xSer, map_mul, map_chi_colSer_zero]
  have : (PowerSeries.C DualNumber.eps : PowerSeries DP) * PowerSeries.C DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  linear_combination (PowerSeries.map inlP cSer * PowerSeries.map inlP cSer) * this

theorem chi_coeff_xSer (k : ℕ) : chi (PowerSeries.coeff k xSer) = 0 := by
  have h := PowerSeries.coeff_map chi.toRingHom k xSer
  rw [map_chi_xSer, map_zero] at h
  exact h.symm

theorem chi_coeff_jSer (m : ℕ) :
    chi (PowerSeries.coeff m jSer) =
      DualNumber.eps * TrivSqZeroExt.inl ((-Polynomial.X : Pl) ^ (m + 1)) := by
  have h := PowerSeries.coeff_map chi.toRingHom m jSer
  rw [map_chi_jSer, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, coeff_wSer] at h
  exact h.symm

theorem map_chi_testSer :
    PowerSeries.map chi.toRingHom testSer =
      PowerSeries.C DualNumber.eps * PowerSeries.map inlP wSer := by
  rw [← map_chi_jSer]
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, testSer, PowerSeries.coeff_mk]
  change chi _ = chi _
  rw [map_add, chi_coeff_xSer, add_zero]

theorem chi_testIdeal {n : ℕ} (hn : 2 ≤ n) : testIdeal n ≤ RingHom.ker chi.toRingHom := by
  rw [testIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, ← PowerSeries.coeff_map, map_pow, map_chi_testSer,
    mul_pow, ← map_pow]
  have : (DualNumber.eps : DP) ^ n = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, sq, DualNumber.eps_mul_eps, zero_mul]
  rw [this, map_zero, zero_mul, map_zero]

/-- The specialisation on the test ring (`n ≥ 2`). -/
def chiQ {n : ℕ} (hn : 2 ≤ n) : TestRing n →ₐ[ℂ] DP :=
  Ideal.Quotient.liftₐ (testIdeal n) chi fun _ ha => chi_testIdeal hn ha

theorem chiQ_tmk {n : ℕ} (hn : 2 ≤ n) (P : JetPoly) : chiQ hn (tmk n P) = chi P := rfl

/-! ### The filtration -/

/-- `W r`: the `a + ε b` with `deg a ≤ r` and `deg (s b) ≤ r`. -/
def W (r : ℕ) : Submodule ℂ DP where
  carrier := {x | (TrivSqZeroExt.fst x).degree ≤ (r : WithBot ℕ) ∧
    (Polynomial.X * TrivSqZeroExt.snd x).degree ≤ (r : WithBot ℕ)}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · rw [TrivSqZeroExt.fst_add]
      exact (Polynomial.degree_add_le _ _).trans (max_le hx1 hy1)
    · rw [TrivSqZeroExt.snd_add, mul_add]
      exact (Polynomial.degree_add_le _ _).trans (max_le hx2 hy2)
  zero_mem' := by simp
  smul_mem' := by
    rintro c x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · rw [TrivSqZeroExt.fst_smul]
      exact (Polynomial.degree_smul_le _ _).trans hx1
    · rw [TrivSqZeroExt.snd_smul, mul_smul_comm]
      exact (Polynomial.degree_smul_le _ _).trans hx2

theorem mem_W {r : ℕ} {x : DP} :
    x ∈ W r ↔ (TrivSqZeroExt.fst x).degree ≤ (r : WithBot ℕ) ∧
      (Polynomial.X * TrivSqZeroExt.snd x).degree ≤ (r : WithBot ℕ) := Iff.rfl

theorem mul_mem_W {a b : ℕ} {x y : DP} (hx : x ∈ W a) (hy : y ∈ W b) : x * y ∈ W (a + b) := by
  obtain ⟨hx1, hx2⟩ := mem_W.mp hx
  obtain ⟨hy1, hy2⟩ := mem_W.mp hy
  refine mem_W.mpr ⟨?_, ?_⟩
  · rw [TrivSqZeroExt.fst_mul, Nat.cast_add]
    exact (Polynomial.degree_mul_le _ _).trans (add_le_add hx1 hy1)
  · rw [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul,
      show Polynomial.X * (x.fst * y.snd + x.snd * y.fst) =
        x.fst * (Polynomial.X * y.snd) + (Polynomial.X * x.snd) * y.fst by ring, Nat.cast_add]
    refine (Polynomial.degree_add_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.degree_mul_le _ _).trans (add_le_add hx1 hy2)
    · exact (Polynomial.degree_mul_le _ _).trans (add_le_add hx2 hy1)

theorem inl_mem_W {r : ℕ} {p : Pl} (hp : p.degree ≤ (r : WithBot ℕ)) :
    (TrivSqZeroExt.inl p : DP) ∈ W r :=
  mem_W.mpr ⟨by simpa using hp, by simp⟩

theorem eps_inl_mem_W {r : ℕ} {p : Pl} (hp : (Polynomial.X * p).degree ≤ (r : WithBot ℕ)) :
    DualNumber.eps * (TrivSqZeroExt.inl p : DP) ∈ W r :=
  mem_W.mpr ⟨by simp, by simpa using hp⟩

/-! ### The letters land in `W 1` -/

theorem chi_coeff_zSer (m : ℕ) :
    chi (PowerSeries.coeff m zSer) =
      TrivSqZeroExt.inl (PowerSeries.coeff m
        (1 + PowerSeries.C (Polynomial.X : Pl) * PowerSeries.X)) := by
  have h := PowerSeries.coeff_map chi.toRingHom m zSer
  rw [zSer, map_mul, map_chi_colSer_one, ← map_mul, bSer_mul_bSer, PowerSeries.coeff_map] at h
  exact h.symm

theorem chi_coeff_ySer (m : ℕ) :
    chi (PowerSeries.coeff m ySer) =
      DualNumber.eps * TrivSqZeroExt.inl (PowerSeries.coeff m (1 : PowerSeries Pl)) := by
  have h := PowerSeries.coeff_map chi.toRingHom m ySer
  rw [ySer, map_mul, map_chi_colSer_zero, map_chi_colSer_one, mul_assoc, ← map_mul,
    cSer_mul_bSer, PowerSeries.coeff_C_mul, PowerSeries.coeff_map] at h
  exact h.symm

theorem degree_coeff_one_add_le (m : ℕ) :
    (PowerSeries.coeff m (1 + PowerSeries.C (Polynomial.X : Pl) * PowerSeries.X)).degree ≤ 1 := by
  rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  refine (Polynomial.degree_add_le _ _).trans (max_le ?_ ?_)
  · split_ifs
    · rw [Polynomial.degree_one]; exact zero_le_one
    · simp
  · split_ifs
    · rw [mul_one, Polynomial.degree_X]
    · simp

theorem chi_letter_mem_W (a : Fin 3) (m : ℕ) : chi (letterSym (.current a, m)) ∈ W 1 := by
  match a with
  | 0 =>
    change chi (PowerSeries.coeff m xSer) ∈ W 1
    rw [chi_coeff_xSer]; exact (W 1).zero_mem
  | 1 =>
    change chi (PowerSeries.coeff m (-zSer)) ∈ W 1
    rw [map_neg, map_neg, chi_coeff_zSer]
    exact (W 1).neg_mem (inl_mem_W (by exact_mod_cast degree_coeff_one_add_le m))
  | 2 =>
    change chi (PowerSeries.coeff m (-(ySer + ySer))) ∈ W 1
    rw [map_neg, map_add, map_neg, map_add, chi_coeff_ySer]
    refine (W 1).neg_mem ((W 1).add_mem ?_ ?_) <;>
    · refine eps_inl_mem_W ?_
      simp only [PowerSeries.coeff_one]
      split_ifs
      · rw [mul_one, Polynomial.degree_X]; rfl
      · simp

theorem chiQ_testLetters {n : ℕ} (hn : 2 ≤ n) :
    testLetters n ≤ (W 1).comap (chiQ hn).toLinearMap := by
  rw [testLetters, Submodule.span_le]
  rintro _ ⟨⟨a, m⟩, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply]
  dsimp only
  rw [testHom_mletter_current, chiQ_tmk]
  exact chi_letter_mem_W a m

/-- **Products of `r` letters land in `W r`.** -/
theorem chiQ_testLetters_pow {n : ℕ} (hn : 2 ≤ n) :
    ∀ r : ℕ, testLetters n ^ r ≤ (W r).comap (chiQ hn).toLinearMap
  | 0 => by
    intro x hx
    rw [pow_zero, Submodule.mem_one] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, AlgHom.commutes]
    refine mem_W.mpr ⟨?_, ?_⟩
    · rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_inl, Polynomial.algebraMap_eq]
      exact Polynomial.degree_C_le.trans (by simp)
    · rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, mul_zero]
      simp
  | r + 1 => by
    rw [pow_succ, Submodule.mul_le]
    intro x hx y hy
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, map_mul]
    exact mul_mem_W (chiQ_testLetters_pow hn r hx) (chiQ_testLetters hn hy)

/-! ### `T_M` fails the test for `M ≥ N` -/

theorem chi_v0 : chi (X (1, 0)) = 1 := by
  simp [chi, chiV, coeff_zero_bSer]

theorem degree_X_mul_negX_pow (M : ℕ) :
    (Polynomial.X * (-Polynomial.X : Pl) ^ (M + 1)).degree = ((M + 2 : ℕ) : WithBot ℕ) := by
  rw [neg_pow, ← mul_assoc, mul_comm Polynomial.X, mul_assoc, ← pow_succ']
  rw [Polynomial.degree_mul, Polynomial.degree_pow, Polynomial.degree_neg, Polynomial.degree_one,
    Polynomial.degree_X_pow, nsmul_zero, zero_add]

/-- **`T_M` fails the `(N + 1, N)` test once `M ≥ N`** (every `n ≥ 2`). -/
theorem tn_not_mem_testSp {n : ℕ} (hn : 2 ≤ n) {N M : ℕ} (hNM : N ≤ M) :
    tn n M ∉ testSp n (N + 1) N := by
  intro h
  rw [mem_testSp] at h
  have hW := chiQ_testLetters_pow hn (N + 1) h
  rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, map_mul, map_pow, ψn_tn, chiQ_tmk,
    chiQ_tmk, chi_v0, one_pow, mul_one, map_add, chi_coeff_xSer, add_zero, chi_coeff_jSer] at hW
  have h2 := (mem_W.mp hW).2
  rw [TrivSqZeroExt.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.fst_inl, smul_zero, zero_add, op_smul_eq_mul, one_mul,
    degree_X_mul_negX_pow] at h2
  have h3 : M + 2 ≤ N + 1 := by exact_mod_cast h2
  omega

/-! ### The `T`-degree-one slots -/

theorem tMonW_one_le {R : Type} [CommRing R] [Algebra ℂ R] (t : ℕ → R) (M : ℕ) :
    tMonW R t 1 ((M + 1 : ℕ) : ℤ) ≤ Submodule.span ℂ {t M} := by
  rw [tMonW, Submodule.span_le]
  rintro _ ⟨l, hl, he, rfl⟩
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at he
  have : a = M := by omega
  subst this
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact Submodule.subset_span rfl

/-- **`BoxInclusion` in `T`-degree one**: for `n ≥ 2`, a `T`-polynomial of degree one passing
the `(N + 1, N)` test only involves `T_0, …, T_{N-1}`. -/
theorem boxInclusion_degOne {n : ℕ} (hn : 2 ≤ n) (e : ℤ) (N : ℕ) :
    tMonW (Rn n) (tn n) 1 e ⊓ testSp n (N + 1) N ≤ boxW (tn n) N 1 e := by
  rintro τ ⟨hτ, hT⟩
  by_cases he : ∃ M : ℕ, ((M + 1 : ℕ) : ℤ) = e
  · obtain ⟨M, rfl⟩ := he
    have hspan := tMonW_one_le (tn n) M hτ
    by_cases hM : M < N
    · have hbox : tn n M ∈ boxW (tn n) N 1 ((M + 1 : ℕ) : ℤ) :=
        Submodule.subset_span ⟨[M], rfl, by simp, by simpa using hM, by simp⟩
      exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hbox)) hspan
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hspan
      by_cases hc : c = 0
      · rw [hc, zero_smul]; exact Submodule.zero_mem _
      · exfalso
        have : tn n M ∈ testSp n (N + 1) N := by
          have := (testSp n (N + 1) N).smul_mem c⁻¹ hT
          rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        exact tn_not_mem_testSp hn (by omega) this
  · have hbot : tMonW (Rn n) (tn n) 1 e = ⊥ := by
      rw [eq_bot_iff, tMonW, Submodule.span_le]
      rintro _ ⟨l, hl, hle, rfl⟩
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hle
      exact absurd ⟨a, hle⟩ he
    rw [hbot] at hτ
    rw [(Submodule.mem_bot ℂ).mp hτ]
    exact Submodule.zero_mem _

end InclDegOne

open InclDegOne

/-! ### `n = 1` -/

theorem tn_level_one (j : ℕ) : tn 1 j = 0 := by
  rw [tn, Ideal.Quotient.eq_zero_iff_mem, jetIdealT]
  refine Ideal.subset_span ⟨j, ?_⟩
  change PowerSeries.coeff j (tSer ^ 1) = X j
  rw [pow_one, tSer, PowerSeries.coeff_mk]

theorem tMonW_level_one {k : ℕ} (hk : 1 ≤ k) (e : ℤ) : tMonW (Rn 1) (tn 1) k e = ⊥ := by
  rw [eq_bot_iff, tMonW, Submodule.span_le]
  rintro _ ⟨l, hl, -, rfl⟩
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_length_pos (show 0 < l.length by omega)
  rw [SetLike.mem_coe, List.map_cons, List.prod_cons, tn_level_one, zero_mul]
  exact Submodule.zero_mem _

/-- **`BoxInclusion 1 r` for every `r`**: `R_1 = ℂ`, so there is nothing of positive
`T`-degree. -/
theorem boxInclusion_level_one (r : ℕ) : BoxInclusion 1 r := by
  intro d N hN
  rw [tMonW_level_one (by omega)]
  exact bot_le.trans' inf_le_left

/-! ### `r = 1` and the remaining slots -/

/-- **`BoxInclusion n 1` for every `n ≥ 1`.** -/
theorem boxInclusion_r_one {n : ℕ} (hn : 1 ≤ n) : BoxInclusion n 1 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact boxInclusion_level_one 1
  · intro d N hN
    obtain rfl : N = 0 := by omega
    exact boxInclusion_degOne h (d - (1 : ℕ)) 0

/-- **The remaining slots of `BoxInclusion n r`**: `T`-degree `r - N ≥ 2`. -/
def BoxInclusionHigh (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), N + 2 ≤ r →
    tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N ≤ boxW (tn n) N (r - N) (d - r)

/-- **`BoxInclusion` from its slots of `T`-degree at least two.** -/
theorem boxInclusion_of_high {n r : ℕ} (hn : 1 ≤ n) (h : BoxInclusionHigh n r) :
    BoxInclusion n r := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    exact boxInclusion_level_one r
  intro d N hN
  by_cases hk : N + 2 ≤ r
  · exact h d N hk
  · obtain rfl : r = N + 1 := by omega
    rw [show N + 1 - N = 1 by omega]
    exact boxInclusion_degOne hn2 (d - ((N + 1 : ℕ) : ℤ)) N

/-- `BoxInclusionHigh` is vacuous for `r ≤ 1`. -/
theorem boxInclusionHigh_of_le_one {n r : ℕ} (hr : r ≤ 1) : BoxInclusionHigh n r :=
  fun _ N hN => absurd hN (by omega)

/-! ### The endpoints -/

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional only on `hA`,
detection `det` and the slots of `BoxInclusion` of `T`-degree at least two. -/
theorem twoSeries_gradedUnitary_of_strictModel_inclHigh (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (incl : ∀ r, BoxInclusionHigh n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_incl n hn hA det fun r =>
    boxInclusion_of_high hn (incl r)

/-- **Affine GU ⇒ GU of `M(2, 5)`** (`n = 1`), `#print axioms`-clean, conditional only on
`hA` and detection `det`. -/
theorem twoSeries_gradedUnitary_of_strictModel_level_one
    (hA : GradedUnitary (affineForm (twoSeriesLevels 1)) (affineRealStructure (twoSeriesLevels 1))
      (affineFlag (twoSeriesLevels 1)))
    (det : TwoSeriesModelDetects 1) :
    VirGradedUnitary (twoSeriesLevels 1).c (targetRealStructure (twoSeriesLevels 1)) :=
  twoSeries_gradedUnitary_of_strictModel_incl 1 le_rfl hA det boxInclusion_level_one

end

end VOA.TwoSeries.StrictModel
