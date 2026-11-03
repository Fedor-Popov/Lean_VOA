/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesInclLead

/-!
# `BoxInclusion` below the nilpotency degree

This file proves the slots of `BoxInclusion n r` whose `T`-degree `k = r - N` is smaller than `n`.

The tool is one specialisation `chi` of the jet variables into the dual numbers `ℂ[s][ε]` over the
coefficient ring `Cq = ℂ[α, r₀, q₁, q₂, …]`:

  `v = √(1 + s t)`,    `u = α² ε / √(1 + s t) + η √(1 + s t)`,    `η = α ξ`,
  `ξ = r₀ + α Σ_{m ≥ 1} q_m t^m / m`,    `ε² = 0`.

Then `v² = 1 + s t`, `uv = α² ε + η v²`, `u² = 2 α² ε η + η² v²`, so every jet of `u², uv, v²` lies
in `W 1` (`a + ε b` with `deg_s a ≤ 1`, `deg_s b ≤ 0`), and products of `r` letters lie in `W r`.
Every Sugawara image is a multiple of `α²`: `chi(T_m) = α² (A_m + ε B_m)` with `deg_s A_m ≤ 1`,
`B_m = (-s)^{m+1} + O(s⁰)`.  Hence the jets of `(J + x̃)ⁿ` land in the ideal `(α^{2n})`, while a
`T`-polynomial `τ` of degree `k` maps to `α^{2k} τ(A + ε B)`.  For `k < n` the `ε s^{k+M} α^{2k}`
coefficient (with `M` the largest index in `τ`) survives, and at `α = 0` it equals
`± ∂_M τ (r₀², q₁, q₂, …)`, which vanishes only if `τ` does not involve `T_M`.

Main results (the leading-coefficient lemma `InclLead.lead_span`, the injectivity
`InclLead.aeval_sq_injective` of `T₀ ↦ T₀²` and `InclLead.not_mem_vars_of_pderiv_eq_zero` are in
`TwoSeriesInclLead`):

* `chi`, `W r`, `chi_Lpoly_pow` — products of `r` letters land in `W r`;
* `chi_tSug` — `chi(T_m) = α² (A_m + ε B_m)`; `chi_testIdeal` — the jets of `(J + x̃)ⁿ` land
  in `(α^{2n})`;
* `piA_sb` — at `α = 0` the `s`-coefficient of `A_m` is `r₀²` (`m = 0`) or `q_m` (`m ≥ 1`);
* `piA_coeff_eq_zero` — the test, read through `chi`, at `α = 0`;
* `InclLow.boxInclusion_low` — **every slot of `BoxInclusion n r` with `r - N < n`**;
* `boxInclusion_of_lt` — **`BoxInclusion n r` for every `r < n`**;
* `BoxInclusionTail n r` — the remaining slots (`r - N ≥ n`); `boxInclusion_of_tail`;
* `twoSeries_gradedUnitary_of_strictModel_inclTail` — Affine GU ⇒ GU of `M(2, 2n+3)`,
  conditional on `hA`, detection `det` and `BoxInclusionTail n r` for every `r`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.InvariantSymbol VOA.SocleEval
open VOA.AdamovicSymbol Module
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

-- The dual numbers over `Cq[s]` make instance search and unification expensive.
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace InclLow

/-! ### Generic square roots -/

section Series

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- `√(1 + s t)`. -/
def bS (s : A) : PowerSeries A :=
  PowerSeries.rescale s (PowerSeries.binomialSeries A (1 / 2 : ℂ))

/-- `1 / √(1 + s t)`. -/
def cS (s : A) : PowerSeries A :=
  PowerSeries.rescale s (PowerSeries.binomialSeries A (-(1 / 2) : ℂ))

theorem bS_mul_bS (s : A) : bS s * bS s = 1 + PowerSeries.C s * PowerSeries.X := by
  rw [bS, ← map_mul, ← PowerSeries.binomialSeries_add]
  have h : (1 / 2 : ℂ) + 1 / 2 = ((1 : ℕ) : ℂ) := by norm_num
  rw [h, PowerSeries.binomialSeries_nat, pow_one, map_add, map_one, PowerSeries.rescale_X]

theorem cS_mul_bS (s : A) : cS s * bS s = 1 := by
  rw [cS, bS, ← map_mul, ← PowerSeries.binomialSeries_add, neg_add_cancel,
    PowerSeries.binomialSeries_zero, map_one]

theorem coeff_zero_bS (s : A) : PowerSeries.coeff 0 (bS s) = 1 := by
  rw [bS, PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.binomialSeries_coeff,
    Ring.choose_zero_right, one_smul]

/-- `c' b - c b'`. -/
def wS (s : A) : PowerSeries A := (cS s).derivativeFun * bS s - cS s * (bS s).derivativeFun

omit [Algebra ℂ A] in
theorem derivativeFun_one_add' (a : A) :
    (1 + PowerSeries.C a * PowerSeries.X).derivativeFun = PowerSeries.C a := by
  refine PowerSeries.ext fun k => ?_
  rw [PowerSeries.coeff_derivativeFun, map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X, PowerSeries.coeff_C]
  rcases k with _ | k <;> simp

theorem wS_mul (s : A) :
    wS s * (1 + PowerSeries.C s * PowerSeries.X) = -PowerSeries.C s := by
  have h1 : (cS s).derivativeFun * bS s + cS s * (bS s).derivativeFun = 0 := by
    have := congrArg PowerSeries.derivativeFun (cS_mul_bS s)
    rw [PowerSeries.derivativeFun_mul, PowerSeries.derivativeFun_one, smul_eq_mul,
      smul_eq_mul] at this
    rw [← this]; ring
  have h2 : 2 * bS s * (bS s).derivativeFun = PowerSeries.C s := by
    have := congrArg PowerSeries.derivativeFun (bS_mul_bS s)
    rw [PowerSeries.derivativeFun_mul, smul_eq_mul, derivativeFun_one_add'] at this
    rw [← this]; ring
  rw [← bS_mul_bS, wS]
  linear_combination (bS s * bS s) * h1 - (cS s * bS s) * h2 - PowerSeries.C s * cS_mul_bS s

theorem coeff_wS (s : A) (m : ℕ) : PowerSeries.coeff m (wS s) = (-s) ^ (m + 1) := by
  have key : ∀ k, PowerSeries.coeff k (wS s * (1 + PowerSeries.C s * PowerSeries.X)) =
      PowerSeries.coeff k (wS s) +
        (if k = 0 then 0 else s * PowerSeries.coeff (k - 1) (wS s)) := by
    intro k
    rw [mul_add, mul_one, map_add, ← mul_assoc, mul_comm (wS s), mul_assoc,
      PowerSeries.coeff_C_mul]
    rcases k with _ | k
    · simp
    · rw [PowerSeries.coeff_succ_mul_X]; simp
  induction m with
  | zero =>
    have := key 0
    rw [wS_mul, map_neg, PowerSeries.coeff_C] at this
    simp only [if_true] at this
    rw [zero_add, pow_one]
    linear_combination -this
  | succ m ih =>
    have := key (m + 1)
    rw [wS_mul, map_neg, PowerSeries.coeff_C] at this
    simp only [Nat.add_one_ne_zero, if_false, add_tsub_cancel_right, neg_zero] at this
    rw [ih] at this
    rw [pow_succ]
    linear_combination -this

omit [Algebra ℂ A] in
theorem map_derivativeFun' {B : Type*} [CommRing B] (f : A →+* B) (g : PowerSeries A) :
    PowerSeries.map f g.derivativeFun = PowerSeries.derivative B (PowerSeries.map f g) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivativeFun, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul]
  congr 1
  rw [map_add, map_natCast, map_one]

omit [Algebra ℂ A] in
theorem map_derivativeFun'' {B : Type*} [CommRing B] (f : A →+* B) (g : PowerSeries A) :
    PowerSeries.map f g.derivativeFun = (PowerSeries.map f g).derivativeFun := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivativeFun, PowerSeries.coeff_derivativeFun,
    PowerSeries.coeff_map, map_mul]
  congr 1
  rw [map_add, map_natCast, map_one]

omit [Algebra ℂ A] in
theorem derivativeFun_C_mul' (a : A) (g : PowerSeries A) :
    (PowerSeries.C a * g).derivativeFun = PowerSeries.C a * g.derivativeFun := by
  rw [PowerSeries.derivativeFun_mul, PowerSeries.derivativeFun_C, smul_zero, add_zero,
    smul_eq_mul]

end Series

/-! ### The rings -/

/-- The coefficient ring `ℂ[α, r₀, q₁, q₂, …]` (`none ↦ α`, `some 0 ↦ r₀`, `some m ↦ q_m`). -/
abbrev Cq : Type := MvPolynomial (Option ℕ) ℂ

/-- `Cq[s]`. -/
abbrev Pl : Type := Polynomial Cq

/-- `Cq[s][ε]`, `ε² = 0`. -/
abbrev DP : Type := DualNumber Pl

/-- `α`. -/
abbrev al : Cq := X none

/-- `s`. -/
abbrev sv : Pl := Polynomial.X

/-- `α²` in `Cq[s]`. -/
abbrev a2 : Pl := Polynomial.C (al ^ 2)

/-- Constant series. -/
abbrev cst : PowerSeries Cq →+* PowerSeries Pl := PowerSeries.map Polynomial.C

/-- `Σ_{m ≥ 1} q_m t^m / m`. -/
def qS : PowerSeries Cq :=
  PowerSeries.mk fun m => if m = 0 then 0 else ((m : ℂ)⁻¹) • X (some m)

/-- `ξ = r₀ + α q`. -/
def ξS : PowerSeries Cq := PowerSeries.C (X (some 0)) + PowerSeries.C al * qS

/-- `η = α ξ`. -/
def ηS : PowerSeries Cq := PowerSeries.C al * ξS

/-- `v² = 1 + s t`. -/
abbrev zS : PowerSeries Pl := bS sv * bS sv

/-- The inclusion `Cq[s] → Cq[s][ε]`. -/
abbrev inlP : Pl →+* DP := TrivSqZeroExt.inlHom Pl Pl

/-- The images of the jet variables. -/
def chiV (x : Fin 2 × ℕ) : DP :=
  if x.1 = 0 then
    DualNumber.eps * TrivSqZeroExt.inl (PowerSeries.coeff x.2 (PowerSeries.C a2 * cS sv)) +
      TrivSqZeroExt.inl (PowerSeries.coeff x.2 (cst ηS * bS sv))
  else TrivSqZeroExt.inl (PowerSeries.coeff x.2 (bS sv))

/-- The specialisation. -/
def chi : JetPoly →ₐ[ℂ] DP := aeval chiV

/-- The `u`-series. -/
abbrev uHat : PowerSeries DP :=
  PowerSeries.C DualNumber.eps * PowerSeries.map inlP (PowerSeries.C a2 * cS sv) +
    PowerSeries.map inlP (cst ηS * bS sv)

/-- The `v`-series. -/
abbrev vHat : PowerSeries DP := PowerSeries.map inlP (bS sv)

theorem map_chi_colSer_zero : PowerSeries.map chi.toRingHom (colSer 0) = uHat := by
  refine PowerSeries.ext fun j => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_map, PowerSeries.coeff_map]
  simp [chi, chiV]

theorem map_chi_colSer_one : PowerSeries.map chi.toRingHom (colSer 1) = vHat := by
  refine PowerSeries.ext fun j => ?_
  rw [PowerSeries.coeff_map, colSer, PowerSeries.coeff_mk, PowerSeries.coeff_map]
  simp [chi, chiV]

theorem eps_sq : (PowerSeries.C DualNumber.eps : PowerSeries DP) * PowerSeries.C DualNumber.eps =
    0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

theorem derivative_C_mul' {B : Type*} [CommRing B] (a : B) (g : PowerSeries B) :
    PowerSeries.derivative B (PowerSeries.C a * g) =
      PowerSeries.C a * PowerSeries.derivative B g := by
  rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul]

theorem mapInl_mul (f g : PowerSeries Pl) :
    PowerSeries.map inlP (f * g) = PowerSeries.map inlP f * PowerSeries.map inlP g :=
  map_mul _ f g

theorem mapInl_add (f g : PowerSeries Pl) :
    PowerSeries.map inlP (f + g) = PowerSeries.map inlP f + PowerSeries.map inlP g :=
  map_add _ f g

theorem mapInl_sub (f g : PowerSeries Pl) :
    PowerSeries.map inlP (f - g) = PowerSeries.map inlP f - PowerSeries.map inlP g :=
  map_sub _ f g

theorem map_chi_jSer :
    PowerSeries.map chi.toRingHom jSer =
      PowerSeries.C DualNumber.eps * PowerSeries.map inlP (PowerSeries.C a2 * wS sv) +
        PowerSeries.map inlP ((cst ηS).derivativeFun * zS) := by
  have hP1 : (PowerSeries.C a2 * cS sv).derivativeFun =
      PowerSeries.C a2 * (cS sv).derivativeFun := derivativeFun_C_mul' _ _
  have hP0 : (cst ηS * bS sv).derivativeFun =
      cst ηS * (bS sv).derivativeFun + bS sv * (cst ηS).derivativeFun := by
    rw [PowerSeries.derivativeFun_mul, smul_eq_mul, smul_eq_mul]
  rw [jSer, map_sub, map_mul, map_mul, InclDegOne.map_derivative, InclDegOne.map_derivative,
    map_chi_colSer_zero, map_chi_colSer_one, map_add, derivative_C_mul', ← map_derivativeFun',
    ← map_derivativeFun', ← map_derivativeFun', hP1, hP0, wS]
  simp only [uHat, vHat, mapInl_mul, mapInl_sub, mapInl_add]
  ring

theorem map_chi_xSer :
    PowerSeries.map chi.toRingHom xSer =
      PowerSeries.C DualNumber.eps * PowerSeries.map inlP (PowerSeries.C (2 * a2) * cst ηS) +
        PowerSeries.map inlP (cst ηS * cst ηS * zS) := by
  rw [xSer, map_mul, map_chi_colSer_zero]
  have hcb := congrArg (PowerSeries.map inlP) (cS_mul_bS sv)
  rw [map_mul, map_one] at hcb
  simp only [mapInl_mul, uHat]
  rw [show PowerSeries.C (2 * a2) = 2 * PowerSeries.C a2 by rw [map_mul, map_ofNat], mapInl_mul,
    map_ofNat]
  linear_combination (PowerSeries.map inlP (PowerSeries.C a2) *
      PowerSeries.map inlP (cS sv)) ^ 2 * eps_sq +
    2 * PowerSeries.C DualNumber.eps * PowerSeries.map inlP (PowerSeries.C a2) *
      PowerSeries.map inlP (cst ηS) * hcb

theorem map_chi_ySer :
    PowerSeries.map chi.toRingHom ySer =
      PowerSeries.C DualNumber.eps * PowerSeries.map inlP (PowerSeries.C a2) +
        PowerSeries.map inlP (cst ηS * zS) := by
  rw [ySer, map_mul, map_chi_colSer_zero, map_chi_colSer_one]
  have hcb := congrArg (PowerSeries.map inlP) (cS_mul_bS sv)
  rw [map_mul, map_one] at hcb
  simp only [mapInl_mul, uHat, vHat]
  linear_combination PowerSeries.C DualNumber.eps * PowerSeries.map inlP (PowerSeries.C a2) * hcb

theorem map_chi_zSer : PowerSeries.map chi.toRingHom zSer = PowerSeries.map inlP zS := by
  rw [zSer, map_mul, map_chi_colSer_one, ← map_mul]

/-! ### The filtration `W r` -/

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

theorem coeff_cst_mul_zS (g : PowerSeries Cq) (m : ℕ) :
    PowerSeries.coeff m (cst g * zS) =
      Polynomial.C (PowerSeries.coeff m g) +
        (if m = 0 then 0 else sv * Polynomial.C (PowerSeries.coeff (m - 1) g)) := by
  rw [zS, bS_mul_bS, mul_add, mul_one, map_add, ← mul_assoc, mul_comm (cst g), mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  rcases m with _ | m
  · simp
  · rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_map]; simp

theorem natDegree_coeff_cst_mul_zS (g : PowerSeries Cq) (m : ℕ) :
    (PowerSeries.coeff m (cst g * zS)).natDegree ≤ 1 := by
  rw [coeff_cst_mul_zS]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · split_ifs
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)

theorem degree_coeff_cst_mul_zS (g : PowerSeries Cq) (m : ℕ) :
    (PowerSeries.coeff m (cst g * zS)).degree ≤ 1 :=
  (Polynomial.degree_le_natDegree).trans (by exact_mod_cast natDegree_coeff_cst_mul_zS g m)

theorem letter_form_mem (c : Cq) (g : PowerSeries Cq) (m : ℕ) :
    DualNumber.eps * TrivSqZeroExt.inl (Polynomial.C c) +
      TrivSqZeroExt.inl (PowerSeries.coeff m (cst g * zS)) ∈ W 1 := by
  refine mem_W.mpr ⟨?_, ?_⟩
  · simpa using degree_coeff_cst_mul_zS g m
  · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul, DualNumber.fst_eps,
      DualNumber.snd_eps, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl, smul_zero, zero_add,
      op_smul_eq_mul, one_mul, add_zero]
    exact (Polynomial.degree_mul_le _ _).trans
      ((add_le_add Polynomial.degree_X_le Polynomial.degree_C_le).trans (by simp))

theorem coeff_epsForm (F G : PowerSeries Pl) (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.C DualNumber.eps * PowerSeries.map inlP F +
      PowerSeries.map inlP G) =
      DualNumber.eps * TrivSqZeroExt.inl (PowerSeries.coeff m F) +
        TrivSqZeroExt.inl (PowerSeries.coeff m G) := by
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, PowerSeries.coeff_map]
  rfl

theorem chi_coeff (P : PowerSeries JetPoly) (m : ℕ) :
    chi (PowerSeries.coeff m P) = PowerSeries.coeff m (PowerSeries.map chi.toRingHom P) := by
  rw [PowerSeries.coeff_map]; rfl

theorem chi_letter_mem_W (a : Fin 3) (m : ℕ) : chi (letterSym (.current a, m)) ∈ W 1 := by
  match a with
  | 0 =>
    change chi (PowerSeries.coeff m xSer) ∈ W 1
    rw [chi_coeff, map_chi_xSer, coeff_epsForm, PowerSeries.coeff_C_mul, PowerSeries.coeff_map,
      ← map_mul]
    rw [show (2 * a2 * Polynomial.C (PowerSeries.coeff m ηS) : Pl) =
      Polynomial.C (2 * al ^ 2 * PowerSeries.coeff m ηS) by simp only [a2, map_mul, map_ofNat]]
    exact letter_form_mem _ _ m
  | 1 =>
    change chi (PowerSeries.coeff m (-zSer)) ∈ W 1
    rw [map_neg, map_neg, chi_coeff, map_chi_zSer, PowerSeries.coeff_map]
    refine (W 1).neg_mem ?_
    have h := letter_form_mem 0 1 m
    rwa [map_zero, TrivSqZeroExt.inl_zero, mul_zero, zero_add, map_one, one_mul] at h
  | 2 =>
    change chi (PowerSeries.coeff m (-(ySer + ySer))) ∈ W 1
    rw [map_neg, map_add, map_neg, map_add, chi_coeff, map_chi_ySer, coeff_epsForm,
      PowerSeries.coeff_C]
    have h : ∀ c : Cq, DualNumber.eps * TrivSqZeroExt.inl (Polynomial.C c) +
        TrivSqZeroExt.inl (PowerSeries.coeff m (cst ηS * zS)) ∈ W 1 := fun c =>
      letter_form_mem c ηS m
    refine (W 1).neg_mem ((W 1).add_mem ?_ ?_) <;>
    · split_ifs
      · exact h _
      · simpa using h 0

/-! ### The Sugawara images -/

/-- The `s`-linear part `A_m` of `chi(T_m) / α²`. -/
def Aco (m : ℕ) : Pl :=
  PowerSeries.coeff m (cst qS.derivativeFun * zS) + PowerSeries.coeff (m + 1) (cst (ξS * ξS) * zS)

/-- The `ε`-part `B_m` of `chi(T_m) / α²`. -/
def Bco (m : ℕ) : Pl :=
  PowerSeries.coeff m (wS sv) + 2 * Polynomial.C (al * PowerSeries.coeff (m + 1) ξS)

theorem ηS_derivativeFun : ηS.derivativeFun = PowerSeries.C (al ^ 2) * qS.derivativeFun := by
  rw [ηS, ξS, derivativeFun_C_mul', PowerSeries.derivativeFun_add, PowerSeries.derivativeFun_C,
    zero_add, derivativeFun_C_mul', ← mul_assoc, ← map_mul, sq]

theorem chi_tSug (m : ℕ) :
    chi (PowerSeries.coeff m testSer) =
      TrivSqZeroExt.inl a2 *
        (TrivSqZeroExt.inl (Aco m) + DualNumber.eps * TrivSqZeroExt.inl (Bco m)) := by
  rw [testSer, PowerSeries.coeff_mk, map_add, chi_coeff, chi_coeff, map_chi_jSer, map_chi_xSer,
    coeff_epsForm, coeff_epsForm]
  have h1 : (cst ηS).derivativeFun = PowerSeries.C a2 * cst qS.derivativeFun := by
    rw [← map_derivativeFun'', ηS_derivativeFun, map_mul, PowerSeries.map_C]
  have h2 : cst ηS * cst ηS = PowerSeries.C a2 * cst (ξS * ξS) := by
    rw [ηS, map_mul, map_mul, PowerSeries.map_C, a2]
    simp only [map_pow]
    ring
  rw [h1, h2, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, ηS,
    PowerSeries.coeff_C_mul, Aco, Bco]
  simp only [TrivSqZeroExt.inl_mul, TrivSqZeroExt.inl_add, map_mul]
  ring

/-- `T̂ = A + ε B`. -/
def tHat : PowerSeries DP :=
  PowerSeries.mk fun m => TrivSqZeroExt.inl (Aco m) + DualNumber.eps * TrivSqZeroExt.inl (Bco m)

theorem map_chi_testSer :
    PowerSeries.map chi.toRingHom testSer = PowerSeries.C (TrivSqZeroExt.inl a2) * tHat := by
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_C_mul, tHat, PowerSeries.coeff_mk, ← chi_coeff, chi_tSug]

/-- The ideal `(α^{2n})`. -/
abbrev Jn (n : ℕ) : Ideal DP := Ideal.span {(TrivSqZeroExt.inl a2 : DP) ^ n}

theorem chi_testIdeal (n : ℕ) : (testIdeal n).map chi.toRingHom ≤ Jn n := by
  rw [Ideal.map_le_iff_le_comap, testIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap]
  change chi (PowerSeries.coeff j (testSer ^ n)) ∈ Jn n
  rw [chi_coeff, map_pow, map_chi_testSer, mul_pow, ← map_pow, PowerSeries.coeff_C_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-! ### The data of the leading-coefficient lemma -/

theorem natDegree_Aco (m : ℕ) : (Aco m).natDegree ≤ 1 :=
  (Polynomial.natDegree_add_le _ _).trans
    (max_le (natDegree_coeff_cst_mul_zS _ _) (natDegree_coeff_cst_mul_zS _ _))

theorem Bco_eq (m : ℕ) :
    Bco m = Polynomial.C ((-1) ^ (m + 1)) * Polynomial.X ^ (m + 1) +
      Polynomial.C (2 * (al * PowerSeries.coeff (m + 1) ξS)) := by
  rw [Bco, coeff_wS, neg_pow]
  simp only [map_mul, map_pow, map_neg, map_one, map_ofNat]

theorem natDegree_Bco (m : ℕ) : (Bco m).natDegree ≤ m + 1 := by
  rw [Bco_eq]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact Polynomial.natDegree_C_mul_X_pow_le _ _
  · rw [Polynomial.natDegree_C]; exact Nat.zero_le _

theorem coeff_Bco (m : ℕ) : (Bco m).coeff (m + 1) = (-1) ^ (m + 1) := by
  rw [Bco_eq, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, if_pos rfl,
    Polynomial.coeff_C, if_neg (Nat.succ_ne_zero m), add_zero]

/-- `α ↦ 0`, `r₀ ↦ T₀`, `q_m ↦ T_m`. -/
def piA : Cq →ₐ[ℂ] MvPolynomial ℕ ℂ := aeval fun o => o.elim 0 X

theorem piA_al : piA al = 0 := by simp [piA, al]

theorem coeff_one_coeff_cst_mul_zS (g : PowerSeries Cq) (m : ℕ) :
    (PowerSeries.coeff m (cst g * zS)).coeff 1 =
      if m = 0 then 0 else PowerSeries.coeff (m - 1) g := by
  rw [coeff_cst_mul_zS, Polynomial.coeff_add, Polynomial.coeff_C, if_neg one_ne_zero, zero_add]
  split_ifs with h
  · simp
  · rw [show (1 : ℕ) = 0 + 1 from rfl, Polynomial.coeff_X_mul, Polynomial.coeff_C_zero]

theorem inv_smul_mul_natCast {σ : Type} (Y : MvPolynomial σ ℂ) (c : ℕ) (hc : c ≠ 0) :
    ((c : ℂ)⁻¹ • Y) * (c : MvPolynomial σ ℂ) = Y := by
  rw [smul_mul_assoc, ← map_natCast (algebraMap ℂ (MvPolynomial σ ℂ)) c, mul_comm,
    ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hc), one_smul]

theorem coeff_qS_derivativeFun (m : ℕ) :
    PowerSeries.coeff m qS.derivativeFun = X (some (m + 1)) := by
  rw [PowerSeries.coeff_derivativeFun, qS, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero m),
    show ((m : Cq) + 1) = ((m + 1 : ℕ) : Cq) by push_cast; ring,
    show ((m + 1 : ℕ) : ℂ) = (((m + 1 : ℕ) : ℕ) : ℂ) from rfl]
  exact inv_smul_mul_natCast _ (m + 1) (Nat.succ_ne_zero m)

theorem piA_sb (m : ℕ) :
    piA ((Aco m).coeff 1) = if m = 0 then (X 0 : MvPolynomial ℕ ℂ) ^ 2 else X m := by
  rw [Aco, Polynomial.coeff_add, coeff_one_coeff_cst_mul_zS, coeff_one_coeff_cst_mul_zS,
    if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel, map_add]
  have hξ : PowerSeries.map piA.toRingHom ξS = PowerSeries.C (X 0) := by
    rw [ξS, map_add, map_mul, PowerSeries.map_C, PowerSeries.map_C]
    change PowerSeries.C (piA (X (some 0))) + PowerSeries.C (piA al) * _ = _
    rw [piA_al, map_zero, zero_mul, add_zero]
    simp [piA]
  have h2 : piA (PowerSeries.coeff m (ξS * ξS)) =
      if m = 0 then (X 0 : MvPolynomial ℕ ℂ) ^ 2 else 0 := by
    change piA.toRingHom _ = _
    rw [← PowerSeries.coeff_map, map_mul, hξ, ← map_mul, PowerSeries.coeff_C, sq]
  rw [h2]
  rcases m with _ | m
  · simp
  · rw [if_neg (Nat.succ_ne_zero m), if_neg (Nat.succ_ne_zero m), if_neg (Nat.succ_ne_zero m),
      add_zero, Nat.add_sub_cancel, coeff_qS_derivativeFun]
    simp [piA]

/-! ### Bookkeeping in `ℂ[T_j]` -/

/-- `tMonW` in `R_n` is the image of `tMonW` in `ℂ[T_j]`. -/
theorem tMonW_Rn_eq (n k : ℕ) (e : ℤ) :
    tMonW (Rn n) (tn n) k e =
      (tMonW TPoly X k e).map (Ideal.Quotient.mkₐ ℂ (jetIdealT n)).toLinearMap := by
  rw [tMonW, tMonW, Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨l, hl, he, rfl⟩
    refine ⟨(l.map X).prod, ⟨l, hl, he, rfl⟩, ?_⟩
    rw [AlgHom.toLinearMap_apply, map_list_prod, List.map_map]
    rfl
  · rintro ⟨_, ⟨l, hl, he, rfl⟩, rfl⟩
    refine ⟨l, hl, he, ?_⟩
    rw [AlgHom.toLinearMap_apply, map_list_prod, List.map_map]
    rfl

theorem boxW_map (n N k : ℕ) (e : ℤ) :
    (boxW (X : ℕ → TPoly) N k e).map (Ideal.Quotient.mkₐ ℂ (jetIdealT n)).toLinearMap ≤
      boxW (tn n) N k e := by
  rw [boxW, Submodule.map_span_le]
  rintro _ ⟨l, hl, he, hN, rfl⟩
  refine Submodule.subset_span ⟨l, hl, he, hN, ?_⟩
  rw [AlgHom.toLinearMap_apply, map_list_prod, List.map_map]
  rfl

/-- Kill the jets `T_m` with `m ∉ S`. -/
def cut (S : ℕ → Prop) [DecidablePred S] : TPoly →ₐ[ℂ] TPoly :=
  aeval fun m => if S m then X m else 0

theorem cut_listProd (S : ℕ → Prop) [DecidablePred S] (l : List ℕ) :
    cut S (l.map X).prod = if ∀ x ∈ l, S x then (l.map X).prod else 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih, cut, aeval_X]
    by_cases hx : S x
    · simp only [hx, if_true, List.forall_mem_cons, true_and]
      split_ifs <;> simp
    · simp [hx]

theorem cut_eq_self {S : ℕ → Prop} [DecidablePred S] {F : TPoly} (h : ∀ m ∈ F.vars, S m) :
    cut S F = F := by
  conv_rhs => rw [← aeval_X_left_apply F]
  change eval₂Hom (algebraMap ℂ TPoly) _ F = eval₂Hom (algebraMap ℂ TPoly) _ F
  refine eval₂Hom_congr' rfl (fun i hi _ => ?_) rfl
  rw [if_pos (h i hi)]

theorem cut_tMonW_le_V (M k : ℕ) (e : ℤ) :
    (tMonW TPoly X k e).map (cut (· ≤ M)).toLinearMap ≤ InclLead.V M k := by
  rw [tMonW, Submodule.map_span_le]
  rintro _ ⟨l, hl, -, rfl⟩
  rw [AlgHom.toLinearMap_apply, cut_listProd]
  split_ifs with h
  · exact Submodule.subset_span ⟨l, hl, h, rfl⟩
  · exact Submodule.zero_mem _

theorem cut_tMonW_le_boxW (N k : ℕ) (e : ℤ) :
    (tMonW TPoly X k e).map (cut (· < N)).toLinearMap ≤ boxW X N k e := by
  rw [tMonW, Submodule.map_span_le]
  rintro _ ⟨l, hl, he, rfl⟩
  rw [AlgHom.toLinearMap_apply, cut_listProd]
  split_ifs with h
  · exact Submodule.subset_span ⟨l, hl, he, h, rfl⟩
  · exact Submodule.zero_mem _

/-- Homogeneity: scaling every `T_m` by `c` scales a degree-`k` polynomial by `c^k`. -/
theorem aeval_mul_tMonW {B : Type} [CommRing B] [Algebra ℂ B] (c : B) (h : ℕ → B) {k : ℕ}
    {e : ℤ} {F : TPoly} (hF : F ∈ tMonW TPoly X k e) :
    aeval (fun m => c * h m) F = c ^ k * aeval h F := by
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, rfl, -, rfl⟩ := hP
    induction l with
    | nil => simp
    | cons x l ih => simp [ih, pow_succ]; ring
  | zero => simp
  | add P Q _ _ hP hQ => rw [map_add, map_add, hP, hQ, mul_add]
  | smul a P _ hP => rw [map_smul, map_smul, hP, mul_smul_comm]

/-! ### The letters at the level of `JetPoly` -/

/-- The span of the jets of `u², uv, v²` in `JetPoly`. -/
def Lpoly : Submodule ℂ JetPoly :=
  Submodule.span ℂ (Set.range fun p : Fin 3 × ℕ => letterSym (.current p.1, p.2))

theorem testLetters_eq (n : ℕ) :
    testLetters n = Lpoly.map (Ideal.Quotient.mkₐ ℂ (testIdeal n)).toLinearMap := by
  rw [testLetters, Lpoly, Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span ℂ) (congrArg Set.range (funext fun p => ?_))
  rw [Function.comp_apply, testHom_mletter_current]
  rfl

theorem chi_Lpoly_pow : ∀ r : ℕ, Lpoly ^ r ≤ (W r).comap chi.toLinearMap
  | 0 => by
    intro x hx
    rw [pow_zero, Submodule.mem_one] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, AlgHom.commutes]
    refine mem_W.mpr ⟨?_, ?_⟩
    · rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_inl, Polynomial.algebraMap_apply]
      exact Polynomial.degree_C_le.trans (by simp)
    · rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, mul_zero]
      simp
  | r + 1 => by
    rw [pow_succ, Submodule.mul_le]
    intro x hx y hy
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, map_mul]
    refine mul_mem_W (chi_Lpoly_pow r hx) ?_
    have : Lpoly ≤ (W 1).comap chi.toLinearMap := by
      rw [Lpoly, Submodule.span_le]
      rintro _ ⟨⟨a, m⟩, rfl⟩
      exact chi_letter_mem_W a m
    exact this hy

theorem chi_v0 : chi (X (1, 0)) = 1 := by
  simp [chi, chiV, coeff_zero_bS]

/-! ### The `ε`-part bound -/

theorem coeff_eq_zero_of_mem_W {r : ℕ} {x : DP} (hx : x ∈ W r) {D : ℕ} (hD : r ≤ D) :
    (TrivSqZeroExt.snd x).coeff D = 0 := by
  have h2 := (mem_W.mp hx).2
  rw [← Polynomial.coeff_X_mul]
  exact Polynomial.coeff_eq_zero_of_degree_lt
    (lt_of_le_of_lt h2 (by exact_mod_cast Nat.lt_succ_of_le hD))

theorem coeff_snd_mem_Jn {n : ℕ} {x : DP} (hx : x ∈ Jn n) (D : ℕ) :
    ∃ z : Cq, (TrivSqZeroExt.snd x).coeff D = z * al ^ (2 * n) := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  refine ⟨(TrivSqZeroExt.snd y).coeff D, ?_⟩
  rw [TrivSqZeroExt.inl_pow, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl, smul_zero, zero_add,
    TrivSqZeroExt.fst_inl, op_smul_eq_mul, a2, ← map_pow, Polynomial.coeff_mul_C, ← pow_mul]

/-- **The test, read through `chi`**: for `F` of `T`-degree `k < n` passing the `(r, N)` test, the
`ε s^D` coefficients of `F(A + ε B)` (`D ≥ r`) vanish at `α = 0`. -/
theorem piA_coeff_eq_zero {n r N k : ℕ} (hk : k < n) {e : ℤ} {F : TPoly}
    (hF : F ∈ tMonW TPoly X k e)
    (hT : ψn n (Ideal.Quotient.mk (jetIdealT n) F) * tmk n (X (1, 0)) ^ (2 * N) ∈
      testLetters n ^ r) {D : ℕ} (hD : r ≤ D) :
    piA ((TrivSqZeroExt.snd (InclLead.theta Aco Bco F)).coeff D) = 0 := by
  have hψ : ψn n (Ideal.Quotient.mk (jetIdealT n) F) =
      tmk n (aeval (fun m => PowerSeries.coeff m testSer) F) := by
    change (testT n) F = Ideal.Quotient.mkₐ ℂ (testIdeal n) _
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  rw [hψ, ← map_pow, ← map_mul, testLetters_eq, ← Submodule.map_pow] at hT
  obtain ⟨y, hy, hyP⟩ := hT
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hyP
  have hJ := chi_testIdeal n (Ideal.mem_map_of_mem chi.toRingHom hyP)
  have hW : chi y ∈ W r := chi_Lpoly_pow r hy
  have hg : (fun m => chi (PowerSeries.coeff m testSer)) = fun m =>
      TrivSqZeroExt.inl a2 * (TrivSqZeroExt.inl (Aco m) +
        DualNumber.eps * TrivSqZeroExt.inl (Bco m)) := funext chi_tSug
  have hchiP : chi (aeval (fun m => PowerSeries.coeff m testSer) F) =
      TrivSqZeroExt.inl a2 ^ k * InclLead.theta Aco Bco F := by
    rw [MvPolynomial.comp_aeval_apply, hg, aeval_mul_tMonW _ _ hF]
    rfl
  change chi (y - _ * X (1, 0) ^ (2 * N)) ∈ Jn n at hJ
  rw [map_sub, map_mul, map_pow, chi_v0, one_pow, mul_one, hchiP] at hJ
  obtain ⟨z, hz⟩ := coeff_snd_mem_Jn hJ D
  rw [TrivSqZeroExt.snd_sub, Polynomial.coeff_sub, coeff_eq_zero_of_mem_W hW hD, zero_sub,
    TrivSqZeroExt.inl_pow, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl, smul_zero, add_zero,
    TrivSqZeroExt.fst_inl, smul_eq_mul, a2, ← map_pow, Polynomial.coeff_C_mul, ← pow_mul] at hz
  set Y := (TrivSqZeroExt.snd (InclLead.theta Aco Bco F)).coeff D
  have hal : (al ^ (2 * k) : Cq) ≠ 0 := pow_ne_zero _ (X_ne_zero _)
  have hY : Y = -(z * al ^ (2 * (n - k))) := by
    apply mul_left_cancel₀ hal
    rw [show 2 * n = 2 * k + 2 * (n - k) by omega, pow_add] at hz
    linear_combination -hz
  rw [hY, map_neg, map_mul, map_pow, piA_al, zero_pow (by omega), mul_zero, neg_zero]

/-! ### The low slots -/

/-- **Every slot of `BoxInclusion n r` with `T`-degree `r - N < n`.** -/
theorem boxInclusion_low {n r : ℕ} (d : ℤ) (N : ℕ) (hNr : N < r) (hk : r - N < n) :
    tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N ≤ boxW (tn n) N (r - N) (d - r) := by
  rintro τ ⟨hτ, hT⟩
  rw [tMonW_Rn_eq] at hτ
  obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.mp hτ
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] at hT ⊢
  rw [SetLike.mem_coe, mem_testSp] at hT
  have hvars : ∀ m ∈ F.vars, m < N := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m0, hm0, hm0N⟩ := hcon
    have hne : F.vars.Nonempty := ⟨m0, hm0⟩
    have hMmem : F.vars.max' hne ∈ F.vars := Finset.max'_mem _ _
    have hMle : ∀ m ∈ F.vars, m ≤ F.vars.max' hne := fun m hm => Finset.le_max' _ _ hm
    have hNM : N ≤ F.vars.max' hne := le_trans hm0N (hMle m0 hm0)
    have hFV : F ∈ InclLead.V (F.vars.max' hne) (r - N) := by
      have := cut_tMonW_le_V (F.vars.max' hne) (r - N) (d - r) (Submodule.mem_map.mpr ⟨F, hF, rfl⟩)
      rwa [AlgHom.toLinearMap_apply, cut_eq_self (fun m hm => hMle m hm)] at this
    obtain ⟨-, hlead⟩ :=
      InclLead.lead_span Aco Bco natDegree_Aco natDegree_Bco coeff_Bco hFV
    have h0 := piA_coeff_eq_zero hk hF hT (D := r - N + F.vars.max' hne) (by omega)
    rw [hlead, map_mul, map_pow, map_neg, map_one] at h0
    have hsq : piA (aeval (InclLead.sb Aco) (pderiv (F.vars.max' hne) F)) =
        InclLead.sqMap (pderiv (F.vars.max' hne) F) := by
      rw [MvPolynomial.comp_aeval_apply, InclLead.sqMap]
      exact congrArg (fun g : ℕ → MvPolynomial ℕ ℂ => aeval g (pderiv (F.vars.max' hne) F))
        (funext piA_sb)
    rw [hsq] at h0
    have hpd : InclLead.sqMap (pderiv (F.vars.max' hne) F) = 0 :=
      (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    exact InclLead.not_mem_vars_of_pderiv_eq_zero
      (InclLead.aeval_sq_injective (hpd.trans (map_zero _).symm)) hMmem
  have hbox : F ∈ boxW X N (r - N) (d - r) := by
    have := cut_tMonW_le_boxW N (r - N) (d - r) (Submodule.mem_map.mpr ⟨F, hF, rfl⟩)
    rwa [AlgHom.toLinearMap_apply, cut_eq_self hvars] at this
  exact boxW_map n N (r - N) (d - r) (Submodule.mem_map.mpr ⟨F, hbox, rfl⟩)

end InclLow

open InclLow

/-- **The remaining slots of `BoxInclusion n r`**: `T`-degree `r - N ≥ n`. -/
def BoxInclusionTail (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), N < r → n ≤ r - N →
    tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N ≤ boxW (tn n) N (r - N) (d - r)

/-- **`BoxInclusion` from its slots of `T`-degree at least `n`.** -/
theorem boxInclusion_of_tail {n r : ℕ} (h : BoxInclusionTail n r) : BoxInclusion n r :=
  fun d N hN => if hk : r - N < n then boxInclusion_low d N hN hk else h d N hN (by omega)

/-- `BoxInclusionTail n r` is vacuous for `r < n`. -/
theorem boxInclusionTail_of_lt {n r : ℕ} (hr : r < n) : BoxInclusionTail n r :=
  fun _ _ _ h => absurd h (by omega)

/-- **`BoxInclusion n r` for every `r < n`.** -/
theorem boxInclusion_of_lt {n r : ℕ} (hr : r < n) : BoxInclusion n r :=
  boxInclusion_of_tail (boxInclusionTail_of_lt hr)

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional only on `hA`,
detection `det` and the slots of `BoxInclusion` of `T`-degree at least `n`. -/
theorem twoSeries_gradedUnitary_of_strictModel_inclTail (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (incl : ∀ r, BoxInclusionTail n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_incl n hn hA det fun r => boxInclusion_of_tail (incl r)

end

end VOA.TwoSeries.StrictModel
