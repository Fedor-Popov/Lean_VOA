/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesInclLow

/-!
# Positive Witt operators preserve the test

For `k ≥ 1` let `Δ_k` be the derivation of `ℂ[u_j, v_j]` given on the series `u(t), v(t)` by

  `Δ_k u = t^k (t u' - (k/2) u)`,    `Δ_k v = t^k (t v' - (k/2) v - u)`,

that is, `t^{k+1} ∂_t` acting on fields of conformal weight `-k / (2(k+1))`, corrected by the
lowering element `f ⊗ t^k` of `sl₂[t]`.  The weight is chosen exactly so that the stray `x₀`-term
coming from the shift `x̃(t) = (x(t) - x₀)/t` cancels:

* `wittD_testSer` — `Δ_k (J + x̃) = t^k ((J + x̃) + t (J + x̃)')`, i.e.
  `Δ_k(T_m) = (m - k + 1) T_{m-k}` for the test images `T_m = J_m + x_{m+1}`;
* `wittD_testIdeal` — `Δ_k` preserves the ideal of jets of `(J + x̃)ⁿ`;
* `wittD_Lpoly` — `Δ_k` maps jets of `u², uv, v²` to such jets, hence (`wittD_Lpoly_pow`)
  preserves the span of products of `r` of them;
* `wittD_v0` — `Δ_k v₀ = 0`.

On `ℂ[T_j]` the matching derivation is `dT k : T_m ↦ (m - k + 1) T_{m-k}`; it preserves the jets of
`Tⁿ` (`dT_jetIdealT`), so it descends to `dR n k : R_n → R_n`.  Consequences:

* `dR_testSp` — **the test space is stable under every `dR n k`, `k ≥ 1`**;
* `dR_tMonW` — `dR n k` lowers the weight by `k` and keeps the `T`-degree;
* `dR_boxW` — the box is stable too, so `R_n / box` is a module over the positive Witt operators;
* `boxInclusionTail_of_singular` — **the tail of `BoxInclusion` follows from its Witt-singular
  part** `BoxSingularTail n r`: a `T`-polynomial passing the test whose images under every
  `dR n j` (`j ≥ 1`) lie in the box lies in the box (induction on the weight);
  `boxSingularTail_of_inclTail` is the converse, so the two inputs are equivalent;
* `twoSeries_gradedUnitary_of_strictModel_singular` — the endpoint with that input.

Numerical evidence (exact linear algebra mod `p = 1000003`, script not in the repository, not a proof): the
Witt-singular vectors of `R_n / box` in `T`-degree `k ≥ n` are rare and sit at low weight.  For
`n = 2`, `k ∈ {2, 3}`, `N ≤ 4`, weight `≤ 13` the singular quotient has dimension `1` in 14 slots
and `0` elsewhere; for `n = 3`, `k ∈ {3, 4}`, `N ≤ 3`, weight `≤ 12` it has dimension `≤ 2` in 13 slots.
So `BoxSingularTail` concerns a handful of lowest-weight vectors per `(n, k, N)`, against the full
weight range of `BoxInclusionTail`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.InvariantSymbol VOA.SocleEval
open VOA.AdamovicSymbol Module
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

namespace TailWitt

/-! ### Coefficientwise derivations of power series -/

section Gen

variable {B : Type} [CommRing B] [Algebra ℂ B]

/-- A derivation applied coefficientwise. -/
def serG (D : Derivation ℂ B B) (f : PowerSeries B) : PowerSeries B :=
  PowerSeries.mk fun n => D (PowerSeries.coeff n f)

@[simp] theorem coeff_serG (D : Derivation ℂ B B) (f : PowerSeries B) (n : ℕ) :
    PowerSeries.coeff n (serG D f) = D (PowerSeries.coeff n f) := PowerSeries.coeff_mk _ _

theorem serG_add (D : Derivation ℂ B B) (f g : PowerSeries B) :
    serG D (f + g) = serG D f + serG D g := by
  ext n; simp

theorem serG_sub (D : Derivation ℂ B B) (f g : PowerSeries B) :
    serG D (f - g) = serG D f - serG D g := by
  ext n; simp

theorem serG_mul (D : Derivation ℂ B B) (f g : PowerSeries B) :
    serG D (f * g) = serG D f * g + f * serG D g := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_serG, PowerSeries.coeff_mul, map_add, map_sum, Derivation.leibniz, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem serG_derivative (D : Derivation ℂ B B) (f : PowerSeries B) :
    serG D (PowerSeries.derivative B f) = PowerSeries.derivative B (serG D f) := by
  ext n
  simp only [coeff_serG, PowerSeries.coeff_derivative, Derivation.leibniz, smul_eq_mul]
  have h : D ((n : B) + 1) = 0 := by
    rw [show ((n : B) + 1) = ((n + 1 : ℕ) : B) by push_cast; ring]
    exact D.map_natCast _
  rw [h, mul_zero, zero_add, mul_comm]

theorem serG_X_mul (D : Derivation ℂ B B) (f : PowerSeries B) :
    serG D (PowerSeries.X * f) = PowerSeries.X * serG D f := by
  ext n
  rcases n with _ | n
  · simp
  · simp [PowerSeries.coeff_succ_X_mul]

theorem serG_X_pow_mul (D : Derivation ℂ B B) (m : ℕ) (f : PowerSeries B) :
    serG D (PowerSeries.X ^ m * f) = PowerSeries.X ^ m * serG D f := by
  ext n
  simp only [coeff_serG, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

theorem serG_C (D : Derivation ℂ B B) (a : B) :
    serG D (PowerSeries.C a) = PowerSeries.C (D a) := by
  ext n
  rcases n with _ | n <;> simp [PowerSeries.coeff_C]

/-- The Witt shape `t^k (c f + t f')`. -/
def wshape (k : ℕ) (c : B) (f : PowerSeries B) : PowerSeries B :=
  PowerSeries.X ^ k * (PowerSeries.C c * f + PowerSeries.X * PowerSeries.derivative B f)

omit [Algebra ℂ B] in
theorem coeff_wshape (k : ℕ) (c : B) (f : PowerSeries B) (m : ℕ) :
    PowerSeries.coeff m (wshape k c f) =
      if k ≤ m then (c + ((m - k : ℕ) : B)) * PowerSeries.coeff (m - k) f else 0 := by
  rw [wshape, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [map_add, PowerSeries.coeff_C_mul, add_mul]
    congr 1
    rcases Nat.eq_zero_or_pos (m - k) with h0 | h0
    · rw [h0]; simp
    · obtain ⟨p, hp⟩ : ∃ p, m - k = p + 1 := ⟨m - k - 1, by omega⟩
      rw [hp, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      push_cast
      ring
  · rfl

/-- **Powers of a Witt-shaped series**: if `D f = t^k (f + t f')` coefficientwise, then
`D (fⁿ) = t^k (n fⁿ + t (fⁿ)')`. -/
theorem serG_pow_wshape (D : Derivation ℂ B B) (k : ℕ) {f : PowerSeries B}
    (hf : serG D f = wshape k 1 f) :
    ∀ n : ℕ, serG D (f ^ n) = wshape k (n : B) (f ^ n)
  | 0 => by
    ext m
    simp only [pow_zero, coeff_serG, wshape, Nat.cast_zero, map_zero, zero_mul, zero_add,
      Derivation.map_one_eq_zero, mul_zero, map_zero]
    rw [PowerSeries.coeff_one]
    split_ifs <;> simp
  | n + 1 => by
    rw [pow_succ, serG_mul, serG_pow_wshape D k hf n, hf, wshape, wshape, wshape,
      Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    push_cast
    rw [map_add, map_one]
    ring

/-- **A derivation that is Witt-shaped on `f` preserves the ideal of jets of `fⁿ`.** -/
theorem serG_mem_span_pow (D : Derivation ℂ B B) (k : ℕ) {f : PowerSeries B}
    (hf : serG D f = wshape k 1 f) (n : ℕ) :
    ∀ x ∈ Ideal.span (Set.range fun j => PowerSeries.coeff j (f ^ n)),
      D x ∈ Ideal.span (Set.range fun j => PowerSeries.coeff j (f ^ n)) := by
  have hgen : ∀ j, D (PowerSeries.coeff j (f ^ n)) ∈
      Ideal.span (Set.range fun j => PowerSeries.coeff j (f ^ n)) := by
    intro j
    have h := congrArg (PowerSeries.coeff j) (serG_pow_wshape D k hf n)
    rw [coeff_serG, coeff_wshape] at h
    rw [h]
    split_ifs
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j - k, rfl⟩)
    · exact Submodule.zero_mem _
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact hgen j
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b hb ihb =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ ihb) (Ideal.mul_mem_right _ _ hb)

/-- A derivation along an algebra map, checked on the variables. -/
theorem deriv_aeval_comm {σ : Type} (D : Derivation ℂ B B)
    (D' : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (g : σ → B)
    (h : ∀ i, D (g i) = aeval g (D' (X i))) (F : MvPolynomial σ ℂ) :
    D (aeval g F) = aeval g (D' F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, aeval_X, hp, h]

/-- A derivation maps `S ^ r` into itself when it maps `S` into itself. -/
theorem deriv_pow_le (D : Derivation ℂ B B) (S : Submodule ℂ B)
    (hS : ∀ x ∈ S, D x ∈ S) : ∀ r : ℕ, ∀ x ∈ S ^ r, D x ∈ S ^ r
  | 0 => by
    intro x hx
    rw [pow_zero, Submodule.mem_one] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [Derivation.map_algebraMap]
    exact Submodule.zero_mem _
  | r + 1 => by
    intro x hx
    rw [pow_succ] at hx ⊢
    have hle : S ^ r * S ≤ (S ^ r * S).comap D.toLinearMap := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      rw [Submodule.mem_comap, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul,
        smul_eq_mul]
      refine add_mem (Submodule.mul_mem_mul ha (hS b hb)) ?_
      rw [mul_comm b]
      exact Submodule.mul_mem_mul (deriv_pow_le D S hS r a ha) hb
    exact hle hx

end Gen

/-! ### The Witt derivation of `ℂ[u_j, v_j]` -/

/-- The values of `Δ_k` on the jet variables:
`u_m ↦ (m - 3k/2) u_{m-k}`, `v_m ↦ (m - 3k/2) v_{m-k} - u_{m-k}`. -/
def wittVal (k : ℕ) (p : Fin 2 × ℕ) : JetPoly :=
  if k ≤ p.2 then
    (((p.2 - k : ℕ) : ℂ) - (k : ℂ) / 2) • X (p.1, p.2 - k) -
      (if p.1 = 1 then X (0, p.2 - k) else 0)
  else 0

/-- The Witt derivation `Δ_k`. -/
def wittD (k : ℕ) : Derivation ℂ JetPoly JetPoly := MvPolynomial.mkDerivation ℂ (wittVal k)

theorem wittD_X (k : ℕ) (p : Fin 2 × ℕ) : wittD k (X p) = wittVal k p :=
  MvPolynomial.mkDerivation_X _ _ _

/-- `Δ_k v₀ = 0` for `k ≥ 1`. -/
theorem wittD_v0 {k : ℕ} (hk : 1 ≤ k) : wittD k (X (1, 0)) = 0 := by
  rw [wittD_X, wittVal, if_neg (by simp; omega)]

/-- The scalar `-k/2` as a jet polynomial. -/
abbrev hc (k : ℕ) : JetPoly := MvPolynomial.C (-((k : ℂ) / 2))

theorem coeff_hc_mul (k m : ℕ) (b : Fin 2) :
    (((m - k : ℕ) : ℂ) - (k : ℂ) / 2) • (X (b, m - k) : JetPoly) =
      (hc k + ((m - k : ℕ) : JetPoly)) * X (b, m - k) := by
  rw [smul_eq_C_mul, hc, ← map_natCast (MvPolynomial.C (σ := Fin 2 × ℕ) (R := ℂ)), ← map_add]
  congr 2
  ring

theorem serG_u (k : ℕ) : serG (wittD k) (colSer 0) = wshape k (hc k) (colSer 0) := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_serG, coeff_wshape]
  simp only [colSer, PowerSeries.coeff_mk, wittD_X, wittVal]
  split_ifs with h h'
  · exact absurd h' (by decide)
  · rw [sub_zero, coeff_hc_mul]
  · rfl

theorem serG_v (k : ℕ) : serG (wittD k) (colSer 1) =
    wshape k (hc k) (colSer 1) - PowerSeries.X ^ k * colSer 0 := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_serG, map_sub, coeff_wshape, PowerSeries.coeff_X_pow_mul']
  simp only [colSer, PowerSeries.coeff_mk, wittD_X, wittVal]
  split_ifs with h
  · rw [coeff_hc_mul]
  · simp

/-- `S = t J + x - x₀ = t (J + x̃)`. -/
def sSer : JetSer := sX * jSer + xSer - PowerSeries.C (PowerSeries.coeff 0 xSer)

theorem X_mul_testSer : sX * testSer = sSer := by
  ext m
  rcases m with _ | m
  · simp [sSer]
  · rw [sSer, map_sub, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
      testSer, PowerSeries.coeff_mk, PowerSeries.coeff_C]
    simp

theorem wittD_x0 {k : ℕ} (hk : 1 ≤ k) : wittD k (PowerSeries.coeff 0 xSer) = 0 := by
  rw [xSer, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  simp only [colSer, PowerSeries.coeff_mk, Derivation.leibniz, wittD_X, wittVal]
  rw [if_neg (by simp; omega)]
  simp

/-- **The Witt identity** `Δ_k S = t^{k+1} S'`. -/
theorem serG_sSer {k : ℕ} (hk : 1 ≤ k) :
    serG (wittD k) sSer = sX ^ (k + 1) * dS sSer := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hx0 := wittD_x0 hk
  rw [sSer, serG_sub, serG_add, serG_X_mul, serG_C, hx0, map_zero, sub_zero, jSer, serG_sub,
    serG_mul, serG_mul, serG_derivative, serG_derivative, xSer, serG_mul, serG_u, serG_v]
  simp only [wshape, map_sub, map_add, Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_C, PowerSeries.derivative_X, dS_X_pow, nsmul_eq_mul, mul_zero,
    add_zero, sub_zero]
  have hc2 : ((j + 1 : ℕ) : JetSer) + 2 * PowerSeries.C (hc (j + 1)) = 0 := by
    have e : ((j + 1 : ℕ) : JetSer) + 2 * PowerSeries.C (hc (j + 1)) =
        PowerSeries.C (MvPolynomial.C (((j + 1 : ℕ) : ℂ) + 2 * -(((j + 1 : ℕ) : ℂ) / 2))) := by
      rw [map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, map_ofNat, map_ofNat]
    rw [e, show (((j + 1 : ℕ) : ℂ) + 2 * -(((j + 1 : ℕ) : ℂ) / 2)) = 0 by ring, map_zero,
      map_zero]
  simp only [Nat.add_sub_cancel] at *
  linear_combination (sX ^ (j + 1) * colSer 0 ^ 2 +
    sX ^ (j + 2) * (dS (colSer 0) * colSer 1 - colSer 0 * dS (colSer 1))) * hc2

/-- **`Δ_k (J + x̃) = t^k ((J + x̃) + t (J + x̃)')`.** -/
theorem wittD_testSer {k : ℕ} (hk : 1 ≤ k) :
    serG (wittD k) testSer = wshape k 1 testSer := by
  refine mul_left_cancel₀ (PowerSeries.X_ne_zero (R := JetPoly)) ?_
  change sX * _ = sX * _
  rw [← serG_X_mul, X_mul_testSer, serG_sSer hk, ← X_mul_testSer, wshape, map_one, one_mul,
    Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul, smul_eq_mul, mul_one]
  ring

/-- **`Δ_k` preserves the jets of `(J + x̃)ⁿ`.** -/
theorem wittD_testIdeal {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ∀ x ∈ testIdeal n, wittD k x ∈ testIdeal n :=
  serG_mem_span_pow (wittD k) k (wittD_testSer hk) n

/-! ### Letters go to letters -/

open InclLow

/-- All coefficients lie in the span of the letters. -/
def InL (f : JetSer) : Prop := ∀ m, PowerSeries.coeff m f ∈ Lpoly

theorem inL_add {f g : JetSer} (hf : InL f) (hg : InL g) : InL (f + g) := fun m => by
  rw [map_add]; exact add_mem (hf m) (hg m)

theorem inL_sub {f g : JetSer} (hf : InL f) (hg : InL g) : InL (f - g) := fun m => by
  rw [map_sub]; exact sub_mem (hf m) (hg m)

theorem inL_neg {f : JetSer} (hf : InL f) : InL (-f) := fun m => by
  rw [map_neg]; exact neg_mem (hf m)

theorem inL_C_mul {f : JetSer} (c : ℂ) (hf : InL f) :
    InL (PowerSeries.C (MvPolynomial.C c) * f) := fun m => by
  rw [PowerSeries.coeff_C_mul, ← smul_eq_C_mul]; exact Submodule.smul_mem _ c (hf m)

theorem inL_X_pow_mul {f : JetSer} (k : ℕ) (hf : InL f) : InL (sX ^ k * f) := fun m => by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs
  · exact hf _
  · exact Submodule.zero_mem _

theorem inL_X_mul_dS {f : JetSer} (hf : InL f) : InL (sX * dS f) := fun m => by
  rcases m with _ | p
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      show ((p : JetPoly) + 1) = ((p + 1 : ℕ) : JetPoly) by push_cast; ring, mul_comm,
      ← nsmul_eq_mul]
    exact nsmul_mem (hf _) _

theorem inL_x : InL xSer := fun m => Submodule.subset_span ⟨(0, m), rfl⟩

theorem inL_z : InL zSer := fun m => by
  have h : PowerSeries.coeff m (-zSer) ∈ Lpoly := Submodule.subset_span ⟨(1, m), rfl⟩
  rw [map_neg] at h
  simpa using neg_mem h

theorem inL_y : InL ySer := fun m => by
  have h : PowerSeries.coeff m (-(ySer + ySer)) ∈ Lpoly := Submodule.subset_span ⟨(2, m), rfl⟩
  have h2 := Submodule.smul_mem Lpoly (-(1 / 2 : ℂ)) h
  rw [map_neg, map_add, smul_neg, ← two_smul ℂ, smul_smul] at h2
  rw [show -(1 / 2 : ℂ) * 2 = -1 by norm_num, neg_one_smul, neg_neg] at h2
  exact h2

theorem serG_xSer (k : ℕ) : serG (wittD k) xSer = sX ^ k *
    (PowerSeries.C (hc k) * xSer + PowerSeries.C (hc k) * xSer + sX * dS xSer) := by
  rw [xSer, serG_mul, serG_u, wshape, Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem serG_ySer (k : ℕ) : serG (wittD k) ySer = sX ^ k *
    (PowerSeries.C (hc k) * ySer + PowerSeries.C (hc k) * ySer + sX * dS ySer - xSer) := by
  rw [ySer, serG_mul, serG_u, serG_v, wshape, wshape, Derivation.leibniz, smul_eq_mul,
    smul_eq_mul, xSer]
  ring

theorem serG_zSer (k : ℕ) : serG (wittD k) zSer = sX ^ k *
    (PowerSeries.C (hc k) * zSer + PowerSeries.C (hc k) * zSer + sX * dS zSer - ySer - ySer) := by
  rw [zSer, serG_mul, serG_v, wshape, Derivation.leibniz, ySer]
  simp only [smul_eq_mul]
  ring

theorem inL_serG_x (k : ℕ) : InL (serG (wittD k) xSer) := by
  rw [serG_xSer]
  exact inL_X_pow_mul _ (inL_add (inL_add (inL_C_mul _ inL_x) (inL_C_mul _ inL_x))
    (inL_X_mul_dS inL_x))

theorem inL_serG_y (k : ℕ) : InL (serG (wittD k) ySer) := by
  rw [serG_ySer]
  exact inL_X_pow_mul _ (inL_sub (inL_add (inL_add (inL_C_mul _ inL_y) (inL_C_mul _ inL_y))
    (inL_X_mul_dS inL_y)) inL_x)

theorem inL_serG_z (k : ℕ) : InL (serG (wittD k) zSer) := by
  rw [serG_zSer]
  exact inL_X_pow_mul _ (inL_sub (inL_sub (inL_add (inL_add (inL_C_mul _ inL_z)
    (inL_C_mul _ inL_z)) (inL_X_mul_dS inL_z)) inL_y) inL_y)

/-- **`Δ_k` maps the letters into their span.** -/
theorem wittD_Lpoly (k : ℕ) : ∀ x ∈ Lpoly, wittD k x ∈ Lpoly := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨a, m⟩, rfl⟩ := hy
    change wittD k (PowerSeries.coeff m (curSer a)) ∈ Lpoly
    rw [← coeff_serG]
    fin_cases a
    · exact inL_serG_x k m
    · change PowerSeries.coeff m (serG (wittD k) (-zSer)) ∈ Lpoly
      rw [show (-zSer) = 0 - zSer by ring, serG_sub,
        show serG (wittD k) 0 = 0 by ext; simp, zero_sub]
      exact inL_neg (inL_serG_z k) m
    · change PowerSeries.coeff m (serG (wittD k) (-(ySer + ySer))) ∈ Lpoly
      rw [show -(ySer + ySer) = 0 - (ySer + ySer) by ring, serG_sub, serG_add,
        show serG (wittD k) 0 = 0 by ext; simp, zero_sub]
      exact inL_neg (inL_add (inL_serG_y k) (inL_serG_y k)) m
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Derivation.map_smul]; exact Submodule.smul_mem _ c ha

/-- **`Δ_k` preserves the span of products of `r` letters.** -/
theorem wittD_Lpoly_pow (k r : ℕ) : ∀ x ∈ Lpoly ^ r, wittD k x ∈ Lpoly ^ r :=
  deriv_pow_le (wittD k) Lpoly (wittD_Lpoly k) r

/-! ### The matching derivation of `ℂ[T_j]` and of `R_n` -/

/-- `T_m ↦ (m - k + 1) T_{m-k}`. -/
def dT (k : ℕ) : Derivation ℂ TPoly TPoly :=
  MvPolynomial.mkDerivation ℂ fun m => if k ≤ m then (((m - k : ℕ) : ℂ) + 1) • X (m - k) else 0

theorem dT_X (k m : ℕ) :
    dT k (X m) = if k ≤ m then (((m - k : ℕ) : ℂ) + 1) • X (m - k) else 0 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem serG_dT_tSer (k : ℕ) : serG (dT k) tSer = wshape k 1 tSer := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_serG, coeff_wshape, tSer, PowerSeries.coeff_mk, dT_X, PowerSeries.coeff_mk]
  split_ifs
  · rw [smul_eq_C_mul]
    congr 1
    simp [add_comm]
  · rfl

/-- **`dT k` preserves the jets of `Tⁿ`.** -/
theorem dT_jetIdealT (k n : ℕ) : ∀ x ∈ jetIdealT n, dT k x ∈ jetIdealT n :=
  serG_mem_span_pow (dT k) k (serG_dT_tSer k) n

/-- The images `T_m ↦ J_m + x_{m+1}`. -/
abbrev tco (m : ℕ) : JetPoly := PowerSeries.coeff m testSer

/-- **Intertwining**: `Δ_k (τ(J + x̃)) = (dT k τ)(J + x̃)`. -/
theorem wittD_aeval {k : ℕ} (hk : 1 ≤ k) (F : TPoly) :
    wittD k (aeval tco F) = aeval tco (dT k F) := by
  refine deriv_aeval_comm (wittD k) (dT k) tco (fun m => ?_) F
  rw [tco, ← coeff_serG, wittD_testSer hk, coeff_wshape, dT_X]
  split_ifs
  · rw [map_smul, aeval_X, smul_eq_C_mul]
    congr 1
    simp [add_comm]
  · simp

/-- `dT k` on `R_n`. -/
def dR (n k : ℕ) : Rn n →ₗ[ℂ] Rn n :=
  (((jetIdealT n).restrictScalars ℂ).liftQ
      ((Ideal.Quotient.mkₐ ℂ (jetIdealT n)).toLinearMap ∘ₗ (dT k).toLinearMap)
      (fun x hx => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
          Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact dT_jetIdealT k n x hx)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℂ (jetIdealT n)).symm.toLinearMap

theorem dR_mk (n k : ℕ) (F : TPoly) :
    dR n k (Ideal.Quotient.mk (jetIdealT n) F) = Ideal.Quotient.mk (jetIdealT n) (dT k F) :=
  rfl

/-! ### The test space and the weight spaces are stable -/

theorem ψn_mk (n : ℕ) (F : TPoly) :
    ψn n (Ideal.Quotient.mk (jetIdealT n) F) = tmk n (aeval tco F) := by
  change (testT n) F = Ideal.Quotient.mkₐ ℂ (testIdeal n) _
  rw [MvPolynomial.comp_aeval_apply]
  rfl

/-- **The test space is stable under the positive Witt operators.** -/
theorem dR_testSp {n r N k : ℕ} (hk : 1 ≤ k) {τ : Rn n} (hτ : τ ∈ testSp n r N) :
    dR n k τ ∈ testSp n r N := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective τ
  rw [dR_mk]
  rw [mem_testSp, ψn_mk, ← map_pow, ← map_mul, testLetters_eq, ← Submodule.map_pow] at hτ ⊢
  obtain ⟨y, hy, hyP⟩ := hτ
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hyP
  refine ⟨wittD k y, wittD_Lpoly_pow k r y hy, ?_⟩
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
  have h := wittD_testIdeal hk n _ hyP
  have hv : wittD k (X (1, 0) ^ (2 * N)) = 0 := by
    rw [Derivation.leibniz_pow, wittD_v0 hk, smul_zero, smul_zero]
  rwa [map_sub, Derivation.leibniz, hv, smul_zero, zero_add, smul_eq_mul, wittD_aeval hk,
    mul_comm (X (1, 0) ^ (2 * N))] at h

/-- The weight of a list of jet indices. -/
abbrev wt (l : List ℕ) : ℤ := (((l.map fun m => m + 1).sum : ℕ) : ℤ)

theorem dT_listProd (j : ℕ) :
    ∀ l : List ℕ, dT j (l.map X).prod ∈ tMonW TPoly X l.length (wt l - j)
  | [] => by
    rw [List.map_nil, List.prod_nil, Derivation.map_one_eq_zero]
    exact Submodule.zero_mem _
  | x :: l => by
    rw [List.map_cons, List.prod_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      List.length_cons]
    have hw : wt (x :: l) = wt l + x + 1 := by
      simp only [wt, List.map_cons, List.sum_cons]; push_cast; ring
    refine add_mem ?_ ?_
    · have := mul_mem_tMonW (R := TPoly) X (dT_listProd j l) x
      rw [hw]
      convert this using 2
      ring
    · rw [dT_X]
      split_ifs with hjx
      · rw [mul_smul_comm, mul_comm]
        refine Submodule.smul_mem _ _ ?_
        have hP : (l.map X).prod ∈ tMonW TPoly X l.length (wt l) :=
          Submodule.subset_span ⟨l, rfl, rfl, rfl⟩
        have := mul_mem_tMonW (R := TPoly) X hP (x - j)
        rw [hw]
        convert this using 2
        push_cast [hjx]
        ring
      · rw [mul_zero]; exact Submodule.zero_mem _

/-- `dT j` lowers the weight by `j`. -/
theorem dT_tMonW (j k : ℕ) (e : ℤ) {F : TPoly} (hF : F ∈ tMonW TPoly X k e) :
    dT j F ∈ tMonW TPoly X k (e - j) := by
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, rfl, he, rfl⟩ := hP
    rw [← he]
    exact dT_listProd j l
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Derivation.map_smul]; exact Submodule.smul_mem _ c ha

/-- **`dR n j` lowers the weight by `j` and keeps the `T`-degree.** -/
theorem dR_tMonW (n j k : ℕ) (e : ℤ) {τ : Rn n} (hτ : τ ∈ tMonW (Rn n) (tn n) k e) :
    dR n j τ ∈ tMonW (Rn n) (tn n) k (e - j) := by
  rw [tMonW_Rn_eq] at hτ ⊢
  obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.mp hτ
  refine Submodule.mem_map.mpr ⟨dT j F, dT_tMonW j k e hF, ?_⟩
  rfl

/-- Negative weights are empty. -/
theorem tMonW_neg {R : Type} [CommRing R] [Algebra ℂ R] (t : ℕ → R) (k : ℕ) {e : ℤ}
    (he : e < 0) : tMonW R t k e = ⊥ := by
  rw [tMonW, Submodule.span_eq_bot]
  rintro _ ⟨l, -, hl, -⟩
  exact absurd hl (by have : (0 : ℤ) ≤ _ := Int.natCast_nonneg ((l.map fun m => m + 1).sum); omega)

theorem mul_mem_boxW {R : Type} [CommRing R] [Algebra ℂ R] (t : ℕ → R) {N k : ℕ} {e : ℤ} {c : R}
    (hc : c ∈ boxW t N k e) {m : ℕ} (hm : m < N) : t m * c ∈ boxW t N (k + 1) (e + m + 1) := by
  have h : boxW t N k e ≤ (boxW t N (k + 1) (e + m + 1)).comap (LinearMap.mulLeft ℂ (t m)) := by
    rw [boxW, Submodule.span_le]
    rintro _ ⟨l, hl, he, hN, rfl⟩
    refine Submodule.subset_span ⟨m :: l, by simp [hl], ?_, ?_, by simp⟩
    · rw [List.map_cons, List.sum_cons, Nat.cast_add, he]; push_cast; ring
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hm
      · exact hN x hx
  exact h hc

theorem dT_listProd_box (j N : ℕ) :
    ∀ l : List ℕ, (∀ m ∈ l, m < N) → dT j (l.map X).prod ∈ boxW X N l.length (wt l - j)
  | [], _ => by
    rw [List.map_nil, List.prod_nil, Derivation.map_one_eq_zero]
    exact Submodule.zero_mem _
  | x :: l, hl => by
    have hxN : x < N := hl x (by simp)
    have hlN : ∀ m ∈ l, m < N := fun m hm => hl m (by simp [hm])
    rw [List.map_cons, List.prod_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      List.length_cons]
    have hw : wt (x :: l) = wt l + x + 1 := by
      simp only [wt, List.map_cons, List.sum_cons]; push_cast; ring
    refine add_mem ?_ ?_
    · have := mul_mem_boxW (R := TPoly) X (dT_listProd_box j N l hlN) hxN
      rw [hw]
      convert this using 2
      ring
    · rw [dT_X]
      split_ifs with hjx
      · rw [mul_smul_comm, mul_comm]
        refine Submodule.smul_mem _ _ ?_
        have hP : ((l.map X).prod : TPoly) ∈ boxW (X : ℕ → TPoly) N l.length (wt l) :=
          Submodule.subset_span ⟨l, rfl, rfl, hlN, rfl⟩
        have := mul_mem_boxW (R := TPoly) X hP (m := x - j) (by omega)
        rw [hw]
        convert this using 2
        push_cast [hjx]
        ring
      · rw [mul_zero]; exact Submodule.zero_mem _

/-- **The box is stable under `dR n j`** (weight lowered by `j`), so `R_n / box` is a module over
the positive Witt operators. -/
theorem dR_boxW (n j N k : ℕ) (e : ℤ) {τ : Rn n} (hτ : τ ∈ boxW (tn n) N k e) :
    dR n j τ ∈ boxW (tn n) N k (e - j) := by
  induction hτ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, rfl, he, hN, rfl⟩ := hP
    have h1 : (l.map (tn n)).prod = Ideal.Quotient.mk (jetIdealT n) (l.map X).prod := by
      rw [map_list_prod, List.map_map]; rfl
    rw [h1, dR_mk, ← he]
    exact boxW_map n N l.length (wt l - j)
      (Submodule.mem_map.mpr ⟨_, dT_listProd_box j N l hN, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end TailWitt

open TailWitt

/-! ### The reduction to Witt-singular vectors -/

/-- **The Witt-singular part of the tail of `BoxInclusion`**: for `N < r` and `T`-degree
`r - N ≥ n`, a `T`-polynomial of weight `d - r` passing the test, whose images under every positive
Witt operator `dR n j` (`j ≥ 1`) lie in the box (of weight `d - r - j`), lies in the box. -/
def BoxSingularTail (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), N < r → n ≤ r - N → ∀ τ : Rn n,
    τ ∈ tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N →
    (∀ j : ℕ, 1 ≤ j → dR n j τ ∈ boxW (tn n) N (r - N) (d - r - j)) →
    τ ∈ boxW (tn n) N (r - N) (d - r)

/-- **The tail of `BoxInclusion` from its Witt-singular part** (induction on the weight). -/
theorem boxInclusionTail_of_singular {n r : ℕ} (h : BoxSingularTail n r) :
    BoxInclusionTail n r := by
  intro d N hN hk
  suffices H : ∀ M : ℕ, ∀ d : ℤ, (d - r).toNat ≤ M → ∀ τ : Rn n,
      τ ∈ tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N →
      τ ∈ boxW (tn n) N (r - N) (d - r) from
    fun τ hτ => H _ d le_rfl τ hτ
  intro M
  induction M with
  | zero =>
    intro d hd τ hτ
    refine h d N hN hk τ hτ fun j hj => ?_
    have hτj := dR_tMonW n j (r - N) (d - r) hτ.1
    rw [tMonW_neg _ _ (by omega), Submodule.mem_bot] at hτj
    rw [hτj]
    exact Submodule.zero_mem _
  | succ M ih =>
    intro d hd τ hτ
    refine h d N hN hk τ hτ fun j hj => ?_
    have hτj := dR_tMonW n j (r - N) (d - r) hτ.1
    by_cases hneg : d - r - j < 0
    · rw [tMonW_neg _ _ hneg, Submodule.mem_bot] at hτj
      rw [hτj]
      exact Submodule.zero_mem _
    · have := ih (d - j) (by omega) (dR n j τ)
        ⟨by rwa [show d - j - r = d - r - j by ring], dR_testSp hj hτ.2⟩
      rwa [show d - j - r = d - r - j by ring] at this

/-- The converse: `BoxSingularTail` is a special case of `BoxInclusionTail`, so the reduction is an
equivalence. -/
theorem boxSingularTail_of_inclTail {n r : ℕ} (h : BoxInclusionTail n r) : BoxSingularTail n r :=
  fun d N hN hk _ hτ _ => h d N hN hk hτ

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional only on `hA`,
detection `det` and the Witt-singular part of the tail of `BoxInclusion`. -/
theorem twoSeries_gradedUnitary_of_strictModel_singular (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (sing : ∀ r, BoxSingularTail n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_inclTail n hn hA det fun r =>
    boxInclusionTail_of_singular (sing r)

end

end VOA.TwoSeries.StrictModel
