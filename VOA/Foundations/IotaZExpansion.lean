/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.DeltaJump

/-!
# The general-`n` `ι_z` expansion algebra (the lattice-locality toolkit)

Extends `Foundations.Expansion` / `Foundations.DeltaJump` with the reusable
`ι_z` expansion algebra needed for vertex-operator (lattice) locality and the two-sided
form of skew-symmetry.

* **(1) Multiplicativity** (the core, proved in full):
  `ι₁₂((z₁-z₂)^m)·ι₁₂((z₁-z₂)^n) = ι₁₂((z₁-z₂)^{m+n})`  (`expandPos_mul`) and the
  `z₁`-dominant analogue `expandNeg_mul`.  Each `expandPos n` / `expandNeg n` lives on the
  *single antidiagonal* `a+b=n`, so the formal-series product (convolution
  `convolPos`/`convolNeg`) is finite per coefficient and lands on `a+b=m+n`.  The algebraic
  engine is the generalized-binomial Vandermonde `cbz_vandermonde` (`C(m,i)C(n,k-i)`
  convolution `= C(m+n,k)`).
* **(2) General-order δ-jump consequences.**  `mulBySubPow (k+1) (negPowJump k) = 0`
  (`mulBySubPow_negPowJump_self`) and the sharper `mulBySubPow_negPowJump_eq_zero`
  (`k+1 ≤ N ⟹ (z₁-z₂)^N · Jₖ = 0`): a high enough power of `(z₁-z₂)` annihilates the
  `ι₁₂-ι₂₁` jump of `(z₁-z₂)^{-k-1}` — the general `(z₁-z₂)^{⟨α,β⟩}` lattice factor.
  Plus the regular-part **reproducing identity** `(z₁-z₂)^N · ι₁₂((z₁-z₂)^{-N}) = 1`
  (`mulBySubPow_expandPos_neg`).
* **(3) Integer-shift binomial bookkeeping** for the exp-of-oscillator vertex operator:
  `gBinom`/`cbz` Pascal multiplicativity re-exported as `cbz_mul_vandermonde`, the unit
  `expandPos 0 = expandNeg 0 = 1` (`expandPos_zero`/`expandNeg_zero`), the unit laws
  `convolPos_zero_left`/`convolPos_zero_right`, and the explicit antidiagonal extraction
  (`expandPos_diag_cbz`/`expandNeg_diag_cbz`) the lattice VO needs.

## Status
All declarations `sorry`-free / axiom-free
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`).  See the final block.
-/

namespace VOA

open scoped BigOperators

/-! ## §0  Antidiagonal support of the two expansions -/

/-- `expandPos n` is supported on the single antidiagonal `a + b = n` (with `b ≥ 0`):
off that line every coefficient vanishes. -/
theorem expandPos_eq_zero_off_diag (n a b : ℤ) (h : a + b ≠ n) : expandPos n a b = 0 := by
  rw [expandPos_apply, if_neg]; rintro ⟨_, rfl⟩; omega

/-- `expandNeg n` is supported on the single antidiagonal `a + b = n` (with `a ≥ 0`). -/
theorem expandNeg_eq_zero_off_diag (n a b : ℤ) (h : a + b ≠ n) : expandNeg n a b = 0 := by
  rw [expandNeg_apply, if_neg]; rintro ⟨_, rfl⟩; omega

/-- `expandPos n` is also zero whenever the `z₂`-power `b` is negative. -/
theorem expandPos_eq_zero_of_neg (n a : ℤ) {b : ℤ} (hb : b < 0) : expandPos n a b = 0 := by
  rw [expandPos_apply, if_neg]; rintro ⟨h, _⟩; omega

/-- `expandNeg n` is zero whenever the `z₁`-power `a` is negative. -/
theorem expandNeg_eq_zero_of_neg (n b : ℤ) {a : ℤ} (ha : a < 0) : expandNeg n a b = 0 := by
  rw [expandNeg_apply, if_neg]; rintro ⟨h, _⟩; omega

/-- The value of `expandPos n` on its antidiagonal, parametrized by the `z₂`-power `b ≥ 0`. -/
theorem expandPos_diag (n b : ℤ) (hb : 0 ≤ b) :
    expandPos n (n - b) b = negOnePow b * gBinom n b.toNat := by
  rw [expandPos_apply, if_pos ⟨hb, rfl⟩]

/-- The value of `expandNeg n` on its antidiagonal, parametrized by the `z₁`-power `a ≥ 0`. -/
theorem expandNeg_diag (n a : ℤ) (ha : 0 ≤ a) :
    expandNeg n a (n - a) = negOnePow (n + a) * gBinom n a.toNat := by
  rw [expandNeg_apply, if_pos ⟨ha, rfl⟩]

/-- The predecessor sign relation `(-1)^{t-1} = -(-1)^t`. -/
theorem negOnePow_pred (t : ℤ) : negOnePow (t - 1) = - negOnePow t := by
  have := negOnePow_succ (t - 1); rw [show t - 1 + 1 = t from by ring] at this
  rw [this, neg_neg]

/-- The sign is multiplicative: `(-1)^{x+y} = (-1)^x·(-1)^y`.
(FIX: in this Lean/Mathlib `Int.induction_on` names the cases `zero`/`succ`/`pred`.) -/
theorem negOnePow_add (x y : ℤ) : negOnePow (x + y) = negOnePow x * negOnePow y := by
  induction y using Int.induction_on with
  | zero => rw [add_zero, show negOnePow 0 = 1 from by simp [negOnePow], mul_one]
  | succ k ih => rw [show x + ((k : ℤ) + 1) = (x + (k : ℤ)) + 1 from by ring, negOnePow_succ, ih,
      negOnePow_succ]; ring
  | pred k ih => rw [show x + (-(k : ℤ) - 1) = (x + (-(k : ℤ))) - 1 from by ring,
      negOnePow_pred, ih, negOnePow_pred]; ring

/-! ## §1  The generalized-binomial Vandermonde identity

The algebraic engine of multiplicativity.  The integer-indexed binomial `cbz`
(`C(·,k)=0` for `k<0`) satisfies `∑_{i} C(m,i) C(n,k-i) = C(m+n,k)`. -/

/-- Upper-index Pascal for `cbz`: `C(n+1,k) = C(n,k) + C(n,k-1)`. -/
theorem cbz_pascal_up (n k : ℤ) : cbz (n + 1) k = cbz n k + cbz n (k - 1) := by
  have h := cbz_pascal (n + 1) k
  rwa [show (n + 1 - 1 : ℤ) = n by ring] at h

/-- `cbz n k = 0` for `k < 0`. -/
theorem cbz_neg' (n : ℤ) {k : ℤ} (hk : k < 0) : cbz n k = 0 := cbz_apply_neg n hk

/-- `cbz 0 k = [k = 0]`: the zeroth row is the unit mass. -/
theorem cbz_zero_left (k : ℤ) : cbz 0 k = if k = 0 then 1 else 0 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [cbz_neg' 0 hk, if_neg (by omega)]
  · subst hk; simp
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    rw [cbz_apply_nonneg 0 (by omega), if_neg (by omega), gBinom,
      Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr (by omega))]
    · simp
    · push_cast; ring

/-- For fixed `m n k`, the convolution family `i ↦ C(m,i)·C(n,k-i)` has finite support
(`cbz m i = 0` for `i<0`, `cbz n (k-i) = 0` for `i>k`), so its `finsum` is well-defined. -/
theorem cbz_convol_support_finite (m n k : ℤ) :
    (Function.support (fun i : ℤ => cbz m i * cbz n (k - i))).Finite := by
  apply Set.Finite.subset (Set.finite_Icc 0 k)
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_neg' m h, zero_mul]
  · rw [cbz_neg' n (by omega), mul_zero]

/-- The convolution sum `V(m,n,k) = ∑ᶠ i, C(m,i)·C(n,k-i)` (the `ι_z`-product coefficient). -/
noncomputable def cbzConvol (m n k : ℤ) : ℂ := ∑ᶠ i : ℤ, cbz m i * cbz n (k - i)

theorem cbzConvol_neg (m n : ℤ) {k : ℤ} (hk : k < 0) : cbzConvol m n k = 0 := by
  rw [cbzConvol, finsum_eq_zero_of_forall_eq_zero]
  intro i
  rcases lt_or_ge i 0 with h | h
  · rw [cbz_neg' m h, zero_mul]
  · rw [cbz_neg' n (by omega), mul_zero]

/-- The Pascal recursion for the convolution in the first upper index:
`V(m+1,n,k) = V(m,n,k) + V(m,n,k-1)` (engine of the Vandermonde induction). -/
theorem cbzConvol_pascal (m n k : ℤ) :
    cbzConvol (m + 1) n k = cbzConvol m n k + cbzConvol m n (k - 1) := by
  have hfin1 : (Function.support (fun i : ℤ => cbz m i * cbz n (k - i))).Finite :=
    cbz_convol_support_finite _ _ _
  have hfin2 : (Function.support (fun i : ℤ => cbz m (i - 1) * cbz n (k - i))).Finite := by
    apply Set.Finite.subset (Set.finite_Icc 1 k)
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_neg' m (by omega), zero_mul]
    · rw [cbz_neg' n (by omega), mul_zero]
  rw [cbzConvol, cbzConvol, cbzConvol]
  rw [show (∑ᶠ i : ℤ, cbz (m + 1) i * cbz n (k - i))
        = ∑ᶠ i : ℤ, (cbz m i * cbz n (k - i) + cbz m (i - 1) * cbz n (k - i)) from
      finsum_congr fun i => by rw [cbz_pascal_up, add_mul]]
  rw [finsum_add_distrib hfin1 hfin2]
  congr 1
  rw [← finsum_int_succ_shift (fun i : ℤ => cbz m (i - 1) * cbz n (k - i))]
  refine finsum_congr fun i => ?_
  dsimp only
  rw [show i + 1 - 1 = i from by ring, show k - (i + 1) = k - 1 - i from by ring]

/-- `V(0,n,k) = C(n,k)`: the zeroth row collapses to the second factor. -/
theorem cbzConvol_zero_left (n k : ℤ) : cbzConvol 0 n k = cbz n k := by
  rw [cbzConvol]
  rw [show (∑ᶠ i : ℤ, cbz 0 i * cbz n (k - i))
        = ∑ᶠ i : ℤ, (if i = 0 then (1 : ℂ) else 0) * cbz n (k - i) from
      finsum_congr fun i => by rw [cbz_zero_left]]
  rw [finsum_eq_single _ 0 (fun i hi => by rw [if_neg hi, zero_mul])]
  simp

/-- **Generalized-binomial Vandermonde** (Gannon 5.1.4; the `ι_z` multiplicativity engine):
`∑ᶠ i, C(m,i)·C(n,k-i) = C(m+n,k)` for all integers `m,n,k`.  Integer induction on `m`
(Pascal `cbzConvol_pascal` / `cbz_pascal_up`); the downward step uses an inner downward
`k`-induction `D(k) = -D(k-1)`, `D = 0` for `k<0`, to pin the unknown. -/
theorem cbz_vandermonde (m n k : ℤ) : cbzConvol m n k = cbz (m + n) k := by
  induction m using Int.induction_on generalizing k with
  | zero => rw [zero_add, cbzConvol_zero_left]
  | succ j ih => rw [cbzConvol_pascal, ih k, ih (k - 1),
      show (j : ℤ) + 1 + n = ((j : ℤ) + n) + 1 from by ring, cbz_pascal_up]
  | pred j ih =>
      -- Want: `cbzConvol (-j-1) n k = cbz (-j-1+n) k`.  Define `D k` = LHS − RHS; show `D = 0`.
      set M : ℤ := -(j : ℤ) - 1 with hM
      have hMp : M + 1 = -(j : ℤ) := by rw [hM]; ring
      have hrec : ∀ k : ℤ, cbzConvol M n k + cbzConvol M n (k - 1)
          = cbz (M + n) k + cbz (M + n) (k - 1) := by
        intro k
        have hp := cbzConvol_pascal M n k
        rw [hMp] at hp
        rw [← hp, ih k, show (-(j : ℤ)) + n = (M + n) + 1 from by rw [hM]; ring, cbz_pascal_up]
      have hD : ∀ k : ℤ, cbzConvol M n (k + 1) - cbz (M + n) (k + 1)
          = -(cbzConvol M n k - cbz (M + n) k) := fun k => by
        have h := hrec (k + 1)
        rw [show (k + 1 - 1 : ℤ) = k from by ring] at h
        rw [eq_neg_iff_add_eq_zero,
          show (cbzConvol M n (k + 1) - cbz (M + n) (k + 1))
                + (cbzConvol M n k - cbz (M + n) k)
              = (cbzConvol M n (k + 1) + cbzConvol M n k)
                - (cbz (M + n) (k + 1) + cbz (M + n) k) from by ring,
          h, sub_self]
      have hDneg : ∀ k : ℤ, k < 0 → cbzConvol M n k - cbz (M + n) k = 0 := fun k hk => by
        rw [cbzConvol_neg M n hk, cbz_neg' (M + n) hk, sub_zero]
      have hDnonneg : ∀ k : ℤ, 0 ≤ k → cbzConvol M n k - cbz (M + n) k = 0 := by
        intro k hk
        induction k, hk using Int.leInduction with
        | base =>
            have h := hD (-1)
            rw [show (-1 + 1 : ℤ) = 0 from by ring, hDneg (-1) (by norm_num), neg_zero] at h
            exact h
        | succ p _ ihp => rw [hD p, ihp, neg_zero]
      have hDall : cbzConvol M n k - cbz (M + n) k = 0 := by
        rcases le_or_gt 0 k with hk | hk
        · exact hDnonneg k hk
        · exact hDneg k hk
      exact sub_eq_zero.mp hDall

/-- The Vandermonde convolution, packaged as the bare summation identity the lattice
exp-of-oscillator bookkeeping (§3) consumes: `∑ᶠ i, C(m,i)·C(n,k-i) = C(m+n,k)`. -/
theorem cbz_mul_vandermonde (m n k : ℤ) :
    (∑ᶠ i : ℤ, cbz m i * cbz n (k - i)) = cbz (m + n) k := cbz_vandermonde m n k

/-! ## §2  Multiplicativity `ι₁₂((z₁-z₂)^m)·ι₁₂((z₁-z₂)^n) = ι₁₂((z₁-z₂)^{m+n})`

Each `expandPos n` lives on the single antidiagonal `a+b=n` (`expandPos_eq_zero_off_diag`),
so the formal-series product collapses to a single `z₂`-split finsum.  The identity
`convolPos m n = expandPos (m+n)` is exactly the Vandermonde §1. -/

/-- The bridge `expandPos n (n-b₁) b₁ = (-1)^{b₁} · C(n,b₁)` for all integers `b₁`
(using `cbz`, which is `0` for `b₁<0`). -/
theorem expandPos_diag_cbz (n b₁ : ℤ) :
    expandPos n (n - b₁) b₁ = negOnePow b₁ * cbz n b₁ := by
  rcases le_or_gt 0 b₁ with hb | hb
  · rw [expandPos_diag n b₁ hb, cbz_apply_nonneg n hb]
  · rw [expandPos_eq_zero_of_neg n (n - b₁) hb, cbz_neg' n hb, mul_zero]

/-- The bridge `expandNeg n a₁ (n-a₁) = (-1)^{n+a₁} · C(n,a₁)` for all integers `a₁`. -/
theorem expandNeg_diag_cbz (n a₁ : ℤ) :
    expandNeg n a₁ (n - a₁) = negOnePow (n + a₁) * cbz n a₁ := by
  rcases le_or_gt 0 a₁ with ha | ha
  · rw [expandNeg_diag n a₁ ha, cbz_apply_nonneg n ha]
  · rw [expandNeg_eq_zero_of_neg n (n - a₁) ha, cbz_neg' n ha, mul_zero]

/-- The `z₂`-dominant `ι₁₂` product `convolPos m n`: coefficient of `z₁ᵃz₂ᵇ` in the formal
product `ι₁₂((z₁-z₂)^m)·ι₁₂((z₁-z₂)^n)`, collapsed (via the single-antidiagonal support of
the first factor) to a single `z₂`-split `finsum`. -/
noncomputable def convolPos (m n : ℤ) : FormalDist₂ ℂ :=
  fun a b => ∑ᶠ b₁ : ℤ, expandPos m (m - b₁) b₁ * expandPos n (a - (m - b₁)) (b - b₁)

@[simp] theorem convolPos_apply (m n a b : ℤ) :
    convolPos m n a b = ∑ᶠ b₁ : ℤ, expandPos m (m - b₁) b₁ * expandPos n (a - (m - b₁)) (b - b₁) :=
  rfl

/-- The `z₁`-dominant `ι₂₁` product `convolNeg m n`: the `z₁`-split companion of `convolPos`. -/
noncomputable def convolNeg (m n : ℤ) : FormalDist₂ ℂ :=
  fun a b => ∑ᶠ a₁ : ℤ, expandNeg m a₁ (m - a₁) * expandNeg n (a - a₁) (b - (m - a₁))

@[simp] theorem convolNeg_apply (m n a b : ℤ) :
    convolNeg m n a b = ∑ᶠ a₁ : ℤ, expandNeg m a₁ (m - a₁) * expandNeg n (a - a₁) (b - (m - a₁)) :=
  rfl

/-- **Multiplicativity of `ι₁₂`** (Gannon §5.1.2): the two `z₂`-dominant expansions multiply
to the expansion of the sum of exponents,
`ι₁₂((z₁-z₂)^m)·ι₁₂((z₁-z₂)^n) = ι₁₂((z₁-z₂)^{m+n})`, i.e. `convolPos m n = expandPos (m+n)`.
The algebraic core is the generalized-binomial Vandermonde `cbz_vandermonde`.
(FIX vs. the prior draft: the sign collapse is done by a single `negOnePow_add` rewrite into
`•`-scaled summands, and the scalar is pulled out with `smul_finsum'` on `•`, not `*`.) -/
theorem expandPos_mul (m n : ℤ) : convolPos m n = expandPos (m + n) := by
  ext a b
  rw [convolPos_apply]
  by_cases hdiag : a + b = m + n
  · -- on the antidiagonal: rewrite each factor via `cbz`, scale by the (single) sign `(-1)^b`
    have hstep : ∀ b₁ : ℤ,
        expandPos m (m - b₁) b₁ * expandPos n (a - (m - b₁)) (b - b₁)
          = negOnePow b • (cbz m b₁ * cbz n (b - b₁)) := by
      intro b₁
      rw [expandPos_diag_cbz m b₁]
      by_cases hb1 : 0 ≤ b - b₁
      · have he : a - (m - b₁) = n - (b - b₁) := by omega
        rw [he, expandPos_diag_cbz n (b - b₁), smul_eq_mul]
        rw [show negOnePow b₁ * cbz m b₁ * (negOnePow (b - b₁) * cbz n (b - b₁))
              = (negOnePow b₁ * negOnePow (b - b₁)) * (cbz m b₁ * cbz n (b - b₁)) from by ring,
          ← negOnePow_add, show b₁ + (b - b₁) = b from by ring]
      · rw [expandPos_eq_zero_of_neg n (a - (m - b₁)) (by omega), mul_zero,
          cbz_neg' n (by omega), mul_zero, smul_zero]
    rw [show (∑ᶠ b₁ : ℤ, expandPos m (m - b₁) b₁ * expandPos n (a - (m - b₁)) (b - b₁))
          = ∑ᶠ b₁ : ℤ, negOnePow b • (cbz m b₁ * cbz n (b - b₁)) from finsum_congr hstep]
    rw [← smul_finsum' (negOnePow b) (cbz_convol_support_finite m n b)]
    rw [show (∑ᶠ b₁ : ℤ, cbz m b₁ * cbz n (b - b₁)) = cbzConvol m n b from rfl, cbz_vandermonde,
      smul_eq_mul]
    -- RHS: `expandPos (m+n) a b = negOnePow b * cbz (m+n) b` (diagonal value, all `b`)
    rw [show a = (m + n) - b from by omega, expandPos_diag_cbz (m + n) b]
  · -- off the antidiagonal both sides vanish
    rw [expandPos_eq_zero_off_diag (m + n) a b hdiag]
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro b₁
    by_cases h1 : (m - b₁) + b₁ = m
    · rw [expandPos_eq_zero_off_diag n (a - (m - b₁)) (b - b₁) (by omega), mul_zero]
    · rw [expandPos_eq_zero_off_diag m (m - b₁) b₁ h1, zero_mul]

/-- **Multiplicativity of `ι₂₁`** (the `z₁`-dominant companion of `expandPos_mul`):
`ι₂₁((z₁-z₂)^m)·ι₂₁((z₁-z₂)^n) = ι₂₁((z₁-z₂)^{m+n})`, i.e. `convolNeg m n = expandNeg (m+n)`.
The sign collapses by `(-1)^{m+a₁}·(-1)^{n+(a-a₁)} = (-1)^{(m+n)+a}` via two `negOnePow_add`s. -/
theorem expandNeg_mul (m n : ℤ) : convolNeg m n = expandNeg (m + n) := by
  ext a b
  rw [convolNeg_apply]
  by_cases hdiag : a + b = m + n
  · have hstep : ∀ a₁ : ℤ,
        expandNeg m a₁ (m - a₁) * expandNeg n (a - a₁) (b - (m - a₁))
          = negOnePow ((m + n) + a) • (cbz m a₁ * cbz n (a - a₁)) := by
      intro a₁
      rw [expandNeg_diag_cbz m a₁]
      by_cases ha1 : 0 ≤ a - a₁
      · have he : b - (m - a₁) = n - (a - a₁) := by omega
        rw [he, expandNeg_diag_cbz n (a - a₁), smul_eq_mul]
        rw [show negOnePow (m + a₁) * cbz m a₁ * (negOnePow (n + (a - a₁)) * cbz n (a - a₁))
              = (negOnePow (m + a₁) * negOnePow (n + (a - a₁)))
                  * (cbz m a₁ * cbz n (a - a₁)) from by ring,
          ← negOnePow_add, show (m + a₁) + (n + (a - a₁)) = (m + n) + a from by ring]
      · rw [expandNeg_eq_zero_of_neg n (b - (m - a₁)) (by omega), mul_zero,
          cbz_neg' n (by omega), mul_zero, smul_zero]
    rw [show (∑ᶠ a₁ : ℤ, expandNeg m a₁ (m - a₁) * expandNeg n (a - a₁) (b - (m - a₁)))
          = ∑ᶠ a₁ : ℤ, negOnePow ((m + n) + a) • (cbz m a₁ * cbz n (a - a₁)) from
      finsum_congr hstep]
    rw [← smul_finsum' (negOnePow ((m + n) + a)) (cbz_convol_support_finite m n a)]
    rw [show (∑ᶠ a₁ : ℤ, cbz m a₁ * cbz n (a - a₁)) = cbzConvol m n a from rfl, cbz_vandermonde,
      smul_eq_mul]
    rw [show b = (m + n) - a from by omega, expandNeg_diag_cbz (m + n) a]
  · rw [expandNeg_eq_zero_off_diag (m + n) a b hdiag]
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro a₁
    by_cases h1 : a₁ + (m - a₁) = m
    · rw [expandNeg_eq_zero_off_diag n (a - a₁) (b - (m - a₁)) (by omega), mul_zero]
    · rw [expandNeg_eq_zero_off_diag m a₁ (m - a₁) h1, zero_mul]

/-! ## §3  The unit, and the general-order δ-jump consequences (the lattice gate) -/

/-- The two-variable unit `1 = z₁⁰z₂⁰`: coefficient `[a=0][b=0]`. -/
def unitDist : FormalDist₂ ℂ := fun a b => if a = 0 ∧ b = 0 then (1 : ℂ) else 0

@[simp] theorem unitDist_apply (a b : ℤ) :
    unitDist a b = if a = 0 ∧ b = 0 then (1 : ℂ) else 0 := rfl

/-- The coefficient of `ι₁₂((z₁-z₂)^0)` is `[a=0][b=0]`, all `a b`. -/
theorem expandPos_zero_apply (a b : ℤ) :
    expandPos 0 a b = if a = 0 ∧ b = 0 then (1 : ℂ) else 0 := by
  rw [expandPos_apply]
  by_cases h : 0 ≤ b ∧ a = 0 - b
  · obtain ⟨hb, ha⟩ := h
    by_cases hb0 : b = 0
    · subst hb0; rw [if_pos ⟨le_rfl, by omega⟩, if_pos ⟨by omega, rfl⟩,
        show ((0 : ℤ)).toNat = 0 from rfl, gBinom_zero, mul_one]
      simp [negOnePow]
    · rw [if_pos ⟨hb, ha⟩, if_neg (by rintro ⟨_, h⟩; omega),
        gBinom, Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr (by omega)) (by push_cast; ring)]
      simp
  · rw [if_neg h, if_neg (by rintro ⟨ha, hb⟩; exact h ⟨by omega, by omega⟩)]

/-- The unit: `ι₁₂((z₁-z₂)^0) = 1`. -/
theorem expandPos_zero : expandPos 0 = unitDist := by
  ext a b; rw [unitDist_apply, expandPos_zero_apply]

/-- The coefficient of `ι₂₁((z₁-z₂)^0)` is `[a=0][b=0]`, all `a b`. -/
theorem expandNeg_zero_apply (a b : ℤ) :
    expandNeg 0 a b = if a = 0 ∧ b = 0 then (1 : ℂ) else 0 := by
  rw [expandNeg_apply]
  by_cases h : 0 ≤ a ∧ b = 0 - a
  · obtain ⟨ha, hb⟩ := h
    by_cases ha0 : a = 0
    · subst ha0; rw [if_pos ⟨le_rfl, by omega⟩, if_pos ⟨rfl, by omega⟩,
        show ((0 : ℤ)).toNat = 0 from rfl, gBinom_zero, mul_one]
      simp [negOnePow]
    · rw [if_pos ⟨ha, hb⟩, if_neg (by rintro ⟨h, _⟩; omega),
        gBinom, Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr (by omega)) (by push_cast; ring)]
      simp
  · rw [if_neg h, if_neg (by rintro ⟨ha, hb⟩; exact h ⟨by omega, by omega⟩)]

/-- The two expansions agree at `n = 0` (both are the genuine two-variable unit `1`). -/
theorem expandNeg_zero : expandNeg 0 = expandPos 0 := by
  ext a b; rw [expandPos_zero_apply, expandNeg_zero_apply]

/-- **`expandPos` as a multiplicative monoid morphism on the exponent.**  Re-stated for the
lattice exp-of-oscillator bookkeeping: `ι₁₂((z₁-z₂)^m)·ι₁₂((z₁-z₂)^n)` (the `convolPos`
product) equals `ι₁₂((z₁-z₂)^{m+n})`; combined with `expandPos_zero` this exhibits the
family `{expandPos n}_{n∈ℤ}` as the homomorphic image of `(ℤ,+)` (group, since each `n` has
the inverse `-n`).  This is the bookkeeping the `(z-w)^{⟨α,β⟩}` lattice factor consumes. -/
theorem convolPos_zero_right (m : ℤ) : convolPos m 0 = expandPos m := by
  rw [expandPos_mul, add_zero]

theorem convolPos_zero_left (n : ℤ) : convolPos 0 n = expandPos n := by
  rw [expandPos_mul, zero_add]

/-- The `z₁-z₂` reproducing power law via the engine `mulBySub_expandPos`:
`(z₁-z₂)^N · ι₁₂((z₁-z₂)^{m}) = ι₁₂((z₁-z₂)^{m+N})`. -/
theorem mulBySubPow_expandPos (N : ℕ) (m : ℤ) :
    mulBySubPow N (expandPos m) = expandPos (m + (N : ℤ)) := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [mulBySubPow_succ, LinearMap.comp_apply, ih, mulBySub_expandPos,
        show m + ((k : ℤ)) + 1 = m + (((k + 1 : ℕ)) : ℤ) from by push_cast; ring]

/-- **The regular-part / reproducing identity** for the lattice OPE (Gannon §5.1.2):
`(z₁-z₂)^N · ι₁₂((z₁-z₂)^{-N}) = 1`.  A high enough power of `(z₁-z₂)` extracts the regular
part: applied to the singular factor `ι₁₂((z₁-z₂)^{-N})` it returns the unit.  This is the
identity the lattice vertex operator uses to strip the `(z₁-z₂)^{⟨α,β⟩}` prefactor. -/
theorem mulBySubPow_expandPos_neg (N : ℕ) :
    mulBySubPow N (expandPos (-(N : ℤ))) = expandPos 0 := by
  rw [mulBySubPow_expandPos, neg_add_cancel]

/-- The same companion for the `z₁`-dominant expansion `expandNeg`. -/
theorem mulBySubPow_expandNeg (N : ℕ) (m : ℤ) :
    mulBySubPow N (expandNeg m) = expandNeg (m + (N : ℤ)) := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [mulBySubPow_succ, LinearMap.comp_apply, ih, mulBySub_expandNeg,
        show m + ((k : ℤ)) + 1 = m + (((k + 1 : ℕ)) : ℤ) from by push_cast; ring]

theorem mulBySubPow_expandNeg_neg (N : ℕ) :
    mulBySubPow N (expandNeg (-(N : ℤ))) = expandNeg 0 := by
  rw [mulBySubPow_expandNeg, neg_add_cancel]

/-- **The general-order δ-jump is killed by `(z₁-z₂)^{k+1}`.**  Extends
`negPowJump_eq_deltaDeriv`: `(z₁-z₂)^{k+1} · Jₖ = 0`, where `Jₖ = ι₁₂((z₁-z₂)^{-k-1}) −
ι₂₁((z₁-z₂)^{-k-1})` is the `ι₁₂ − ι₂₁` jump of `(z₁-z₂)^{-k-1}`.  This is the lattice-locality
gate for the diagonal `⟨α,α⟩`-power: a high enough power of `(z₁-z₂)` annihilates the jump. -/
theorem mulBySubPow_negPowJump_self (k : ℕ) :
    mulBySubPow (k + 1) (negPowJump k) = 0 := by
  rw [negPowJump_eq_deltaDeriv, map_smul, mulBySubPow_succ_deltaDeriv, smul_zero]

/-- **The sharp lattice-locality bound** (Proposition 5.1.2 specialized to the negative-power
jump): for any `N ≥ k+1`, `(z₁-z₂)^N · Jₖ = 0`.  This is the precise `(z₁-z₂)^{⟨α,β⟩}` locality
order the lattice vertex operator consumes: the OPE singularity of order `k+1` is annihilated
by `(z₁-z₂)^N` for all `N > k`. -/
theorem mulBySubPow_negPowJump_eq_zero {k N : ℕ} (h : k + 1 ≤ N) :
    mulBySubPow N (negPowJump k) = 0 := by
  rw [negPowJump_eq_deltaDeriv, map_smul, mulBySubPow_deltaDeriv_eq_zero h, smul_zero]

/-- The δ-decomposition of the jump (the converse content of Proposition 5.1.2 made explicit
for the lattice OPE): `Jₖ` is a single `δ`-derivative term `(1/k!)·∂ᵏδ`, hence lies in the
span of `{∂ʲδ}_{j<k+1}` — which is exactly the `local_iff_deltaSum` normal form at bound
`N = k+1`.  This packages the jump as the locality data `(z₁-z₂)^{k+1}`-locality provides. -/
theorem negPowJump_deltaSum (k : ℕ) :
    ∃ c : Fin (k + 1) → FormalDist ℂ,
      negPowJump k = ∑ j : Fin (k + 1), deltaDeriv (j : ℕ) (c j) :=
  (local_iff_deltaSum (negPowJump k) (k + 1)).mp (mulBySubPow_negPowJump_self k)

/-! ## §4  Smoke tests / the lattice-VO consumer interface -/

/-- Sanity: the `n = -1` instance of the jump bound is `(z₁-z₂)·(ι₁₂ − ι₂₁)(1/(z₁-z₂)) = 0`,
i.e. `(z₁-z₂)·δ = 0`. -/
example : mulBySubPow 1 (negPowJump 0) = 0 := mulBySubPow_negPowJump_self 0

/-- Sanity: multiplicativity composes — `ι₁₂((z₁-z₂)^m)·ι₁₂((z₁-z₂)^{-m}) = 1`. -/
example (m : ℤ) : convolPos m (-m) = expandPos 0 := by rw [expandPos_mul, add_neg_cancel]

/-- Sanity: the reproducing identity strips the order-`3` pole. -/
example : mulBySubPow 3 (expandPos (-3)) = expandPos 0 := mulBySubPow_expandPos_neg 3

end VOA
