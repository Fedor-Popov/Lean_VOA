/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ChiralBlock

/-!
# Zhu's recursion — the corrected formal statement  (Gannon 5.3.17 / Zhu Prop. 4.3.2)

Zhu's recursion expresses a one-point function of `a[−1]v` in terms of a two-point trace plus an
Eisenstein-weighted sum of one-point functions of `a[2k−1]v`:

  `𝒵_M(a[−1]v; τ) = tr_M(o(a)o(v)q^{L₀−c/24}) + Σ_{k ≥ 1} G_{2k}(τ)·𝒵_M(a[2k−1]v; τ)`,

together with the companion vanishing `𝒵_M(a[0]v; τ) = 0`.

## Two statement bugs fixed here

The earlier interface in `OnePointFunctions` (`ZhuRecursion`) had two defects, corrected in this file:

1. **The product must be a convolution.**  `FormalQSeries = ℂ → ℂ` is the *coefficient* function
   `e ↦ [q^e]`, so the product of two `q`-series is the Cauchy **convolution**, not the pointwise
   product of functions.  Since the Eisenstein series have `ℕ`-indexed exponents, the right operation
   is `qConv : (ℕ → ℂ) → FormalQSeries → FormalQSeries`,
   `(f ⋆ g)(e) = Σᶠ_{n : ℕ} f n · g (e − n)` (`qConv`).
2. **The `Σ_{k ≥ 1}` needs a finiteness witness.**  It is supplied by the VOA itself: VA5 regularity
   forces `a[m]v = 0` for all large `m` (`vSqZ_eventually_zero`), so only finitely many `k` contribute
   (`zhuRecursion_support_finite`).  With that, `∑ᶠ k` is a genuine finite sum.

## Status
The corrected **statement** (`ZhuRecursionAt`), its finiteness witness, and the supporting `q`-series
algebra are proved here, axiom-clean and `pbw`-free.  The Eisenstein layer and the proof of the
recursion itself are the named residuals (see the end of the file).

## References
* Gannon §5.3.5, eq. (5.3.17); Zhu, *Modular invariance…*, J. AMS 9 (1996), Prop. 4.3.2.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The finiteness witness: square-bracket modes vanish for large index -/

/-- **`a[m]v = 0` for all large `m`** — VA5 `regularity` plus the lower-triangularity of the
square-bracket coefficients (`sqBracketCoeffZ_of_lt`: the coefficient vanishes for `i < m`, and every
`i ≥ m ≥ N` kills the ordinary mode).  This is the finiteness witness that makes Zhu's `Σ_{k≥1}`
well-defined. -/
theorem vSqZ_eventually_zero (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) (k : ℕ) (x : 𝒱) :
    ∃ N : ℤ, ∀ m : ℤ, N ≤ m → vSqZ W v k m x = 0 := by
  obtain ⟨N, hN⟩ := W.regularity v x
  refine ⟨N, fun m hm => ?_⟩
  rw [vSqZ_apply]
  have hz : (fun i : ℤ => sqBracketCoeffZ k m i • mode (W.Y v) i x) = fun _ => 0 := by
    funext i
    by_cases hi : m ≤ i
    · rw [hN i (by omega), smul_zero]
    · push_neg at hi
      rw [sqBracketCoeffZ_of_lt k hi, zero_smul]
  rw [hz, finsum_zero]

/-! ## `q`-series convolution -/

/-- **Convolution of a formal `q`-series against an `ℕ`-indexed one**:
`(f ⋆ g)(e) = Σᶠ_{n} f n · g (e − n)` — the Cauchy product `[qᵉ](f·g)`.  This is the correct product
for Zhu's recursion; the pointwise product of `ℂ → ℂ` would be meaningless. -/
noncomputable def qConv (f : ℕ → ℂ) (g : FormalQSeries) : FormalQSeries :=
  fun e => ∑ᶠ n : ℕ, f n * g (e - (n : ℂ))

@[simp] theorem qConv_zero_right (f : ℕ → ℂ) : qConv f 0 = 0 := by
  funext e
  simp only [qConv, Pi.zero_apply, mul_zero, finsum_zero]

@[simp] theorem qConv_zero_left (g : FormalQSeries) : qConv 0 g = 0 := by
  funext e
  simp only [qConv, Pi.zero_apply, zero_mul, finsum_zero]

/-! ## Vanishing of the one-point function at `0` -/

section
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

@[simp] theorem torusOnePoint_zero (N : OrdVModule W M) : torusOnePoint N (0 : 𝒱) = 0 := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  rw [torusOnePoint, onePoint, map_zero]
  show LinearMap.trace ℂ _ (weightBlock N 0 (e + W.centralCharge / 24)) = 0
  rw [show weightBlock N (0 : Module.End ℂ M) (e + W.centralCharge / 24) = 0 from by
    simp only [weightBlock, LinearMap.zero_comp, LinearMap.comp_zero], map_zero]

/-! ## The corrected recursion statement -/

/-- **Zhu's recursion at `(a, v)`** (Gannon 5.3.17 / Zhu Prop. 4.3.2), stated correctly:
`𝒵_M(a[−1]v) = tr_M(o(a)o(v)q^{L₀−c/24}) + Σ_{k≥1} G_{2k} ⋆ 𝒵_M(a[2k−1]v)`,
with `⋆` the `q`-series **convolution** `qConv` and the `Σ_{k≥1}` a genuine finite sum
(`zhuRecursion_support_finite`).  `G : ℕ → (ℕ → ℂ)` is the Eisenstein family as formal `q`-expansion
coefficients, `G k` standing for `G_{2k}`. -/
def ZhuRecursionAt (N : OrdVModule W M) (G : ℕ → (ℕ → ℂ)) (a v : 𝒱) (ka : ℕ) : Prop :=
  torusOnePoint N (vSqZ W a ka (-1) v)
    = torusTwoPoint N a v
      + ∑ᶠ k : ℕ, qConv (G (k + 1))
          (torusOnePoint N (vSqZ W a ka (2 * (k + 1) - 1 : ℤ) v))

/-- **The companion vanishing** `𝒵_M(a[0]v; τ) = 0` (Zhu Prop. 4.3.2, the `n = 0` case). -/
def ZhuVanishingAt (N : OrdVModule W M) (a v : 𝒱) (ka : ℕ) : Prop :=
  torusOnePoint N (vSqZ W a ka 0 v) = 0

/-- **The finiteness witness**: only finitely many `k` contribute to Zhu's sum, because
`a[2k−1]v = 0` once `2k−1` exceeds the regularity bound (`vSqZ_eventually_zero`).  So the `∑ᶠ k` in
`ZhuRecursionAt` is a genuine finite sum, not a formal artifact. -/
theorem zhuRecursion_support_finite (N : OrdVModule W M) (G : ℕ → (ℕ → ℂ)) (a v : 𝒱) (ka : ℕ) :
    (Function.support fun k : ℕ => qConv (G (k + 1))
      (torusOnePoint N (vSqZ W a ka (2 * (k + 1) - 1 : ℤ) v))).Finite := by
  obtain ⟨Nb, hNb⟩ := vSqZ_eventually_zero W a ka v
  refine Set.Finite.subset (Set.finite_Iio Nb.toNat) ?_
  intro k hk
  simp only [Function.mem_support, ne_eq] at hk
  simp only [Set.mem_Iio]
  by_contra hc
  push_neg at hc
  exact hk (by rw [hNb (2 * (k + 1) - 1 : ℤ) (by omega), torusOnePoint_zero, qConv_zero_right])

end

/-! ## Residual

* **The Eisenstein layer.** `G : ℕ → (ℕ → ℂ)` is carried as formal `q`-expansion coefficient data.
  Mathlib's `EisensteinSeries.E_qExpansion_coeff` (proved, `k ≥ 3` even) and `E2`/`G2` supply the
  concrete coefficients; instantiating `G` from them is a leaf-file job (it would be the repo's first
  `Mathlib.NumberTheory.*` import, so it must not sit under the green core).
* **The recursion itself** (`ZhuRecursionAt` holds).  This is Zhu Prop. 4.3.2: it needs the module-mode
  commutator, the cyclicity of the graded trace, and the `sqBracketCoeffZ` bookkeeping — the real
  theorem, not yet proved here.
-/

end VOA
