/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.TraceIndependence
import VOA.Modularity.GrowthBound

/-!
# The characters do not vanish identically

`Modularity.TraceIndependence` reduces `TraceIndependent` to two hypotheses: distinct
`T`-eigenvalues, and `TraceNonvanishing`.  This file discharges the **second** one from
summability alone, by evaluating the character at a point of the imaginary axis.

## The mechanism

At `τ = i·t` (`t > 0`) the parameter `q = e^{2πiτ}` is the **positive real** number `e^{−2πt}`.
The character's coefficients are dimensions, hence nonnegative reals, and the leading one is
`dim M_h ≥ 1` because `HasConformalWeight` says `M_h ≠ 0`.  So the sum has real part `≥ 1`, and
`qEvalAt` — which multiplies by the nowhere-zero `e^{2πiτ(h−c/24)}` — is nonzero there.

## Contents

* `imAxis t` — the point `i·t ∈ ℍ`, with `qParam_imAxis : q = e^{−2πt} > 0`.
* `one_le_re_tsum_gradedDim` — the character series has real part `≥ 1` at `i·t`.
* `qEvalAt_gradedDim_ne_zero` — the character is nonzero at `i·t`.
* **`traceNonvanishing_of_qSummable`** — hence `TraceNonvanishing`, taking `v = 𝟙`
  (square-bracket weight `0`, `𝒵_M(𝟙) = χ_M`).
* **`traceIndependent_of_tEigen_injective'`** — `TraceIndependent` from *only* the distinct
  `T`-eigenvalues plus summability of the characters, the latter supplied by
  `Modularity.BuhlSpanningC2` whenever the modules carry ordered spanning data.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The imaginary axis -/

/-- The point `i·t` of the upper half-plane (`t > 0`). -/
noncomputable def imAxis (t : ℝ) (ht : 0 < t) : UpperHalfPlane :=
  ⟨Complex.I * (t : ℂ), by simp [ht]⟩

@[simp] theorem coe_imAxis (t : ℝ) (ht : 0 < t) :
    ((imAxis t ht : UpperHalfPlane) : ℂ) = Complex.I * (t : ℂ) := rfl

/-- At `i·t` the parameter `q = e^{2πiτ}` is the positive real `e^{−2πt}`. -/
theorem qParam_imAxis (t : ℝ) (ht : 0 < t) :
    qParam (imAxis t ht) = ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) := by
  rw [qParam, coe_imAxis]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (Complex.I * (t : ℂ)))
      = ((-(2 * Real.pi * t) : ℝ) : ℂ) from by
    push_cast
    rw [show Complex.I * ((t : ℂ) : ℂ) = (t : ℂ) * Complex.I from by ring]
    rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I)
        = 2 * (Real.pi : ℂ) * (t : ℂ) * (Complex.I * Complex.I) from by ring,
      Complex.I_mul_I]
    ring]
  rw [← Complex.ofReal_exp]

/-! ## The character series has real part at least one -/

section Char

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The character's coefficients: `gradedDim N` along `h − c/24 + ℕ` is `dim M_{h+n}`. -/
theorem gradedDim_shift (N : OrdVModule W M) (h : ℂ) (n : ℕ) :
    gradedDim N (h - W.centralCharge / 24 + (n : ℂ))
      = (Module.finrank ℂ (N.weight (h + (n : ℂ))) : ℂ) := by
  rw [gradedDim, show h - W.centralCharge / 24 + (n : ℂ) + W.centralCharge / 24
    = h + (n : ℂ) from by ring]

/-- **The character series has real part `≥ 1` at `i·t`.** -/
theorem one_le_re_tsum_gradedDim (N : OrdVModule W M) (h : ℂ) (hcw : HasConformalWeight N h)
    (t : ℝ) (ht : 0 < t)
    (hsum : QSummableAt (gradedDim N) (h - W.centralCharge / 24) (imAxis t ht)) :
    1 ≤ (∑' n : ℕ, gradedDim N (h - W.centralCharge / 24 + (n : ℂ))
          * (qParam (imAxis t ht)) ^ n).re := by
  set r : ℝ := Real.exp (-(2 * Real.pi * t)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hterm : ∀ n : ℕ, gradedDim N (h - W.centralCharge / 24 + (n : ℂ))
      * (qParam (imAxis t ht)) ^ n
      = (((Module.finrank ℂ (N.weight (h + (n : ℂ))) : ℝ) * r ^ n : ℝ) : ℂ) := by
    intro n
    rw [gradedDim_shift, qParam_imAxis, ← hr]
    push_cast
    ring
  have hcong : (fun n : ℕ => gradedDim N (h - W.centralCharge / 24 + (n : ℂ))
      * (qParam (imAxis t ht)) ^ n)
      = fun n : ℕ => (((Module.finrank ℂ (N.weight (h + (n : ℂ))) : ℝ) * r ^ n : ℝ) : ℂ) :=
    funext hterm
  have hsum' : Summable
      (fun n : ℕ => (Module.finrank ℂ (N.weight (h + (n : ℂ))) : ℝ) * r ^ n) := by
    have hs := hsum
    rw [QSummableAt, hcong] at hs
    exact Complex.summable_ofReal.mp hs
  have hre : (∑' n : ℕ, gradedDim N (h - W.centralCharge / 24 + (n : ℂ))
      * (qParam (imAxis t ht)) ^ n)
      = ((∑' n : ℕ, (Module.finrank ℂ (N.weight (h + (n : ℂ))) : ℝ) * r ^ n : ℝ) : ℂ) := by
    rw [hcong, Complex.ofReal_tsum]
  rw [hre, Complex.ofReal_re]
  have hnn : ∀ n : ℕ, 0 ≤ (Module.finrank ℂ (N.weight (h + (n : ℂ))) : ℝ) * r ^ n := by
    intro n; positivity
  have hle := hsum'.le_tsum 0 (fun n _ => hnn n)
  refine le_trans ?_ hle
  have h0 : h + ((0 : ℕ) : ℂ) = h := by norm_num
  rw [h0, pow_zero, mul_one]
  haveI := N.finrank h
  have hne : N.weight h ≠ ⊥ := hcw.1
  have hpos : 0 < Module.finrank ℂ (N.weight h) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ (N.weight h)) with hz | hp
    · exact absurd (Submodule.finrank_eq_zero.mp hz) hne
    · exact hp
  exact_mod_cast hpos

/-- **The character is nonzero at `i·t`.** -/
theorem qEvalAt_gradedDim_ne_zero (N : OrdVModule W M) (h : ℂ) (hcw : HasConformalWeight N h)
    (t : ℝ) (ht : 0 < t)
    (hsum : QSummableAt (gradedDim N) (h - W.centralCharge / 24) (imAxis t ht)) :
    qEvalAt (gradedDim N) (h - W.centralCharge / 24) (imAxis t ht) ≠ 0 := by
  rw [qEvalAt]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  intro hz
  have := one_le_re_tsum_gradedDim N h hcw t ht hsum
  rw [hz, Complex.zero_re] at this
  linarith

end Char

/-! ## `TraceNonvanishing` and the improved independence theorem -/

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}
variable (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- `𝟙` has square-bracket weight `0`. -/
theorem vacuum_mem_sqWeightSpace_zero (W : VertexOperatorAlgebra 𝒱) :
    W.vacuum ∈ sqWeightSpace W ((0 : ℕ) : ℂ) := by
  rw [mem_sqWeightSpace_iff, Nat.cast_zero, zero_smul, Lsq_zero_apply]
  refine finsum_eq_zero_of_forall_eq_zero (fun a => ?_)
  by_cases ha : a < 0
  · rw [sqBracketCoeff_zero_of_neg ha, zero_smul]
  · push_neg at ha
    rw [VertexOperatorAlgebra.L_def,
      show mode (W.Y W.conformalVector) (a + 1) W.vacuum
        = W.smul W.conformalVector (a + 1) W.vacuum from rfl,
      W.smul_vacuum_nonneg _ (by omega), smul_zero]

/-- **`TraceNonvanishing` from summability of the characters.**  Take `v = 𝟙`: the trace
function is the character, which is nonzero on the imaginary axis. -/
theorem traceNonvanishing_of_qSummable (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsum : ∀ (i : ι) (t : ℝ) (ht : 0 < t),
      QSummableAt (gradedDim (Mfam i).isMod) (h i - W.centralCharge / 24) (imAxis t ht)) :
    TraceNonvanishing Mfam h := by
  intro i
  refine ⟨0, W.vacuum, vacuum_mem_sqWeightSpace_zero W, imAxis 1 one_pos, ?_⟩
  rw [traceFun, torusOnePoint_vacuum, torusPartition]
  exact qEvalAt_gradedDim_ne_zero (Mfam i).isMod (h i) (hcw i) 1 one_pos (hsum i 1 one_pos)

/-- **`TraceIndependent` from distinct `T`-eigenvalues and summability alone.**

Combining `Modularity.TraceIndependence.traceIndependent_of_tEigen_injective` with the
nonvanishing above: the *only* remaining input is that the conformal weights be pairwise distinct
modulo `ℤ`, plus convergence of the characters — which `Modularity.BuhlSpanningC2` supplies from
`C₂`-cofiniteness whenever the modules carry ordered spanning data. -/
theorem traceIndependent_of_tEigen_injective' (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hinj : Function.Injective (tEigen W h))
    (hsum : ∀ (i : ι) (t : ℝ) (ht : 0 < t),
      QSummableAt (gradedDim (Mfam i).isMod) (h i - W.centralCharge / 24) (imAxis t ht)) :
    TraceIndependent Mfam h :=
  traceIndependent_of_tEigen_injective Mfam h hcw hinj
    (traceNonvanishing_of_qSummable Mfam h hcw hsum)

/-- **`TraceIndependent` from ordered spanning data.**  Combining with
`Modularity.GrowthBound.subexponentialCoeffs_of_ordered`: once every module of the family carries
ordered (colored-partition) spanning data — which `Modularity.BuhlSpanningC2` produces from
`C₂`-cofiniteness — the *only* remaining hypothesis of `TraceIndependent` is that the conformal
weights be pairwise distinct modulo `ℤ`. -/
theorem traceIndependent_of_orderedSpanning (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hinj : Function.Injective (tEigen W h))
    (hspan : ∀ i, Nonempty (OrderedSpanningData (Mfam i).isMod (h i))) :
    TraceIndependent Mfam h := by
  refine traceIndependent_of_tEigen_injective' Mfam h hcw hinj (fun i t ht => ?_)
  refine qSummable_gradedDim _ _ ?_ _
  exact (hspan i).elim (fun d => subexponentialCoeffs_of_ordered (Mfam i).isMod (h i) d)

end Family

end VOA
