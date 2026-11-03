/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormPStep
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Floor

/-!
# FHL full invariance, reduced to two precise analytic residuals (`GoodBound` + `CreationVanish`)

Building on `Core.InvariantFormPStep` (which reduced the would-be general-`B` FHL statement to the
pure `p`-recursion predicate `PStep`), this file performs the **convergence analysis** that
closes the
recursion modulo two sharply-isolated inputs, reducing that route to
`GoodBound B ∧ CreationVanish B`.

* **`matchDiff_iterate`** — the iterated pure `p`-recursion
  `riseCoeff_k · D(p,q,a,b) = D(p+k, q, (L₋₁)ᵏa, b)`, `riseCoeff = ∏_{i<k}(p+i+wt−q)`.
* **`factorial_le_norm_riseCoeff`** / **`tendsto_pow_div_riseCoeff`** — in the *good regime*
  `1 ≤ p+wt−q`, the rising factorial dominates every polynomial (`(k+1)^d/‖riseCoeff‖ → 0`).
* **`matchDiff_eq_zero_good`** — hence, given a polynomial bound `IterPolyBound` on the iterate, the
  squeeze forces `D(p,q,a,b) = 0` in the good regime.
* **`matchDiff_down_step`** / **`diagAt_of_inputs`** — downward `p`-propagation through every
  non-creation mode, seeded at the creation grade, assembles `DiagAt B wt q`.
* **`isFullyInvariant_of_inputs`** — full `IsFullyInvariant` from `GoodBound B` + `CreationVanish B`.

## Status
**Delimited by a conditional obstruction.** The iterated recursion, rising-factorial estimate,
squeeze, and downward propagation are axiom-clean.
`Core.InvariantFormDelimitation.general_fhlClosure_not_a_theorem` rules out uniform
`GoodBound B ∧ CreationVanish B` only under `hqp` and an explicitly supplied nonsymmetric
grade-one invariant-form witness; it does not construct that witness.  The canonical-form theorem
is complete in `Core.InvariantFormFHL2`.

⚠ **Honest caveat (verified).** `GoodBound` turns out to be *equivalent in strength* to the FHL
identity, not a soft estimate: since `matchDiff_iterate` gives `D_k = riseCoeff_k • D₀` and
`factorial_le_norm_riseCoeff` gives `k! ≤ ‖riseCoeff_k‖` in the good regime, a polynomial bound on
`D_k` forces `D₀ = 0` — so `GoodBound B` is exactly the good-regime slice of `DiagonalFHL`. The
convergence machinery here is genuine and reusable, but it does **not** reduce the *difficulty*: the
irreducible FHL core is `Core.InvariantFormDiagonal.DiagonalFHL` (reached directly by
`isFullyInvariant_of_diagonal`). `CreationVanish` is proved for `a = 𝟙`/`wt ≤ 0`; its hard wedge
(`1 ≤ wt ≤ q`) is the `n = −1` free initial condition, also of FHL strength. Both residuals are
hypotheses, not axioms.  They are retained as a delimited reduction interface, not as an active
proof obligation.

## References
* Gannon §5.1.3, eq. (5.1.11a); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA.VertexOperatorAlgebra

open scoped BigOperators
open Filter Topology

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- Under the diagonal at grade `q−1`, the matching-mode recursion (★) loses its `L₁b` branch,
giving the **pure `p`-recursion** `(p+wt−q)·D(p,q,a,b) = D(p+1,q,L₋₁a,b)`. -/
theorem matchDiff_pure_rec (B : InvariantForm W) {wt q : ℤ} (hwt : 0 ≤ wt)
    (hlow : DiagAt B wt (q - 1)) {u : 𝒱} (hu : u ∈ W.grading wt)
    {p : ℤ} {a b : 𝒱} (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) :
    ((p + wt - q : ℤ) : ℂ) • matchDiff B wt p q u a b
      = matchDiff B wt (p + 1) q u (W.L (-1) a) b := by
  have hrec := matchDiff_rec B hwt hu ha hb
  have hL1b : W.L 1 b ∈ W.grading (q - 1) := L_one_lower W hb
  have hbranch : matchDiff B wt p (q - 1) u a (W.L 1 b) = 0 :=
    hlow p u a (W.L 1 b) hu ha hL1b
  rw [hbranch, sub_zero] at hrec
  exact hrec

/-- `(L₋₁)ᵏ` raises the grading by `k`: `(L₋₁)ᵏ 𝒱_p ⊆ 𝒱_{p+k}`. -/
theorem L_neg_one_pow_raise (W : VertexOperatorAlgebra 𝒱) {p : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading p) (k : ℕ) : ((W.L (-1)) ^ k) a ∈ W.grading (p + k) := by
  induction k with
  | zero => simpa using ha
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := W.L_neg_one_raise ih
    rwa [show (p + (n : ℤ)) + 1 = p + ((n : ℤ) + 1) by ring, ← Nat.cast_one, ← Nat.cast_add] at h

/-- The **rising-factorial coefficient** `∏_{i=0}^{k-1}(p+i+wt−q)` of the iterated recursion. -/
noncomputable def riseCoeff (p wt q : ℤ) (k : ℕ) : ℂ :=
  ∏ i ∈ Finset.range k, ((p + (i : ℤ) + wt - q : ℤ) : ℂ)

@[simp] theorem riseCoeff_zero (p wt q : ℤ) : riseCoeff p wt q 0 = 1 := by
  simp [riseCoeff]

theorem riseCoeff_succ (p wt q : ℤ) (k : ℕ) :
    riseCoeff p wt q (k + 1) = riseCoeff p wt q k * ((p + (k : ℤ) + wt - q : ℤ) : ℂ) := by
  rw [riseCoeff, riseCoeff, Finset.prod_range_succ]

/-- **The iterated pure `p`-recursion.**
`(∏_{i<k}(p+i+wt−q))·D(p,q,a,b) = D(p+k, q, (L₋₁)ᵏa, b)`. -/
theorem matchDiff_iterate (B : InvariantForm W) {wt q : ℤ} (hwt : 0 ≤ wt)
    (hlow : DiagAt B wt (q - 1)) {u : 𝒱} (hu : u ∈ W.grading wt) :
    ∀ (k : ℕ) {p : ℤ} {a b : 𝒱}, a ∈ W.grading p → b ∈ W.grading q →
      riseCoeff p wt q k • matchDiff B wt p q u a b
        = matchDiff B wt (p + k) q u (((W.L (-1)) ^ k) a) b := by
  intro k
  induction k with
  | zero =>
    intro p a b ha hb
    simp only [riseCoeff_zero, one_smul, Nat.cast_zero, add_zero, pow_zero,
      Module.End.one_apply]
  | succ n ih =>
    intro p a b ha hb
    have hstep := matchDiff_pure_rec B hwt hlow hu ha hb
    have hLa : W.L (-1) a ∈ W.grading (p + 1) := W.L_neg_one_raise ha
    have hih := ih (p := p + 1) (a := W.L (-1) a) (b := b) hLa hb
    have hcoeff : riseCoeff p wt q (n + 1)
        = riseCoeff (p + 1) wt q n * ((p + wt - q : ℤ) : ℂ) := by
      rw [riseCoeff, riseCoeff, Finset.prod_range_succ']
      simp only [Nat.cast_zero, add_zero]
      congr 1
      refine Finset.prod_congr rfl (fun i _ => ?_)
      congr 1
      push_cast
      ring
    rw [hcoeff, mul_smul]
    rw [hstep, hih]
    rw [show (p + 1 + (n : ℤ)) = p + ((n : ℤ) + 1) by ring, ← Nat.cast_one, ← Nat.cast_add,
      ← Module.End.mul_apply, ← pow_succ]

/-- In the **good regime** `1 ≤ p+wt−q`, the norm of `riseCoeff` dominates `k!`. -/
theorem factorial_le_norm_riseCoeff {p wt q : ℤ} (hp : 1 ≤ p + wt - q) (k : ℕ) :
    (k.factorial : ℝ) ≤ ‖riseCoeff p wt q k‖ := by
  rw [riseCoeff, norm_prod]
  rw [show (k.factorial : ℝ) = ∏ i ∈ Finset.range k, ((i : ℝ) + 1) from by
    rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl]
  refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
  rw [Complex.norm_intCast]
  have : ((i : ℝ) + 1) ≤ ((p + (i : ℤ) + wt - q : ℤ) : ℝ) := by
    exact_mod_cast (by omega : ((i:ℤ)+1) ≤ p + (i:ℤ) + wt - q)
  calc ((i : ℝ) + 1) ≤ ((p + (i : ℤ) + wt - q : ℤ) : ℝ) := this
    _ ≤ |((p + (i : ℤ) + wt - q : ℤ) : ℝ)| := le_abs_self _

/-- **The rising factorial beats every polynomial.**  In the good regime, for any degree `d`,
`(k+1)^d / ‖riseCoeff p wt q k‖ → 0`. -/
theorem tendsto_pow_div_riseCoeff {p wt q : ℤ} (hp : 1 ≤ p + wt - q) (d : ℕ) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ d / ‖riseCoeff p wt q k‖) atTop (𝓝 0) := by
  have hbase : Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ d / (k.factorial : ℝ)) atTop (𝓝 0) := by
    have hlit : (fun k : ℕ => ((k : ℝ) + 1) ^ d) =o[atTop] (fun k : ℕ => (k.factorial : ℝ)) := by
      have h1 : (fun k : ℕ => ((k : ℝ) + 1) ^ d) =o[atTop] (fun k : ℕ => (2 : ℝ) ^ k) := by
        have hk : (fun k : ℕ => (k : ℝ) ^ d) =o[atTop] (fun k : ℕ => (2 : ℝ) ^ k) :=
          isLittleO_pow_const_const_pow_of_one_lt d (by norm_num)
        have hb : (fun k : ℕ => ((k : ℝ) + 1) ^ d) =O[atTop] (fun k : ℕ => (k : ℝ) ^ d) := by
          refine Asymptotics.IsBigO.of_bound (2 ^ d) ?_
          filter_upwards [eventually_ge_atTop 1] with k hk1
          have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
            abs_of_nonneg (by positivity), ← mul_pow]
          apply pow_le_pow_left₀ (by positivity)
          nlinarith [hk1']
        exact hb.trans_isLittleO hk
      have h2 : (fun k : ℕ => (2 : ℝ) ^ k) =o[atTop] (fun k : ℕ => (k.factorial : ℝ)) := by
        rw [Asymptotics.isLittleO_iff]
        intro c hc
        have := (FloorSemiring.tendsto_pow_div_factorial_atTop (2 : ℝ)).eventually_lt_const hc
        filter_upwards [this] with k hk
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          abs_of_nonneg (by positivity)]
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < (k.factorial : ℝ))] at hk
        nlinarith [hk]
      exact h1.trans h2
    have := hlit.tendsto_div_nhds_zero
    simpa using this
  apply squeeze_zero (fun k => by positivity) (fun k => ?_) hbase
  rcases Nat.eq_zero_or_pos k.factorial with h0 | hpos
  · exact absurd h0 (Nat.factorial_ne_zero k)
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact factorial_le_norm_riseCoeff hp k

/-- **The polynomial-bound residual (the genuine analytic estimate of FHL).**  For a fixed
homogeneous datum, the iterate `D(p+k, q, (L₋₁)ᵏa, b)` grows at most polynomially in `k`.  A
*hypothesis* here (honest, not faked, not an axiom). -/
def IterPolyBound (B : InvariantForm W) (wt q : ℤ) (u a b : 𝒱) (p : ℤ) : Prop :=
  ∃ (C : ℝ) (d : ℕ), ∀ k : ℕ,
    ‖matchDiff B wt (p + k) q u (((W.L (-1)) ^ k) a) b‖ ≤ C * ((k : ℝ) + 1) ^ d

/-- **Good-regime vanishing.**  In the good regime `1 ≤ p+wt−q`, the iterate identity together with
a polynomial bound on the iterate forces `D(p,q,a,b) = 0`. -/
theorem matchDiff_eq_zero_good (B : InvariantForm W) {wt q : ℤ} (hwt : 0 ≤ wt)
    (hlow : DiagAt B wt (q - 1)) {u : 𝒱} (hu : u ∈ W.grading wt) {p : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hgood : 1 ≤ p + wt - q)
    (hbd : IterPolyBound B wt q u a b p) :
    matchDiff B wt p q u a b = 0 := by
  obtain ⟨C, d, hC⟩ := hbd
  set D₀ := matchDiff B wt p q u a b with hD₀
  have hiter : ∀ k : ℕ, riseCoeff p wt q k • D₀
      = matchDiff B wt (p + k) q u (((W.L (-1)) ^ k) a) b :=
    fun k => matchDiff_iterate B hwt hlow hu k ha hb
  have hrise_ne : ∀ k : ℕ, riseCoeff p wt q k ≠ 0 := by
    intro k
    rw [riseCoeff]
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
    exact_mod_cast (by omega : (p + (i : ℤ) + wt - q : ℤ) ≠ 0)
  have hnormD : ∀ k : ℕ, ‖D₀‖ ≤ C * ((k : ℝ) + 1) ^ d / ‖riseCoeff p wt q k‖ := by
    intro k
    have h1 : ‖riseCoeff p wt q k‖ * ‖D₀‖
        = ‖matchDiff B wt (p + k) q u (((W.L (-1)) ^ k) a) b‖ := by
      rw [← norm_mul, ← smul_eq_mul, ← hiter k]
    have hposr : (0 : ℝ) < ‖riseCoeff p wt q k‖ := norm_pos_iff.mpr (hrise_ne k)
    rw [le_div_iff₀ hposr, mul_comm]
    rw [h1]
    exact hC k
  have hlim : Tendsto (fun k : ℕ => C * ((k : ℝ) + 1) ^ d / ‖riseCoeff p wt q k‖)
      atTop (𝓝 0) := by
    have := (tendsto_pow_div_riseCoeff hgood d).const_mul C
    simpa [mul_div_assoc] using this
  have hDle : ‖D₀‖ ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hnormD
  have : ‖D₀‖ = 0 := le_antisymm hDle (norm_nonneg _)
  exact norm_eq_zero.mp this

/-- **One downward step.**  If `p+wt−q ≠ 0` and the diagonal vanishes one step up (at source `p+1`
with `L₋₁a`), then it vanishes at source `p`. -/
theorem matchDiff_down_step (B : InvariantForm W) {wt q : ℤ} (hwt : 0 ≤ wt)
    (hlow : DiagAt B wt (q - 1)) {u : 𝒱} (hu : u ∈ W.grading wt) {p : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hne : (p + wt - q : ℤ) ≠ 0)
    (hup : matchDiff B wt (p + 1) q u (W.L (-1) a) b = 0) :
    matchDiff B wt p q u a b = 0 := by
  have hstep := matchDiff_pure_rec B hwt hlow hu ha hb
  rw [hup] at hstep
  have hcne : ((p + wt - q : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hne
  rcases smul_eq_zero.mp hstep with h | h
  · exact absurd h hcne
  · exact h

/-- `matchDiff` vanishes when `a` lies in a negative grade (then `a = 0`). -/
theorem matchDiff_eq_zero_of_neg_p (B : InvariantForm W) {wt p q : ℤ} (hp : p < 0) {u a b : 𝒱}
    (ha : a ∈ W.grading p) : matchDiff B wt p q u a b = 0 := by
  rw [eq_zero_of_mem_neg_grading W hp ha, matchDiff, fhlDiff_zero_left]

/-- **`DiagAt` from the two residual inputs.**  Given the lower-grade diagonal, the good-regime
polynomial bound and the single creation-mode value at `p = q−wt`, the full diagonal holds: good
regime by convergence, bad regime by downward propagation seeded at the creation mode. -/
theorem diagAt_of_inputs (B : InvariantForm W) {wt q : ℤ} (hwt : 0 ≤ wt)
    (hlow : DiagAt B wt (q - 1))
    (hgood : ∀ (p : ℤ) (u a b : 𝒱), u ∈ W.grading wt → a ∈ W.grading p → b ∈ W.grading q →
      1 ≤ p + wt - q → IterPolyBound B wt q u a b p)
    (hcreation : ∀ (u a b : 𝒱), u ∈ W.grading wt → a ∈ W.grading (q - wt) → b ∈ W.grading q →
      matchDiff B wt (q - wt) q u a b = 0) :
    DiagAt B wt q := by
  intro p u a b hu ha hb
  rcases lt_or_ge p 0 with hpneg | hp0
  · exact matchDiff_eq_zero_of_neg_p B hpneg ha
  rcases le_or_gt (q - wt + 1) p with hpgood | hpbad
  · exact matchDiff_eq_zero_good B hwt hlow hu ha hb (by omega)
      (hgood p u a b hu ha hb (by omega))
  · have hple : p ≤ q - wt := by omega
    have key : ∀ m : ℕ, ∀ a' : 𝒱, a' ∈ W.grading (q - wt - m) →
        matchDiff B wt (q - wt - m) q u a' b = 0 := by
      intro m
      induction m with
      | zero =>
        intro a' ha'
        simpa using hcreation u a' b hu (by simpa using ha') hb
      | succ n ih =>
        intro a' ha'
        have hne : ((q - wt - ((n : ℤ) + 1)) + wt - q : ℤ) ≠ 0 := by omega
        have hLa' : W.L (-1) a' ∈ W.grading (q - wt - ((n : ℤ) + 1) + 1) := W.L_neg_one_raise ha'
        have hup : matchDiff B wt (q - wt - ((n : ℤ) + 1) + 1) q u (W.L (-1) a') b = 0 := by
          have hidx : q - wt - ((n : ℤ) + 1) + 1 = q - wt - (n : ℤ) := by ring
          rw [hidx] at hLa' ⊢
          exact ih (W.L (-1) a') hLa'
        have := matchDiff_down_step B hwt hlow hu ha' hb (by push_cast; exact hne) hup
        simpa using this
    have hm : ((q - wt - p).toNat : ℤ) = q - wt - p := Int.toNat_of_nonneg (by omega)
    have hamem : a ∈ W.grading (q - wt - ((q - wt - p).toNat : ℤ)) := by
      rw [hm, show q - wt - (q - wt - p) = p by ring]; exact ha
    have := key (q - wt - p).toNat a hamem
    rwa [hm, show q - wt - (q - wt - p) = p by ring] at this

/-- **The good-regime polynomial-bound residual, globally.** -/
def GoodBound (B : InvariantForm W) : Prop :=
  ∀ (wt q p : ℤ) (u a b : 𝒱), u ∈ W.grading wt → a ∈ W.grading p → b ∈ W.grading q →
    1 ≤ p + wt - q → IterPolyBound B wt q u a b p

/-- **The creation-mode residual, globally.**  At the exceptional source grade `p = q−wt`
(mode `n = −1`), the matching-mode obstruction vanishes. -/
def CreationVanish (B : InvariantForm W) : Prop :=
  ∀ (wt q : ℤ) (u a b : 𝒱), u ∈ W.grading wt → a ∈ W.grading (q - wt) → b ∈ W.grading q →
    matchDiff B wt (q - wt) q u a b = 0

/-- **`PStep` from the two residual inputs.** -/
theorem pstep_of_inputs (B : InvariantForm W) (hG : GoodBound B) (hC : CreationVanish B) :
    PStep B := by
  intro wt q hwt _hq hprev
  have hlow : DiagAt B wt (q - 1) := hprev (q - 1) (by omega)
  exact diagAt_of_inputs B hwt hlow
    (fun p u a b hu ha hb hgd => hG wt q p u a b hu ha hb hgd)
    (fun u a b hu ha hb => hC wt q u a b hu ha hb)

/-- **Full FHL from the two residual inputs.**  Composing `pstep_of_inputs` with the already-built
`isFullyInvariant_of_pstep`, the entire Frenkel–Huang–Lepowsky full-invariance theorem follows from
the good-regime polynomial bound and the creation-mode value. -/
theorem isFullyInvariant_of_inputs (B : InvariantForm W) (hG : GoodBound B) (hC : CreationVanish B) :
    B.IsFullyInvariant :=
  isFullyInvariant_of_pstep B (pstep_of_inputs B hG hC)

end VOA.VertexOperatorAlgebra
