/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuODEAssembly

/-!
# ⚠ The unitriangular hypothesis `huni` **collapses** — a certificate

The natural reading of Zhu Lemma 4.4.4 as a statement about *every* `v`,

  `huni` : `∀ v i, ∃ hc, … ∧ 𝒵(L[−2]^i v) = ∑_{j ≤ i} hc j ⋆ (q d/dq)^j 𝒵(v)`,

is **not provable**, and this file says exactly why in one line of mathematics.

Apply it at `i = 1` to `v = L[−1]x`.  The right-hand side is built entirely from `𝒵(v)`, and
`𝒵(L[−1]x) = 0` unconditionally (`torusOnePoint_Lsq_neg_one`), so the right-hand side is `0`.  The
left-hand side is `𝒵(L[−2]L[−1]x)`, which the (unconditional) square-bracket Virasoro relation
rewrites as `−𝒵(L[−3]x)`.  Hence `huni` forces `𝒵(L[−3]x) = 0` for every `x`, and then — feeding
`x ↦ L[−1]x` back in — `𝒵(L[−n]x) = 0` for **every** `n ≥ 3`.

That is a statement about the trace functions that neither Zhu nor Dong–Li–Mason assert and that
does not follow from `IsFormalBlock`.  The obstruction is structural, not a missing lemma: the
right-hand side of `huni` only ever sees `𝒵(v)`, whereas the `ω`-law's tail
`∑ₖ G_{2k} ⋆ 𝒵(L[2k−2]v)` sees the *other* vectors `L[2k−2]v`, whose one-point functions are not
`ℂ⟦q⟧`-multiples of `𝒵(v)`.

**The route to residual (c) therefore does not go through `huni`.**  See
`Modularity.BlockSystem`: the correct object is the *first-order system* satisfied by a finite
`SubexpPS`-generating family of the block span, not a scalar ODE for a single `v`.

## ⚠⚠ What this file refutes — and what it does **not**

The hypothesis refuted here is the one quantified over **every** `v`.  The refutation runs entirely
through `v = L[−1]x`, and that vector is **not square-bracket primary**: the Virasoro relation gives
`L[1]L[−1]x = L[−1]L[1]x + 2L[0]x ≠ 0` in general.

Arakawa–Kawasetsu (arXiv:1610.05865v4) state the same conclusion — their Lemma 5.5 — **only for a
primary `a`** ("`L[0]a = Δa` and `L[n]a = 0` for `n ≥ 1`"), and their Theorem 5.1 needs it only at
`a = |0⟩`, which is primary.  So the collapse below is simply **not an instance of AK Lemma 5.5**,
and this file is **not** an obstruction to the Arakawa–Kawasetsu route.  The primary case is proved
in `Modularity.AKModularODE.huni_of_sqPrimary`, and carried to AK's equation (2) for the character
in `Modularity.AKModularODE.character_formalODE_of_etingofFinite`.

The structural diagnosis above is exactly right, and is the reason: the `ω`-law tail sees the
*other* vectors `L[2k−2]v`, and **primarity is precisely the condition that closes the tail back
into the same `L[−2]`-tower** (`Modularity.AKModularODE.Lsq_tower`).

⚠ Consequently `Modularity.ZhuODEAssembly.onePointSubexp_of_unitriangular` and
`onePointSubexp_of_unitriangular_cw` are **dead**: their `huni` is quantified over all `v` and is
refuted below.  `Modularity.ZhuODEAssembly.formalODE_of_unitriangular` in the same file is **not**
affected — it takes `v` as a *fixed* argument, with `huni` quantified only over `i`.

## Main results

* `torusOnePoint_Lsq_neg_three_eq_zero_of_uniStep` — the `i = 1` collapse;
* `torusOnePoint_Lsq_neg_eq_zero_of_uniStep` — the full collapse, all `n ≥ 3`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  These are certificates *about* a hypothesis; nothing
downstream depends on them.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

section Collapse

variable (N : OrdVModule W M)

/-- The one-point function of `L[−n]L[−1]x` in terms of `L[−n−1]`, for `n ≠ −1`. -/
theorem torusOnePoint_Lsq_comp_neg_one (n : ℤ) (hn : n ≠ -1) (x : 𝒱) :
    torusOnePoint N (Lsq W (-n) (Lsq W (-1) x))
      = ((1 - n : ℤ) : ℂ) • torusOnePoint N (Lsq W (-n - 1) x) := by
  have hne : (-n) + (-1) ≠ 0 := by omega
  have hv := Lsq_virasoro_apply' W (-n) (-1) x
  rw [if_neg hne, zero_smul, add_zero] at hv
  have hidx : ((-n) + (-1) : ℤ) = -n - 1 := by ring
  rw [hidx] at hv
  have hx : Lsq W (-n) (Lsq W (-1) x)
      = Lsq W (-1) (Lsq W (-n) x) + ((((-n) - (-1) : ℤ)) : ℂ) • Lsq W (-n - 1) x := by
    rw [← hv]; abel
  rw [hx, torusOnePoint_add, torusOnePoint_Lsq_neg_one, zero_add, torusOnePoint_smul]
  have hc : ((-n) - (-1) : ℤ) = (1 - n : ℤ) := by ring
  rw [hc]

/-- Iterated `qDeriv` of the zero series is zero. -/
theorem qDeriv_iterate_zero (j : ℕ) : (qDeriv^[j] (0 : FormalQSeries)) = 0 := by
  induction j with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext e
      change e * (0 : FormalQSeries) e = 0
      simp

/-- Cancel a nonzero complex scalar from a `FormalQSeries` equation. -/
theorem eq_zero_of_smul_eq_zero' {c : ℂ} (hc : c ≠ 0) {f : FormalQSeries}
    (h : c • f = 0) : f = 0 := by
  funext e
  have he := congrFun h e
  change c * f e = 0 at he
  rcases mul_eq_zero.mp he with h1 | h1
  · exact absurd h1 hc
  · exact h1

/-- **The `i = 1` collapse.**  The unitriangular hypothesis at `i = 1`, applied to `L[−1]x`,
forces `𝒵(L[−3]x) = 0`. -/
theorem torusOnePoint_Lsq_neg_three_eq_zero_of_uniStep
    (huni1 : ∀ v : 𝒱, ∃ hc : ℕ → PowerSeries ℂ,
      torusOnePoint N ((⇑(Lsq W (-2)))^[1] v)
        = ∑ j ∈ Finset.range 2, psSMul (hc j) (qDeriv^[j] (torusOnePoint N v)))
    (x : 𝒱) : torusOnePoint N (Lsq W (-3) x) = 0 := by
  obtain ⟨hc, hEq⟩ := huni1 (Lsq W (-1) x)
  have hz : torusOnePoint N (Lsq W (-1) x) = 0 := torusOnePoint_Lsq_neg_one N x
  have hRHS : ∑ j ∈ Finset.range 2,
      psSMul (hc j) (qDeriv^[j] (torusOnePoint N (Lsq W (-1) x))) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [hz, qDeriv_iterate_zero, psSMul_zero_right]
  rw [hRHS, Function.iterate_one] at hEq
  have hL := torusOnePoint_Lsq_comp_neg_one N 2 (by omega) x
  rw [hEq] at hL
  have h3 : (-(2 : ℤ) - 1 : ℤ) = -3 := by ring
  rw [h3] at hL
  have hne : ((1 - (2 : ℤ) : ℤ) : ℂ) ≠ 0 := by
    rw [Int.cast_ne_zero]; omega
  exact eq_zero_of_smul_eq_zero' hne hL.symm

/-- **The full collapse.**  Feeding `x ↦ L[−1]x` back in, the hypothesis forces
`𝒵(L[−n]x) = 0` for every `n ≥ 3` and every `x` — an identity no source asserts. -/
theorem torusOnePoint_Lsq_neg_eq_zero_of_uniStep
    (huni1 : ∀ v : 𝒱, ∃ hc : ℕ → PowerSeries ℂ,
      torusOnePoint N ((⇑(Lsq W (-2)))^[1] v)
        = ∑ j ∈ Finset.range 2, psSMul (hc j) (qDeriv^[j] (torusOnePoint N v)))
    : ∀ k : ℕ, ∀ x : 𝒱, torusOnePoint N (Lsq W (-(3 + (k : ℤ))) x) = 0 := by
  intro k
  induction k with
  | zero =>
      intro x
      simpa using torusOnePoint_Lsq_neg_three_eq_zero_of_uniStep N huni1 x
  | succ j ih =>
      intro x
      have hstep := torusOnePoint_Lsq_comp_neg_one N (3 + (j : ℤ)) (by omega) x
      rw [ih (Lsq W (-1) x)] at hstep
      have hne : ((1 - (3 + (j : ℤ)) : ℤ) : ℂ) ≠ 0 := by
        rw [Int.cast_ne_zero]; omega
      have h0 := eq_zero_of_smul_eq_zero' hne hstep.symm
      have hidx : (-(3 + (j : ℤ)) - 1 : ℤ) = -(3 + ((j + 1 : ℕ) : ℤ)) := by push_cast; ring
      rwa [hidx] at h0

end Collapse

end VOA
