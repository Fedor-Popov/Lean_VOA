/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.LambertSeries

/-!
# The pinned normalisation of Zhu's Eisenstein family  (TASK 1c, normalisation layer)

`ZhuRecursionAt` deliberately carries the coefficient family `G : ℕ → (ℕ → ℂ)` as a **parameter**,
because the constant relating the several standard Eisenstein normalisations is exactly the sort of
thing one must not guess.  This file records the normalisation that is actually forced, and builds
it.

## Which normalisation, and how it was settled

The coefficient function appearing in

  `𝒵_M(a[−1]v; q) = tr_M(o(a)o(v)q^{L₀−c/24}) + Σ_{k ≥ 1} G_{2k}(q)·𝒵_M(a[2k−1]v; q)`

is

  `G_{2k}(q) = −B_{2k}/(2k)! + (2/(2k−1)!)·Σ_{n ≥ 1} σ_{2k−1}(n)·qⁿ = −(B_{2k}/(2k)!)·E_{2k}(q)`,

the *Zhu-normalised* Eisenstein series — `E_{2k}` (constant term `1`, the `eisensteinCoeff`
normalisation, which is Mathlib's) rescaled by the nonzero constant `−B_{2k}/(2k)!`.  Equivalently
it is `G_{2k} = 2ζ(2k)E_{2k}` with the transcendental factor `(2πi)^{2k}` divided out, using
`2ζ(2k)/(2πi)^{2k} = −B_{2k}/(2k)!`.

This was determined by an exact-rational computation on the rank-one Heisenberg VOA
(`certificates/mathematica/zhu_eisenstein_norm.wl`, `certificates/mathematica/zhu_simul.wl`, `certificates/mathematica/zhu_g10_check.wl`), where
`o(α) = α₀ = 0` on the vacuum Fock module makes the two-point term drop out, so the recursion
becomes a pure *determination* of the `G_{2k}`.  Two probes were used — `a = v = α` (pins `G₂`
alone, giving `G₂ = 2 q d log Z/dq = −1/12 + 2Σσ₁(n)qⁿ = −E₂/12`) and `a = α`, `v = α₋ₙ|0⟩`
(pins all higher `k`).  Solving the resulting **unconstrained** linear system (n = 1…10, 110
equations, 55 unknown `q`-coefficients) has a unique solution, matching the formula above for
`2k = 2,4,6,8,10` through `O(q¹⁰)`.  The alternatives were explicitly *falsified*, not merely
disfavoured: plain
`E_{2k}` (constant term `1`) — false; `2ζ(2k)E_{2k}` — false; the `(2πi)^{2k}`-carrying form and
"`E_{2k} − 1`, no constant term" — both false (the constant term is essential).

⚠ **The engine is confirmation, not derivation.**  What is *proved* below is the algebra relating
the two normalisations (`zhuG_eq_smul_zhuEisenstein`) and the shape of the convolution
(`qConv_zhuG_eq`).  That `ZhuRecursionAt N zhuG` actually **holds** is proved downstream as
`zhuRecursionPinned_holds` (`Modularity/ZhuRecursionClose.lean`); the engine's role was only to
remove the risk of building the assembly against the wrong constant.

## What this file provides
* `zhuG j` — the pinned family `G_{2j}`, defined by its closed form **without** dividing by a
  Bernoulli number (so it is unconditionally well-behaved);
* `zhuG_eq_smul_zhuEisenstein` — it is `−(B_{2j}/(2j)!)·E_{2j}`, the bridge to `zhuEisenstein`;
* `qConv_zhuG_eq` — the pinned right-hand side split as "constant·`g` + Lambert tail";
* `ZhuRecursionPinned` — `ZhuRecursionAt` at the pinned family.

## Status
Proved, axiom-clean, `pbw`-free.  The recursion itself is still the named residual.

## References
* Zhu, J. AMS 9 (1996), Prop. 4.3.2 and §4.4; Gannon §5.3.5; Serre, *A Course in Arithmetic*,
  VII §4.
-/

namespace VOA

open scoped BigOperators

/-- **The pinned Zhu coefficient family** `G_{2j}`:
`G_{2j}(q) = −B_{2j}/(2j)! + (2/(2j−1)!)·Σ_{n≥1} σ_{2j−1}(n)qⁿ`.

Defined by this closed form rather than as a multiple of `zhuEisenstein`, so that no Bernoulli
number is ever divided by; `zhuG_eq_smul_zhuEisenstein` supplies the comparison. -/
noncomputable def zhuG (j : ℕ) : ℕ → ℂ :=
  fun m =>
    if m = 0 then -(((bernoulli (2 * j) : ℚ) : ℂ) / (Nat.factorial (2 * j) : ℂ))
    else (2 / (Nat.factorial (2 * j - 1) : ℂ)) * lambertCoeff (2 * j - 1) m

/-- The constant term of `G_{2j}` is `−B_{2j}/(2j)!` — *not* `1`, and not `0`.  Both of those
alternatives are falsified by the Heisenberg computation; see the module docstring. -/
@[simp] theorem zhuG_zero (j : ℕ) :
    zhuG j 0 = -(((bernoulli (2 * j) : ℚ) : ℂ) / (Nat.factorial (2 * j) : ℂ)) := by
  rw [zhuG, if_pos rfl]

/-- The higher coefficients of `G_{2j}`: `(2/(2j−1)!)·σ_{2j−1}(m)`. -/
theorem zhuG_of_ne_zero (j : ℕ) {m : ℕ} (hm : m ≠ 0) :
    zhuG j m = (2 / (Nat.factorial (2 * j - 1) : ℂ)) * lambertCoeff (2 * j - 1) m := by
  rw [zhuG, if_neg hm]

/-- `(2j)! = 2j·(2j−1)!` over `ℂ`, for `j ≠ 0` — the factorial step that converts the `2/(2j−1)!` of
`zhuG` into the `4j/(2j)!` produced by rescaling `E_{2j}`. -/
theorem factorial_two_mul_cast {j : ℕ} (hj : j ≠ 0) :
    (Nat.factorial (2 * j) : ℂ)
      = (2 * (j : ℂ)) * (Nat.factorial (2 * j - 1) : ℂ) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * j = n + 1 := ⟨2 * j - 1, by omega⟩
  have h1 : 2 * j - 1 = n := by omega
  have hc : (2 : ℂ) * (j : ℂ) = (n : ℂ) + 1 := by exact_mod_cast hn
  rw [h1, hn, Nat.factorial_succ]
  push_cast
  rw [hc]

/-- **The bridge between the two normalisations**:
`G_{2j} = −(B_{2j}/(2j)!)·E_{2j}`, where `E_{2j} = zhuEisenstein j` has constant term `1`.

The hypothesis `bernoulli (2*j) ≠ 0` is genuine only as a *bookkeeping* device: it is needed because
`zhuEisenstein` divides by `B_{2j}` while `zhuG` does not, so the two agree exactly when that
division is meaningful.  The hypothesis is in fact always satisfied (`B_{2j} ≠ 0` for every
`j ≥ 1`, e.g. by von Staudt–Clausen, or by `riemannZeta_two_mul_nat` together with `ζ(2j) ≠ 0`),
but Mathlib carries no such lemma, so it is carried explicitly rather than asserted. -/
theorem zhuG_eq_smul_zhuEisenstein {j : ℕ} (hj : j ≠ 0)
    (hB : ((bernoulli (2 * j) : ℚ) : ℂ) ≠ 0) (m : ℕ) :
    zhuG j m
      = -(((bernoulli (2 * j) : ℚ) : ℂ) / (Nat.factorial (2 * j) : ℂ)) * zhuEisenstein j m := by
  by_cases hm : m = 0
  · subst hm
    rw [zhuG_zero, zhuEisenstein_zero, mul_one]
  · have hfac : (Nat.factorial (2 * j - 1) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hjc : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hj
    rw [zhuG_of_ne_zero j hm, zhuEisenstein_eq_lambert j hm, factorial_two_mul_cast hj]
    push_cast
    field_simp

/-! ## The pinned right-hand side -/

/-- **The pinned Eisenstein convolution, split**:
`(G_{2j} ⋆ g)(e) = (−B_{2j}/(2j)!)·g(e) + (2/(2j−1)!)·(Lambert tail)(e)`.

This is the exact shape the assembled recursion must produce: the constant term of `G_{2j}`
multiplies `g` itself, and the divisor-sum tail is what `q`-graded trace cyclicity
(`trace_weightBlock_comm_shift`) generates.  Compare `qConv_zhuEisenstein_eq`, which is the same
split in the `E`-normalisation; the difference between the two statements *is* the normalisation
constant. -/
theorem qConv_zhuG_eq (j : ℕ) (g : FormalQSeries) (e : ℂ)
    (hfin : (Function.support fun n : ℕ =>
      lambertCoeff (2 * j - 1) n * g (e - (n : ℂ))).Finite) :
    qConv (zhuG j) g e
      = -(((bernoulli (2 * j) : ℚ) : ℂ) / (Nat.factorial (2 * j) : ℂ)) * g e
        + (2 / (Nat.factorial (2 * j - 1) : ℂ)) * lambertConv (2 * j - 1) g e := by
  have hpt : ∀ n : ℕ, zhuG j n * g (e - (n : ℂ))
      = (if n = 0 then -(((bernoulli (2 * j) : ℚ) : ℂ) / (Nat.factorial (2 * j) : ℂ)) * g e else 0)
        + (2 / (Nat.factorial (2 * j - 1) : ℂ))
          * (lambertCoeff (2 * j - 1) n * g (e - (n : ℂ))) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [zhuG_zero, if_pos rfl, lambertCoeff_zero, zero_mul, mul_zero, add_zero,
        Nat.cast_zero, sub_zero]
    · rw [if_neg hn, zero_add, zhuG_of_ne_zero j hn]
      ring
  have h1 : (Function.support fun n : ℕ =>
      (if n = 0 then -(((bernoulli (2 * j) : ℚ) : ℂ) / (Nat.factorial (2 * j) : ℂ)) * g e
        else 0)).Finite := by
    refine Set.Finite.subset (Set.finite_singleton 0) (fun n hn => ?_)
    simp only [Function.mem_support, ne_eq] at hn
    simp only [Set.mem_singleton_iff]
    by_contra hc
    exact hn (if_neg hc)
  have h2 : (Function.support fun n : ℕ =>
      (2 / (Nat.factorial (2 * j - 1) : ℂ))
        * (lambertCoeff (2 * j - 1) n * g (e - (n : ℂ)))).Finite := by
    refine hfin.subset (fun n hn => ?_)
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro hz
    exact hn (by rw [hz, mul_zero])
  rw [qConv, finsum_congr hpt, finsum_add_distrib h1 h2,
    finsum_eq_single _ (0 : ℕ) (fun n hn => if_neg hn), if_pos rfl,
    ← mul_finsum' _ _ hfin]
  rfl

/-! ## Zhu's recursion at the pinned family -/

section
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **Zhu's recursion with the pinned normalisation** — `ZhuRecursionAt` at `zhuG`.

This, rather than `ZhuRecursionEisenstein`, is the true statement: the Heisenberg computation
falsifies the `E`-normalised variant.  Proved downstream as `zhuRecursionPinned_holds`
(`Modularity/ZhuRecursionClose.lean`). -/
def ZhuRecursionPinned (N : OrdVModule W M) (a v : 𝒱) (ka : ℕ) : Prop :=
  ZhuRecursionAt N zhuG a v ka

end

/-! ## Former residuals

* **The recursion itself** (`ZhuRecursionPinned` holds) — Zhu Prop. 4.3.2 — is proved:
  `zhuRecursionPinned_holds` (`Modularity/ZhuRecursionClose.lean`).
* **`bernoulli (2*j) ≠ 0`** — carried as a hypothesis by `zhuG_eq_smul_zhuEisenstein` alone; it is
  proved in the library as `bernoulli_two_mul_ne_zero` (`Modularity/EisensteinAnalytic.lean`).
-/

end VOA
