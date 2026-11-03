/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmRightDiff
import VOA.Modules.ZhuVermaAnArchBottomDefectClose
import VOA.Modules.ZhuRingInstance

/-!
# Dong–Jiang Lemma 2.8 — the base case `n = 0` of the induction on `n`.

The sole open Half-A core is the pole-difference right-action-difference family membership

  `(DJ 2.8)   anmRightDiff W n K a c d ∈ Onm W n 0`

(`ZhuVermaAnArchAnmRightDiff`, the `a`-outer twin of the discharged `crossDiffComm`), the Lean form of
the Dong–Jiang filtration ideal property `V ∗ⁿ₀ O(V) ⊆ O_{n,0}(V)`.  The pinned proof structure is an
**induction on the level `n`**: the grade-lowering commutator content
is already fully proven (`crossDiffComm_mem_Onm`), so the remaining content is the pure inter-level
filtration statement, and the natural handle is the level `n`.

## This file — the base case `n = 0` (a genuinely closed brick)

At level `n = 0` the family `anmRightDiff` is *identically the zero vector*, so its membership is trivial.
Concretely, `anmRightDiff_eq_terms` (`ZhuVermaAnArchAnmRightDiff`) gives

  `anmRightDiff W n K a c d
     = anmRight W n 0 a (anmCirc W 0 0 c d) − anmRight W n 0 a (anmCirc W n 0 c d)`,

and at `n = 0` the two circles coincide (`anmCirc W 0 0 c d = anmCirc W (0 : ℕ) 0 c d`), so the whole
difference is `X − X = 0` (`sub_self`).  Membership in `Onm W 0 0` is then `Submodule.zero_mem`.

This is *stronger* than the abstract `n = 0` Zhu-algebra base case sketched in the audit
(`a ∗⁰₀ (c ∘⁰₀ d) ∈ O(V)` via the two-sided ideal property of `O(V)`): because `anmRightDiff` is a
*pole-difference*, its `n = 0` instance is not merely in `O(V)` — it is literally `0`.  We record both
the vanishing (`anmRightDiff_base_eq_zero`) and the membership (`anmRightDiff_base_mem`), the latter
being exactly the `n = 0` instance of `(DJ 2.8)`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemmas 2.2–2.8); Gannon §5.3.2,
Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The base case `n = 0`: `anmRightDiff` vanishes identically. -/

/-- **`anmRightDiff` vanishes at level `n = 0`.**  For homogeneous `a ∈ 𝒱_K`,
`anmRightDiff W 0 K a c d = 0`.  By `anmRightDiff_eq_terms`,
`anmRightDiff W 0 K a c d = anmRight W 0 0 a (anmCirc W 0 0 c d) − anmRight W 0 0 a (anmCirc W 0 0 c d)`
— the two terms are the *same* level-`0` circle (`anmCirc W n 0` at `n = 0` is `anmCirc W 0 0`), so the
difference is `sub_self`. -/
theorem anmRightDiff_base_eq_zero (W : VertexOperatorAlgebra 𝒱) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c d : 𝒱) :
    anmRightDiff W 0 K a c d = 0 := by
  rw [anmRightDiff_eq_terms W 0 ha c d, sub_self]

/-! ## The base case `n = 0` of Dong–Jiang Lemma 2.8. -/

/-- **The base case `n = 0` of `(DJ 2.8)`.**  For homogeneous `a ∈ 𝒱_K`,
`anmRightDiff W 0 K a c d ∈ Onm W 0 0`.  Immediate from `anmRightDiff_base_eq_zero` (the family is `0`)
and `Submodule.zero_mem`.  This is the (trivial) base brick of the induction on `n` for
`V ∗ⁿ₀ O(V) ⊆ O_{n,0}(V)`. -/
theorem anmRightDiff_base_mem (W : VertexOperatorAlgebra 𝒱) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c d : 𝒱) :
    anmRightDiff W 0 K a c d ∈ Onm W 0 0 := by
  rw [anmRightDiff_base_eq_zero W ha c d]
  exact Submodule.zero_mem _

/-- **The base case `n = 0` of `(DJ 2.8)`, universally quantified over the homogeneous data.**  This is
exactly the `n = 0` slice of the target predicate `∀ n K M P, ∀ homogeneous a c d, anmRightDiff ∈ Onm`
required by `HARDhom_of_towerEqs`/`MUGradedAction_of_HARDhom`. -/
theorem anmRightDiff_base_mem_forall (W : VertexOperatorAlgebra 𝒱) :
    ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ _c ∈ W.grading (M : ℤ),
      ∀ _d ∈ W.grading (P : ℤ), anmRightDiff W 0 K a _c _d ∈ Onm W 0 0 :=
  fun _K _M _P a ha _c _ _d _ => anmRightDiff_base_mem W ha _c _d

/-! ## The *meaningful* base case: the DJ Lemma 2.8 closures at level `n = 0` are the Zhu
two-sided ideal property.

The trivial vanishing above is the `n = 0` slice of the *difference* `anmRightDiff`.  The genuine
`n = 0` base case of the induction — the one that seeds the level-recursion for the individual pieces
`Term₁ = a *ⁿ₀ (c ∘⁰₀ d)` and `Term₂ = a *ⁿ₀ (c ∘ⁿ₀ d)` — is the statement that the level-`0`
Dong–Jiang closures hold, which at `n = 0` collapse *exactly* to Zhu's two-sided ideal property of
`O(𝒱)`.  Concretely, `Onm W 0 0 = O W` (`Onm_zero_zero_eq_O`) and `anmRight W 0 0 = zhuMul W`
(`anmRight_zero_zero`), so:

* **`AnmCrossClosure W 0`** (`𝒱 *⁰₀ O_{0,0} ⊆ O'_{0,0}`) is Zhu's **right** ideal `𝒱 * O(𝒱) ⊆ O(𝒱)`;
* **`AnmRightModule W 0`** (`O'_{0,0} *⁰₀ 𝒱 ⊆ O'_{0,0}`) is Zhu's **left** ideal `O(𝒱) * 𝒱 ⊆ O(𝒱)`.

Both are discharged unconditionally by `zhuRingData_holds` (Zhu Thm 2.1.1/2.1.2, an in-repo theorem,
not an axiom). -/

/-- **The `n = 0` base case of the DJ Lemma 2.8 cross closure** — Zhu's *right* ideal.  `AnmCrossClosure
W 0` says `∀ a, ∀ g ∈ Onm W 0 0, anmRight W 0 0 a g ∈ Onm W 0 0`; via `Onm_zero_zero_eq_O` and
`anmRight_zero_zero` this is `∀ a, ∀ g ∈ O W, zhuMul W a g ∈ O W`, i.e. `𝒱 * O(𝒱) ⊆ O(𝒱)`
(`ZhuRingData.right_ideal`). -/
theorem AnmCrossClosure_base (W : VertexOperatorAlgebra 𝒱) : AnmCrossClosure W 0 := by
  intro a g hg
  rw [Onm_zero_zero_eq_O] at hg ⊢
  rw [anmRight_zero_zero]
  exact (zhuRingData_holds W).right_ideal a hg

/-- **The `n = 0` base case of the DJ Lemma 2.8 right-module closure** — Zhu's *left* ideal.
`AnmRightModule W 0` says `∀ g ∈ Onm W 0 0, ∀ v, anmRight W 0 0 g v ∈ Onm W 0 0`; via
`Onm_zero_zero_eq_O` and `anmRight_zero_zero` this is `∀ g ∈ O W, ∀ v, zhuMul W g v ∈ O W`, i.e.
`O(𝒱) * 𝒱 ⊆ O(𝒱)` (`ZhuRingData.left_ideal`). -/
theorem AnmRightModule_base (W : VertexOperatorAlgebra 𝒱) : AnmRightModule W 0 := by
  intro g hg v
  rw [Onm_zero_zero_eq_O] at hg ⊢
  rw [anmRight_zero_zero]
  exact (zhuRingData_holds W).left_ideal hg v

/-- **The `n = 0` base of both `Term₁` and `Term₂`.**  At `n = 0` the two pieces of `anmRightDiff`
coincide (`anmCirc W 0 0 = anmCirc W (0 : ℕ) 0`): `anmRight W 0 0 a (anmCirc W 0 0 c d) ∈ Onm W 0 0`.
Immediate from `AnmCrossClosure_base` applied to the circle generator `anmCirc W 0 0 c d ∈ Onm W 0 0`
(`anmCirc_mem_Onm`).  This is the coach's base brick `a *⁰₀ (c ∘⁰₀ d) ∈ O(𝒱)`. -/
theorem anmRight_circ_base (W : VertexOperatorAlgebra 𝒱) (a c d : 𝒱) :
    anmRight W 0 0 a (anmCirc W 0 0 c d) ∈ Onm W 0 0 :=
  AnmCrossClosure_base W a _ (anmCirc_mem_Onm W 0 0 c d)

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmRightDiff_base_eq_zero
  #print axioms VOA.anmRightDiff_base_mem
  #print axioms VOA.anmRightDiff_base_mem_forall
-/
