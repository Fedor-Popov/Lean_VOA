/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGateB1Ann
import VOA.Modules.ZhuVermaAnArchCollapseAssoc

/-!
# The `(n,0)` ideal-descent: `o_{n,0}(O_{n,0}(𝒱))` annihilates the bottom.

`ZhuVermaAnArchGate`/`ZhuVermaAnArchGateB1Ann` prove the annihilation half of the `(0,0)` gate — the
zero mode of every element of the full Dong–Jiang ideal `O_{0,0}(𝒱)` kills the bottom level of any
non-negatively levelled weak `𝒱`-module (`gateAnnihilationLev_holds`, `oLevW_OnmFull_zero_zero_vanish`).

This file supplies the **off-diagonal `(n,0)`** version, which the *universal property* of the
generalized-Verma module `M(U)` needs (DJ Thm 4.13's second half): for the induced map
`φ̄([v] ⊗ w) = o_{n,0}(v)·φ(w)` to be well defined against the ideal `O_{n,0}(𝒱)`, one needs

  `o_{n,0}(x)·φ(w) = 0` for every `x ∈ O_{n,0}(𝒱)` and every bottom vector `φ(w) ∈ Ω(P)`.

The generalization from `(0,0)` is direct, exactly as the repo already anticipated
(`ZhuVermaAnArchLU`:451-457): the inner associator `assocInner` is `n`-independent (already at
`m = 0`), so its proved bottom-vanishing (`oLevW_assocInner_vanish`) reuses verbatim; only the outer
composition index and the target level shift move `0 → n`, discharged by the **proved** DJ Lemma
4.1 (`djCompositionLev_holds`).  The `O'` summand `OnmW_annihilates_lev` was already general-`n`.

## Contents

* `oLevW_assocDefect_n0_vanish` — the `O''_{n,0}` (associator-defect) generators kill the bottom;
* `oLevW_levelMix_n0_vanish` — the `O'''_{n,0}` (level-mixing) generators kill the bottom;
* **`oLevW_OnmFull_n0_vanish`** — the full ideal `O_{n,0}(𝒱)`, given DJ Lemma 4.1;
* **`oLevW_OnmFull_n0_vanish_uncond`** — the same, unconditional (`djCompositionLev_holds`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free, `pbw`-free; no existing file
mutated.

## References
Dong–Jiang math/0601626 Lemma 4.1, Thm 4.13; DLM3 §4.  `ZhuVermaAnArchGate`
(`DJCompositionLev`, `OnmW_annihilates_lev`, `OnmW_annihilates_diag`, `oLevW_mem_level`, `levAnnW`),
`ZhuVermaAnArchGateB1Ann` (`djCompositionLev_holds`, `oLevW_assocInner_vanish`),
`ZhuVermaAnArchCollapseAssoc` (`assocInner`, `assocDefect_zero_eq`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {A : WeakModule W M}

/-- **The `O''_{n,0}` (associator-defect) generators annihilate the bottom** (given DJ Lemma 4.1).
`assocDefect W n 0 …` is the outer `u`-wrap of the `n`-independent inner associator `assocInner`,
whose bottom-vanishing is the proved `oLevW_assocInner_vanish`; one application of DJ Lemma 4.1 peels
the outer wrap. -/
theorem oLevW_assocDefect_n0_vanish (hdj : DJCompositionLev W) (L : AdmLev W A) (n p₁ p₂ p₃ : ℕ)
    (a b c u : 𝒱) {w : M} (hw : w ∈ L.lev 0) :
    oLevW A (((0 : ℕ) : ℤ) - (n : ℤ)) (assocDefect W n 0 p₁ p₂ p₃ a b c u) w = 0 := by
  have hw0 : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  rw [assocDefect_zero_eq, hdj A L n 0 p₃ u (assocInner W p₁ p₂ p₃ a b c) hw0,
    oLevW_assocInner_vanish L p₁ p₂ p₃ a b c hw, map_zero]

/-- **The `O'''_{n,0}` (level-mixing) generators annihilate the bottom** (given DJ Lemma 4.1).
Two applications of DJ Lemma 4.1 peel `levelMix W n 0 p a g v` to
`o_{n,p}(a)·o_{p,p}(g)·o_{p,0}(v)·w`, and the middle factor dies by the proven
`OnmW_annihilates_diag` (Dong–Jiang Theorem 4.3). -/
theorem oLevW_levelMix_n0_vanish (hdj : DJCompositionLev W) (L : AdmLev W A) (n p : ℕ) (a v g : 𝒱)
    (hg : g ∈ Onm W p p) {w : M} (hw : w ∈ L.lev 0) :
    oLevW A (((0 : ℕ) : ℤ) - (n : ℤ)) (levelMix W n 0 p a g v) w = 0 := by
  have hw0 : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  set y : M := oLevW A (((0 : ℕ) : ℤ) - (p : ℤ)) v w with hy
  have hyw : y ∈ L.lev (p : ℤ) := oLevW_mem_level L 0 p v hw0
  have e0 := hdj A L n 0 p (anmGen W n p p a g) v hw0
  have e1 := hdj A L n p p a g hyw
  have hmid : oLevW A ((p : ℤ) - (p : ℤ)) g y = 0 := OnmW_annihilates_diag L p hg hyw
  rw [levelMix, e0, ← hy, e1, hmid, map_zero]

/-- **The full `(n,0)` ideal-descent** (given DJ Lemma 4.1): the zero mode of every element of the
full Dong–Jiang ideal `O_{n,0}(𝒱)` — circle and shifted-grading generators (`O'`), associator defects
(`O''`), and level-mixing generators (`O'''`) — annihilates the bottom level `M(0)` of every
non-negatively levelled weak `𝒱`-module.  The `O'` summand is the proven `OnmW_annihilates_lev`. -/
theorem oLevW_OnmFull_n0_vanish (hdj : DJCompositionLev W) (L : AdmLev W A) (n : ℕ) {x : 𝒱}
    (hx : x ∈ OnmFull W n 0) {w : M} (hw : w ∈ L.lev 0) :
    oLevW A (((0 : ℕ) : ℤ) - (n : ℤ)) x w = 0 := by
  have hw0 : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  have hle : OnmFull W n 0 ≤ levAnnW A (((0 : ℕ) : ℤ) - (n : ℤ)) w := by
    simp only [OnmFull, OnmAssoc, OnmLevel]
    refine sup_le (sup_le ?_ (Submodule.span_le.mpr ?_)) (Submodule.span_le.mpr ?_)
    · intro z hz'
      exact OnmW_annihilates_lev L n 0 hz' hw0
    · rintro z ⟨q₁, q₂, q₃, aa, bb, cc, uu, rfl⟩
      exact oLevW_assocDefect_n0_vanish hdj L n q₁ q₂ q₃ aa bb cc uu hw
    · rintro z ⟨q, aa, vv, gg, hgg, rfl⟩
      exact oLevW_levelMix_n0_vanish hdj L n q aa vv gg hgg hw
  exact hle hx

/-- **The full `(n,0)` ideal-descent, unconditional** (`djCompositionLev_holds`).  The precise
analytic input the universal property of `M(U)` needs against the ideal `O_{n,0}(𝒱)`. -/
theorem oLevW_OnmFull_n0_vanish_uncond (L : AdmLev W A) (n : ℕ) {x : 𝒱}
    (hx : x ∈ OnmFull W n 0) {w : M} (hw : w ∈ L.lev 0) :
    oLevW A (((0 : ℕ) : ℤ) - (n : ℤ)) x w = 0 :=
  oLevW_OnmFull_n0_vanish (djCompositionLev_holds W) L n hx hw

end

end VOA
