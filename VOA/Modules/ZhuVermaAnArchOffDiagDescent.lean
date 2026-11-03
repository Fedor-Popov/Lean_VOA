/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGateB1Ann

/-!
# The off-diagonal `(n,m)` ideal-descent: `o_{n,m}(O_{n,m}(𝒱))` annihilates level `m`.

`ZhuVermaAnArchGate`/`ZhuVermaAnArchGateB1Ann` prove the annihilation half of the `(0,0)` gate — the
zero mode of every element of the full Dong–Jiang ideal `O_{0,0}(𝒱)` kills the bottom level of any
non-negatively levelled weak `𝒱`-module.  This file supplies the **general off-diagonal `(n,m)`**
version, index-generalising the `(0,0)` proofs (`oLevW_assocDefect_vanish`/`oLevW_levelMix_vanish`),
which `ZhuVermaAnArchLU`:452-457 flagged as "NOT ESTABLISHED, not attempted".

The `(n,0)` instance `oLevW_OnmFull_n_zero_vanish` is exactly what the *universal property* of the
generalized-Verma module `M(U)` needs (DJ Thm 4.13's second half): for the induced map
`φ̄([v] ⊗ u) = o_{n,0}(v)·(emb u)` to be well defined against the ideal `O_{n,0}(𝒱)`, one needs
`o_{n,0}(x)·(emb u) = 0` for every `x ∈ O_{n,0}(𝒱)` and every bottom vector `emb u ∈ Ω(P)`.

All three ideal summands descend via the **proved** DJ Lemma 4.1 (`djCompositionLev_holds`): the `O'`
summand by `OnmW_annihilates_lev` (already general-`(n,m)`), the `O''` associator defect by four
applications of DJ Lemma 4.1, and the `O'''` level-mixing generator by two applications plus the
proven `OnmW_annihilates_diag` (DJ Thm 4.3).  Everything unconditional.

⚠ Elaboration note: `have hdj := djCompositionLev_holds W` gets stuck on `Module ℂ ?m`; write the
explicit `have hdj : DJCompositionLev W := djCompositionLev_holds W`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free, `pbw`-free; no existing file
mutated.

## References
Dong–Jiang math/0601626 Lemma 4.1, Thm 4.13; DLM3 §4.  `ZhuVermaAnArchGate`
(`DJCompositionLev`, `OnmW_annihilates_lev`, `OnmW_annihilates_diag`, `oLevW_mem_level`, `levAnnW`,
`oLevW_assocDefect_vanish`, `oLevW_levelMix_vanish`), `ZhuVermaAnArchGateB1Ann`
(`djCompositionLev_holds`).
-/

namespace VOA

open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {A : WeakModule W M}

/-- **The `(n,m)` associator-defect annihilation** — the index generalisation of
`oLevW_assocDefect_vanish`.  Four applications of DJ Lemma 4.1 rewrite both halves of the inner
associator as the same triple composite. -/
theorem oLevW_assocDefect_vanish_nm (hdj : DJCompositionLev W) (L : AdmLev W A)
    (n m : ℕ) (p₁ p₂ p₃ : ℕ) (a b c u : 𝒱) {w : M} (hw : w ∈ L.lev (m : ℤ)) :
    oLevW A ((m : ℤ) - (n : ℤ)) (assocDefect W n m p₁ p₂ p₃ a b c u) w = 0 := by
  set y : M := oLevW A ((m : ℤ) - (p₁ : ℤ)) c w with hy
  have hyw : y ∈ L.lev (p₁ : ℤ) := oLevW_mem_level L m p₁ c hw
  have e1 := hdj A L p₃ m p₁ (anmGen W p₃ p₁ p₂ a b) c hw
  have e2 := hdj A L p₃ p₁ p₂ a b hyw
  have e3 := hdj A L p₃ m p₂ a (anmGen W p₂ m p₁ b c) hw
  have e4 := hdj A L p₂ m p₁ b c hw
  have hX : oLevW A ((m : ℤ) - (p₃ : ℤ))
      (anmGen W p₃ m p₁ (anmGen W p₃ p₁ p₂ a b) c
        - anmGen W p₃ m p₂ a (anmGen W p₂ m p₁ b c)) w = 0 := by
    rw [map_sub, LinearMap.sub_apply, e1, e3, e2, e4, ← hy, sub_self]
  have e0 := hdj A L n m p₃ u
      (anmGen W p₃ m p₁ (anmGen W p₃ p₁ p₂ a b) c
        - anmGen W p₃ m p₂ a (anmGen W p₂ m p₁ b c)) hw
  rw [assocDefect, e0, hX, map_zero]

/-- **The `(n,m)` level-mixing annihilation** — the index generalisation of `oLevW_levelMix_vanish`.
Two applications of DJ Lemma 4.1 peel the generator to `o_{n,p}(a)·o_{p,p}(g)·o_{p,m}(v)·w`, and the
middle factor dies by the proven `OnmW_annihilates_diag`. -/
theorem oLevW_levelMix_vanish_nm (hdj : DJCompositionLev W) (L : AdmLev W A)
    (n m : ℕ) (p : ℕ) (a v g : 𝒱) (hg : g ∈ Onm W p p) {w : M} (hw : w ∈ L.lev (m : ℤ)) :
    oLevW A ((m : ℤ) - (n : ℤ)) (levelMix W n m p a g v) w = 0 := by
  set y : M := oLevW A ((m : ℤ) - (p : ℤ)) v w with hy
  have hyw : y ∈ L.lev (p : ℤ) := oLevW_mem_level L m p v hw
  have e0 := hdj A L n m p (anmGen W n p p a g) v hw
  have e1 := hdj A L n p p a g hyw
  have hmid : oLevW A ((p : ℤ) - (p : ℤ)) g y = 0 := OnmW_annihilates_diag L p hg hyw
  rw [levelMix, e0, ← hy, e1, hmid, map_zero]

/-- **THE OFF-DIAGONAL DESCENT**: the full Dong–Jiang ideal `O_{n,m}(𝒱)` annihilates level `m`, at
every `(n,m)` — unconditional (`djCompositionLev_holds` is a theorem). -/
theorem oLevW_OnmFull_vanish_nm (L : AdmLev W A) (n m : ℕ) {x : 𝒱}
    (hx : x ∈ OnmFull W n m) {w : M} (hw : w ∈ L.lev (m : ℤ)) :
    oLevW A ((m : ℤ) - (n : ℤ)) x w = 0 := by
  have hdj : DJCompositionLev W := djCompositionLev_holds W
  have hle : OnmFull W n m ≤ levAnnW A ((m : ℤ) - (n : ℤ)) w := by
    simp only [OnmFull, OnmAssoc, OnmLevel]
    refine sup_le (sup_le ?_ (Submodule.span_le.mpr ?_)) (Submodule.span_le.mpr ?_)
    · intro z hz'
      exact OnmW_annihilates_lev L n m hz' hw
    · rintro z ⟨q₁, q₂, q₃, aa, bb, cc, uu, rfl⟩
      exact oLevW_assocDefect_vanish_nm hdj L n m q₁ q₂ q₃ aa bb cc uu hw
    · rintro z ⟨q, aa, vv, gg, hgg, rfl⟩
      exact oLevW_levelMix_vanish_nm hdj L n m q aa vv gg hgg hw
  exact hle hx

/-- **The `(n,0)` instance the universal property of `M(U)` needs** — the zero mode of every
`x ∈ O_{n,0}(𝒱)` annihilates the bottom level `M(0)`. -/
theorem oLevW_OnmFull_n_zero_vanish (L : AdmLev W A) (n : ℕ) {x : 𝒱}
    (hx : x ∈ OnmFull W n 0) {w : M} (hw : w ∈ L.lev 0) :
    oLevW A (-(n : ℤ)) x w = 0 := by
  have hw' : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  have := oLevW_OnmFull_vanish_nm L n 0 hx hw'
  simpa using this

end VOA
