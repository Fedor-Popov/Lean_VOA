/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchUnivMap
import VOA.Modules.ZhuVermaAnArchDJAction

/-!
# DJ Theorem 4.13 (second half): the induced map `φ̄ : M(U) → M` is a weak-module map.

`ZhuVermaAnArchUnivMap` built the induced `ℂ`-linear map `φ̄ = oLevUnivMap A L U φ … : M(U) → M`
for an `A(𝒱)`-equivariant bottom embedding `φ : U → Ω(M)`, well-defined against both the ideal
`O_{n,0}(𝒱)` and the `⊗_{A(𝒱)}`-balancing.  This file proves φ̄ **intertwines the `𝒱`-action** — DJ
Thm 4.13's computation (`refs/dj.txt`:1707-1719), ported line by line:

  `φ̄(uₚ(v ⊗ w)) = φ̄((u ∗^{wtu-p-1+n}_{0,n} v) ⊗ w) = o_{N,0}(u ∗^N_{0,n} v)·φ(w)`
  `= o_{N,n}(u)·o_{n,0}(v)·φ(w) = o_{N,n}(u)·φ̄(v ⊗ w) = uₚ·φ̄(v ⊗ w)`,   `N = wt u − p − 1 + n`,

using DJ Lemma 4.1 (`oLevW_anmGen_law_lev`) and the mode identity `o_{N,n}(u) = uₚ` on level `n`
(`oLevW A (n − N) u = A.act u p`, since `n − N = p − wt u + 1`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free, `pbw`-free; no existing file
mutated.

## References
Dong–Jiang math/0601626 Thm 4.13, Lemma 4.1; DLM3 §4.  `ZhuVermaAnArchUnivMap`
(`oLevUnivMap`, `oLevPieceMap`, `oLevUnivMap_incl`), `ZhuVermaAnArchDJAction`
(`djModeZero`, `djMode_apply_tmul`, `djMode_incl_eq_zero`, `djActionDescent_zero`, `muTargetLevel`),
`ZhuVermaAnArchGate` (`oLevW_homogeneous`, `modeW_vanish_of_lev`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {A : WeakModule W M}

/-- **DJ Thm 4.13 intertwining, on an elementary generator with homogeneous `a`.**
`φ̄(aₚ·([v] ⊗ w)) = aₚ·φ̄([v] ⊗ w)` at every level `n`, for `a ∈ 𝒱ₖ`.  The DJ target level
`N = wt a − p − 1 + n` (`muTargetLevel`); above it (`N ≥ 0`) both the DJ action and DJ Lemma 4.1 fire;
below it (`N < 0`) both sides vanish (`aₚ` lands in a negative level). -/
theorem oLevUnivMap_intertwine_tmul (L : AdmLev W A) (U : AmMod W 0) (φ : U.carrier →ₗ[ℂ] M)
    (hφlev : ∀ u, φ u ∈ L.lev 0)
    (hφact : ∀ (a : 𝒱) (u : U.carrier), φ (U.ρ (mkAnFull W 0 a) u) = oLevW A (0 : ℤ) a (φ u))
    (k p : ℤ) {a : 𝒱} (ha : a ∈ W.grading k) (n : ℕ) (v : 𝒱) (w : U.carrier) :
    oLevUnivMap A L U φ hφlev hφact
        (djModeZero W U p a (DJCarrier.incl W U n (mkDJPiece W U n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w))))
      = A.act a p (oLevUnivMap A L U φ hφlev hφact
          (DJCarrier.incl W U n (mkDJPiece W U n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w)))) := by
  have hw0 : φ w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hφlev w
  -- `φ̄` on the level-`n` generator.
  have hphi : oLevUnivMap A L U φ hφlev hφact
      (DJCarrier.incl W U n (mkDJPiece W U n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w)))
      = oLevW A (((0 : ℕ) : ℤ) - (n : ℤ)) v (φ w) := by
    rw [oLevUnivMap_incl, oLevPieceMap_mk]
  by_cases hN : 0 ≤ muTargetLevel k p n
  · obtain ⟨N, hNeq⟩ : ∃ N : ℕ, muTargetLevel k p n = (N : ℤ) :=
      ⟨(muTargetLevel k p n).toNat, (Int.toNat_of_nonneg hN).symm⟩
    rw [djModeZero, djMode_apply_tmul U (djActionDescent_zero W) p ha hNeq,
      oLevUnivMap_incl, oLevPieceMap_mk, hphi,
      oLevW_anmGen_law_lev L N 0 n a v hw0, WeakModule.act_def,
      oLevW_homogeneous A ((n : ℤ) - (N : ℤ)) ha]
    -- mode indices agree: `k − 1 + (n − N) = p`, since `N = k − p − 1 + n`.
    have hidx : k - 1 + ((n : ℤ) - (N : ℤ)) = p := by
      have : (N : ℤ) = muTargetLevel k p n := hNeq.symm
      simp only [muTargetLevel] at this; omega
    rw [hidx]
  · -- `N < 0`: `aₚ` lands below level 0, so both sides vanish.
    have hp : k + (n : ℤ) ≤ p := by simp only [muTargetLevel] at hN; omega
    rw [djModeZero, djMode_incl_eq_zero U (djActionDescent_zero W) ha hp, map_zero, hphi,
      WeakModule.act_def]
    refine (modeW_vanish_of_lev L ha ?_ hp).symm
    exact oLevW_mem_level L 0 n v hw0

/-- **DJ Thm 4.13 intertwining, homogeneous `a`, all `x`.**  Extends `oLevUnivMap_intertwine_tmul`
over the direct sum and the balanced tensor (`DirectSum.linearMap_ext` + `djPiece_ext`). -/
theorem oLevUnivMap_intertwine_homog (L : AdmLev W A) (U : AmMod W 0) (φ : U.carrier →ₗ[ℂ] M)
    (hφlev : ∀ u, φ u ∈ L.lev 0)
    (hφact : ∀ (a : 𝒱) (u : U.carrier), φ (U.ρ (mkAnFull W 0 a) u) = oLevW A (0 : ℤ) a (φ u))
    (k p : ℤ) {a : 𝒱} (ha : a ∈ W.grading k) (x : DJCarrier W U) :
    oLevUnivMap A L U φ hφlev hφact (djModeZero W U p a x)
      = A.act a p (oLevUnivMap A L U φ hφlev hφact x) := by
  have hcomp : (oLevUnivMap A L U φ hφlev hφact).comp (djModeZero W U p a)
      = (mode (A.YM a) p).comp (oLevUnivMap A L U φ hφlev hφact) := by
    refine DirectSum.linearMap_ext ℂ (fun n => ?_)
    refine djPiece_ext (fun v w => ?_)
    simp only [LinearMap.comp_apply]
    have hkey := oLevUnivMap_intertwine_tmul L U φ hφlev hφact k p ha n v w
    rwa [WeakModule.act_def] at hkey
  have := LinearMap.congr_fun hcomp x
  rwa [LinearMap.comp_apply, LinearMap.comp_apply, ← WeakModule.act_def] at this

/-- **DJ Thm 4.13 — the induced map `φ̄` is a weak-module map.**  `φ̄(aₚ·x) = aₚ·φ̄(x)` for every
`a : 𝒱`, `p : ℤ`, `x : M(U)`.  Extends the homogeneous case over the grade decomposition of `a`. -/
theorem oLevUnivMap_intertwine (L : AdmLev W A) (U : AmMod W 0) (φ : U.carrier →ₗ[ℂ] M)
    (hφlev : ∀ u, φ u ∈ L.lev 0)
    (hφact : ∀ (a : 𝒱) (u : U.carrier), φ (U.ρ (mkAnFull W 0 a) u) = oLevW A (0 : ℤ) a (φ u))
    (p : ℤ) (a : 𝒱) (x : DJCarrier W U) :
    oLevUnivMap A L U φ hφlev hφact (djModeZero W U p a x)
      = A.act a p (oLevUnivMap A L U φ hφlev hφact x) := by
  refine reduce_homogeneous W
    (P := fun a => oLevUnivMap A L U φ hφlev hφact (djModeZero W U p a x)
      = A.act a p (oLevUnivMap A L U φ hφlev hφact x)) ?_ ?_ ?_ a
  · intro k a ha
    exact oLevUnivMap_intertwine_homog L U φ hφlev hφact k p ha x
  · change oLevUnivMap A L U φ hφlev hφact (djModeZero W U p (0 : 𝒱) x)
      = A.act (0 : 𝒱) p (oLevUnivMap A L U φ hφlev hφact x)
    have h0 : djModeZero W U p (0 : 𝒱) = 0 := by
      have := djMode_smul_acting U (djActionDescent_zero W) p (0 : ℂ) W.vacuum
      rwa [zero_smul, zero_smul] at this
    have h1 : A.act (0 : 𝒱) p (oLevUnivMap A L U φ hφlev hφact x) = 0 := by
      have hadd := WeakModule.act_add_left A 0 0 p (oLevUnivMap A L U φ hφlev hφact x)
      rw [add_zero] at hadd
      have hz : (0 : M) + A.act (0 : 𝒱) p (oLevUnivMap A L U φ hφlev hφact x)
          = A.act (0 : 𝒱) p (oLevUnivMap A L U φ hφlev hφact x)
            + A.act (0 : 𝒱) p (oLevUnivMap A L U φ hφlev hφact x) := by rw [zero_add]; exact hadd
      exact (add_right_cancel hz).symm
    rw [h0, LinearMap.zero_apply, map_zero, h1]
  · intro b c hb hc
    change oLevUnivMap A L U φ hφlev hφact (djModeZero W U p (b + c) x)
      = A.act (b + c) p (oLevUnivMap A L U φ hφlev hφact x)
    rw [show djModeZero W U p (b + c) = djModeZero W U p b + djModeZero W U p c from
        djMode_add_acting U (djActionDescent_zero W) p b c, LinearMap.add_apply, map_add, hb, hc,
      WeakModule.act_add_left]

end

end VOA
