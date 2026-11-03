/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Goddard
import VOA.Core.SuperVertexAlgebra

/-!
# Goddard uniqueness, `ε`-generically

The engine of the reconstruction cascade, ported to the sign-twisted setting.  This is what
super skew-symmetry is proved through, exactly as `goddard_uniqueness` drives the bosonic
`Core.SkewSymmetry`.

## Why the port is nearly free

Read the bosonic proof and the sign never participates.  The whole argument is: the
difference field `A(z)Y(b,w)𝟙 - Y(a,z)Y(b,w)𝟙` equals a difference of two `applyVec`-bracket
distributions, is therefore killed by `(z-w)^{N₁+N₂}`, is lower-truncated in `w`, and hence
vanishes by the `𝒱((z))((w))` cancellation.

The one place the sign could have interfered is the rewriting step `hDeq`, and there it
**cancels**: both brackets carry the *same* `ε`, so the two `ε`-terms are
`ε · (Y b)_q (A_p 𝟙)` and `ε · (Y b)_q ((Y a)_p 𝟙)`, which the creation hypothesis
`A_p 𝟙 = (Y a)_p 𝟙` identifies. This is why `goddard_pointwiseε` can take `ε` as a bare
scalar with no parity hypotheses at all.

## Main results

* `goddard_pointwiseε` — the sign-agnostic core: `A` and `Y(a,·)` agree on any `b` for which
  both are `ε`-local against `Y(b,·)`, for *any* scalar `ε`.
* `goddard_uniquenessε` — the super statement: parity-homogeneous locality with the Koszul
  signs determines the field, the inhomogeneous case following by splitting `b` into its
  even and odd parts.

## References
* Gannon §5.1.2–5.1.3; Kac, *VA for Beginners* §4.4; Frenkel–Ben-Zvi §3.1.
-/

namespace VOA

open Module (End)

universe u

namespace SuperVertexAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The parity grading of a super vertex algebra, bundled. -/
def toParityGrading (V : SuperVertexAlgebra 𝒱) : ParityGrading 𝒱 :=
  ⟨V.parity, V.parity_isInternal⟩

@[simp] theorem toParityGrading_parity (V : SuperVertexAlgebra 𝒱) :
    V.toParityGrading.parity = V.parity := rfl

/-! ## The vacuum expansion -/

/-- `Y(b,w)𝟙` has no negative powers of `w` (creation, VA3). -/
theorem Y_apply_vacuum_eq_zero (V : SuperVertexAlgebra 𝒱) (b : 𝒱) {n : ℤ} (hn : n < 0) :
    (V.Y b) n V.vacuum = 0 := by
  have h : (V.Y b) n V.vacuum = V.smul b (-n - 1) V.vacuum := by
    rw [smul_def, mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring]
  rw [h]
  exact V.smul_vacuum_eq_zero b (by omega)

/-- `Y(b,w)𝟙` has constant term `b`: `(Y b)₀ 𝟙 = b` (creation, VA3). -/
theorem Y_apply_vacuum_zero (V : SuperVertexAlgebra 𝒱) (b : 𝒱) : (V.Y b) 0 V.vacuum = b := by
  have h : (V.Y b) 0 V.vacuum = V.smul b (-1) V.vacuum := by
    rw [smul_def, mode_apply]; norm_num
  rw [h, smul_neg_one_vacuum]

/-! ## The `ε`-generic uniqueness theorem -/

/-- The difference field of the Goddard argument. -/
private def gDiff (V : SuperVertexAlgebra 𝒱) (A : FormalDist (End ℂ 𝒱)) (a b : 𝒱) :
    FormalDist₂ 𝒱 := fun p q => A p ((V.Y b) q V.vacuum) - (V.Y a) p ((V.Y b) q V.vacuum)

@[simp] private theorem gDiff_apply (V : SuperVertexAlgebra 𝒱) (A : FormalDist (End ℂ 𝒱))
    (a b : 𝒱) (p q : ℤ) :
    gDiff V A a b p q = A p ((V.Y b) q V.vacuum) - (V.Y a) p ((V.Y b) q V.vacuum) := rfl

/-- **Goddard uniqueness, sign-agnostic core.**  If `A` and `Y(a,·)` are `ε`-local against
`Y(b,·)` *for the same scalar `ε`*, and `A` creates the same vacuum tower as `Y(a,·)`, then
they agree on `b`.

No parity hypothesis appears: `ε` is an arbitrary complex scalar.  The bosonic case is
`ε = 1`, the super case `ε = (-1)^{|a||b|}`. -/
theorem goddard_pointwiseε (V : SuperVertexAlgebra 𝒱) (A : FormalDist (End ℂ 𝒱)) (a : 𝒱)
    (ε : ℂ) (b : 𝒱) (hAloc : Localε ε A (V.Y b)) (hVloc : Localε ε (V.Y a) (V.Y b))
    (hAvac : ∀ m : ℤ, A m V.vacuum = (V.Y a) m V.vacuum) (m : ℤ) :
    A m b = (V.Y a) m b := by
  obtain ⟨N₁, hN₁⟩ := hAloc
  obtain ⟨N₂, hN₂⟩ := hVloc
  -- the difference field is a difference of two `applyVec`-bracket distributions
  have hDeq : gDiff V A a b = applyVec V.vacuum (bracketDistε ε A (V.Y b))
      - applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b)) := by
    ext p q
    have hsub : (applyVec V.vacuum (bracketDistε ε A (V.Y b))
        - applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b))) p q
        = applyVec V.vacuum (bracketDistε ε A (V.Y b)) p q
          - applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b)) p q := rfl
    rw [hsub]
    simp only [gDiff_apply, applyVec_apply, bracketDistε_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.mul_apply]
    rw [hAvac p]
    abel
  -- it is annihilated by `(z-w)^{N₁+N₂}`
  have hkill : mulBySubPow (N₁ + N₂) (gDiff V A a b) = 0 := by
    rw [hDeq, map_sub]
    have e1 : mulBySubPow (N₁ + N₂) (applyVec V.vacuum (bracketDistε ε A (V.Y b))) = 0 :=
      mulBySubPow_eq_zero_mono (Nat.le_add_right N₁ N₂)
        (by rw [← applyVec_mulBySubPow, hN₁, applyVec_zero])
    have e2 : mulBySubPow (N₁ + N₂)
        (applyVec V.vacuum (bracketDistε ε (V.Y a) (V.Y b))) = 0 :=
      mulBySubPow_eq_zero_mono (Nat.le_add_left N₂ N₁)
        (by rw [← applyVec_mulBySubPow, hN₂, applyVec_zero])
    rw [e1, e2, sub_zero]
  -- it is lower-truncated in `w`
  have hbb : IsBddBelow₂ (gDiff V A a b) := by
    refine ⟨0, fun p q hq => ?_⟩
    rw [gDiff_apply, V.Y_apply_vacuum_eq_zero b hq, map_zero, map_zero, sub_zero]
  have hD0 : gDiff V A a b = 0 :=
    eq_zero_of_mulBySubPow_of_bddBelow (N₁ + N₂) _ hkill hbb
  have hfin : gDiff V A a b m 0 = 0 := congrFun (congrFun hD0 m) 0
  rw [gDiff_apply, V.Y_apply_vacuum_zero b, sub_eq_zero] at hfin
  exact hfin

/-- **Goddard uniqueness for a super vertex algebra.**  A field that is Koszul-locally
compatible with every parity-homogeneous `Y(b,·)`, and creates the same vacuum tower as
`Y(a,·)`, *is* `Y(a,·)`.

The inhomogeneous case is not a hypothesis: it follows by splitting `b` into even and odd
parts, since the conclusion is linear in `b` even though locality is not. -/
theorem goddard_uniquenessε (V : SuperVertexAlgebra 𝒱) (A : FormalDist (End ℂ 𝒱)) (a : 𝒱)
    {p : ZMod 2} (_ha : a ∈ V.parity p)
    (hAloc : ∀ (q : ZMod 2) (b : 𝒱), b ∈ V.parity q → Localε (koszul p q) A (V.Y b))
    (hAvac : ∀ m : ℤ, A m V.vacuum = (V.Y a) m V.vacuum) :
    A = V.Y a := by
  funext m
  refine LinearMap.ext fun b => ?_
  obtain ⟨b₀, hb₀, b₁, hb₁, rfl⟩ := V.toParityGrading.exists_parity_decomp b
  have h0 : A m b₀ = (V.Y a) m b₀ :=
    goddard_pointwiseε V A a (koszul p 0) b₀ (hAloc 0 b₀ hb₀)
      (V.locality a _ha b₀ hb₀) hAvac m
  have h1 : A m b₁ = (V.Y a) m b₁ :=
    goddard_pointwiseε V A a (koszul p 1) b₁ (hAloc 1 b₁ hb₁)
      (V.locality a _ha b₁ hb₁) hAvac m
  rw [map_add, map_add, h0, h1]

end SuperVertexAlgebra

end VOA
