/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbOctaSpan
import VOA.Classification.COne.OrbC2dExceptional
import VOA.Classification.COne.OrbC2bReduction
import VOA.Modularity.C2GradedVanishing

/-! # OrbOcta: the octahedral involution input reduced to nilpotence of `ω̄`

With the finite conformal towers of `V₂^{S₄}` (`octaConformalTowerSpan_holds`, proved), the
B2 involution input `OrbC2b.InvolutionMovingPairSpan` reduces to ONE named statement:

* `OctahedralConformalNilpotent`: the class `ω̄` of the conformal vector is nilpotent in
  `A₂(V₂^{S₄}) = V₂^{S₄}/C₂(V₂^{S₄})`.

`octahedralConformalNilpotent_iff_c2`: this Prop is EQUIVALENT to `C₂`-cofiniteness of
`V₂^{S₄}` (no loss in the reduction).

`involutionMovingPairSpan_of_octahedralConformalNilpotent`.

`solvableExceptionalOrbifoldC2Fact_of_octa`: B2 from the tetrahedral mode decomposition
and `OctahedralConformalNilpotent`.

`OctahedralConformalNilpotent` is OPEN. It is the octahedral analogue of the Dong--Jiang
weight-20/22 relations. The tetrahedral relations do not give it, and the first octahedral
relations live at weight `≥ 33`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbOcta
open VOA VertexOperatorAlgebra OrbC2b OrbC2c OrbC2d

/-- OPEN: `ω̄` is nilpotent in `A₂(V₂^{S₄})`. Equivalent to `C₂`-cofiniteness of `V₂^{S₄}`
(`octahedralConformalNilpotent_iff_c2`). -/
def OctahedralConformalNilpotent : Prop :=
  ∃ n : ℕ, (exceptionalConformalEnd (orbifoldVOA octa) ^ n)
    (mk₂ (orbifoldVOA octa) (orbifoldVOA octa).vacuum) = 0

theorem L_neg_two_pow_vacuum_mem {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (n : ℕ) :
    ((W.L (-2)) ^ n) W.vacuum ∈ W.grading (2 * (n : ℤ)) := by
  induction n with
  | zero => simpa using W.vacuum_mem
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := OrbSpan.L_mem_grading_aux W ih (-2)
    rwa [show 2 * (n : ℤ) - -2 = 2 * ((n + 1 : ℕ) : ℤ) by push_cast; ring] at h

/-- `C₂`-cofiniteness forces `ω̄` to be nilpotent (graded `O₂`, Buhl's Remark 3.5). -/
theorem conformal_nilpotent_of_c2 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (h : C2Cofinite W) :
    ∃ n : ℕ, (exceptionalConformalEnd W ^ n) (mk₂ W W.vacuum) = 0 := by
  obtain ⟨N, hN⟩ := exists_grading_le_O₂ W h
  refine ⟨N, ?_⟩
  rw [exceptionalConformalEnd_pow_mk, mk₂_eq_zero_iff]
  exact hN _ (by omega) (L_neg_two_pow_vacuum_mem W N)

/-- `C₂` for `V₂^{S₄}` from nilpotence of `ω̄` and the proved finite conformal towers. -/
theorem octa_c2Cofinite_of_nilpotent (h : OctahedralConformalNilpotent) :
    C2Cofinite (orbifoldVOA octa) := by
  obtain ⟨n, hn⟩ := h
  exact c2Cofinite_of_conformal_towers _ octaConformalTowerSpan_holds hn

/-- The reduction is lossless. -/
theorem octahedralConformalNilpotent_iff_c2 :
    OctahedralConformalNilpotent ↔ C2Cofinite (orbifoldVOA octa) :=
  ⟨octa_c2Cofinite_of_nilpotent, conformal_nilpotent_of_c2 _⟩

/-- `C₂` of the octahedral orbifold gives the involution moving-pair input (no cubic input
needed in this direction). -/
theorem involutionMovingPairSpan_of_octa_c2 (h : C2Cofinite (orbifoldVOA octa)) :
    InvolutionMovingPairSpan := by
  obtain ⟨e, he, _⟩ := octa_involution_iso
  exact OrbC2.movingPairSpanFinite_of_c2Cofinite _
    (ConverseUniverse.c2Cofinite_of_iso e he h)

/-- **The involution input from nilpotence of `ω̄` in `A₂(V₂^{S₄})`.** -/
theorem involutionMovingPairSpan_of_octahedralConformalNilpotent
    (h : OctahedralConformalNilpotent) : InvolutionMovingPairSpan :=
  involutionMovingPairSpan_of_octa_c2 (octa_c2Cofinite_of_nilpotent h)

/-- Given the cubic input, the involution input is EQUIVALENT to `OctahedralConformalNilpotent`. -/
theorem involutionMovingPairSpan_iff_octahedralConformalNilpotent (hC : CubicMovingPairSpan) :
    InvolutionMovingPairSpan ↔ OctahedralConformalNilpotent :=
  (involutionMovingPairSpan_iff_octa_c2 hC).trans octahedralConformalNilpotent_iff_c2.symm

/-- **B2 from the tetrahedral mode decomposition and `OctahedralConformalNilpotent`.** -/
theorem solvableExceptionalOrbifoldC2Fact_of_octa (hr : TetrahedralModeDecomposition)
    (hN : OctahedralConformalNilpotent) : SolvableExceptionalOrbifoldC2Fact :=
  solvableExceptionalOrbifoldC2Fact_of_three_inputs OrbPrim.tetrahedralVirasoroSpan_holds hr
    (involutionMovingPairSpan_of_octahedralConformalNilpotent hN)

/-! ## A sharper sufficient condition: two quadratic relations in weights `32` and `34`

In `A₂(V₂^{S₄})` the only seeds of weight `≤ 35` are `𝟙` and `X = T(I₄)` (weight 16), so the
weight-32 product `x̄² = [X₍₋₁₎X]` is automatically `a₁ ω̄¹⁶ + b₁ ω̄⁸ x̄` for some `a₁, b₁`, and the
`C₂`-element `X₍₋₃₎X` (weight 34) gives `a₂ ω̄¹⁷ + b₂ ω̄⁹ x̄ = 0`. If the 2×2 elimination
determinant is nonzero, `ω̄²⁵ = 0`. The coefficients are NOT computed here. -/

section Elimination
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

theorem conformal_pow_A₂mul (n : ℕ) (p q : A₂ W) :
    (exceptionalConformalEnd W ^ n) (A₂mul W p q) =
      A₂mul W ((exceptionalConformalEnd W ^ n) p) q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Module.End.mul_apply]
    exact (A₂mul_assoc W _ _ _).symm

/-- Generic elimination: two quadratic relations with nonzero determinant force
`ω̄^{3p+1} = 0`. -/
theorem conformal_nilpotent_of_quadratic (x : A₂ W) (p : ℕ) (a₁ b₁ a₂ b₂ : ℂ)
    (hdet : a₂ * (a₂ + b₂ * b₁) - b₂ * a₁ * b₂ ≠ 0)
    (h₁ : A₂mul W x x = a₁ • (exceptionalConformalEnd W ^ (2 * p)) (mk₂ W W.vacuum) +
      b₁ • (exceptionalConformalEnd W ^ p) x)
    (h₂ : a₂ • (exceptionalConformalEnd W ^ (2 * p + 1)) (mk₂ W W.vacuum) +
      b₂ • (exceptionalConformalEnd W ^ (p + 1)) x = 0) :
    (exceptionalConformalEnd W ^ (3 * p + 1)) (mk₂ W W.vacuum) = 0 := by
  set D := exceptionalConformalEnd W
  set v := mk₂ W W.vacuum
  have hpow (a b : ℕ) (y : A₂ W) : (D ^ a) ((D ^ b) y) = (D ^ (a + b)) y := by
    rw [← Module.End.mul_apply, ← pow_add]
  have hA : a₂ • (D ^ (3 * p + 1)) v + b₂ • (D ^ (2 * p + 1)) x = 0 := by
    have h := congrArg (D ^ p) h₂
    rw [map_add, map_smul, map_smul, hpow, hpow, map_zero] at h
    rwa [show p + (2 * p + 1) = 3 * p + 1 by ring, show p + (p + 1) = 2 * p + 1 by ring] at h
  have hB : (b₂ * a₁) • (D ^ (3 * p + 1)) v + (a₂ + b₂ * b₁) • (D ^ (2 * p + 1)) x = 0 := by
    have h := congrArg (fun y => A₂mul W y x) h₂
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_zero,
      LinearMap.zero_apply] at h
    rw [← OrbC2b.conformal_pow_mul_vacuum, ← conformal_pow_A₂mul, h₁, map_add, map_smul,
      map_smul, hpow, hpow] at h
    rw [show p + 1 + 2 * p = 3 * p + 1 by ring, show p + 1 + p = 2 * p + 1 by ring] at h
    rw [← h]
    module
  exact (exceptional_two_relations_vanish hdet hA hB).1

end Elimination

/-- `OctahedralConformalNilpotent` from the two quadratic relations of `x̄ = [T(I₄)]` in
weights `32` and `34` with nonzero elimination determinant (coefficients left existential). -/
def OctahedralQuadraticRelations : Prop :=
  ∃ a₁ b₁ a₂ b₂ : ℂ, a₂ * (a₂ + b₂ * b₁) - b₂ * a₁ * b₂ ≠ 0 ∧
    let W := orbifoldVOA octa
    let D := exceptionalConformalEnd W
    let v := mk₂ W W.vacuum
    let x := mk₂ W (Tav OrbPrim.I4)
    A₂mul W x x = a₁ • (D ^ 16) v + b₁ • (D ^ 8) x ∧
    a₂ • (D ^ 17) v + b₂ • (D ^ 9) x = 0

theorem octahedralConformalNilpotent_of_quadratic (h : OctahedralQuadraticRelations) :
    OctahedralConformalNilpotent := by
  obtain ⟨a₁, b₁, a₂, b₂, hdet, h₁, h₂⟩ := h
  exact ⟨25, conformal_nilpotent_of_quadratic (orbifoldVOA octa) _ 8 a₁ b₁ a₂ b₂ hdet h₁ h₂⟩

theorem involutionMovingPairSpan_of_quadratic (h : OctahedralQuadraticRelations) :
    InvolutionMovingPairSpan :=
  involutionMovingPairSpan_of_octahedralConformalNilpotent
    (octahedralConformalNilpotent_of_quadratic h)

end VOA.Classification.COne.OrbOcta
