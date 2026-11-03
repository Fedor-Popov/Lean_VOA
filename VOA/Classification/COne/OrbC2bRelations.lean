import VOA.Classification.COne.OrbC2bReduction

/-! # The algebraic end of Dong--Jiang's tetrahedral C₂ proof

Source: arXiv:1209.1168v2, Lemmas 4.2--4.4 and Theorem 4.6.
The numerical determinant is checked, including cancellation of the unknown
weight-sixteen coefficient. The VOA coefficient identities and the spanning
theorem are explicitly OPEN inputs; arithmetic is not a verification of them.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2b
open VOA VertexOperatorAlgebra

section General
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- Finitely many conformal towers span the intrinsic quotient. This is weaker
than C₂-cofiniteness: the towers have not yet been truncated. -/
def ConformalTowerSpan : Prop :=
  ∃ (k : ℕ) (v : Fin k → A₂ W),
    Submodule.span ℂ (Set.range (fun p : Fin k × ℕ =>
      (exceptionalConformalEnd W ^ p.2) (v p.1))) = ⊤

theorem conformal_pow_mul_vacuum (n : ℕ) (x : A₂ W) :
    (exceptionalConformalEnd W ^ n) x =
      A₂mul W ((exceptionalConformalEnd W ^ n) (mk₂ W W.vacuum)) x := by
  induction n with
  | zero => exact (A₂mul_one_left W x).symm
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Module.End.mul_apply]
    exact (A₂mul_assoc W _ _ _).symm

/-- A nilpotent conformal class kills every tower, not just the vacuum tower. -/
theorem conformal_pow_eq_zero {n : ℕ}
    (h : (exceptionalConformalEnd W ^ n) (mk₂ W W.vacuum) = 0) :
    exceptionalConformalEnd W ^ n = 0 := by
  apply LinearMap.ext
  intro x
  rw [conformal_pow_mul_vacuum W n x, h, map_zero]

/-- Finite generation over the conformal operator plus its nilpotence suffices. -/
theorem c2Cofinite_of_conformal_towers (hs : ConformalTowerSpan W) {n : ℕ}
    (hn : (exceptionalConformalEnd W ^ n) (mk₂ W W.vacuum) = 0) : C2Cofinite W := by
  obtain ⟨k, v, hv⟩ := hs
  let D := exceptionalConformalEnd W
  have hD : D ^ n = 0 := conformal_pow_eq_zero W hn
  let f : Fin k × Fin n → A₂ W := fun p => (D ^ p.2.val) (v p.1)
  have hf : Submodule.span ℂ (Set.range f) = ⊤ := by
    rw [← top_le_iff, ← hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    by_cases hj : j < n
    · exact Submodule.subset_span ⟨(i, ⟨j, hj⟩), rfl⟩
    · have hnj : n ≤ j := by omega
      obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hnj
      change (D ^ (n + l)) (v i) ∈ _
      rw [pow_add, hD, zero_mul, LinearMap.zero_apply]
      exact Submodule.zero_mem _
  exact ⟨hf ▸ Submodule.fg_span (Set.finite_range f)⟩

end General

/-- Published oscillator coefficients; their identification with VOA products is an input. -/
def djC20 : ℚ := -447232 / (19 * 17 * 11 * 7 ^ 2 * 5 ^ 2 * 3)
def djC22 : ℚ := -328099328 / (19 * 17 * 13 * 11 ^ 2 * 7 ^ 3 * 5 ^ 2 * 3 ^ 6)
def djB20 : ℚ := 14760 / 11
def djB22 : ℚ := 19408720 / (7007 * 27)

theorem dongJiang_determinant_ne_zero :
    (2 ^ 10 * djC20) * djB22 - (2 ^ 11 * djC22) * djB20 ≠ 0 := by
  norm_num [djC20, djC22, djB20, djB22]

/-- The unknown coefficient of the weight-sixteen primary cancels from the determinant. -/
theorem dongJiang_shifted_determinant (t : ℂ) :
    (2 ^ 10 * ((djC20 : ℂ) - (djB20 : ℂ) / 4 * t)) * (djB22 : ℂ) -
      (2 ^ 11 * ((djC22 : ℂ) - (djB22 : ℂ) / 8 * t)) * (djB20 : ℂ) ≠ 0 := by
  have he :
      (2 ^ 10 * ((djC20 : ℂ) - (djB20 : ℂ) / 4 * t)) * (djB22 : ℂ) -
      (2 ^ 11 * ((djC22 : ℂ) - (djB22 : ℂ) / 8 * t)) * (djB20 : ℂ) =
      (2 ^ 10 * (djC20 : ℂ)) * (djB22 : ℂ) -
        (2 ^ 11 * (djC22 : ℂ)) * (djB20 : ℂ) := by ring
  rw [he]
  exact_mod_cast dongJiang_determinant_ne_zero

section Elimination
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The two published relations force the vacuum's eleventh conformal power to vanish. -/
theorem dongJiang_elimination (D : Module.End ℂ M) (v x : M) (t : ℂ)
    (h20 : (2 ^ 10 * ((djC20 : ℂ) - (djB20 : ℂ) / 4 * t)) • ((D ^ 10) v) +
      (djB20 : ℂ) • ((D ^ 2) x) = 0)
    (h22 : (2 ^ 11 * ((djC22 : ℂ) - (djB22 : ℂ) / 8 * t)) • ((D ^ 11) v) +
      (djB22 : ℂ) • ((D ^ 3) x) = 0) :
    (D ^ 11) v = 0 ∧ (D ^ 3) x = 0 := by
  have h := congrArg D h20
  simp only [map_add, map_smul, map_zero] at h
  have hp (j : ℕ) (y : M) : D ((D ^ j) y) = (D ^ (j + 1)) y := by
    rw [pow_succ', Module.End.mul_apply]
  rw [hp, hp] at h
  exact exceptional_two_relations_vanish (dongJiang_shifted_determinant t) h h22

end Elimination

/-- OPEN VOA input: the two intrinsic quotient relations, with oscillator
normalization made explicit. True by Dong--Jiang Lemmas 4.3--4.4.
The extra parameter `t` is the coefficient of the weight-sixteen primary. -/
def TetrahedralDongJiangRelations : Prop :=
  ∃ (X : (orbifold tetra).carrier) (t : ℂ), X ∈ (orbifoldVOA tetra).grading 16 ∧
    let W := orbifoldVOA tetra
    let D := exceptionalConformalEnd W
    let v := mk₂ W W.vacuum
    let x := mk₂ W X
    (2 ^ 10 * ((djC20 : ℂ) - (djB20 : ℂ) / 4 * t)) • ((D ^ 10) v) +
      (djB20 : ℂ) • ((D ^ 2) x) = 0 ∧
    (2 ^ 11 * ((djC22 : ℂ) - (djB22 : ℂ) / 8 * t)) • ((D ^ 11) v) +
      (djB22 : ℂ) • ((D ^ 3) x) = 0

/-- OPEN spanning input, a consequence of Dong--Jiang Lemma 4.2 on the actual quotient. -/
def TetrahedralConformalSpan : Prop := ConformalTowerSpan (orbifoldVOA tetra)

theorem tetra_conformal_nilpotent_of_relations (hr : TetrahedralDongJiangRelations) :
    exceptionalConformalEnd (orbifoldVOA tetra) ^ 11 = 0 := by
  obtain ⟨X, t, _, h20, h22⟩ := hr
  exact conformal_pow_eq_zero _ (dongJiang_elimination _ _ _ t h20 h22).1

/-- Concrete A₄ C₂ theorem conditional on exactly the missing span and two mode relations. -/
theorem tetra_c2Cofinite_of_dongJiang (hs : TetrahedralConformalSpan)
    (hr : TetrahedralDongJiangRelations) : C2Cofinite (orbifoldVOA tetra) := by
  obtain ⟨X, t, _, h20, h22⟩ := hr
  exact c2Cofinite_of_conformal_towers _ hs (dongJiang_elimination _ _ _ t h20 h22).1

theorem tetrahedralMovingPairSpan_of_dongJiang (hF : TetrahedralStandardForm)
    (hs : TetrahedralConformalSpan) (hr : TetrahedralDongJiangRelations) :
    OrbC2.TetrahedralMovingPairSpan :=
  tetrahedralMovingPairSpan_of_cubic hF
    (cubicMovingPairSpan_iff_tetra_c2.mpr (tetra_c2Cofinite_of_dongJiang hs hr))

end VOA.Classification.COne.OrbC2b
