import VOA.Classification.COne.OrbC2cSpan
import VOA.Classification.COne.OrbC2cCharged

/-! # Exact geometric and mode-decomposition residuals

The Props marked OPEN are not theorems. Their implications are proved.
The mode residual is the actual weight-20/22 decomposition in Dong--Jiang
1209.1168v2, Lemmas 4.3--4.4, with all discarded Virasoro descendants
explicitly constrained. The octahedral moving-pair input is retained.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2c
open VOA VertexOperatorAlgebra OrbC2b
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- A descendant with any factor other than L(-2) vanishes intrinsically. -/
theorem mk₂_virWord_eq_zero_of_bad (W : VertexOperatorAlgebra V) (x : V)
    (ks : List ℕ) (h : ∃ k ∈ ks, k ≠ 1) : mk₂ W (virWord W ks x) = 0 := by
  induction ks with
  | nil => simp at h
  | cons k ks ih =>
    by_cases hk : k = 1
    · subst k
      have ht : ∃ j ∈ ks, j ≠ 1 := by simpa using h
      change mk₂ W (W.L (-2) (virWord W ks x)) = 0
      rw [← exceptionalConformalEnd_mk, ih ht, map_zero]
    · cases k with
      | zero => exact (mk₂_eq_zero_iff W).mpr (L_neg_one_mem_O₂ W _)
      | succ k =>
        exact (mk₂_eq_zero_iff W).mpr
          (smul_le_neg_two_mem_O₂ W _ _ (by omega))

/-- The span of the discarded Virasoro descendants of a specified state. -/
def virError (W : VertexOperatorAlgebra V) (x : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (fun p : {ks : List ℕ // ∃ k ∈ ks, k ≠ 1} =>
    virWord W p.val x))

theorem virError_le_c2 (W : VertexOperatorAlgebra V) (x : V) : virError W x ≤ O₂ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨ks, hks⟩, rfl⟩
  exact (mk₂_eq_zero_iff W).mp (mk₂_virWord_eq_zero_of_bad W x ks hks)

/-- OPEN: conjugacy in the actual automorphism group, stronger than an
abstract group equivalence. FiniteRotationGroups does not prove this. -/
def TetrahedralConjugacy : Prop :=
  ∀ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* alternatingGroup (Fin 4)) →
    ∃ g : Aut (V2m 1 le_rfl), G.map (MulAut.conj g).toMonoidHom = tetra

/-- OPEN: the analogous actual octahedral conjugacy. -/
def OctahedralConjugacy : Prop :=
  ∀ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* Equiv.Perm (Fin 4)) →
    ∃ g : Aut (V2m 1 le_rfl), G.map (MulAut.conj g).toMonoidHom = octa

theorem tetrahedralStandardForm_of_conjugacy (h : TetrahedralConjugacy) :
    TetrahedralStandardForm := by
  intro G hG
  obtain ⟨g,hg⟩ := h G hG
  rw [← hg]
  exact orbifold_conj_iso g G

theorem octahedralStandardForm_of_conjugacy (h : OctahedralConjugacy) :
    OctahedralStandardForm := by
  intro G hG
  obtain ⟨g,hg⟩ := h G hG
  rw [← hg]
  exact orbifold_conj_iso g G

/-- OPEN actual-state identities. The remainders must lie in the span of
specified Virasoro descendants, not merely in the ambient lattice C₂ space.
The nonzero weight-nine state is required explicitly. -/
def TetrahedralModeDecomposition : Prop :=
  ∃ (U X : (orbifold tetra).carrier) (t : ℂ),
    U ≠ 0 ∧ U ∈ (orbifoldVOA tetra).grading 9 ∧
    X ∈ (orbifoldVOA tetra).grading 16 ∧
    let W := orbifoldVOA tetra
    let R := virError W W.vacuum ⊔ virError W X
    W.smul U (-3) U -
      ((2 ^ 10 * ((djC20 : ℂ) - (djB20 : ℂ) / 4 * t)) •
        ((W.L (-2) ^ 10) W.vacuum) + (djB20 : ℂ) • ((W.L (-2) ^ 2) X)) ∈ R ∧
    W.smul U (-5) U -
      ((2 ^ 11 * ((djC22 : ℂ) - (djB22 : ℂ) / 8 * t)) •
        ((W.L (-2) ^ 11) W.vacuum) + (djB22 : ℂ) • ((W.L (-2) ^ 3) X)) ∈ R

/-- Certified actual-state decompositions suffice for `TetrahedralDongJiangRelations`. -/
theorem tetrahedralDongJiangRelations_of_modeDecomposition
    (h : TetrahedralModeDecomposition) : TetrahedralDongJiangRelations := by
  obtain ⟨U,X,t,_,_,hX,h20,h22⟩ := h
  refine ⟨X,t,hX,?_,?_⟩
  all_goals
    have hR : virError (orbifoldVOA tetra) (orbifoldVOA tetra).vacuum ⊔
        virError (orbifoldVOA tetra) X ≤ O₂ (orbifoldVOA tetra) :=
      sup_le (virError_le_c2 _ _) (virError_le_c2 _ _)
  · have he := (mk₂_eq_zero_iff (orbifoldVOA tetra)).mpr (hR h20)
    rw [map_sub, map_add, map_smul, map_smul,
      (mk₂_eq_zero_iff _).mpr (smul_le_neg_two_mem_O₂ _ U U (by norm_num)),
      zero_sub, neg_eq_zero] at he
    simpa only [exceptionalConformalEnd_pow_mk] using he
  · have he := (mk₂_eq_zero_iff (orbifoldVOA tetra)).mpr (hR h22)
    rw [map_sub, map_add, map_smul, map_smul,
      (mk₂_eq_zero_iff _).mpr (smul_le_neg_two_mem_O₂ _ U U (by norm_num)),
      zero_sub, neg_eq_zero] at he
    simpa only [exceptionalConformalEnd_pow_mk] using he

/-- The concrete tetrahedral conclusion with the state-level residuals visible. -/
theorem tetra_c2Cofinite_of_state_inputs (hs : TetrahedralVirasoroSpan)
    (hr : TetrahedralModeDecomposition) : C2Cofinite (orbifoldVOA tetra) :=
  tetra_c2Cofinite_of_dongJiang (tetrahedralConformalSpan_of_virasoroSpan hs)
    (tetrahedralDongJiangRelations_of_modeDecomposition hr)

/-- B2 conditional on the exact geometric/state residuals and the still-open
involution moving-pair bound. No octahedral descent is inferred from inclusion. -/
theorem solvableExceptionalOrbifoldC2Fact_of_state_inputs
    (hA : TetrahedralConjugacy) (hS : OctahedralConjugacy)
    (hs : TetrahedralVirasoroSpan) (hr : TetrahedralModeDecomposition)
    (hI : InvolutionMovingPairSpan) : SolvableExceptionalOrbifoldC2Fact :=
  solvableExceptionalOrbifoldC2Fact_of_tower
    (tetrahedralStandardForm_of_conjugacy hA) (octahedralStandardForm_of_conjugacy hS)
    (cubicMovingPairSpan_iff_tetra_c2.mpr (tetra_c2Cofinite_of_state_inputs hs hr)) hI

end VOA.Classification.COne.OrbC2c
