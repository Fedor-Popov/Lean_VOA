import VOA.Huang.LiFusionPairing

/-! # The exact bottom extension problem for Li's converse

`ScalarTopExtension` retains the unproved part of Li's construction: scalar
coefficients on the full input modules, extending the specified top datum and
satisfying weight support and Jacobi. It assumes neither vector-valued modes,
truncation nor the derivative axiom. The reconstruction implication and its
converse are proved, so this residual is not stronger than top-map surjectivity.

The intended existence theorem is for rational VOAs and irreducible
lowest-weight `P₂, P₃`. Source: Li, J. Algebra 212 (1999), Corollary 2.13;
Miyamoto, arXiv:math/0010180, Theorem 2.10. No assertion that semisimplicity
of `A(V)` alone implies the extension is made.
-/
namespace VOA.Huang.LiFusion
open VOA VOA.FZ FusionTop
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {P₂ P₃ : LWModule W}

/-- The scalar coefficients on bottom input at the top output index agree
with the given element of the actual library `fzSpace`. -/
def ExtendsTop (A : OrdVModule W M) (P₂ P₃ : LWModule W)
    (C : ScalarModes M P₂.carrier P₃.carrier) (T : fzSpace A P₂ P₃) : Prop :=
  ∀ (α : ℂ) (x : M), x ∈ A.weight α → ∀ (y : bot P₂) (f : Module.Dual ℂ P₃.carrier),
    C (α + P₂.h - P₃.h - 1) x y f = f (T.val x y)

/-- The remaining scalar extension problem. Its existence under rationality
is not established by the results in this file. -/
def ScalarTopExtension (A : OrdVModule W M) (P₂ P₃ : LWModule W) : Prop :=
  ∀ T : fzSpace A P₂ P₃, ∃ C : ScalarModes M P₂.carrier P₃.carrier,
    ScalarWeightCompatible A P₂.isMod P₃.isMod C ∧
      ScalarJacobi A P₂.isMod P₃.isMod C ∧ ExtendsTop A P₂ P₃ C T

theorem topMapFZ_recovered_eq {C : ScalarModes M P₂.carrier P₃.carrier}
    (hw : ScalarWeightCompatible A P₂.isMod P₃.isMod C)
    (hj : ScalarJacobi A P₂.isMod P₃.isMod C) (T : fzSpace A P₂ P₃)
    (ht : ExtendsTop A P₂ P₃ C T) :
    topMapFZ A P₂ P₃ ⟨recoveredModes hw, isIntertwiningOperator_recoveredModes hw hj⟩ = T := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  induction x using induction_weight A with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, hx, hx']
  | hhom α x hx =>
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change topComp A P₂ P₃ (recoveredModes hw) x y = (T.val x y : P₃.carrier)
    rw [topComp_of_mem _ hx]
    exact dual_ext fun f => (recoveredModes_pairing hw _ x y f).trans (ht α x hx y f)

/-- Li's scalar extension, when supplied, gives precisely surjectivity of
the existing `topMapFZ`, with no new definition of intertwiner. -/
theorem topMapFZ_surjective_of_scalarTopExtension
    (hext : ScalarTopExtension A P₂ P₃) : Function.Surjective (topMapFZ A P₂ P₃) := by
  intro T
  obtain ⟨C, hw, hj, ht⟩ := hext T
  exact ⟨⟨recoveredModes hw, isIntertwiningOperator_recoveredModes hw hj⟩,
    topMapFZ_recovered_eq hw hj T ht⟩

theorem scalarTopExtension_of_topMapFZ_surjective
    (hs : Function.Surjective (topMapFZ A P₂ P₃)) : ScalarTopExtension A P₂ P₃ := by
  intro T
  obtain ⟨Y, rfl⟩ := hs T
  refine ⟨scalarize Y.val, scalarize_weightCompatible Y.property,
    scalarize_jacobi Y.property, ?_⟩
  intro α x hx y f
  change f (Y.val (α + P₂.h - P₃.h - 1) x y) = f (topComp A P₂ P₃ Y.val x y)
  rw [topComp_of_mem _ hx]

/-- The scalar residual has exactly the strength of the missing converse;
this equivalence is not a proof of its rational-VOA instance. -/
theorem scalarTopExtension_iff_surjective :
    ScalarTopExtension A P₂ P₃ ↔ Function.Surjective (topMapFZ A P₂ P₃) :=
  ⟨topMapFZ_surjective_of_scalarTopExtension, scalarTopExtension_of_topMapFZ_surjective⟩

/-- Once existence is known, injectivity gives uniqueness of every lift. -/
theorem existsUnique_intertwiner_of_scalarTopExtension
    (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW)
    (hext : ScalarTopExtension A P₂ P₃) (T : fzSpace A P₂ P₃) :
    ∃! Y : IntertwiningOperator A P₂.isMod P₃.isMod, topMapFZ A P₂ P₃ Y = T := by
  obtain ⟨Y, hY⟩ := topMapFZ_surjective_of_scalarTopExtension hext T
  exact ⟨Y, hY, fun Z hZ => topMapFZ_injective h₂ h₃ (hZ.trans hY.symm)⟩

/-- The equality of fusion multiplicities, conditional only on the scalar
extension beyond the existing injective half. -/
theorem fusionRule_eq_finrank_fzSpace_of_scalarTopExtension
    (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW)
    (hext : ScalarTopExtension A P₂ P₃) :
    fusionRule A P₂.isMod P₃.isMod = Module.finrank ℂ (fzSpace A P₂ P₃) :=
  (LinearEquiv.ofBijective (topMapFZ A P₂ P₃)
    ⟨topMapFZ_injective h₂ h₃, topMapFZ_surjective_of_scalarTopExtension hext⟩).finrank_eq

/-- The `L(-1)` bottom relation is already forced by the conformal left and
right Zhu actions. It is not an extra condition on the datum being lifted. -/
theorem fzSpace_translation (T : fzSpace A P₂ P₃) (x : M) :
    T.val (A.Lm1 x + mode (A.YM W.conformalVector) 1 x) =
      (P₃.h - P₂.h) • T.val x := by
  have hdiff : fzLeft A.toWeakModule 2 W.conformalVector x -
      fzRight A.toWeakModule 2 W.conformalVector x =
      A.Lm1 x + mode (A.YM W.conformalVector) 1 x := by
    rw [fzLeft_sub_fzRight]
    simp [Finset.sum_range_succ, cbz, gBinom, OrdVModule.Lm1]
  apply LinearMap.ext
  intro y
  have hl := T.property.2.1 2 W.conformalVector W.conformalVector_mem_grading_two x y
  have hr := T.property.2.2 2 (by norm_num) W.conformalVector W.conformalVector_mem_grading_two
    x y (P₂.h • y) (by simpa using (P₂.isMod.L0_weight P₂.h y y.property).symm)
  apply Subtype.ext
  rw [← hdiff, map_sub, LinearMap.sub_apply]
  simp only [Submodule.coe_sub, LinearMap.smul_apply, Submodule.coe_smul]
  rw [hl, hr]
  norm_num only at *
  rw [P₃.isMod.L0_weight P₃.h _ (T.val x y).property]
  simp only [map_smul, Submodule.coe_smul]
  module

theorem fzSpace_translation_homogeneous (T : fzSpace A P₂ P₃)
    {α : ℂ} {x : M} (hx : x ∈ A.weight α) :
    T.val (A.Lm1 x) = (P₃.h - P₂.h - α) • T.val x := by
  have h := fzSpace_translation T x
  rw [map_add, A.L0_weight α x hx, map_smul] at h
  rw [eq_sub_of_add_eq h]
  module

end VOA.Huang.LiFusion
