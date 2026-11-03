import VOA.Classification.COne.PlusSplitIntervals

/-! The remaining resonant obstruction as a disjoint cyclic lift.
The existence proposition is open. Finite length does not imply its disjointness
clause; that clause is where extension/fusion input is still needed. -/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.PlusSplitting
open PlusRational VOA.Huang.LogRemovalAdmissible
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- A cyclic lift outside a maximal submodule splits exactly when it misses
the kernel. All modes are included in the cyclic span. -/
theorem isCompl_cyclic_of_disjoint (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hP : P ⋖ ⊤) (x : M)
    (hx : x ∉ P) (hd : Disjoint P (cyclic A x)) : IsCompl P (cyclic A x) := by
  refine ⟨hd, codisjoint_iff.mpr ?_⟩
  rcases hP.wcovBy.eq_or_eq (show P ≤ P ⊔ cyclic A x from le_sup_left) le_top with he | he
  · exact (hx (he ▸ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)))).elim
  · exact he

/-- A generalized vector in the quotient's bottom always lifts to a
nonzero generalized vector outside the kernel. Disjointness is not asserted. -/
theorem exists_generalized_lift_of_factorBottom (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (k : ℂ) (hb : FactorBottom A P ⊤ k) :
    ∃ x : M, x ∈ (L0 A).maxGenEigenspace k ∧ x ∉ P := by
  obtain ⟨x, hx, hn⟩ := SetLike.not_le_iff_exists.mp hb.1
  exact ⟨x, hx.2, hn⟩

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne
open PlusRational PlusSplitting VOA.Huang.LogRemovalAdmissible

/-- OPEN: in a resonant whole weak extension, choose a bottom generalized
lift whose full cyclic module has zero intersection with the kernel.
Both orientations of the nonzero integral weight difference are retained. -/
def V2mPlusResonantCyclicLifts : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (A : WeakModule (V2mPlus m hm) M) (P : Submodule (modeAlg A) M) (h k : ℂ),
      IsAtom P → P ⋖ ⊤ → FactorBottom A ⊥ P h → FactorBottom A P ⊤ k →
      (∃ z : ℤ, z ≠ 0 ∧ k = h + (z : ℂ)) →
      ∃ x : M, x ∈ (L0 A).maxGenEigenspace k ∧ x ∉ P ∧ Disjoint P (cyclic A x)

/-- The cyclic-lift residual suffices for every original resonant interval
and hence for stability under all three generating fields. -/
theorem resonantGeneratorComplements_of_cyclicLifts (hl : V2mPlusResonantCyclicLifts) :
    V2mPlusResonantGeneratorComplements := by
  apply resonantBottomSplitting_iff_generatorComplements.mp
  intro m hm hm2 M _ _ N a b c h k hab hbc hb ht hz
  apply relativeComplement_of_whole_factorBottoms (V2mPlus_c2Cofinite m hm)
    N.toWeakModule hab hbc h k hb ht
  intro X _ _ B P hP hQ hlo hup
  obtain ⟨x, _, hx, hd⟩ := hl m hm hm2 B P h k hP hQ hlo hup hz
  exact ⟨cyclic B x, isCompl_cyclic_of_disjoint B P hQ x hx hd⟩

/-- Conditional rationality with the specific cyclic-intersection obstruction
in place of the generator-complement hypothesis. -/
theorem rationality_of_twistedTopModels_normalForms_cyclicLifts
    (ht : V2mPlusTwistedTopModels) (hr : V2mPlusZhuNormalFormReductions)
    (hl : V2mPlusResonantCyclicLifts) : V2mPlusRationalFactGe2 :=
  rationality_of_twistedTopModels_normalForms_resonant ht hr
    (resonantGeneratorComplements_of_cyclicLifts hl)

end VOA.Classification.COne
