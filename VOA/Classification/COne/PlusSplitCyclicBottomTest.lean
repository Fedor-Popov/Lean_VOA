import VOA.Classification.COne.PlusSplitExtraCharacters
import Mathlib.LinearAlgebra.Projection

/-! Exact tests for the remaining cyclic-intersection obstruction.
The tests do not assume an ordinary middle module. They do not prove
resonant splitting or invoke an unformalized higher Zhu criterion. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusRational VOA.Huang.LogRemovalAdmissible
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- For a simple kernel, avoiding any one nonzero vector is equivalent to
avoiding the entire kernel. The chosen vector can be at its bottom weight. -/
theorem disjoint_iff_avoids_kernel_vector (A : WeakModule W M)
    (P Q : Submodule (modeAlg A) M) (hP : IsAtom P)
    {y : M} (hy : y ∈ P) (hy0 : y ≠ 0) : Disjoint P Q ↔ y ∉ Q := by
  constructor
  · intro hd hQ
    exact hy0 (Submodule.disjoint_def.mp hd y hy hQ)
  · intro hn
    rw [disjoint_iff]
    by_contra hne
    have he : P ⊓ Q = P := (hP.le_iff_eq hne).mp inf_le_left
    exact hn ((show P ≤ Q from he ▸ inf_le_right) hy)

/-- The precise mode-algebra obstruction for a fixed nonzero kernel vector.
Checking only zero modes would not establish this condition. -/
theorem disjoint_cyclic_iff_no_mode_word (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hP : IsAtom P)
    {y : M} (hy : y ∈ P) (hy0 : y ≠ 0) (x : M) :
    Disjoint P (cyclic A x) ↔ ∀ r : modeAlg A, r • x ≠ y := by
  rw [disjoint_iff_avoids_kernel_vector A P _ hP hy hy0]
  change (¬ y ∈ Submodule.span (modeAlg A) {x}) ↔ _
  rw [Submodule.mem_span_singleton]
  exact not_exists

/-- A genuine mode-submodule complement supplies a generalized cyclic lift.
The projection commutes with L(0) because it is linear over the full mode
algebra. No local finiteness or diagonalizability assumption is needed. -/
theorem generalized_cyclic_lift_of_complement (A : WeakModule W M)
    (P Q : Submodule (modeAlg A) M) (hPQ : IsCompl P Q)
    (k : ℂ) (hb : FactorBottom A P ⊤ k) :
    ∃ x : M, x ∈ (L0 A).maxGenEigenspace k ∧ x ∉ P ∧ Disjoint P (cyclic A x) := by
  obtain ⟨z, hz, hzP⟩ := exists_generalized_lift_of_factorBottom A P k hb
  let p : M →ₗ[modeAlg A] M := Q.projection P hPQ.symm
  have hp (x : M) : p (L0 A x) = L0 A (p x) := by
    let r : modeAlg A := ⟨L0 A, Algebra.subset_adjoin ⟨W.conformalVector, 1, rfl⟩⟩
    exact p.map_smul r x
  have hpQ : p z ∈ Q := Submodule.projection_apply_mem hPQ.symm z
  have hpP : p z ∉ P := by
    intro h
    have h0 : p z = 0 := Submodule.disjoint_def.mp hPQ.disjoint (p z) h hpQ
    exact hzP ((Submodule.projection_apply_eq_zero_iff hPQ.symm).mp h0)
  refine ⟨p z, map_mem_maxGenEigenspace (L0 A) (L0 A) (p.restrictScalars ℂ) hp k hz,
    hpP, hPQ.disjoint.mono_right ?_⟩
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hpQ)

/-- The original cyclic-lift condition is exactly whole-extension splitting,
not an extra restriction on an already available complement. -/
theorem exists_cyclic_lift_iff_complement (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (hQ : P ⋖ ⊤) (k : ℂ)
    (hb : FactorBottom A P ⊤ k) :
    (∃ x : M, x ∈ (L0 A).maxGenEigenspace k ∧ x ∉ P ∧ Disjoint P (cyclic A x)) ↔
      ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
  constructor
  · rintro ⟨x, _, hx, hd⟩
    exact ⟨cyclic A x, isCompl_cyclic_of_disjoint A P hQ x hx hd⟩
  · rintro ⟨Q, hPQ⟩
    exact generalized_cyclic_lift_of_complement A P Q hPQ k hb

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne
open PlusRational PlusSplitting VOA.Huang.LogRemovalAdmissible

/-- OPEN, equivalent to the existing cyclic-lift residual: for each nonzero
bottom kernel vector, find a generalized quotient-bottom lift from which no
element of the full mode algebra reaches that vector. Both gap signs remain. -/
def V2mPlusResonantBottomAvoidance : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (A : WeakModule (V2mPlus m hm) M) (P : Submodule (modeAlg A) M) (h k : ℂ),
      IsAtom P → P ⋖ ⊤ → FactorBottom A ⊥ P h → FactorBottom A P ⊤ k →
      (∃ z : ℤ, z ≠ 0 ∧ k = h + (z : ℂ)) →
      ∀ y : M, y ∈ P → y ∈ (L0 A).maxGenEigenspace h → y ≠ 0 →
      ∃ x : M, x ∈ (L0 A).maxGenEigenspace k ∧ x ∉ P ∧
        ∀ r : modeAlg A, r • x ≠ y

theorem resonantCyclicLifts_iff_bottomAvoidance :
    V2mPlusResonantCyclicLifts ↔ V2mPlusResonantBottomAvoidance := by
  constructor
  · intro hl m hm hm2 M _ _ A P h k hP hQ hb ht hz y hy _ hy0
    obtain ⟨x, hx, hxP, hd⟩ := hl m hm hm2 A P h k hP hQ hb ht hz
    exact ⟨x, hx, hxP, (disjoint_cyclic_iff_no_mode_word A P hP hy hy0 x).mp hd⟩
  · intro hl m hm hm2 M _ _ A P h k hP hQ hb ht hz
    obtain ⟨y, hy, hy0⟩ := SetLike.not_le_iff_exists.mp hb.1
    obtain ⟨x, hx, hxP, hn⟩ := hl m hm hm2 A P h k hP hQ hb ht hz y hy.1 hy.2 hy0
    exact ⟨x, hx, hxP, (disjoint_cyclic_iff_no_mode_word A P hP hy.1 hy0 x).mpr hn⟩

theorem rationality_of_fourExtraCharacters_bottomAvoidance
    (hc : V2mPlusFourExtraCharacters) (ha : V2mPlusResonantBottomAvoidance) :
    V2mPlusRationalFactGe2 :=
  rationality_of_fourExtraCharacters_cyclicLifts hc
    (resonantCyclicLifts_iff_bottomAvoidance.mpr ha)

end VOA.Classification.COne
