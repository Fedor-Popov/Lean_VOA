import VOA.Classification.COne.PlusSplitCandidateMultiplication

/-! Resonant bottom avoidance reduces to one finite-dimensional degree span.
No non-membership assertion for a resonant extension is proved here. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

theorem homogeneousDegreeSpan_le_cyclic (A : WeakModule W M) (x : M) (d : ℤ) :
    homogeneousDegreeSpan A x d ≤ (cyclic A x).restrictScalars ℂ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  clear hl
  induction l with
  | nil => exact Submodule.mem_span_singleton_self x
  | cons a l ih =>
    exact (cyclic A x).smul_mem
      (⟨mode (A.YM a.state) a.modeIndex,
        Algebra.subset_adjoin ⟨a.state, a.modeIndex, rfl⟩⟩ : modeAlg A) ih

theorem homogeneousDegreeSpan_gen (A : WeakModule W M) {x : M} {k : ℂ}
    (hx : x ∈ (L0 A).maxGenEigenspace k) (d : ℤ) :
    homogeneousDegreeSpan A x d ≤ (L0 A).maxGenEigenspace (k + (d : ℂ)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  change homogeneousDegree l = d at hl
  subst d
  change homogeneousWord A l x ∈ (L0 A).maxGenEigenspace (k + (homogeneousDegree l : ℂ))
  induction l with
  | nil => simpa [homogeneousWord, homogeneousDegree] using hx
  | cons a l ih =>
    have h := mode_mem_maxGenEigenspace A a.homogeneous a.modeIndex ih
    simpa only [homogeneousWord, LinearMap.comp_apply, homogeneousDegree, Int.cast_add,
      add_assoc, add_comm, add_left_comm] using h

theorem cyclic_eq_iSup_homogeneousDegreeSpan (hC2 : C2Cofinite W)
    (A : WeakModule W M) (x : M) :
    (cyclic A x).restrictScalars ℂ = ⨆ d : ℤ, homogeneousDegreeSpan A x d := by
  apply le_antisymm
  · obtain ⟨D, Q, Bm, _, _, hs⟩ := weak_cyclic_spanning hC2 A x
    exact hs.trans (iSup_le fun d => le_iSup_of_le d
      (normalDegreeSpan_le_homogeneousDegreeSpan D A x Q Bm d))
  · exact iSup_le (homogeneousDegreeSpan_le_cyclic A x)

/-- In a generalized cyclic module, the degree-d span is exactly its
generalized weight k+d part. No ordinary-middle-module assumption is made. -/
theorem cyclic_inf_gen_eq_degreeSpan (hC2 : C2Cofinite W) (A : WeakModule W M)
    {x : M} {k : ℂ} (hx : x ∈ (L0 A).maxGenEigenspace k) (d : ℤ) :
    (cyclic A x).restrictScalars ℂ ⊓ (L0 A).maxGenEigenspace (k + (d : ℂ)) =
      homogeneousDegreeSpan A x d := by
  let other := spectralPart A {μ | μ ≠ k + (d : ℂ)}
  have hd : Disjoint ((L0 A).maxGenEigenspace (k + (d : ℂ))) other := by
    have h := spectralPart_disjoint A
      (s := {k + (d : ℂ)}) (t := {μ | μ ≠ k + (d : ℂ)})
      (Set.disjoint_left.mpr (by intro μ hμ hn; exact hn (Set.mem_singleton_iff.mp hμ)))
    simpa [spectralPart, other] using h
  have hs : (cyclic A x).restrictScalars ℂ ≤ homogeneousDegreeSpan A x d ⊔ other := by
    rw [cyclic_eq_iSup_homogeneousDegreeSpan hC2 A x]
    apply iSup_le
    intro n
    by_cases hn : n = d
    · subst n; exact le_sup_left
    · apply (homogeneousDegreeSpan_gen A hx n).trans
      apply le_trans _ le_sup_right
      apply le_iSup_of_le (k + (n : ℂ))
      apply le_iSup_of_le
        (show k + (n : ℂ) ≠ k + (d : ℂ) from fun he =>
          hn (Int.cast_injective (add_left_cancel he)))
      exact le_rfl
  apply le_antisymm
  · intro y hy
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hs hy.1)
    have hbgen : b ∈ (L0 A).maxGenEigenspace (k + (d : ℂ)) := by
      have he : b = y - a := by rw [← hab]; abel
      rw [he]
      exact Submodule.sub_mem _ hy.2 (homogeneousDegreeSpan_gen A hx d ha)
    have hb0 := Submodule.disjoint_def.mp hd b hbgen hb
    simpa [← hab, hb0] using ha
  · exact le_inf (homogeneousDegreeSpan_le_cyclic A x d) (homogeneousDegreeSpan_gen A hx d)

/-- The full mode-algebra avoidance test is precisely one degree-span test. -/
theorem no_mode_word_iff_not_mem_degreeSpan (hC2 : C2Cofinite W)
    (A : WeakModule W M) {x y : M} {k : ℂ}
    (hx : x ∈ (L0 A).maxGenEigenspace k) (d : ℤ)
    (hy : y ∈ (L0 A).maxGenEigenspace (k + (d : ℂ))) :
    (∀ r : modeAlg A, r • x ≠ y) ↔ y ∉ homogeneousDegreeSpan A x d := by
  have he : y ∈ cyclic A x ↔ y ∈ homogeneousDegreeSpan A x d := by
    constructor
    · intro h
      rw [← cyclic_inf_gen_eq_degreeSpan hC2 A hx d]
      exact ⟨h, hy⟩
    · intro h
      exact homogeneousDegreeSpan_le_cyclic A x d h
  rw [← he]
  change _ ↔ ¬y ∈ Submodule.span (modeAlg A) {x}
  rw [Submodule.mem_span_singleton]
  exact not_exists.symm

theorem finiteDimensional_resonantDegree (hC2 : C2Cofinite W)
    (A : WeakModule W M) (x : M) (d : ℤ) :
    FiniteDimensional ℂ (homogeneousDegreeSpan A x d) :=
  finiteDimensional_homogeneousDegreeSpan_of_normalForm weakDegreeNormalForm hC2 A x d

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne
open PlusSplitting ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible

/-- OPEN: choose a generalized quotient-bottom lift whose single degree -z
span omits the kernel bottom vector. Both signs of the resonance are retained. -/
def V2mPlusResonantDegreeAvoidance : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (A : WeakModule (V2mPlus m hm) M) (P : Submodule (modeAlg A) M) (h k : ℂ),
      IsAtom P → P ⋖ ⊤ → FactorBottom A ⊥ P h → FactorBottom A P ⊤ k →
      ∀ z : ℤ, z ≠ 0 → k = h + (z : ℂ) →
      ∀ y : M, y ∈ P → y ∈ (L0 A).maxGenEigenspace h → y ≠ 0 →
      ∃ x : M, x ∈ (L0 A).maxGenEigenspace k ∧ x ∉ P ∧
        y ∉ homogeneousDegreeSpan A x (-z)

theorem resonantDegreeAvoidance_iff_bottomAvoidance :
    V2mPlusResonantDegreeAvoidance ↔ V2mPlusResonantBottomAvoidance := by
  constructor
  · intro hd m hm hm2 M _ _ A P h k hP hQ hb ht hz y hy hyg hy0
    obtain ⟨z, hz, he⟩ := hz
    obtain ⟨x, hx, hxP, hn⟩ := hd m hm hm2 A P h k hP hQ hb ht z hz he y hy hyg hy0
    have hs : k + ((-z : ℤ) : ℂ) = h := by rw [he]; push_cast; ring
    exact ⟨x, hx, hxP,
      (no_mode_word_iff_not_mem_degreeSpan (V2mPlus_c2Cofinite m hm) A hx (-z)
        (hs.symm ▸ hyg)).mpr hn⟩
  · intro hb m hm hm2 M _ _ A P h k hP hQ hlo hup z hz he y hy hyg hy0
    obtain ⟨x, hx, hxP, hn⟩ := hb m hm hm2 A P h k hP hQ hlo hup
      ⟨z, hz, he⟩ y hy hyg hy0
    have hs : k + ((-z : ℤ) : ℂ) = h := by rw [he]; push_cast; ring
    exact ⟨x, hx, hxP,
      (no_mode_word_iff_not_mem_degreeSpan (V2mPlus_c2Cofinite m hm) A hx (-z)
        (hs.symm ▸ hyg)).mp hn⟩

theorem rationality_of_twistedOmegaECharacters_degreeAvoidance
    (hc : V2mPlusTwistedOmegaECharacters) (hd : V2mPlusResonantDegreeAvoidance) :
    V2mPlusRationalFactGe2 :=
  rationality_of_twistedOmegaECharacters_cyclicLifts hc
    (resonantCyclicLifts_iff_bottomAvoidance.mpr
      (resonantDegreeAvoidance_iff_bottomAvoidance.mp hd))

end VOA.Classification.COne
