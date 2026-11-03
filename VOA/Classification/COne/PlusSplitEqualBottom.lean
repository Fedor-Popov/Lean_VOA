import VOA.Classification.COne.PlusSplitUntwistedCharacters

/-! # Intrinsic equal bottoms give a common admissible level zero

For a whole weak extension 0 < P < M, both intrinsic FactorBottom witnesses
bound the entire generalized spectrum below. Regrading by floor(Re(alpha-h))
puts both witnesses at degree zero, so the proved Zhu bottom splitter applies.
The middle module is not assumed ordinary, or supplied with a grading.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

theorem spectrum_lower_bound_of_equal_factorBottoms (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (h : ℂ)
    (hb : FactorBottom A ⊥ P h) (ht : FactorBottom A P ⊤ h) :
    ∀ a, (L0 A).maxGenEigenspace a ≠ ⊥ → h.re ≤ a.re := by
  intro a ha
  by_cases hp : (L0 A).maxGenEigenspace a ≤ P.restrictScalars ℂ
  · apply hb.2 a
    intro he
    apply ha
    apply bot_unique
    intro x hx
    exact he ⟨hp hx, hx⟩
  · apply ht.2 a
    simpa only [FactorWeight, Submodule.restrictScalars_top, top_inf_eq] using hp

/-- Construct a grading at an intrinsic spectral lower bound, retaining the
given weak action and putting every generalized h-vector at level zero. -/
theorem exists_admissible_at_spectral_bottom (A : WeakModule W M)
    (hspan : (⨆ a : ℂ, (L0 A).maxGenEigenspace a) = ⊤)
    (h : ℂ) (hbound : ∀ a, (L0 A).maxGenEigenspace a ≠ ⊥ → h.re ≤ a.re) :
    ∃ N : AdmissibleModule W M, N.toWeakModule = A ∧
      (L0 A).maxGenEigenspace h ≤ N.lev 0 := by
  let index : ℂ → ℤ := fun a => ⌊a.re - h.re⌋
  have hn : ∀ a, (L0 A).maxGenEigenspace a ≠ ⊥ → 0 ≤ index a := by
    intro a ha
    exact Int.floor_nonneg.mpr (sub_nonneg.mpr (hbound a ha))
  have hs : ∀ (a : ℂ) (d : ℤ), index (a + (d : ℂ)) = index a + d := by
    intro a d
    dsimp [index]
    rw [add_sub_right_comm, Int.floor_add_intCast]
  refine ⟨admissibleOfSpectralIndex A index hspan hn hs, rfl, ?_⟩
  exact le_iSup_of_le h (le_iSup_of_le (by simp [index]) le_rfl)

/-- Equal intrinsic bottoms split a whole simple weak extension. This is the
FactorBottom-to-level-zero bridge without an ordinary-extension assumption. -/
theorem exists_isCompl_of_semisimpleZhu_equalBottom
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (A : WeakModule W M) (P : Submodule (modeAlg A) M)
    (hP : IsAtom P) (hQ : P ⋖ ⊤) (h : ℂ)
    (hb : FactorBottom A ⊥ P h) (ht : FactorBottom A P ⊤ h) :
    ∃ Q : Submodule (modeAlg A) M, IsCompl P Q := by
  obtain ⟨N, he, hlev⟩ := exists_admissible_at_spectral_bottom A
    (weak_spectral_decomposition A (weakL0LocallyFinite hC2 A)) h
    (spectrum_lower_bound_of_equal_factorBottoms A P h hb ht)
  subst A
  apply exists_isCompl_of_semisimpleZhu_levelZero hss N P hP hQ
  · obtain ⟨x, hx, hx0⟩ := SetLike.not_le_iff_exists.mp hb.1
    exact ⟨x, hx.1, hlev hx.2, hx0⟩
  · intro hz
    apply ht.1
    intro x hx
    exact hz (hlev hx.2)

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne
open PlusSplitting

/-- A narrower, whole-extension version of the arbitrary-interval target.
Both bottom witnesses are intrinsic; the weak middle module is unrestricted. -/
def V2mPlusWholeEqualBottomSplitting : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (A : WeakModule (V2mPlus m hm) M) (P : Submodule (modeAlg A) M) (h : ℂ),
      IsAtom P → P ⋖ ⊤ → PlusSplitting.FactorBottom A ⊥ P h →
      PlusSplitting.FactorBottom A P ⊤ h →
      ∃ Q : Submodule (modeAlg A) M, IsCompl P Q

theorem wholeEqualBottomSplitting_of_zhuSemisimple (hzhu : ZhuV2mPlusSemisimple) :
    V2mPlusWholeEqualBottomSplitting := by
  intro m hm hm2 M _ _ A P h hP hQ hb ht
  exact exists_isCompl_of_semisimpleZhu_equalBottom (V2mPlus_c2Cofinite m hm)
    (hzhu m hm hm2) A P hP hQ h hb ht

end VOA.Classification.COne
