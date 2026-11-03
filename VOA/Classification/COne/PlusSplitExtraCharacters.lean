import VOA.Classification.COne.PlusSplitZhuFiniteTests

/-! Character-level replacements for the twisted top-model input. The
existence inputs below remain open. The finite tests are necessary and
sufficient, and involve the genuine Zhu quotient throughout. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusCharacterTable

abbrev UntwistedIndex (m : ℕ) := Fin (m - 1) ⊕ Fin 4

def untwistedLabel (m : ℕ) : UntwistedIndex m → Label m :=
  Sum.map id (Fin.castLE (by omega))

theorem untwistedLabel_injective (m : ℕ) : Function.Injective (untwistedLabel m) := by
  intro i j he
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (Sum.inl.inj he)
  · cases he
  · cases he
  · have hv : i.val = j.val := congrArg (fun x : Fin 8 => x.val) (Sum.inr.inj he)
    exact congrArg Sum.inr (Fin.ext hv)

theorem untwistedLabel_isUntwisted (m : ℕ) (i : UntwistedIndex m) :
    IsUntwisted (untwistedLabel m i) := by
  cases i with
  | inl i => trivial
  | inr i => exact i.isLt

def twistedLabel (m : ℕ) (i : Fin 4) : Label m := .inr ⟨i.val + 4, by omega⟩

theorem twistedLabel_injective (m : ℕ) : Function.Injective (twistedLabel m) := by
  intro i j h
  have hv := congrArg Fin.val (Sum.inr.inj h)
  apply Fin.ext
  dsimp [twistedLabel] at hv
  omega

theorem twistedLabel_not_isUntwisted (m : ℕ) (i : Fin 4) :
    ¬ IsUntwisted (twistedLabel m i) := by
  simp [IsUntwisted, twistedLabel]

variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance zhuRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-- Fix the already constructed m+3 genuine untwisted characters. -/
def untwistedCharacter (hm2 : 2 ≤ m) (i : UntwistedIndex m) :
    VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ :=
  Classical.choose (untwisted_character_exists m hm hm2 (untwistedLabel m i)
    (untwistedLabel_isUntwisted m i))

theorem untwistedCharacter_hasValues (hm2 : 2 ≤ m) (i : UntwistedIndex m) :
    HasValues m hm (untwistedLabel m i) (untwistedCharacter m hm hm2 i) :=
  Classical.choose_spec (untwisted_character_exists m hm hm2 (untwistedLabel m i)
    (untwistedLabel_isUntwisted m i))

theorem untwistedCharacter_injective (hm2 : 2 ≤ m) :
    Function.Injective (untwistedCharacter m hm hm2) := by
  intro i j h
  apply untwistedLabel_injective m
  exact label_eq_of_hasValues m hm hm2 _ _ _ (untwistedCharacter_hasValues m hm hm2 i)
    (h.symm ▸ untwistedCharacter_hasValues m hm hm2 j)

/-- The three scalar values in a character-table row. -/
def row (i : Label m) : Fin 3 → ℂ :=
  ![((values m (twistedScale m) i).1 : ℂ),
    ((values m (twistedScale m) i).2.1 : ℂ),
    ((values m (twistedScale m) i).2.2 : ℂ)]

/-- One normalization and 3(m+7) multiplication entries, plus the three
prescribed generator values. The linear functional must already be defined
on the actual quotient: descent is not omitted. -/
def FiniteCharacterTests (i : Label m) : Prop :=
  ∃ f : VOA.A (V2mPlus m hm) →ₗ[ℂ] ℂ,
    f 1 = 1 ∧
    (∀ a : Fin 3, f (PlusZhuNormalForms.generator m hm a) = row m i a) ∧
    (∀ (a : Fin 3) (j : PlusZhuFiniteTests.Index m),
      f (PlusZhuNormalForms.generator m hm a * PlusZhuFiniteTests.spanningClass m hm j) =
        row m i a * f (PlusZhuFiniteTests.spanningClass m hm j))

/-- Exact equivalence, not a purported proof of the existence input. -/
theorem finiteCharacterTests_iff (hm2 : 2 ≤ m) (i : Label m) :
    FiniteCharacterTests m hm i ↔
      ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm i χ := by
  constructor
  · rintro ⟨f, h1, hv, ht⟩
    let χ := PlusZhuFiniteTests.characterOfFiniteTests (PlusZhuNormalForms.generator m hm)
      (V2mPlus_zhu_adjoin_generators m hm hm2) (PlusZhuFiniteTests.spanningClass m hm)
      (PlusZhuFiniteTests.spanningClass_span m hm hm2) f h1
      (by intro a j; rw [ht, hv])
    exact ⟨χ, hv 0, hv 1, hv 2⟩
  · rintro ⟨χ, h0, h1, h2⟩
    have hv : ∀ a : Fin 3, χ (PlusZhuNormalForms.generator m hm a) = row m i a := by
      intro a
      fin_cases a
      · exact h0
      · exact h1
      · exact h2
    refine ⟨χ.toLinearMap, map_one χ, hv, ?_⟩
    intro a j
    exact (map_mul χ _ _).trans
      (congrArg (fun z => z * χ (PlusZhuFiniteTests.spanningClass m hm j)) (hv a))

end VOA.Classification.COne.PlusCharacterTable

namespace VOA.Classification.COne
open PlusCharacterTable

/-- OPEN: four additional characters, with no prescribed values and no
ordinary or twisted-module structure. Distinctness from the known characters
is explicit. -/
def V2mPlusFourExtraCharacters : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m),
    letI := instRingA (V2mPlus m hm)
    letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : Fin 4 → VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ,
      Function.Injective χ ∧ ∀ i j, χ i ≠ untwistedCharacter m hm hm2 j

/-- OPEN: only the four character-table rows, without top models. -/
def V2mPlusTwistedCharacters : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ i : Label m, ¬ IsUntwisted i →
    letI := instRingA (V2mPlus m hm)
    letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm i χ

/-- OPEN: finite linear-functional tests for each missing row. -/
def V2mPlusTwistedFiniteTests : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ i : Label m, ¬ IsUntwisted i →
    FiniteCharacterTests m hm i

theorem twistedCharacters_of_twistedTopModels (ht : V2mPlusTwistedTopModels) :
    V2mPlusTwistedCharacters := by
  intro m hm hm2 i hi
  exact character_exists_of_topModel m hm i (ht m hm hm2 i hi)

theorem twistedFiniteTests_iff_twistedCharacters :
    V2mPlusTwistedFiniteTests ↔ V2mPlusTwistedCharacters := by
  constructor <;> intro h m hm hm2 i hi
  · exact (finiteCharacterTests_iff m hm hm2 i).mp (h m hm hm2 i hi)
  · exact (finiteCharacterTests_iff m hm hm2 i).mpr (h m hm hm2 i hi)

theorem fourExtraCharacters_of_twistedCharacters (ht : V2mPlusTwistedCharacters) :
    V2mPlusFourExtraCharacters := by
  classical
  intro m hm hm2
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  have hex := fun i : Fin 4 => ht m hm hm2 (twistedLabel m i)
    (twistedLabel_not_isUntwisted m i)
  choose χ hχ using hex
  refine ⟨χ, ?_, ?_⟩
  · intro i j h
    apply twistedLabel_injective m
    exact label_eq_of_hasValues m hm hm2 _ _ _ (hχ i) (h.symm ▸ hχ j)
  · intro i j h
    have he := label_eq_of_hasValues m hm hm2 _ _ _ (hχ i)
      (h.symm ▸ untwistedCharacter_hasValues m hm hm2 j)
    exact twistedLabel_not_isUntwisted m i (he ▸ untwistedLabel_isUntwisted m j)

/-- No eigenvalue table for the four extra characters is required. -/
theorem zhuDistinctCharacters_of_fourExtraCharacters (hc : V2mPlusFourExtraCharacters) :
    V2mPlusZhuDistinctCharacters := by
  classical
  intro m hm hm2
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  obtain ⟨χ, hχ, hdis⟩ := hc m hm hm2
  let f := Sum.elim (untwistedCharacter m hm hm2) χ
  have hf : Function.Injective f := by
    intro i j h
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (untwistedCharacter_injective m hm hm2 h)
    · exact (hdis j i h.symm).elim
    · exact (hdis i j h).elim
    · exact congrArg Sum.inr (hχ h)
  let e : UntwistedIndex m ⊕ Fin 4 ≃ Fin (m + 7) :=
    Fintype.equivFinOfCardEq (by simp [UntwistedIndex]; omega)
  exact ⟨f ∘ e.symm, hf.comp e.symm.injective⟩

theorem zhuDistinctCharacters_of_twistedCharacters (ht : V2mPlusTwistedCharacters) :
    V2mPlusZhuDistinctCharacters :=
  zhuDistinctCharacters_of_fourExtraCharacters (fourExtraCharacters_of_twistedCharacters ht)

theorem zhu_finrank_eq_of_fourExtraCharacters (hc : V2mPlusFourExtraCharacters)
    (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    Module.finrank ℂ (VOA.A (V2mPlus m hm)) = m + 7 := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  letI := finiteDimensional_A_of_C2Cofinite _ (V2mPlus_c2Cofinite m hm)
  obtain ⟨χ, hχ⟩ := zhuDistinctCharacters_of_fourExtraCharacters hc m hm hm2
  have he := PlusSplitting.characterAlgEquiv χ hχ
    (by simpa using v2mPlusZhuDimensionBound_holds m hm hm2)
  simpa using he.toLinearEquiv.finrank_eq

theorem zhuSemisimple_of_fourExtraCharacters (hc : V2mPlusFourExtraCharacters) :
    ZhuV2mPlusSemisimple :=
  zhuV2mPlusSemisimple_of_distinctCharacters (zhuDistinctCharacters_of_fourExtraCharacters hc)

theorem rationality_of_fourExtraCharacters_cyclicLifts
    (hc : V2mPlusFourExtraCharacters) (hl : V2mPlusResonantCyclicLifts) :
    V2mPlusRationalFactGe2 :=
  rationality_of_distinctCharacters_resonant (zhuDistinctCharacters_of_fourExtraCharacters hc)
    (resonantGeneratorComplements_of_cyclicLifts hl)

theorem rationality_of_twistedFiniteTests_cyclicLifts
    (hc : V2mPlusTwistedFiniteTests) (hl : V2mPlusResonantCyclicLifts) :
    V2mPlusRationalFactGe2 :=
  rationality_of_fourExtraCharacters_cyclicLifts
    (fourExtraCharacters_of_twistedCharacters (twistedFiniteTests_iff_twistedCharacters.mp hc)) hl

end VOA.Classification.COne
