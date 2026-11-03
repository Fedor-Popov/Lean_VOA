import VOA.Classification.COne.PlusSplitCyclicBottomTest

/-! The four missing characters need only their omega and E coordinates.
In particular, a twisted W top-action calculation is not required for the
character-count route. Existence as actual algebra homomorphisms is still open. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusCharacterTable

def twistedPair (m : ℕ) (a : ℝ) : Fin 4 → ℝ × ℝ :=
  ![(1/16, a), (9/16, -a*(4*m-1)), (1/16, -a), (9/16, a*(4*m-1))]

theorem twistedPair_injective (m : ℕ) (hm : 2 ≤ m) (a : ℝ) (ha : a ≠ 0) :
    Function.Injective (twistedPair m a) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  intro i j hij
  have hh := congrArg Prod.fst hij
  have he := congrArg Prod.snd hij
  fin_cases i <;> fin_cases j <;> norm_num [twistedPair] at hh <;>
    norm_num [twistedPair] at he
  all_goals first | rfl | (exfalso; apply ha; nlinarith)

/-- Even at coincident charged conformal weights, nonzero E separates the
twisted characters. The half-lattice conformal weights cannot coincide. -/
theorem twistedPair_ne_untwisted (m : ℕ) (hm : 2 ≤ m) (a : ℝ) (ha : a ≠ 0)
    (i : Fin 4) (j : UntwistedIndex m) :
    twistedPair m a i ≠
      ((values m a (untwistedLabel m j)).1, (values m a (untwistedLabel m j)).2.2) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmCases : (m : ℝ) = 2 ∨ (3 : ℝ) ≤ m := by
    by_cases h : m = 2
    · left; exact_mod_cast h
    · right; exact_mod_cast (show 3 ≤ m by omega)
  intro hij
  have hh := congrArg Prod.fst hij
  have he := congrArg Prod.snd hij
  rcases j with j | j
  · fin_cases i <;> norm_num [twistedPair, values, untwistedLabel] at he
    all_goals first | exact ha he | (rcases he with he | he <;> first | exact ha he | linarith)
  · fin_cases i <;> fin_cases j <;>
      norm_num [twistedPair, values, exceptional, untwistedLabel, Fin.castLE] at hh <;>
      norm_num [twistedPair, values, exceptional, untwistedLabel, Fin.castLE] at he
    all_goals rcases hmCases with h | h <;> nlinarith

theorem twistedPair_eq_table (m : ℕ) (a : ℝ) (i : Fin 4) :
    twistedPair m a i =
      ((values m a (twistedLabel m i)).1, (values m a (twistedLabel m i)).2.2) := by
  fin_cases i <;> rfl

end VOA.Classification.COne.PlusCharacterTable

namespace VOA.Classification.COne
open PlusCharacterTable PlusZhuNormalForms

/-- OPEN: four genuine Zhu characters with prescribed omega and E values.
No W value, full twisted module, or irreducibility witness is required. -/
def V2mPlusTwistedOmegaECharacters : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    letI := instRingA (V2mPlus m hm)
    letI := instAlgebraA (V2mPlus m hm)
    ∀ i : Fin 4, ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ,
      χ (generator m hm 0) = ((twistedPair m (twistedScale m) i).1 : ℂ) ∧
      χ (generator m hm 2) = ((twistedPair m (twistedScale m) i).2 : ℂ)

theorem twistedOmegaECharacters_of_twistedCharacters (ht : V2mPlusTwistedCharacters) :
    V2mPlusTwistedOmegaECharacters := by
  intro m hm hm2
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  intro i
  obtain ⟨χ, h0, _, h2⟩ := ht m hm hm2 (twistedLabel m i)
    (twistedLabel_not_isUntwisted m i)
  rw [twistedPair_eq_table]
  exact ⟨χ, h0, h2⟩

theorem fourExtraCharacters_of_twistedOmegaECharacters
    (ht : V2mPlusTwistedOmegaECharacters) : V2mPlusFourExtraCharacters := by
  classical
  intro m hm hm2
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  choose χ h0 h2 using ht m hm hm2
  refine ⟨χ, ?_, ?_⟩
  · intro i j he
    apply twistedPair_injective m hm2 _ (twistedScale_ne_zero m)
    exact Prod.ext
      (Complex.ofReal_injective ((h0 i).symm.trans (he.symm ▸ h0 j)))
      (Complex.ofReal_injective ((h2 i).symm.trans (he.symm ▸ h2 j)))
  · intro i j he
    have hv := untwistedCharacter_hasValues m hm hm2 j
    apply twistedPair_ne_untwisted m hm2 _ (twistedScale_ne_zero m) i j
    exact Prod.ext
      (Complex.ofReal_injective ((h0 i).symm.trans (he.symm ▸ hv.1)))
      (Complex.ofReal_injective ((h2 i).symm.trans (he.symm ▸ hv.2.2)))

theorem zhuDistinctCharacters_of_twistedOmegaECharacters
    (ht : V2mPlusTwistedOmegaECharacters) : V2mPlusZhuDistinctCharacters :=
  zhuDistinctCharacters_of_fourExtraCharacters
    (fourExtraCharacters_of_twistedOmegaECharacters ht)

theorem rationality_of_twistedOmegaECharacters_cyclicLifts
    (ht : V2mPlusTwistedOmegaECharacters) (hl : V2mPlusResonantCyclicLifts) :
    V2mPlusRationalFactGe2 :=
  rationality_of_fourExtraCharacters_cyclicLifts
    (fourExtraCharacters_of_twistedOmegaECharacters ht) hl

end VOA.Classification.COne
