import VOA.Classification.COne.PlusTwistTopActions
import VOA.Classification.COne.PlusSplitResonantDegree

/-! # The four twisted Zhu characters from actual lattice modules -/
noncomputable section
namespace VOA.Classification.COne.PlusTwistLattice
open PlusCharacterTable PlusUnitary PlusZhuNormalForms

/-- A scalar on one nonzero vector determines the character of a one-dimensional top. -/
theorem topCharacter_mk_of_eigenvector {V M : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
    (N : OrdVModule W M) {h : ℂ} (hlow : IsLowestWeight N h)
    (e : N.weight h ≃ₗ[ℂ] ℂ) (a : V) (c : ℂ) (x : N.weight h) (hx : x ≠ 0)
    (ha : oMod N a (x : M) = c • (x : M)) :
    PlusCharacterTable.topCharacter N hlow e (VOA.mk W a) = c := by
  have hx' : e x ≠ 0 := fun hz => hx (e.injective (hz.trans (map_zero e).symm))
  apply mul_right_cancel₀ hx'
  have hrep : x = e x • e.symm 1 := by apply e.injective; simp
  have hact : actA N hlow (VOA.mk W a) x = c • x := by
    apply Subtype.ext
    rw [actA_mk_apply_coe]
    exact ha
  calc
    _ = e (actA N hlow (VOA.mk W a) x) := by
      change e (actA N hlow (VOA.mk W a) (e.symm 1)) * e x = _
      conv_rhs => rw [hrep]
      simp only [map_smul, smul_eq_mul]
      ring
    _ = _ := by rw [hact, map_smul]; rfl

theorem topCharacter_omega (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    topCharacter m hm t odd (generator m hm 0) = bottom odd := by
  apply PlusCharacterTable.topCharacter_mk_of_scalar
  intro x
  change oMod (fourModules m hm t odd) (V2mPlus m hm).conformalVector (x : _) = _
  rw [oMod_conformalVector]
  exact (fourModules m hm t odd).L0_weight _ _ x.2

theorem topCharacter_E (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    topCharacter m hm t odd (generator m hm 2) = eValue m t odd := by
  apply topCharacter_mk_of_eigenvector (fourModules m hm t odd)
    (fourModules_lowest m hm t odd) (topCoordinate m hm t odd) (EP m hm)
    (eValue m t odd) ⟨topVector m hm t odd, topVector_mem m hm t odd⟩
  · intro hz
    exact topVector_ne_zero m hm t odd (congrArg Subtype.val hz)
  · exact topVector_E m hm t odd

end VOA.Classification.COne.PlusTwistLattice

namespace VOA.Classification.COne
open PlusTwistLattice PlusCharacterTable PlusZhuNormalForms

/-- The four prescribed omega/E characters, obtained from the constructed twisted modules. -/
theorem V2mPlus_twistedOmegaECharacters : V2mPlusTwistedOmegaECharacters := by
  intro m hm _
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  intro i
  fin_cases i
  · refine ⟨PlusTwistLattice.topCharacter m hm 0 false, ?_, ?_⟩
    · rw [topCharacter_omega]; norm_num [bottom, twistedPair]
    · rw [topCharacter_E]; norm_num [eValue, twistedPair, VOA.Moonshine.Extraspecial.sgn_zero]
  · refine ⟨PlusTwistLattice.topCharacter m hm 0 true, ?_, ?_⟩
    · rw [topCharacter_omega]; norm_num [bottom, twistedPair]
    · rw [topCharacter_E]
      simp [eValue, twistedPair, VOA.Moonshine.Extraspecial.sgn_zero]
      ring
  · refine ⟨PlusTwistLattice.topCharacter m hm 1 false, ?_, ?_⟩
    · rw [topCharacter_omega]; norm_num [bottom, twistedPair]
    · rw [topCharacter_E]; norm_num [eValue, twistedPair, VOA.Moonshine.Extraspecial.sgn_one]
  · refine ⟨PlusTwistLattice.topCharacter m hm 1 true, ?_, ?_⟩
    · rw [topCharacter_omega]; norm_num [bottom, twistedPair]
    · rw [topCharacter_E]
      simp [eValue, twistedPair, VOA.Moonshine.Extraspecial.sgn_one]
      ring

/-- The full character-table statement follows from the proved omega/E equivalence. -/
theorem V2mPlus_twistedCharacters : V2mPlusTwistedCharacters :=
  twistedOmegaECharacters_iff_twistedCharacters.mp V2mPlus_twistedOmegaECharacters

/-- The actual plus Zhu algebra is semisimple. -/
theorem V2mPlus_zhuSemisimple : ZhuV2mPlusSemisimple :=
  zhuSemisimple_of_fourExtraCharacters
    (fourExtraCharacters_of_twistedOmegaECharacters V2mPlus_twistedOmegaECharacters)

/-- The sharp Zhu dimension, with character existence discharged. -/
theorem V2mPlus_zhu_finrank (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    Module.finrank ℂ (VOA.A (V2mPlus m hm)) = m + 7 :=
  zhu_finrank_eq_of_fourExtraCharacters
    (fourExtraCharacters_of_twistedOmegaECharacters V2mPlus_twistedOmegaECharacters) m hm hm2

/-- Only the resonant degree-avoidance input remains on this rationality route. -/
theorem rationality_of_resonantDegreeAvoidance
    (hr : V2mPlusResonantDegreeAvoidance) : V2mPlusRationalFactGe2 :=
  rationality_of_twistedOmegaECharacters_degreeAvoidance V2mPlus_twistedOmegaECharacters hr

end VOA.Classification.COne
