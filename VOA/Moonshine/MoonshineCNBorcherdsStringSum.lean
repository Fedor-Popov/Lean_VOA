import VOA.Moonshine.MoonshineCNBorcherdsSl2
import VOA.Moonshine.MoonshineCNBorcherdsLevi

/-! The real-root strings form an actual direct sum, with canonical sum map onto U. -/

noncomputable section
open scoped DirectSum
namespace VOA.Moonshine.ConwayNorton

/-- The nonzero positions allowed in a positive imaginary string. -/
def borcherdsStringIndex := {jk : ℤ × ℕ // 1 ≤ jk.1 ∧ (jk.2 : ℤ) < jk.1}

def borcherdsStringDegree (i : borcherdsStringIndex) : ℤ × ℤ :=
  (1 + (i.val.2 : ℤ), i.val.1 - (i.val.2 : ℤ))

theorem borcherdsStringDegree_injective : Function.Injective borcherdsStringDegree := by
  intro i j h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only [borcherdsStringDegree] at h₁ h₂
  apply Subtype.ext
  apply Prod.ext <;> omega

namespace BorcherdsData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

theorem generatorString_le_genSpace (e : g) (j : ℤ) (hj : 1 ≤ j)
    (k : ℕ) (hk : (k : ℤ) < j) : D.generatorString e j k ≤ D.genSpace e :=
  le_iSup_of_le j (le_iSup_of_le hj (le_iSup_of_le k (le_iSup_of_le hk le_rfl)))

theorem genSpace_eq_iSup_strings (e : g) :
    D.genSpace e = ⨆ i : borcherdsStringIndex, D.generatorString e i.val.1 i.val.2 := by
  apply le_antisymm
  · exact iSup_le fun j => iSup_le fun hj => iSup_le fun k => iSup_le fun hk =>
      le_iSup_of_le ⟨(j, k), hj, hk⟩ le_rfl
  · exact iSup_le fun i => D.generatorString_le_genSpace e _ i.property.1 _ i.property.2

/-- Distinct string positions have distinct ambient homogeneous degrees. -/
theorem generatorStrings_independent (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot) :
    iSupIndep (fun i : borcherdsStringIndex => D.generatorString e i.val.1 i.val.2) :=
  (D.weight_internal.submodule_iSupIndep.comp borcherdsStringDegree_injective).mono
    (fun i => D.generatorString_le_weight e he i.val.1 i.val.2)

/-- Sum the actual string subspaces into U. -/
def genSpaceDirectSumMap (e : g) :
    (⨁ i : borcherdsStringIndex, D.generatorString e i.val.1 i.val.2) →ₗ[ℂ] D.genSpace e := by
  classical
  refine (DirectSum.coeLinearMap (fun i : borcherdsStringIndex =>
    D.generatorString e i.val.1 i.val.2)).codRestrict _ (fun x => ?_)
  rw [D.genSpace_eq_iSup_strings, ← DirectSum.range_coeLinearMap]
  exact LinearMap.mem_range_self _ x

theorem genSpaceDirectSumMap_bijective (e : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot) :
    Function.Bijective (D.genSpaceDirectSumMap e) := by
  classical
  constructor
  · intro x y h
    exact (D.generatorStrings_independent e he).dfinsupp_lsum_injective
      (congrArg Subtype.val h)
  · rintro ⟨y, hy⟩
    rw [D.genSpace_eq_iSup_strings, ← DirectSum.range_coeLinearMap] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

/-- The direct-sum identification does not assume freeness or a presentation of the Lie algebra. -/
def genSpaceDirectSumEquiv (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot) :
    (⨁ i : borcherdsStringIndex, D.generatorString e i.val.1 i.val.2) ≃ₗ[ℂ] D.genSpace e :=
  LinearEquiv.ofBijective (D.genSpaceDirectSumMap e) (D.genSpaceDirectSumMap_bijective e he)

end BorcherdsData
end VOA.Moonshine.ConwayNorton
