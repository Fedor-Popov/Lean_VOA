import VOA.Classification.COne.OrbC2bTower
import VOA.Classification.COne.V2PlusV8
import VOA.Classification.COne.PlusRat2Rational

/-! # The norm-eight plus algebra and its concrete cubic automorphism

`klein` is exactly the standard order-four dihedral subgroup. The generator
`rotC` cyclically permutes the three weight-one coordinate axes of `V₂`.
Its restriction to the fixed algebra is constructed, not postulated.
-/

noncomputable section
namespace VOA.Classification.COne.OrbC2b
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice

abbrev klein := (dihHom 1 le_rfl 2).range

/-- The lattice has rank one and generator of norm eight (`m = 4`). -/
theorem klein_iso_plus_four :
    VOAIsomorphic (orbifoldVOA klein) (V2mPlus 4 (by norm_num)) := by
  simpa using orbifold_dihedral_iso 1 le_rfl 2

/-- Unconditional strong rationality of the actual standard Klein-four fixed algebra. -/
theorem klein_stronglyRational : StronglyRational (orbifoldVOA klein) := by
  obtain ⟨e, he, hω⟩ := klein_iso_plus_four
  exact stronglyRational_of_iso e he hω (PlusRat2.V2mPlus_stronglyRational_four _)

theorem klein_fixed_iff (x : VOA.LatGen.LatModuleGen (latP 1)) :
    x ∈ (orbifold klein).carrier ↔
      charU 1 le_rfl (-1) x = x ∧ thetaM 1 le_rfl x = x := by
  rw [show (x ∈ (orbifold klein).carrier) ↔
    (∀ g ∈ (dihHom 1 le_rfl 2).range, g x = x) from Iff.rfl, fix_dih_iff]
  change (x ∈ (orbifold (cycHom 1 le_rfl 2).range).carrier ∧ _) ↔ _
  rw [← zpowers_charU_neg_one, mem_orbifold_zpowers_iff]

theorem rotC_cube : rotC ^ 3 = 1 := by
  apply aut_ext_xyz
  intro a b c
  simp only [pow_succ, pow_zero, one_mul, Aut.mul_apply, rotC_xyz, Aut.one_apply]

private theorem rotC_preserves_klein (x : VOA.LatGen.LatModuleGen (latP 1))
    (hx : x ∈ (orbifold klein).carrier) : rotC x ∈ (orbifold klein).carrier := by
  obtain ⟨hz, ht⟩ := (klein_fixed_iff x).mp hx
  apply (klein_fixed_iff _).mpr
  rcases eps1_cases with he | he
  · have hzC : charU 1 le_rfl (-1) * rotC = rotC * thetaM 1 le_rfl := by
      apply aut_ext_xyz
      intro a b c
      simp only [Aut.mul_apply, charU_neg_one_xyz, rotC_xyz, thetaM1_xyz, he]
      apply xyz_congr <;> ring
    have htC : thetaM 1 le_rfl * rotC =
        rotC * (thetaM 1 le_rfl * charU 1 le_rfl (-1)) := by
      apply aut_ext_xyz
      intro a b c
      simp only [Aut.mul_apply, charU_neg_one_xyz, rotC_xyz, thetaM1_xyz, he]
      apply xyz_congr <;> ring
    constructor
    · change (charU 1 le_rfl (-1) * rotC) x = _
      rw [hzC, Aut.mul_apply, ht]
    · change (thetaM 1 le_rfl * rotC) x = _
      rw [htC, Aut.mul_apply, Aut.mul_apply, hz, ht]
  · have hzC : charU 1 le_rfl (-1) * rotC =
        rotC * (thetaM 1 le_rfl * charU 1 le_rfl (-1)) := by
      apply aut_ext_xyz
      intro a b c
      simp only [Aut.mul_apply, charU_neg_one_xyz, rotC_xyz, thetaM1_xyz, he]
      apply xyz_congr <;> ring
    have htC : thetaM 1 le_rfl * rotC = rotC * charU 1 le_rfl (-1) := by
      apply aut_ext_xyz
      intro a b c
      simp only [Aut.mul_apply, charU_neg_one_xyz, rotC_xyz, thetaM1_xyz, he]
      apply xyz_congr <;> ring
    constructor
    · change (charU 1 le_rfl (-1) * rotC) x = _
      rw [hzC, Aut.mul_apply, Aut.mul_apply, hz, ht]
    · change (thetaM 1 le_rfl * rotC) x = _
      rw [htC, Aut.mul_apply, hz]
theorem rotC_klein_iff (x : VOA.LatGen.LatModuleGen (latP 1)) :
    rotC x ∈ (orbifold klein).carrier ↔ x ∈ (orbifold klein).carrier := by
  constructor
  · intro hx
    have h := rotC_preserves_klein _ (rotC_preserves_klein _ hx)
    have hc : rotC (rotC (rotC x)) = x := by
      change (rotC ^ 3) x = x
      rw [rotC_cube, Aut.one_apply]
    rwa [hc] at h
  · exact rotC_preserves_klein x

/-- The actual order-dividing-three automorphism on the Klein-four fixed VOA. -/
def kleinCubic : Aut (orbifoldVOA klein) :=
  restrictAut (orbifold klein) rotC rotC_klein_iff

theorem kleinCubic_cube : kleinCubic ^ 3 = 1 :=
  restrictAut_pow_eq_one _ _ _ rotC_cube

/-- Concrete iterated fixed-point identification, with the ambient group shown explicitly. -/
theorem klein_cubic_orbifold_iso :
    VOAIsomorphic (orbifoldVOA (Subgroup.zpowers kleinCubic))
      (orbifoldVOA (klein ⊔ Subgroup.zpowers rotC)) :=
  iterated_orbifold_iso _ _ _

end VOA.Classification.COne.OrbC2b
