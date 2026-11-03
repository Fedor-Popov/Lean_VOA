import VOA.Classification.COne.OrbC2bKlein

/-! # The tetrahedral group is the concrete cubic extension of the Klein group -/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbC2b
open VOA Equiv Equiv.Perm

def halfX : Perm (Fin 4) := swap 0 1 * swap 2 3
def halfY : Perm (Fin 4) := swap 0 3 * swap 1 2
def halfZ : Perm (Fin 4) := swap 0 2 * swap 1 3
def cycleThree : Perm (Fin 4) := swap 0 (finRotate 4 0) * finRotate 4

theorem octHom_cycleThree : octHom cycleThree = rotC :=
  (octFun_spec _).unique (isOct_rot2.mul isOct_rot4)

theorem octHom_halfZ : octHom halfZ = charU 1 le_rfl (-1) := by
  apply (octFun_spec _).unique
  have hs : sgnC halfZ = 1 := by norm_num [sgnC, halfZ, Fin.ext_iff]
  intro i
  rw [tvec, charU_neg_one_xyz, hs, one_smul, tvec]
  fin_cases i <;> apply xyz_congr <;>
    norm_num [halfZ, ta, tb, tc, swap_apply_def, Fin.ext_iff] <;> rfl

theorem octHom_halfX_theta (he : eps1 = 1) : octHom halfX = thetaM 1 le_rfl := by
  apply (octFun_spec _).unique
  have hs : sgnC halfX = 1 := by norm_num [sgnC, halfX, Fin.ext_iff]
  intro i
  rw [tvec, thetaM1_xyz, he, hs, one_smul, tvec]
  fin_cases i <;> apply xyz_congr <;>
    norm_num [halfX, ta, tb, tc, swap_apply_def, Fin.ext_iff] <;> rfl

theorem octHom_halfY_theta (he : eps1 = -1) : octHom halfY = thetaM 1 le_rfl := by
  apply (octFun_spec _).unique
  have hs : sgnC halfY = 1 := by norm_num [sgnC, halfY, Fin.ext_iff]
  intro i
  rw [tvec, thetaM1_xyz, he, hs, one_smul, tvec]
  fin_cases i <;> apply xyz_congr <;>
    norm_num [halfY, ta, tb, tc, swap_apply_def, Fin.ext_iff] <;> rfl

theorem klein_eq_join :
    klein = Subgroup.zpowers (charU 1 le_rfl (-1)) ⊔
      Subgroup.zpowers (thetaM 1 le_rfl) := by
  rw [zpowers_charU_neg_one]
  apply le_antisymm
  · rintro g ⟨d, rfl⟩
    cases d with
    | r i => exact Subgroup.mem_sup_left (show cycHom 1 le_rfl 2 (Multiplicative.ofAdd i) ∈
        (cycHom 1 le_rfl 2).range from ⟨_, rfl⟩)
    | sr i =>
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (Subgroup.mem_sup_left ⟨_, rfl⟩)
  · apply sup_le
    · rintro g ⟨z, rfl⟩
      exact ⟨DihedralGroup.r z.toAdd, rfl⟩
    · apply Subgroup.zpowers_le.mpr
      refine ⟨DihedralGroup.sr 0, ?_⟩
      change thetaM 1 le_rfl * cycHom 1 le_rfl 2 (Multiplicative.ofAdd 0) = _
      rw [ofAdd_zero, map_one, mul_one]

def tetra : Subgroup (Aut (V2m 1 le_rfl)) := (alternatingGroup (Fin 4)).map octHom

theorem tetra_group : Nonempty (tetra ≃* alternatingGroup (Fin 4)) :=
  ⟨((alternatingGroup (Fin 4)).equivMapOfInjective octHom octHom_injective).symm⟩

private theorem even_generators :
    halfX ∈ alternatingGroup (Fin 4) ∧ halfY ∈ alternatingGroup (Fin 4) ∧
      halfZ ∈ alternatingGroup (Fin 4) ∧ cycleThree ∈ alternatingGroup (Fin 4) := by
  simp only [mem_alternatingGroup]
  decide +kernel

private theorem half_images_mem :
    octHom halfX ∈ klein ∧ octHom halfY ∈ klein ∧ octHom halfZ ∈ klein := by
  have hz : octHom halfZ ∈ klein := by
    rw [octHom_halfZ, klein_eq_join]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have ht : thetaM 1 le_rfl ∈ klein := by
    rw [klein_eq_join]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hxz : halfX * halfZ = halfY := by decide +kernel
  have hyz : halfY * halfZ = halfX := by decide +kernel
  rcases eps1_cases with he | he
  · have hx : octHom halfX ∈ klein := by rwa [octHom_halfX_theta he]
    exact ⟨hx, by rw [← hxz, map_mul]; exact klein.mul_mem hx hz, hz⟩
  · have hy : octHom halfY ∈ klein := by rwa [octHom_halfY_theta he]
    exact ⟨by rw [← hyz, map_mul]; exact klein.mul_mem hy hz, hy, hz⟩

/-- A kernel-checked enumeration of the twelve even permutations. -/
theorem even_decomposition (s : Perm (Fin 4)) (hs : s ∈ alternatingGroup (Fin 4)) :
    ∃ (i : Fin 4) (j : Fin 3), s = ![1, halfX, halfY, halfZ] i * cycleThree ^ j.val := by
  have h : ∀ s : Perm (Fin 4), s ∈ alternatingGroup (Fin 4) →
      ∃ (i : Fin 4) (j : Fin 3), s = ![1, halfX, halfY, halfZ] i * cycleThree ^ j.val := by
    simp only [mem_alternatingGroup]
    decide +kernel
  exact h s hs

/-- The actual tetrahedral embedding is the cubic extension used above. -/
theorem tetra_eq_join : tetra = klein ⊔ Subgroup.zpowers rotC := by
  apply le_antisymm
  · rintro g ⟨s, hs, rfl⟩
    obtain ⟨i, j, rfl⟩ := even_decomposition s hs
    simp only [map_mul, map_pow]
    apply Subgroup.mul_mem
    · apply Subgroup.mem_sup_left
      fin_cases i
      · change octHom 1 ∈ klein
        rw [map_one]
        exact klein.one_mem
      · exact half_images_mem.1
      · exact half_images_mem.2.1
      · exact half_images_mem.2.2
    · apply Subgroup.pow_mem
      apply Subgroup.mem_sup_right
      exact octHom_cycleThree.symm ▸ Subgroup.mem_zpowers rotC
  · apply sup_le
    · rw [klein_eq_join]
      apply sup_le <;> apply Subgroup.zpowers_le.mpr
      · exact ⟨halfZ, even_generators.2.2.1, octHom_halfZ⟩
      · rcases eps1_cases with he | he
        · exact ⟨halfX, even_generators.1, octHom_halfX_theta he⟩
        · exact ⟨halfY, even_generators.2.1, octHom_halfY_theta he⟩
    · exact Subgroup.zpowers_le.mpr
        ⟨cycleThree, even_generators.2.2.2, octHom_cycleThree⟩

theorem tetra_cubic_iso :
    VOAIsomorphic (orbifoldVOA (Subgroup.zpowers kleinCubic)) (orbifoldVOA tetra) := by
  rw [tetra_eq_join]
  exact klein_cubic_orbifold_iso

end VOA.Classification.COne.OrbC2b
