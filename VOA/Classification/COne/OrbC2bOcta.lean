import VOA.Classification.COne.OrbC2bTetra

/-! # The octahedral involution step after the tetrahedral fixed algebra -/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbC2b
open VOA Equiv Equiv.Perm VOA.LatGen VOA.LatGen.Triplet

def transposition : Perm (Fin 4) := swap 0 (finRotate 4 0)

theorem octHom_transposition : octHom transposition = rot2 :=
  (octFun_spec _).unique isOct_rot2

theorem rot2_square : rot2 ^ 2 = 1 := by
  apply aut_ext_xyz
  intro a b c
  simp only [pow_two, Aut.mul_apply, rot2_xyz, neg_neg, Aut.one_apply]

private theorem rot2_preserves_tetra (x : LatModuleGen (latP 1))
    (hx : x ∈ (orbifold tetra).carrier) : rot2 x ∈ (orbifold tetra).carrier := by
  rintro g ⟨s, hs, rfl⟩
  have hmem : transposition⁻¹ * s * transposition ∈ alternatingGroup (Fin 4) := by
    rw [mem_alternatingGroup, map_mul, map_mul, map_inv,
      (mem_alternatingGroup.mp hs), mul_one, inv_mul_cancel]
  have hf := hx _ (show octHom (transposition⁻¹ * s * transposition) ∈ tetra from
    ⟨_, hmem, rfl⟩)
  have he : octHom s * rot2 = rot2 * octHom (transposition⁻¹ * s * transposition) := by
    rw [← octHom_transposition, ← map_mul, ← map_mul]
    congr 1
    group
  change (octHom s * rot2) x = rot2 x
  rw [he, Aut.mul_apply, hf]

theorem rot2_tetra_iff (x : LatModuleGen (latP 1)) :
    rot2 x ∈ (orbifold tetra).carrier ↔ x ∈ (orbifold tetra).carrier := by
  constructor
  · intro hx
    have h := rot2_preserves_tetra _ hx
    have he : rot2 (rot2 x) = x := by
      change (rot2 ^ 2) x = x
      rw [rot2_square, Aut.one_apply]
    rwa [he] at h
  · exact rot2_preserves_tetra x

def tetraInvolution : Aut (orbifoldVOA tetra) :=
  restrictAut (orbifold tetra) rot2 rot2_tetra_iff

theorem tetraInvolution_square : tetraInvolution ^ 2 = 1 :=
  restrictAut_pow_eq_one _ _ _ rot2_square

abbrev octa := octHom.range

theorem octa_group : Nonempty (octa ≃* Perm (Fin 4)) :=
  ⟨(MonoidHom.ofInjective octHom_injective).symm⟩

theorem octa_eq_join : octa = tetra ⊔ Subgroup.zpowers rot2 := by
  apply le_antisymm
  · rintro g ⟨s, rfl⟩
    have h : ∀ s : Perm (Fin 4), ∃ t : Perm (Fin 4),
        t ∈ alternatingGroup (Fin 4) ∧ (s = t ∨ s = t * transposition) := by
      simp only [mem_alternatingGroup]
      decide +kernel
    obtain ⟨t, ht, he | he⟩ := h s
    · rw [he]
      exact Subgroup.mem_sup_left ⟨t, ht, rfl⟩
    · rw [he]
      simp only [map_mul]
      apply Subgroup.mul_mem
      · exact Subgroup.mem_sup_left ⟨t, ht, rfl⟩
      · apply Subgroup.mem_sup_right
        exact octHom_transposition.symm ▸ Subgroup.mem_zpowers rot2
  · apply sup_le
    · rintro g ⟨s, _, rfl⟩
      exact ⟨s, rfl⟩
    · exact Subgroup.zpowers_le.mpr ⟨transposition, octHom_transposition⟩

theorem octa_involution_iso :
    VOAIsomorphic (orbifoldVOA (Subgroup.zpowers tetraInvolution)) (orbifoldVOA octa) := by
  rw [octa_eq_join]
  exact iterated_orbifold_iso _ _ _

end VOA.Classification.COne.OrbC2b
