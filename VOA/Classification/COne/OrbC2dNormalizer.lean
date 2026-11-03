import VOA.Classification.COne.OrbC2dConjugacy
import VOA.Classification.COne.OrbC2dFinite

/-! # The normalizer of the standard Klein four subgroup is exactly S₄ -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2d
open VOA OrbC2b Equiv Equiv.Perm
local notation "V1" => LatGen.latticeVOAGen (LatGen.Triplet.latP 1)
  (LatGen.Triplet.latP_even 1) (LatGen.Triplet.latP_posDef 1 le_rfl)

private theorem theta_mem_klein : thetaM 1 le_rfl ∈ klein := by
  rw [klein_eq_join]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

private theorem z_mem_klein : charU 1 le_rfl (-1) ∈ klein := by
  rw [klein_eq_join]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

private theorem half_mem_klein :
    octHom halfX ∈ klein ∧ octHom halfY ∈ klein ∧ octHom halfZ ∈ klein := by
  have hz : octHom halfZ ∈ klein := octHom_halfZ.symm ▸ z_mem_klein
  have hxz : halfX * halfZ = halfY := by decide +kernel
  have hyz : halfY * halfZ = halfX := by decide +kernel
  rcases eps1_cases with he | he
  · have hx : octHom halfX ∈ klein := (octHom_halfX_theta he).symm ▸ theta_mem_klein
    exact ⟨hx, by rw [← hxz, map_mul]; exact klein.mul_mem hx hz, hz⟩
  · have hy : octHom halfY ∈ klein := (octHom_halfY_theta he).symm ▸ theta_mem_klein
    exact ⟨by rw [← hyz, map_mul]; exact klein.mul_mem hy hz, hy, hz⟩

def kleinMap : DihedralGroup 2 →* Aut V1 := octHom.comp kleinPerm

theorem kleinMap_injective : Function.Injective kleinMap :=
  octHom_injective.comp kleinPerm_injective

theorem kleinMap_range : kleinMap.range = klein := by
  have hle : kleinMap.range ≤ klein := by
    rintro _ ⟨d, rfl⟩
    change octHom (kleinPerm d) ∈ klein
    rcases kleinPerm_values d with h | h | h | h
    · rw [h, map_one]; exact klein.one_mem
    · rw [h]; exact half_mem_klein.1
    · rw [h]; exact half_mem_klein.2.1
    · rw [h]; exact half_mem_klein.2.2
  have hc : Nat.card kleinMap.range = Nat.card klein := by
    rw [← Nat.card_congr (MonoidHom.ofInjective kleinMap_injective).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective (dihHom_injective 1 le_rfl (n := 2))).toEquiv]
  letI : Finite klein := Finite.of_equiv (DihedralGroup 2)
    (MonoidHom.ofInjective (dihHom_injective 1 le_rfl (n := 2))).toEquiv
  exact Subgroup.eq_of_le_of_card_ge hle hc.ge

def kleinEquiv : DihedralGroup 2 ≃* klein :=
  (MonoidHom.ofInjective kleinMap_injective).trans (MulEquiv.subgroupCongr kleinMap_range)

theorem kleinEquiv_coe (d : DihedralGroup 2) : (kleinEquiv d : Aut V1) = kleinMap d := rfl

theorem klein_le_octa : klein ≤ octa := by
  rw [← kleinMap_range]
  rintro _ ⟨d, rfl⟩
  exact ⟨kleinPerm d, rfl⟩

/-- A direct calculation: the centralizer of the Klein group is itself. -/
theorem centralizer_klein_le (y : Aut V1)
    (hy : ∀ x ∈ klein, y * x = x * y) : y ∈ klein := by
  have hz := hy _ z_mem_klein
  have hfix : charU 1 le_rfl (-1) (y (LatGen.hSt (LatGen.Triplet.latP 1)
      (a1 1))) = y (LatGen.hSt (LatGen.Triplet.latP 1) (a1 1)) := by
    rw [← Aut.mul_apply, ← hz, Aut.mul_apply, charU_hSt]
  have hc (u : ℂˣ) (hu : charU 1 le_rfl u * thetaM 1 le_rfl =
      thetaM 1 le_rfl * charU 1 le_rfl u) : u = 1 ∨ u = -1 := by
    rw [charU_mul_thetaM] at hu
    have he : u⁻¹ = u := charU_injective 1 le_rfl (mul_left_cancel hu)
    have hs : (u : ℂ) ^ 2 = 1 := by
      have : u * u = 1 := by calc
        u * u = u⁻¹ * u := congrArg (fun t => t * u) he.symm
        _ = 1 := inv_mul_cancel u
      have ht := congrArg (fun v : ℂˣ => (v : ℂ)) this
      simpa only [Units.val_mul, Units.val_one, pow_two] using ht
    rcases eq_one_or_neg_one_of_sq hs with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by simpa using h))
  rcases normalizer_of_fix (by norm_num : (-1 : ℂˣ) ≠ 1) hfix with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · rcases hc u (hy _ theta_mem_klein) with rfl | rfl
    · rw [map_one]; exact klein.one_mem
    · exact z_mem_klein
  · have ht := hy _ theta_mem_klein
    have hu : charU 1 le_rfl u * thetaM 1 le_rfl = thetaM 1 le_rfl * charU 1 le_rfl u := by
      apply mul_left_cancel (a := thetaM 1 le_rfl)
      simpa only [mul_assoc] using ht
    rcases hc u hu with rfl | rfl
    · rw [map_one, mul_one]; exact theta_mem_klein
    · exact klein.mul_mem theta_mem_klein z_mem_klein

/-- Every automorphism normalizing the concrete Klein group is octahedral. -/
theorem normalizer_klein_le_octa : Subgroup.normalizer klein ≤ octa := by
  intro y hy
  let f : klein ≃* klein :=
    (klein.equivMapOfInjective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective).trans
      (MulEquiv.subgroupCongr (by
        apply SetLike.coe_injective
        exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hy))
  obtain ⟨s, hs⟩ := kleinPerm_aut_realized (kleinEquiv.trans (f.trans kleinEquiv.symm))
  have he (d : DihedralGroup 2) :
      y * kleinMap d * y⁻¹ = octHom s * kleinMap d * (octHom s)⁻¹ := by
    have hh := congrArg octHom (hs d)
    simp only [map_mul, map_inv] at hh
    change (kleinEquiv (kleinEquiv.symm (f (kleinEquiv d))) : Aut V1) = _ at hh
    simpa only [MulEquiv.apply_symm_apply] using hh
  have hr : (octHom s)⁻¹ * y ∈ klein := by
    apply centralizer_klein_le
    intro x hx
    obtain ⟨d, hd⟩ := kleinEquiv.surjective ⟨x, hx⟩
    have hd' : kleinMap d = x := congrArg Subtype.val hd
    have hh := he d
    rw [hd'] at hh
    calc
      (octHom s)⁻¹ * y * x = (octHom s)⁻¹ * (y * x * y⁻¹) * y := by group
      _ = (octHom s)⁻¹ * (octHom s * x * (octHom s)⁻¹) * y := by rw [hh]
      _ = x * ((octHom s)⁻¹ * y) := by group
  have ho := octa.mul_mem (show octHom s ∈ octa from ⟨s, rfl⟩) (klein_le_octa hr)
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using ho

theorem octa_le_normalizer_klein : octa ≤ Subgroup.normalizer klein := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨s, rfl⟩ x hx
  rw [← kleinMap_range] at hx ⊢
  obtain ⟨d, rfl⟩ := hx
  obtain ⟨e, he⟩ := kleinPerm_normal s d
  exact ⟨e, by simpa only [kleinMap, MonoidHom.comp_apply, map_mul, map_inv] using
    (congrArg octHom he).symm⟩

/-- Exact normalizer equality in the full, infinite automorphism group. -/
theorem normalizer_klein_eq_octa : Subgroup.normalizer klein = octa :=
  le_antisymm normalizer_klein_le_octa octa_le_normalizer_klein

end VOA.Classification.COne.OrbC2d
