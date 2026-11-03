import VOA.Classification.COne.OrbIcoVVacCoordinates

/-! The actual vacuum Fock image saturates its translation bound at c=1,
so fixed PBW combinations provide local bases without a flatness hypothesis. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.VirasoroVerma Filter Topology
open scoped Classical

theorem radical_bound_zero (m : ℕ) :
    Module.finrank ℂ (vermaRadicalLevel 1 0 (1+m)) ≤ Fintype.card (VermaPartitions m) := by
  have transfer (h : ℂ) (hh : h=0) (N : ℕ) (hN : N=1+m)
      (he : Module.finrank ℂ (vermaRadicalLevel 1 h N) ≤ Fintype.card (VermaPartitions m)) :
      Module.finrank ℂ (vermaRadicalLevel 1 0 (1+m)) ≤ Fintype.card (VermaPartitions m) := by
    subst h
    subst N
    exact he
  exact transfer _ (by norm_num) _ (by omega) (FFLower.radical_bound 0 m)

theorem vacuum_fock_image_dimension_one (m : ℕ) :
    Module.finrank ℂ (LinearMap.range
      (chargedFockLevelMap (familyBackground 1) (vacFamilyMomentum 1) (1+m))) +
      Fintype.card (VermaPartitions m) = Fintype.card (VermaPartitions (1+m)) := by
  apply Nat.le_antisymm (vacuum_fock_image_bound (familyBackground 1) m)
  apply chargedFockLevel_image_lower
  have hrad (c h : ℂ) (hc : c=1) (hh : h=0) :
      Module.finrank ℂ (vermaRadicalLevel c h (1+m)) ≤ Fintype.card (VermaPartitions m) := by
    subst c
    subst h
    exact radical_bound_zero m
  apply hrad
  · norm_num [familyBackground]
  · norm_num [familyBackground, vacFamilyMomentum]

def vacFirstRowBasisSize (m : ℕ) : ℕ := Module.finrank ℂ (LinearMap.range
  (chargedFockLevelMap (familyBackground 1) (vacFamilyMomentum 1) (1+m)))

theorem vacFirstRowBasisSize_partition (m : ℕ) :
    vacFirstRowBasisSize m + Fintype.card (VermaPartitions m) =
      Fintype.card (VermaPartitions (1+m)) := vacuum_fock_image_dimension_one m

theorem exists_local_vac_first_row_basis (m : ℕ) :
    ∃ a : Fin (vacFirstRowBasisSize m) → VermaPartitions (1+m) → ℂ,
      ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
        LinearIndependent ℂ (vacColumns (1+m) a s.val) ∧
          Submodule.span ℂ (Set.range (vacColumns (1+m) a s.val)) =
            vacCoordinateImage (1+m) s.val := by
  let N := 1+m
  let F := chargedFockLevelMap (familyBackground 1) (vacFamilyMomentum 1) N
  let J := Fin (vacFirstRowBasisSize m)
  let B : Module.Basis J ℂ (LinearMap.range F) := Module.finBasis ℂ (LinearMap.range F)
  choose u hu using fun j : J => (LinearMap.mem_range.mp (B j).property)
  let a : J → VermaPartitions N → ℂ :=
    fun j w => (vermaLevelBasis (familyCharge 1) (vacFamilyWeight 1) N).repr (u j) w
  have hcols (j : J) : vacColumns N a 1 j = fockCoordinates N (B j).val := by
    funext d
    rw [vacColumns, ← vacLevelCoefficient_sound N (a j) 1 one_ne_zero d.val]
    change coeff d.val (vacFamilyMap 1 (vermaLevelState _ _ N
      (fun w => (vermaLevelBasis _ _ N).repr (u j) w))) = _
    rw [vermaLevelState_coordinates]
    exact congrArg (fun v : gradingWN 1 N => coeff d.val v.val) (hu j)
  let K : LinearMap.range F →ₗ[ℂ] (FockOccupations N → ℂ) :=
    (fockCoordinates N).comp (LinearMap.range F).subtype
  have hK : Function.Injective K :=
    (fockCoordinates_injective N).comp (LinearMap.range F).subtype_injective
  have hLI : LinearIndependent ℂ (vacColumns N a 1) := by
    have hl := B.linearIndependent.map' K (LinearMap.ker_eq_bot.mpr hK)
    have he : vacColumns N a 1 = K ∘ B := by
      funext j
      exact hcols j
    rw [he]
    exact hl
  refine ⟨a, ?_⟩
  apply fixed_columns_near_basis_with_defect parameterOne
    (fun s : NonzeroParameter => vacColumns N a s.val)
    (fun s : NonzeroParameter => vacCoordinateImage N s.val)
    (Fintype.card (VermaPartitions m)) (Fintype.card (VermaPartitions N))
  · simpa [J, N] using vacFirstRowBasisSize_partition m
  · have hh : ContinuousAt (fun s : NonzeroParameter => s.val) parameterOne :=
      continuous_subtype_val.continuousAt
    exact (vacColumns_continuousAt N a 1 one_ne_zero).comp_of_eq hh rfl
  · exact hLI
  · intro s j
    exact vacColumns_mem N a s.val s.property j
  · exact Filter.Eventually.of_forall (fun s => by
      rw [vacCoordinateImage_finrank]
      exact vacuum_fock_image_bound (familyBackground s.val) m)


end VOA.Classification.COne.OrbIcoV
