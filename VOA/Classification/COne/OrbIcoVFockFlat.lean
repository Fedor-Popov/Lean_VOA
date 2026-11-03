import VOA.Classification.COne.OrbIcoVFockCoordinates

/-! Genuine local first-row Fock bases near c=1: fixed PBW combinations
remain a basis because independence is open and the actual singular
kernel provides the matching all-parameter image dimension bound. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.VirasoroVerma Filter Topology
open scoped Classical

abbrev NonzeroParameter := {s : ℂ // s ≠ 0}

def parameterOne : NonzeroParameter := ⟨1, one_ne_zero⟩

def firstRowBasisSize (m : ℕ) : ℕ := Module.finrank ℂ (LinearMap.range
  (chargedFockLevelMap (familyBackground 1) (familyMomentum 1) (13+m)))

theorem firstRowBasisSize_partition (m : ℕ) :
    firstRowBasisSize m + Fintype.card (VermaPartitions m) =
      Fintype.card (VermaPartitions (13+m)) := family_fock_image_dimension_one m

theorem exists_local_first_row_basis (m : ℕ) :
    ∃ a : Fin (firstRowBasisSize m) → VermaPartitions (13+m) → ℂ,
      ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
        LinearIndependent ℂ (familyColumns (13+m) a s.val) ∧
          Submodule.span ℂ (Set.range (familyColumns (13+m) a s.val)) =
            familyCoordinateImage (13+m) s.val := by
  let N := 13+m
  let F := chargedFockLevelMap (familyBackground 1) (familyMomentum 1) N
  let J := Fin (firstRowBasisSize m)
  let B : Module.Basis J ℂ (LinearMap.range F) := Module.finBasis ℂ (LinearMap.range F)
  choose u hu using fun j : J => (LinearMap.mem_range.mp (B j).property)
  let a : J → VermaPartitions N → ℂ :=
    fun j w => (vermaLevelBasis (familyCharge 1) (familyWeight 1) N).repr (u j) w
  have hcols (j : J) : familyColumns N a 1 j = fockCoordinates N (B j).val := by
    funext d
    rw [familyColumns, ← familyLevelCoefficient_sound N (a j) 1 one_ne_zero d.val]
    change coeff d.val (familyMap 1 (vermaLevelState _ _ N
      (fun w => (vermaLevelBasis _ _ N).repr (u j) w))) = _
    rw [vermaLevelState_coordinates]
    exact congrArg (fun v : gradingWN 1 N => coeff d.val v.val) (hu j)
  let K : LinearMap.range F →ₗ[ℂ] (FockOccupations N → ℂ) :=
    (fockCoordinates N).comp (LinearMap.range F).subtype
  have hK : Function.Injective K :=
    (fockCoordinates_injective N).comp (LinearMap.range F).subtype_injective
  have hLI : LinearIndependent ℂ (familyColumns N a 1) := by
    have hl := B.linearIndependent.map' K (LinearMap.ker_eq_bot.mpr hK)
    have he : familyColumns N a 1 = K ∘ B := by
      funext j
      exact hcols j
    rw [he]
    exact hl
  refine ⟨a, ?_⟩
  apply fixed_columns_near_basis_with_defect parameterOne
    (fun s : NonzeroParameter => familyColumns N a s.val)
    (fun s : NonzeroParameter => familyCoordinateImage N s.val)
    (Fintype.card (VermaPartitions m)) (Fintype.card (VermaPartitions N))
  · simpa [J, N] using firstRowBasisSize_partition m
  · have hh : ContinuousAt (fun s : NonzeroParameter => s.val) parameterOne :=
      continuous_subtype_val.continuousAt
    exact (familyColumns_continuousAt N a 1 one_ne_zero).comp_of_eq hh rfl
  · exact hLI
  · intro s j
    exact familyColumns_mem N a s.val s.property j
  · exact Filter.Eventually.of_forall (fun s => by
      rw [familyCoordinateImage_finrank]
      exact family_fock_image_bound s.val s.property m)

end VOA.Classification.COne.OrbIcoV
