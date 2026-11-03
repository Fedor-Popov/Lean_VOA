import VOA.Classification.COne.OrbIcoVVacDescent

/-! Complete actual vacuum local bases, including the relative ground
level, and descent of the C2 probe in every finite level near c=1. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.VirasoroVerma Filter Topology
open scoped Classical

def vacBasisSize (N : ℕ) : ℕ := Module.finrank ℂ (LinearMap.range
  (chargedFockLevelMap (familyBackground 1) (vacFamilyMomentum 1) N))

theorem vac_fock_ground_dimension_one (N : ℕ) (hN : N < 1) :
    vacBasisSize N = Fintype.card (VermaPartitions N) := by
  have hz : N=0 := by omega
  subst N
  have hd : (vermaGramMatrix (familyCharge 1) (vacFamilyWeight 1) 0).det ≠ 0 := by
    rw [vermaGramMatrix_zero_det]
    exact one_ne_zero
  rw [vacBasisSize, LinearMap.finrank_range_of_inj
    (chargedFockLevelMap_injective _ _ 0 0 hd le_rfl), vermaLevel_finrank]

theorem exists_local_vac_ground_basis (N : ℕ) (hN : N < 1) :
    ∃ a : Fin (vacBasisSize N) → VermaPartitions N → ℂ,
      ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
        LinearIndependent ℂ (vacColumns N a s.val) ∧
          Submodule.span ℂ (Set.range (vacColumns N a s.val)) =
            vacCoordinateImage N s.val := by
  let F := chargedFockLevelMap (familyBackground 1) (vacFamilyMomentum 1) N
  let J := Fin (vacBasisSize N)
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
  apply fixed_columns_near_basis parameterOne
    (fun s : NonzeroParameter => vacColumns N a s.val)
    (fun s : NonzeroParameter => vacCoordinateImage N s.val)
  · have hh : ContinuousAt (fun s : NonzeroParameter => s.val) parameterOne :=
      continuous_subtype_val.continuousAt
    exact (vacColumns_continuousAt N a 1 one_ne_zero).comp_of_eq hh rfl
  · exact hLI
  · intro s j
    exact vacColumns_mem N a s.val s.property j
  · exact Filter.Eventually.of_forall (fun s => by
      rw [vacCoordinateImage_finrank]
      have hb := (chargedFockLevelMap (familyBackground s.val) (vacFamilyMomentum s.val) N).finrank_range_le
      rw [vermaLevel_finrank] at hb
      change Module.finrank ℂ (LinearMap.range (chargedFockLevelMap (familyBackground s.val) (vacFamilyMomentum s.val) N)) ≤ Fintype.card (Fin (vacBasisSize N))
      simpa only [Fintype.card_fin, vac_fock_ground_dimension_one N hN] using hb)


theorem exists_local_vac_fock_basis (N : ℕ) :
    ∃ a : Fin (vacBasisSize N) → VermaPartitions N → ℂ,
      ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
        LinearIndependent ℂ (vacColumns N a s.val) ∧
          Submodule.span ℂ (Set.range (vacColumns N a s.val)) =
            vacCoordinateImage N s.val := by
  by_cases hN : N < 1
  · exact exists_local_vac_ground_basis N hN
  · have he : N = 1+(N-1) := by omega
    rw [he]
    exact exists_local_vac_first_row_basis (N-1)

theorem vac_uniformProbe_kills_ground_kernel_near (N : ℕ) (hN : N < 1) :
    ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
      ∀ v : Verma (familyCharge s.val) (vacFamilyWeight s.val),
        v ∈ sortedSpan _ _ N → vacFamilyMap s.val v=0 → uniformProbe _ _ v=0 := by
  obtain ⟨a,ha⟩ := exists_local_vac_ground_basis N hN
  filter_upwards [ha] with s hs
  have hF : Module.finrank ℂ (LinearMap.range (chargedFockLevelMap
      (familyBackground s.val) (vacFamilyMomentum s.val) N)) = Fintype.card (VermaPartitions N) := by
    rw [← vacCoordinateImage_finrank, ← hs.2, finrank_span_eq_card hs.1]
    simp [vac_fock_ground_dimension_one N hN]
  have hi : Function.Injective (chargedFockLevelMap
      (familyBackground s.val) (vacFamilyMomentum s.val) N) := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hr := (chargedFockLevelMap (familyBackground s.val) (vacFamilyMomentum s.val) N).finrank_range_add_finrank_ker
    rw [hF, vermaLevel_finrank] at hr
    omega
  intro v hv hz
  have hvz : (⟨v,hv⟩ : sortedSpan (familyCharge s.val) (vacFamilyWeight s.val) N) = 0 :=
    hi (Subtype.ext (by simpa only [map_zero] using hz))
  have he : v=0 := congrArg Subtype.val hvz
  rw [he, map_zero]

theorem vac_uniformProbe_kills_all_kernel_near (N : ℕ) :
    ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
      ∀ v : Verma (familyCharge s.val) (vacFamilyWeight s.val),
        v ∈ sortedSpan _ _ N → vacFamilyMap s.val v=0 → uniformProbe _ _ v=0 := by
  by_cases hN : N < 1
  · exact vac_uniformProbe_kills_ground_kernel_near N hN
  · have he : N=1+(N-1) := by omega
    rw [he]
    exact vac_uniformProbe_kills_kernel_near (N-1)


end VOA.Classification.COne.OrbIcoV
