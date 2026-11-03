import VOA.Classification.COne.OrbIcoVProbeDescent

/-! Low levels of the same actual first-row Fock family have full Verma
rank at c=1, hence fixed local bases and zero generic kernel near c=1. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.VirasoroVerma Filter Topology
open scoped Classical

def fockBasisSize (N : ℕ) : ℕ := Module.finrank ℂ (LinearMap.range
  (chargedFockLevelMap (familyBackground 1) (familyMomentum 1) N))

theorem family_fock_low_dimension_one (N : ℕ) (hN : N < 13) :
    fockBasisSize N = Fintype.card (VermaPartitions N) := by
  have hdet (c h : ℂ) (hc : c=1) (hh : h=36) : (vermaGramMatrix c h N).det ≠ 0 := by
    subst c
    subst h
    convert vermaGramMatrix_one_sq_det_ne_zero 6 (by omega : N ≤ 2*6) using 1 <;> norm_num
  have hd := hdet (familyCharge 1) (familyWeight 1)
    (by norm_num [familyCharge, familyBackground])
    (by norm_num [familyWeight, familyBackground, familyMomentum])
  rw [fockBasisSize, LinearMap.finrank_range_of_inj
    (chargedFockLevelMap_injective _ _ N N hd le_rfl), vermaLevel_finrank]

theorem exists_local_low_first_row_basis (N : ℕ) (hN : N < 13) :
    ∃ a : Fin (fockBasisSize N) → VermaPartitions N → ℂ,
      ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
        LinearIndependent ℂ (familyColumns N a s.val) ∧
          Submodule.span ℂ (Set.range (familyColumns N a s.val)) =
            familyCoordinateImage N s.val := by
  let F := chargedFockLevelMap (familyBackground 1) (familyMomentum 1) N
  let J := Fin (fockBasisSize N)
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
  apply fixed_columns_near_basis parameterOne
    (fun s : NonzeroParameter => familyColumns N a s.val)
    (fun s : NonzeroParameter => familyCoordinateImage N s.val)
  · have hh : ContinuousAt (fun s : NonzeroParameter => s.val) parameterOne :=
      continuous_subtype_val.continuousAt
    exact (familyColumns_continuousAt N a 1 one_ne_zero).comp_of_eq hh rfl
  · exact hLI
  · intro s j
    exact familyColumns_mem N a s.val s.property j
  · exact Filter.Eventually.of_forall (fun s => by
      rw [familyCoordinateImage_finrank]
      have hb := (chargedFockLevelMap (familyBackground s.val) (familyMomentum s.val) N).finrank_range_le
      rw [vermaLevel_finrank] at hb
      change Module.finrank ℂ (LinearMap.range (chargedFockLevelMap (familyBackground s.val) (familyMomentum s.val) N)) ≤ Fintype.card (Fin (fockBasisSize N))
      simpa only [Fintype.card_fin, family_fock_low_dimension_one N hN] using hb)


theorem exists_local_self_fock_basis (N : ℕ) :
    ∃ a : Fin (fockBasisSize N) → VermaPartitions N → ℂ,
      ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
        LinearIndependent ℂ (familyColumns N a s.val) ∧
          Submodule.span ℂ (Set.range (familyColumns N a s.val)) =
            familyCoordinateImage N s.val := by
  by_cases hN : N < 13
  · exact exists_local_low_first_row_basis N hN
  · have he : N = 13+(N-13) := by omega
    rw [he]
    exact exists_local_first_row_basis (N-13)

theorem family_uniformProbe_kills_low_kernel_near (N : ℕ) (hN : N < 13) :
    ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
      ∀ v : Verma (familyCharge s.val) (familyWeight s.val),
        v ∈ sortedSpan _ _ N → familyMap s.val v=0 → uniformProbe _ _ v=0 := by
  obtain ⟨a,ha⟩ := exists_local_low_first_row_basis N hN
  filter_upwards [ha] with s hs
  have hF : Module.finrank ℂ (LinearMap.range (chargedFockLevelMap
      (familyBackground s.val) (familyMomentum s.val) N)) = Fintype.card (VermaPartitions N) := by
    rw [← familyCoordinateImage_finrank, ← hs.2, finrank_span_eq_card hs.1]
    simp [family_fock_low_dimension_one N hN]
  have hi : Function.Injective (chargedFockLevelMap
      (familyBackground s.val) (familyMomentum s.val) N) := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hr := (chargedFockLevelMap (familyBackground s.val) (familyMomentum s.val) N).finrank_range_add_finrank_ker
    rw [hF, vermaLevel_finrank] at hr
    omega
  intro v hv hz
  have hvz : (⟨v,hv⟩ : sortedSpan (familyCharge s.val) (familyWeight s.val) N) = 0 :=
    hi (Subtype.ext (by simpa only [map_zero] using hz))
  have he : v=0 := congrArg Subtype.val hvz
  rw [he, map_zero]

theorem family_uniformProbe_kills_self_kernel_near (N : ℕ) :
    ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
      ∀ v : Verma (familyCharge s.val) (familyWeight s.val),
        v ∈ sortedSpan _ _ N → familyMap s.val v=0 → uniformProbe _ _ v=0 := by
  by_cases hN : N < 13
  · exact family_uniformProbe_kills_low_kernel_near N hN
  · have he : N=13+(N-13) := by omega
    rw [he]
    exact family_uniformProbe_kills_kernel_near (N-13)

end VOA.Classification.COne.OrbIcoV
