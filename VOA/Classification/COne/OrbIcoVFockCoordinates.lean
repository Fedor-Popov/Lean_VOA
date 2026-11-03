import VOA.Classification.COne.OrbIcoVFockContinuity
import VOA.Classification.COne.OrbIcoVFockCOne
import VOA.Classification.COne.OrbIcoVFixedColumns

/-! Actual finite occupation coordinates for the first-row Fock image.
The coordinate map is injective, and fixed PBW combinations give its
continuous parameter-dependent columns. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.VirasoroVerma Filter Topology
open scoped Classical

abbrev FockOccupations (N : ℕ) :=
  {d : (ℕ × Fin 1) →₀ ℕ // Finsupp.weight weightFnN d = N}

instance fockOccupations_fintype (N : ℕ) : Fintype (FockOccupations N) :=
  Fintype.ofEquiv (VermaMultisetPartitions N) (fockMultisetPartitionEquiv N).symm

def fockCoordinates (N : ℕ) : gradingWN 1 N →ₗ[ℂ] (FockOccupations N → ℂ) where
  toFun v d := coeff d.val v.val
  map_add' v w := by ext d; exact coeff_add _ _ _
  map_smul' z v := by ext d; exact coeff_smul _ _ _

theorem fockCoordinates_injective (N : ℕ) : Function.Injective (fockCoordinates N) := by
  intro v w he
  apply Subtype.ext
  apply MvPolynomial.ext
  intro d
  by_cases hd : Finsupp.weight weightFnN d = N
  · exact congrArg (fun f => f ⟨d,hd⟩) he
  · have hv : coeff d v.val = 0 := by
      by_contra hn
      exact hd (v.property hn)
    have hw : coeff d w.val = 0 := by
      by_contra hn
      exact hd (w.property hn)
    rw [hv,hw]

def familyCoordinateImage (N : ℕ) (s : ℂ) : Submodule ℂ (FockOccupations N → ℂ) :=
  (LinearMap.range (chargedFockLevelMap (familyBackground s) (familyMomentum s) N)).map
    (fockCoordinates N)

theorem familyCoordinateImage_finrank (N : ℕ) (s : ℂ) :
    Module.finrank ℂ (familyCoordinateImage N s) =
      Module.finrank ℂ (LinearMap.range
        (chargedFockLevelMap (familyBackground s) (familyMomentum s) N)) := by
  exact (Submodule.equivMapOfInjective (fockCoordinates N) (fockCoordinates_injective N)
    (LinearMap.range (chargedFockLevelMap (familyBackground s) (familyMomentum s) N))).finrank_eq.symm

def familyColumns {J : Type*} (N : ℕ) (a : J → VermaPartitions N → ℂ)
    (s : ℂ) (j : J) (d : FockOccupations N) : ℂ :=
  familyLevelCoefficient N (a j) s d.val

theorem familyColumns_mem {J : Type*} (N : ℕ) (a : J → VermaPartitions N → ℂ)
    (s : ℂ) (hs : s ≠ 0) (j : J) : familyColumns N a s j ∈ familyCoordinateImage N s := by
  let u : sortedSpan (familyCharge s) (familyWeight s) N :=
    ⟨vermaLevelState (familyCharge s) (familyWeight s) N (a j),
      vermaLevelState_mem _ _ _ _⟩
  refine ⟨chargedFockLevelMap (familyBackground s) (familyMomentum s) N u,
    ⟨u,rfl⟩,?_⟩
  funext d
  exact familyLevelCoefficient_sound N (a j) s hs d.val

theorem familyColumns_continuousAt {J : Type*} (N : ℕ)
    (a : J → VermaPartitions N → ℂ) (s₀ : ℂ) (hs : s₀ ≠ 0) :
    ContinuousAt (familyColumns N a) s₀ := by
  apply continuousAt_pi.mpr
  intro j
  apply continuousAt_pi.mpr
  intro d
  exact familyLevelCoefficient_continuousAt N (a j) s₀ hs d.val

end VOA.Classification.COne.OrbIcoV
