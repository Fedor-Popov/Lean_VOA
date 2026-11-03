import VOA.Classification.COne.OrbIcoVVacContinuity

/-! Actual vacuum image occupation coordinates. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.VirasoroVerma Filter Topology
open scoped Classical

def vacCoordinateImage (N : ℕ) (s : ℂ) : Submodule ℂ (FockOccupations N → ℂ) :=
  (LinearMap.range (chargedFockLevelMap (familyBackground s) (vacFamilyMomentum s) N)).map
    (fockCoordinates N)

theorem vacCoordinateImage_finrank (N : ℕ) (s : ℂ) :
    Module.finrank ℂ (vacCoordinateImage N s) =
      Module.finrank ℂ (LinearMap.range
        (chargedFockLevelMap (familyBackground s) (vacFamilyMomentum s) N)) := by
  exact (Submodule.equivMapOfInjective (fockCoordinates N) (fockCoordinates_injective N)
    (LinearMap.range (chargedFockLevelMap (familyBackground s) (vacFamilyMomentum s) N))).finrank_eq.symm

def vacColumns {J : Type*} (N : ℕ) (a : J → VermaPartitions N → ℂ)
    (s : ℂ) (j : J) (d : FockOccupations N) : ℂ :=
  vacLevelCoefficient N (a j) s d.val

theorem vacColumns_mem {J : Type*} (N : ℕ) (a : J → VermaPartitions N → ℂ)
    (s : ℂ) (hs : s ≠ 0) (j : J) : vacColumns N a s j ∈ vacCoordinateImage N s := by
  let u : sortedSpan (familyCharge s) (vacFamilyWeight s) N :=
    ⟨vermaLevelState (familyCharge s) (vacFamilyWeight s) N (a j),
      vermaLevelState_mem _ _ _ _⟩
  refine ⟨chargedFockLevelMap (familyBackground s) (vacFamilyMomentum s) N u,
    ⟨u,rfl⟩,?_⟩
  funext d
  exact vacLevelCoefficient_sound N (a j) s hs d.val

theorem vacColumns_continuousAt {J : Type*} (N : ℕ)
    (a : J → VermaPartitions N → ℂ) (s₀ : ℂ) (hs : s₀ ≠ 0) :
    ContinuousAt (vacColumns N a) s₀ := by
  apply continuousAt_pi.mpr
  intro j
  apply continuousAt_pi.mpr
  intro d
  exact vacLevelCoefficient_continuousAt N (a j) s₀ hs d.val


end VOA.Classification.COne.OrbIcoV
