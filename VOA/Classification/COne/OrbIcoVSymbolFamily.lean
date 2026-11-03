import VOA.Classification.COne.OrbIcoVVacLow
import VOA.Classification.COne.OrbIcoVGenericScalar
import VOA.Classification.COne.OrbIcoVActionContinuity

/-! Unified actual Fock realizations of the two symbol channels, with
local finite bases and a parameter-independent PBW survival measure. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.VirasoroVerma InverseDS.LeeYangFockVirasoro Filter Topology
open scoped Classical

def symbolFamilyMomentum (self : Bool) (s : ℂ) : ℂ :=
  if self then familyMomentum s else vacFamilyMomentum s

def symbolFamilyWeight (self : Bool) (s : ℂ) : ℂ :=
  (symbolFamilyMomentum self s)^2-2*familyBackground s*symbolFamilyMomentum self s

abbrev symbolFamilyMap (self : Bool) (s : ℂ) :=
  chargedFockMap (familyBackground s) (symbolFamilyMomentum self s)

def symbolBasisSize (self : Bool) (N : ℕ) : ℕ :=
  if self then fockBasisSize N else vacBasisSize N

def symbolCoordinateImage (self : Bool) (N : ℕ) (s : ℂ) :=
  if self then familyCoordinateImage N s else vacCoordinateImage N s

def symbolColumns {J : Type*} (self : Bool) (N : ℕ)
    (a : J → VermaPartitions N → ℂ) (s : ℂ) : J → FockOccupations N → ℂ :=
  if self then familyColumns N a s else vacColumns N a s

theorem symbolFamily_weight (self : Bool) (s : ℂ) (hs : s≠0) :
    symbolFamilyWeight self s=symbolTargetWeight self (s^2) := by
  cases self
  · simp [symbolFamilyWeight,symbolFamilyMomentum,symbolTargetWeight,vacFamilyMomentum]
  · exact family_weight s hs

theorem symbolFamily_incoming (s : ℂ) (hs : s≠0) :
    familyWeight s=incomingWeight (s^2) := family_weight s hs

theorem symbolColumns_sound {J : Type*} (self : Bool) (N : ℕ)
    (a : J → VermaPartitions N → ℂ) (s : ℂ) (hs : s≠0)
    (j : J) (d : FockOccupations N) :
    coeff d.val (symbolFamilyMap self s
      (vermaLevelState (familyCharge s) (symbolFamilyWeight self s) N (a j)))=
        symbolColumns self N a s j d := by
  cases self
  · exact vacLevelCoefficient_sound N (a j) s hs d.val
  · exact familyLevelCoefficient_sound N (a j) s hs d.val

theorem exists_local_symbol_basis (self : Bool) (N : ℕ) :
    ∃ a : Fin (symbolBasisSize self N) → VermaPartitions N → ℂ,
      ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
        LinearIndependent ℂ (symbolColumns self N a s.val) ∧
          Submodule.span ℂ (Set.range (symbolColumns self N a s.val)) =
            symbolCoordinateImage self N s.val := by
  cases self
  · exact exists_local_vac_fock_basis N
  · exact exists_local_self_fock_basis N

theorem symbol_uniformProbe_kills_kernel_near (self : Bool) (N : ℕ) :
    ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
      ∀ v : Verma (familyCharge s.val) (symbolFamilyWeight self s.val),
        v ∈ sortedSpan _ _ N → symbolFamilyMap self s.val v=0 → uniformProbe _ _ v=0 := by
  cases self
  · exact vac_uniformProbe_kills_all_kernel_near N
  · exact family_uniformProbe_kills_self_kernel_near N

def levelProbe (N : ℕ) (a : VermaPartitions N → ℂ) : ℂ :=
  ∑ w : VermaPartitions N, a w*wordProbe w.val

theorem uniformProbe_levelState (c h : ℂ) (N : ℕ) (a : VermaPartitions N → ℂ) :
    uniformProbe c h (vermaLevelState c h N a)=levelProbe N a := by
  simp only [vermaLevelState,map_sum,map_smul,uniformProbe_word,levelProbe,smul_eq_mul]

theorem symbolColumns_continuousAt {J : Type*} (self : Bool) (N : ℕ)
    (a : J → VermaPartitions N → ℂ) (s₀ : ℂ) (hs : s₀≠0) :
    ContinuousAt (symbolColumns self N a) s₀ := by
  cases self
  · exact vacColumns_continuousAt N a s₀ hs
  · exact familyColumns_continuousAt N a s₀ hs

end VOA.Classification.COne.OrbIcoV
