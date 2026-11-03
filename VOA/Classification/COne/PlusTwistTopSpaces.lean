import VOA.Classification.COne.PlusTwistLatticeModules
import VOA.Moonshine.LatticeTwistedGeneralTops

/-! # One-dimensional lowest-weight spaces of the four twisted plus modules -/
noncomputable section
namespace VOA.Classification.COne.PlusTwistLattice
open VOA.IntegralLattice VOA.LatGen.Triplet VOA.Moonshine.LatticeTwistedGeneral
open VOA.TwistedHeisenberg VOA.TwistedSector VOA.TwistedPlus

/-- Even and odd oscillator bottoms, respectively. -/
def bottom (odd : Bool) : ℂ := if odd then 9/16 else 1/16

theorem level_bottom (m : ℕ) (odd : Bool) :
    ((levelT (rank (latP m)) odd.toNat : ℚ) : ℂ) = bottom odd := by
  rw [rank_latP]
  cases odd <;> norm_num [bottom, levelT]

theorem fourModules_lowest (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    IsLowestWeight (fourModules m hm t odd) (bottom odd) := by
  intro α hα
  obtain ⟨d, rfl, hd⟩ := parityModule_weight_support
    (latP m) (latP_even m) (charge m t) (latP_posDef m hm) odd α hα
  rw [rank_latP]
  rw [Nat.even_iff] at hd
  refine ⟨d / 2, ?_⟩
  cases odd
  · have hd' : d = 2 * (d / 2) := by simp only [Bool.toNat_false, add_zero] at hd; omega
    have he : (d : ℂ) = 2 * (d / 2 : ℕ) := by exact_mod_cast hd'
    norm_num [bottom, levelT]
    rw [he]
    ring
  · have hd' : d = 2 * (d / 2) + 1 := by simp only [Bool.toNat_true] at hd; omega
    have he : (d : ℂ) = 2 * (d / 2 : ℕ) + 1 := by exact_mod_cast hd'
    norm_num [bottom, levelT]
    rw [he]
    ring

theorem fourModules_top_finrank (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    Module.finrank ℂ ((fourModules m hm t odd).weight (bottom odd)) = 1 := by
  rw [← level_bottom m odd]
  change Module.finrank ℂ ((parityModule (latP m) (latP_even m) (charge m t)
    (latP_posDef m hm) odd).weight _) = _
  rw [finrank_parityModule_weight_level _ _ _ _ _ _ (show Even (odd.toNat + odd.toNat) from ⟨odd.toNat, rfl⟩), rank_latP]
  change twCount 1 odd.toNat * Module.finrank ℂ ℂ = 1
  cases odd <;> simp [twCount_zero, twCount_one]

/-- A coordinate on the actual lowest-weight space. -/
def topCoordinate (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    (fourModules m hm t odd).weight (bottom odd) ≃ₗ[ℂ] ℂ := by
  haveI := (fourModules m hm t odd).finrank (bottom odd)
  exact LinearEquiv.ofFinrankEq _ _ (by rw [fourModules_top_finrank, Module.finrank_self])

/-- These are algebra homomorphisms on the genuine Zhu quotient. E values are
not part of this constructor's specification. -/
def topCharacter (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ :=
  PlusCharacterTable.topCharacter (fourModules m hm t odd)
    (fourModules_lowest m hm t odd) (topCoordinate m hm t odd)

end VOA.Classification.COne.PlusTwistLattice
