import VOA.Moonshine.MoonshineCNNearNilpotence
import VOA.Moonshine.MoonshineCNMomentum
import VOA.Core.DeformationLiftedModes

/-! The precise oscillator-level cutoff for the reconstructed lattice fields. -/

namespace VOA.Moonshine.ConwayNorton

open IntegralLattice LatGen HeisenbergN

/-- Fixing total weight and charge recovers exactly one oscillator weight. -/
theorem latticeMomentum_weight_intersection (L : IntegralLattice) (α : L.carrier) (N : ℤ) :
    latticeMomentumGrading L α ⊓ gradingLatGen L N =
      bigradα L (N - halfNorm L α, α) := by
  have h := VOA.Deform.iSup_inf_eq_of_le_independent
    (p := fun w => bigradα L (w, α))
    (q := fun w => gradingLatGen L (w + halfNorm L α))
    (fun w => bigradα_le_gradingLatGen L w α)
    ((latticeWeightGrading_independent L).comp
      (fun a b h => add_right_cancel h)) (N - halfNorm L α)
  simpa only [latticeMomentumGrading, sub_add_cancel] using h

theorem latticeMomentum_weight_below_halfNorm (L : IntegralLattice)
    (α : L.carrier) (N : ℤ) (hN : N < halfNorm L α) :
    latticeMomentumGrading L α ⊓ gradingLatGen L N = ⊥ := by
  rw [latticeMomentum_weight_intersection,
    bigradα_eq_bot_of_neg L α (sub_neg.mpr hN)]

theorem latticeMomentum_weight_span (L : IntegralLattice) :
    (⨆ α, ⨆ N, latticeMomentumGrading L α ⊓ gradingLatGen L N) = ⊤ := by
  apply top_unique
  rw [← bigradα_iSup_eq_top L]
  refine iSup_le fun p => ?_
  apply le_iSup_of_le p.2
  apply le_iSup_of_le (p.1 + halfNorm L p.2)
  rw [latticeMomentum_weight_intersection, add_sub_cancel_right]

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem frameVirasoroMode_preserves_momentum (α : L.carrier) (n : ℤ)
    {u : LatModuleGen L} (hu : u ∈ latticeMomentumGrading L α) :
    frameVirasoroMode F n u ∈ latticeMomentumGrading L α := by
  rw [latticeMomentumGrading_eq_range] at hu
  obtain ⟨p, rfl⟩ := hu
  rw [show mkEα L α p = latStateGen L p α from rfl, frameVirasoroMode_tmul]
  apply Submodule.add_mem
  · exact Submodule.add_mem _ (latState_mem_momentum L _ _) (latState_mem_momentum L _ _)
  · split_ifs
    · exact Submodule.smul_mem _ _ (latState_mem_momentum L _ _)
    · exact Submodule.zero_mem _

theorem frameVirasoroMode_mem_weight (hEven : L.Even) {N : ℤ} {u : LatModuleGen L}
    (hu : u ∈ gradingLatGen L N) (n : ℤ) :
    frameVirasoroMode F n u ∈ gradingLatGen L (N - n) := by
  rw [← mode_frameStateField_omega_eq_frameVirasoroMode F hEven]
  simpa only [show 2 + N - (n + 1) - 1 = N - n by ring] using
    frameStateField_grading_mode F hEven (latticeConformalVector L)
      (latticeConformalVector_mem L) u hu (n + 1)

/-- All powers at or above the charge-sensitive cutoff vanish. -/
theorem frameVirasoroOne_pow_eq_zero (hEven : L.Even) (α : L.carrier)
    {N : ℤ} {u : LatModuleGen L} (hu : u ∈ gradingLatGen L N)
    (hα : u ∈ latticeMomentumGrading L α) (k : ℕ)
    (hk : (N - halfNorm L α).toNat < k) : (frameVirasoroMode F 1 ^ k) u = 0 := by
  have hmem : ∀ j : ℕ, (frameVirasoroMode F 1 ^ j) u ∈
      latticeMomentumGrading L α ⊓ gradingLatGen L (N - (j : ℤ)) := by
    intro j
    induction j with
    | zero => simpa using And.intro hα hu
    | succ j ih =>
        rw [pow_succ', Module.End.mul_apply]
        constructor
        · exact frameVirasoroMode_preserves_momentum F α 1 ih.1
        · simpa only [Nat.cast_succ, sub_add_eq_sub_sub] using
            frameVirasoroMode_mem_weight F hEven ih.2 1
  have hz := hmem k
  rw [latticeMomentum_weight_below_halfNorm L α _ (by omega), Submodule.mem_bot] at hz
  exact hz

/-- Local nilpotence on arbitrary finite sums of charges and oscillator weights. -/
theorem lorentzianVirasoroOne_locallyNilpotent (u : LorentzianFockSpace) :
    ∃ k : ℕ, (lorentzianNearVOA.L 1 ^ k) u = 0 := by
  apply lorentzianNearVOA.virasoroOne_locallyNilpotent_of_weight_sectors
    (latticeMomentumGrading lorentzianLattice) (halfNorm lorentzianLattice)
    (fun α v hv => ?_) (latticeMomentum_weight_below_halfNorm lorentzianLattice)
    (latticeMomentum_weight_span lorentzianLattice) u
  change mode (frameStateField lorentzianComplexFrame lorentzian_even
    (latticeConformalVector lorentzianLattice)) (1 + 1) v ∈ _
  rw [mode_frameStateField_omega_eq_frameVirasoroMode]
  exact frameVirasoroMode_preserves_momentum lorentzianComplexFrame α 1 hv

end VOA.Moonshine.ConwayNorton
