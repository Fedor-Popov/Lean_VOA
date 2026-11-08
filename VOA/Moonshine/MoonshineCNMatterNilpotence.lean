import VOA.Moonshine.MoonshineCNChargeNilpotence
import VOA.Moonshine.MoonshineCNSectorVirasoroComparison
import VOA.Moonshine.MoonshineCNMonsterGrading
import VOA.Moonshine.MoonshineCNVnatSectorGrading

/-! Local nilpotence and the charge-sensitive cutoff on the actual matter NearVOA. -/

namespace VOA.Moonshine.ConwayNorton

open IntegralLattice LatGen

/-- The matter sector has ground energy `LatGen.halfNorm α`, including negative ground energies. -/
theorem moonshineMatterMomentum_weight_below_halfNorm (α : lorentzianLattice.carrier)
    (N : ℤ) (hN : N < LatGen.halfNorm lorentzianLattice α) :
    moonshineMatterMomentum α ⊓ moonshineMatterNearVOA.grading N = ⊥ := by
  have hα : α = ![α 0, α 1] := by funext i; fin_cases i <;> rfl
  rw [hα] at hN ⊢
  rw [lorentzian_halfNorm] at hN
  change N < α 0 * α 1 at hN
  apply bot_unique
  intro u hu
  have hw := (moonshineMatterSector_weight_iff (α 0) (α 1) N
    (moonshineMatterSectorInverse ![α 0, α 1] u)).mp
      ((moonshineMatterSector_rightInverse _ u hu.1).symm ▸ hu.2)
  rw [vnatSectorWeight_negative _ _ _ hN, Submodule.mem_bot] at hw
  have he := moonshineMatterSector_rightInverse _ u hu.1
  rw [hw, map_zero] at he
  exact he.symm

theorem moonshineMatterMomentum_weight_span :
    (⨆ α, ⨆ N, moonshineMatterMomentum α ⊓ moonshineMatterNearVOA.grading N) = ⊤ := by
  classical
  apply top_unique
  rw [← moonshineMatterMomentum_isInternal.submodule_iSup_eq_top]
  refine iSup_le fun α => ?_
  intro u hu
  have hα : α = ![α 0, α 1] := by funext i; fin_cases i <;> rfl
  rw [hα] at hu
  rw [← moonshineMatterSector_rightInverse _ u hu]
  generalize moonshineMatterSectorInverse ![α 0, α 1] u = v
  have hw : v ∈ ⨆ N, vnatSectorWeight (α 0) (α 1) N := by
    rw [vnatSectorWeight_top]
    trivial
  induction hw using Submodule.iSup_induction' with
  | mem N v hv =>
      exact Submodule.mem_iSup_of_mem ![α 0, α 1] (Submodule.mem_iSup_of_mem N
        ⟨moonshineMatterSectorMap_mem _ _,
          (moonshineMatterSector_weight_iff _ _ _ v).mpr hv⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw

/-- Every power beyond matter/oscillator level vanishes at fixed weight and charge. -/
theorem moonshineMatterVirasoroOne_pow_eq_zero (α : lorentzianLattice.carrier)
    {N : ℤ} {u : moonshineMatterSpace} (hu : u ∈ moonshineMatterNearVOA.grading N)
    (hα : u ∈ moonshineMatterMomentum α) (k : ℕ)
    (hk : (N - LatGen.halfNorm lorentzianLattice α).toNat < k) :
    (moonshineMatterNearVOA.L 1 ^ k) u = 0 :=
  moonshineMatterNearVOA.virasoroOne_pow_zero_of_lower_bound
    (moonshineMatterMomentum α) (LatGen.halfNorm lorentzianLattice α)
    (moonshineMatterVirasoro_momentum 1 α)
    (moonshineMatterMomentum_weight_below_halfNorm α) hu hα k hk

/-- The requested explicit finite cutoff on the actual reconstructed matter algebra. -/
theorem moonshineMatterVirasoroOne_cutoff (α : lorentzianLattice.carrier)
    {N : ℤ} {u : moonshineMatterSpace} (hu : u ∈ moonshineMatterNearVOA.grading N)
    (hα : u ∈ moonshineMatterMomentum α) :
    (moonshineMatterNearVOA.L 1 ^ ((N - LatGen.halfNorm lorentzianLattice α).toNat + 1)) u = 0 :=
  moonshineMatterVirasoroOne_pow_eq_zero α hu hα _ (Nat.lt_succ_self _)

theorem moonshineMatterVirasoroOne_locallyNilpotent (u : moonshineMatterSpace) :
    ∃ k : ℕ, (moonshineMatterNearVOA.L 1 ^ k) u = 0 :=
  moonshineMatterNearVOA.virasoroOne_locallyNilpotent_of_weight_sectors
    moonshineMatterMomentum (LatGen.halfNorm lorentzianLattice)
    (fun α => moonshineMatterVirasoro_momentum 1 α)
    moonshineMatterMomentum_weight_below_halfNorm moonshineMatterMomentum_weight_span u

end VOA.Moonshine.ConwayNorton
