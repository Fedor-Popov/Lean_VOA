import VOA.Moonshine.MoonshineCNTensorRealization
import VOA.Moonshine.MoonshineCNMomentum

/-! The internal `II_{1,1}` grading of the actual central-charge-26 tensor algebra. -/

namespace VOA.Moonshine.ConwayNorton

open scoped TensorProduct Classical
open Module (End)
open IntegralLattice LatGen HeisenbergN AutMonster

/-- An injective complex label for the two integer coordinates, used only to prove independence. -/
noncomputable def lorentzianChargeLabel (α : lorentzianLattice.carrier) : ℂ :=
  (α 0 : ℂ) + Complex.I * (α 1 : ℂ)

theorem lorentzianChargeLabel_injective : Function.Injective lorentzianChargeLabel := by
  intro α β h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [lorentzianChargeLabel] at hr hi
  apply funext
  intro i
  fin_cases i
  · exact_mod_cast hr
  · exact_mod_cast hi

noncomputable def lorentzianChargeDiagonal : End ℂ (lorentzianLattice.carrier →₀ ℂ) :=
  Finsupp.lsum ℂ fun α => lorentzianChargeLabel α • Finsupp.lsingle α

theorem lorentzianChargeDiagonal_single (α : lorentzianLattice.carrier) :
    lorentzianChargeDiagonal (eGen lorentzianLattice α) =
      lorentzianChargeLabel α • eGen lorentzianLattice α := by
  simp [lorentzianChargeDiagonal, eGen, Finsupp.lsum_single]

noncomputable def lorentzianLatticeMomentumOperator : End ℂ LorentzianFockSpace :=
  LinearMap.lTensor (FockN (rank lorentzianLattice)) lorentzianChargeDiagonal

theorem lorentzianLatticeMomentumOperator_eigen (α : lorentzianLattice.carrier)
    {v : LorentzianFockSpace} (hv : v ∈ latticeMomentumGrading lorentzianLattice α) :
    lorentzianLatticeMomentumOperator v = lorentzianChargeLabel α • v := by
  rw [latticeMomentumGrading_eq_range] at hv
  obtain ⟨p, rfl⟩ := hv
  change LinearMap.lTensor _ lorentzianChargeDiagonal (p ⊗ₜ eGen lorentzianLattice α) = _
  rw [LinearMap.lTensor_tmul, lorentzianChargeDiagonal_single]
  exact TensorProduct.tmul_smul _ _ _

/-- Momentum comes from the lattice factor; all of `V♮` has zero momentum. -/
noncomputable def moonshineMatterMomentum (α : lorentzianLattice.carrier) : Submodule ℂ moonshineMatterSpace :=
  TensorVA.tenSub (⊤ : Submodule ℂ Vnat) (latticeMomentumGrading lorentzianLattice α)

theorem moonshineMatterMomentum_tmul (α : lorentzianLattice.carrier) (a : Vnat)
    {b : LorentzianFockSpace} (hb : b ∈ latticeMomentumGrading lorentzianLattice α) :
    a ⊗ₜ[ℂ] b ∈ moonshineMatterMomentum α :=
  TensorVA.tmul_mem_tenSub (Submodule.mem_top) hb

theorem moonshineMatterMomentum_eigen (α : lorentzianLattice.carrier) :
    moonshineMatterMomentum α ≤
      Module.End.eigenspace (LinearMap.lTensor Vnat lorentzianLatticeMomentumOperator)
        (lorentzianChargeLabel α) := by
  intro u hu
  rw [Module.End.mem_eigenspace_iff]
  refine TensorVA.tenSub_induction (P := ⊤)
    (Q := latticeMomentumGrading lorentzianLattice α)
    (motive := fun u => LinearMap.lTensor Vnat lorentzianLatticeMomentumOperator u =
      lorentzianChargeLabel α • u) ?_ ?_ ?_ ?_ hu
  · simp
  · intro x y hx hy; simp only [map_add, hx, hy, smul_add]
  · intro c x hx; simp only [map_smul, hx, smul_comm c]
  · intro a _ b hb
    rw [LinearMap.lTensor_tmul, lorentzianLatticeMomentumOperator_eigen α hb]
    exact TensorProduct.tmul_smul _ _ _

theorem moonshineMatterMomentum_isInternal : DirectSum.IsInternal moonshineMatterMomentum := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact ((Module.End.eigenspaces_iSupIndep
      (LinearMap.lTensor Vnat lorentzianLatticeMomentumOperator)).comp
      lorentzianChargeLabel_injective).mono moonshineMatterMomentum_eigen
  · apply TensorVA.eq_top_of_tmul_mem (P := fun _ : Unit => (⊤ : Submodule ℂ Vnat))
      (Q := latticeMomentumGrading lorentzianLattice) (by simp)
      ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
        (latticeMomentumGrading_isInternal lorentzianLattice)).2
    intro _ α a _ b hb
    exact Submodule.mem_iSup_of_mem α (moonshineMatterMomentum_tmul α a hb)

/-- Every actual tensor vertex mode adds its two lattice momenta. -/
theorem moonshineMatterMomentum_mode (α β : lorentzianLattice.carrier)
    (u v : moonshineMatterSpace) (hu : u ∈ moonshineMatterMomentum α)
    (hv : v ∈ moonshineMatterMomentum β) (n : ℤ) :
    mode (moonshineMatterNearVOA.Y u) n v ∈ moonshineMatterMomentum (α + β) := by
  change nearTensorCoefficient VnatVOA.toNearVOA lorentzianNearVOA (-n - 1) u v ∈ _
  let C := nearTensorCoefficient VnatVOA.toNearVOA lorentzianNearVOA (-n - 1)
  change C u v ∈ _
  refine TensorVA.tenSub_induction (P := ⊤)
    (Q := latticeMomentumGrading lorentzianLattice α)
    (motive := fun u => C u v ∈ moonshineMatterMomentum (α + β)) ?_ ?_ ?_ ?_ hu
  · dsimp only
    rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  · intro x y hx hy; rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  · intro c x hx; rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c hx
  · intro a _ b hb
    refine TensorVA.tenSub_induction (P := ⊤)
      (Q := latticeMomentumGrading lorentzianLattice β)
      (motive := fun v => C (a ⊗ₜ b) v ∈ moonshineMatterMomentum (α + β)) ?_ ?_ ?_ ?_ hv
    · dsimp only
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
    · intro a' _ b' hb'
      change moonshineMatterNearVOA.Y (a ⊗ₜ b) (-n - 1) (a' ⊗ₜ b') ∈ _
      rw [moonshineMatterNearVOA_tmul_field]
      apply tensorFinsum_mem
      intro m
      apply moonshineMatterMomentum_tmul
      have h := lorentzianNearVOA_momentum α β b b' hb hb' (-(-n - 1 - m) - 1)
      simpa only [mode_apply,
        show -(-(-n - 1 - m) - 1) - 1 = -n - 1 - m from by omega] using h

end VOA.Moonshine.ConwayNorton
