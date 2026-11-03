import VOA.Classification.COne.OrbIcoVVacActualKernel

/-! Actual VOA/Fock PBW coefficient relations in every relative level,
including the nonsingular levels below the first-row source. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco
  VOA.VirasoroScreening InverseDS.VirasoroVerma HeisenbergN
open scoped Classical
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem properMap_coefficient_kernel_of_det (c h : ℂ) (f : Verma c h →ₗ[ℂ] V)
    (hker : LinearMap.ker f ≤ vermaRadical c h) (N : ℕ)
    (hd : (vermaGramMatrix c h N).det ≠ 0) (a : VermaPartitions N → ℂ) :
    f (vermaLevelState c h N a)=0 ↔ a=0 := by
  constructor
  · intro hz
    apply (vermaLevelState_eq_zero_iff c h N a).mp
    exact verma_radical_zero_of_det_ne_zero c h N hd _
      (vermaLevelState_mem c h N a) (hker hz)
  · intro hz
    rw [hz,(vermaLevelState_eq_zero_iff c h N 0).mpr rfl,map_zero]

theorem Xico_Fock_coefficient_relations_all (N : ℕ) (a : VermaPartitions N → ℂ) :
    seedMap Wi 36 Xico OrbIcoZ.X_primary
      (vermaLevelState Wi.centralCharge ((36:ℤ):ℂ) N a)=0 ↔
      familyMap 1 (vermaLevelState (familyCharge 1) (familyWeight 1) N a)=0 := by
  by_cases hN : N<13
  · have hd (c h : ℂ) (hc : c=1) (hh : h=36) : (vermaGramMatrix c h N).det ≠ 0 := by
      subst c
      subst h
      convert vermaGramMatrix_one_sq_det_ne_zero 6 (by omega : N≤2*6) using 1 <;> norm_num
    have hs := properMap_coefficient_kernel_of_det _ _
      (seedMap Wi 36 Xico OrbIcoZ.X_primary)
      (seedMap_kernel_le_radical Wi 36 Xico OrbIcoZ.X_primary OrbIcoS.Xico_ne_zero) N
      (hd _ _ Wi_charge_one (by norm_num)) a
    have hf := properMap_coefficient_kernel_of_det _ _ (familyMap 1)
      (by intro v hv; exact chargedFockMap_kernel_radical _ _ v hv) N
      (hd _ _ (by norm_num [familyCharge,familyBackground])
        (by norm_num [familyWeight,familyBackground,familyMomentum])) a
    exact hs.trans hf.symm
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 13≤N)
    exact Xico_Fock_coefficient_relations m a

theorem vacuum_Fock_coefficient_relations_all (N : ℕ) (a : VermaPartitions N → ℂ) :
    seedMap Wi 0 Wi.vacuum (vacuum_mem_prim Wi)
      (vermaLevelState Wi.centralCharge ((0:ℤ):ℂ) N a)=0 ↔
      vacFamilyMap 1 (vermaLevelState (familyCharge 1) (vacFamilyWeight 1) N a)=0 := by
  by_cases hN : N=0
  · subst N
    have hd (c h : ℂ) : (vermaGramMatrix c h 0).det ≠ 0 := by
      rw [vermaGramMatrix_zero_det]
      exact one_ne_zero
    have hs := properMap_coefficient_kernel_of_det _ _
      (seedMap Wi 0 Wi.vacuum (vacuum_mem_prim Wi))
      (seedMap_kernel_le_radical Wi 0 Wi.vacuum (vacuum_mem_prim Wi) vacuum_seed_ne_zero)
      0 (hd _ _) a
    have hf := properMap_coefficient_kernel_of_det _ _ (vacFamilyMap 1)
      (by intro v hv; exact chargedFockMap_kernel_radical _ _ v hv) 0 (hd _ _) a
    exact hs.trans hf.symm
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1≤N)
    exact vacuum_Fock_coefficient_relations m a

end VOA.Classification.COne.OrbIcoV
