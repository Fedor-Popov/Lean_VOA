import VOA.Classification.COne.OrbIcoVVacKernel

/-! The actual vacuum VOA and c=1 Fock realization have precisely the
same finite PBW coefficient relations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco
  VOA.VirasoroScreening InverseDS.VirasoroVerma HeisenbergN MvPolynomial

theorem vacuum_seedMap_coefficient_kernel (m : ℕ) (a : VermaPartitions (1+m) → ℂ) :
    seedMap Wi 0 Wi.vacuum (vacuum_mem_prim Wi)
      (vermaLevelState Wi.centralCharge ((0:ℤ):ℂ) (1+m) a)=0 ↔
      (vermaGramMatrix 1 0 (1+m)).mulVec a=0 := by
  have hg : vermaGramMatrix Wi.centralCharge ((0:ℤ):ℂ) (1+m) =
      vermaGramMatrix 1 0 (1+m) := by
    rw [Wi_charge_one, show ((0:ℤ):ℂ)=(0:ℂ) by norm_num]
  rw [← hg, vermaGramMatrix_kernel_iff_radical]
  have hlev := vermaLevelState_mem Wi.centralCharge ((0:ℤ):ℂ) (1+m) a
  constructor
  · intro hz
    have hm : vermaLevelState Wi.centralCharge ((0:ℤ):ℂ) (1+m) a ∈
        sortedSpan Wi.centralCharge ((0:ℤ):ℂ) (1+m) ⊓
        LinearMap.ker (seedMap Wi 0 Wi.vacuum (vacuum_mem_prim Wi)) := ⟨hlev,hz⟩
    rw [vacuum_seedMap_kernel_level] at hm
    exact hm.2
  · intro hz
    have hm : vermaLevelState Wi.centralCharge ((0:ℤ):ℂ) (1+m) a ∈
        vermaRadicalLevel Wi.centralCharge ((0:ℤ):ℂ) (1+m) := ⟨hlev,hz⟩
    rw [← vacuum_seedMap_kernel_level] at hm
    exact hm.2

theorem vacFamilyMap_one_coefficient_kernel (m : ℕ) (a : VermaPartitions (1+m) → ℂ) :
    vacFamilyMap 1 (vermaLevelState (familyCharge 1) (vacFamilyWeight 1) (1+m) a)=0 ↔
      (vermaGramMatrix 1 0 (1+m)).mulVec a=0 := by
  have hg : vermaGramMatrix (familyCharge 1) (vacFamilyWeight 1) (1+m) =
      vermaGramMatrix 1 0 (1+m) := by
    have hc : familyCharge 1=1 := by norm_num [familyCharge, familyBackground]
    have hh : vacFamilyWeight 1=0 := by norm_num [vacFamilyWeight, vacFamilyMomentum, familyBackground]
    rw [hc,hh]
  rw [← hg, vermaGramMatrix_kernel_iff_radical]
  have hlev := vermaLevelState_mem (familyCharge 1) (vacFamilyWeight 1) (1+m) a
  constructor
  · intro hz
    have hm : vermaLevelState (familyCharge 1) (vacFamilyWeight 1) (1+m) a ∈
        sortedSpan (familyCharge 1) (vacFamilyWeight 1) (1+m) ⊓ LinearMap.ker (vacFamilyMap 1) :=
      ⟨hlev,hz⟩
    rw [vacFamilyMap_one_kernel_level] at hm
    exact hm.2
  · intro hz
    have hm : vermaLevelState (familyCharge 1) (vacFamilyWeight 1) (1+m) a ∈
        vermaRadicalLevel (familyCharge 1) (vacFamilyWeight 1) (1+m) := ⟨hlev,hz⟩
    rw [← vacFamilyMap_one_kernel_level] at hm
    exact hm.2

theorem vacuum_Fock_coefficient_relations (m : ℕ) (a : VermaPartitions (1+m) → ℂ) :
    seedMap Wi 0 Wi.vacuum (vacuum_mem_prim Wi)
      (vermaLevelState Wi.centralCharge ((0:ℤ):ℂ) (1+m) a)=0 ↔
      vacFamilyMap 1 (vermaLevelState (familyCharge 1) (vacFamilyWeight 1) (1+m) a)=0 :=
  (vacuum_seedMap_coefficient_kernel m a).trans (vacFamilyMap_one_coefficient_kernel m a).symm


end VOA.Classification.COne.OrbIcoV
