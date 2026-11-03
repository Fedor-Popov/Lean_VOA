import VOA.Classification.COne.OrbIcoVKernelComparison
import VOA.Classification.COne.OrbIcoVFockFlat

/-! Actual c=1 coefficient kernels for the self channel and its Fock
realization. Both are the same proved Virasoro Gram kernel. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco
  VOA.VirasoroScreening InverseDS.VirasoroVerma HeisenbergN MvPolynomial

theorem Wi_charge_one : Wi.centralCharge=1 := by
  change (V2m 1 le_rfl).centralCharge=1
  simpa using V2m_centralCharge 1 le_rfl

theorem Xico_seedMap_kernel_level (m : ℕ) :
    sortedSpan Wi.centralCharge ((36:ℤ):ℂ) (13+m) ⊓
      LinearMap.ker (seedMap Wi 36 Xico OrbIcoZ.X_primary) =
      vermaRadicalLevel Wi.centralCharge ((36:ℤ):ℂ) (13+m) := by
  exact killed_bsa_kernel_eq_radicalLevel _ _ Wi_charge_one (by norm_num)
    (seedMap Wi 36 Xico OrbIcoZ.X_primary) Wi.L
    (seedMap_mode Wi 36 Xico OrbIcoZ.X_primary)
    (seedMap_kernel_le_radical Wi 36 Xico OrbIcoZ.X_primary OrbIcoS.Xico_ne_zero)
    Xico_seedMap_s13_zero m

theorem familyMap_one_kernel_level (m : ℕ) :
    sortedSpan (familyCharge 1) (familyWeight 1) (13+m) ⊓ LinearMap.ker (familyMap 1) =
      vermaRadicalLevel (familyCharge 1) (familyWeight 1) (13+m) := by
  apply killed_bsa_kernel_eq_radicalLevel _ _
    (by norm_num [familyCharge, familyBackground])
    (by norm_num [familyWeight, familyMomentum, familyBackground])
    (familyMap 1) (InverseDS.LeeYangFockVirasoro.sectorVirasoro (familyBackground 1) (familyMomentum 1))
  · intro k u
    exact chargedFockMap_mode _ _ k u
  · intro v hv
    exact chargedFockMap_kernel_radical _ _ v hv
  · simpa only [familyBSASource, one_pow] using family_fock_s13_zero 1 one_ne_zero

theorem Xico_seedMap_coefficient_kernel (m : ℕ) (a : VermaPartitions (13+m) → ℂ) :
    seedMap Wi 36 Xico OrbIcoZ.X_primary
      (vermaLevelState Wi.centralCharge ((36:ℤ):ℂ) (13+m) a)=0 ↔
      (vermaGramMatrix 1 36 (13+m)).mulVec a=0 := by
  have hg : vermaGramMatrix Wi.centralCharge ((36:ℤ):ℂ) (13+m) =
      vermaGramMatrix 1 36 (13+m) := by
    rw [Wi_charge_one, show ((36:ℤ):ℂ)=(36:ℂ) by norm_num]
  rw [← hg, vermaGramMatrix_kernel_iff_radical]
  have hlev := vermaLevelState_mem Wi.centralCharge ((36:ℤ):ℂ) (13+m) a
  constructor
  · intro hz
    have hm : vermaLevelState Wi.centralCharge ((36:ℤ):ℂ) (13+m) a ∈
        sortedSpan Wi.centralCharge ((36:ℤ):ℂ) (13+m) ⊓
        LinearMap.ker (seedMap Wi 36 Xico OrbIcoZ.X_primary) := ⟨hlev,hz⟩
    rw [Xico_seedMap_kernel_level] at hm
    exact hm.2
  · intro hz
    have hm : vermaLevelState Wi.centralCharge ((36:ℤ):ℂ) (13+m) a ∈
        vermaRadicalLevel Wi.centralCharge ((36:ℤ):ℂ) (13+m) := ⟨hlev,hz⟩
    rw [← Xico_seedMap_kernel_level] at hm
    exact hm.2

theorem familyMap_one_coefficient_kernel (m : ℕ) (a : VermaPartitions (13+m) → ℂ) :
    familyMap 1 (vermaLevelState (familyCharge 1) (familyWeight 1) (13+m) a)=0 ↔
      (vermaGramMatrix 1 36 (13+m)).mulVec a=0 := by
  have hg : vermaGramMatrix (familyCharge 1) (familyWeight 1) (13+m) =
      vermaGramMatrix 1 36 (13+m) := by
    have hc : familyCharge 1=1 := by norm_num [familyCharge, familyBackground]
    have hh : familyWeight 1=36 := by norm_num [familyWeight, familyMomentum, familyBackground]
    rw [hc,hh]
  rw [← hg, vermaGramMatrix_kernel_iff_radical]
  have hlev := vermaLevelState_mem (familyCharge 1) (familyWeight 1) (13+m) a
  constructor
  · intro hz
    have hm : vermaLevelState (familyCharge 1) (familyWeight 1) (13+m) a ∈
        sortedSpan (familyCharge 1) (familyWeight 1) (13+m) ⊓ LinearMap.ker (familyMap 1) :=
      ⟨hlev,hz⟩
    rw [familyMap_one_kernel_level] at hm
    exact hm.2
  · intro hz
    have hm : vermaLevelState (familyCharge 1) (familyWeight 1) (13+m) a ∈
        vermaRadicalLevel (familyCharge 1) (familyWeight 1) (13+m) := ⟨hlev,hz⟩
    rw [← familyMap_one_kernel_level] at hm
    exact hm.2

theorem Xico_Fock_coefficient_relations (m : ℕ) (a : VermaPartitions (13+m) → ℂ) :
    seedMap Wi 36 Xico OrbIcoZ.X_primary
      (vermaLevelState Wi.centralCharge ((36:ℤ):ℂ) (13+m) a)=0 ↔
      familyMap 1 (vermaLevelState (familyCharge 1) (familyWeight 1) (13+m) a)=0 :=
  (Xico_seedMap_coefficient_kernel m a).trans (familyMap_one_coefficient_kernel m a).symm

end VOA.Classification.COne.OrbIcoV
