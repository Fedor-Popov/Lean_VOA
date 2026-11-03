import VOA.Classification.COne.OrbIcoVSpecializeFinal
import VOA.Classification.COne.OrbIcoVActualSpecializationChannels

/-! Specialized actual Ward solutions coincide with the genuine projected self-product. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco OrbIcoT OrbC2c
  InverseDS.VirasoroVerma HeisenbergN VOA.VirasoroScreening
  InverseDS.LeeYangFockVirasoro MvPolynomial
open scoped Classical

def finiteActualSequence (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (v : FiniteFockColumns self R → ℂ) (n : ℕ) : (orbifold ico).carrier :=
  if hn : n≤R then actualFiberMap self (finiteBlockVerma self R a 1 ⟨n,by omega⟩ v) else 0

theorem finiteActualSequence_grading (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (v : FiniteFockColumns self R → ℂ) (n : ℕ) (hn : n≤R) :
    finiteActualSequence self R a v n∈Wi.grading (actualChannelWeight self+(n:ℤ)) := by
  obtain ⟨b,hb⟩ := exists_vermaLevelState (familyCharge 1) (symbolFamilyWeight self 1) n
    (finiteBlockVerma self R a 1 ⟨n,by omega⟩ v)
    (finiteBlockVerma_level self R a 1 ⟨n,by omega⟩ v)
  simp only [finiteActualSequence,dif_pos hn]
  rw [← hb,actualFiberMap_levelState]
  exact actualLevelState_grading self n b

theorem finiteActualSequence_vacuum_spin (R : ℕ) (a : FiniteFockPBW false R)
    (v : FiniteFockColumns false R → ℂ) (n : ℕ) (hn : n≤R) :
    spinCasimir (finiteActualSequence false R a v n : Sp)=0 := by
  obtain ⟨b,hb⟩ := exists_vermaLevelState (familyCharge 1) (symbolFamilyWeight false 1) n
    (finiteBlockVerma false R a 1 ⟨n,by omega⟩ v)
    (finiteBlockVerma_level false R a 1 ⟨n,by omega⟩ v)
  simp only [finiteActualSequence,dif_pos hn]
  rw [← hb,actualFiberMap_levelState]
  simp only [actualLevelState,actualChannelSeed,Bool.false_eq_true,if_false,map_sum,map_smul,
    Submodule.coe_sum,Submodule.coe_smul,spinCasimir_word_vacuum,smul_zero,Finset.sum_const_zero]

theorem finiteActualSequence_ground (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (v : FiniteFockColumns self R → ℂ)
    (hv : finiteBlockProbe self R a ⟨0,by omega⟩ v=1) :
    finiteActualSequence self R a v 0=actualChannelSeed self := by
  have hg := zero_level_probe (familyCharge 1) (symbolFamilyWeight self 1)
    (finiteBlockVerma self R a 1 ⟨0,by omega⟩ v)
    (finiteBlockVerma_level self R a 1 ⟨0,by omega⟩ v)
  rw [finiteBlockProbe_sound,hv,one_smul] at hg
  simp only [finiteActualSequence,dif_pos (by omega : 0≤R)]
  rw [hg,actualFiberMap_highest]

theorem finiteActualSequence_first (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (v : FiniteFockColumns self R → ℂ) (hrows : finiteWardRowMap self R a 1 v=0)
    (n : ℕ) (hpos : 0<n) (hn : n≤R) :
    Wi.L 1 (finiteActualSequence self R a v n) =
      (symbolFamilyWeight self 1+((n-1:ℕ):ℂ)) • finiteActualSequence self R a v (n-1) := by
  have hd := ((finiteWardRowMap_eq_zero_iff self R a 1 v).mp hrows).1 ⟨n-1,by omega⟩
  have hF : sectorVirasoro (familyBackground 1) (symbolFamilyMomentum self 1) 1
      (finiteBlockFock self R a 1 ⟨n,by omega⟩ v) =
      (symbolFamilyWeight self 1+((n-1:ℕ):ℂ)) •
        finiteBlockFock self R a 1 ⟨n-1,by omega⟩ v := by
    have he : n-1+1=n := by omega
    simpa only [finiteFirstDefect,LinearMap.sub_apply,LinearMap.comp_apply,
      LinearMap.smul_apply,he] using sub_eq_zero.mp hd
  simp only [finiteActualSequence,dif_pos hn,dif_pos (by omega : n-1≤R)]
  exact actualFiberMap_positive_ward self n 1 (by omega) _ _ _
    (finiteBlockVerma_level self R a 1 ⟨n,by omega⟩ v)
    (finiteBlockVerma_level self R a 1 ⟨n-1,by omega⟩ v) hF

theorem finiteActualSequence_second (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (v : FiniteFockColumns self R → ℂ) (hrows : finiteWardRowMap self R a 1 v=0)
    (n : ℕ) (hpos : 0<n) (hn : n≤R) :
    Wi.L 2 (finiteActualSequence self R a v n) =
      if 2≤n then (symbolFamilyWeight self 1+incomingWeight 1+((n-2:ℕ):ℂ)) •
        finiteActualSequence self R a v (n-2) else 0 := by
  by_cases htwo : 2≤n
  · have hd := ((finiteWardRowMap_eq_zero_iff self R a 1 v).mp hrows).2 ⟨n-2,by omega⟩
    have hF : sectorVirasoro (familyBackground 1) (symbolFamilyMomentum self 1) 2
        (finiteBlockFock self R a 1 ⟨n,by omega⟩ v) =
        (symbolFamilyWeight self 1+incomingWeight 1+((n-2:ℕ):ℂ)) •
          finiteBlockFock self R a 1 ⟨n-2,by omega⟩ v := by
      have he : n-2+2=n := by omega
      simpa only [finiteSecondDefect,LinearMap.sub_apply,LinearMap.comp_apply,
        LinearMap.smul_apply,he,one_pow] using sub_eq_zero.mp hd
    simp only [finiteActualSequence,dif_pos hn,dif_pos (by omega : n-2≤R),if_pos htwo]
    exact actualFiberMap_positive_ward self n 2 htwo _ _ _
      (finiteBlockVerma_level self R a 1 ⟨n,by omega⟩ v)
      (finiteBlockVerma_level self R a 1 ⟨n-2,by omega⟩ v) hF
  · simp only [if_neg htwo,finiteActualSequence,dif_pos hn]
    exact actualFiberMap_positive_above self n 2 (by omega) _
      (finiteBlockVerma_level self R a 1 ⟨n,by omega⟩ v)

theorem finiteActualSequence_probe (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (v : FiniteFockColumns self R → ℂ) (n : ℕ) (hn : n≤R) :
    (if self then sixthProbe else vacuumProbe) (finiteActualSequence self R a v n) =
      finiteBlockProbe self R a ⟨n,by omega⟩ v *
        (if self then OrbIcoS.neutralProbe Xico else 1) := by
  simp only [finiteActualSequence,dif_pos hn]
  rw [actualProbe_fiber self n _ (finiteBlockVerma_level self R a 1 ⟨n,by omega⟩ v),
    finiteBlockProbe_sound]

-- The comparison includes all finite grades and both positive generators.
set_option maxHeartbeats 1000000 in
theorem finiteActualSequence_matches_vacuum (R : ℕ) (hR : R<100)
    (a : FiniteFockPBW false R) (v : FiniteFockColumns false R → ℂ)
    (hv0 : finiteBlockProbe false R a ⟨0,by omega⟩ v=1)
    (hrows : finiteWardRowMap false R a 1 v=0) :
    ∀ n (hn : n≤R), (vacuumState n (by omega)).val =
      vacuumCoefficient 0 • finiteActualSequence false R a v n := by
  let c₁ : ℕ → ℂ := fun n => symbolFamilyWeight false 1+((n-1:ℕ):ℂ)
  let c₂ : ℕ → ℂ := fun n => symbolFamilyWeight false 1+incomingWeight 1+((n-2:ℕ):ℂ)
  let f : ℕ → (orbifold ico).carrier := fun n =>
    vacuumCoefficient 0 • finiteActualSequence false R a v n
  let g : ℕ → (orbifold ico).carrier := fun n =>
    if hn : n≤R then (vacuumState n (by omega)).val else 0
  have hfC (n : ℕ) (hn : n≤R) : spinCasimir (f n : Sp)=0 := by
    change spinCasimir (vacuumCoefficient 0 • (finiteActualSequence false R a v n : Sp))=0
    rw [map_smul,finiteActualSequence_vacuum_spin R a v n hn,smul_zero]
  have hgC (n : ℕ) (hn : n≤R) : spinCasimir (g n : Sp)=0 := by
    simp only [g,dif_pos hn]
    exact vacuumProjection_spin (productState n (by omega))
  have hfg (n : ℕ) (hn : n≤R) : f n∈Wi.grading (n:ℤ) := by
    exact (Wi.grading _).smul_mem _ (by
      simpa [actualChannelWeight] using finiteActualSequence_grading false R a v n hn)
  have hgg (n : ℕ) (hn : n≤R) : g n∈Wi.grading (n:ℤ) := by
    simpa only [g,dif_pos hn] using vacuumState_grading n (by omega)
  have hf1 (n : ℕ) (hp : 0<n) (hn : n≤R) : Wi.L 1 (f n)=c₁ n • f (n-1) := by
    change Wi.L 1 (vacuumCoefficient 0 • finiteActualSequence false R a v n)=_
    rw [map_smul,finiteActualSequence_first false R a v hrows n hp hn,smul_comm]
  have hg1 (n : ℕ) (hp : 0<n) (hn : n≤R) : Wi.L 1 (g n)=c₁ n • g (n-1) := by
    simp only [g,dif_pos hn,dif_pos (by omega : n-1≤R)]
    have he : (n:ℂ)+35*(1:ℂ)-36=c₁ n := by
      dsimp [c₁,symbolFamilyWeight,symbolFamilyMomentum]
      rw [Nat.cast_sub (by omega : 1≤n)]
      norm_num
      ring
    simpa only [Nat.cast_one,Nat.cast_ofNat,he] using vacuumState_positive n 1 (by omega) (by omega) (by omega)
  have hf2 (n : ℕ) (hp : 0<n) (hn : n≤R) :
      Wi.L 2 (f n)=if 2≤n then c₂ n • f (n-2) else 0 := by
    change Wi.L 2 (vacuumCoefficient 0 • finiteActualSequence false R a v n)=_
    rw [map_smul,finiteActualSequence_second false R a v hrows n hp hn]
    split_ifs with htwo
    · rw [smul_comm]
    · rw [smul_zero]
  have hg2 (n : ℕ) (hp : 0<n) (hn : n≤R) :
      Wi.L 2 (g n)=if 2≤n then c₂ n • g (n-2) else 0 := by
    simp only [g,dif_pos hn]
    by_cases htwo : 2≤n
    · rw [if_pos htwo,dif_pos (by omega : n-2≤R)]
      have he : (n:ℂ)+35*(2:ℂ)-36=c₂ n := by
        dsimp [c₂,symbolFamilyWeight,symbolFamilyMomentum,incomingWeight,vermaBSAWeight]
        rw [Nat.cast_sub htwo]
        norm_num
        ring
      simpa only [Nat.cast_one,Nat.cast_ofNat,he] using vacuumState_positive n 2 (by omega) (by omega) htwo
    · rw [if_neg htwo]
      have hz := VOA.L_mem_grading Wi (vacuumState_grading n (by omega)) 2
      rw [Wi.positivity ((n:ℤ)-2) (by omega),Submodule.mem_bot] at hz
      exact hz
  have hz : f 0=g 0 := by
    simp only [f,g,dif_pos (by omega : 0≤R),
      finiteActualSequence_ground false R a v hv0,actualChannelSeed,if_false]
    exact vacuumState_ground.symm
  have hu := vacuum_ward_sequence_unique R hR c₁ c₂ f g hfC hgC hfg hgg hf1 hg1 hf2 hg2 hz
  intro n hn
  simpa only [f,g,dif_pos hn] using (hu n hn).symm

-- The spin-six comparison retains the below-ground L₂ boundary equation.
set_option maxHeartbeats 1000000 in
theorem finiteActualSequence_matches_sixth (R : ℕ) (hR : R<64)
    (a : FiniteFockPBW true R) (v : FiniteFockColumns true R → ℂ)
    (hv0 : finiteBlockProbe true R a ⟨0,by omega⟩ v=1)
    (hrows : finiteWardRowMap true R a 1 v=0) :
    ∀ n (hn : n≤R), (sixthState (36+n) (by omega)).val =
      icoSixthCoupling • finiteActualSequence true R a v n := by
  let c₁ : ℕ → ℂ := fun n => symbolFamilyWeight true 1+((n-1:ℕ):ℂ)
  let c₂ : ℕ → ℂ := fun n => symbolFamilyWeight true 1+incomingWeight 1+((n-2:ℕ):ℂ)
  let f : ℕ → (orbifold ico).carrier := fun n =>
    icoSixthCoupling • finiteActualSequence true R a v n
  let g : ℕ → (orbifold ico).carrier := fun n =>
    if hn : n≤R then (sixthState (36+n) (by omega)).val else 0
  have hfg (n : ℕ) (hn : n≤R) : f n∈Wi.grading ((36+n:ℕ):ℤ) := by
    exact (Wi.grading _).smul_mem _ (by
      simpa [actualChannelWeight] using finiteActualSequence_grading true R a v n hn)
  have hgg (n : ℕ) (hn : n≤R) : g n∈Wi.grading ((36+n:ℕ):ℤ) := by
    simpa only [g,dif_pos hn] using sixthState_grading (36+n) (by omega)
  have hf1 (n : ℕ) (hp : 0<n) (hn : n≤R) : Wi.L 1 (f n)=c₁ n • f (n-1) := by
    change Wi.L 1 (icoSixthCoupling • finiteActualSequence true R a v n)=_
    rw [map_smul,finiteActualSequence_first true R a v hrows n hp hn,smul_comm]
  have hg1 (n : ℕ) (hp : 0<n) (hn : n≤R) : Wi.L 1 (g n)=c₁ n • g (n-1) := by
    simp only [g,dif_pos hn,dif_pos (by omega : n-1≤R)]
    have he : ((36+n:ℕ):ℂ)+35*(1:ℂ)-36=c₁ n := by
      dsimp [c₁,symbolFamilyWeight,symbolFamilyMomentum,familyMomentum,familyBackground]
      rw [Nat.cast_sub (by omega : 1≤n)]
      push_cast
      norm_num
      ring
    have hindex : 36+n-1=36+(n-1) := by omega
    simpa only [Nat.cast_one,Nat.cast_ofNat,he,hindex] using sixthState_positive (36+n) 1 (by omega) (by omega) (by omega)
  have hf2 (n : ℕ) (hp : 0<n) (hn : n≤R) :
      Wi.L 2 (f n)=if 2≤n then c₂ n • f (n-2) else 0 := by
    change Wi.L 2 (icoSixthCoupling • finiteActualSequence true R a v n)=_
    rw [map_smul,finiteActualSequence_second true R a v hrows n hp hn]
    split_ifs with htwo
    · rw [smul_comm]
    · rw [smul_zero]
  have hg2 (n : ℕ) (hp : 0<n) (hn : n≤R) :
      Wi.L 2 (g n)=if 2≤n then c₂ n • g (n-2) else 0 := by
    simp only [g,dif_pos hn]
    by_cases htwo : 2≤n
    · rw [if_pos htwo,dif_pos (by omega : n-2≤R)]
      have he : ((36+n:ℕ):ℂ)+35*(2:ℂ)-36=c₂ n := by
        dsimp [c₂,symbolFamilyWeight,symbolFamilyMomentum,familyMomentum,familyBackground,
          incomingWeight,vermaBSAWeight]
        rw [Nat.cast_sub htwo]
        push_cast
        norm_num
        ring
      have hindex : 36+n-2=36+(n-2) := by omega
      simpa only [Nat.cast_one,Nat.cast_ofNat,he,hindex] using sixthState_positive (36+n) 2 (by omega) (by omega) (by omega)
    · rw [if_neg htwo]
      have he := sixthState_positive (36+n) 2 (by omega) (by omega) (by omega)
      rw [sixthState_below (36+n-2) (by omega),smul_zero] at he
      exact he
  have hz : f 0=g 0 := by
    simp only [f,g,dif_pos (by omega : 0≤R),Nat.add_zero,
      finiteActualSequence_ground true R a v hv0,actualChannelSeed,if_true]
    exact sixthState_ground.symm
  have hu := sixth_ward_sequence_unique R hR c₁ c₂ f g hfg hgg hf1 hg1 hf2 hg2 hz
  intro n hn
  simpa only [f,g,dif_pos hn] using (hu n hn).symm

end VOA.Classification.COne.OrbIcoV
