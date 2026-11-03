import VOA.Classification.COne.OrbIcoVAllCoefficients
import VOA.Classification.COne.OrbIcoVSymbolFamily
import VOA.Classification.COne.OrbIcoVWardUnique

/-! The actual fiber-at-one Virasoro channel map and its faithful Fock realization. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco OrbC2c
  InverseDS.VirasoroVerma HeisenbergN VOA.VirasoroScreening
  InverseDS.LeeYangFockVirasoro MvPolynomial
open scoped Classical

def actualChannelWeight (self : Bool) : ℤ := if self then 36 else 0

def actualChannelSeed (self : Bool) : (orbifold ico).carrier := if self then Xico else Wi.vacuum

theorem actualChannelPrimary (self : Bool) :
    actualChannelSeed self∈prim Wi (actualChannelWeight self) := by
  cases self
  · exact vacuum_mem_prim Wi
  · exact OrbIcoZ.X_primary

/-- The genuine universal highest-weight map at the c=1 fiber. -/
def actualFiberMap (self : Bool) :
    Verma (familyCharge 1) (symbolFamilyWeight self 1) →ₗ[ℂ] (orbifold ico).carrier :=
  (seedMap Wi (actualChannelWeight self) (actualChannelSeed self) (actualChannelPrimary self)).comp
    (uniformTransport (familyCharge 1) (symbolFamilyWeight self 1) Wi.centralCharge
      ((actualChannelWeight self : ℤ) : ℂ)).toLinearMap

def actualLevelState (self : Bool) (N : ℕ) (a : VermaPartitions N → ℂ) : (orbifold ico).carrier :=
  ∑ w : VermaPartitions N, a w • virWord Wi w.val (actualChannelSeed self)

theorem uniformTransport_levelState (c h c' h' : ℂ) (N : ℕ) (a : VermaPartitions N → ℂ) :
    uniformTransport c h c' h' (vermaLevelState c h N a)=vermaLevelState c' h' N a := by
  simp only [vermaLevelState,map_sum,map_smul,uniformTransport_word]

theorem actualFiberMap_levelState (self : Bool) (N : ℕ) (a : VermaPartitions N → ℂ) :
    actualFiberMap self (vermaLevelState (familyCharge 1) (symbolFamilyWeight self 1) N a)=
      actualLevelState self N a := by
  simp only [actualFiberMap,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [uniformTransport_levelState]
  simp only [vermaLevelState,map_sum,map_smul,seedMap_word,actualLevelState]

theorem actualFiberMap_highest (self : Bool) :
    actualFiberMap self (highestVector (familyCharge 1) (symbolFamilyWeight self 1))=actualChannelSeed self := by
  simp only [actualFiberMap,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show highestVector (familyCharge 1) (symbolFamilyWeight self 1)=
    negWord (familyCharge 1) (symbolFamilyWeight self 1) [] by rfl,
    uniformTransport_word,seedMap_word]
  rfl

theorem actualFiberMap_mode (self : Bool) (k : ℤ)
    (v : Verma (familyCharge 1) (symbolFamilyWeight self 1)) :
    actualFiberMap self (vermaMode _ _ k v)=Wi.L k (actualFiberMap self v) := by
  have hc : familyCharge 1=Wi.centralCharge := by
    rw [Wi_charge_one]
    norm_num [familyCharge,familyBackground]
  have hh : symbolFamilyWeight self 1=((actualChannelWeight self : ℤ) : ℂ) := by
    cases self <;> norm_num [symbolFamilyWeight,symbolFamilyMomentum,actualChannelWeight,
      familyMomentum,vacFamilyMomentum,familyBackground]
  have hm (c h c' h' : ℂ) (hc : c=c') (hh : h=h') (v : Verma c h) :
      uniformTransport c h c' h' (vermaMode c h k v)=
        vermaMode c' h' k (uniformTransport c h c' h' v) := by
    subst c'
    subst h'
    simp [uniformTransport]
  simp only [actualFiberMap,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [hm _ _ _ _ hc hh,seedMap_mode]

/-- The actual VOA channel and the c=1 Fock realization have exactly the same
relations at every relative level. -/
theorem actualLevelState_zero_iff_fock (self : Bool) (N : ℕ) (a : VermaPartitions N → ℂ) :
    actualLevelState self N a=0 ↔
      symbolFamilyMap self 1 (vermaLevelState (familyCharge 1) (symbolFamilyWeight self 1) N a)=0 := by
  rw [← actualFiberMap_levelState]
  simp only [actualFiberMap,LinearMap.comp_apply,LinearEquiv.coe_coe,uniformTransport_levelState]
  cases self
  · exact vacuum_Fock_coefficient_relations_all N a
  · exact Xico_Fock_coefficient_relations_all N a

/-- Faithfulness on each genuine homogeneous Fock fiber. -/
theorem actualFiberMap_zero_iff_fock (self : Bool) (N : ℕ)
    (v : Verma (familyCharge 1) (symbolFamilyWeight self 1)) (hv : v∈sortedSpan _ _ N) :
    actualFiberMap self v=0 ↔ symbolFamilyMap self 1 v=0 := by
  obtain ⟨a,rfl⟩ := exists_vermaLevelState _ _ N v hv
  rw [actualFiberMap_levelState]
  exact actualLevelState_zero_iff_fock self N a

theorem actualLevelState_grading (self : Bool) (N : ℕ) (a : VermaPartitions N → ℂ) :
    actualLevelState self N a∈Wi.grading (actualChannelWeight self+(N : ℤ)) := by
  have h := seedMap_mem_grading Wi (actualChannelWeight self) (actualChannelSeed self)
    (actualChannelPrimary self) N
    (vermaLevelState Wi.centralCharge ((actualChannelWeight self : ℤ) : ℂ) N a)
    (vermaLevelState_mem _ _ _ _)
  simpa only [vermaLevelState,map_sum,map_smul,seedMap_word,actualLevelState] using h

/-- The two actual oscillator probes agree with the universal PBW survival measure. -/
theorem actualProbe_virWord (self : Bool) (w : List ℕ) :
    (if self then sixthProbe else vacuumProbe) (virWord Wi w (actualChannelSeed self))=
      wordProbe w*(if self then OrbIcoS.neutralProbe Xico else 1) := by
  induction w with
  | nil =>
    cases self
    · simpa only [actualChannelSeed,virWord,wordProbe,List.map_nil,List.prod_nil,one_mul]
        using vacuumProbe_vacuum
    · simpa only [actualChannelSeed,virWord,wordProbe,List.map_nil,List.prod_nil,one_mul]
        using sixthProbe_Xico
  | cons k w ih =>
    cases self <;> simp only [Bool.false_eq_true,if_false,if_true] at ih ⊢
    · rw [virWord,vacuumProbe_L,ih]
      simp only [wordProbe,List.map_cons,List.prod_cons]
      ring
    · rw [virWord,sixthProbe_L,ih]
      simp only [wordProbe,List.map_cons,List.prod_cons]
      ring

theorem actualProbe_levelState (self : Bool) (N : ℕ) (a : VermaPartitions N → ℂ) :
    (if self then sixthProbe else vacuumProbe) (actualLevelState self N a)=
      levelProbe N a*(if self then OrbIcoS.neutralProbe Xico else 1) := by
  simp only [actualLevelState,map_sum,map_smul,actualProbe_virWord,levelProbe,smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  ring

/-- A genuine positive Fock Ward equation transfers to the actual VOA channel. -/
theorem actualFiberMap_positive_ward (self : Bool) (N k : ℕ) (hk : k≤N) (c : ℂ)
    (v u : Verma (familyCharge 1) (symbolFamilyWeight self 1))
    (hv : v∈sortedSpan _ _ N) (hu : u∈sortedSpan _ _ (N-k))
    (hF : sectorVirasoro (familyBackground 1) (symbolFamilyMomentum self 1) (k : ℤ)
      (symbolFamilyMap self 1 v)=c • symbolFamilyMap self 1 u) :
    Wi.L (k : ℤ) (actualFiberMap self v)=c • actualFiberMap self u := by
  have hm : vermaMode _ _ (k : ℤ) v∈sortedSpan _ _ (N-k) :=
    verma_mode_mem_level _ _ N (N-k) v hv k (by omega)
  have hd : symbolFamilyMap self 1 (vermaMode _ _ (k : ℤ) v-c • u)=0 := by
    change chargedFockMap (familyBackground 1) (symbolFamilyMomentum self 1)
      (vermaMode (familyCharge 1) (symbolFamilyWeight self 1) (k : ℤ) v-c • u)=0
    calc
      _ = chargedFockMap (familyBackground 1) (symbolFamilyMomentum self 1)
          (vermaMode (familyCharge 1) (symbolFamilyWeight self 1) (k : ℤ) v) -
          chargedFockMap (familyBackground 1) (symbolFamilyMomentum self 1) (c • u) :=
        map_sub (chargedFockMap (familyBackground 1) (symbolFamilyMomentum self 1)) _ _
      _ = sectorVirasoro (familyBackground 1) (symbolFamilyMomentum self 1) (k : ℤ)
          (symbolFamilyMap self 1 v)-c • symbolFamilyMap self 1 u :=
        congrArg₂ (fun x y : FF => x-y) (chargedFockMap_mode _ _ (k : ℤ) v)
          (map_smul (chargedFockMap (familyBackground 1) (symbolFamilyMomentum self 1)) c u)
      _ = 0 := sub_eq_zero.mpr hF
  have ha := (actualFiberMap_zero_iff_fock self (N-k) _
    ((sortedSpan _ _ _).sub_mem hm ((sortedSpan _ _ _).smul_mem c hu))).mpr hd
  rw [map_sub,map_smul,actualFiberMap_mode] at ha
  exact sub_eq_zero.mp ha

/-- Above the relative level, positive modes vanish in the actual channel. -/
theorem actualFiberMap_positive_above (self : Bool) (N k : ℕ) (hk : N<k)
    (v : Verma (familyCharge 1) (symbolFamilyWeight self 1)) (hv : v∈sortedSpan _ _ N) :
    Wi.L (k : ℤ) (actualFiberMap self v)=0 := by
  rw [← actualFiberMap_mode,verma_mode_above_level _ _ N v hv k (by omega),map_zero]

/-- Actual finite homogeneous Ward solutions are determined by their ground state. -/
theorem actualFiberMap_ward_ground_zero (self : Bool) (R : ℕ)
    (hR : R < (if self then 64 else 100))
    (f : ℕ → Verma (familyCharge 1) (symbolFamilyWeight self 1))
    (hf : ∀ n≤R, f n∈sortedSpan _ _ n)
    (c₁ c₂ : ℕ → ℂ)
    (h₁ : ∀ n, 0<n → n≤R → sectorVirasoro (familyBackground 1)
      (symbolFamilyMomentum self 1) 1 (symbolFamilyMap self 1 (f n))=
        c₁ n • symbolFamilyMap self 1 (f (n-1)))
    (h₂ : ∀ n, 2≤n → n≤R → sectorVirasoro (familyBackground 1)
      (symbolFamilyMomentum self 1) 2 (symbolFamilyMap self 1 (f n))=
        c₂ n • symbolFamilyMap self 1 (f (n-2)))
    (hzero : actualFiberMap self (f 0)=0) :
    ∀ n≤R, actualFiberMap self (f n)=0 := by
  have hg (n : ℕ) (hn : n≤R) :
      actualFiberMap self (f n)∈Wi.grading (actualChannelWeight self+(n : ℤ)) := by
    obtain ⟨a,ha⟩ := exists_vermaLevelState _ _ n (f n) (hf n hn)
    rw [← ha,actualFiberMap_levelState]
    exact actualLevelState_grading self n a
  have hone (n : ℕ) (hn : 0<n) (hnR : n≤R) :
      Wi.L 1 (actualFiberMap self (f n))=c₁ n • actualFiberMap self (f (n-1)) := by
    exact actualFiberMap_positive_ward self n 1 (by omega) (c₁ n)
      _ _ (hf n hnR) (hf (n-1) (by omega)) (h₁ n hn hnR)
  have htwo (n : ℕ) (hn : 0<n) (hnR : n≤R) :
      Wi.L 2 (actualFiberMap self (f n))=
        if 2≤n then c₂ n • actualFiberMap self (f (n-2)) else 0 := by
    by_cases h2 : 2≤n
    · rw [if_pos h2]
      exact actualFiberMap_positive_ward self n 2 h2 (c₂ n)
        _ _ (hf n hnR) (hf (n-2) (by omega)) (h₂ n h2 hnR)
    · rw [if_neg h2]
      exact actualFiberMap_positive_above self n 2 (by omega) _ (hf n hnR)
  cases self
  · have hC (n : ℕ) (hn : n≤R) : spinCasimir (actualFiberMap false (f n) : Sp)=0 := by
      obtain ⟨a,ha⟩ := exists_vermaLevelState _ _ n (f n) (hf n hn)
      rw [← ha,actualFiberMap_levelState]
      simp only [actualLevelState,actualChannelSeed,Bool.false_eq_true,if_false,map_sum,map_smul,
        Submodule.coe_sum,Submodule.coe_smul,spinCasimir_word_vacuum,smul_zero,Finset.sum_const_zero]
    have hu := vacuum_ward_sequence_unique R hR c₁ c₂ (fun n => actualFiberMap false (f n))
      (fun _ => 0) hC (by simp) (by simpa [actualChannelWeight] using hg)
      (by simp) hone (by simp) htwo (by simp) hzero
    exact hu
  · have hu := sixth_ward_sequence_unique R hR c₁ c₂ (fun n => actualFiberMap true (f n))
      (fun _ => 0) (by simpa [actualChannelWeight] using hg) (by simp)
      hone (by simp) htwo (by simp) hzero
    exact hu

end VOA.Classification.COne.OrbIcoV
