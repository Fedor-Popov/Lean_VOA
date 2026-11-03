import VOA.Classification.COne.OrbIcoVSymbolFamily
import VOA.Classification.COne.OrbIcoWJetApproach
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Finite actual Fock Ward systems with retained scalar coordinates. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.VirasoroVerma InverseDS.LeeYangFockVirasoro Filter Topology
open scoped Classical

abbrev FiniteFockColumns (self : Bool) (R : ℕ) :=
  Σ n : Fin (R+1), Fin (symbolBasisSize self n.val)
abbrev FiniteFockRows (R : ℕ) :=
  (Σ n : Fin R, FockOccupations n.val) ⊕
    (Σ n : Fin (R-1), FockOccupations n.val)
abbrev FiniteFockPBW (self : Bool) (R : ℕ) :=
  (n : Fin (R+1)) → Fin (symbolBasisSize self n.val) → VermaPartitions n.val → ℂ

def finiteBlockVerma (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (n : Fin (R+1)) :
    (FiniteFockColumns self R → ℂ) →ₗ[ℂ]
      Verma (familyCharge s) (symbolFamilyWeight self s) :=
  { toFun := fun v => ∑ j : Fin (symbolBasisSize self n.val),
      v ⟨n,j⟩ • vermaLevelState (familyCharge s) (symbolFamilyWeight self s) n.val (a n j)
    map_add' := by
      intro v w
      simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
    map_smul' := by
      intro z v
      simp only [Pi.smul_apply,smul_smul,RingHom.id_apply,Finset.smul_sum,smul_eq_mul] }

def finiteBlockFock (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (n : Fin (R+1)) :
    (FiniteFockColumns self R → ℂ) →ₗ[ℂ] FF :=
  (symbolFamilyMap self s).comp (finiteBlockVerma self R a s n)

def finiteBlockProbe (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (n : Fin (R+1)) : (FiniteFockColumns self R → ℂ) →ₗ[ℂ] ℂ :=
  ∑ j : Fin (symbolBasisSize self n.val),
    (levelProbe n.val (a n j)) • LinearMap.proj (⟨n,j⟩ : FiniteFockColumns self R)

theorem finiteBlockVerma_level (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (n : Fin (R+1)) (v : FiniteFockColumns self R → ℂ) :
    finiteBlockVerma self R a s n v ∈ sortedSpan _ _ n.val := by
  change (∑ j : Fin (symbolBasisSize self n.val),
    v ⟨n,j⟩ • vermaLevelState (familyCharge s) (symbolFamilyWeight self s) n.val (a n j)) ∈ _
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (vermaLevelState_mem _ _ _ _)

theorem map_finiteBlockVerma {V : Type*} [AddCommGroup V] [Module ℂ V]
    (self : Bool) (R : ℕ) (a : FiniteFockPBW self R) (s : ℂ)
    (n : Fin (R+1)) (v : FiniteFockColumns self R → ℂ)
    (F : Verma (familyCharge s) (symbolFamilyWeight self s) →ₗ[ℂ] V) :
    F (finiteBlockVerma self R a s n v) =
      ∑ j : Fin (symbolBasisSize self n.val), v ⟨n,j⟩ •
        F (vermaLevelState (familyCharge s) (symbolFamilyWeight self s) n.val (a n j)) := by
  change F (∑ j : Fin (symbolBasisSize self n.val),
    v ⟨n,j⟩ • vermaLevelState (familyCharge s) (symbolFamilyWeight self s) n.val (a n j)) = _
  exact (map_sum F _ _).trans (Finset.sum_congr rfl (fun j hj => map_smul F _ _))

theorem finiteBlockProbe_sound (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (n : Fin (R+1)) (v : FiniteFockColumns self R → ℂ) :
    uniformProbe _ _ (finiteBlockVerma self R a s n v) = finiteBlockProbe self R a n v := by
  rw [map_finiteBlockVerma self R a s n v (uniformProbe _ _)]
  simp only [finiteBlockProbe,LinearMap.sum_apply,uniformProbe_levelState,
    LinearMap.smul_apply,LinearMap.proj_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

def finiteFirstDefect (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (n : Fin R) : (FiniteFockColumns self R → ℂ) →ₗ[ℂ] FF :=
  (sectorVirasoro (familyBackground s) (symbolFamilyMomentum self s) 1).comp
      (finiteBlockFock self R a s ⟨n.val+1,by omega⟩) -
    (symbolFamilyWeight self s+(n.val:ℂ)) •
      finiteBlockFock self R a s ⟨n.val,by omega⟩

def finiteSecondDefect (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (n : Fin (R-1)) : (FiniteFockColumns self R → ℂ) →ₗ[ℂ] FF :=
  (sectorVirasoro (familyBackground s) (symbolFamilyMomentum self s) 2).comp
      (finiteBlockFock self R a s ⟨n.val+2,by omega⟩) -
    (symbolFamilyWeight self s+incomingWeight (s^2)+(n.val:ℂ)) •
      finiteBlockFock self R a s ⟨n.val,by omega⟩

def finiteWardRowMap (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) : (FiniteFockColumns self R → ℂ) →ₗ[ℂ] (FiniteFockRows R → ℂ) where
  toFun v row := match row with
    | Sum.inl ⟨n,d⟩ => coeff d.val (finiteFirstDefect self R a s n v)
    | Sum.inr ⟨n,d⟩ => coeff d.val (finiteSecondDefect self R a s n v)
  map_add' v w := by
    funext row
    rcases row with ⟨n,d⟩ | ⟨n,d⟩ <;> simp only [map_add,coeff_add,Pi.add_apply]
  map_smul' z v := by
    funext row
    rcases row with ⟨n,d⟩ | ⟨n,d⟩ <;> simp only [map_smul,coeff_smul,Pi.smul_apply,RingHom.id_apply]

def finiteAugmentedWardMap (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (positions : Fin 2 → Fin (R+1)) (s : ℂ) (values : Fin 2 → ℂ) :
    (FiniteFockColumns self R → ℂ) →ₗ[ℂ] ((FiniteFockRows R ⊕ Fin 2) → ℂ) where
  toFun v row := match row with
    | Sum.inl r => finiteWardRowMap self R a s v r
    | Sum.inr r => finiteBlockProbe self R a (positions r) v -
        values r * finiteBlockProbe self R a ⟨0,by omega⟩ v
  map_add' v w := by
    funext row
    rcases row with r | r
    · exact congrFun (map_add (finiteWardRowMap self R a s) v w) r
    · simp only [map_add,mul_add,Pi.add_apply]
      ring
  map_smul' z v := by
    funext row
    rcases row with r | r
    · exact congrFun (map_smul (finiteWardRowMap self R a s) z v) r
    · simp only [map_smul,smul_eq_mul,Pi.smul_apply,RingHom.id_apply]
      ring

def finiteAugmentedWardMatrix (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (positions : Fin 2 → Fin (R+1)) (s : ℂ) (values : Fin 2 → ℂ) :
    Matrix (FiniteFockRows R ⊕ Fin 2) (FiniteFockColumns self R) ℂ :=
  LinearMap.toMatrix' (finiteAugmentedWardMap self R a positions s values)

theorem symbolFamilyMomentum_continuousAt (self : Bool) (s : ℂ) (hs : s≠0) :
    ContinuousAt (symbolFamilyMomentum self) s := by
  cases self
  · exact continuousAt_const
  · exact familyMomentum_continuousAt s hs

theorem symbolFamilyWeight_continuousAt (self : Bool) (s : ℂ) (hs : s≠0) :
    ContinuousAt (symbolFamilyWeight self) s :=
  ((symbolFamilyMomentum_continuousAt self s hs).pow 2).sub
    ((continuousAt_const.mul (familyBackground_continuousAt s hs)).mul
      (symbolFamilyMomentum_continuousAt self s hs))

theorem incomingWeight_square_continuousAt (s : ℂ) (hs : s≠0) :
    ContinuousAt (fun s => incomingWeight (s^2)) s := by
  unfold incomingWeight vermaBSAWeight
  fun_prop (disch := exact mul_ne_zero (by norm_num) (pow_ne_zero _ hs))

theorem symbolLevel_mode_coeff_continuousAt (self : Bool) (N : ℕ)
    (a : VermaPartitions N → ℂ) (s : ℂ) (hs : s≠0) (k : ℤ) (hk : k≠0)
    (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => coeff d (sectorVirasoro (familyBackground s)
      (symbolFamilyMomentum self s) k (symbolFamilyMap self s
        (vermaLevelState (familyCharge s) (symbolFamilyWeight self s) N a)))) s := by
  have hnear : ∀ᶠ z in 𝓝 s, z≠0 := continuousAt_id.eventually_ne hs
  cases self
  · change ContinuousAt (fun z => coeff d (sectorVirasoro (familyBackground z) 0 k
      (vacFamilyMap z (vermaLevelState (familyCharge z) (vacFamilyWeight z) N a)))) s
    have hc : ContinuousAt (fun z => ∑ w : VermaPartitions N, a w * coeff d
        (sectorVirasoro (familyBackground z) 0 k (fockRawEval z (vacDescData w.val)))) s := by
      apply tendsto_finsetSum
      intro w hw
      exact continuousAt_const.mul (sector_mode_coefficient_continuousAt
        familyBackground (fun _ => 0) s hs (familyBackground_continuousAt s hs)
        continuousAt_const k hk _ d)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hnear] with z hz
    simp only [vermaLevelState,map_sum,map_smul,coeff_sum,coeff_smul,
      vacDescData_sound z hz,smul_eq_mul]
  · change ContinuousAt (fun z => coeff d (sectorVirasoro (familyBackground z)
      (familyMomentum z) k
      (familyMap z (vermaLevelState (familyCharge z) (familyWeight z) N a)))) s
    have hc : ContinuousAt (fun z => ∑ w : VermaPartitions N, a w * coeff d
        (sectorVirasoro (familyBackground z) (familyMomentum z) k
          (fockRawEval z (fockDescData w.val)))) s := by
      apply tendsto_finsetSum
      intro w hw
      exact continuousAt_const.mul (sector_mode_coefficient_continuousAt
        familyBackground familyMomentum s hs (familyBackground_continuousAt s hs)
        (familyMomentum_continuousAt s hs) k hk _ d)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hnear] with z hz
    simp only [vermaLevelState,map_sum,map_smul,coeff_sum,coeff_smul,
      fockDescData_sound z hz,smul_eq_mul]

theorem symbolLevel_coeff_continuousAt (self : Bool) (N : ℕ)
    (a : VermaPartitions N → ℂ) (s : ℂ) (hs : s≠0)
    (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => coeff d (symbolFamilyMap self s
      (vermaLevelState (familyCharge s) (symbolFamilyWeight self s) N a))) s := by
  have hnear : ∀ᶠ z in 𝓝 s, z≠0 := continuousAt_id.eventually_ne hs
  cases self
  · apply (vacLevelCoefficient_continuousAt N a s hs d).congr_of_eventuallyEq
    filter_upwards [hnear] with z hz
    exact vacLevelCoefficient_sound N a z hz d
  · apply (familyLevelCoefficient_continuousAt N a s hs d).congr_of_eventuallyEq
    filter_upwards [hnear] with z hz
    exact familyLevelCoefficient_sound N a z hz d

theorem finiteBlockFock_coeff_continuousAt (self : Bool) (R : ℕ)
    (a : FiniteFockPBW self R) (n : Fin (R+1)) (v : FiniteFockColumns self R → ℂ)
    (s : ℂ) (hs : s≠0) (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => coeff d (finiteBlockFock self R a s n v)) s := by
  have he (z : ℂ) : coeff d (finiteBlockFock self R a z n v) =
      ∑ j : Fin (symbolBasisSize self n.val), v ⟨n,j⟩ * coeff d
        (symbolFamilyMap self z
          (vermaLevelState (familyCharge z) (symbolFamilyWeight self z) n.val (a n j))) := by
    change coeff d (symbolFamilyMap self z (finiteBlockVerma self R a z n v)) = _
    have hm := congrArg (coeff d)
      (map_finiteBlockVerma self R a z n v (symbolFamilyMap self z))
    simpa only [coeff_sum,coeff_smul,smul_eq_mul] using hm
  simp_rw [he]
  apply tendsto_finsetSum
  intro j hj
  exact continuousAt_const.mul (symbolLevel_coeff_continuousAt self n.val (a n j) s hs d)

theorem finiteBlockFock_mode_coeff_continuousAt (self : Bool) (R : ℕ)
    (a : FiniteFockPBW self R) (n : Fin (R+1)) (v : FiniteFockColumns self R → ℂ)
    (s : ℂ) (hs : s≠0) (k : ℤ) (hk : k≠0) (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => coeff d (sectorVirasoro (familyBackground s)
      (symbolFamilyMomentum self s) k (finiteBlockFock self R a s n v))) s := by
  have he (z : ℂ) : coeff d (sectorVirasoro (familyBackground z)
      (symbolFamilyMomentum self z) k (finiteBlockFock self R a z n v)) =
      ∑ j : Fin (symbolBasisSize self n.val), v ⟨n,j⟩ * coeff d
        (sectorVirasoro (familyBackground z) (symbolFamilyMomentum self z) k
          (symbolFamilyMap self z
            (vermaLevelState (familyCharge z) (symbolFamilyWeight self z) n.val (a n j)))) := by
    change coeff d (((sectorVirasoro (familyBackground z) (symbolFamilyMomentum self z) k).comp
      (symbolFamilyMap self z)) (finiteBlockVerma self R a z n v)) = _
    have hm := congrArg (coeff d) (map_finiteBlockVerma self R a z n v
      ((sectorVirasoro (familyBackground z) (symbolFamilyMomentum self z) k).comp
        (symbolFamilyMap self z)))
    simpa only [coeff_sum,coeff_smul,smul_eq_mul,LinearMap.comp_apply] using hm
  simp_rw [he]
  apply tendsto_finsetSum
  intro j hj
  exact continuousAt_const.mul
    (symbolLevel_mode_coeff_continuousAt self n.val (a n j) s hs k hk d)

theorem finiteFirstDefect_coeff_continuousAt (self : Bool) (R : ℕ)
    (a : FiniteFockPBW self R) (n : Fin R) (v : FiniteFockColumns self R → ℂ)
    (s : ℂ) (hs : s≠0) (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => coeff d (finiteFirstDefect self R a s n v)) s := by
  simp only [finiteFirstDefect,LinearMap.sub_apply,LinearMap.comp_apply,
    LinearMap.smul_apply,coeff_sub,coeff_smul,smul_eq_mul]
  exact (finiteBlockFock_mode_coeff_continuousAt self R a _ v s hs 1 (by norm_num) d).sub
    (((symbolFamilyWeight_continuousAt self s hs).add continuousAt_const).mul
      (finiteBlockFock_coeff_continuousAt self R a _ v s hs d))

theorem finiteSecondDefect_coeff_continuousAt (self : Bool) (R : ℕ)
    (a : FiniteFockPBW self R) (n : Fin (R-1)) (v : FiniteFockColumns self R → ℂ)
    (s : ℂ) (hs : s≠0) (d : (ℕ × Fin 1) →₀ ℕ) :
    ContinuousAt (fun s => coeff d (finiteSecondDefect self R a s n v)) s := by
  simp only [finiteSecondDefect,LinearMap.sub_apply,LinearMap.comp_apply,
    LinearMap.smul_apply,coeff_sub,coeff_smul,smul_eq_mul]
  exact (finiteBlockFock_mode_coeff_continuousAt self R a _ v s hs 2 (by norm_num) d).sub
    ((((symbolFamilyWeight_continuousAt self s hs).add
      (incomingWeight_square_continuousAt s hs)).add continuousAt_const).mul
      (finiteBlockFock_coeff_continuousAt self R a _ v s hs d))

theorem finiteAugmentedWardMatrix_tendsto {X : Type*} {l : Filter X}
    (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (positions : Fin 2 → Fin (R+1)) (parameter : X → ℂ) (values : X → Fin 2 → ℂ)
    (value : Fin 2 → ℂ) (hp : Tendsto parameter l (𝓝 (1 : ℂ)))
    (hv : ∀ r, Tendsto (fun x => values x r) l (𝓝 (value r))) :
    Tendsto (fun x => finiteAugmentedWardMatrix self R a positions (parameter x) (values x))
      l (𝓝 (finiteAugmentedWardMatrix self R a positions 1 value)) := by
  apply tendsto_pi_nhds.mpr
  intro row
  apply tendsto_pi_nhds.mpr
  intro col
  simp only [finiteAugmentedWardMatrix,LinearMap.toMatrix'_apply]
  rcases row with row | r
  · rcases row with ⟨n,d⟩ | ⟨n,d⟩
    · exact (finiteFirstDefect_coeff_continuousAt self R a n (Pi.single col 1)
        1 one_ne_zero d.val).tendsto.comp hp
    · exact (finiteSecondDefect_coeff_continuousAt self R a n (Pi.single col 1)
        1 one_ne_zero d.val).tendsto.comp hp
  · exact tendsto_const_nhds.sub ((hv r).mul tendsto_const_nhds)

-- Dependent Verma parameters require extra elaboration for homogeneous mode transfer.
set_option maxHeartbeats 1000000 in
theorem finiteFirstDefect_level (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (n : Fin R) (v : FiniteFockColumns self R → ℂ) :
    finiteFirstDefect self R a s n v ∈ gradingWN 1 n.val := by
  have hlev : vermaMode (familyCharge s) (symbolFamilyWeight self s) 1
      (finiteBlockVerma self R a s ⟨n.val+1,by omega⟩ v) -
      (symbolFamilyWeight self s+(n.val:ℂ)) •
      finiteBlockVerma self R a s ⟨n.val,by omega⟩ v ∈ sortedSpan _ _ n.val := by
    apply Submodule.sub_mem
    · apply verma_mode_mem_level _ _ (n.val+1) n.val _
        (finiteBlockVerma_level self R a s ⟨n.val+1,by omega⟩ v) 1
      push_cast
      ring
    · exact Submodule.smul_mem _ _ (finiteBlockVerma_level self R a s ⟨n.val,by omega⟩ v)
  convert chargedFockMap_mem_level (familyBackground s) (symbolFamilyMomentum self s)
    n.val _ hlev using 1
  simp only [finiteFirstDefect,finiteBlockFock,LinearMap.sub_apply,
    LinearMap.comp_apply,LinearMap.smul_apply]
  symm
  exact (map_sub (chargedFockMap (familyBackground s) (symbolFamilyMomentum self s)) _ _).trans
    (congrArg₂ (fun x y : FF => x-y)
      (chargedFockMap_mode _ _ _ _)
      (map_smul (chargedFockMap (familyBackground s) (symbolFamilyMomentum self s)) _ _))

-- Dependent Verma parameters require extra elaboration for homogeneous mode transfer.
set_option maxHeartbeats 1000000 in
theorem finiteSecondDefect_level (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (n : Fin (R-1)) (v : FiniteFockColumns self R → ℂ) :
    finiteSecondDefect self R a s n v ∈ gradingWN 1 n.val := by
  have hlev : vermaMode (familyCharge s) (symbolFamilyWeight self s) 2
      (finiteBlockVerma self R a s ⟨n.val+2,by omega⟩ v) -
      (symbolFamilyWeight self s+incomingWeight (s^2)+(n.val:ℂ)) •
      finiteBlockVerma self R a s ⟨n.val,by omega⟩ v ∈ sortedSpan _ _ n.val := by
    apply Submodule.sub_mem
    · apply verma_mode_mem_level _ _ (n.val+2) n.val _
        (finiteBlockVerma_level self R a s ⟨n.val+2,by omega⟩ v) 2
      push_cast
      ring
    · exact Submodule.smul_mem _ _ (finiteBlockVerma_level self R a s ⟨n.val,by omega⟩ v)
  convert chargedFockMap_mem_level (familyBackground s) (symbolFamilyMomentum self s)
    n.val _ hlev using 1
  simp only [finiteSecondDefect,finiteBlockFock,LinearMap.sub_apply,
    LinearMap.comp_apply,LinearMap.smul_apply]
  symm
  exact (map_sub (chargedFockMap (familyBackground s) (symbolFamilyMomentum self s)) _ _).trans
    (congrArg₂ (fun x y : FF => x-y)
      (chargedFockMap_mode _ _ _ _)
      (map_smul (chargedFockMap (familyBackground s) (symbolFamilyMomentum self s)) _ _))

theorem fock_level_zero_of_coeff (N : ℕ) (f : FF) (hf : f ∈ gradingWN 1 N)
    (hz : ∀ d : FockOccupations N, coeff d.val f=0) : f=0 := by
  have he : fockCoordinates N (⟨f,hf⟩ : gradingWN 1 N) = 0 := by
    funext d
    exact hz d
  have hzero := fockCoordinates_injective N (a₁ := (⟨f,hf⟩ : gradingWN 1 N))
    (a₂ := 0) (he.trans (map_zero (fockCoordinates N)).symm)
  exact congrArg Subtype.val hzero

theorem finiteWardRowMap_eq_zero_iff (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (s : ℂ) (v : FiniteFockColumns self R → ℂ) :
    finiteWardRowMap self R a s v=0 ↔
      (∀ n, finiteFirstDefect self R a s n v=0) ∧
        (∀ n, finiteSecondDefect self R a s n v=0) := by
  constructor
  · intro he
    constructor
    · intro n
      apply fock_level_zero_of_coeff n.val _ (finiteFirstDefect_level self R a s n v)
      intro d
      exact congrFun he (Sum.inl ⟨n,d⟩)
    · intro n
      apply fock_level_zero_of_coeff n.val _ (finiteSecondDefect_level self R a s n v)
      intro d
      exact congrFun he (Sum.inr ⟨n,d⟩)
  · rintro ⟨h1,h2⟩
    funext row
    rcases row with ⟨n,d⟩ | ⟨n,d⟩
    · change coeff d.val (finiteFirstDefect self R a s n v)=0
      simp only [h1,coeff_zero]
    · change coeff d.val (finiteSecondDefect self R a s n v)=0
      simp only [h2,coeff_zero]

/-- Compact specialization preserves the leading scalar and both specified scalar rows.
The ground-injectivity hypothesis is discharged on the actual c=1 channel. -/
theorem finiteFock_normalized_specialization {X : Type*} {l : Filter X} [l.NeBot]
    (self : Bool) (R : ℕ) (a : FiniteFockPBW self R)
    (positions : Fin 2 → Fin (R+1)) (parameter : X → ℂ) (values : X → Fin 2 → ℂ)
    (value : Fin 2 → ℂ) (hp : Tendsto parameter l (𝓝 (1 : ℂ)))
    (hv : ∀ r, Tendsto (fun x => values x r) l (𝓝 (value r)))
    (hker : ∀ᶠ x in l, ∃ v : FiniteFockColumns self R → ℂ,
      v≠0 ∧ finiteWardRowMap self R a (parameter x) v=0 ∧
      ∀ r, finiteBlockProbe self R a (positions r) v =
        values x r * finiteBlockProbe self R a ⟨0,by omega⟩ v)
    (hground : ∀ v : FiniteFockColumns self R → ℂ,
      finiteWardRowMap self R a 1 v=0 → finiteBlockProbe self R a ⟨0,by omega⟩ v=0 → v=0) :
    ∃ v : FiniteFockColumns self R → ℂ,
      finiteBlockProbe self R a ⟨0,by omega⟩ v=1 ∧
      finiteWardRowMap self R a 1 v=0 ∧
      ∀ r, finiteBlockProbe self R a (positions r) v=value r := by
  have hk : ∀ᶠ x in l, ∃ v : FiniteFockColumns self R → ℂ, v≠0 ∧
      (finiteAugmentedWardMatrix self R a positions (parameter x) (values x)).mulVec v=0 := by
    filter_upwards [hker] with x hx
    obtain ⟨v,hvn,hvw,hvs⟩ := hx
    refine ⟨v,hvn,?_⟩
    rw [finiteAugmentedWardMatrix,LinearMap.toMatrix'_mulVec]
    funext row
    rcases row with row | r
    · exact congrFun hvw row
    · exact sub_eq_zero.mpr (hvs r)
  obtain ⟨v,hv0,hvm,hvs⟩ := normalized_kernel_with_scalar_rows
    (fun x => finiteAugmentedWardMatrix self R a positions (parameter x) (values x))
    (finiteAugmentedWardMatrix self R a positions 1 value)
    (finiteBlockProbe self R a ⟨0,by omega⟩) value
    (fun r => finiteBlockProbe self R a (positions r))
    (finiteAugmentedWardMatrix_tendsto self R a positions parameter values value hp hv) hk
    (by
      intro v he hz
      apply hground v _ hz
      rw [finiteAugmentedWardMatrix,LinearMap.toMatrix'_mulVec] at he
      funext row
      exact congrFun he (Sum.inl row))
    (by intro r v; rw [finiteAugmentedWardMatrix,LinearMap.toMatrix'_mulVec]; rfl)
  refine ⟨v,hv0,?_,hvs⟩
  rw [finiteAugmentedWardMatrix,LinearMap.toMatrix'_mulVec] at hvm
  funext row
  exact congrFun hvm (Sum.inl row)

end VOA.Classification.COne.OrbIcoV
