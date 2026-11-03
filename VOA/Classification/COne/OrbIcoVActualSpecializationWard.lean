import VOA.Classification.COne.OrbIcoVActualSpecialization
import VOA.Classification.COne.OrbIcoVSpecializeWard

/-! Actual ground injectivity of the finite Fock Ward kernel at c=1. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco OrbC2c
  InverseDS.VirasoroVerma HeisenbergN VOA.VirasoroScreening
  InverseDS.LeeYangFockVirasoro MvPolynomial
open scoped Classical

theorem zero_partition_word (w : VermaPartitions 0) : w.val=[] := by
  have h := w.property.2
  cases he : w.val with
  | nil => rfl
  | cons i w => simp [energyHW,he] at h

theorem zero_level_probe (c h : ℂ) (v : Verma c h) (hv : v∈sortedSpan c h 0) :
    v=uniformProbe c h v • highestVector c h := by
  obtain ⟨a,rfl⟩ := exists_vermaLevelState c h 0 v hv
  simp only [vermaLevelState,map_sum,map_smul,uniformProbe_word,smul_eq_mul]
  simp_rw [zero_partition_word]
  simp only [negWord,wordProbe,List.map_nil,List.prod_nil,mul_one]
  rw [Finset.sum_smul]

/-- Linear independence of genuine local Fock columns makes the ground
coefficient injective on the actual finite Ward kernel. -/
theorem finiteWard_ground_injective (self : Bool) (R : ℕ)
    (hR : R < (if self then 64 else 100)) (a : FiniteFockPBW self R)
    (hLI : ∀ n : Fin (R+1), LinearIndependent ℂ (symbolColumns self n.val (a n) 1))
    (v : FiniteFockColumns self R → ℂ)
    (hrows : finiteWardRowMap self R a 1 v=0)
    (hzero : finiteBlockProbe self R a ⟨0,by omega⟩ v=0) : v=0 := by
  let f : ℕ → Verma (familyCharge 1) (symbolFamilyWeight self 1) := fun n =>
    if hn : n≤R then finiteBlockVerma self R a 1 ⟨n,by omega⟩ v else 0
  have hf (n : ℕ) (hn : n≤R) : f n∈sortedSpan _ _ n := by
    simp only [f,dif_pos hn]
    exact finiteBlockVerma_level self R a 1 ⟨n,by omega⟩ v
  have hdef := (finiteWardRowMap_eq_zero_iff self R a 1 v).mp hrows
  have hfirst (n : ℕ) (hn : 0<n) (hnR : n≤R) :
      sectorVirasoro (familyBackground 1) (symbolFamilyMomentum self 1) 1
        (symbolFamilyMap self 1 (f n))=
        (symbolFamilyWeight self 1+((n-1 : ℕ) : ℂ)) • symbolFamilyMap self 1 (f (n-1)) := by
    have h := sub_eq_zero.mp (hdef.1 ⟨n-1,by omega⟩)
    simp only [finiteFirstDefect,LinearMap.sub_apply,LinearMap.comp_apply,
      LinearMap.smul_apply,finiteBlockFock] at h
    simpa only [f,dif_pos hnR,dif_pos (by omega : n-1≤R),
      show n-1+1=n by omega] using h
  have hsecond (n : ℕ) (hn : 2≤n) (hnR : n≤R) :
      sectorVirasoro (familyBackground 1) (symbolFamilyMomentum self 1) 2
        (symbolFamilyMap self 1 (f n))=
        (symbolFamilyWeight self 1+incomingWeight (1^2)+((n-2 : ℕ) : ℂ)) •
          symbolFamilyMap self 1 (f (n-2)) := by
    have h := sub_eq_zero.mp (hdef.2 ⟨n-2,by omega⟩)
    simp only [finiteSecondDefect,LinearMap.sub_apply,LinearMap.comp_apply,
      LinearMap.smul_apply,finiteBlockFock] at h
    simpa only [f,dif_pos hnR,dif_pos (by omega : n-2≤R),
      show n-2+2=n by omega] using h
  have hz : actualFiberMap self (f 0)=0 := by
    have hp : uniformProbe _ _ (f 0)=0 := by
      simp only [f,dif_pos (by omega : 0≤R)]
      rw [finiteBlockProbe_sound]
      exact hzero
    rw [zero_level_probe _ _ (f 0) (hf 0 (by omega)),hp,zero_smul,map_zero]
  have hall := actualFiberMap_ward_ground_zero self R hR f hf
    (fun n => symbolFamilyWeight self 1+((n-1 : ℕ) : ℂ))
    (fun n => symbolFamilyWeight self 1+incomingWeight (1^2)+((n-2 : ℕ) : ℂ))
    hfirst hsecond hz
  have hF (n : Fin (R+1)) : finiteBlockFock self R a 1 n v=0 := by
    change symbolFamilyMap self 1 (finiteBlockVerma self R a 1 n v)=0
    have h := (actualFiberMap_zero_iff_fock self n.val (f n.val) (hf n.val (by omega))).mp
      (hall n.val (by omega))
    simpa only [f,dif_pos (by omega : n.val≤R)] using h
  have hb (n : Fin (R+1)) : ∑ j : Fin (symbolBasisSize self n.val),
      v ⟨n,j⟩ • symbolColumns self n.val (a n) 1 j=0 := by
    funext d
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply]
    change (∑ j : Fin (symbolBasisSize self n.val), v ⟨n,j⟩ •
      symbolColumns self n.val (a n) 1 j d)=0
    have hm := map_finiteBlockVerma self R a 1 n v (symbolFamilyMap self 1)
    have hz := hF n
    change symbolFamilyMap self 1 (finiteBlockVerma self R a 1 n v)=0 at hz
    have hc := congrArg (coeff d.val) (hm.symm.trans hz)
    have hc' : (∑ j : Fin (symbolBasisSize self n.val), v ⟨n,j⟩ •
        coeff d.val (symbolFamilyMap self 1
          (vermaLevelState (familyCharge 1) (symbolFamilyWeight self 1) n.val (a n j))))=0 := by
      simpa only [coeff_sum,coeff_smul,coeff_zero] using hc
    calc
      _ = ∑ j : Fin (symbolBasisSize self n.val), v ⟨n,j⟩ •
          coeff d.val (symbolFamilyMap self 1
            (vermaLevelState (familyCharge 1) (symbolFamilyWeight self 1) n.val (a n j))) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (fun z : ℂ => v ⟨n,j⟩ • z)
          (symbolColumns_sound self n.val (a n) 1 one_ne_zero j d).symm
      _ = 0 := hc'
  funext col
  rcases col with ⟨n,j⟩
  have h := (Fintype.linearIndependent_iff.mp (hLI n)) (fun j => v ⟨n,j⟩) (hb n)
  exact h j

end VOA.Classification.COne.OrbIcoV
