import VOA.Classification.COne.OrbIcoVChannelStates
import VOA.Classification.COne.OrbIcoVFockFamily

/-! Actual universal Virasoro maps into VOA primary channels. The same
first-row BSA singular vector is killed in the actual spin-six channel. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco OrbC2c
  InverseDS.VirasoroVerma InverseDS.LeeYangWardClosure VirModule VirDeformModes

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

def seedData (W : VertexOperatorAlgebra V) : CentralVirasoroData V where
  L := W.L
  central := W.centralCharge • 1
  comm m n := by
    rw [W.L_virasoro]
    by_cases h : m+n=0 <;> simp [h, smul_smul]
  central_comm n := by
    change (W.centralCharge • (1 : Module.End ℂ V)) * W.L n = _
    simp

def seedRep (W : VertexOperatorAlgebra V) : VirRep V where
  ρ := fixedRho (seedData W) rfl
  centralCharge := W.centralCharge
  acts_central := fixedRho_C (seedData W) rfl

theorem seedRep_mode (W : VertexOperatorAlgebra V) (n : ℤ) :
    virMode (seedRep W) n = W.L n := fixedRho_L (seedData W) rfl n

theorem seedHighest (W : VertexOperatorAlgebra V) (h : ℤ) (x : V)
    (hp : x ∈ prim W h) : IsHighestWeightVector (seedRep W) x W.centralCharge (h : ℂ) where
  centralCharge := rfl
  pos_annihilate n hn := by
    rw [seedRep_mode]
    have he := ((mem_prim W).mp hp).2 (n-1).toNat
    rwa [show (((n-1).toNat : ℕ) : ℤ)+1 = n by omega] at he
  zero_acts := by
    rw [seedRep_mode]
    exact W.L_zero_grading x ((mem_prim W).mp hp).1

def seedMap (W : VertexOperatorAlgebra V) (h : ℤ) (x : V) (hp : x ∈ prim W h) :
    Verma W.centralCharge (h : ℂ) →ₗ[ℂ] V :=
  universalMap (seedRep W) x (seedHighest W h x hp)

theorem seedMap_mode (W : VertexOperatorAlgebra V) (h : ℤ) (x : V)
    (hp : x ∈ prim W h) (n : ℤ) (v : Verma W.centralCharge (h : ℂ)) :
    seedMap W h x hp (vermaMode _ _ n v) = W.L n (seedMap W h x hp v) := by
  simpa only [seedMap, seedRep, seedData, fixedRho_L] using universalMap_intertwines
    (seedRep W) x (seedHighest W h x hp) (VOA.L n) v

theorem seedMap_word (W : VertexOperatorAlgebra V) (h : ℤ) (x : V)
    (hp : x ∈ prim W h) (w : List ℕ) :
    seedMap W h x hp (negWord W.centralCharge (h : ℂ) w) = virWord W w x := by
  induction w with
  | nil => exact universalMap_highestVector _ _ _
  | cons i w ih =>
    rw [negWord_cons, seedMap_mode, ih]
    rfl

theorem seedMap_mem_grading (W : VertexOperatorAlgebra V) (h : ℤ) (x : V)
    (hp : x ∈ prim W h) (N : ℕ) (v : Verma W.centralCharge (h : ℂ))
    (hv : v ∈ sortedSpan _ _ N) : seedMap W h x hp v ∈ W.grading (h+(N : ℤ)) := by
  obtain ⟨a,rfl⟩ := exists_vermaLevelState _ _ N v hv
  simp only [vermaLevelState, map_sum, map_smul]
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  rw [seedMap_word]
  have hg := OrbOctaR.virWord_grading W ((mem_prim W).mp hp).1 w.val
  have he : OrbOctaR.wordWeight w.val = N := by
    simpa [OrbOctaR.wordWeight, energyHW] using w.property.2
  rwa [he] at hg

theorem seedMap_kernel_le_radical (W : VertexOperatorAlgebra V) (h : ℤ) (x : V)
    (hp : x ∈ prim W h) (hne : x ≠ 0) :
    LinearMap.ker (seedMap W h x hp) ≤ vermaRadical W.centralCharge (h : ℂ) := by
  apply verma_proper_submodule_le_radical _ _ _
  · intro m v hv
    change seedMap W h x hp (vermaMode _ _ m v) = 0
    rw [seedMap_mode, show seedMap W h x hp v = 0 from hv, map_zero]
  · intro ht
    have hh : highestVector W.centralCharge (h : ℂ) ∈
        LinearMap.ker (seedMap W h x hp) := ht ▸ Submodule.mem_top
    change seedMap W h x hp (highestVector _ _) = 0 at hh
    rw [seedMap, universalMap_highestVector] at hh
    exact hne hh

/-- The genuine BSA terminal source, at c=1 and h=36, vanishes in the
actual icosahedral primary channel by the proved positive-mode rigidity. -/
theorem Xico_seedMap_s13_zero :
    seedMap Wi 36 Xico OrbIcoZ.X_primary
      (vermaBSASource Wi.centralCharge (36 : ℂ) 1 13 13) = 0 := by
  have hc : Wi.centralCharge = 1 := by
    change (V2m 1 le_rfl).centralCharge = 1
    simpa using V2m_centralCharge 1 le_rfl
  have hpos : vermaMode Wi.centralCharge (36:ℂ) 1
      (vermaBSASource Wi.centralCharge (36:ℂ) 1 13 13) = 0 ∧
      vermaMode Wi.centralCharge (36:ℂ) 2
      (vermaBSASource Wi.centralCharge (36:ℂ) 1 13 13) = 0 := by
    have haux (c : ℂ) (hc : c=1) : vermaMode c (36:ℂ) 1
        (vermaBSASource c (36:ℂ) 1 13 13) = 0 ∧
        vermaMode c (36:ℂ) 2 (vermaBSASource c (36:ℂ) 1 13 13) = 0 := by
      subst c
      have he := vermaBSASource_one_two_all (1:ℂ) 13 one_ne_zero (by norm_num)
      have transfer (c h : ℂ) (hc : c=1) (hh : h=36)
          (he : vermaMode c h 1 (vermaBSASource c h 1 13 13) = 0 ∧
            vermaMode c h 2 (vermaBSASource c h 1 13 13) = 0) :
          vermaMode 1 36 1 (vermaBSASource 1 36 1 13 13) = 0 ∧
            vermaMode 1 36 2 (vermaBSASource 1 36 1 13 13) = 0 := by
        subst c
        subst h
        exact he
      exact transfer _ _ (by norm_num [vermaBSACharge])
        (by norm_num [vermaBSAWeight]) he
    exact haux _ hc
  apply sixth_channel_positive_rigidity 49 (by norm_num) (by norm_num)
  · simpa using seedMap_mem_grading Wi 36 Xico OrbIcoZ.X_primary 13 _
      (vermaBSASource_mem_level _ _ _ _ _)
  · rw [← seedMap_mode]
    have hz : vermaMode Wi.centralCharge ((36 : ℤ) : ℂ) 1
        (vermaBSASource Wi.centralCharge 36 1 13 13) = 0 := hpos.1
    rw [hz, map_zero]
  · rw [← seedMap_mode]
    have hz : vermaMode Wi.centralCharge ((36 : ℤ) : ℂ) 2
        (vermaBSASource Wi.centralCharge 36 1 13 13) = 0 := hpos.2
    rw [hz, map_zero]

end VOA.Classification.COne.OrbIcoV
