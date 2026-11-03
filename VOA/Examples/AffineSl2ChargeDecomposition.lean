/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2SimpleCharacterRank
import VOA.Examples.AffineSl2ParabolicCharacter

/-! # Finite charge decompositions of the actual affine conformal grades -/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineLie Sl2Sing Sl2NonLisse AffineSl2PBWWakimotoReduction
noncomputable section

/-- Root-charge window containing every negative-current PBW state of energy N. -/
def chargeWindow (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

theorem currentCharge_even (mu : CurrentIndex) : ∃ c : ℤ, currentCharge mu = 2*c := by
  suffices H : ∀ w : List (Fin 3×ℕ),∃ c : ℤ,wordCharge w=2*c from H _
  intro w
  induction w with
  | nil => exact ⟨0,rfl⟩
  | cons an w ih =>
    obtain ⟨c,hc⟩ := ih
    rcases an with ⟨a,n⟩
    fin_cases a
    · exact ⟨c+1,by simp [wordCharge,colourCharge,hc]; ring⟩
    · exact ⟨c-1,by simp [wordCharge,colourCharge,hc]; ring⟩
    · exact ⟨c,by simp [wordCharge,colourCharge,hc]⟩

theorem currentCharge_bounds (mu : CurrentIndex) :
    -(2*currentEnergy mu) ≤ currentCharge mu ∧ currentCharge mu ≤ 2*currentEnergy mu := by
  have hu := wordCharge_le_twice_wordDeg (orderedPBWColorWord mu)
  have hl := wordCharge_le_twice_wordDeg (orderedPBWColorWord (flipCurrentIndex mu))
  change currentCharge mu ≤ 2*currentEnergy mu at hu
  change currentCharge (flipCurrentIndex mu) ≤ 2*currentEnergy (flipCurrentIndex mu) at hl
  rw [currentCharge_flip,currentEnergy_flip] at hl
  constructor <;> omega

theorem jointIndex_charge_mem_window (N : ℕ) (c : ℤ) (i : JointIndex N (2*c)) :
    c ∈ chargeWindow N := by
  have h := currentCharge_bounds i.val
  rw [i.property.1,i.property.2] at h
  simp only [chargeWindow,Finset.mem_Icc]
  omega

/-- The actual universal conformal grade is the finite sum of its integer root charges. -/
theorem universal_grading_eq_joint_sum (k : ℂ) (hk : k+2≠0) (N : ℕ) :
    (universal k hk).grading N = ⨆ c ∈ chargeWindow N,jointSpace k hk N (2*c) := by
  apply le_antisymm
  · intro x hx
    have hl := (universal k hk).L_zero_grading x hx
    rw [← (currentPBWBasis k hk).linearCombination_repr x]
    change (∑ mu ∈ ((currentPBWBasis k hk).repr x).support,
      (currentPBWBasis k hk).repr x mu • currentPBWBasis k hk mu) ∈ _
    apply Submodule.sum_mem
    intro mu hm
    have hn : currentEnergy mu=(N : ℤ) := by
      by_contra hn
      have hz := basis_eigen_coordinate_zero (currentPBWBasis k hk) ((universal k hk).L 0)
        (fun mu => (currentEnergy mu : ℂ)) (currentPBWBasis_L0 k hk) x N hl mu
        (by
          intro he
          apply hn
          change (currentEnergy mu : ℂ) = (N : ℂ) at he
          exact_mod_cast he)
      exact (Finsupp.mem_support_iff.mp hm) hz
    obtain ⟨c,hc⟩ := currentCharge_even mu
    have hw := jointIndex_charge_mem_window N c ⟨mu,hn,hc⟩
    apply Submodule.smul_mem
    exact Submodule.mem_iSup_of_mem c
      (Submodule.mem_iSup_of_mem hw (Submodule.subset_span ⟨⟨mu,hn,hc⟩,rfl⟩))
  · exact iSup_le (fun c => iSup_le (fun _ => jointSpace_le_grading k hk N (2*c)))

/-- The true simple conformal grade inherits the same finite charge decomposition. -/
theorem simple_grading_eq_joint_sum (k : ℂ) (hk : k+2≠0) (N : ℕ) :
    (simple k hk).grading N = ⨆ c ∈ chargeWindow N,simpleJointPiece k hk N (2*c) := by
  change ((universal k hk).grading N).map (QuotVOA.maxGradedIdeal (universal k hk)).mkQ = _
  rw [universal_grading_eq_joint_sum,Submodule.map_iSup]
  simp only [Submodule.map_iSup,simpleJointPiece]

/-- Distinct integer charges remain independent after the actual maximal-ideal quotient. -/
theorem simpleJointPiece_iSupIndep (k : ℂ) (hk : k+2≠0) (N : ℕ) :
    iSupIndep (fun c : ℤ => simpleJointPiece k hk N (2*c)) := by
  let H : Module.End ℂ (WakModule k ⧸ QuotVOA.maxGradedIdeal (universal k hk)) :=
    mode ((simple k hk).Y (simpleCurrent k hk 2)) 0
  have hi : Function.Injective (fun c : ℤ => ((2*c : ℤ) : ℂ)) := by
    intro a b hab
    change ((2*a : ℤ) : ℂ) = ((2*b : ℤ) : ℂ) at hab
    have h : (2*a : ℤ)=2*b := Int.cast_injective hab
    omega
  apply ((H.eigenspaces_iSupIndep).comp hi).mono
  intro c x hx
  obtain ⟨y,hy,rfl⟩ := hx
  change _ ∈ H.eigenspace ((2*c : ℤ) : ℂ)
  rw [Module.End.mem_eigenspace_iff]
  change (simple k hk).smul (simpleCurrent k hk 2) 0
    ((QuotVOA.maxGradedIdeal (universal k hk)).mkQ y) = _
  rw [simpleCurrent_mode_mkQ]
  have hh := ((mem_jointSpace_iff k hk N (2*c) y).mp hy).2
  change J k 2 0 y = _ at hh
  rw [hh,map_smul]

private theorem finite_independent_sum_dimension {ι V : Type*}
    [AddCommGroup V] [Module ℂ V] (p : ι → Submodule ℂ V) (hp : iSupIndep p)
    [∀ i,FiniteDimensional ℂ (p i)] (s : Finset ι) :
    FiniteDimensional ℂ ↥(⨆ i ∈ s,p i) ∧
      Module.finrank ℂ ↥(⨆ i ∈ s,p i) = ∑ i ∈ s,Module.finrank ℂ (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (⨆ i ∈ (∅ : Finset ι),p i)=⊥ := by simp
    rw [h0,Finset.sum_empty,finrank_bot]
    exact ⟨inferInstance,rfl⟩
  | insert a s ha ih =>
    obtain ⟨hfd,hrk⟩ := ih
    rw [Finset.iSup_insert,Finset.sum_insert ha]
    have hd : Disjoint (p a) (⨆ i ∈ s,p i) := by
      have := hp.disjoint_biSup (y := (s : Set ι)) (by simpa using ha)
      simpa using this
    refine ⟨inferInstance,?_⟩
    have h := Submodule.finrank_sup_add_finrank_inf_eq (p a) (⨆ i ∈ s,p i)
    rw [hd.eq_bot,finrank_bot,add_zero] at h
    rw [h,hrk]

/-- Exact actual simple dimension is the finite sum of the proved joint dimensions. -/
theorem simple_grading_finrank_eq_sum_joint (k : ℂ) (hk : k+2≠0) (N : ℕ) :
    Module.finrank ℂ ((simple k hk).grading N) =
      ∑ c ∈ chargeWindow N,Module.finrank ℂ (simpleJointPiece k hk N (2*c)) := by
  letI (c : ℤ) : Module.Finite ℂ (simpleJointPiece k hk N (2*c)) := by
    change Module.Finite ℂ ((jointSpace k hk N (2*c)).map
      (QuotVOA.maxGradedIdeal (universal k hk)).mkQ)
    infer_instance
  rw [simple_grading_eq_joint_sum]
  exact (finite_independent_sum_dimension _ (simpleJointPiece_iSupIndep k hk N) (chargeWindow N)).2

/-- The universal charge spaces are independent eigenspaces of its actual Cartan operator. -/
theorem universalJointSpace_iSupIndep (k : ℂ) (hk : k+2≠0) (N : ℕ) :
    iSupIndep (fun c : ℤ => jointSpace k hk N (2*c)) := by
  have hi : Function.Injective (fun c : ℤ => ((2*c : ℤ) : ℂ)) := by
    intro a b hab
    change ((2*a : ℤ) : ℂ)=((2*b : ℤ) : ℂ) at hab
    have h : (2*a : ℤ)=2*b := Int.cast_injective hab
    omega
  apply (((J k colH 0).eigenspaces_iSupIndep).comp hi).mono
  intro c x hx
  exact Module.End.mem_eigenspace_iff.mpr ((mem_jointSpace_iff k hk N (2*c) x).mp hx).2

/-- Summing the finite PBW charge counts gives the actual universal conformal dimension. -/
theorem universal_grading_finrank_eq_sum_joint (k : ℂ) (hk : k+2≠0) (N : ℕ) :
    Module.finrank ℂ ((universal k hk).grading N) =
      ∑ c ∈ chargeWindow N,Fintype.card (JointIndex N (2*c)) := by
  rw [universal_grading_eq_joint_sum,
    (finite_independent_sum_dimension _ (universalJointSpace_iSupIndep k hk N) (chargeWindow N)).2]
  exact Finset.sum_congr rfl (fun c _ => jointSpace_finrank k hk N (2*c))

/-- All PBW occupation indices in one actual conformal energy. -/
def EnergyIndex (N : ℕ) := {mu : CurrentIndex // currentEnergy mu=(N : ℤ)}

/-- The actual homogeneous PBW family spans its conformal grade. -/
theorem energySpan_eq_grading (k : ℂ) (hk : k+2≠0) (N : ℕ) :
    Submodule.span ℂ (Set.range (fun i : EnergyIndex N => currentPBWBasis k hk i.val)) =
      (universal k hk).grading N := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    change currentPBWBasis k hk i.val ∈ (universal k hk).grading N
    rw [currentPBWBasis_apply]
    have h := creation_state_grading k hk (orderedPBWColorWord i.val)
    change _ ∈ (universal k hk).grading (currentEnergy i.val) at h
    simpa only [i.property] using h
  · rw [universal_grading_eq_joint_sum]
    refine iSup_le fun c => iSup_le fun hc => ?_
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact Submodule.subset_span ⟨⟨i.val,i.property.1⟩,rfl⟩

/-- An actual homogeneous basis indexed by exactly the positive-energy occupations. -/
def energyBasis (k : ℂ) (hk : k+2≠0) (N : ℕ) :
    Module.Basis (EnergyIndex N) ℂ ((universal k hk).grading N) :=
  (Module.Basis.span ((currentPBWBasis k hk).linearIndependent.comp
    (fun i : EnergyIndex N => i.val) Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ (energySpan_eq_grading k hk N))

instance energyIndex_finite (N : ℕ) : Finite (EnergyIndex N) := by
  have hk : (1 : ℂ)+2≠0 := by norm_num
  letI := (universal 1 hk).finrank (N : ℤ)
  exact (energyBasis 1 hk N).linearIndependent.finite

theorem universal_grading_finrank_eq_energy_count (k : ℂ) (hk : k+2≠0) (N : ℕ) :
    Module.finrank ℂ ((universal k hk).grading N) = Nat.card (EnergyIndex N) := by
  letI := Fintype.ofFinite (EnergyIndex N)
  rw [Nat.card_eq_fintype_card]
  exact Module.finrank_eq_card_basis (energyBasis k hk N)

end
end VOA.AffineSl2GeneralRigidity
