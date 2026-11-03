/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2UniversalGram
import VOA.Examples.AffineSl2NonLisse

/-!
# Actual simultaneous energy and Cartan spaces of the affine vacuum module

The existing affine PBW basis consists of simultaneous eigenvectors of L₀
and h₀. Restricting its indices by their two integer labels gives a basis of
the actual simultaneous eigenspace. These are finite spaces; the argument
uses the proved PBW basis and the VOA's finite-dimensional energy spaces.
No determinant or singular-existence theorem is assumed.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.Inst AffineLie Sl2Sing Sl2NonLisse
open AffineSl2PBWWakimotoReduction AffineSl2UniversalC2PBW
open Module (End)
variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- PBW multiplicities of the three current colours and all negative depths. -/
abbrev CurrentIndex := (Fin 3 ×ₗ ℕ) →₀ ℕ

/-- The proved universal basis, with the original ordered creation states
as its vectors. Choice selects a witness of the already proved PBW theorem. -/
noncomputable def currentPBWBasis : Module.Basis CurrentIndex ℂ (WakModule k) :=
  Classical.choose (AffineSl2WakimotoLiLeading.affineSl2PBWBasis k hk)

/-- No rescaling is hidden in the chosen basis: each vector is the explicit
ordered current word attached to its multiplicity function. -/
theorem currentPBWBasis_apply (mu : CurrentIndex) :
    currentPBWBasis k hk mu = wordStateA k (orderedPBWColorWord mu) := by
  rw [currentPBWBasis, Classical.choose_spec
    (AffineSl2WakimotoLiLeading.affineSl2PBWBasis k hk)]
  exact orderedCreationState_eq_wordStateA k mu

/-- The integer energy label of a PBW monomial. -/
def currentEnergy (mu : CurrentIndex) : ℤ := wordDegA (orderedPBWColorWord mu)

/-- The actual h₀ charge of a PBW monomial, with contributions +2, −2, 0
from the e, f, h colours respectively. -/
def currentCharge (mu : CurrentIndex) : ℤ := wordCharge (orderedPBWColorWord mu)

/-- Every negative current word is homogeneous of the sum of its creation
energies. This follows directly from the current's weight-one grading. -/
theorem creation_state_grading (w : List (Fin 3 × ℕ)) :
    wordStateA k w ∈ (universal k hk).grading (wordDegA w) := by
  induction w with
  | nil => exact (universal k hk).vacuum_mem
  | cons an w ih =>
    rw [wordStateA_cons, ← smul_currentState_eq_J k hk]
    have h := (universal k hk).smul_mem_grading (currentState_mem_grading k hk an.1)
      ih (-(an.2:ℤ)-1)
    convert h using 1 <;> simp only [wordDegA_cons] <;> congr 1 <;> omega

/-- Energy acts diagonally on the actual PBW basis. -/
theorem currentPBWBasis_L0 (mu : CurrentIndex) :
    (universal k hk).L 0 (currentPBWBasis k hk mu) =
      (currentEnergy mu : ℂ) • currentPBWBasis k hk mu := by
  rw [currentPBWBasis_apply]
  exact (universal k hk).L_zero_grading _ (creation_state_grading k hk _)

/-- Cartan acts diagonally on the same actual PBW basis. -/
theorem currentPBWBasis_H0 (mu : CurrentIndex) :
    J k colH 0 (currentPBWBasis k hk mu) =
      (currentCharge mu : ℂ) • currentPBWBasis k hk mu := by
  rw [currentPBWBasis_apply]
  exact H0_wordStateA k _

/-- A diagonal operator multiplies each basis coordinate by its corresponding
eigenvalue. This elementary observation is applied to both energy and Cartan. -/
theorem basis_diagonal_coordinate {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (b : Module.Basis ι ℂ V) (T : End ℂ V) (d : ι → ℂ)
    (hd : ∀ i, T (b i) = d i • b i) (x : V) (i : ι) :
    b.repr (T x) i = d i * b.repr x i := by
  classical
  let E : V →ₗ[ℂ] ℂ := (Finsupp.lapply i).comp b.repr.toLinearMap
  have he : E.comp T = d i • E := by
    apply b.ext
    intro j
    change b.repr (T (b j)) i = d i * b.repr (b j) i
    rw [hd, map_smul, Finsupp.smul_apply, smul_eq_mul, b.repr_self]
    by_cases h : j = i
    · subst j; simp
    · simp [h, Ne.symm h]
  exact LinearMap.congr_fun he x

/-- A coordinate away from an eigenvector's eigenvalue must vanish. -/
theorem basis_eigen_coordinate_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (b : Module.Basis ι ℂ V) (T : End ℂ V) (d : ι → ℂ)
    (hd : ∀ i, T (b i) = d i • b i) (x : V) (z : ℂ)
    (hx : T x = z • x) (i : ι) (hi : d i ≠ z) : b.repr x i = 0 := by
  have he := basis_diagonal_coordinate b T d hd x i
  rw [hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at he
  exact (mul_eq_zero.mp (by linear_combination -he :
    (d i - z) * b.repr x i = 0)).resolve_left (sub_ne_zero.mpr hi)

/-- Indices selecting one simultaneous integer energy and Cartan charge.
This index type is independent of the central level. -/
def JointIndex (n h : ℤ) := {mu : CurrentIndex // currentEnergy mu = n ∧ currentCharge mu = h}

/-- The span of the PBW vectors with the selected pair of labels. -/
noncomputable def jointSpace (n h : ℤ) : Submodule ℂ (WakModule k) :=
  Submodule.span ℂ (Set.range (fun i : JointIndex n h => currentPBWBasis k hk i.val))

/-- The selected PBW span is exactly the actual simultaneous L₀ and h₀
eigenspace. Both inclusions use the actual operator actions, not just labels. -/
theorem mem_jointSpace_iff (n h : ℤ) (x : WakModule k) :
    x ∈ jointSpace k hk n h ↔
      (universal k hk).L 0 x = (n:ℂ) • x ∧ J k colH 0 x = (h:ℂ) • x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩ := hy
      exact ⟨by rw [currentPBWBasis_L0, i.property.1],
        by rw [currentPBWBasis_H0, i.property.2]⟩
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ha.1, ha.2, hb.1, hb.2, smul_add, and_self]
    | smul a b _ hb =>
      constructor
      · rw [map_smul, hb.1, smul_comm]
      · rw [map_smul, hb.2, smul_comm]
  · rintro ⟨hn,hh⟩
    rw [← (currentPBWBasis k hk).linearCombination_repr x]
    change (∑ mu ∈ ((currentPBWBasis k hk).repr x).support,
      (currentPBWBasis k hk).repr x mu • currentPBWBasis k hk mu) ∈ _
    apply Submodule.sum_mem
    intro mu hmu
    by_cases he : currentEnergy mu = n ∧ currentCharge mu = h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨mu,he⟩,rfl⟩)
    · have hz : (currentPBWBasis k hk).repr x mu = 0 := by
        by_cases hm : currentEnergy mu = n
        · apply basis_eigen_coordinate_zero (currentPBWBasis k hk) (J k colH 0)
            (fun mu => (currentCharge mu:ℂ)) (currentPBWBasis_H0 k hk) x h hh mu
          exact_mod_cast (show currentCharge mu ≠ h from fun hc => he ⟨hm,hc⟩)
        · apply basis_eigen_coordinate_zero (currentPBWBasis k hk) ((universal k hk).L 0)
            (fun mu => (currentEnergy mu:ℂ)) (currentPBWBasis_L0 k hk) x n hn mu
          exact_mod_cast hm
      rw [hz,zero_smul]
      exact Submodule.zero_mem _

/-- Restricting the already independent PBW family to the joint indices
preserves independence; no new representation-theoretic assumption is needed. -/
theorem jointWords_linearIndependent (n h : ℤ) :
    LinearIndependent ℂ (fun i : JointIndex n h => currentPBWBasis k hk i.val) :=
  (currentPBWBasis k hk).linearIndependent.comp _ Subtype.val_injective

/-- The actual basis of each joint eigenspace, with the same PBW normalization. -/
noncomputable def jointBasis (n h : ℤ) : Module.Basis (JointIndex n h) ℂ (jointSpace k hk n h) :=
  Module.Basis.span (jointWords_linearIndependent k hk n h)

/-- The joint basis vector is the corresponding original universal PBW vector. -/
theorem jointBasis_apply (n h : ℤ) (i : JointIndex n h) :
    (jointBasis k hk n h i : WakModule k) = currentPBWBasis k hk i.val :=
  Module.Basis.coe_span_apply _ _

/-- Every joint space lies in its ordinary energy grade. -/
theorem jointSpace_le_grading (n h : ℤ) : jointSpace k hk n h ≤ (universal k hk).grading n := by
  rw [jointSpace, Submodule.span_le]
  rintro y ⟨i,rfl⟩
  change currentPBWBasis k hk i.val ∈ _
  rw [currentPBWBasis_apply]
  have hi := creation_state_grading k hk (orderedPBWColorWord i.val)
  change _ ∈ (universal k hk).grading (currentEnergy i.val) at hi
  simpa only [i.property.1] using hi

/-- Joint spaces are finite-dimensional, as subspaces of a VOA energy grade. -/
instance jointSpace_finiteDimensional (n h : ℤ) : FiniteDimensional ℂ (jointSpace k hk n h) := by
  letI := (universal k hk).finrank n
  exact Submodule.finiteDimensional_of_le (jointSpace_le_grading k hk n h)

/-- The joint index set is finite, independently of the level. Its concrete
PBW vectors inject into a finite-dimensional energy space at level one. -/
instance jointIndex_finite (n h : ℤ) : Finite (JointIndex n h) :=
  (jointBasis 1 (by norm_num) n h).linearIndependent.finite

/-- A finite enumeration of the joint indices, for finite Gram matrices. -/
noncomputable instance jointIndex_fintype (n h : ℤ) : Fintype (JointIndex n h) :=
  Fintype.ofFinite _

/-- The joint-space dimension is precisely the number of its PBW indices. -/
theorem jointSpace_finrank (n h : ℤ) :
    Module.finrank ℂ (jointSpace k hk n h) = Fintype.card (JointIndex n h) :=
  Module.finrank_eq_card_basis (jointBasis k hk n h)

end VOA.AffineSl2GeneralRigidity
