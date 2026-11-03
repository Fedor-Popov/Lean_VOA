/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2JointPBW

/-!
# Actual affine Gram blocks and their quotient relations

The canonical form pairs equal energies and opposite Cartan charges. Thus a
row relation in a joint Gram block annihilates the entire universal module,
not merely the selected columns. It lies in the actual maximal ideal and
vanishes in the simple quotient. This is a proved radical extraction; no
root, rank defect, or determinant formula is assumed or concluded here.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.Inst Sl2Sing VertexOperatorAlgebra
open AffineSl2PBWWakimotoReduction
open Module (End)
variable (k : ℂ) (hk : k + 2 ≠ 0)
local notation "I" => QuotVOA.maxGradedIdeal (universal k hk)

/-- The universal canonical form is fully invariant, by the proved vacuum
nonvanishing and quasi-primarity of the weight-one currents. -/
theorem universalForm_invariant : (universalForm k hk).IsFullyInvariant :=
  canonicalInvariantForm_isFullyInvariant
    (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k hk) (LQ43.L1_grading_one k hk)

/-- The universal canonical form has vacuum norm one at every noncritical level. -/
theorem universalForm_normalized : (universalForm k hk).Normalized :=
  canonicalInvariantForm_normalized
    (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k hk) (LQ43.L1_grading_one k hk)

/-- A Cartan mode is skew-adjoint for the canonical bilinear form. Therefore
states with charges that do not sum to zero are orthogonal. -/
theorem universalForm_charge_orthogonal (x y : WakModule k) (h h' : ℤ)
    (hx : J k colH 0 x = (h:ℂ) • x) (hy : J k colH 0 y = (h':ℂ) • y)
    (hne : h + h' ≠ 0) : (universalForm k hk).form x y = 0 := by
  have ha := LQ43.weightOne_adj (universalForm_invariant k hk)
    (currentState_mem_grading k hk colH)
    (LQ43.L1_grading_one k hk _ (currentState_mem_grading k hk colH)) 0 x y
  simp only [smul_currentState_eq_J, neg_zero, hx, hy, map_smul,
    LinearMap.smul_apply, smul_eq_mul] at ha
  have hn : (h:ℂ) + (h':ℂ) ≠ 0 := by exact_mod_cast hne
  exact (mul_eq_zero.mp (by linear_combination ha :
    ((h:ℂ)+(h':ℂ)) * (universalForm k hk).form x y = 0)).resolve_left hn

/-- For a state of joint weight (n,h), only the opposite joint block (n,−h)
can pair nontrivially. This is ordinary energy and Cartan orthogonality. -/
theorem universalForm_joint_orthogonal (n h n' h' : ℤ) (x y : WakModule k)
    (hx : x ∈ jointSpace k hk n h) (hy : y ∈ jointSpace k hk n' h')
    (hne : n ≠ n' ∨ h + h' ≠ 0) : (universalForm k hk).form x y = 0 := by
  rcases hne with hn | hh
  · exact (universalForm k hk).orthogonal_of_ne hn
      (jointSpace_le_grading k hk n h hx) (jointSpace_le_grading k hk n' h' hy)
  · exact universalForm_charge_orthogonal k hk x y h h'
      ((mem_jointSpace_iff k hk n h x).mp hx).2
      ((mem_jointSpace_iff k hk n' h' y).mp hy).2 hh

/-- A homogeneous joint state is in the actual maximal ideal exactly when
its row on the opposite joint PBW basis vanishes. Other PBW columns vanish
by the proved energy/Cartan orthogonality. -/
theorem joint_mem_maxIdeal_iff (n h : ℤ) (x : WakModule k)
    (hx : x ∈ jointSpace k hk n h) :
    x ∈ I ↔ ∀ j : JointIndex n (-h),
      (universalForm k hk).form x (currentPBWBasis k hk j.val) = 0 := by
  rw [LiRadical.mem_maxGradedIdeal_iff (universalForm_invariant k hk) (universalForm_normalized k hk)]
  constructor
  · intro hz j; exact hz _
  · intro hz y
    have he : (universalForm k hk).form x = 0 := by
      apply (currentPBWBasis k hk).ext
      intro mu
      change (universalForm k hk).form x (currentPBWBasis k hk mu) = 0
      by_cases hm : currentEnergy mu = n ∧ currentCharge mu = -h
      · exact hz ⟨mu,hm⟩
      · have hy : currentPBWBasis k hk mu ∈
            jointSpace k hk (currentEnergy mu) (currentCharge mu) :=
          Submodule.subset_span ⟨⟨mu,rfl,rfl⟩,rfl⟩
        apply universalForm_joint_orthogonal k hk n h _ _ x _ hx hy
        omega
    exact LinearMap.congr_fun he y

/-- Literal negative mode indices of the fixed PBW word for a joint index.
The words and their index set are independent of the central level. -/
def jointWord (n h : ℤ) (i : JointIndex n h) : List (Fin 3 × ℤ) :=
  (orderedPBWColorWord i.val).map (fun an => (an.1,-(an.2:ℤ)-1))

/-- Evaluating the literal joint word gives exactly the original PBW vector. -/
theorem jointWord_state (n h : ℤ) (i : JointIndex n h) :
    NormalOrdering.currentWord (J k) (jointWord n h i) (universal k hk).vacuum =
      currentPBWBasis k hk i.val := by
  rw [currentPBWBasis_apply]
  have hw (w : List (Fin 3 × ℕ)) :
      NormalOrdering.currentWord (J k) (w.map (fun an => (an.1,-(an.2:ℤ)-1)))
        (universal k hk).vacuum = wordStateA k w := by
    induction w with
    | nil => rfl
    | cons an w ih => simp only [List.map_cons, NormalOrdering.currentWord,
        Module.End.mul_apply, ih, wordStateA_cons]
  exact hw _

/-- The finite polynomial Gram block pairs the PBW space (n,h) with (n,−h).
This definition retains separate row and column index types. No assertion
about a determinant root or equality of the two dimensions is implicit. -/
noncomputable def jointGramPolynomial (n h : ℤ) :
    Matrix (JointIndex n h) (JointIndex n (-h)) (Polynomial ℂ) :=
  wordGramMatrix (jointWord n h) (jointWord n (-h))

/-- Every entry of the fixed polynomial block is the actual normalized
canonical pairing of the corresponding universal joint PBW states. -/
theorem jointGramPolynomial_eval (hk0 : k ≠ 0) (n h : ℤ)
    (i : JointIndex n h) (j : JointIndex n (-h)) :
    (jointGramPolynomial n h i j).eval k =
      (universalForm k hk).form (currentPBWBasis k hk i.val) (currentPBWBasis k hk j.val) := by
  change (wordGramPolynomial _ _).eval k = _
  rw [wordGramPolynomial_universal k hk hk0, jointWord_state, jointWord_state]

/-- A left-kernel row of the actual joint polynomial Gram block gives an
ordinary finite relation in the simple quotient. No singular-vector
presentation of the maximal ideal is needed for this extraction. -/
theorem jointGram_row_relation (hk0 : k ≠ 0) (n h : ℤ) (r : JointIndex n h → ℂ)
    (hr : ∀ j, ∑ i, r i * (jointGramPolynomial n h i j).eval k = 0) :
    ∑ i, r i • currentWord k hk (jointWord n h i) (simple k hk).vacuum = 0 := by
  have hx : (∑ i, r i • currentPBWBasis k hk i.val) ∈ jointSpace k hk n h :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))
  have hm := (joint_mem_maxIdeal_iff k hk n h _ hx).mpr (fun j => by
    simpa only [jointGramPolynomial_eval k hk hk0, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul] using hr j)
  have hz : (I).mkQ (∑ i, r i • currentPBWBasis k hk i.val) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  simpa only [map_sum, map_smul, ← jointWord_state, universalWord_mkQ] using hz

end VOA.AffineSl2GeneralRigidity
