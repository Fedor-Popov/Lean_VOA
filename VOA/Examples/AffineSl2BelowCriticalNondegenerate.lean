/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumDeterminantOrder
import VOA.Examples.AffineSl2VacuumChevalleyGram
import VOA.Examples.AffineSl2JointGram

/-!
# The universal affine `sl₂` vacuum form is nondegenerate below the critical level

For every real `k < -2`, the normalized canonical invariant form of `V^k(sl₂)` is nondegenerate
on every conformal weight space.

The proof reads off the all-degree order formula `vacuum_determinant_order` of the actual
Chevalley-twisted vacuum Gram determinant: its order at `k` is the weighted count of
nonhorizontal real-root resonances `realRootWeight (k+2) i = 0`, and for real `k + 2 < 0` none of
these resonances occur (`vacuumOrder_eq_zero_of_lt`).  Hence every joint (energy, charge) block
of the twisted Gram matrix `B(θ b_i, b_j)` (`θ = vacuumChevalley`) is invertible, and a vector
orthogonal to a whole weight space has all PBW coordinates zero.

Main results (unconditional):

* `vacuumOrder_eq_zero_of_lt` — no vacuum resonance for real `k < -2`;
* `vacuumChevalleyPolynomial_det_eval_ne_zero` — every vacuum joint block determinant is
  nonzero at real `k < -2`;
* `universalForm_separating_of_lt` — the full weight-`E` form separates in its second slot.
-/

namespace VOA

namespace AffineSl2BelowCritical

open Polynomial AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineVOA.HighestModule
open Wak.Charged
open scoped Classical

noncomputable section

/-- A real level below critical, as a complex number, is noncritical. -/
theorem noncritical_of_lt {x : ℝ} (hx : x < -2) : ((x : ℂ) + 2) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- **No vacuum resonance below the critical level.**  For real `x < -2` every nonhorizontal
real-root label of every joint block has `realRootWeight (x+2) i ≠ 0`. -/
theorem vacuumOrder_eq_zero_of_lt {x : ℝ} (hx : x < -2) (n : ℕ) (c : ℤ) :
    vacuumOrder (x : ℂ) n c = 0 := by
  unfold vacuumOrder
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [if_neg]
  intro hz
  obtain ⟨hne, hlab⟩ := Finset.mem_erase.mp hi
  have h2 := (affineKacLabels_bounds n c i hlab).1
  rcases i with ⟨⟨a, m⟩, r⟩
  simp only [realRootWeight, realRootSlope, realRootOffset] at hz h2
  have hre := congrArg Complex.re hz
  fin_cases a
  · simp at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  · simp at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      simp at hre
      have hr0 : r = 0 := by exact_mod_cast hre
      subst hr0
      exact hne rfl
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
      nlinarith
  · exact h2 rfl

/-- **Every vacuum joint block determinant is nonzero below the critical level.** -/
theorem vacuumChevalleyPolynomial_det_eval_ne_zero {x : ℝ} (hx : x < -2) (n : ℕ) (c : ℤ) :
    (vacuumChevalleyPolynomial n c).det.eval (x : ℂ) ≠ 0 := by
  have hord := vacuum_determinant_order (x : ℂ) (noncritical_of_lt hx) n c
  rw [vacuumOrder_eq_zero_of_lt hx, Nat.zero_sub] at hord
  intro hroot
  have hpos := (Polynomial.rootMultiplicity_pos (vacuumChevalleyPolynomial_det_ne_zero n c)).mpr
    hroot
  omega

/-- Every PBW monomial has even Cartan charge. -/
theorem even_wordCharge (w : List (Fin 3 × ℕ)) : Even (Sl2NonLisse.wordCharge w) := by
  induction w with
  | nil => exact ⟨0, rfl⟩
  | cons b w ih =>
      obtain ⟨t, ht⟩ := ih
      change Even (Sl2NonLisse.colourCharge b.1 + Sl2NonLisse.wordCharge w)
      rw [ht]
      rcases b with ⟨a, m⟩
      fin_cases a
      · exact ⟨t + 1, by simp [Sl2NonLisse.colourCharge]; ring⟩
      · exact ⟨t - 1, by simp [Sl2NonLisse.colourCharge]; ring⟩
      · exact ⟨t, by simp [Sl2NonLisse.colourCharge]⟩

theorem even_currentCharge (mu : CurrentIndex) : Even (currentCharge mu) :=
  even_wordCharge _

/-- **The full universal form separates on every weight space below the critical level.**
For real `x < -2`, a weight-`E` vector orthogonal (in the second slot) to all of `V_E` is zero. -/
theorem universalForm_separating_of_lt {x : ℝ} (hx : x < -2) (E : ℤ) :
    ∀ v ∈ (universal (x : ℂ) (noncritical_of_lt hx)).grading E,
      (∀ y ∈ (universal (x : ℂ) (noncritical_of_lt hx)).grading E,
        (universalForm (x : ℂ) (noncritical_of_lt hx)).form y v = 0) → v = 0 := by
  set k : ℂ := (x : ℂ) with hkx
  have hk : k + 2 ≠ 0 := noncritical_of_lt hx
  intro v hv hperp
  rcases lt_or_ge E 0 with hneg | hnn
  · have := (universal k hk).positivity E hneg
    rw [this] at hv
    exact (Submodule.mem_bot ℂ).mp hv
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
  set b := currentPBWBasis k hk with hb
  set B := universalForm k hk with hB
  -- energy coordinates
  have hL0 : (universal k hk).L 0 v = ((N : ℤ) : ℂ) • v := (universal k hk).L_zero_grading v hv
  have henergy : ∀ mu, currentEnergy mu ≠ (N : ℤ) → b.repr v mu = 0 := by
    intro mu hmu
    apply basis_eigen_coordinate_zero b ((universal k hk).L 0) (fun mu => (currentEnergy mu : ℂ))
      (currentPBWBasis_L0 k hk) v _ hL0 mu
    exact_mod_cast hmu
  -- it suffices to kill every coordinate
  suffices hcoord : ∀ mu, b.repr v mu = 0 by
    have : b.repr v = 0 := Finsupp.ext hcoord
    exact b.repr.injective (by rw [this, map_zero])
  intro mu0
  by_cases he : currentEnergy mu0 = (N : ℤ)
  swap
  · exact henergy mu0 he
  obtain ⟨c, hc⟩ := even_currentCharge mu0
  -- the joint block containing `mu0`
  let G : Matrix (JointIndex (N : ℤ) (2 * c)) (JointIndex (N : ℤ) (2 * c)) ℂ :=
    fun i j => B.form (vacuumChevalley k (b i.val)) (b j.val)
  have hG : G = (vacuumChevalleyPolynomial N c).map (Polynomial.eval k) := by
    ext i j
    simp only [G, Matrix.map_apply]
    rw [vacuumChevalleyPolynomial_actual k hk N c i j]
  have hdet : G.det ≠ 0 := by
    rw [hG, show (vacuumChevalleyPolynomial N c).map (Polynomial.eval k) =
      (Polynomial.evalRingHom k).mapMatrix (vacuumChevalleyPolynomial N c) from rfl,
      ← RingHom.map_det, Polynomial.coe_evalRingHom]
    exact vacuumChevalleyPolynomial_det_eval_ne_zero hx N c
  let w : JointIndex (N : ℤ) (2 * c) → ℂ := fun j => b.repr v j.val
  have hw : G.mulVec w = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, G, w]
    -- `θ b_i` lies in weight `N`
    have hθ : vacuumChevalley k (b i.val) ∈ (universal k hk).grading (N : ℤ) := by
      have hi : b i.val ∈ jointSpace k hk N (2 * c) := by
        rw [← jointBasis_apply k hk]
        exact (jointBasis k hk N (2 * c) i).2
      exact jointSpace_le_grading k hk _ _ (vacuumChevalley_mem_joint k hk _ _ _ hi)
    have h0 := hperp _ hθ
    -- expand `v` in the PBW basis
    rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum] at h0
    simp only [map_smul, smul_eq_mul] at h0
    rw [← h0]
    -- compare the two finite sums
    set f : CurrentIndex → ℂ := fun mu => b.repr v mu * B.form (vacuumChevalley k (b i.val)) (b mu)
      with hf
    have hfzero : ∀ mu, ¬ (currentEnergy mu = (N : ℤ) ∧ currentCharge mu = 2 * c) → f mu = 0 := by
      intro mu hmu
      by_cases hmuE : currentEnergy mu = (N : ℤ)
      · have hch : currentCharge mu ≠ 2 * c := fun h => hmu ⟨hmuE, h⟩
        have hθi : vacuumChevalley k (b i.val) ∈ jointSpace k hk N (-(2 * c)) := by
          apply vacuumChevalley_mem_joint
          rw [← jointBasis_apply k hk]
          exact (jointBasis k hk N (2 * c) i).2
        have hmuj : b mu ∈ jointSpace k hk (currentEnergy mu) (currentCharge mu) :=
          Submodule.subset_span ⟨⟨mu, rfl, rfl⟩, rfl⟩
        rw [hmuE] at hmuj
        simp only [hf]
        rw [universalForm_joint_orthogonal k hk _ _ _ _ _ _ hθi hmuj (Or.inr (by omega)),
          mul_zero]
      · simp only [hf]
        rw [henergy mu hmuE, zero_mul]
    let T : Finset CurrentIndex := Finset.univ.map
      ⟨fun j : JointIndex (N : ℤ) (2 * c) => j.val, Subtype.val_injective⟩
    have hT : ∑ j : JointIndex (N : ℤ) (2 * c), f j.val = ∑ mu ∈ T, f mu := by
      simp [T, Finset.sum_map]
    have hS : ∑ mu ∈ (b.repr v).support, f mu = ∑ mu ∈ T, f mu := by
      have h1 : ∑ mu ∈ (b.repr v).support, f mu = ∑ mu ∈ (b.repr v).support ∪ T, f mu :=
        Finset.sum_subset Finset.subset_union_left (fun mu _ hmu => by
          simp only [hf, Finsupp.notMem_support_iff.mp hmu, zero_mul])
      have h2 : ∑ mu ∈ T, f mu = ∑ mu ∈ (b.repr v).support ∪ T, f mu :=
        Finset.sum_subset Finset.subset_union_right (fun mu _ hmu => by
          by_cases hj : currentEnergy mu = (N : ℤ) ∧ currentCharge mu = 2 * c
          · let j : JointIndex (N : ℤ) (2 * c) := ⟨mu, hj⟩
            exact absurd (Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩) hmu
          · exact hfzero mu hj)
      rw [h1, h2]
    rw [hS, ← hT]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hf]
    ring
  have hw0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hw
  have := congrFun hw0 ⟨mu0, he, hc.trans (by ring)⟩
  simpa [w] using this

end

end AffineSl2BelowCritical

end VOA
