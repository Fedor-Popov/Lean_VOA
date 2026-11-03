/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeInvolution

/-!
# `(V_Λ^+)₁ = 0`  (Moonshine step M3)

The untwisted half of `V♮` has no weight-`1` states.  Two facts combine:

* the Leech lattice has no roots, so `(V_Λ)₁` is the Heisenberg weight-`1` space `h(-1)𝟙`
  (`Moonshine.leechVOA_grading_one`);
* the Fock involution `σ` acts on a monomial by `(-1)^{degree}` (`LatGen.sigmaN_monomial`), and
  every weight-`1` monomial has degree `1`, so `θ = -1` on `(V_Λ)₁` (`LatGen.sigmaN_weight_one`).

Hence the `θ`-fixed subspace of `(V_Λ)₁` is zero (`Moonshine.leechVOAPlus_grading_one`).
This is half of `V♮₁ = 0`; the other half is that the twisted sector has lowest weight `3/2`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

namespace LatGen

open HeisenbergN MvPolynomial

variable (r : ℕ)

/-- `σ` acts on a monomial by the sign `(-1)^{degree}`. -/
theorem sigmaN_monomial (d : (ℕ × Fin r) →₀ ℕ) :
    sigmaN r (monomial d 1) = (-1 : ℂ) ^ d.degree • monomial d 1 := by
  rw [sigmaN_apply, sigmaAlg, aeval_monomial, map_one, one_mul, Finsupp.prod]
  simp_rw [neg_pow (X _ : FockN r)]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.prod, Finsupp.prod,
    prod_X_pow_eq_monomial, Algebra.smul_def]
  simp [Finsupp.degree]

/-- The total degree of a monomial is at most its Fock weight (every variable has weight `≥ 1`). -/
theorem degree_le_weight (d : (ℕ × Fin r) →₀ ℕ) :
    d.degree ≤ Finsupp.weight weightFnN d := by
  rw [Finsupp.degree, Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [smul_eq_mul, weightFnN_apply]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

/-- `σ = -1` on the weight-`1` Fock space. -/
theorem sigmaN_weight_one {p : FockN r} (hp : p ∈ gradingWN r 1) : sigmaN r p = -p := by
  have hp' := gradingWN_le_span r 1 hp
  clear hp
  induction hp' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      have hw : Finsupp.weight weightFnN d = 1 := hd
      have hle := degree_le_weight r d
      have hne : d.degree ≠ 0 := by
        intro h0
        rw [Finsupp.degree_eq_zero_iff] at h0
        rw [h0, map_zero] at hw
        exact zero_ne_one hw
      have h1 : d.degree = 1 := by omega
      rw [sigmaN_monomial, h1, pow_one, neg_one_smul]
  | zero => rw [map_zero, neg_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, neg_add]
  | smul c x _ hx => rw [map_smul, hx, smul_neg]

end LatGen

namespace Moonshine

open LatGen HeisenbergN

/-- **`(V_Λ^+)₁ = 0`**: the `θ`-fixed subVOA of the Leech lattice VOA has no weight-`1` states. -/
theorem leechVOAPlus_grading_one : leechVOAPlus.grading 1 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx1 : (x : LatModuleGen leech) ∈ leechVOA.grading 1 := hx
  rw [leechVOA_grading_one, bigradα, Submodule.mem_map] at hx1
  obtain ⟨p, hp, hpx⟩ := hx1
  rw [gradingZN_of_nonneg (by norm_num)] at hp
  have hfix := (mem_leechVOAPlus_iff (x : LatModuleGen leech)).mp x.2
  rw [← hpx, mkEα_apply, thetaLat_tmul, neg_zero, sigmaN_weight_one _ hp,
    TensorProduct.neg_tmul] at hfix
  have h0 : (x : LatModuleGen leech) = 0 := by
    rw [← hpx, mkEα_apply]
    have h2 : (2 : ℂ) • (p ⊗ₜ[ℂ] eGen leech 0) = 0 := by
      rw [two_smul]; nth_rewrite 1 [← hfix]; rw [neg_add_cancel]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  exact (Submodule.mem_bot ℂ).mpr (Subtype.ext h0)

end Moonshine

end VOA
