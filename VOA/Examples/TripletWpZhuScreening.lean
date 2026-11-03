/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpAmbient
import VOA.Modules.ZhuModule

/-!
# The screened lattice state belongs to Zhu's O(W(p))

This file proves the Zhu-algebra analogue of the earlier `C₂` membership, without using that
membership.  The key is the depth-`2p-1` Frenkel--Zhu residue.  Its modes start at `-2p-1`;
the leading mode is the screened state, while every later mode vanishes by applying `Q²` to
`F₍n₎F = 0` for `n ≥ -2p`.

The cocycle-normalized intrinsic state `qwpSqNegTwoAlphaTriplet` is proved equal, after inclusion
in the lattice VOA, to `Q²e^{-2α}`.  Its membership in `O(W(p))` is therefore an exact intrinsic
statement, not an identification of Zhu's `O` with the `C₂` subspace.
-/

namespace VOA.LatGen.WpC2

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp

/-- The `Q²(F₍n₎F)` combination, intrinsically in `W(p)`. -/
noncomputable def qwpSqModeTriplet (p : ℕ) (hp : 1 ≤ p) (n : ℤ) :
    (tripletW p hp).carrier :=
  (tripletWVOA p hp).smul (genE p hp) n (genF p hp)
    + (2 : ℂ) • (tripletWVOA p hp).smul (genH p hp) n (genH p hp)
    + (tripletWVOA p hp).smul (genF p hp) n (genE p hp)

@[simp] theorem qwpSqModeTriplet_coe (p : ℕ) (hp : 1 ≤ p) (n : ℤ) :
    ((qwpSqModeTriplet p hp n : (tripletW p hp).carrier) : LatModuleGen (latP p)) =
      (tripletLatticeVOA p hp).smul (Etrip p) n (Ftrip p)
        + (2 : ℂ) • (tripletLatticeVOA p hp).smul (Htrip p) n (Htrip p)
        + (tripletLatticeVOA p hp).smul (Ftrip p) n (Etrip p) := by
  simp only [qwpSqModeTriplet, Submodule.coe_add, Submodule.coe_smul, smul_coe,
    genE_coe, genH_coe, genF_coe]

/-- All non-leading modes of the screened combination vanish. -/
theorem qwpSqModeTriplet_eq_zero (p : ℕ) (hp : 1 ≤ p) {n : ℤ}
    (hn : -(2 * (p : ℤ)) ≤ n) : qwpSqModeTriplet p hp n = 0 := by
  apply Subtype.ext
  rw [qwpSqModeTriplet_coe]
  have h := Qwp_sq_smul_Ftrip p hp n
  rw [smul_Ftrip_Ftrip p hp hn, map_zero, map_zero] at h
  exact h.symm

/-- The three depth-`2p-1` Frenkel--Zhu residues whose leading term is `Q²e^{-2α}`. -/
noncomputable def qwpSqPresTriplet (p : ℕ) (hp : 1 ≤ p) : (tripletW p hp).carrier :=
  let W := tripletWVOA p hp
  let M := 2 * p - 1
  Pres W M (genE p hp) (genF p hp) M
    + (2 : ℂ) • Pres W M (genH p hp) (genH p hp) M
    + Pres W M (genF p hp) (genE p hp) M

/-- Expanding the three residues groups them mode-by-mode into the `Q²(F₍n₎F)` combination. -/
theorem qwpSqPresTriplet_eq_sum (p : ℕ) (hp : 1 ≤ p) :
    qwpSqPresTriplet p hp =
      ∑ i ∈ Finset.range ((2 * p - 1) + (2 * p - 1) + 1),
        cbz (((2 * p - 1 : ℕ) : ℤ) + (2 * p - 1 : ℕ)) (i : ℤ) •
          qwpSqModeTriplet p hp ((i : ℤ) - 2 - (2 * p - 1 : ℕ)) := by
  simp only [qwpSqPresTriplet, Pres, Finset.smul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold qwpSqModeTriplet
  module

/-- The residue sum has only its `i=0`, mode `-2p-1`, term. -/
theorem qwpSqPresTriplet_eq_bottomMode (p : ℕ) (hp : 1 ≤ p) :
    qwpSqPresTriplet p hp = qwpSqModeTriplet p hp (-(2 * (p : ℤ)) - 1) := by
  rw [qwpSqPresTriplet_eq_sum]
  rw [Finset.sum_eq_single 0]
  · have hM : (((2 * p - 1 : ℕ) : ℤ)) = 2 * (p : ℤ) - 1 := by
      have hpz : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
      omega
    simp only [Nat.cast_zero, cbz_zero, one_smul, zero_sub]
    congr 1
    rw [hM]
    omega
  · intro i hi hi0
    have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    rw [qwpSqModeTriplet_eq_zero]
    · exact smul_zero _
    · have hM : (((2 * p - 1 : ℕ) : ℤ)) = 2 * (p : ℤ) - 1 := by
        have hpz : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
        omega
      rw [hM]
      have hi1z : (1 : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi1
      omega
  · simp only [Finset.mem_range]
    omega

/-- The cocycle-normalized intrinsic state represented ambiently by `Q²e^{-2α}`. -/
noncomputable def qwpSqNegTwoAlphaTriplet (p : ℕ) (hp : 1 ≤ p) :
    (tripletW p hp).carrier :=
  (latticeCocycle (latP p) (-alphaP p) (-alphaP p))⁻¹ •
    qwpSqModeTriplet p hp (-(2 * (p : ℤ)) - 1)

/-- The intrinsic state is exactly the twice-screened charged lattice vacuum. -/
theorem qwpSqNegTwoAlphaTriplet_coe (p : ℕ) (hp : 1 ≤ p) :
    ((qwpSqNegTwoAlphaTriplet p hp : (tripletW p hp).carrier) : LatModuleGen (latP p)) =
      Qwp p hp (Qwp p hp (latChargeGen (latP p) (-alphaP p + -alphaP p))) := by
  have hε : latticeCocycle (latP p) (-alphaP p) (-alphaP p) ≠ 0 :=
    Screen.latticeCocycle_ne_zero (latP p) (-alphaP p) (-alphaP p)
  have h := Qwp_sq_smul_Ftrip p hp (-(2 * (p : ℤ)) - 1)
  rw [smul_Ftrip_Ftrip_bottom p hp, map_smul, map_smul] at h
  simp only [qwpSqNegTwoAlphaTriplet, Submodule.coe_smul, qwpSqModeTriplet_coe]
  rw [← h, smul_smul, inv_mul_cancel₀ hε, one_smul]

/-- The depth residue is in Zhu's `O(W(p))`, by the Frenkel--Zhu residue theorem. -/
theorem qwpSqPresTriplet_mem_O (p : ℕ) (hp : 1 ≤ p) :
    qwpSqPresTriplet p hp ∈ O (tripletWVOA p hp) := by
  let W := tripletWVOA p hp
  let M := 2 * p - 1
  have hM : ((M : ℕ) : ℤ) = 2 * (p : ℤ) - 1 := by
    dsimp [M]
    have hpz : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    omega
  have hE : genE p hp ∈ W.grading (M : ℤ) := by
    change genE p hp ∈ (tripletWVOA p hp).grading (M : ℤ)
    rw [hM]
    exact Etrip_mem_grading p hp
  have hH : genH p hp ∈ W.grading (M : ℤ) := by
    change genH p hp ∈ (tripletWVOA p hp).grading (M : ℤ)
    rw [hM]
    exact Htrip_mem_grading p hp
  have hF : genF p hp ∈ W.grading (M : ℤ) := by
    change genF p hp ∈ (tripletWVOA p hp).grading (M : ℤ)
    rw [hM]
    exact Ftrip_mem_grading p hp
  change Pres W M (genE p hp) (genF p hp) M
      + (2 : ℂ) • Pres W M (genH p hp) (genH p hp) M
      + Pres W M (genF p hp) (genE p hp) M ∈ O W
  exact (O W).add_mem
    ((O W).add_mem (Pres_mem_O W hE (genF p hp) M)
      ((O W).smul_mem (2 : ℂ) (Pres_mem_O W hH (genH p hp) M)))
    (Pres_mem_O W hF (genE p hp) M)

/-- The exact Zhu-algebra bridge: `Q²e^{-2α}`, as a state of `W(p)`, belongs to `O(W(p))`.
No `C₂` quotient or `AMOmegaIdentity` is used. -/
theorem Qwp_sq_latChargeGen_mem_O (p : ℕ) (hp : 1 ≤ p) :
    qwpSqNegTwoAlphaTriplet p hp ∈ O (tripletWVOA p hp) := by
  change (latticeCocycle (latP p) (-alphaP p) (-alphaP p))⁻¹ •
      qwpSqModeTriplet p hp (-(2 * (p : ℤ)) - 1) ∈ O (tripletWVOA p hp)
  rw [← qwpSqPresTriplet_eq_bottomMode p hp]
  exact (O (tripletWVOA p hp)).smul_mem _ (qwpSqPresTriplet_mem_O p hp)

end VOA.LatGen.WpC2

section AxiomAudit
#print axioms VOA.LatGen.WpC2.qwpSqPresTriplet_eq_bottomMode
#print axioms VOA.LatGen.WpC2.qwpSqNegTwoAlphaTriplet_coe
#print axioms VOA.LatGen.WpC2.Qwp_sq_latChargeGen_mem_O
end AxiomAudit
