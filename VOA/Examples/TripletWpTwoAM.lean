/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.TripletWpAmbient

/-!
# The `p = 2` Adamovic--Milas identity: an exact finite coordinate certificate

This file reduces `AMOmegaIdentity 2 hp 5` to one completely explicit equality in the
rank-one lattice Fock space.  Unlike `AMOmegaIdentity`, the remaining equality has no existential
coefficients and no submodule-membership conclusion hidden in it: all twelve Virasoro words and
all rational coefficients are printed below.

The coefficient of `L(-2)^5` is

`B_2 = 1024 / 1575`,

the specialization of Adamovic--Milas' closed formula
`(-1)^p binom(2p,p) (4p)^(3p-1) / (binom(4p-1,p) ((3p-1)!)^2)`.
The other eleven partitions of `10` with parts at least two all begin with a mode different from
`L(-2)`, and consequently their states lie in `VirDeep 2 hp`.  That membership, the non-vanishing
of `B_2`, and the assembly into `AMOmegaIdentity` are proved here.

What remains is the literal 42-coordinate Fock-space equality `AMTwoCoordinateIdentity hp`.
Its coefficients were obtained by expanding

* `Q^2 e^{-2 alpha} = EE(alpha)_3 S_7(alpha)`,
* `H = S_3(alpha)` and `H_{-5}H`, and
* the twelve background-charge Virasoro words of weight ten at central charge `-2`.

No use is made of the conclusion `AMOmegaIdentity`, of `C2Cofinite`, or of a quotient by
`VirDeep`.  In particular this file does not claim the coordinate equality is proved: it isolates
the one finite polynomial computation which the current lattice API cannot yet normalize.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpC2

open VOA VOA.IntegralLattice
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp

/-! ## Virasoro words in the ambient lattice VOA -/

/-- The ambient Virasoro word `L(-n_1) ... L(-n_r)|0>` at `p = 2`. -/
noncomputable def virWordTwo (hp : 1 ≤ 2) : List ℕ → LatModuleGen (latP 2)
  | [] => latVacuumGen (latP 2)
  | n :: ns => (tripletLatticeVOA 2 hp).L (-(n : ℤ)) (virWordTwo hp ns)

@[simp] theorem virWordTwo_nil (hp : 1 ≤ 2) :
    virWordTwo hp [] = latVacuumGen (latP 2) := rfl

@[simp] theorem virWordTwo_cons (hp : 1 ≤ 2) (n : ℕ) (ns : List ℕ) :
    virWordTwo hp (n :: ns) =
      (tripletLatticeVOA 2 hp).L (-(n : ℤ)) (virWordTwo hp ns) := rfl

/-- Every Virasoro word on the vacuum belongs to the generated triplet subalgebra: the conformal
vector belongs to the generating set and the carrier is closed under all products. -/
theorem virWordTwo_mem_carrier (hp : 1 ≤ 2) (ns : List ℕ) :
    virWordTwo hp ns ∈ (tripletW 2 hp).carrier := by
  induction ns with
  | nil =>
      simpa [virWordTwo] using vacuum_mem_tripletW 2 hp
  | cons n ns ih =>
      rw [virWordTwo_cons]
      have hL : (tripletLatticeVOA 2 hp).L (-(n : ℤ)) (virWordTwo hp ns)
          = (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (-(n : ℤ) + 1)
              (virWordTwo hp ns) := rfl
      rw [hL]
      exact (tripletW 2 hp).smul_mem (omegaTrip 2) (omegaTrip_mem_tripletW 2 hp)
        (-(n : ℤ) + 1) (virWordTwo hp ns) ih

/-- If the leftmost mode of a Virasoro word is `L(-n)` with `n >= 1`, `n != 2`, then the word is
one of the literal generators of `VirDeep`. -/
theorem virWordTwo_cons_mem_virDeep (hp : 1 ≤ 2) (n : ℕ) (ns : List ℕ)
    (hn : 1 ≤ n) (hn2 : n ≠ 2) :
    virWordTwo hp (n :: ns) ∈ VirDeep 2 hp := by
  rw [VirDeep]
  apply Submodule.subset_span
  exact ⟨(n : ℤ), by exact_mod_cast hn, by exact_mod_cast hn2,
    virWordTwo hp ns, virWordTwo_mem_carrier hp ns, rfl⟩

/-! ## The explicit weight-ten remainder -/

/-- The eleven Virasoro words other than `L(-2)^5`, with the exact coefficients of the
rank-one `p = 2` Fock-space calculation. -/
noncomputable def amTwoRemainder (hp : 1 ≤ 2) : LatModuleGen (latP 2) :=
    (128 / 35 : ℂ) • virWordTwo hp [10]
  + (-27232 / 525 : ℂ) • virWordTwo hp [8, 2]
  + (-12308 / 525 : ℂ) • virWordTwo hp [7, 3]
  + (20896 / 525 : ℂ) • virWordTwo hp [6, 4]
  + (-106816 / 1575 : ℂ) • virWordTwo hp [6, 2, 2]
  + (18544 / 1575 : ℂ) • virWordTwo hp [5, 5]
  + (-59392 / 1575 : ℂ) • virWordTwo hp [5, 3, 2]
  + (-752 / 525 : ℂ) • virWordTwo hp [4, 4, 2]
  + (1688 / 525 : ℂ) • virWordTwo hp [4, 3, 3]
  + (-512 / 63 : ℂ) • virWordTwo hp [4, 2, 2, 2]
  + (832 / 315 : ℂ) • virWordTwo hp [3, 3, 2, 2]

/-- The printed remainder really lies in the strict `VirDeep` submodule, not merely in
`O2amb`. -/
theorem amTwoRemainder_mem_virDeep (hp : 1 ≤ 2) :
    amTwoRemainder hp ∈ VirDeep 2 hp := by
  have h10 := virWordTwo_cons_mem_virDeep hp 10 [] (by norm_num) (by norm_num)
  have h82 := virWordTwo_cons_mem_virDeep hp 8 [2] (by norm_num) (by norm_num)
  have h73 := virWordTwo_cons_mem_virDeep hp 7 [3] (by norm_num) (by norm_num)
  have h64 := virWordTwo_cons_mem_virDeep hp 6 [4] (by norm_num) (by norm_num)
  have h622 := virWordTwo_cons_mem_virDeep hp 6 [2, 2] (by norm_num) (by norm_num)
  have h55 := virWordTwo_cons_mem_virDeep hp 5 [5] (by norm_num) (by norm_num)
  have h532 := virWordTwo_cons_mem_virDeep hp 5 [3, 2] (by norm_num) (by norm_num)
  have h442 := virWordTwo_cons_mem_virDeep hp 4 [4, 2] (by norm_num) (by norm_num)
  have h433 := virWordTwo_cons_mem_virDeep hp 4 [3, 3] (by norm_num) (by norm_num)
  have h4222 := virWordTwo_cons_mem_virDeep hp 4 [2, 2, 2] (by norm_num) (by norm_num)
  have h3322 := virWordTwo_cons_mem_virDeep hp 3 [3, 2, 2] (by norm_num) (by norm_num)
  rw [amTwoRemainder]
  exact add_mem
    (add_mem
      (add_mem
        (add_mem
          (add_mem
            (add_mem
              (add_mem
                (add_mem
                  (add_mem
                    (add_mem
                      (Submodule.smul_mem _ _ h10)
                      (Submodule.smul_mem _ _ h82))
                    (Submodule.smul_mem _ _ h73))
                  (Submodule.smul_mem _ _ h64))
                (Submodule.smul_mem _ _ h622))
              (Submodule.smul_mem _ _ h55))
            (Submodule.smul_mem _ _ h532))
          (Submodule.smul_mem _ _ h442))
        (Submodule.smul_mem _ _ h433))
      (Submodule.smul_mem _ _ h4222))
    (Submodule.smul_mem _ _ h3322)

/-- The exceptional partition is exactly `L(-2)^5|0>` as defined above. -/
theorem virWordTwo_two_pow_five (hp : 1 ≤ 2) :
    virWordTwo hp [2, 2, 2, 2, 2] = omegaPowAmb 2 hp 5 := by
  rw [show [2, 2, 2, 2, 2] = 2 :: 2 :: 2 :: 2 :: 2 :: [] from rfl]
  simp only [virWordTwo_cons, virWordTwo_nil, omegaPowAmb_succ_L, omegaPowAmb_zero]
  norm_num

/-! ## The one residual coordinate equality and its exact payoff -/

/-- The literal finite Fock-space identity left by the reduction.  It is stronger than
`AMOmegaIdentity 2 hp 5`: every coefficient and every Virasoro word is fixed.

This definition is not asserted or assumed anywhere in this file. -/
def AMTwoCoordinateIdentity (hp : 1 ≤ 2) : Prop :=
  Qwp 2 hp (Qwp 2 hp
      (latChargeGen (latP 2) (-alphaP 2 + -alphaP 2)))
    = (3 : ℂ) • (tripletLatticeVOA 2 hp).smul (Htrip 2) (-5) (Htrip 2)
      + (1024 / 1575 : ℂ) • virWordTwo hp [2, 2, 2, 2, 2]
      + amTwoRemainder hp

/-- The published coefficient `B_2 = 1024/1575` is nonzero. -/
theorem amTwo_B_ne_zero : (1024 / 1575 : ℂ) ≠ 0 := by norm_num

/-- Once the one printed 42-coordinate equality is checked, the original
Adamovic--Milas proposition follows with no further structural input. -/
theorem amOmegaIdentity_two_of_coordinateIdentity (hp : 1 ≤ 2)
    (h : AMTwoCoordinateIdentity hp) : AMOmegaIdentity 2 hp 5 := by
  refine ⟨3, 1024 / 1575, amTwo_B_ne_zero, amTwoRemainder hp,
    amTwoRemainder_mem_virDeep hp, ?_⟩
  norm_num at h ⊢
  rw [← virWordTwo_two_pow_five hp]
  exact h

end VOA.LatGen.WpC2

section AxiomAudit
#print axioms VOA.LatGen.WpC2.virWordTwo_mem_carrier
#print axioms VOA.LatGen.WpC2.amTwoRemainder_mem_virDeep
#print axioms VOA.LatGen.WpC2.amOmegaIdentity_two_of_coordinateIdentity
end AxiomAudit
