/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.Expansion
import VOA.Foundations.Substitution

/-!
# The all-order δ-function jumps `ι₁₂ − ι₂₁` of `(z₁−z₂)^{−k−1}`  (Gannon §5.1.2; FLM §8.10)

`Foundations.Expansion` proves the canonical `n=−1` δ-jump
`expandPos(−1) − expandNeg(−1) = deltaForm`.  Here we **generalize it to all negative powers**: the
two formal expansions of `(z₁−z₂)^{−k−1}` (the `z₂`-dominant `ι₁₂ = expandPos` and the `z₁`-dominant
`ι₂₁ = expandNeg`) differ by the `k`-th `δ`-derivative,

  `expandPos(−k−1) − expandNeg(−k−1)  =  (1/k!) · ∂ᵏδ(z₁/z₂)`   (`negPowJump_eq_deltaDeriv`).

This is the precise `ι₁₂ − ι₂₁` jump content distinguishing the two domains of a Laurent
expansion — the foundational analytic datum of the two-sided `ι_z` formal calculus
(`𝒱((z₁))((z₂)) ↔ 𝒱((z₂))((z₁))`) underlying weak associativity, the Jacobi identity and
skew-symmetry (Gannon 5.1.8).

## Engines
`mulBySub_expandPos` / `mulBySub_expandNeg`: `(z₁−z₂)·(z₁−z₂)ⁿ = (z₁−z₂)ⁿ⁺¹` for **both**
expansions, proved coefficient-wise from the generalized-binomial Pascal rule (`gBinom_pascal_up`).
The induction then peels the jump with `mulBySub_deltaDeriv` (`(z₁−z₂)·∂ʲ⁺¹δ = (j+1)·∂ʲδ`); the
residue at `z₁⁻¹` (`m=−1`) pins down the otherwise-free `deltaDeriv 0` summand via
`eq_deltaDeriv_zero_of_mulBySub_eq_zero`.

## Status
Complete & `sorry`-free / axiom-free (the `ι_z` δ-calculus).  The
`mulBySub` action on `expandPos`/`expandNeg`, the negative-power jump `negPowJump` and its
residue/`deltaDeriv` identities — every declaration — are proved (verified by `#print axioms` =
`[propext, Classical.choice, Quot.sound]`).  Consumed by the skew-symmetry / two-sided
completion argument (`Core.WeakAssoc`).

## References
* Gannon §5.1.2; Frenkel–Lepowsky–Meurman §8.10; Kac, *VA for Beginners* §2.
-/

namespace VOA

open scoped BigOperators

/-- gBinom Pascal in the form `gBinom (n+1) (j+1) = gBinom n (j+1) + gBinom n j`. -/
theorem gBinom_pascal_up (n : ℤ) (j : ℕ) :
    gBinom (n + 1) (j + 1) = gBinom n (j + 1) + gBinom n j := by
  have := gBinom_succ_pascal (n + 1) j
  rwa [show (n + 1 - 1 : ℤ) = n by ring] at this

/-- **Engine: `(z₁−z₂)·(z₁−z₂)ⁿ = (z₁−z₂)ⁿ⁺¹` for the `z₂`-dominant expansion** `expandPos`. -/
theorem mulBySub_expandPos (n : ℤ) : mulBySub (expandPos n) = expandPos (n + 1) := by
  ext m k
  rw [mulBySub_apply, expandPos_apply, expandPos_apply, expandPos_apply]
  by_cases hline : m = n + 1 - k
  · by_cases hk1 : 1 ≤ k
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
      rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩,
        show ((j : ℤ) + 1).toNat = j + 1 by omega,
        show ((j : ℤ) + 1 - 1).toNat = j by omega,
        gBinom_pascal_up n j,
        show ((j : ℤ) + 1 - 1) = (j : ℤ) by ring,
        show negOnePow ((j : ℤ) + 1) = - negOnePow (j : ℤ) from negOnePow_succ (j : ℤ)]
      ring
    · by_cases hk0 : k = 0
      · subst hk0
        rw [if_pos ⟨le_rfl, by omega⟩, if_neg (by rintro ⟨h, _⟩; omega),
          if_pos ⟨le_rfl, by omega⟩, show ((0:ℤ)).toNat = 0 by rfl, gBinom_zero, gBinom_zero,
          sub_zero]
      · rw [if_neg (by rintro ⟨h, _⟩; omega), if_neg (by rintro ⟨h, _⟩; omega),
          if_neg (by rintro ⟨h, _⟩; omega), sub_zero]
  · rw [if_neg (by rintro ⟨_, h⟩; omega), if_neg (by rintro ⟨_, h⟩; omega),
      if_neg (by rintro ⟨_, h⟩; omega), sub_zero]

/-- **Engine: `(z₁−z₂)·(z₁−z₂)ⁿ = (z₁−z₂)ⁿ⁺¹` for the `z₁`-dominant expansion** `expandNeg`. -/
theorem mulBySub_expandNeg (n : ℤ) : mulBySub (expandNeg n) = expandNeg (n + 1) := by
  ext m k
  rw [mulBySub_apply, expandNeg_apply, expandNeg_apply, expandNeg_apply]
  by_cases hline : k = n + 1 - m
  · by_cases hm1 : 1 ≤ m
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
      have hp1 : negOnePow (n + ((j : ℤ) + 1)) = - negOnePow (n + (j : ℤ)) := by
        rw [show n + ((j : ℤ) + 1) = (n + (j : ℤ)) + 1 by ring, negOnePow_succ]
      have hp2 : negOnePow (n + ((j : ℤ) + 1 - 1)) = negOnePow (n + (j : ℤ)) := by
        congr 1; ring
      have hp3 : negOnePow (n + 1 + ((j : ℤ) + 1)) = negOnePow (n + (j : ℤ)) := by
        rw [show n + 1 + ((j : ℤ) + 1) = ((n + (j : ℤ)) + 1) + 1 by ring, negOnePow_succ,
          negOnePow_succ, neg_neg]
      rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩,
        show ((j : ℤ) + 1).toNat = j + 1 by omega,
        show ((j : ℤ) + 1 - 1).toNat = j by omega,
        gBinom_pascal_up n j, hp1, hp2, hp3]
      ring
    · by_cases hm0 : m = 0
      · subst hm0
        rw [if_neg (by rintro ⟨h, _⟩; omega), if_pos ⟨le_rfl, by omega⟩,
          if_pos ⟨le_rfl, by omega⟩, show ((0:ℤ)).toNat = 0 by rfl, gBinom_zero, gBinom_zero,
          zero_sub, show (n + 1 + 0) = (n + 0) + 1 by ring, negOnePow_succ, mul_one, mul_one]
      · rw [if_neg (by rintro ⟨h, _⟩; omega), if_neg (by rintro ⟨h, _⟩; omega),
          if_neg (by rintro ⟨h, _⟩; omega), sub_zero]
  · rw [if_neg (by rintro ⟨_, h⟩; omega), if_neg (by rintro ⟨_, h⟩; omega),
      if_neg (by rintro ⟨_, h⟩; omega), sub_zero]

/-- The one-variable point mass `[t=0]`, the natural `δ`-coefficient distribution. -/
def deltaCoeff : FormalDist ℂ := fun t => if t = 0 then 1 else 0

@[simp] theorem deltaCoeff_apply (t : ℤ) : deltaCoeff t = if t = 0 then 1 else 0 := rfl

/-- The `ι`-jump of `(z₁−z₂)^{−k−1}`: the difference of its two formal expansions. -/
noncomputable def negPowJump (k : ℕ) : FormalDist₂ ℂ :=
  expandPos (-(k : ℤ) - 1) - expandNeg (-(k : ℤ) - 1)

/-- Base `k=0`: the jump is the formal delta `δ(z₁/z₂) = deltaDeriv 0 deltaCoeff` (= `expand_jump`). -/
theorem negPowJump_zero : negPowJump 0 = deltaDeriv 0 deltaCoeff := by
  rw [negPowJump, show (-((0:ℕ):ℤ) - 1) = (-1 : ℤ) by norm_num, expand_jump]
  ext m n
  rw [deltaForm_apply, deltaDeriv_apply, deltaCoeff_apply,
    Finset.range_zero, Finset.prod_empty, one_smul, Nat.cast_zero,
    show m + n + 1 + (0 : ℤ) = m + n + 1 by ring]

/-- `mulBySub` lowers the jump index: `(z₁−z₂)·Jₖ₊₁ = Jₖ`. -/
theorem mulBySub_negPowJump (k : ℕ) :
    mulBySub (negPowJump (k + 1)) = negPowJump k := by
  rw [negPowJump, negPowJump, map_sub, mulBySub_expandPos, mulBySub_expandNeg]
  congr 2 <;> push_cast <;> ring

/-- The residue (`m=−1` slice) of the jump vanishes for `k ≥ 1`. -/
theorem negPowJump_residue_zero (k : ℕ) (n : ℤ) :
    negPowJump (k + 1) (-1) n = 0 := by
  show expandPos (-((k:ℤ)+1) - 1) (-1) n - expandNeg (-((k:ℤ)+1) - 1) (-1) n = 0
  rw [expandPos_apply, expandNeg_apply,
    if_neg (by rintro ⟨hn, he⟩; omega), if_neg (by rintro ⟨h, _⟩; omega), sub_zero]

/-- The residue (`m=−1` slice) of `deltaDeriv (k+1) c` vanishes (the `i=0` falling factor is `0`). -/
theorem deltaDeriv_succ_residue_zero (k : ℕ) (c : FormalDist ℂ) (n : ℤ) :
    deltaDeriv (k + 1) c (-1) n = 0 := by
  rw [deltaDeriv_apply, Finset.prod_range_succ' (fun i => -(-1 : ℤ) - 1 - (i : ℤ)) k]
  simp

/-- **The all-order higher δ-jump** (Gannon §5.1.2; FLM §8.10).  The two formal expansions of
`(z₁−z₂)^{−k−1}` differ by the `k`-th `δ`-derivative, normalized by `1/k!`:
`expandPos(−k−1) − expandNeg(−k−1) = (1/k!) • deltaDeriv k deltaCoeff`.  Generalizes the `n=−1`
`expand_jump`; this is the full `ι₁₂ − ι₂₁` jump for all negative powers. -/
theorem negPowJump_eq_deltaDeriv (k : ℕ) :
    negPowJump k = (((k.factorial : ℂ))⁻¹) • deltaDeriv k deltaCoeff := by
  induction k with
  | zero => rw [negPowJump_zero]; simp
  | succ j ih =>
    set L := negPowJump (j + 1)
    set R := (((j + 1).factorial : ℂ))⁻¹ • deltaDeriv (j + 1) deltaCoeff with hR
    have hmulL : mulBySub L = negPowJump j := mulBySub_negPowJump j
    have hmulR : mulBySub R = negPowJump j := by
      rw [hR, map_smul, mulBySub_deltaDeriv j deltaCoeff, ih,
        ← Int.cast_smul_eq_zsmul ℂ ((j : ℤ) + 1), smul_smul]
      congr 1
      have hj1 : ((j : ℂ) + 1) ≠ 0 :=
        by exact_mod_cast (Nat.cast_add_one_ne_zero j : ((j : ℂ) + 1) ≠ 0)
      rw [Nat.factorial_succ]
      push_cast
      rw [mul_comm ((j : ℂ) + 1) (j.factorial : ℂ), mul_inv, mul_assoc,
        inv_mul_cancel₀ hj1, mul_one]
    have hmul0 : mulBySub (L - R) = 0 := by rw [map_sub, hmulL, hmulR, sub_self]
    have hres : ∀ n : ℤ, (L - R) (-1) n = 0 := by
      intro n
      show negPowJump (j + 1) (-1) n
        - (((j + 1).factorial : ℂ))⁻¹ • deltaDeriv (j + 1) deltaCoeff (-1) n = 0
      rw [negPowJump_residue_zero j n, deltaDeriv_succ_residue_zero j deltaCoeff n,
        smul_zero, sub_zero]
    have hLR : L - R = 0 := by
      rw [eq_deltaDeriv_zero_of_mulBySub_eq_zero hmul0]
      ext m n
      rw [deltaDeriv_apply, Finset.range_zero, Finset.prod_empty, one_smul]
      show (L - R) (-1) (m + n + 1 + 0) = (0 : FormalDist₂ ℂ) m n
      rw [hres (m + n + 1 + 0)]; rfl
    rw [← sub_eq_zero]; exact hLR

end VOA
