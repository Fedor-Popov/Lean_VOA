/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.RRLowerPartition
import VOA.Examples.LeeYangCharacterReduction

/-!
# The Lee–Yang lower bound, reduced to the Rocha-Caridi (Feigin–Fuchs) lower bound

`LeeYangCharacter.LeeYangRRLowerBound` asks for

`#{partitions of N into parts ≥ 2 with adjacent difference ≥ 2}  ≤  dim L(-22/5, 0)_N`.

Classically this is two theorems: the Rocha-Caridi / Feigin–Fuchs vacuum character of the
`(2,5)` minimal model, `ch L = (q)_∞⁻¹ Σ_k (-1)^k q^{k(5k+3)/2}`, and the second
Rogers–Ramanujan identity.  This file **proves the combinatorial half** (via Andrews' polynomial
identity, `RRLowerAndrews`, `RRLowerLimit`) and thereby isolates the representation-theoretic
half as the single named hypothesis `LeeYangRochaCaridiLowerBound`.

## Main results

* `gapTwoCoefficient_eq_pc` — the repository's coefficient `gapTwoCoefficient N r` is
  `#{partitions of N - r(r+1) into parts ≤ r}`;
* `sum_gapTwoCoefficient_eq_rc` — **the second Rogers–Ramanujan identity at the level of the
  Lee–Yang coefficients**: `Σ_{r ≤ N} gapTwoCoefficient N r = Σ_k (-1)^k p(N - k(5k+3)/2)`;
  proved outright;
* `rc_eq_card` — `rc` written with Mathlib's `Nat.Partition` count (via `pp_eq_card`);
* `finrank_le_rc` — **unconditional upper bound by the Rocha-Caridi character**:
  `dim L(-22/5,0)_N ≤ Σ_k (-1)^k p(N - k(5k+3)/2)` for every `N`;
* `leeYangRRLowerBound_iff_rochaCaridi` — `LeeYangRRLowerBound ↔ LeeYangRochaCaridiLowerBound`;
* `leeYangRRCharacter_iff_rochaCaridiCharacter` — the exact character in either form.

## The remaining lower bound (since proved)

`LeeYangRochaCaridiLowerBound` — proved downstream as
`VOA.RRLower.leeYangRochaCaridiLowerBound_holds` (`LYGramRank.lean`).  It is the statement
that the maximal submodule of the Virasoro Verma module `M(-22/5, 0)` is no larger than the
Feigin–Fuchs embedding structure predicts (`J_max = M(1) + M(4)` with the alternating
inclusion–exclusion of the braid), i.e. the lower half of Rocha-Caridi's character formula.
No combinatorics is left in it.
-/

namespace VOA.RRLower

open VOA.LeeYangCharacter VOA.LeeYangTransferAssembly VOA.VirSimple VOA.LeeYang
open Finset

noncomputable section

/-- The repository's Lee–Yang coefficient is a bounded-part partition count. -/
theorem gapTwoCoefficient_eq_pc (N r : ℕ) :
    (gapTwoCoefficient (N : ℤ) r : ℤ) = pc r ((N : ℤ) - (r : ℤ) * ((r : ℤ) + 1)) := by
  classical
  unfold gapTwoCoefficient
  rw [← card_wt ((N : ℤ).toNat) r _ (by simp)]
  congr 1
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  push_cast
  constructor <;> intro h <;> linarith

/-- **The second Rogers–Ramanujan identity for the Lee–Yang coefficients**, proved outright:
the number of gap-two partitions of `N` is the Rocha-Caridi alternating sum. -/
theorem sum_gapTwoCoefficient_eq_rc (N : ℕ) :
    ((∑ r ∈ Finset.range (N + 1), gapTwoCoefficient (N : ℤ) r : ℕ) : ℤ) = rc N := by
  rw [← gapSum_eq_rc, gapSum]
  push_cast
  exact Finset.sum_congr rfl fun r _ => gapTwoCoefficient_eq_pc N r

/-- The Rocha-Caridi side with Mathlib's partition count:
`rc N = Σ_{|k| ≤ N, k(5k+3)/2 ≤ N} (-1)^k · #(Nat.Partition (N - k(5k+3)/2))`. -/
theorem rc_eq_card (N : ℕ) :
    rc N = ∑ k ∈ Ico (-(N : ℤ) - 1) ((N : ℤ) + 1),
      sgn k * (if ee k ≤ N then (Fintype.card (Nat.Partition ((N : ℤ) - ee k).toNat) : ℤ)
        else 0) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  split_ifs with h
  · rw [← pp_eq_card, Int.toNat_of_nonneg (by omega)]
  · exact pp_of_neg (by omega)

/-- **Unconditional upper bound by the Rocha-Caridi character.** -/
theorem finrank_le_rc (N : ℕ) :
    (Module.finrank ℂ ((virasoroSimple leeYangC).grading (N : ℤ)) : ℤ) ≤ rc N := by
  rw [← sum_gapTwoCoefficient_eq_rc]
  exact_mod_cast finrank_grading_le N

/-- Proved: `leeYangRochaCaridiLowerBound_holds` (`LYGramRank.lean`).  (Classical: Feigin–Fuchs
1984, Rocha-Caridi 1985.)  The lower half of the vacuum character of the `(2,5)` minimal model,
`Σ_k (-1)^k p(N - k(5k+3)/2) ≤ dim L(-22/5,0)_N` for every `N`. -/
def LeeYangRochaCaridiLowerBound : Prop :=
  ∀ N : ℕ, rc N ≤ (Module.finrank ℂ ((virasoroSimple leeYangC).grading (N : ℤ)) : ℤ)

/-- The Rocha-Caridi character identity for `L(-22/5, 0)`. -/
def LeeYangRochaCaridiCharacter : Prop :=
  ∀ N : ℕ, (Module.finrank ℂ ((virasoroSimple leeYangC).grading (N : ℤ)) : ℤ) = rc N

/-- **The gap-two lower bound is exactly the Rocha-Caridi lower bound.** -/
theorem leeYangRRLowerBound_iff_rochaCaridi :
    LeeYangRRLowerBound ↔ LeeYangRochaCaridiLowerBound := by
  constructor
  · intro h N
    rw [← sum_gapTwoCoefficient_eq_rc]
    exact_mod_cast h N
  · intro h N
    have := h N
    rw [← sum_gapTwoCoefficient_eq_rc] at this
    exact_mod_cast this

theorem rochaCaridiLowerBound_iff_character :
    LeeYangRochaCaridiLowerBound ↔ LeeYangRochaCaridiCharacter :=
  ⟨fun h N => le_antisymm (finrank_le_rc N) (h N), fun h N => (h N).ge⟩

theorem leeYangRRCharacter_iff_rochaCaridiCharacter :
    LeeYangRRCharacter ↔ LeeYangRochaCaridiCharacter :=
  leeYangRRCharacter_iff_lowerBound.trans
    (leeYangRRLowerBound_iff_rochaCaridi.trans rochaCaridiLowerBound_iff_character)

/-! ## Sanity values (kernel-checked by `decide`) -/

/-- `p(10) = 42`. -/
example : pp 10 = 42 := by decide

/-- At `N = 10` both sides equal `4` (`10, 8+2, 7+3, 6+4`). -/
example : rc 10 = 4 ∧ gapSum 10 = 4 := by decide

end

end VOA.RRLower
