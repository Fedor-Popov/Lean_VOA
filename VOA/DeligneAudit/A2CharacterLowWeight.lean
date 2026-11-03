/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CharacterInterface
import VOA.DeligneAudit.A2CharacterGram

/-!
# The A₂ character side in conformal weights `0, 1, 2`, unconditionally

`demazureCoeff N ≤ dim L_{-3/2}(sl₃)_N` for `N ≤ 2`, with no literature input:

* `N = 0`: the weight-zero space is the vacuum line (`vacuum_grade`), and the vacuum survives;
* `N = 1`: `simple_weightOne_finrank` (nonzero level);
* `N = 2`: the Gram certificate `A2.finrank_grading_two_ge`.

The values `D_0, D_1, D_2 = 1, 8, 36` come from `demazureCoeff_small`.  This is a finite guard on
the conventions of the interface; the all-`N` statement remains `DemazureCharacterBound`.
-/

namespace VOA.DeligneAudit.A2

open VOA.AffineSl3

theorem finrank_grading_zero : Module.finrank ℂ (W.grading (0 : ℕ)) = 1 := by
  have h : W.grading ((0 : ℕ) : ℤ) = ℂ ∙ W.vacuum := W.vacuum_grade
  rw [h]
  exact finrank_span_singleton (simple_vacuum_ne_zero _ level_add_three_ne_zero)

theorem finrank_grading_one : Module.finrank ℂ (W.grading (1 : ℕ)) = 8 :=
  simple_weightOne_finrank _ level_add_three_ne_zero (by norm_num)

/-- (⋆) checked by computation through `q^8` (`1, 8, 36, 128, 394, 1088, 2776, 6656, 15155`). -/
theorem demazureCoeff_eq_productCoeff_upto_eight :
    (List.range 9).map demazureCoeff = (List.range 9).map productCoeff := by
  decide +kernel

/-- **The character side holds unconditionally in weights `0, 1, 2`.** -/
theorem demazureCoeff_le_finrank_of_le_two (N : ℕ) (hN : N ≤ 2) :
    demazureCoeff N ≤ Module.finrank ℂ (W.grading N) := by
  have hD := demazureCoeff_small
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq] at hD
  interval_cases N
  · rw [hD.1, finrank_grading_zero]
  · rw [hD.2.1, finrank_grading_one]
  · rw [hD.2.2.1]; exact finrank_grading_two_ge

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.demazureCoeff_eq_productCoeff_upto_eight
#print axioms VOA.DeligneAudit.A2.finrank_grading_zero
#print axioms VOA.DeligneAudit.A2.finrank_grading_one
#print axioms VOA.DeligneAudit.A2.demazureCoeff_le_finrank_of_le_two
end AxiomAudit
