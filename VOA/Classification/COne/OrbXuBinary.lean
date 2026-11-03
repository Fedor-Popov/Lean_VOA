import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
# Small binary-form certificates for Xu's icosahedral channels

These are identities of actual polynomials with actual partial derivatives.
They do not assert an invariant-ring presentation or identify a VOA mode with
a transvectant. Those are separate representation-theoretic steps.
Source: Xu, arXiv:2608.13872v2, Lemma 6.2 and Lemma 7.5.
-/

set_option Elab.async false

noncomputable section

namespace VOA.Classification.COne.OrbXu
open MvPolynomial

abbrev Binary := MvPolynomial (Fin 2) ℚ

@[simp] theorem pderiv_numeral (i : Fin 2) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Binary) = 0 :=
  Derivation.map_natCast (pderiv i) n

/-- Klein's degree-12 form, corresponding to spin 6 and VOA weight 36. -/
def kleinF : Binary := X 0 ^ 11 * X 1 + 11 * X 0 ^ 6 * X 1 ^ 6 - X 0 * X 1 ^ 11

/-- The normalization of the degree-20 form in Xu's Lemma 6.2. -/
def kleinH : Binary := -X 0 ^ 20 + 228 * X 0 ^ 15 * X 1 ^ 5 -
  494 * X 0 ^ 10 * X 1 ^ 10 - 228 * X 0 ^ 5 * X 1 ^ 15 - X 1 ^ 20

/-- The degree-30 Jacobian form, normalized to have leading coefficient 1. -/
def kleinT : Binary := X 0 ^ 30 + 522 * X 0 ^ 25 * X 1 ^ 5 -
  10005 * X 0 ^ 20 * X 1 ^ 10 - 10005 * X 0 ^ 10 * X 1 ^ 20 -
  522 * X 0 ^ 5 * X 1 ^ 25 + X 1 ^ 30

/-- Actual repeated differentiation, first in the second variable. -/
noncomputable def mixed (a b : ℕ) (F : Binary) : Binary :=
  (pderiv 0)^[a] ((pderiv 1)^[b] F)

/-- Unnormalized transvectant, using Xu's convention. -/
noncomputable def transvectant (q : ℕ) (F G : Binary) : Binary :=
  ∑ j ∈ Finset.range (q + 1),
    ((-1 : Binary) ^ j * (q.choose j : Binary)) * mixed (q - j) j F * mixed j (q - j) G

theorem mixed_succ_left (a b : ℕ) (F : Binary) :
    mixed (a + 1) b F = pderiv 0 (mixed a b F) := by
  simp only [mixed, Function.iterate_succ_apply']

theorem mixed_zero_succ (b : ℕ) (F : Binary) :
    mixed 0 (b + 1) F = pderiv 1 (mixed 0 b F) := by
  simp only [mixed, Function.iterate_zero_apply, Function.iterate_succ_apply']

/- The table contains at most three monomials per derivative. Normalizing after
   each derivative avoids repeatedly expanding unnormalized product rules. -/
private theorem df_0_0 : mixed 0 0 kleinF = kleinF := rfl

private theorem df_1_0 : mixed 1 0 kleinF =
    (11 : Binary) * X 0 ^ 10 * X 1 ^ 1 +
    (66 : Binary) * X 0 ^ 5 * X 1 ^ 6 +
    (-1 : Binary) * X 0 ^ 0 * X 1 ^ 11 := by
  rw [mixed_succ_left, df_0_0]
  simp [kleinF]
  ring

private theorem df_2_0 : mixed 2 0 kleinF =
    (110 : Binary) * X 0 ^ 9 * X 1 ^ 1 + (330 : Binary) * X 0 ^ 4 * X 1 ^ 6 := by
  rw [mixed_succ_left, df_1_0]
  simp
  ring

private theorem df_3_0 : mixed 3 0 kleinF =
    (990 : Binary) * X 0 ^ 8 * X 1 ^ 1 + (1320 : Binary) * X 0 ^ 3 * X 1 ^ 6 := by
  rw [mixed_succ_left, df_2_0]
  simp
  ring

private theorem df_4_0 : mixed 4 0 kleinF =
    (7920 : Binary) * X 0 ^ 7 * X 1 ^ 1 + (3960 : Binary) * X 0 ^ 2 * X 1 ^ 6 := by
  rw [mixed_succ_left, df_3_0]
  simp
  ring

private theorem df_5_0 : mixed 5 0 kleinF =
    (55440 : Binary) * X 0 ^ 6 * X 1 ^ 1 + (7920 : Binary) * X 0 ^ 1 * X 1 ^ 6 := by
  rw [mixed_succ_left, df_4_0]
  simp
  ring

private theorem df_6_0 : mixed 6 0 kleinF =
    (332640 : Binary) * X 0 ^ 5 * X 1 ^ 1 + (7920 : Binary) * X 0 ^ 0 * X 1 ^ 6 := by
  rw [mixed_succ_left, df_5_0]
  simp
  ring

private theorem df_7_0 : mixed 7 0 kleinF =
    (1663200 : Binary) * X 0 ^ 4 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_6_0]
  simp
  ring

private theorem df_8_0 : mixed 8 0 kleinF =
    (6652800 : Binary) * X 0 ^ 3 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_7_0]
  simp
  ring

private theorem df_9_0 : mixed 9 0 kleinF =
    (19958400 : Binary) * X 0 ^ 2 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_8_0]
  simp
  ring

private theorem df_10_0 : mixed 10 0 kleinF =
    (39916800 : Binary) * X 0 ^ 1 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_9_0]
  simp
  ring

private theorem df_11_0 : mixed 11 0 kleinF =
    (39916800 : Binary) * X 0 ^ 0 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_10_0]
  simp
  ring

private theorem df_12_0 : mixed 12 0 kleinF =
    0 := by
  rw [mixed_succ_left, df_11_0]
  simp

private theorem df_0_1 : mixed 0 1 kleinF =
    (1 : Binary) * X 0 ^ 11 * X 1 ^ 0 +
    (66 : Binary) * X 0 ^ 6 * X 1 ^ 5 +
    (-11 : Binary) * X 0 ^ 1 * X 1 ^ 10 := by
  rw [mixed_zero_succ, df_0_0]
  simp [kleinF]
  ring

private theorem df_1_1 : mixed 1 1 kleinF =
    (11 : Binary) * X 0 ^ 10 * X 1 ^ 0 +
    (396 : Binary) * X 0 ^ 5 * X 1 ^ 5 +
    (-11 : Binary) * X 0 ^ 0 * X 1 ^ 10 := by
  rw [mixed_succ_left, df_0_1]
  simp
  ring

private theorem df_2_1 : mixed 2 1 kleinF =
    (110 : Binary) * X 0 ^ 9 * X 1 ^ 0 + (1980 : Binary) * X 0 ^ 4 * X 1 ^ 5 := by
  rw [mixed_succ_left, df_1_1]
  simp
  ring

private theorem df_3_1 : mixed 3 1 kleinF =
    (990 : Binary) * X 0 ^ 8 * X 1 ^ 0 + (7920 : Binary) * X 0 ^ 3 * X 1 ^ 5 := by
  rw [mixed_succ_left, df_2_1]
  simp
  ring

private theorem df_4_1 : mixed 4 1 kleinF =
    (7920 : Binary) * X 0 ^ 7 * X 1 ^ 0 + (23760 : Binary) * X 0 ^ 2 * X 1 ^ 5 := by
  rw [mixed_succ_left, df_3_1]
  simp
  ring

private theorem df_5_1 : mixed 5 1 kleinF =
    (55440 : Binary) * X 0 ^ 6 * X 1 ^ 0 + (47520 : Binary) * X 0 ^ 1 * X 1 ^ 5 := by
  rw [mixed_succ_left, df_4_1]
  simp
  ring

private theorem df_6_1 : mixed 6 1 kleinF =
    (332640 : Binary) * X 0 ^ 5 * X 1 ^ 0 + (47520 : Binary) * X 0 ^ 0 * X 1 ^ 5 := by
  rw [mixed_succ_left, df_5_1]
  simp
  ring

private theorem df_7_1 : mixed 7 1 kleinF =
    (1663200 : Binary) * X 0 ^ 4 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_6_1]
  simp
  ring

private theorem df_8_1 : mixed 8 1 kleinF =
    (6652800 : Binary) * X 0 ^ 3 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_7_1]
  simp
  ring

private theorem df_9_1 : mixed 9 1 kleinF =
    (19958400 : Binary) * X 0 ^ 2 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_8_1]
  simp
  ring

private theorem df_10_1 : mixed 10 1 kleinF =
    (39916800 : Binary) * X 0 ^ 1 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_9_1]
  simp
  ring

private theorem df_11_1 : mixed 11 1 kleinF =
    (39916800 : Binary) * X 0 ^ 0 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_10_1]
  simp

private theorem df_0_2 : mixed 0 2 kleinF =
    (330 : Binary) * X 0 ^ 6 * X 1 ^ 4 + (-110 : Binary) * X 0 ^ 1 * X 1 ^ 9 := by
  rw [mixed_zero_succ, df_0_1]
  simp
  ring

private theorem df_1_2 : mixed 1 2 kleinF =
    (1980 : Binary) * X 0 ^ 5 * X 1 ^ 4 + (-110 : Binary) * X 0 ^ 0 * X 1 ^ 9 := by
  rw [mixed_succ_left, df_0_2]
  simp
  ring

private theorem df_2_2 : mixed 2 2 kleinF =
    (9900 : Binary) * X 0 ^ 4 * X 1 ^ 4 := by
  rw [mixed_succ_left, df_1_2]
  simp
  ring

private theorem df_3_2 : mixed 3 2 kleinF =
    (39600 : Binary) * X 0 ^ 3 * X 1 ^ 4 := by
  rw [mixed_succ_left, df_2_2]
  simp
  ring

private theorem df_4_2 : mixed 4 2 kleinF =
    (118800 : Binary) * X 0 ^ 2 * X 1 ^ 4 := by
  rw [mixed_succ_left, df_3_2]
  simp
  ring

private theorem df_5_2 : mixed 5 2 kleinF =
    (237600 : Binary) * X 0 ^ 1 * X 1 ^ 4 := by
  rw [mixed_succ_left, df_4_2]
  simp
  ring

private theorem df_6_2 : mixed 6 2 kleinF =
    (237600 : Binary) * X 0 ^ 0 * X 1 ^ 4 := by
  rw [mixed_succ_left, df_5_2]
  simp
  ring

private theorem df_7_2 : mixed 7 2 kleinF =
    0 := by
  rw [mixed_succ_left, df_6_2]
  simp

private theorem df_8_2 : mixed 8 2 kleinF =
    0 := by
  rw [mixed_succ_left, df_7_2]
  simp

private theorem df_9_2 : mixed 9 2 kleinF =
    0 := by
  rw [mixed_succ_left, df_8_2]
  simp

private theorem df_10_2 : mixed 10 2 kleinF =
    0 := by
  rw [mixed_succ_left, df_9_2]
  simp

private theorem df_0_3 : mixed 0 3 kleinF =
    (1320 : Binary) * X 0 ^ 6 * X 1 ^ 3 + (-990 : Binary) * X 0 ^ 1 * X 1 ^ 8 := by
  rw [mixed_zero_succ, df_0_2]
  simp
  ring

private theorem df_1_3 : mixed 1 3 kleinF =
    (7920 : Binary) * X 0 ^ 5 * X 1 ^ 3 + (-990 : Binary) * X 0 ^ 0 * X 1 ^ 8 := by
  rw [mixed_succ_left, df_0_3]
  simp
  ring

private theorem df_2_3 : mixed 2 3 kleinF =
    (39600 : Binary) * X 0 ^ 4 * X 1 ^ 3 := by
  rw [mixed_succ_left, df_1_3]
  simp
  ring

private theorem df_3_3 : mixed 3 3 kleinF =
    (158400 : Binary) * X 0 ^ 3 * X 1 ^ 3 := by
  rw [mixed_succ_left, df_2_3]
  simp
  ring

private theorem df_4_3 : mixed 4 3 kleinF =
    (475200 : Binary) * X 0 ^ 2 * X 1 ^ 3 := by
  rw [mixed_succ_left, df_3_3]
  simp
  ring

private theorem df_5_3 : mixed 5 3 kleinF =
    (950400 : Binary) * X 0 ^ 1 * X 1 ^ 3 := by
  rw [mixed_succ_left, df_4_3]
  simp
  ring

private theorem df_6_3 : mixed 6 3 kleinF =
    (950400 : Binary) * X 0 ^ 0 * X 1 ^ 3 := by
  rw [mixed_succ_left, df_5_3]
  simp
  ring

private theorem df_7_3 : mixed 7 3 kleinF =
    0 := by
  rw [mixed_succ_left, df_6_3]
  simp

private theorem df_8_3 : mixed 8 3 kleinF =
    0 := by
  rw [mixed_succ_left, df_7_3]
  simp

private theorem df_9_3 : mixed 9 3 kleinF =
    0 := by
  rw [mixed_succ_left, df_8_3]
  simp

private theorem df_0_4 : mixed 0 4 kleinF =
    (3960 : Binary) * X 0 ^ 6 * X 1 ^ 2 + (-7920 : Binary) * X 0 ^ 1 * X 1 ^ 7 := by
  rw [mixed_zero_succ, df_0_3]
  simp
  ring

private theorem df_1_4 : mixed 1 4 kleinF =
    (23760 : Binary) * X 0 ^ 5 * X 1 ^ 2 + (-7920 : Binary) * X 0 ^ 0 * X 1 ^ 7 := by
  rw [mixed_succ_left, df_0_4]
  simp
  ring

private theorem df_2_4 : mixed 2 4 kleinF =
    (118800 : Binary) * X 0 ^ 4 * X 1 ^ 2 := by
  rw [mixed_succ_left, df_1_4]
  simp
  ring

private theorem df_3_4 : mixed 3 4 kleinF =
    (475200 : Binary) * X 0 ^ 3 * X 1 ^ 2 := by
  rw [mixed_succ_left, df_2_4]
  simp
  ring

private theorem df_4_4 : mixed 4 4 kleinF =
    (1425600 : Binary) * X 0 ^ 2 * X 1 ^ 2 := by
  rw [mixed_succ_left, df_3_4]
  simp
  ring

private theorem df_5_4 : mixed 5 4 kleinF =
    (2851200 : Binary) * X 0 ^ 1 * X 1 ^ 2 := by
  rw [mixed_succ_left, df_4_4]
  simp
  ring

private theorem df_6_4 : mixed 6 4 kleinF =
    (2851200 : Binary) * X 0 ^ 0 * X 1 ^ 2 := by
  rw [mixed_succ_left, df_5_4]
  simp
  ring

private theorem df_7_4 : mixed 7 4 kleinF =
    0 := by
  rw [mixed_succ_left, df_6_4]
  simp

private theorem df_8_4 : mixed 8 4 kleinF =
    0 := by
  rw [mixed_succ_left, df_7_4]
  simp

private theorem df_0_5 : mixed 0 5 kleinF =
    (7920 : Binary) * X 0 ^ 6 * X 1 ^ 1 + (-55440 : Binary) * X 0 ^ 1 * X 1 ^ 6 := by
  rw [mixed_zero_succ, df_0_4]
  simp
  ring

private theorem df_1_5 : mixed 1 5 kleinF =
    (47520 : Binary) * X 0 ^ 5 * X 1 ^ 1 + (-55440 : Binary) * X 0 ^ 0 * X 1 ^ 6 := by
  rw [mixed_succ_left, df_0_5]
  simp
  ring

private theorem df_2_5 : mixed 2 5 kleinF =
    (237600 : Binary) * X 0 ^ 4 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_1_5]
  simp
  ring

private theorem df_3_5 : mixed 3 5 kleinF =
    (950400 : Binary) * X 0 ^ 3 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_2_5]
  simp
  ring

private theorem df_4_5 : mixed 4 5 kleinF =
    (2851200 : Binary) * X 0 ^ 2 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_3_5]
  simp
  ring

private theorem df_5_5 : mixed 5 5 kleinF =
    (5702400 : Binary) * X 0 ^ 1 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_4_5]
  simp
  ring

private theorem df_6_5 : mixed 6 5 kleinF =
    (5702400 : Binary) * X 0 ^ 0 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_5_5]
  simp
  ring

private theorem df_7_5 : mixed 7 5 kleinF =
    0 := by
  rw [mixed_succ_left, df_6_5]
  simp

private theorem df_0_6 : mixed 0 6 kleinF =
    (7920 : Binary) * X 0 ^ 6 * X 1 ^ 0 + (-332640 : Binary) * X 0 ^ 1 * X 1 ^ 5 := by
  rw [mixed_zero_succ, df_0_5]
  simp
  ring

private theorem df_1_6 : mixed 1 6 kleinF =
    (47520 : Binary) * X 0 ^ 5 * X 1 ^ 0 + (-332640 : Binary) * X 0 ^ 0 * X 1 ^ 5 := by
  rw [mixed_succ_left, df_0_6]
  simp
  ring

private theorem df_2_6 : mixed 2 6 kleinF =
    (237600 : Binary) * X 0 ^ 4 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_1_6]
  simp
  ring

private theorem df_3_6 : mixed 3 6 kleinF =
    (950400 : Binary) * X 0 ^ 3 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_2_6]
  simp
  ring

private theorem df_4_6 : mixed 4 6 kleinF =
    (2851200 : Binary) * X 0 ^ 2 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_3_6]
  simp
  ring

private theorem df_5_6 : mixed 5 6 kleinF =
    (5702400 : Binary) * X 0 ^ 1 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_4_6]
  simp
  ring

private theorem df_6_6 : mixed 6 6 kleinF =
    (5702400 : Binary) * X 0 ^ 0 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_5_6]
  simp

private theorem df_0_7 : mixed 0 7 kleinF =
    (-1663200 : Binary) * X 0 ^ 1 * X 1 ^ 4 := by
  rw [mixed_zero_succ, df_0_6]
  simp
  ring

private theorem df_1_7 : mixed 1 7 kleinF =
    (-1663200 : Binary) * X 0 ^ 0 * X 1 ^ 4 := by
  rw [mixed_succ_left, df_0_7]
  simp
  ring

private theorem df_2_7 : mixed 2 7 kleinF =
    0 := by
  rw [mixed_succ_left, df_1_7]
  simp

private theorem df_3_7 : mixed 3 7 kleinF =
    0 := by
  rw [mixed_succ_left, df_2_7]
  simp

private theorem df_4_7 : mixed 4 7 kleinF =
    0 := by
  rw [mixed_succ_left, df_3_7]
  simp

private theorem df_5_7 : mixed 5 7 kleinF =
    0 := by
  rw [mixed_succ_left, df_4_7]
  simp

private theorem df_0_8 : mixed 0 8 kleinF =
    (-6652800 : Binary) * X 0 ^ 1 * X 1 ^ 3 := by
  rw [mixed_zero_succ, df_0_7]
  simp
  ring

private theorem df_1_8 : mixed 1 8 kleinF =
    (-6652800 : Binary) * X 0 ^ 0 * X 1 ^ 3 := by
  rw [mixed_succ_left, df_0_8]
  simp
  ring

private theorem df_2_8 : mixed 2 8 kleinF =
    0 := by
  rw [mixed_succ_left, df_1_8]
  simp

private theorem df_3_8 : mixed 3 8 kleinF =
    0 := by
  rw [mixed_succ_left, df_2_8]
  simp

private theorem df_4_8 : mixed 4 8 kleinF =
    0 := by
  rw [mixed_succ_left, df_3_8]
  simp

private theorem df_0_9 : mixed 0 9 kleinF =
    (-19958400 : Binary) * X 0 ^ 1 * X 1 ^ 2 := by
  rw [mixed_zero_succ, df_0_8]
  simp
  ring

private theorem df_1_9 : mixed 1 9 kleinF =
    (-19958400 : Binary) * X 0 ^ 0 * X 1 ^ 2 := by
  rw [mixed_succ_left, df_0_9]
  simp
  ring

private theorem df_2_9 : mixed 2 9 kleinF =
    0 := by
  rw [mixed_succ_left, df_1_9]
  simp

private theorem df_3_9 : mixed 3 9 kleinF =
    0 := by
  rw [mixed_succ_left, df_2_9]
  simp

private theorem df_0_10 : mixed 0 10 kleinF =
    (-39916800 : Binary) * X 0 ^ 1 * X 1 ^ 1 := by
  rw [mixed_zero_succ, df_0_9]
  simp
  ring

private theorem df_1_10 : mixed 1 10 kleinF =
    (-39916800 : Binary) * X 0 ^ 0 * X 1 ^ 1 := by
  rw [mixed_succ_left, df_0_10]
  simp
  ring

private theorem df_2_10 : mixed 2 10 kleinF =
    0 := by
  rw [mixed_succ_left, df_1_10]
  simp

private theorem df_0_11 : mixed 0 11 kleinF =
    (-39916800 : Binary) * X 0 ^ 1 * X 1 ^ 0 := by
  rw [mixed_zero_succ, df_0_10]
  simp

private theorem df_1_11 : mixed 1 11 kleinF =
    (-39916800 : Binary) * X 0 ^ 0 * X 1 ^ 0 := by
  rw [mixed_succ_left, df_0_11]
  simp

private theorem df_0_12 : mixed 0 12 kleinF =
    0 := by
  rw [mixed_zero_succ, df_0_11]
  simp

theorem transvectant_two : transvectant 2 kleinF kleinF = 242 * kleinH := by
  simp only [transvectant, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [Nat.choose]
  rw [df_2_0, df_1_1, df_0_2]
  unfold kleinH
  ring

theorem transvectant_six : transvectant 6 kleinF kleinF = -26345088000 * kleinF := by
  simp only [transvectant, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [Nat.choose]
  rw [df_6_0, df_5_1, df_4_2, df_3_3, df_2_4, df_1_5, df_0_6]
  unfold kleinF
  ring

theorem transvectant_twelve : transvectant 12 kleinF kleinF = 68286468096000000 := by
  simp only [transvectant, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [Nat.choose]
  rw [df_12_0,
    df_11_1,
    df_10_2,
    df_9_3,
    df_8_4,
    df_7_5,
    df_6_6,
    df_5_7,
    df_4_8,
    df_3_9,
    df_2_10,
    df_1_11,
    df_0_12]
  ring

theorem transvectant_one : transvectant 1 kleinF kleinH = 20 * kleinT := by
  simp only [transvectant, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [mixed, kleinF, kleinH, kleinT, pderiv_X]
  ring

theorem kleinF_ne_zero : kleinF ≠ 0 := by
  intro h
  have he := congrArg (eval ![(1 : ℚ), 1]) h
  norm_num [kleinF] at he

theorem kleinH_ne_zero : kleinH ≠ 0 := by
  intro h
  have he := congrArg (eval ![(1 : ℚ), 0]) h
  norm_num [kleinH] at he

theorem kleinT_ne_zero : kleinT ≠ 0 := by
  intro h
  have he := congrArg (eval ![(1 : ℚ), 0]) h
  norm_num [kleinT] at he

theorem klein_relation : kleinT ^ 2 + kleinH ^ 3 = 1728 * kleinF ^ 5 := by
  unfold kleinT kleinH kleinF
  ring

/-- The four finite polynomial identities needed for the relevant channels.
This is deliberately a polynomial statement, not the missing VOA bridge. -/
def XuBinaryChannelIdentities : Prop :=
  transvectant 2 kleinF kleinF = 242 * kleinH ∧
  transvectant 6 kleinF kleinF = -26345088000 * kleinF ∧
  transvectant 12 kleinF kleinF = 68286468096000000 ∧
  transvectant 1 kleinF kleinH = 20 * kleinT

theorem xuBinaryChannelIdentities_holds : XuBinaryChannelIdentities :=
  ⟨transvectant_two, transvectant_six, transvectant_twelve, transvectant_one⟩

/-- In particular all four polynomial projections are nonzero. -/
theorem binary_channels_nonzero :
    transvectant 2 kleinF kleinF ≠ 0 ∧ transvectant 6 kleinF kleinF ≠ 0 ∧
    transvectant 12 kleinF kleinF ≠ 0 ∧ transvectant 1 kleinF kleinH ≠ 0 := by
  rw [transvectant_two, transvectant_six, transvectant_twelve, transvectant_one]
  exact ⟨mul_ne_zero (by norm_num) kleinH_ne_zero,
    mul_ne_zero (by norm_num) kleinF_ne_zero, by norm_num,
    mul_ne_zero (by norm_num) kleinT_ne_zero⟩

end VOA.Classification.COne.OrbXu
