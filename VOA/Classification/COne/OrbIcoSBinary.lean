import VOA.Classification.COne.OrbIcoCoef
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! The sixth and twelfth transvectants in the actual `psi J6` frame.
These are polynomial identities; they do not identify VOA channel coefficients. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoS
open MvPolynomial OrbPrim OrbIco

@[local simp] private theorem pderiv_numeral (i : Fin 2) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : P2) = 0 :=
  Derivation.map_natCast (pderiv i) n

/-- Repeated differentiation over the complex binary-form space. -/
def mixedC (a b : ℕ) (F : P2) : P2 :=
  (pderiv 0)^[a] ((pderiv 1)^[b] F)

/-- Unnormalized transvectant, with the convention used by `OrbXu.transvectant`. -/
def transvectantC (q : ℕ) (F G : P2) : P2 :=
  ∑ j ∈ Finset.range (q + 1),
    ((-1 : P2) ^ j * (q.choose j : P2)) * mixedC (q - j) j F * mixedC j (q - j) G

theorem mixedC_succ_left (a b : ℕ) (F : P2) :
    mixedC (a + 1) b F = pderiv 0 (mixedC a b F) := by
  simp only [mixedC, Function.iterate_succ_apply']

theorem mixedC_zero_succ (b : ℕ) (F : P2) :
    mixedC 0 (b + 1) F = pderiv 1 (mixedC 0 b F) := by
  simp only [mixedC, Function.iterate_zero_apply, Function.iterate_succ_apply']

private theorem df_0_0 : mixedC 0 0 fpoly = fpoly := rfl

private theorem df_1_0 : mixedC 1 0 fpoly =
    (12 : P2) * MvPolynomial.C f0 * X 0 ^ 11 * X 1 ^ 0 +
    (10 : P2) * MvPolynomial.C f2 * X 0 ^ 9 * X 1 ^ 2 +
    (8 : P2) * MvPolynomial.C f4 * X 0 ^ 7 * X 1 ^ 4 +
    (6 : P2) * MvPolynomial.C f6 * X 0 ^ 5 * X 1 ^ 6 +
    (4 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 8 +
    (2 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 10 := by
  rw [mixedC_succ_left, df_0_0]
  simp [fpoly]
  ring

private theorem df_2_0 : mixedC 2 0 fpoly =
    (132 : P2) * MvPolynomial.C f0 * X 0 ^ 10 * X 1 ^ 0 +
    (90 : P2) * MvPolynomial.C f2 * X 0 ^ 8 * X 1 ^ 2 +
    (56 : P2) * MvPolynomial.C f4 * X 0 ^ 6 * X 1 ^ 4 +
    (30 : P2) * MvPolynomial.C f6 * X 0 ^ 4 * X 1 ^ 6 +
    (12 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 8 +
    (2 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 10 := by
  rw [mixedC_succ_left, df_1_0]
  simp
  ring

private theorem df_3_0 : mixedC 3 0 fpoly =
    (1320 : P2) * MvPolynomial.C f0 * X 0 ^ 9 * X 1 ^ 0 +
    (720 : P2) * MvPolynomial.C f2 * X 0 ^ 7 * X 1 ^ 2 +
    (336 : P2) * MvPolynomial.C f4 * X 0 ^ 5 * X 1 ^ 4 +
    (120 : P2) * MvPolynomial.C f6 * X 0 ^ 3 * X 1 ^ 6 +
    (24 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 8 := by
  rw [mixedC_succ_left, df_2_0]
  simp
  ring

private theorem df_4_0 : mixedC 4 0 fpoly =
    (11880 : P2) * MvPolynomial.C f0 * X 0 ^ 8 * X 1 ^ 0 +
    (5040 : P2) * MvPolynomial.C f2 * X 0 ^ 6 * X 1 ^ 2 +
    (1680 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 4 +
    (360 : P2) * MvPolynomial.C f6 * X 0 ^ 2 * X 1 ^ 6 +
    (24 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 8 := by
  rw [mixedC_succ_left, df_3_0]
  simp
  ring

private theorem df_5_0 : mixedC 5 0 fpoly =
    (95040 : P2) * MvPolynomial.C f0 * X 0 ^ 7 * X 1 ^ 0 +
    (30240 : P2) * MvPolynomial.C f2 * X 0 ^ 5 * X 1 ^ 2 +
    (6720 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 4 +
    (720 : P2) * MvPolynomial.C f6 * X 0 ^ 1 * X 1 ^ 6 := by
  rw [mixedC_succ_left, df_4_0]
  simp
  ring

private theorem df_6_0 : mixedC 6 0 fpoly =
    (665280 : P2) * MvPolynomial.C f0 * X 0 ^ 6 * X 1 ^ 0 +
    (151200 : P2) * MvPolynomial.C f2 * X 0 ^ 4 * X 1 ^ 2 +
    (20160 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 4 +
    (720 : P2) * MvPolynomial.C f6 * X 0 ^ 0 * X 1 ^ 6 := by
  rw [mixedC_succ_left, df_5_0]
  simp
  ring

private theorem df_7_0 : mixedC 7 0 fpoly =
    (3991680 : P2) * MvPolynomial.C f0 * X 0 ^ 5 * X 1 ^ 0 +
    (604800 : P2) * MvPolynomial.C f2 * X 0 ^ 3 * X 1 ^ 2 +
    (40320 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 4 := by
  rw [mixedC_succ_left, df_6_0]
  simp
  ring

private theorem df_8_0 : mixedC 8 0 fpoly =
    (19958400 : P2) * MvPolynomial.C f0 * X 0 ^ 4 * X 1 ^ 0 +
    (1814400 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 2 +
    (40320 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 4 := by
  rw [mixedC_succ_left, df_7_0]
  simp
  ring

private theorem df_9_0 : mixedC 9 0 fpoly =
    (79833600 : P2) * MvPolynomial.C f0 * X 0 ^ 3 * X 1 ^ 0 +
    (3628800 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 2 := by
  rw [mixedC_succ_left, df_8_0]
  simp
  ring

private theorem df_10_0 : mixedC 10 0 fpoly =
    (239500800 : P2) * MvPolynomial.C f0 * X 0 ^ 2 * X 1 ^ 0 +
    (3628800 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 2 := by
  rw [mixedC_succ_left, df_9_0]
  simp
  ring

private theorem df_11_0 : mixedC 11 0 fpoly =
    (479001600 : P2) * MvPolynomial.C f0 * X 0 ^ 1 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_10_0]
  simp
  ring

private theorem df_12_0 : mixedC 12 0 fpoly =
    (479001600 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_11_0]
  simp

private theorem df_0_1 : mixedC 0 1 fpoly =
    (2 : P2) * MvPolynomial.C f2 * X 0 ^ 10 * X 1 ^ 1 +
    (4 : P2) * MvPolynomial.C f4 * X 0 ^ 8 * X 1 ^ 3 +
    (6 : P2) * MvPolynomial.C f6 * X 0 ^ 6 * X 1 ^ 5 +
    (8 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 7 +
    (10 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 9 +
    (12 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 11 := by
  rw [mixedC_zero_succ, df_0_0]
  simp [fpoly]
  ring

private theorem df_1_1 : mixedC 1 1 fpoly =
    (20 : P2) * MvPolynomial.C f2 * X 0 ^ 9 * X 1 ^ 1 +
    (32 : P2) * MvPolynomial.C f4 * X 0 ^ 7 * X 1 ^ 3 +
    (36 : P2) * MvPolynomial.C f6 * X 0 ^ 5 * X 1 ^ 5 +
    (32 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 7 +
    (20 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 9 := by
  rw [mixedC_succ_left, df_0_1]
  simp
  ring

private theorem df_2_1 : mixedC 2 1 fpoly =
    (180 : P2) * MvPolynomial.C f2 * X 0 ^ 8 * X 1 ^ 1 +
    (224 : P2) * MvPolynomial.C f4 * X 0 ^ 6 * X 1 ^ 3 +
    (180 : P2) * MvPolynomial.C f6 * X 0 ^ 4 * X 1 ^ 5 +
    (96 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 7 +
    (20 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 9 := by
  rw [mixedC_succ_left, df_1_1]
  simp
  ring

private theorem df_3_1 : mixedC 3 1 fpoly =
    (1440 : P2) * MvPolynomial.C f2 * X 0 ^ 7 * X 1 ^ 1 +
    (1344 : P2) * MvPolynomial.C f4 * X 0 ^ 5 * X 1 ^ 3 +
    (720 : P2) * MvPolynomial.C f6 * X 0 ^ 3 * X 1 ^ 5 +
    (192 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 7 := by
  rw [mixedC_succ_left, df_2_1]
  simp
  ring

private theorem df_4_1 : mixedC 4 1 fpoly =
    (10080 : P2) * MvPolynomial.C f2 * X 0 ^ 6 * X 1 ^ 1 +
    (6720 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 3 +
    (2160 : P2) * MvPolynomial.C f6 * X 0 ^ 2 * X 1 ^ 5 +
    (192 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 7 := by
  rw [mixedC_succ_left, df_3_1]
  simp
  ring

private theorem df_5_1 : mixedC 5 1 fpoly =
    (60480 : P2) * MvPolynomial.C f2 * X 0 ^ 5 * X 1 ^ 1 +
    (26880 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 3 +
    (4320 : P2) * MvPolynomial.C f6 * X 0 ^ 1 * X 1 ^ 5 := by
  rw [mixedC_succ_left, df_4_1]
  simp
  ring

private theorem df_6_1 : mixedC 6 1 fpoly =
    (302400 : P2) * MvPolynomial.C f2 * X 0 ^ 4 * X 1 ^ 1 +
    (80640 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 3 +
    (4320 : P2) * MvPolynomial.C f6 * X 0 ^ 0 * X 1 ^ 5 := by
  rw [mixedC_succ_left, df_5_1]
  simp
  ring

private theorem df_7_1 : mixedC 7 1 fpoly =
    (1209600 : P2) * MvPolynomial.C f2 * X 0 ^ 3 * X 1 ^ 1 +
    (161280 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 3 := by
  rw [mixedC_succ_left, df_6_1]
  simp
  ring

private theorem df_8_1 : mixedC 8 1 fpoly =
    (3628800 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 1 +
    (161280 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 3 := by
  rw [mixedC_succ_left, df_7_1]
  simp
  ring

private theorem df_9_1 : mixedC 9 1 fpoly =
    (7257600 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 1 := by
  rw [mixedC_succ_left, df_8_1]
  simp
  ring

private theorem df_10_1 : mixedC 10 1 fpoly =
    (7257600 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 1 := by
  rw [mixedC_succ_left, df_9_1]
  simp
  ring

private theorem df_11_1 : mixedC 11 1 fpoly =
    0 := by
  rw [mixedC_succ_left, df_10_1]
  simp

private theorem df_0_2 : mixedC 0 2 fpoly =
    (2 : P2) * MvPolynomial.C f2 * X 0 ^ 10 * X 1 ^ 0 +
    (12 : P2) * MvPolynomial.C f4 * X 0 ^ 8 * X 1 ^ 2 +
    (30 : P2) * MvPolynomial.C f6 * X 0 ^ 6 * X 1 ^ 4 +
    (56 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 6 +
    (90 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 8 +
    (132 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 10 := by
  rw [mixedC_zero_succ, df_0_1]
  simp
  ring

private theorem df_1_2 : mixedC 1 2 fpoly =
    (20 : P2) * MvPolynomial.C f2 * X 0 ^ 9 * X 1 ^ 0 +
    (96 : P2) * MvPolynomial.C f4 * X 0 ^ 7 * X 1 ^ 2 +
    (180 : P2) * MvPolynomial.C f6 * X 0 ^ 5 * X 1 ^ 4 +
    (224 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 6 +
    (180 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 8 := by
  rw [mixedC_succ_left, df_0_2]
  simp
  ring

private theorem df_2_2 : mixedC 2 2 fpoly =
    (180 : P2) * MvPolynomial.C f2 * X 0 ^ 8 * X 1 ^ 0 +
    (672 : P2) * MvPolynomial.C f4 * X 0 ^ 6 * X 1 ^ 2 +
    (900 : P2) * MvPolynomial.C f6 * X 0 ^ 4 * X 1 ^ 4 +
    (672 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 6 +
    (180 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 8 := by
  rw [mixedC_succ_left, df_1_2]
  simp
  ring

private theorem df_3_2 : mixedC 3 2 fpoly =
    (1440 : P2) * MvPolynomial.C f2 * X 0 ^ 7 * X 1 ^ 0 +
    (4032 : P2) * MvPolynomial.C f4 * X 0 ^ 5 * X 1 ^ 2 +
    (3600 : P2) * MvPolynomial.C f6 * X 0 ^ 3 * X 1 ^ 4 +
    (1344 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 6 := by
  rw [mixedC_succ_left, df_2_2]
  simp
  ring

private theorem df_4_2 : mixedC 4 2 fpoly =
    (10080 : P2) * MvPolynomial.C f2 * X 0 ^ 6 * X 1 ^ 0 +
    (20160 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 2 +
    (10800 : P2) * MvPolynomial.C f6 * X 0 ^ 2 * X 1 ^ 4 +
    (1344 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 6 := by
  rw [mixedC_succ_left, df_3_2]
  simp
  ring

private theorem df_5_2 : mixedC 5 2 fpoly =
    (60480 : P2) * MvPolynomial.C f2 * X 0 ^ 5 * X 1 ^ 0 +
    (80640 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 2 +
    (21600 : P2) * MvPolynomial.C f6 * X 0 ^ 1 * X 1 ^ 4 := by
  rw [mixedC_succ_left, df_4_2]
  simp
  ring

private theorem df_6_2 : mixedC 6 2 fpoly =
    (302400 : P2) * MvPolynomial.C f2 * X 0 ^ 4 * X 1 ^ 0 +
    (241920 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 2 +
    (21600 : P2) * MvPolynomial.C f6 * X 0 ^ 0 * X 1 ^ 4 := by
  rw [mixedC_succ_left, df_5_2]
  simp
  ring

private theorem df_7_2 : mixedC 7 2 fpoly =
    (1209600 : P2) * MvPolynomial.C f2 * X 0 ^ 3 * X 1 ^ 0 +
    (483840 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 2 := by
  rw [mixedC_succ_left, df_6_2]
  simp
  ring

private theorem df_8_2 : mixedC 8 2 fpoly =
    (3628800 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 0 +
    (483840 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 2 := by
  rw [mixedC_succ_left, df_7_2]
  simp
  ring

private theorem df_9_2 : mixedC 9 2 fpoly =
    (7257600 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_8_2]
  simp
  ring

private theorem df_10_2 : mixedC 10 2 fpoly =
    (7257600 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_9_2]
  simp

private theorem df_0_3 : mixedC 0 3 fpoly =
    (24 : P2) * MvPolynomial.C f4 * X 0 ^ 8 * X 1 ^ 1 +
    (120 : P2) * MvPolynomial.C f6 * X 0 ^ 6 * X 1 ^ 3 +
    (336 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 5 +
    (720 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 7 +
    (1320 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 9 := by
  rw [mixedC_zero_succ, df_0_2]
  simp
  ring

private theorem df_1_3 : mixedC 1 3 fpoly =
    (192 : P2) * MvPolynomial.C f4 * X 0 ^ 7 * X 1 ^ 1 +
    (720 : P2) * MvPolynomial.C f6 * X 0 ^ 5 * X 1 ^ 3 +
    (1344 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 5 +
    (1440 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 7 := by
  rw [mixedC_succ_left, df_0_3]
  simp
  ring

private theorem df_2_3 : mixedC 2 3 fpoly =
    (1344 : P2) * MvPolynomial.C f4 * X 0 ^ 6 * X 1 ^ 1 +
    (3600 : P2) * MvPolynomial.C f6 * X 0 ^ 4 * X 1 ^ 3 +
    (4032 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 5 +
    (1440 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 7 := by
  rw [mixedC_succ_left, df_1_3]
  simp
  ring

private theorem df_3_3 : mixedC 3 3 fpoly =
    (8064 : P2) * MvPolynomial.C f4 * X 0 ^ 5 * X 1 ^ 1 +
    (14400 : P2) * MvPolynomial.C f6 * X 0 ^ 3 * X 1 ^ 3 +
    (8064 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 5 := by
  rw [mixedC_succ_left, df_2_3]
  simp
  ring

private theorem df_4_3 : mixedC 4 3 fpoly =
    (40320 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 1 +
    (43200 : P2) * MvPolynomial.C f6 * X 0 ^ 2 * X 1 ^ 3 +
    (8064 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 5 := by
  rw [mixedC_succ_left, df_3_3]
  simp
  ring

private theorem df_5_3 : mixedC 5 3 fpoly =
    (161280 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 1 +
    (86400 : P2) * MvPolynomial.C f6 * X 0 ^ 1 * X 1 ^ 3 := by
  rw [mixedC_succ_left, df_4_3]
  simp
  ring

private theorem df_6_3 : mixedC 6 3 fpoly =
    (483840 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 1 +
    (86400 : P2) * MvPolynomial.C f6 * X 0 ^ 0 * X 1 ^ 3 := by
  rw [mixedC_succ_left, df_5_3]
  simp
  ring

private theorem df_7_3 : mixedC 7 3 fpoly =
    (967680 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 1 := by
  rw [mixedC_succ_left, df_6_3]
  simp
  ring

private theorem df_8_3 : mixedC 8 3 fpoly =
    (967680 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 1 := by
  rw [mixedC_succ_left, df_7_3]
  simp
  ring

private theorem df_9_3 : mixedC 9 3 fpoly =
    0 := by
  rw [mixedC_succ_left, df_8_3]
  simp

private theorem df_0_4 : mixedC 0 4 fpoly =
    (24 : P2) * MvPolynomial.C f4 * X 0 ^ 8 * X 1 ^ 0 +
    (360 : P2) * MvPolynomial.C f6 * X 0 ^ 6 * X 1 ^ 2 +
    (1680 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 4 +
    (5040 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 6 +
    (11880 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 8 := by
  rw [mixedC_zero_succ, df_0_3]
  simp
  ring

private theorem df_1_4 : mixedC 1 4 fpoly =
    (192 : P2) * MvPolynomial.C f4 * X 0 ^ 7 * X 1 ^ 0 +
    (2160 : P2) * MvPolynomial.C f6 * X 0 ^ 5 * X 1 ^ 2 +
    (6720 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 4 +
    (10080 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 6 := by
  rw [mixedC_succ_left, df_0_4]
  simp
  ring

private theorem df_2_4 : mixedC 2 4 fpoly =
    (1344 : P2) * MvPolynomial.C f4 * X 0 ^ 6 * X 1 ^ 0 +
    (10800 : P2) * MvPolynomial.C f6 * X 0 ^ 4 * X 1 ^ 2 +
    (20160 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 4 +
    (10080 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 6 := by
  rw [mixedC_succ_left, df_1_4]
  simp
  ring

private theorem df_3_4 : mixedC 3 4 fpoly =
    (8064 : P2) * MvPolynomial.C f4 * X 0 ^ 5 * X 1 ^ 0 +
    (43200 : P2) * MvPolynomial.C f6 * X 0 ^ 3 * X 1 ^ 2 +
    (40320 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 4 := by
  rw [mixedC_succ_left, df_2_4]
  simp
  ring

private theorem df_4_4 : mixedC 4 4 fpoly =
    (40320 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 0 +
    (129600 : P2) * MvPolynomial.C f6 * X 0 ^ 2 * X 1 ^ 2 +
    (40320 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 4 := by
  rw [mixedC_succ_left, df_3_4]
  simp
  ring

private theorem df_5_4 : mixedC 5 4 fpoly =
    (161280 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 0 +
    (259200 : P2) * MvPolynomial.C f6 * X 0 ^ 1 * X 1 ^ 2 := by
  rw [mixedC_succ_left, df_4_4]
  simp
  ring

private theorem df_6_4 : mixedC 6 4 fpoly =
    (483840 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 0 +
    (259200 : P2) * MvPolynomial.C f6 * X 0 ^ 0 * X 1 ^ 2 := by
  rw [mixedC_succ_left, df_5_4]
  simp
  ring

private theorem df_7_4 : mixedC 7 4 fpoly =
    (967680 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_6_4]
  simp
  ring

private theorem df_8_4 : mixedC 8 4 fpoly =
    (967680 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_7_4]
  simp

private theorem df_0_5 : mixedC 0 5 fpoly =
    (720 : P2) * MvPolynomial.C f6 * X 0 ^ 6 * X 1 ^ 1 +
    (6720 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 3 +
    (30240 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 5 +
    (95040 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 7 := by
  rw [mixedC_zero_succ, df_0_4]
  simp
  ring

private theorem df_1_5 : mixedC 1 5 fpoly =
    (4320 : P2) * MvPolynomial.C f6 * X 0 ^ 5 * X 1 ^ 1 +
    (26880 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 3 +
    (60480 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 5 := by
  rw [mixedC_succ_left, df_0_5]
  simp
  ring

private theorem df_2_5 : mixedC 2 5 fpoly =
    (21600 : P2) * MvPolynomial.C f6 * X 0 ^ 4 * X 1 ^ 1 +
    (80640 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 3 +
    (60480 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 5 := by
  rw [mixedC_succ_left, df_1_5]
  simp
  ring

private theorem df_3_5 : mixedC 3 5 fpoly =
    (86400 : P2) * MvPolynomial.C f6 * X 0 ^ 3 * X 1 ^ 1 +
    (161280 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 3 := by
  rw [mixedC_succ_left, df_2_5]
  simp
  ring

private theorem df_4_5 : mixedC 4 5 fpoly =
    (259200 : P2) * MvPolynomial.C f6 * X 0 ^ 2 * X 1 ^ 1 +
    (161280 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 3 := by
  rw [mixedC_succ_left, df_3_5]
  simp
  ring

private theorem df_5_5 : mixedC 5 5 fpoly =
    (518400 : P2) * MvPolynomial.C f6 * X 0 ^ 1 * X 1 ^ 1 := by
  rw [mixedC_succ_left, df_4_5]
  simp
  ring

private theorem df_6_5 : mixedC 6 5 fpoly =
    (518400 : P2) * MvPolynomial.C f6 * X 0 ^ 0 * X 1 ^ 1 := by
  rw [mixedC_succ_left, df_5_5]
  simp
  ring

private theorem df_7_5 : mixedC 7 5 fpoly =
    0 := by
  rw [mixedC_succ_left, df_6_5]
  simp

private theorem df_0_6 : mixedC 0 6 fpoly =
    (720 : P2) * MvPolynomial.C f6 * X 0 ^ 6 * X 1 ^ 0 +
    (20160 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 2 +
    (151200 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 4 +
    (665280 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 6 := by
  rw [mixedC_zero_succ, df_0_5]
  simp
  ring

private theorem df_1_6 : mixedC 1 6 fpoly =
    (4320 : P2) * MvPolynomial.C f6 * X 0 ^ 5 * X 1 ^ 0 +
    (80640 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 2 +
    (302400 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 4 := by
  rw [mixedC_succ_left, df_0_6]
  simp
  ring

private theorem df_2_6 : mixedC 2 6 fpoly =
    (21600 : P2) * MvPolynomial.C f6 * X 0 ^ 4 * X 1 ^ 0 +
    (241920 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 2 +
    (302400 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 4 := by
  rw [mixedC_succ_left, df_1_6]
  simp
  ring

private theorem df_3_6 : mixedC 3 6 fpoly =
    (86400 : P2) * MvPolynomial.C f6 * X 0 ^ 3 * X 1 ^ 0 +
    (483840 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 2 := by
  rw [mixedC_succ_left, df_2_6]
  simp
  ring

private theorem df_4_6 : mixedC 4 6 fpoly =
    (259200 : P2) * MvPolynomial.C f6 * X 0 ^ 2 * X 1 ^ 0 +
    (483840 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 2 := by
  rw [mixedC_succ_left, df_3_6]
  simp
  ring

private theorem df_5_6 : mixedC 5 6 fpoly =
    (518400 : P2) * MvPolynomial.C f6 * X 0 ^ 1 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_4_6]
  simp
  ring

private theorem df_6_6 : mixedC 6 6 fpoly =
    (518400 : P2) * MvPolynomial.C f6 * X 0 ^ 0 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_5_6]
  simp

private theorem df_0_7 : mixedC 0 7 fpoly =
    (40320 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 1 +
    (604800 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 3 +
    (3991680 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 5 := by
  rw [mixedC_zero_succ, df_0_6]
  simp
  ring

private theorem df_1_7 : mixedC 1 7 fpoly =
    (161280 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 1 +
    (1209600 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 3 := by
  rw [mixedC_succ_left, df_0_7]
  simp
  ring

private theorem df_2_7 : mixedC 2 7 fpoly =
    (483840 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 1 +
    (1209600 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 3 := by
  rw [mixedC_succ_left, df_1_7]
  simp
  ring

private theorem df_3_7 : mixedC 3 7 fpoly =
    (967680 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 1 := by
  rw [mixedC_succ_left, df_2_7]
  simp
  ring

private theorem df_4_7 : mixedC 4 7 fpoly =
    (967680 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 1 := by
  rw [mixedC_succ_left, df_3_7]
  simp
  ring

private theorem df_5_7 : mixedC 5 7 fpoly =
    0 := by
  rw [mixedC_succ_left, df_4_7]
  simp

private theorem df_0_8 : mixedC 0 8 fpoly =
    (40320 : P2) * MvPolynomial.C f4 * X 0 ^ 4 * X 1 ^ 0 +
    (1814400 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 2 +
    (19958400 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 4 := by
  rw [mixedC_zero_succ, df_0_7]
  simp
  ring

private theorem df_1_8 : mixedC 1 8 fpoly =
    (161280 : P2) * MvPolynomial.C f4 * X 0 ^ 3 * X 1 ^ 0 +
    (3628800 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 2 := by
  rw [mixedC_succ_left, df_0_8]
  simp
  ring

private theorem df_2_8 : mixedC 2 8 fpoly =
    (483840 : P2) * MvPolynomial.C f4 * X 0 ^ 2 * X 1 ^ 0 +
    (3628800 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 2 := by
  rw [mixedC_succ_left, df_1_8]
  simp
  ring

private theorem df_3_8 : mixedC 3 8 fpoly =
    (967680 : P2) * MvPolynomial.C f4 * X 0 ^ 1 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_2_8]
  simp
  ring

private theorem df_4_8 : mixedC 4 8 fpoly =
    (967680 : P2) * MvPolynomial.C f4 * X 0 ^ 0 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_3_8]
  simp

private theorem df_0_9 : mixedC 0 9 fpoly =
    (3628800 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 1 +
    (79833600 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 3 := by
  rw [mixedC_zero_succ, df_0_8]
  simp
  ring

private theorem df_1_9 : mixedC 1 9 fpoly =
    (7257600 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 1 := by
  rw [mixedC_succ_left, df_0_9]
  simp
  ring

private theorem df_2_9 : mixedC 2 9 fpoly =
    (7257600 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 1 := by
  rw [mixedC_succ_left, df_1_9]
  simp
  ring

private theorem df_3_9 : mixedC 3 9 fpoly =
    0 := by
  rw [mixedC_succ_left, df_2_9]
  simp

private theorem df_0_10 : mixedC 0 10 fpoly =
    (3628800 : P2) * MvPolynomial.C f2 * X 0 ^ 2 * X 1 ^ 0 +
    (239500800 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 2 := by
  rw [mixedC_zero_succ, df_0_9]
  simp
  ring

private theorem df_1_10 : mixedC 1 10 fpoly =
    (7257600 : P2) * MvPolynomial.C f2 * X 0 ^ 1 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_0_10]
  simp
  ring

private theorem df_2_10 : mixedC 2 10 fpoly =
    (7257600 : P2) * MvPolynomial.C f2 * X 0 ^ 0 * X 1 ^ 0 := by
  rw [mixedC_succ_left, df_1_10]
  simp

private theorem df_0_11 : mixedC 0 11 fpoly =
    (479001600 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 1 := by
  rw [mixedC_zero_succ, df_0_10]
  simp
  ring

private theorem df_1_11 : mixedC 1 11 fpoly =
    0 := by
  rw [mixedC_succ_left, df_0_11]
  simp

private theorem df_0_12 : mixedC 0 12 fpoly =
    (479001600 : P2) * MvPolynomial.C f0 * X 0 ^ 0 * X 1 ^ 0 := by
  rw [mixedC_zero_succ, df_0_11]
  simp

def sixthScalar : ℂ := 337217126400 + 674434252800 * gp

def twelfthScalar : ℂ := 55940274664243200000 + 89504439462789120000 * gp

set_option maxHeartbeats 2000000 in
-- Normalize the finite derivative products and reduce coefficients using the golden-ratio relation.
theorem ico_transvectant_six :
    transvectantC 6 fpoly fpoly = MvPolynomial.C sixthScalar * fpoly := by
  simp only [transvectantC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [Nat.choose]
  rw [df_6_0, df_5_1, df_4_2, df_3_3, df_2_4, df_1_5, df_0_6]
  apply MvPolynomial.funext
  intro x
  simp only [fpoly, map_add, map_mul, map_pow, eval_C, eval_X, map_ofNat,
    map_neg, map_one, map_zero]
  simp only [sixthScalar, f0, f2, f4, f6]
  ring_nf
  simp only [gp_sq']
  ring

set_option maxHeartbeats 2000000 in
-- Normalize the finite derivative products and reduce coefficients using the golden-ratio relation.
theorem ico_transvectant_twelve : transvectantC 12 fpoly fpoly = MvPolynomial.C twelfthScalar := by
  simp only [transvectantC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [Nat.choose]
  rw [df_12_0, df_11_1, df_10_2, df_9_3, df_8_4, df_7_5, df_6_6,
    df_5_7, df_4_8, df_3_9, df_2_10, df_1_11, df_0_12]
  apply MvPolynomial.funext
  intro x
  simp only [map_add, map_mul, map_pow, eval_C, eval_X, map_ofNat, map_neg, map_one, map_zero]
  simp only [twelfthScalar, f0, f2, f4, f6]
  ring_nf
  simp only [gp_sq']
  ring

theorem sixthScalar_ne_zero : sixthScalar ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp [sixthScalar] at hr
  linarith [gp_re_pos]

theorem twelfthScalar_ne_zero : twelfthScalar ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp [twelfthScalar] at hr
  linarith [gp_re_pos]

end VOA.Classification.COne.OrbIcoS
