/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4JacA
import VOA.AffineGeneral.F4JacB
import VOA.AffineGeneral.F4JacC
import VOA.AffineGeneral.F4JacD
import VOA.AffineGeneral.F4JacE
import VOA.AffineGeneral.F4JacF
import VOA.AffineGeneral.F4JacG
import VOA.AffineGeneral.F4JacH
import VOA.AffineGeneral.F4JacI
import VOA.AffineGeneral.F4JacJ
import VOA.AffineGeneral.F4Bound0
import VOA.AffineGeneral.F4Anti0
import VOA.AffineGeneral.F4Bound1
import VOA.AffineGeneral.F4Anti1
import VOA.AffineGeneral.F4Bound2
import VOA.AffineGeneral.F4Anti2
import VOA.AffineGeneral.F4Bound3
import VOA.AffineGeneral.F4Anti3
import VOA.AffineGeneral.F4RootsA
import VOA.AffineGeneral.F4Hbe0
import VOA.AffineGeneral.F4Hbe1
import VOA.AffineGeneral.F4Hbe2
import VOA.AffineGeneral.F4Hhb0
import VOA.AffineGeneral.F4Sep0
import VOA.AffineGeneral.F4Symm0
import VOA.AffineGeneral.F4Hhb1
import VOA.AffineGeneral.F4Sep1
import VOA.AffineGeneral.F4Symm1
import VOA.AffineGeneral.F4Hhb2
import VOA.AffineGeneral.F4Sep2
import VOA.AffineGeneral.F4Symm2
import VOA.AffineGeneral.DeligneInstance
import VOA.AffineGeneral.Simple

set_option linter.style.longLine false

/-!
# The simple Lie algebra `𝔣₄`

`f4Lie := SCLie.Alg 52 f4T f4Checks`, the structure-constant algebra of `F4Table` (basis of folding a simply-laced algebra by a diagram automorphism (`aff_fold.py`)).
Lean re-checks antisymmetry (`F4Table`), cyclic Jacobi on sorted basis triples (`F4Jac*`, assembled by
`jac_of_sorted`) and the root tables (`f4RootChecks`), all by kernel reduction in small declarations.

* `f4Lie_isSimple`, `finrank_f4Lie : finrank ℂ f4Lie = 52`;
* `f4_killing`, `f4_standard`: Killing(hθ, hθ) = 36 = 4h∨ on a long coroot, so `Killing/18` is the
  standard normalization (long roots of length `2`).  Here `hθ = hbV θ` is minus the standard
  coroot (`f4_coroot`); the value is quadratic in it;
* `f4Data'`, `L_{-5/2}(𝔣₄)`, `f4_currentJetSurjectivity`, `f4_classicallyFree_of_two_inputs`.
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4_bound : boundOK f4T 52 = true :=
  boundOK_of_chunks _ _ fun i hi => by
    rcases (show (0 ≤ i ∧ i < 13) ∨ (13 ≤ i ∧ i < 26) ∨ (26 ≤ i ∧ i < 39) ∨ (39 ≤ i ∧ i < 52) by omega) with h | h | h | h
    · exact ⟨0, 13, h.1, h.2, f4_bound0⟩
    · exact ⟨13, 26, h.1, h.2, f4_bound1⟩
    · exact ⟨26, 39, h.1, h.2, f4_bound2⟩
    · exact ⟨39, 52, h.1, h.2, f4_bound3⟩

theorem f4_anti : antiOK f4T 52 = true :=
  antiOK_of_chunks _ _ fun i hi => by
    rcases (show (0 ≤ i ∧ i < 13) ∨ (13 ≤ i ∧ i < 26) ∨ (26 ≤ i ∧ i < 39) ∨ (39 ≤ i ∧ i < 52) by omega) with h | h | h | h
    · exact ⟨0, 13, h.1, h.2, f4_anti0⟩
    · exact ⟨13, 26, h.1, h.2, f4_anti1⟩
    · exact ⟨26, 39, h.1, h.2, f4_anti2⟩
    · exact ⟨39, 52, h.1, h.2, f4_anti3⟩

theorem f4Row_0 (a j l : Fin 52) (ha : a.val = 0) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_0_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_0_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_0_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_0_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_1 (a j l : Fin 52) (ha : a.val = 1) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_1_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_1_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_1_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_1_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_2 (a j l : Fin 52) (ha : a.val = 2) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_2_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_2_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_2_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_2_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_3 (a j l : Fin 52) (ha : a.val = 3) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_3_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_3_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_3_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_3_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_4 (a j l : Fin 52) (ha : a.val = 4) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_4_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_4_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_4_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_4_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_5 (a j l : Fin 52) (ha : a.val = 5) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_5_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_5_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_5_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_5_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_6 (a j l : Fin 52) (ha : a.val = 6) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_6_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_6_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_6_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_6_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_7 (a j l : Fin 52) (ha : a.val = 7) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_7_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_7_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_7_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_7_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_8 (a j l : Fin 52) (ha : a.val = 8) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_8_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_8_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_8_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_8_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_9 (a j l : Fin 52) (ha : a.val = 9) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_9_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_9_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_9_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_9_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_10 (a j l : Fin 52) (ha : a.val = 10) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_10_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_10_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_10_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_10_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_11 (a j l : Fin 52) (ha : a.val = 11) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h | h
  · exact cycK_of_piece f4_bound f4J_11_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_11_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_11_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_11_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_12 (a j l : Fin 52) (ha : a.val = 12) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_12_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_12_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_12_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_13 (a j l : Fin 52) (ha : a.val = 13) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_13_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_13_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_13_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_14 (a j l : Fin 52) (ha : a.val = 14) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_14_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_14_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_14_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_15 (a j l : Fin 52) (ha : a.val = 15) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_15_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_15_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_15_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_16 (a j l : Fin 52) (ha : a.val = 16) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_16_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_16_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_16_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_17 (a j l : Fin 52) (ha : a.val = 17) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_17_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_17_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_17_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_18 (a j l : Fin 52) (ha : a.val = 18) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_18_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_18_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_18_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_19 (a j l : Fin 52) (ha : a.val = 19) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_19_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_19_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_19_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_20 (a j l : Fin 52) (ha : a.val = 20) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_20_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_20_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_20_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_21 (a j l : Fin 52) (ha : a.val = 21) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_21_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_21_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_21_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_22 (a j l : Fin 52) (ha : a.val = 22) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_22_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_22_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_22_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_23 (a j l : Fin 52) (ha : a.val = 23) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_23_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_23_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_23_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_24 (a j l : Fin 52) (ha : a.val = 24) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h | h
  · exact cycK_of_piece f4_bound f4J_24_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_24_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_24_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_25 (a j l : Fin 52) (ha : a.val = 25) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_25_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_25_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_26 (a j l : Fin 52) (ha : a.val = 26) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_26_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_26_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_27 (a j l : Fin 52) (ha : a.val = 27) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_27_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_27_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_28 (a j l : Fin 52) (ha : a.val = 28) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_28_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_28_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_29 (a j l : Fin 52) (ha : a.val = 29) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_29_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_29_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_30 (a j l : Fin 52) (ha : a.val = 30) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_30_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_30_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_31 (a j l : Fin 52) (ha : a.val = 31) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_31_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_31_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_32 (a j l : Fin 52) (ha : a.val = 32) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_32_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_32_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_33 (a j l : Fin 52) (ha : a.val = 33) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_33_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_33_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_34 (a j l : Fin 52) (ha : a.val = 34) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_34_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_34_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_35 (a j l : Fin 52) (ha : a.val = 35) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_35_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_35_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_36 (a j l : Fin 52) (ha : a.val = 36) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_36_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_36_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_37 (a j l : Fin 52) (ha : a.val = 37) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) by omega) with h | h
  · exact cycK_of_piece f4_bound f4J_37_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece f4_bound f4J_37_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_38 (a j l : Fin 52) (ha : a.val = 38) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_38_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_39 (a j l : Fin 52) (ha : a.val = 39) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_39_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_40 (a j l : Fin 52) (ha : a.val = 40) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_40_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_41 (a j l : Fin 52) (ha : a.val = 41) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_41_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_42 (a j l : Fin 52) (ha : a.val = 42) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_42_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_43 (a j l : Fin 52) (ha : a.val = 43) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_43_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_44 (a j l : Fin 52) (ha : a.val = 44) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_44_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_45 (a j l : Fin 52) (ha : a.val = 45) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_45_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_46 (a j l : Fin 52) (ha : a.val = 46) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_46_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_47 (a j l : Fin 52) (ha : a.val = 47) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_47_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_48 (a j l : Fin 52) (ha : a.val = 48) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_48_3 a j l ha h.1 h.2 hij hjl n

theorem f4Row_49 (a j l : Fin 52) (ha : a.val = 49) (hij : a < j) (hjl : j < l) (n : Fin 52) :
    cycK f4T 52 a j l n = 0 := by
  have hj : j.val < 52 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) by omega) with h
  · exact cycK_of_piece f4_bound f4J_49_3 a j l ha h.1 h.2 hij hjl n


theorem f4_sortedJac (n : Fin 52) (i j l : Fin 52) (hij : i < j) (hjl : j < l) :
    cycK f4T 52 i j l n = 0 := by
  have hl : l.val < 52 := l.2
  have hij' : i.val < j.val := hij
  have hjl' : j.val < l.val := hjl
  have hi : i.val < 50 := by omega
  obtain ⟨iv, hiv⟩ : ∃ iv, iv = i.val := ⟨_, rfl⟩
  rw [← hiv] at hi
  interval_cases iv
  · exact f4Row_0 i j l hiv.symm hij hjl n
  · exact f4Row_1 i j l hiv.symm hij hjl n
  · exact f4Row_2 i j l hiv.symm hij hjl n
  · exact f4Row_3 i j l hiv.symm hij hjl n
  · exact f4Row_4 i j l hiv.symm hij hjl n
  · exact f4Row_5 i j l hiv.symm hij hjl n
  · exact f4Row_6 i j l hiv.symm hij hjl n
  · exact f4Row_7 i j l hiv.symm hij hjl n
  · exact f4Row_8 i j l hiv.symm hij hjl n
  · exact f4Row_9 i j l hiv.symm hij hjl n
  · exact f4Row_10 i j l hiv.symm hij hjl n
  · exact f4Row_11 i j l hiv.symm hij hjl n
  · exact f4Row_12 i j l hiv.symm hij hjl n
  · exact f4Row_13 i j l hiv.symm hij hjl n
  · exact f4Row_14 i j l hiv.symm hij hjl n
  · exact f4Row_15 i j l hiv.symm hij hjl n
  · exact f4Row_16 i j l hiv.symm hij hjl n
  · exact f4Row_17 i j l hiv.symm hij hjl n
  · exact f4Row_18 i j l hiv.symm hij hjl n
  · exact f4Row_19 i j l hiv.symm hij hjl n
  · exact f4Row_20 i j l hiv.symm hij hjl n
  · exact f4Row_21 i j l hiv.symm hij hjl n
  · exact f4Row_22 i j l hiv.symm hij hjl n
  · exact f4Row_23 i j l hiv.symm hij hjl n
  · exact f4Row_24 i j l hiv.symm hij hjl n
  · exact f4Row_25 i j l hiv.symm hij hjl n
  · exact f4Row_26 i j l hiv.symm hij hjl n
  · exact f4Row_27 i j l hiv.symm hij hjl n
  · exact f4Row_28 i j l hiv.symm hij hjl n
  · exact f4Row_29 i j l hiv.symm hij hjl n
  · exact f4Row_30 i j l hiv.symm hij hjl n
  · exact f4Row_31 i j l hiv.symm hij hjl n
  · exact f4Row_32 i j l hiv.symm hij hjl n
  · exact f4Row_33 i j l hiv.symm hij hjl n
  · exact f4Row_34 i j l hiv.symm hij hjl n
  · exact f4Row_35 i j l hiv.symm hij hjl n
  · exact f4Row_36 i j l hiv.symm hij hjl n
  · exact f4Row_37 i j l hiv.symm hij hjl n
  · exact f4Row_38 i j l hiv.symm hij hjl n
  · exact f4Row_39 i j l hiv.symm hij hjl n
  · exact f4Row_40 i j l hiv.symm hij hjl n
  · exact f4Row_41 i j l hiv.symm hij hjl n
  · exact f4Row_42 i j l hiv.symm hij hjl n
  · exact f4Row_43 i j l hiv.symm hij hjl n
  · exact f4Row_44 i j l hiv.symm hij hjl n
  · exact f4Row_45 i j l hiv.symm hij hjl n
  · exact f4Row_46 i j l hiv.symm hij hjl n
  · exact f4Row_47 i j l hiv.symm hij hjl n
  · exact f4Row_48 i j l hiv.symm hij hjl n
  · exact f4Row_49 i j l hiv.symm hij hjl n

theorem f4Checks : Checks 52 f4T :=
  ⟨f4_bound, f4_anti, fun i j l n => jac_of_sorted f4_anti (fun a b c => f4_sortedJac n a b c) i j l⟩

theorem f4RC_hbe : ∀ α β, zeroL (brL f4T (hL f4T f4Data α) (eL f4Data β) ++ scale (-(f4Data.pairT α β)) (eL f4Data β)) = true := by
  intro α β
  have hα : α.val < 48 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 16) ∨ (16 ≤ α.val ∧ α.val < 32) ∨ (32 ≤ α.val ∧ α.val < 48) by omega) with h | h | h
  · exact f4RC_hbe0 α h.1 h.2 β
  · exact f4RC_hbe1 α h.1 h.2 β
  · exact f4RC_hbe2 α h.1 h.2 β

theorem f4RC_hhb : ∀ α β, zeroL (brL f4T (hL f4T f4Data α) (hL f4T f4Data β)) = true := by
  intro α β
  have hα : α.val < 48 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 16) ∨ (16 ≤ α.val ∧ α.val < 32) ∨ (32 ≤ α.val ∧ α.val < 48) by omega) with h | h | h
  · exact f4RC_hhb0 α h.1 h.2 β
  · exact f4RC_hhb1 α h.1 h.2 β
  · exact f4RC_hhb2 α h.1 h.2 β

theorem f4RC_sep : ∀ α β, α ≠ β → ∃ γ, f4Data.pairT γ α ≠ f4Data.pairT γ β := by
  intro α β
  have hα : α.val < 48 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 16) ∨ (16 ≤ α.val ∧ α.val < 32) ∨ (32 ≤ α.val ∧ α.val < 48) by omega) with h | h | h
  · exact f4RC_sep0 α h.1 h.2 β
  · exact f4RC_sep1 α h.1 h.2 β
  · exact f4RC_sep2 α h.1 h.2 β

theorem f4RC_symm : ∀ α β, f4Data.pairT α β ≠ 0 → f4Data.pairT β α ≠ 0 := by
  intro α β
  have hα : α.val < 48 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 16) ∨ (16 ≤ α.val ∧ α.val < 32) ∨ (32 ≤ α.val ∧ α.val < 48) by omega) with h | h | h
  · exact f4RC_symm0 α h.1 h.2 β
  · exact f4RC_symm1 α h.1 h.2 β
  · exact f4RC_symm2 α h.1 h.2 β

theorem f4RootChecks : RootChecks f4T f4Data :=
  ⟨f4RC_inRange, f4RC_hbe, f4RC_hhb, f4RC_diag, f4RC_sep, f4RC_symm, f4RC_M, f4RC_Q, f4RC_conn,
    f4RC_span⟩

/-- **`𝔣₄`.** -/
abbrev f4Lie : Type := Alg 52 f4T f4Checks

instance f4Lie_isSimple : LieAlgebra.IsSimple ℂ f4Lie :=
  haveI : Nonempty (Fin f4Data.nr) := ⟨⟨0, by decide⟩⟩
  isSimple_of_tables f4Checks f4Data f4RootChecks

theorem finrank_f4Lie : Module.finrank ℂ f4Lie = 52 := finrank_alg f4Checks

/-- A long root. -/
def f4Long : Fin f4Data.nr := ⟨2, by decide⟩

theorem f4_coroot : ⁅hbV f4Checks f4Data f4Long, eV f4Checks f4Data f4Long⁆
    = (-2 : ℂ) • eV f4Checks f4Data f4Long := by
  rw [hbV_eq, eV_eq, lie_vec _ (f4RootChecks.inRange_h _) (eL_inRange _ _)]
  exact_mod_cast vec_eq_of_zeroL f4Checks (-2) (by decide +kernel)

theorem f4_killing : killingForm ℂ f4Lie (hbV f4Checks f4Data f4Long)
    (hbV f4Checks f4Data f4Long) = 36 := by
  rw [hbV_eq, killing_vec _ _ (f4RootChecks.inRange_h _) (by decide +kernel)]
  have h : (∑ k : Fin 52, coef (brL f4T (hL f4T f4Data f4Long)
      (brL f4T (hL f4T f4Data f4Long) [((k : ℕ), 1)])) k) = 36 := by decide +kernel
  exact_mod_cast h

/-- **`Killing/18` is the standard normalization on `𝔣₄`**: long roots have length `2`. -/
theorem f4_standard : ((2 * 9 : ℂ)⁻¹ • killingForm ℂ f4Lie) (hbV f4Checks f4Data f4Long)
    (hbV f4Checks f4Data f4Long) = 2 := by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, f4_killing]
  norm_num

end VOA.AffineGeneral.SCLie

namespace VOA.AffineGeneral.F4Deligne

open VOA.AffineGeneral.SCLie VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-- Lie data for `𝔣₄` (form `Killing/18`, `h = 9`), indexed by `Fin 52`. -/
def f4Data' : LieData ((2 * 9 : ℂ)⁻¹ • killingForm ℂ f4Lie)
    (Fin HigherRankDeligneCase.F4.currentDimension) :=
  (standardData f4Lie 9 (by norm_num)).reindex (finCongr finrank_f4Lie)

theorem f4Data'_h : f4Data'.h = 9 := by
  rw [f4Data', LieData.reindex_h, standardData_h]

theorem f4_level_ne : (-5/2 : ℂ) + f4Data'.h ≠ 0 := by
  rw [f4Data'_h]; norm_num

/-- `L_{-5/2}(𝔣₄)`. -/
abbrev f4SimpleVOA := simpleVOA f4Data' (-5/2) f4_level_ne

theorem f4_currentJetSurjectivity :
    CurrentJetSurjectivity .F4 f4SimpleVOA (Deligne.presentation .F4 f4Data' (-5/2) f4_level_ne) :=
  Deligne.currentJetSurjectivity .F4 f4Data' (-5/2) f4_level_ne

/-- **The Deligne case `F4`, conditional on the two remaining packages.** -/
theorem f4_classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .F4 f4SimpleVOA
      (Deligne.presentation .F4 f4Data' (-5/2) f4_level_ne) Carrier)
    (hchar : OrdinaryCarrierCharacter f4SimpleVOA Carrier) :
    CaseClassicallyFree .F4 f4SimpleVOA (Deligne.presentation .F4 f4Data' (-5/2) f4_level_ne) :=
  Deligne.classicallyFree_of_two_inputs .F4 f4Data' (-5/2) f4_level_ne Carrier hgeom hchar

end

end VOA.AffineGeneral.F4Deligne
