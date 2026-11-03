/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6JacA
import VOA.AffineGeneral.E6JacB
import VOA.AffineGeneral.E6JacC
import VOA.AffineGeneral.E6JacD
import VOA.AffineGeneral.E6JacE
import VOA.AffineGeneral.E6JacF
import VOA.AffineGeneral.E6JacG
import VOA.AffineGeneral.E6JacH
import VOA.AffineGeneral.E6JacI
import VOA.AffineGeneral.E6JacJ
import VOA.AffineGeneral.E6JacK
import VOA.AffineGeneral.E6JacL
import VOA.AffineGeneral.E6JacM
import VOA.AffineGeneral.E6JacN
import VOA.AffineGeneral.E6JacO
import VOA.AffineGeneral.E6JacP
import VOA.AffineGeneral.E6JacQ
import VOA.AffineGeneral.E6JacR
import VOA.AffineGeneral.E6JacS
import VOA.AffineGeneral.E6JacT
import VOA.AffineGeneral.E6JacU
import VOA.AffineGeneral.E6JacV
import VOA.AffineGeneral.E6JacW
import VOA.AffineGeneral.E6JacX
import VOA.AffineGeneral.E6JacY
import VOA.AffineGeneral.E6JacZ
import VOA.AffineGeneral.E6JacZA
import VOA.AffineGeneral.E6JacZB
import VOA.AffineGeneral.E6JacZC
import VOA.AffineGeneral.E6Bound0
import VOA.AffineGeneral.E6Anti0
import VOA.AffineGeneral.E6Bound1
import VOA.AffineGeneral.E6Anti1
import VOA.AffineGeneral.E6Bound2
import VOA.AffineGeneral.E6Anti2
import VOA.AffineGeneral.E6Bound3
import VOA.AffineGeneral.E6Anti3
import VOA.AffineGeneral.E6RootsA
import VOA.AffineGeneral.E6Hbe0
import VOA.AffineGeneral.E6Hbe1
import VOA.AffineGeneral.E6Hbe2
import VOA.AffineGeneral.E6Hhb0
import VOA.AffineGeneral.E6Sep0
import VOA.AffineGeneral.E6Symm0
import VOA.AffineGeneral.E6Hhb1
import VOA.AffineGeneral.E6Sep1
import VOA.AffineGeneral.E6Symm1
import VOA.AffineGeneral.E6Hhb2
import VOA.AffineGeneral.E6Sep2
import VOA.AffineGeneral.E6Symm2
import VOA.AffineGeneral.DeligneInstance
import VOA.AffineGeneral.Simple

set_option linter.style.longLine false

/-!
# The simple Lie algebra `𝔢₆`

`e6Lie := SCLie.Alg 78 e6T e6Checks`, the structure-constant algebra of `E6Table` (basis of the Chevalley basis of `casimir_cert/cert_E6.json` (Frenkel–Kac signs)).
Lean re-checks antisymmetry (`E6Table`), cyclic Jacobi on sorted basis triples (`E6Jac*`, assembled by
`jac_of_sorted`) and the root tables (`e6RootChecks`), all by kernel reduction in small declarations.

* `e6Lie_isSimple`, `finrank_e6Lie : finrank ℂ e6Lie = 78`;
* `e6_killing`, `e6_standard`: Killing(hθ, hθ) = 48 = 4h∨ on a long coroot, so `Killing/24` is the
  standard normalization (long roots of length `2`).  Here `hθ = hbV θ` is minus the standard
  coroot (`e6_coroot`); the value is quadratic in it;
* `e6Data'`, `L_{-3}(𝔢₆)`, `e6_currentJetSurjectivity`, `e6_classicallyFree_of_two_inputs`.
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_bound : boundOK e6T 78 = true :=
  boundOK_of_chunks _ _ fun i hi => by
    rcases (show (0 ≤ i ∧ i < 19) ∨ (19 ≤ i ∧ i < 39) ∨ (39 ≤ i ∧ i < 58) ∨ (58 ≤ i ∧ i < 78) by omega) with h | h | h | h
    · exact ⟨0, 19, h.1, h.2, e6_bound0⟩
    · exact ⟨19, 39, h.1, h.2, e6_bound1⟩
    · exact ⟨39, 58, h.1, h.2, e6_bound2⟩
    · exact ⟨58, 78, h.1, h.2, e6_bound3⟩

theorem e6_anti : antiOK e6T 78 = true :=
  antiOK_of_chunks _ _ fun i hi => by
    rcases (show (0 ≤ i ∧ i < 19) ∨ (19 ≤ i ∧ i < 39) ∨ (39 ≤ i ∧ i < 58) ∨ (58 ≤ i ∧ i < 78) by omega) with h | h | h | h
    · exact ⟨0, 19, h.1, h.2, e6_anti0⟩
    · exact ⟨19, 39, h.1, h.2, e6_anti1⟩
    · exact ⟨39, 58, h.1, h.2, e6_anti2⟩
    · exact ⟨58, 78, h.1, h.2, e6_anti3⟩

theorem e6Row_0 (a j l : Fin 78) (ha : a.val = 0) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_0_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_0_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_0_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_0_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_0_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_0_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_1 (a j l : Fin 78) (ha : a.val = 1) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_1_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_1_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_1_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_1_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_1_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_1_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_2 (a j l : Fin 78) (ha : a.val = 2) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_2_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_2_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_2_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_2_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_2_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_2_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_3 (a j l : Fin 78) (ha : a.val = 3) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_3_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_3_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_3_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_3_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_3_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_3_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_4 (a j l : Fin 78) (ha : a.val = 4) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_4_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_4_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_4_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_4_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_4_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_4_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_5 (a j l : Fin 78) (ha : a.val = 5) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_5_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_5_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_5_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_5_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_5_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_5_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_6 (a j l : Fin 78) (ha : a.val = 6) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_6_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_6_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_6_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_6_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_6_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_6_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_7 (a j l : Fin 78) (ha : a.val = 7) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_7_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_7_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_7_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_7_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_7_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_7_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_8 (a j l : Fin 78) (ha : a.val = 8) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_8_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_8_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_8_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_8_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_8_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_8_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_9 (a j l : Fin 78) (ha : a.val = 9) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_9_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_9_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_9_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_9_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_9_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_9_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_10 (a j l : Fin 78) (ha : a.val = 10) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_10_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_10_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_10_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_10_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_10_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_10_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_11 (a j l : Fin 78) (ha : a.val = 11) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) ∨ (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_11_0 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_11_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_11_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_11_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_11_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_11_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_12 (a j l : Fin 78) (ha : a.val = 12) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_12_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_12_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_12_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_12_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_12_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_13 (a j l : Fin 78) (ha : a.val = 13) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_13_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_13_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_13_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_13_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_13_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_14 (a j l : Fin 78) (ha : a.val = 14) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_14_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_14_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_14_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_14_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_14_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_15 (a j l : Fin 78) (ha : a.val = 15) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_15_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_15_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_15_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_15_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_15_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_16 (a j l : Fin 78) (ha : a.val = 16) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_16_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_16_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_16_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_16_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_16_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_17 (a j l : Fin 78) (ha : a.val = 17) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_17_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_17_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_17_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_17_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_17_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_18 (a j l : Fin 78) (ha : a.val = 18) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_18_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_18_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_18_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_18_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_18_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_19 (a j l : Fin 78) (ha : a.val = 19) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_19_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_19_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_19_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_19_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_19_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_20 (a j l : Fin 78) (ha : a.val = 20) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_20_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_20_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_20_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_20_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_20_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_21 (a j l : Fin 78) (ha : a.val = 21) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_21_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_21_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_21_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_21_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_21_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_22 (a j l : Fin 78) (ha : a.val = 22) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_22_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_22_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_22_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_22_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_22_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_23 (a j l : Fin 78) (ha : a.val = 23) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_23_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_23_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_23_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_23_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_23_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_24 (a j l : Fin 78) (ha : a.val = 24) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (13 ≤ j.val ∧ j.val < 26) ∨ (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h | h
  · exact cycK_of_piece e6_bound e6J_24_1 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_24_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_24_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_24_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_24_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_25 (a j l : Fin 78) (ha : a.val = 25) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_25_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_25_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_25_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_25_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_26 (a j l : Fin 78) (ha : a.val = 26) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_26_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_26_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_26_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_26_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_27 (a j l : Fin 78) (ha : a.val = 27) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_27_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_27_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_27_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_27_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_28 (a j l : Fin 78) (ha : a.val = 28) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_28_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_28_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_28_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_28_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_29 (a j l : Fin 78) (ha : a.val = 29) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_29_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_29_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_29_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_29_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_30 (a j l : Fin 78) (ha : a.val = 30) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_30_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_30_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_30_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_30_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_31 (a j l : Fin 78) (ha : a.val = 31) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_31_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_31_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_31_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_31_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_32 (a j l : Fin 78) (ha : a.val = 32) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_32_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_32_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_32_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_32_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_33 (a j l : Fin 78) (ha : a.val = 33) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_33_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_33_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_33_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_33_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_34 (a j l : Fin 78) (ha : a.val = 34) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_34_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_34_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_34_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_34_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_35 (a j l : Fin 78) (ha : a.val = 35) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_35_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_35_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_35_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_35_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_36 (a j l : Fin 78) (ha : a.val = 36) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_36_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_36_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_36_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_36_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_37 (a j l : Fin 78) (ha : a.val = 37) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (26 ≤ j.val ∧ j.val < 39) ∨ (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h | h
  · exact cycK_of_piece e6_bound e6J_37_2 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_37_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_37_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_37_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_38 (a j l : Fin 78) (ha : a.val = 38) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_38_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_38_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_38_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_39 (a j l : Fin 78) (ha : a.val = 39) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_39_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_39_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_39_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_40 (a j l : Fin 78) (ha : a.val = 40) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_40_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_40_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_40_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_41 (a j l : Fin 78) (ha : a.val = 41) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_41_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_41_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_41_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_42 (a j l : Fin 78) (ha : a.val = 42) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_42_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_42_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_42_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_43 (a j l : Fin 78) (ha : a.val = 43) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_43_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_43_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_43_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_44 (a j l : Fin 78) (ha : a.val = 44) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_44_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_44_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_44_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_45 (a j l : Fin 78) (ha : a.val = 45) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_45_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_45_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_45_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_46 (a j l : Fin 78) (ha : a.val = 46) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_46_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_46_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_46_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_47 (a j l : Fin 78) (ha : a.val = 47) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_47_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_47_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_47_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_48 (a j l : Fin 78) (ha : a.val = 48) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_48_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_48_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_48_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_49 (a j l : Fin 78) (ha : a.val = 49) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_49_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_49_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_49_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_50 (a j l : Fin 78) (ha : a.val = 50) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (39 ≤ j.val ∧ j.val < 52) ∨ (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h | h
  · exact cycK_of_piece e6_bound e6J_50_3 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_50_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_50_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_51 (a j l : Fin 78) (ha : a.val = 51) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_51_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_51_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_52 (a j l : Fin 78) (ha : a.val = 52) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_52_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_52_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_53 (a j l : Fin 78) (ha : a.val = 53) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_53_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_53_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_54 (a j l : Fin 78) (ha : a.val = 54) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_54_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_54_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_55 (a j l : Fin 78) (ha : a.val = 55) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_55_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_55_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_56 (a j l : Fin 78) (ha : a.val = 56) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_56_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_56_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_57 (a j l : Fin 78) (ha : a.val = 57) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_57_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_57_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_58 (a j l : Fin 78) (ha : a.val = 58) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_58_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_58_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_59 (a j l : Fin 78) (ha : a.val = 59) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_59_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_59_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_60 (a j l : Fin 78) (ha : a.val = 60) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_60_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_60_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_61 (a j l : Fin 78) (ha : a.val = 61) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_61_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_61_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_62 (a j l : Fin 78) (ha : a.val = 62) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_62_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_62_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_63 (a j l : Fin 78) (ha : a.val = 63) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (52 ≤ j.val ∧ j.val < 65) ∨ (65 ≤ j.val ∧ j.val < 78) by omega) with h | h
  · exact cycK_of_piece e6_bound e6J_63_4 a j l ha h.1 h.2 hij hjl n
  · exact cycK_of_piece e6_bound e6J_63_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_64 (a j l : Fin 78) (ha : a.val = 64) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_64_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_65 (a j l : Fin 78) (ha : a.val = 65) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_65_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_66 (a j l : Fin 78) (ha : a.val = 66) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_66_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_67 (a j l : Fin 78) (ha : a.val = 67) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_67_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_68 (a j l : Fin 78) (ha : a.val = 68) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_68_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_69 (a j l : Fin 78) (ha : a.val = 69) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_69_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_70 (a j l : Fin 78) (ha : a.val = 70) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_70_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_71 (a j l : Fin 78) (ha : a.val = 71) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_71_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_72 (a j l : Fin 78) (ha : a.val = 72) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_72_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_73 (a j l : Fin 78) (ha : a.val = 73) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_73_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_74 (a j l : Fin 78) (ha : a.val = 74) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_74_5 a j l ha h.1 h.2 hij hjl n

theorem e6Row_75 (a j l : Fin 78) (ha : a.val = 75) (hij : a < j) (hjl : j < l) (n : Fin 78) :
    cycK e6T 78 a j l n = 0 := by
  have hj : j.val < 78 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (65 ≤ j.val ∧ j.val < 78) by omega) with h
  · exact cycK_of_piece e6_bound e6J_75_5 a j l ha h.1 h.2 hij hjl n


theorem e6_sortedJac (n : Fin 78) (i j l : Fin 78) (hij : i < j) (hjl : j < l) :
    cycK e6T 78 i j l n = 0 := by
  have hl : l.val < 78 := l.2
  have hij' : i.val < j.val := hij
  have hjl' : j.val < l.val := hjl
  have hi : i.val < 76 := by omega
  obtain ⟨iv, hiv⟩ : ∃ iv, iv = i.val := ⟨_, rfl⟩
  rw [← hiv] at hi
  interval_cases iv
  · exact e6Row_0 i j l hiv.symm hij hjl n
  · exact e6Row_1 i j l hiv.symm hij hjl n
  · exact e6Row_2 i j l hiv.symm hij hjl n
  · exact e6Row_3 i j l hiv.symm hij hjl n
  · exact e6Row_4 i j l hiv.symm hij hjl n
  · exact e6Row_5 i j l hiv.symm hij hjl n
  · exact e6Row_6 i j l hiv.symm hij hjl n
  · exact e6Row_7 i j l hiv.symm hij hjl n
  · exact e6Row_8 i j l hiv.symm hij hjl n
  · exact e6Row_9 i j l hiv.symm hij hjl n
  · exact e6Row_10 i j l hiv.symm hij hjl n
  · exact e6Row_11 i j l hiv.symm hij hjl n
  · exact e6Row_12 i j l hiv.symm hij hjl n
  · exact e6Row_13 i j l hiv.symm hij hjl n
  · exact e6Row_14 i j l hiv.symm hij hjl n
  · exact e6Row_15 i j l hiv.symm hij hjl n
  · exact e6Row_16 i j l hiv.symm hij hjl n
  · exact e6Row_17 i j l hiv.symm hij hjl n
  · exact e6Row_18 i j l hiv.symm hij hjl n
  · exact e6Row_19 i j l hiv.symm hij hjl n
  · exact e6Row_20 i j l hiv.symm hij hjl n
  · exact e6Row_21 i j l hiv.symm hij hjl n
  · exact e6Row_22 i j l hiv.symm hij hjl n
  · exact e6Row_23 i j l hiv.symm hij hjl n
  · exact e6Row_24 i j l hiv.symm hij hjl n
  · exact e6Row_25 i j l hiv.symm hij hjl n
  · exact e6Row_26 i j l hiv.symm hij hjl n
  · exact e6Row_27 i j l hiv.symm hij hjl n
  · exact e6Row_28 i j l hiv.symm hij hjl n
  · exact e6Row_29 i j l hiv.symm hij hjl n
  · exact e6Row_30 i j l hiv.symm hij hjl n
  · exact e6Row_31 i j l hiv.symm hij hjl n
  · exact e6Row_32 i j l hiv.symm hij hjl n
  · exact e6Row_33 i j l hiv.symm hij hjl n
  · exact e6Row_34 i j l hiv.symm hij hjl n
  · exact e6Row_35 i j l hiv.symm hij hjl n
  · exact e6Row_36 i j l hiv.symm hij hjl n
  · exact e6Row_37 i j l hiv.symm hij hjl n
  · exact e6Row_38 i j l hiv.symm hij hjl n
  · exact e6Row_39 i j l hiv.symm hij hjl n
  · exact e6Row_40 i j l hiv.symm hij hjl n
  · exact e6Row_41 i j l hiv.symm hij hjl n
  · exact e6Row_42 i j l hiv.symm hij hjl n
  · exact e6Row_43 i j l hiv.symm hij hjl n
  · exact e6Row_44 i j l hiv.symm hij hjl n
  · exact e6Row_45 i j l hiv.symm hij hjl n
  · exact e6Row_46 i j l hiv.symm hij hjl n
  · exact e6Row_47 i j l hiv.symm hij hjl n
  · exact e6Row_48 i j l hiv.symm hij hjl n
  · exact e6Row_49 i j l hiv.symm hij hjl n
  · exact e6Row_50 i j l hiv.symm hij hjl n
  · exact e6Row_51 i j l hiv.symm hij hjl n
  · exact e6Row_52 i j l hiv.symm hij hjl n
  · exact e6Row_53 i j l hiv.symm hij hjl n
  · exact e6Row_54 i j l hiv.symm hij hjl n
  · exact e6Row_55 i j l hiv.symm hij hjl n
  · exact e6Row_56 i j l hiv.symm hij hjl n
  · exact e6Row_57 i j l hiv.symm hij hjl n
  · exact e6Row_58 i j l hiv.symm hij hjl n
  · exact e6Row_59 i j l hiv.symm hij hjl n
  · exact e6Row_60 i j l hiv.symm hij hjl n
  · exact e6Row_61 i j l hiv.symm hij hjl n
  · exact e6Row_62 i j l hiv.symm hij hjl n
  · exact e6Row_63 i j l hiv.symm hij hjl n
  · exact e6Row_64 i j l hiv.symm hij hjl n
  · exact e6Row_65 i j l hiv.symm hij hjl n
  · exact e6Row_66 i j l hiv.symm hij hjl n
  · exact e6Row_67 i j l hiv.symm hij hjl n
  · exact e6Row_68 i j l hiv.symm hij hjl n
  · exact e6Row_69 i j l hiv.symm hij hjl n
  · exact e6Row_70 i j l hiv.symm hij hjl n
  · exact e6Row_71 i j l hiv.symm hij hjl n
  · exact e6Row_72 i j l hiv.symm hij hjl n
  · exact e6Row_73 i j l hiv.symm hij hjl n
  · exact e6Row_74 i j l hiv.symm hij hjl n
  · exact e6Row_75 i j l hiv.symm hij hjl n

theorem e6Checks : Checks 78 e6T :=
  ⟨e6_bound, e6_anti, fun i j l n => jac_of_sorted e6_anti (fun a b c => e6_sortedJac n a b c) i j l⟩

theorem e6RC_hbe : ∀ α β, zeroL (brL e6T (hL e6T e6Data α) (eL e6Data β) ++ scale (-(e6Data.pairT α β)) (eL e6Data β)) = true := by
  intro α β
  have hα : α.val < 72 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 24) ∨ (24 ≤ α.val ∧ α.val < 48) ∨ (48 ≤ α.val ∧ α.val < 72) by omega) with h | h | h
  · exact e6RC_hbe0 α h.1 h.2 β
  · exact e6RC_hbe1 α h.1 h.2 β
  · exact e6RC_hbe2 α h.1 h.2 β

theorem e6RC_hhb : ∀ α β, zeroL (brL e6T (hL e6T e6Data α) (hL e6T e6Data β)) = true := by
  intro α β
  have hα : α.val < 72 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 24) ∨ (24 ≤ α.val ∧ α.val < 48) ∨ (48 ≤ α.val ∧ α.val < 72) by omega) with h | h | h
  · exact e6RC_hhb0 α h.1 h.2 β
  · exact e6RC_hhb1 α h.1 h.2 β
  · exact e6RC_hhb2 α h.1 h.2 β

theorem e6RC_sep : ∀ α β, α ≠ β → ∃ γ, e6Data.pairT γ α ≠ e6Data.pairT γ β := by
  intro α β
  have hα : α.val < 72 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 24) ∨ (24 ≤ α.val ∧ α.val < 48) ∨ (48 ≤ α.val ∧ α.val < 72) by omega) with h | h | h
  · exact e6RC_sep0 α h.1 h.2 β
  · exact e6RC_sep1 α h.1 h.2 β
  · exact e6RC_sep2 α h.1 h.2 β

theorem e6RC_symm : ∀ α β, e6Data.pairT α β ≠ 0 → e6Data.pairT β α ≠ 0 := by
  intro α β
  have hα : α.val < 72 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 24) ∨ (24 ≤ α.val ∧ α.val < 48) ∨ (48 ≤ α.val ∧ α.val < 72) by omega) with h | h | h
  · exact e6RC_symm0 α h.1 h.2 β
  · exact e6RC_symm1 α h.1 h.2 β
  · exact e6RC_symm2 α h.1 h.2 β

theorem e6RootChecks : RootChecks e6T e6Data :=
  ⟨e6RC_inRange, e6RC_hbe, e6RC_hhb, e6RC_diag, e6RC_sep, e6RC_symm, e6RC_M, e6RC_Q, e6RC_conn,
    e6RC_span⟩

/-- **`𝔢₆`.** -/
abbrev e6Lie : Type := Alg 78 e6T e6Checks

instance e6Lie_isSimple : LieAlgebra.IsSimple ℂ e6Lie :=
  haveI : Nonempty (Fin e6Data.nr) := ⟨⟨0, by decide⟩⟩
  isSimple_of_tables e6Checks e6Data e6RootChecks

theorem finrank_e6Lie : Module.finrank ℂ e6Lie = 78 := finrank_alg e6Checks

/-- A long root. -/
def e6Long : Fin e6Data.nr := ⟨6, by decide⟩

theorem e6_coroot : ⁅hbV e6Checks e6Data e6Long, eV e6Checks e6Data e6Long⁆
    = (-2 : ℂ) • eV e6Checks e6Data e6Long := by
  rw [hbV_eq, eV_eq, lie_vec _ (e6RootChecks.inRange_h _) (eL_inRange _ _)]
  exact_mod_cast vec_eq_of_zeroL e6Checks (-2) (by decide +kernel)

theorem e6_killing : killingForm ℂ e6Lie (hbV e6Checks e6Data e6Long)
    (hbV e6Checks e6Data e6Long) = 48 := by
  rw [hbV_eq, killing_vec _ _ (e6RootChecks.inRange_h _) (by decide +kernel)]
  have h : (∑ k : Fin 78, coef (brL e6T (hL e6T e6Data e6Long)
      (brL e6T (hL e6T e6Data e6Long) [((k : ℕ), 1)])) k) = 48 := by decide +kernel
  exact_mod_cast h

/-- **`Killing/24` is the standard normalization on `𝔢₆`**: long roots have length `2`. -/
theorem e6_standard : ((2 * 12 : ℂ)⁻¹ • killingForm ℂ e6Lie) (hbV e6Checks e6Data e6Long)
    (hbV e6Checks e6Data e6Long) = 2 := by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, e6_killing]
  norm_num

end VOA.AffineGeneral.SCLie

namespace VOA.AffineGeneral.E6Deligne

open VOA.AffineGeneral.SCLie VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-- Lie data for `𝔢₆` (form `Killing/24`, `h = 12`), indexed by `Fin 78`. -/
def e6Data' : LieData ((2 * 12 : ℂ)⁻¹ • killingForm ℂ e6Lie)
    (Fin HigherRankDeligneCase.E6.currentDimension) :=
  (standardData e6Lie 12 (by norm_num)).reindex (finCongr finrank_e6Lie)

theorem e6Data'_h : e6Data'.h = 12 := by
  rw [e6Data', LieData.reindex_h, standardData_h]

theorem e6_level_ne : (-3 : ℂ) + e6Data'.h ≠ 0 := by
  rw [e6Data'_h]; norm_num

/-- `L_{-3}(𝔢₆)`. -/
abbrev e6SimpleVOA := simpleVOA e6Data' (-3) e6_level_ne

theorem e6_currentJetSurjectivity :
    CurrentJetSurjectivity .E6 e6SimpleVOA (Deligne.presentation .E6 e6Data' (-3) e6_level_ne) :=
  Deligne.currentJetSurjectivity .E6 e6Data' (-3) e6_level_ne

/-- **The Deligne case `E6`, conditional on the two remaining packages.** -/
theorem e6_classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .E6 e6SimpleVOA
      (Deligne.presentation .E6 e6Data' (-3) e6_level_ne) Carrier)
    (hchar : OrdinaryCarrierCharacter e6SimpleVOA Carrier) :
    CaseClassicallyFree .E6 e6SimpleVOA (Deligne.presentation .E6 e6Data' (-3) e6_level_ne) :=
  Deligne.classicallyFree_of_two_inputs .E6 e6Data' (-3) e6_level_ne Carrier hgeom hchar

end

end VOA.AffineGeneral.E6Deligne
