/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.G2JacA
import VOA.AffineGeneral.G2Bound0
import VOA.AffineGeneral.G2Anti0
import VOA.AffineGeneral.G2Bound1
import VOA.AffineGeneral.G2Anti1
import VOA.AffineGeneral.G2Bound2
import VOA.AffineGeneral.G2Anti2
import VOA.AffineGeneral.G2Bound3
import VOA.AffineGeneral.G2Anti3
import VOA.AffineGeneral.G2RootsA
import VOA.AffineGeneral.G2Hbe0
import VOA.AffineGeneral.G2Hbe1
import VOA.AffineGeneral.G2Hbe2
import VOA.AffineGeneral.G2Hhb0
import VOA.AffineGeneral.G2Sep0
import VOA.AffineGeneral.G2Symm0
import VOA.AffineGeneral.G2Hhb1
import VOA.AffineGeneral.G2Sep1
import VOA.AffineGeneral.G2Symm1
import VOA.AffineGeneral.G2Hhb2
import VOA.AffineGeneral.G2Sep2
import VOA.AffineGeneral.G2Symm2
import VOA.AffineGeneral.DeligneInstance
import VOA.AffineGeneral.Simple

set_option linter.style.longLine false

/-!
# The simple Lie algebra `𝔤₂`

`g2Lie := SCLie.Alg 14 g2T g2Checks`, the structure-constant algebra of `G2Table` (basis of folding a simply-laced algebra by a diagram automorphism (`aff_fold.py`)).
Lean re-checks antisymmetry (`G2Table`), cyclic Jacobi on sorted basis triples (`G2Jac*`, assembled by
`jac_of_sorted`) and the root tables (`g2RootChecks`), all by kernel reduction in small declarations.

* `g2Lie_isSimple`, `finrank_g2Lie : finrank ℂ g2Lie = 14`;
* `g2_killing`, `g2_standard`: Killing(hθ, hθ) = 16 = 4h∨ on a long coroot, so `Killing/8` is the
  standard normalization (long roots of length `2`).  Here `hθ = hbV θ` is minus the standard
  coroot (`g2_coroot`); the value is quadratic in it;
* `g2Data'`, `L_{-5/3}(𝔤₂)`, `g2_currentJetSurjectivity`, `g2_classicallyFree_of_two_inputs`.
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem g2_bound : boundOK g2T 14 = true :=
  boundOK_of_chunks _ _ fun i hi => by
    rcases (show (0 ≤ i ∧ i < 3) ∨ (3 ≤ i ∧ i < 7) ∨ (7 ≤ i ∧ i < 10) ∨ (10 ≤ i ∧ i < 14) by omega) with h | h | h | h
    · exact ⟨0, 3, h.1, h.2, g2_bound0⟩
    · exact ⟨3, 7, h.1, h.2, g2_bound1⟩
    · exact ⟨7, 10, h.1, h.2, g2_bound2⟩
    · exact ⟨10, 14, h.1, h.2, g2_bound3⟩

theorem g2_anti : antiOK g2T 14 = true :=
  antiOK_of_chunks _ _ fun i hi => by
    rcases (show (0 ≤ i ∧ i < 3) ∨ (3 ≤ i ∧ i < 7) ∨ (7 ≤ i ∧ i < 10) ∨ (10 ≤ i ∧ i < 14) by omega) with h | h | h | h
    · exact ⟨0, 3, h.1, h.2, g2_anti0⟩
    · exact ⟨3, 7, h.1, h.2, g2_anti1⟩
    · exact ⟨7, 10, h.1, h.2, g2_anti2⟩
    · exact ⟨10, 14, h.1, h.2, g2_anti3⟩

theorem g2Row_0 (a j l : Fin 14) (ha : a.val = 0) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_0_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_1 (a j l : Fin 14) (ha : a.val = 1) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_1_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_2 (a j l : Fin 14) (ha : a.val = 2) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_2_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_3 (a j l : Fin 14) (ha : a.val = 3) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_3_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_4 (a j l : Fin 14) (ha : a.val = 4) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_4_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_5 (a j l : Fin 14) (ha : a.val = 5) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_5_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_6 (a j l : Fin 14) (ha : a.val = 6) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_6_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_7 (a j l : Fin 14) (ha : a.val = 7) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_7_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_8 (a j l : Fin 14) (ha : a.val = 8) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_8_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_9 (a j l : Fin 14) (ha : a.val = 9) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_9_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_10 (a j l : Fin 14) (ha : a.val = 10) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_10_0 a j l ha h.1 h.2 hij hjl n

theorem g2Row_11 (a j l : Fin 14) (ha : a.val = 11) (hij : a < j) (hjl : j < l) (n : Fin 14) :
    cycK g2T 14 a j l n = 0 := by
  have hj : j.val < 14 := j.2
  have hij' : a.val < j.val := hij
  rcases (show (0 ≤ j.val ∧ j.val < 13) by omega) with h
  · exact cycK_of_piece g2_bound g2J_11_0 a j l ha h.1 h.2 hij hjl n


theorem g2_sortedJac (n : Fin 14) (i j l : Fin 14) (hij : i < j) (hjl : j < l) :
    cycK g2T 14 i j l n = 0 := by
  have hl : l.val < 14 := l.2
  have hij' : i.val < j.val := hij
  have hjl' : j.val < l.val := hjl
  have hi : i.val < 12 := by omega
  obtain ⟨iv, hiv⟩ : ∃ iv, iv = i.val := ⟨_, rfl⟩
  rw [← hiv] at hi
  interval_cases iv
  · exact g2Row_0 i j l hiv.symm hij hjl n
  · exact g2Row_1 i j l hiv.symm hij hjl n
  · exact g2Row_2 i j l hiv.symm hij hjl n
  · exact g2Row_3 i j l hiv.symm hij hjl n
  · exact g2Row_4 i j l hiv.symm hij hjl n
  · exact g2Row_5 i j l hiv.symm hij hjl n
  · exact g2Row_6 i j l hiv.symm hij hjl n
  · exact g2Row_7 i j l hiv.symm hij hjl n
  · exact g2Row_8 i j l hiv.symm hij hjl n
  · exact g2Row_9 i j l hiv.symm hij hjl n
  · exact g2Row_10 i j l hiv.symm hij hjl n
  · exact g2Row_11 i j l hiv.symm hij hjl n

theorem g2Checks : Checks 14 g2T :=
  ⟨g2_bound, g2_anti, fun i j l n => jac_of_sorted g2_anti (fun a b c => g2_sortedJac n a b c) i j l⟩

theorem g2RC_hbe : ∀ α β, zeroL (brL g2T (hL g2T g2Data α) (eL g2Data β) ++ scale (-(g2Data.pairT α β)) (eL g2Data β)) = true := by
  intro α β
  have hα : α.val < 12 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 4) ∨ (4 ≤ α.val ∧ α.val < 8) ∨ (8 ≤ α.val ∧ α.val < 12) by omega) with h | h | h
  · exact g2RC_hbe0 α h.1 h.2 β
  · exact g2RC_hbe1 α h.1 h.2 β
  · exact g2RC_hbe2 α h.1 h.2 β

theorem g2RC_hhb : ∀ α β, zeroL (brL g2T (hL g2T g2Data α) (hL g2T g2Data β)) = true := by
  intro α β
  have hα : α.val < 12 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 4) ∨ (4 ≤ α.val ∧ α.val < 8) ∨ (8 ≤ α.val ∧ α.val < 12) by omega) with h | h | h
  · exact g2RC_hhb0 α h.1 h.2 β
  · exact g2RC_hhb1 α h.1 h.2 β
  · exact g2RC_hhb2 α h.1 h.2 β

theorem g2RC_sep : ∀ α β, α ≠ β → ∃ γ, g2Data.pairT γ α ≠ g2Data.pairT γ β := by
  intro α β
  have hα : α.val < 12 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 4) ∨ (4 ≤ α.val ∧ α.val < 8) ∨ (8 ≤ α.val ∧ α.val < 12) by omega) with h | h | h
  · exact g2RC_sep0 α h.1 h.2 β
  · exact g2RC_sep1 α h.1 h.2 β
  · exact g2RC_sep2 α h.1 h.2 β

theorem g2RC_symm : ∀ α β, g2Data.pairT α β ≠ 0 → g2Data.pairT β α ≠ 0 := by
  intro α β
  have hα : α.val < 12 := α.2
  rcases (show (0 ≤ α.val ∧ α.val < 4) ∨ (4 ≤ α.val ∧ α.val < 8) ∨ (8 ≤ α.val ∧ α.val < 12) by omega) with h | h | h
  · exact g2RC_symm0 α h.1 h.2 β
  · exact g2RC_symm1 α h.1 h.2 β
  · exact g2RC_symm2 α h.1 h.2 β

theorem g2RootChecks : RootChecks g2T g2Data :=
  ⟨g2RC_inRange, g2RC_hbe, g2RC_hhb, g2RC_diag, g2RC_sep, g2RC_symm, g2RC_M, g2RC_Q, g2RC_conn,
    g2RC_span⟩

/-- **`𝔤₂`.** -/
abbrev g2Lie : Type := Alg 14 g2T g2Checks

instance g2Lie_isSimple : LieAlgebra.IsSimple ℂ g2Lie :=
  haveI : Nonempty (Fin g2Data.nr) := ⟨⟨0, by decide⟩⟩
  isSimple_of_tables g2Checks g2Data g2RootChecks

theorem finrank_g2Lie : Module.finrank ℂ g2Lie = 14 := finrank_alg g2Checks

/-- A long root. -/
def g2Long : Fin g2Data.nr := ⟨1, by decide⟩

theorem g2_coroot : ⁅hbV g2Checks g2Data g2Long, eV g2Checks g2Data g2Long⁆
    = (-2 : ℂ) • eV g2Checks g2Data g2Long := by
  rw [hbV_eq, eV_eq, lie_vec _ (g2RootChecks.inRange_h _) (eL_inRange _ _)]
  exact_mod_cast vec_eq_of_zeroL g2Checks (-2) (by decide +kernel)

theorem g2_killing : killingForm ℂ g2Lie (hbV g2Checks g2Data g2Long)
    (hbV g2Checks g2Data g2Long) = 16 := by
  rw [hbV_eq, killing_vec _ _ (g2RootChecks.inRange_h _) (by decide +kernel)]
  have h : (∑ k : Fin 14, coef (brL g2T (hL g2T g2Data g2Long)
      (brL g2T (hL g2T g2Data g2Long) [((k : ℕ), 1)])) k) = 16 := by decide +kernel
  exact_mod_cast h

/-- **`Killing/8` is the standard normalization on `𝔤₂`**: long roots have length `2`. -/
theorem g2_standard : ((2 * 4 : ℂ)⁻¹ • killingForm ℂ g2Lie) (hbV g2Checks g2Data g2Long)
    (hbV g2Checks g2Data g2Long) = 2 := by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, g2_killing]
  norm_num

end VOA.AffineGeneral.SCLie

namespace VOA.AffineGeneral.G2Deligne

open VOA.AffineGeneral.SCLie VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-- Lie data for `𝔤₂` (form `Killing/8`, `h = 4`), indexed by `Fin 14`. -/
def g2Data' : LieData ((2 * 4 : ℂ)⁻¹ • killingForm ℂ g2Lie)
    (Fin HigherRankDeligneCase.G2.currentDimension) :=
  (standardData g2Lie 4 (by norm_num)).reindex (finCongr finrank_g2Lie)

theorem g2Data'_h : g2Data'.h = 4 := by
  rw [g2Data', LieData.reindex_h, standardData_h]

theorem g2_level_ne : (-5/3 : ℂ) + g2Data'.h ≠ 0 := by
  rw [g2Data'_h]; norm_num

/-- `L_{-5/3}(𝔤₂)`. -/
abbrev g2SimpleVOA := simpleVOA g2Data' (-5/3) g2_level_ne

theorem g2_currentJetSurjectivity :
    CurrentJetSurjectivity .G2 g2SimpleVOA (Deligne.presentation .G2 g2Data' (-5/3) g2_level_ne) :=
  Deligne.currentJetSurjectivity .G2 g2Data' (-5/3) g2_level_ne

/-- **The Deligne case `G2`, conditional on the two remaining packages.** -/
theorem g2_classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .G2 g2SimpleVOA
      (Deligne.presentation .G2 g2Data' (-5/3) g2_level_ne) Carrier)
    (hchar : OrdinaryCarrierCharacter g2SimpleVOA Carrier) :
    CaseClassicallyFree .G2 g2SimpleVOA (Deligne.presentation .G2 g2Data' (-5/3) g2_level_ne) :=
  Deligne.classicallyFree_of_two_inputs .G2 g2Data' (-5/3) g2_level_ne Carrier hgeom hchar

end

end VOA.AffineGeneral.G2Deligne
