/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LiePresentationBase

/-!
# Propagation identities for the `D₄` relations (generated)

`step_s : ad_b P_r = c • P_s`: the coadjoint derivation of the current `x_b` carries an already
established relation `P_r` (of `DeligneCarrierD4`) to a nonzero multiple of a new one `P_s`.  Starting
from the three highest relations `P0, P1, P2`, the 102 steps reach all 105 relations of `I₂ⁿˢ`.
The chain was found by exact linear algebra over `ℚ` (by a script not included in this release); each identity
is checked here by `simp` + `ring`.
-/

namespace VOA.DeligneAudit.D4Lie

open MvPolynomial

set_option linter.unusedSimpArgs false

theorem C2' : (MvPolynomial.C (2 : ℂ) : MvPolynomial (Fin 28) ℂ) = 2 := map_ofNat _ 2
theorem C4' : (MvPolynomial.C (4 : ℂ) : MvPolynomial (Fin 28) ℂ) = 4 := map_ofNat _ 4
theorem C8' : (MvPolynomial.C (8 : ℂ) : MvPolynomial (Fin 28) ℂ) = 8 := map_ofNat _ 8
theorem C16' : (MvPolynomial.C (16 : ℂ) : MvPolynomial (Fin 28) ℂ) = 16 := map_ofNat _ 16

theorem step3 : (1 : ℂ) • ad4 16 (Q 0) = (1 : ℂ) • Q 3 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step6 : (1 : ℂ) • ad4 20 (Q 0) = (-1 : ℂ) • Q 6 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step13 : (1 : ℂ) • ad4 23 (Q 0) = (1 : ℂ) • Q 13 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step12 : (1 : ℂ) • ad4 24 (Q 0) = (-1 : ℂ) • Q 12 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step21 : (1 : ℂ) • ad4 26 (Q 0) = (1 : ℂ) • Q 21 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step33 : (1 : ℂ) • ad4 27 (Q 0) = (1 : ℂ) • Q 33 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step4 : (1 : ℂ) • ad4 17 (Q 1) = (1 : ℂ) • Q 4 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step8 : (1 : ℂ) • ad4 21 (Q 1) = (-1 : ℂ) • Q 8 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step17 : (1 : ℂ) • ad4 23 (Q 1) = (1 : ℂ) • Q 17 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step15 : (1 : ℂ) • ad4 25 (Q 1) = (-1 : ℂ) • Q 15 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step26 : (1 : ℂ) • ad4 26 (Q 1) = (1 : ℂ) • Q 26 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step39 : (1 : ℂ) • ad4 27 (Q 1) = (1 : ℂ) • Q 39 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step5 : (1 : ℂ) • ad4 19 (Q 2) = (1 : ℂ) • Q 5 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step11 : (1 : ℂ) • ad4 22 (Q 2) = (1 : ℂ) • Q 11 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step20 : (1 : ℂ) • ad4 24 (Q 2) = (-1 : ℂ) • Q 20 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step19 : (1 : ℂ) • ad4 25 (Q 2) = (-1 : ℂ) • Q 19 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step32 : (1 : ℂ) • ad4 26 (Q 2) = (1 : ℂ) • Q 32 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step44 : (1 : ℂ) • ad4 27 (Q 2) = (1 : ℂ) • Q 44 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step7 : (1 : ℂ) • ad4 16 (Q 3) = (1 : ℂ) • Q 7 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step14 : (1 : ℂ) • ad4 20 (Q 3) = (-1 : ℂ) • Q 14 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step23 : (1 : ℂ) • ad4 23 (Q 3) = (1 : ℂ) • Q 23 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step22 : (1 : ℂ) • ad4 24 (Q 3) = (-1 : ℂ) • Q 22 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step34 : (1 : ℂ) • ad4 26 (Q 3) = (1 : ℂ) • Q 34 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step45 : (1 : ℂ) • ad4 27 (Q 3) = (1 : ℂ) • Q 45 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step9 : (1 : ℂ) • ad4 17 (Q 4) = (1 : ℂ) • Q 9 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step16 : (1 : ℂ) • ad4 21 (Q 4) = (-1 : ℂ) • Q 16 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step28 : (1 : ℂ) • ad4 23 (Q 4) = (1 : ℂ) • Q 28 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step25 : (1 : ℂ) • ad4 25 (Q 4) = (-1 : ℂ) • Q 25 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step38 : (1 : ℂ) • ad4 26 (Q 4) = (1 : ℂ) • Q 38 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step53 : (1 : ℂ) • ad4 27 (Q 4) = (1 : ℂ) • Q 53 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step10 : (1 : ℂ) • ad4 19 (Q 5) = (1 : ℂ) • Q 10 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step18 : (2 : ℂ) • ad4 22 (Q 5) = (1 : ℂ) • Q 18 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step31 : (2 : ℂ) • ad4 24 (Q 5) = (-1 : ℂ) • Q 31 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step30 : (2 : ℂ) • ad4 25 (Q 5) = (-1 : ℂ) • Q 30 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step43 : (2 : ℂ) • ad4 26 (Q 5) = (1 : ℂ) • Q 43 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step59 : (1 : ℂ) • ad4 27 (Q 5) = (1 : ℂ) • Q 59 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step24 : (1 : ℂ) • ad4 20 (Q 6) = (-1 : ℂ) • Q 24 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step36 : (1 : ℂ) • ad4 23 (Q 6) = (1 : ℂ) • Q 36 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step35 : (1 : ℂ) • ad4 24 (Q 6) = (-1 : ℂ) • Q 35 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step60 : (1 : ℂ) • ad4 27 (Q 6) = (1 : ℂ) • Q 60 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step61 : (1 : ℂ) • ad4 27 (Q 7) = (1 : ℂ) • Q 61 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step27 : (1 : ℂ) • ad4 21 (Q 8) = (-1 : ℂ) • Q 27 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step40 : (2 : ℂ) • ad4 23 (Q 8) = (1 : ℂ) • Q 40 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step37 : (1 : ℂ) • ad4 25 (Q 8) = (-1 : ℂ) • Q 37 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step65 : (1 : ℂ) • ad4 27 (Q 8) = (1 : ℂ) • Q 65 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step67 : (1 : ℂ) • ad4 27 (Q 9) = (2 : ℂ) • Q 67 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step71 : (1 : ℂ) • ad4 27 (Q 10) = (1 : ℂ) • Q 71 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step29 : (2 : ℂ) • ad4 22 (Q 11) = (1 : ℂ) • Q 29 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step42 : (4 : ℂ) • ad4 24 (Q 11) = (-1 : ℂ) • Q 42 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step41 : (4 : ℂ) • ad4 25 (Q 11) = (-1 : ℂ) • Q 41 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step69 : (4 : ℂ) • ad4 27 (Q 11) = (1 : ℂ) • Q 69 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step47 : (1 : ℂ) • ad4 24 (Q 12) = (-1 : ℂ) • Q 47 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step62 : (1 : ℂ) • ad4 26 (Q 12) = (1 : ℂ) • Q 62 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step72 : (1 : ℂ) • ad4 27 (Q 12) = (1 : ℂ) • Q 72 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step49 : (1 : ℂ) • ad4 23 (Q 13) = (1 : ℂ) • Q 49 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step63 : (1 : ℂ) • ad4 26 (Q 13) = (1 : ℂ) • Q 63 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step73 : (1 : ℂ) • ad4 27 (Q 13) = (1 : ℂ) • Q 73 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step46 : (1 : ℂ) • ad4 25 (Q 14) = (1 : ℂ) • Q 46 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step74 : (1 : ℂ) • ad4 27 (Q 14) = (1 : ℂ) • Q 74 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step50 : (1 : ℂ) • ad4 25 (Q 15) = (-1 : ℂ) • Q 50 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step64 : (2 : ℂ) • ad4 26 (Q 15) = (1 : ℂ) • Q 64 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step76 : (2 : ℂ) • ad4 27 (Q 15) = (1 : ℂ) • Q 76 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step52 : (1 : ℂ) • ad4 24 (Q 16) = (1 : ℂ) • Q 52 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step78 : (1 : ℂ) • ad4 27 (Q 16) = (1 : ℂ) • Q 78 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step54 : (2 : ℂ) • ad4 23 (Q 17) = (1 : ℂ) • Q 54 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step66 : (2 : ℂ) • ad4 26 (Q 17) = (1 : ℂ) • Q 66 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step79 : (1 : ℂ) • ad4 27 (Q 17) = (1 : ℂ) • Q 79 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step58 : (1 : ℂ) • ad4 23 (Q 18) = (-1 : ℂ) • Q 58 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step82 : (2 : ℂ) • ad4 27 (Q 18) = (1 : ℂ) • Q 82 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step55 : (4 : ℂ) • ad4 25 (Q 19) = (-1 : ℂ) • Q 55 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step68 : (8 : ℂ) • ad4 26 (Q 19) = (1 : ℂ) • Q 68 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step80 : (8 : ℂ) • ad4 27 (Q 19) = (1 : ℂ) • Q 80 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step57 : (4 : ℂ) • ad4 24 (Q 20) = (-1 : ℂ) • Q 57 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step70 : (8 : ℂ) • ad4 26 (Q 20) = (1 : ℂ) • Q 70 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step83 : (4 : ℂ) • ad4 27 (Q 20) = (1 : ℂ) • Q 83 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step75 : (1 : ℂ) • ad4 26 (Q 21) = (1 : ℂ) • Q 75 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step84 : (1 : ℂ) • ad4 27 (Q 21) = (1 : ℂ) • Q 84 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step85 : (1 : ℂ) • ad4 27 (Q 22) = (1 : ℂ) • Q 85 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step86 : (1 : ℂ) • ad4 27 (Q 23) = (1 : ℂ) • Q 86 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step87 : (2 : ℂ) • ad4 27 (Q 25) = (1 : ℂ) • Q 87 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step77 : (2 : ℂ) • ad4 26 (Q 26) = (1 : ℂ) • Q 77 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step88 : (2 : ℂ) • ad4 27 (Q 26) = (1 : ℂ) • Q 88 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step89 : (1 : ℂ) • ad4 27 (Q 28) = (1 : ℂ) • Q 89 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step90 : (4 : ℂ) • ad4 27 (Q 30) = (1 : ℂ) • Q 90 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step92 : (2 : ℂ) • ad4 27 (Q 31) = (1 : ℂ) • Q 92 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step81 : (8 : ℂ) • ad4 26 (Q 32) = (1 : ℂ) • Q 81 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step91 : (8 : ℂ) • ad4 27 (Q 32) = (1 : ℂ) • Q 91 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step93 : (1 : ℂ) • ad4 27 (Q 33) = (1 : ℂ) • Q 93 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step94 : (1 : ℂ) • ad4 27 (Q 34) = (1 : ℂ) • Q 94 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step48 : (1 : ℂ) • ad4 17 (Q 35) = (1 : ℂ) • Q 48 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step51 : (1 : ℂ) • ad4 16 (Q 37) = (1 : ℂ) • Q 51 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step95 : (2 : ℂ) • ad4 27 (Q 38) = (1 : ℂ) • Q 95 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step96 : (2 : ℂ) • ad4 27 (Q 39) = (1 : ℂ) • Q 96 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step56 : (1 : ℂ) • ad4 16 (Q 41) = (1 : ℂ) • Q 56 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step97 : (4 : ℂ) • ad4 27 (Q 43) = (1 : ℂ) • Q 97 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step98 : (8 : ℂ) • ad4 27 (Q 44) = (1 : ℂ) • Q 98 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step99 : (1 : ℂ) • ad4 27 (Q 45) = (1 : ℂ) • Q 99 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step100 : (2 : ℂ) • ad4 27 (Q 52) = (1 : ℂ) • Q 100 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step101 : (4 : ℂ) • ad4 27 (Q 58) = (1 : ℂ) • Q 101 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step102 : (1 : ℂ) • ad4 27 (Q 61) = (1 : ℂ) • Q 102 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step103 : (2 : ℂ) • ad4 27 (Q 67) = (1 : ℂ) • Q 103 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

theorem step104 : (4 : ℂ) • ad4 27 (Q 71) = (1 : ℂ) • Q 104 := by
  rw [ad4_Q, Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp only [ad4_X]
  simp [DeligneCarrier.D4.relTable, sL, smul_eq_C_mul, C2', C4', C8', C16']
  ring

end VOA.DeligneAudit.D4Lie
