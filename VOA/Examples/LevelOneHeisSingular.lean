/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.CyclicEvalHeisenberg
import VOA.Examples.LevelOneUnitaryPositivity

/-!
# Heisenberg-singular vectors of `L_1(sl₂)` sit at energy `μ²/4`

At level one the Sugawara vector of `sl₂` coincides, in the simple quotient, with the Heisenberg
conformal vector of the Cartan current:

  `ω = ¼ h₋₁h₋₁|0⟩` in `L_1(sl₂)`.

Proof: the defect `D = ω - ¼ h₋₁h₋₁|0⟩` of the universal module `V^1(sl₂)` is killed by every
positive current mode (`[J^a_m, L₋₂] = m J^a_{m-2}` against the explicit commutators of
`h₋₁h₋₁|0⟩`; the `e₁`/`f₁` checks use `k = 1`), so it lies in the maximal ideal
(`mem_maxIdeal_of_pos_kill`).

Then the Borcherds iterate formula for `(h₍₋₁₎h)₍₁₎` gives, for a vector `b` of `h₀`-charge `μ`
killed by all positive Cartan modes,

  `L₀ b = ¼ Σ_{i ≥ 0} (h₍₋₁₋ᵢ₎ h₍₁₊ᵢ₎ + h₍₋ᵢ₎ h₍ᵢ₎) b = ¼ μ² b`.

* `sugawaraDefect_mem` — `ω - ¼ h₋₁h₋₁|0⟩ ∈ I` (proved);
* `bConformal_eq` — `ω_B = ¼ h₍₋₁₎h` in `BSpace` (proved);
* `bL0_heisenbergSingular` — `L₀ b = (μ²/4) b` for Heisenberg-singular `b` of charge `μ`;
* `levelOneHeisenbergSingular` — **`LevelOneHeisenbergSingular` proved outright.**
-/

namespace VOA.LevelOneHeis

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineSl2BelowCritical Sl2Sing
open VOA.Sl2CosetConcrete VOA.CyclicEval VOA.LevelOneUnitary
open Module (End)

noncomputable section

/-- The universal level-one affine VOA. -/
abbrev WU : VertexOperatorAlgebra (WakModule 1) := universal 1 bNoncritical

/-- The maximal graded ideal of `V^1(sl₂)`. -/
abbrev IB : Submodule ℂ (WakModule 1) := QuotVOA.maxGradedIdeal WU

/-! ### The Sugawara defect in the universal module -/

/-- `h₋₁h₋₁|0⟩`. -/
def hhState : WakModule 1 := J 1 colH (-1) (J 1 colH (-1) (vacuumA 1))

/-- The Sugawara defect `ω - ¼ h₋₁h₋₁|0⟩`. -/
def sugawaraDefect : WakModule 1 := omegaA 1 - (1 / 4 : ℂ) • hhState

theorem J_omegaA (a : Fin 3) {m : ℤ} (hm : 0 ≤ m) :
    J 1 a m (omegaA 1) = (m : ℂ) • J 1 a (m - 2) (vacuumA 1) := by
  have h := Vir.Lcomm_J_apply 1 bNoncritical (-2) a m (vacuumA 1)
  rw [J_vac 1 a hm, map_zero] at h
  have hω : mode (YA 1 bNoncritical (omegaA 1)) (-2 + 1) (vacuumA 1) = omegaA 1 := by
    have := WU.smul_vacuum_neg_one (omegaA 1)
    rw [show (-2 : ℤ) + 1 = -1 by norm_num]
    exact this
  rw [hω] at h
  have h2 : J 1 a m (omegaA 1) = -(((-m : ℤ) : ℂ) • J 1 a (-2 + m) (vacuumA 1)) :=
    eq_neg_of_add_eq_zero_left h.symm
  rw [h2, show (-2 : ℤ) + m = m - 2 by ring]
  push_cast
  rw [neg_smul, neg_neg]

theorem H_hhState_one : J 1 colH 1 hhState = (4 : ℂ) • J 1 colH (-1) (vacuumA 1) := by
  rw [hhState, HHz 1 1 (-1) (by norm_num), HHz 1 1 (-1) (by norm_num),
    J_vac 1 colH (by norm_num : (0 : ℤ) ≤ 1)]
  simp only [map_zero, zero_add, map_smul]
  push_cast
  module

theorem H_hhState_two : J 1 colH 2 hhState = 0 := by
  rw [hhState, HHs 1 2 (-1) (by norm_num), HHs 1 2 (-1) (by norm_num),
    J_vac 1 colH (by norm_num : (0 : ℤ) ≤ 2)]
  simp

theorem E_hhState_one : J 1 colE 1 hhState = (4 : ℂ) • J 1 colE (-1) (vacuumA 1) := by
  rw [hhState, EHs 1 1 (-1) 0 (by norm_num), EHs 1 1 (-1) 0 (by norm_num),
    EHs 1 0 (-1) (-1) (by norm_num), J_vac 1 colE (by norm_num : (0 : ℤ) ≤ 1),
    J_vac 1 colE (by norm_num : (0 : ℤ) ≤ 0)]
  simp only [map_zero, zero_sub, map_neg, map_smul]
  module

theorem E_hhState_two : J 1 colE 2 hhState = 0 := by
  rw [hhState, EHs 1 2 (-1) 1 (by norm_num), EHs 1 2 (-1) 1 (by norm_num),
    EHs 1 1 (-1) 0 (by norm_num), J_vac 1 colE (by norm_num : (0 : ℤ) ≤ 2),
    J_vac 1 colE (by norm_num : (0 : ℤ) ≤ 1), J_vac 1 colE (by norm_num : (0 : ℤ) ≤ 0)]
  simp

theorem F_hhState_one : J 1 colF 1 hhState = (4 : ℂ) • J 1 colF (-1) (vacuumA 1) := by
  rw [hhState, FHs 1 1 (-1) 0 (by norm_num), FHs 1 1 (-1) 0 (by norm_num),
    FHs 1 0 (-1) (-1) (by norm_num), J_vac 1 colF (by norm_num : (0 : ℤ) ≤ 1),
    J_vac 1 colF (by norm_num : (0 : ℤ) ≤ 0)]
  simp only [map_zero, zero_add, map_smul]
  module

theorem F_hhState_two : J 1 colF 2 hhState = 0 := by
  rw [hhState, FHs 1 2 (-1) 1 (by norm_num), FHs 1 2 (-1) 1 (by norm_num),
    FHs 1 1 (-1) 0 (by norm_num), J_vac 1 colF (by norm_num : (0 : ℤ) ≤ 2),
    J_vac 1 colF (by norm_num : (0 : ℤ) ≤ 1), J_vac 1 colF (by norm_num : (0 : ℤ) ≤ 0)]
  simp

theorem hhState_mem_grading : hhState ∈ WU.grading 2 := by
  have h0 : vacuumA 1 ∈ WU.grading 0 := vacuum_mem_grading_zero bNoncritical
  have h1 := J_mem_grading bNoncritical colH (-1) h0
  have h2 := J_mem_grading bNoncritical colH (-1) h1
  simpa [hhState] using h2

theorem sugawaraDefect_mem_grading : sugawaraDefect ∈ WU.grading 2 :=
  Submodule.sub_mem _ WU.conformal_mem (Submodule.smul_mem _ _ hhState_mem_grading)

theorem J_sugawaraDefect_one (a : Fin 3) : J 1 a 1 sugawaraDefect = 0 := by
  rw [sugawaraDefect, map_sub, map_smul, J_omegaA a (by norm_num)]
  fin_cases a
  · simp only [Fin.zero_eta]
    rw [E_hhState_one, smul_smul]; norm_num
  · simp only [Fin.mk_one]
    rw [F_hhState_one, smul_smul]; norm_num
  · simp only [Fin.reduceFinMk]
    rw [H_hhState_one, smul_smul]; norm_num

theorem J_sugawaraDefect_two (a : Fin 3) : J 1 a 2 sugawaraDefect = 0 := by
  rw [sugawaraDefect, map_sub, map_smul, J_omegaA a (by norm_num)]
  rw [show (2 : ℤ) - 2 = 0 by norm_num, J_vac 1 a le_rfl]
  fin_cases a
  · simp only [Fin.zero_eta]; rw [E_hhState_two]; simp
  · simp only [Fin.mk_one]; rw [F_hhState_two]; simp
  · simp only [Fin.reduceFinMk]; rw [H_hhState_two]; simp

/-- **The level-one Sugawara defect lies in the maximal ideal**: `ω = ¼ h₋₁h₋₁|0⟩` in
`L_1(sl₂)`. -/
theorem sugawaraDefect_mem : sugawaraDefect ∈ IB := by
  refine mem_maxIdeal_of_pos_kill bNoncritical (E := 2) (by norm_num)
    sugawaraDefect_mem_grading ?_
  intro a m hm
  rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | h3
  · rw [Nat.cast_one, J_sugawaraDefect_one]; exact Submodule.zero_mem _
  · rw [Nat.cast_two, J_sugawaraDefect_two]; exact Submodule.zero_mem _
  · rw [eq_zero_of_grading_neg bNoncritical (n := 2 - (m : ℤ)) (by omega)
      (J_mem_grading bNoncritical a (m : ℤ) sugawaraDefect_mem_grading)]
    exact Submodule.zero_mem _

/-! ### Descent to `L_1(sl₂)` -/

/-- The Cartan current `h` of `L_1(sl₂)`. -/
abbrev hB : BSpace := bAction.current 2

theorem bSmul_hB (n : ℤ) (b : BSpace) :
    BVOA.smul hB n b = mode (BSVA.Y (bAction.current 2)) n b := rfl

theorem bConformal_mkQ : BVOA.conformalVector = IB.mkQ (omegaA 1) := rfl

theorem bSmul_hB_hB : BVOA.smul hB (-1) hB = IB.mkQ hhState := by
  have h := SimpleQuot.maxQuotientVOA_mkQ_smul WU (currentState 1 2) (-1) (currentState 1 2)
  rw [smul_currentState_eq_J] at h
  exact h

/-- **`ω = ¼ h₍₋₁₎h` in `L_1(sl₂)`**: the level-one Sugawara vector is the Heisenberg
conformal vector of the Cartan current. -/
theorem bConformal_eq : BVOA.conformalVector = (1 / 4 : ℂ) • BVOA.smul hB (-1) hB := by
  rw [bSmul_hB_hB, bConformal_mkQ, ← map_smul, ← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr sugawaraDefect_mem

/-- **`L₀ = (μ²/4)` on Heisenberg-singular vectors** of `h₀`-charge `μ`. -/
theorem bL0_heisenbergSingular {μ : ℂ} {b : BSpace}
    (hc : bMode bHZero b = μ • b) (hsing : ∀ i, bMode (bHPos i) b = 0) :
    BVOA.L 0 b = (μ ^ 2 / 4) • b := by
  have hpos : ∀ n : ℤ, 0 < n → BVOA.smul hB n b = 0 := by
    intro n hn
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = ((i + 1 : ℕ) : ℤ) := ⟨(n - 1).toNat, by omega⟩
    exact hsing i
  have hzero : BVOA.smul hB 0 b = μ • b := hc
  rw [VertexOperatorAlgebra.L_def, zero_add, bConformal_eq]
  change BVOA.smul ((1 / 4 : ℂ) • BVOA.smul hB (-1) hB) 1 b = _
  rw [PreVertexAlgebra.smul_smul_left]
  have h := VertexOperatorAlgebra.mode_iterate_neg BVOA hB hB 0 1 b
  simp only [Nat.cast_zero, neg_zero, zero_sub] at h
  rw [h, finsum_eq_single _ 0]
  · simp only [Nat.cast_zero, pow_zero, gBinom_zero, mul_one, one_smul, sub_zero, add_zero]
    rw [hpos 1 (by norm_num), PreVertexAlgebra.smul_zero_right, show (-1 : ℤ) + 1 = 0 by norm_num,
      hzero, PreVertexAlgebra.smul_smul_right, hzero, smul_smul,
      show ((-1 : ℂ) ^ (-1 : ℤ)) = -1 by norm_num, smul_smul, zero_sub, ← neg_smul, smul_smul]
    congr 1
    ring
  · intro i hi
    rw [hpos (1 + i) (by omega), PreVertexAlgebra.smul_zero_right, hpos i (by omega),
      PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero, smul_zero]

/-- **`LevelOneHeisenbergSingular`, proved outright**: a vector of `L_1(sl₂)` of charge `2r`
killed by every positive Cartan mode has energy `r²` (or vanishes). -/
theorem levelOneHeisenbergSingular : LevelOneHeisenbergSingular := by
  intro r E b hb hc hsing hE
  have hL := bL0_heisenbergSingular hc hsing
  have hb' : b ∈ BVOA.grading E := by
    have : b ∈ BVOA.toPreVertexAlgebra.gradingC (E : ℂ) := hb
    rwa [PreVertexAlgebra.gradingC_intCast] at this
  rw [BVOA.L_zero_grading b hb'] at hL
  have h2 : ((E : ℂ) - (r : ℂ) ^ 2) • b = 0 := by
    rw [sub_smul, hL]; ring_nf; simp
  rcases smul_eq_zero.mp h2 with h | h
  · exfalso
    apply hE
    have : (E : ℂ) = ((r * r : ℤ) : ℂ) := by push_cast; linear_combination h
    exact_mod_cast this
  · exact h

end

end VOA.LevelOneHeis
