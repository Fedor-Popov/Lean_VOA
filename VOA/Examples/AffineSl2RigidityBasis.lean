/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2Rigidity43

/-!
# The weight-one basis of the simple affine algebra at level -4/3

The currents survive the simple quotient independently: their first positive modes
recover the three coefficients of any linear relation, as nonzero multiples of the
vacuum. Together with current-word spanning, this supplies the Lie-theoretic input
to the rigidity programme without assuming a PBW theorem or a Gram determinant.

This file does not assume or assert the two remaining deformation-theoretic inputs.
-/

namespace VOA.LQ43

open AffineVOA AffineLie AffineVOA.Inst Sl2Sing

local notation "kk" => (-4 / 3 : ℂ)
local notation "I" => QuotVOA.maxGradedIdeal voaSl2Adm

/-- Convert the order `(e,h,f)` to the original current colour indices. -/
private def currentColor : Fin 3 → Fin 3 := ![colE, colH, colF]

/-- The three current states, regarded as weight-one states of the simple quotient. -/
noncomputable def quotientCurrent (a : Fin 3) : L43.grading 1 :=
  ⟨(I).mkQ (currentState kk (currentColor a)),
    Submodule.mem_map.mpr ⟨currentState kk (currentColor a),
      currentState_mem_grading kk admLevel_noncritical (currentColor a), rfl⟩⟩

/-- Computing a product of quotient currents reduces to the original current modes. -/
theorem quotientCurrent_mode (a b : Fin 3) (n : ℤ) :
    L43.smul (quotientCurrent a) n (quotientCurrent b) =
      (I).mkQ (J kk (currentColor a) n (J kk (currentColor b) (-1) (vacuumA kk))) := by
  change L43.smul ((I).mkQ (currentState kk (currentColor a))) n
    ((I).mkQ (currentState kk (currentColor b))) = _
  change (QuotVOA.quotientVOA voaSl2Adm (I)
    (QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm)
    (QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm)).smul _ n _ = _
  rw [QuotVOA.quotientVOA_mkQ_smul (QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm)
    (QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm), smul_currentState_adm, currentState_def]

/-- The first positive modes detect each current coefficient through the vacuum. -/
theorem quotientCurrent_pole (a b : Fin 3) :
    L43.smul (quotientCurrent a) 1 (quotientCurrent b) =
      (if a = 0 ∧ b = 2 ∨ a = 2 ∧ b = 0 then kk
       else if a = 1 ∧ b = 1 then 2 * kk else 0) • L43.vacuum := by
  rw [quotientCurrent_mode]
  fin_cases a <;> fin_cases b <;>
    simp [currentColor, E1E1, E1H1, E1F1, H1E1, H1H1, H1F1,
      F1E1, F1H1, F1F1, L43, QuotVOA.maxQuotientVOA, voaSl2Adm_vacuum]

/-- No nonzero linear combination of the three currents vanishes in the simple quotient. -/
theorem quotientCurrent_linearIndependent : LinearIndependent ℂ quotientCurrent := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hv : (∑ i, c i • (quotientCurrent i : WakModule kk ⧸ I)) = 0 :=
    by simpa using congrArg (fun x : L43.grading 1 => (x : WakModule kk ⧸ I)) hc
  have probe (a : Fin 3) := congrArg (fun x => L43.smul (quotientCurrent a) 1 x) hv
  simp only [Fin.sum_univ_three] at probe
  have h0 : c 0 = 0 := by
    have h := probe 2
    norm_num [PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
      quotientCurrent_pole, smul_smul, Fin.ext_iff, smul_eq_zero,
      L43_vacuum_ne_zero] at h
    exact h
  have h1 : c 1 = 0 := by
    have h := probe 1
    norm_num [PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
      quotientCurrent_pole, smul_smul, Fin.ext_iff, smul_eq_zero,
      L43_vacuum_ne_zero] at h
    exact h
  have h2 : c 2 = 0 := by
    have h := probe 0
    norm_num [PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
      quotientCurrent_pole, smul_smul, Fin.ext_iff, smul_eq_zero,
      L43_vacuum_ne_zero] at h
    exact h
  intro i
  fin_cases i <;> assumption

/-- Every weight-one state of the simple quotient is a combination of the currents. -/
theorem quotientCurrent_span :
    Submodule.span ℂ (Set.range quotientCurrent) = ⊤ := by
  classical
  let S := (Submodule.span ℂ (Set.range quotientCurrent)).map (L43.grading 1).subtype
  have hmem (v : WakModule kk) (hv : v ∈ HSpan kk 1) : (I).mkQ v ∈ S := by
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      obtain ⟨a, rfl⟩ := wordDegA_eq_one hl
      have ha : ∃ b, currentColor b = a := by
        fin_cases a
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨1, rfl⟩
      obtain ⟨b, rfl⟩ := ha
      refine Submodule.mem_map.mpr ⟨quotientCurrent b,
        Submodule.subset_span (Set.mem_range_self b), ?_⟩
      simp [quotientCurrent, currentState_def, wordStateA_cons, wordStateA_nil]
    | zero => simp [S]
    | add x y _ _ hx hy => simpa using S.add_mem hx hy
    | smul c x _ hx => simpa using S.smul_mem c hx
  apply top_unique
  intro x _
  obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp x.property
  have hv' : v ∈ (affineSl2VOA_closed kk admLevel_noncritical).grading 1 := hv
  rw [closed_grading] at hv'
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hmem v (gradingZA_le_hspan kk 1 hv'))
  have : y = x := Subtype.ext (hyx.trans he)
  exact this ▸ hy

/-- The explicit basis `(e,h,f)` of the simple quotient's weight-one Lie algebra. -/
noncomputable def L43_weightOneBasis : Module.Basis (Fin 3) ℂ (L43.grading 1) :=
  Module.Basis.mk quotientCurrent_linearIndependent (by rw [quotientCurrent_span])

/-- The abstract basis constructed from independence and spanning consists
exactly of the three quotient currents, in the order e, h, f. This lets the
concrete current-mode calculations establish the basis's sl₂ bracket relations. -/
@[simp] theorem L43_weightOneBasis_apply (a : Fin 3) :
    L43_weightOneBasis a = quotientCurrent a := Module.Basis.mk_apply _ _ a

/-- The basis has the sl₂ commutation relations, including a nonzero Cartan current. -/
theorem L43_weightOneTriple :
    IsSl2Triple (L43_weightOneBasis 1) (L43_weightOneBasis 0) (L43_weightOneBasis 2) where
  h_ne_zero := L43_weightOneBasis.ne_zero 1
  lie_e_f := by
    apply Subtype.ext
    change L43.smul _ 0 _ = _
    simp only [L43_weightOneBasis_apply, quotientCurrent_mode]
    simp [currentColor, E0F1, quotientCurrent, currentState_def]
  lie_h_e_nsmul := by
    apply Subtype.ext
    change L43.smul _ 0 _ = _
    simp only [L43_weightOneBasis_apply, quotientCurrent_mode]
    simp [currentColor, H0E1, quotientCurrent, currentState_def, two_smul]
  lie_h_f_nsmul := by
    apply Subtype.ext
    change L43.smul _ 0 _ = _
    simp only [L43_weightOneBasis_apply, quotientCurrent_mode]
    simp [currentColor, H0F1, quotientCurrent, currentState_def, two_smul]

/-- The weight-one Lie-theoretic input `Sl2BasisOnWeightOne` is constructed, not assumed. -/
theorem L43_sl2BasisOnWeightOne : Sl2BasisOnWeightOne L43 :=
  ⟨L43_weightOneBasis, L43_weightOneTriple⟩

/-- Whitehead normalization applies to the concrete simple quotient without a basis hypothesis. -/
theorem L43_weightOneH2Vanishes : L43.WeightOneH2Vanishes :=
  weightOneH2Vanishes_of_sl2Basis' L43 L43_sl2BasisOnWeightOne

/-- The concrete weight-one Lie algebra has zero centre. -/
theorem L43_centrelessWeightOne : L43.CentrelessWeightOne :=
  centrelessWeightOne_of_sl2Basis' L43 L43_sl2BasisOnWeightOne

/-- The affine rigidity reduction has only the two deformation-theoretic inputs.
Neither input is proved here; this is not an unconditional rigidity theorem. -/
theorem L43_isRigidGraded_of_deformation_inputs
    (h31 : RegularImpliesTrivialGraded L43) (h2 : NormalisedPoleVanishes L43) :
    Deform.IsRigidGraded L43 :=
  L43_isRigidGraded L43_sl2BasisOnWeightOne h31 h2

end VOA.LQ43
