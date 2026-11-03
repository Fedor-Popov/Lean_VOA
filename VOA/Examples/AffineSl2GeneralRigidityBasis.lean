/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSimpleQuotient
import VOA.Examples.AffineSl2RigidityBasis
import VOA.Examples.AffineSl2BoundaryMaximalIdeal

/-!
# Weight-one normalization for every nonzero noncritical affine sl₂ level

The positive current modes detect coefficients through the nonzero level and
vacuum. This supplies an actual sl₂ basis of the simple quotient, not a basis
hypothesis. No admissibility, determinant formula or rigidity is assumed.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineLie AffineVOA.Inst Sl2Sing LQ43
variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The universal affine VOA with its noncritical Sugawara conformal structure. -/
noncomputable abbrev universal := affineSl2VOA_closed k hk
/-- Its actual maximal-ideal quotient, without a singular-vector presentation. -/
noncomputable abbrev simple := QuotVOA.maxQuotientVOA (universal k hk)
local notation "I" => QuotVOA.maxGradedIdeal (universal k hk)

/-- The quotient vacuum survives, using the proved concrete affine PBW basis. -/
theorem simple_vacuum_ne_zero : (simple k hk).vacuum ≠ 0 :=
  SimpleQuot.maxQuotientVOA_vacuum_ne_zero (universal k hk)
    (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k hk)

/-- The maximal-ideal quotient is simple at every noncritical level. -/
theorem simple_isSimple : (simple k hk).IsSimple :=
  QuotVOA.isSimple_maxQuotientVOA' _
    (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero k hk)

/-- Convert the order `(e,h,f)` to the original current colour indices. -/
private def currentColor : Fin 3 → Fin 3 := ![colE, colH, colF]

/-- The three current states, regarded as weight-one states of the simple quotient. -/
noncomputable def quotientCurrent (a : Fin 3) : (simple k hk).grading 1 :=
  ⟨(I).mkQ (currentState k (currentColor a)),
    Submodule.mem_map.mpr ⟨currentState k (currentColor a),
      currentState_mem_grading k hk (currentColor a), rfl⟩⟩

/-- Computing a product of quotient currents reduces to the original current modes. -/
theorem quotientCurrent_mode (a b : Fin 3) (n : ℤ) :
    (simple k hk).smul ((quotientCurrent k hk) a) n ((quotientCurrent k hk) b) =
      (I).mkQ (J k (currentColor a) n (J k (currentColor b) (-1) (vacuumA k))) := by
  change (simple k hk).smul ((I).mkQ (currentState k (currentColor a))) n
    ((I).mkQ (currentState k (currentColor b))) = _
  change (QuotVOA.quotientVOA (universal k hk) (I)
    (QuotVOA.maxGradedIdeal_isIdeal (universal k hk))
    (QuotVOA.maxGradedIdeal_isGradedIdeal (universal k hk))).smul _ n _ = _
  rw [QuotVOA.quotientVOA_mkQ_smul (QuotVOA.maxGradedIdeal_isIdeal (universal k hk))
    (QuotVOA.maxGradedIdeal_isGradedIdeal (universal k hk)), smul_currentState_eq_J, currentState_def]

/-- The first positive modes detect each current coefficient through the vacuum. -/
theorem quotientCurrent_pole (a b : Fin 3) :
    (simple k hk).smul ((quotientCurrent k hk) a) 1 ((quotientCurrent k hk) b) =
      (if a = 0 ∧ b = 2 ∨ a = 2 ∧ b = 0 then k
       else if a = 1 ∧ b = 1 then 2 * k else 0) • (simple k hk).vacuum := by
  rw [(quotientCurrent_mode k hk)]
  fin_cases a <;> fin_cases b <;>
    simp [currentColor, E1E1, E1H1, E1F1, H1E1, H1H1, H1F1,
      F1E1, F1H1, F1F1, simple, QuotVOA.maxQuotientVOA, universal, closed_vacuum]

/-- No nonzero linear combination of the three currents vanishes in the simple quotient. -/
theorem quotientCurrent_linearIndependent (hk0 : k ≠ 0) : LinearIndependent ℂ (quotientCurrent k hk) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hv : (∑ i, c i • ((quotientCurrent k hk) i : WakModule k ⧸ I)) = 0 :=
    by simpa using congrArg (fun x : (simple k hk).grading 1 => (x : WakModule k ⧸ I)) hc
  have probe (a : Fin 3) := congrArg (fun x => (simple k hk).smul ((quotientCurrent k hk) a) 1 x) hv
  simp only [Fin.sum_univ_three] at probe
  have h0 : c 0 = 0 := by
    have h := probe 2
    norm_num [PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
      (quotientCurrent_pole k hk), smul_smul, Fin.ext_iff, smul_eq_zero,
      simple_vacuum_ne_zero k hk, hk0] at h
    exact h
  have h1 : c 1 = 0 := by
    have h := probe 1
    norm_num [PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
      (quotientCurrent_pole k hk), smul_smul, Fin.ext_iff, smul_eq_zero,
      simple_vacuum_ne_zero k hk, hk0] at h
    exact h
  have h2 : c 2 = 0 := by
    have h := probe 0
    norm_num [PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
      (quotientCurrent_pole k hk), smul_smul, Fin.ext_iff, smul_eq_zero,
      simple_vacuum_ne_zero k hk, hk0] at h
    exact h
  intro i
  fin_cases i <;> assumption

/-- Every weight-one state of the simple quotient is a combination of the currents. -/
theorem quotientCurrent_span :
    Submodule.span ℂ (Set.range (quotientCurrent k hk)) = ⊤ := by
  classical
  let S := (Submodule.span ℂ (Set.range (quotientCurrent k hk))).map ((simple k hk).grading 1).subtype
  have hmem (v : WakModule k) (hv : v ∈ HSpan k 1) : (I).mkQ v ∈ S := by
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
      refine Submodule.mem_map.mpr ⟨(quotientCurrent k hk) b,
        Submodule.subset_span (Set.mem_range_self b), ?_⟩
      simp [quotientCurrent, currentState_def, wordStateA_cons, wordStateA_nil]
    | zero => simp [S]
    | add x y _ _ hx hy => simpa using S.add_mem hx hy
    | smul c x _ hx => simpa using S.smul_mem c hx
  apply top_unique
  intro x _
  obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp x.property
  have hv' : v ∈ (affineSl2VOA_closed k hk).grading 1 := hv
  rw [closed_grading] at hv'
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hmem v (gradingZA_le_hspan k 1 hv'))
  have : y = x := Subtype.ext (hyx.trans he)
  exact this ▸ hy

/-- The explicit basis `(e,h,f)` of the simple quotient's weight-one Lie algebra. -/
noncomputable def simple_weightOneBasis (hk0 : k ≠ 0) : Module.Basis (Fin 3) ℂ ((simple k hk).grading 1) :=
  Module.Basis.mk (quotientCurrent_linearIndependent k hk hk0) (by rw [(quotientCurrent_span k hk)])

/-- The abstract basis constructed from independence and spanning consists
exactly of the three quotient currents, in the order e, h, f. This lets the
concrete current-mode calculations establish the basis's sl₂ bracket relations. -/
@[simp] theorem simple_weightOneBasis_apply (hk0 : k ≠ 0) (a : Fin 3) :
    (simple_weightOneBasis k hk hk0) a = (quotientCurrent k hk) a := Module.Basis.mk_apply _ _ a

/-- The basis has the sl₂ commutation relations, including a nonzero Cartan current. -/
theorem simple_weightOneTriple (hk0 : k ≠ 0) :
    IsSl2Triple ((simple_weightOneBasis k hk hk0) 1) ((simple_weightOneBasis k hk hk0) 0) ((simple_weightOneBasis k hk hk0) 2) where
  h_ne_zero := (simple_weightOneBasis k hk hk0).ne_zero 1
  lie_e_f := by
    apply Subtype.ext
    change (simple k hk).smul _ 0 _ = _
    simp only [(simple_weightOneBasis_apply k hk hk0), (quotientCurrent_mode k hk)]
    simp [currentColor, E0F1, quotientCurrent, currentState_def]
  lie_h_e_nsmul := by
    apply Subtype.ext
    change (simple k hk).smul _ 0 _ = _
    simp only [(simple_weightOneBasis_apply k hk hk0), (quotientCurrent_mode k hk)]
    simp [currentColor, H0E1, quotientCurrent, currentState_def, two_smul]
  lie_h_f_nsmul := by
    apply Subtype.ext
    change (simple k hk).smul _ 0 _ = _
    simp only [(simple_weightOneBasis_apply k hk hk0), (quotientCurrent_mode k hk)]
    simp [currentColor, H0F1, quotientCurrent, currentState_def, two_smul]

/-- The weight-one Lie-theoretic input `Sl2BasisOnWeightOne` is constructed, not assumed. -/
theorem simple_sl2BasisOnWeightOne (hk0 : k ≠ 0) : Sl2BasisOnWeightOne (simple k hk) :=
  ⟨(simple_weightOneBasis k hk hk0), (simple_weightOneTriple k hk hk0)⟩

/-- Whitehead normalization applies to the concrete simple quotient without a basis hypothesis. -/
theorem simple_weightOneH2Vanishes (hk0 : k ≠ 0) : (simple k hk).WeightOneH2Vanishes :=
  weightOneH2Vanishes_of_sl2Basis' (simple k hk) (simple_sl2BasisOnWeightOne k hk hk0)

/-- The concrete weight-one Lie algebra has zero centre. -/
theorem simple_centrelessWeightOne (hk0 : k ≠ 0) : (simple k hk).CentrelessWeightOne :=
  centrelessWeightOne_of_sl2Basis' (simple k hk) (simple_sl2BasisOnWeightOne k hk hk0)


end VOA.AffineSl2GeneralRigidity
