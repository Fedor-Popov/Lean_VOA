/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2NormalizedRepresentation

/-!
# Actual deformed singular words and their adjoint pairing

The ordinary singular state vanishes in the simple quotient. Its word expression
in lifted currents need not vanish: it is a pure tangent state. The adjoint word
expression, paired against the vacuum, annihilates every pure tangent state.
This provides a genuine identity for actual deformation operators. Computing
that identity from the normalized affine commutators remains a separate step.
-/
namespace VOA.LQ43
open AffineVOA AffineVOA.Inst Sl2Sing Deform VertexOperatorAlgebra
open Module (End)
local notation "kk" => (-4 / 3 : ℂ)
local notation "I" => QuotVOA.maxGradedIdeal voaSl2Adm
local notation "Q" => WakModule kk ⧸ I

/-- The original colour order (e,f,h), now as states of the simple quotient. -/
noncomputable def simpleCurrent (a : Fin 3) : Q := (I).mkQ (currentState kk a)

/-- Quotient currents still have weight one. -/
theorem simpleCurrent_mem (a : Fin 3) : simpleCurrent a ∈ L43.grading 1 :=
  Submodule.mem_map.mpr ⟨_, currentState_mem_grading kk admLevel_noncritical a, rfl⟩

/-- Current modes commute with the projection to the simple quotient. -/
theorem simpleCurrent_mode_mkQ (a : Fin 3) (n : ℤ) (v : WakModule kk) :
    L43.smul (simpleCurrent a) n ((I).mkQ v) = (I).mkQ (J kk a n v) := by
  change (QuotVOA.quotientVOA voaSl2Adm I
    (QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm)
    (QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm)).smul _ n _ = _
  rw [simpleCurrent, QuotVOA.quotientVOA_mkQ_smul, smul_currentState_adm]

/-- Quasi-primarity descends to the simple quotient by lifting a weight-one state
through the homogeneous quotient map. -/
theorem L43_quasiPrimary (v : Q) (hv : v ∈ L43.grading 1) : L43.L 1 v = 0 := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
  change (I).mkQ (voaSl2Adm.L 1 x) = 0
  rw [quasiPrimary x hx, map_zero]

/-- The canonical normalized invariant form on the simple affine algebra. It is
constructed using its nonzero vacuum and the proved quasi-primarity condition. -/
noncomputable def form43 : InvariantForm L43 :=
  canonicalInvariantForm L43_vacuum_ne_zero L43_quasiPrimary

/-- An ordinary current word, with the leftmost letter acting last. -/
noncomputable def currentWord : List (Fin 3 × ℤ) → End ℂ Q
  | [] => 1
  | an :: l => mode (L43.Y (simpleCurrent an.1)) an.2 * currentWord l

/-- The same ordered word in the actual lifted deformation operators. -/
noncomputable def liftedCurrentWord (D : FirstOrderDeformation L43) :
    List (Fin 3 × ℤ) → End ℂ (Q × Q)
  | [] => 1
  | an :: l => liftedMode D (simpleCurrent an.1) an.2 * liftedCurrentWord D l

/-- Ordinary adjoint words reverse the operator order, negate each index, and
supply a minus sign per weight-one current. -/
noncomputable def adjointCurrentWord : List (Fin 3 × ℤ) → End ℂ Q
  | [] => 1
  | an :: l => adjointCurrentWord l * (-mode (L43.Y (simpleCurrent an.1)) (-an.2))

/-- The adjoint word expression evaluated in lifted currents. No deformed
invariant form is assumed: this is an explicit expression in known operators. -/
noncomputable def liftedAdjointCurrentWord (D : FirstOrderDeformation L43) :
    List (Fin 3 × ℤ) → End ℂ (Q × Q)
  | [] => 1
  | an :: l => liftedAdjointCurrentWord D l * (-liftedMode D (simpleCurrent an.1) (-an.2))

/-- Taking the constant coordinate of a lifted word recovers its ordinary action. -/
theorem liftedCurrentWord_fst (D : FirstOrderDeformation L43)
    (l : List (Fin 3 × ℤ)) (x : Q × Q) :
    (liftedCurrentWord D l x).1 = currentWord l x.1 := by
  induction l with
  | nil => rfl
  | cons an l ih =>
    change L43.smul _ _ (liftedCurrentWord D l x).1 = _
    rw [ih]
    rfl

/-- On a pure tangent state, all deformation corrections disappear from a word. -/
theorem liftedCurrentWord_tangent (D : FirstOrderDeformation L43)
    (l : List (Fin 3 × ℤ)) (x : Q) :
    liftedCurrentWord D l (0, x) = (0, currentWord l x) := by
  induction l with
  | nil => rfl
  | cons an l ih =>
    simp only [liftedCurrentWord, Module.End.mul_apply, ih, liftedMode_apply,
      PreVertexAlgebra.smul_zero_right, FirstOrderDeformation.smul₁_zero_right, zero_add]
    rfl

/-- The same pure tangent rule for the reverse-order adjoint expression. -/
theorem liftedAdjointCurrentWord_tangent (D : FirstOrderDeformation L43)
    (l : List (Fin 3 × ℤ)) (x : Q) :
    liftedAdjointCurrentWord D l (0, x) = (0, adjointCurrentWord l x) := by
  induction l generalizing x with
  | nil => rfl
  | cons an l ih =>
    simp only [liftedAdjointCurrentWord, Module.End.mul_apply, LinearMap.neg_apply,
      liftedMode_apply, PreVertexAlgebra.smul_zero_right,
      FirstOrderDeformation.smul₁_zero_right, zero_add, Prod.neg_mk, neg_zero]
    rw [ih]
    rfl

/-- Full invariance moves any finite current word across the canonical form.
The one-current step is the weight-one adjointness already established for VOAs. -/
theorem form43_currentWord (l : List (Fin 3 × ℤ)) (x y : Q) :
    form43.form (currentWord l x) y = form43.form x (adjointCurrentWord l y) := by
  have hB : form43.IsFullyInvariant :=
    canonicalInvariantForm_isFullyInvariant L43_vacuum_ne_zero L43_quasiPrimary
  induction l generalizing x y with
  | nil => rfl
  | cons an l ih =>
    change form43.form (L43.smul (simpleCurrent an.1) an.2 (currentWord l x)) y = _
    rw [weightOne_adj hB (simpleCurrent_mem an.1)
      (L43_quasiPrimary _ (simpleCurrent_mem an.1)), ih]
    change -form43.form x (adjointCurrentWord l
      (L43.smul (simpleCurrent an.1) (-an.2) y)) =
      form43.form x (adjointCurrentWord l (-(L43.smul (simpleCurrent an.1) (-an.2) y)))
    rw [map_neg, map_neg]

/-- The five creation words in the integral singular-vector expression. Indices
are literal current modes, not creation degrees minus one. -/
def singularWords : Fin 5 → List (Fin 3 × ℤ) :=
  ![[(colE, -3)], [(colE, -2), (colH, -1)], [(colH, -2), (colE, -1)],
    [(colE, -1), (colE, -1), (colF, -1)], [(colE, -1), (colH, -1), (colH, -1)]]

/-- Integer coefficients of the singular state in this precise word order. -/
def singularCoefficients : Fin 5 → ℂ := ![20, -12, -6, 36, 9]

/-- The ordinary combination of these five words is zero in the simple quotient. -/
theorem singularWords_relation :
    ∑ i, singularCoefficients i • currentWord (singularWords i) L43.vacuum = 0 := by
  have h := mkQ_sl2Singular_eq_zero
  simp only [sl2Singular, ansatz, map_add, map_smul] at h
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, singularWords,
    singularCoefficients, Matrix.cons_val_zero, Matrix.cons_val_succ, currentWord,
    Module.End.mul_apply, Module.End.one_apply, ← PreVertexAlgebra.smul_def,
    show L43.vacuum = (I).mkQ (vacuumA kk) from rfl,
    simpleCurrent_mode_mkQ, M1, M2, M3, M4, M5, add_assoc] using h

/-- Evaluate the actual lifted singular word combination on the pure vacuum.
This is not asserted to be zero; its constant coordinate alone is known to vanish. -/
noncomputable def liftedSingularState (D : FirstOrderDeformation L43) : Q × Q :=
  ∑ i, singularCoefficients i • liftedCurrentWord D (singularWords i) (L43.vacuum, 0)

/-- The lifted singular state is a pure tangent state, by the actual quotient
relation and the constant-coordinate formula for lifted words. -/
theorem liftedSingularState_fst (D : FirstOrderDeformation L43) :
    (liftedSingularState D).1 = 0 := by
  simpa only [liftedSingularState, Prod.fst_sum, Prod.smul_fst,
    liftedCurrentWord_fst] using singularWords_relation

/-- The adjoint expression of the singular state, evaluated using the lifted
currents. It is a finite linear combination of positive-mode words. -/
noncomputable def liftedSingularAdjoint (D : FirstOrderDeformation L43) : End ℂ (Q × Q) :=
  ∑ i, singularCoefficients i • liftedAdjointCurrentWord D (singularWords i)

/-- The ordinary adjoint singular word has zero vacuum pairing on every state.
This follows from the singular STATE relation by actual current adjointness. -/
theorem singularAdjoint_pairing_zero (v : Q) :
    ∑ i, singularCoefficients i *
      form43.form L43.vacuum (adjointCurrentWord (singularWords i) v) = 0 := by
  have h := congrArg (fun z : Q => form43.form z v) singularWords_relation
  simpa only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, map_zero, LinearMap.zero_apply, form43_currentWord] using h

/-- The lifted adjoint singular expression annihilates the vacuum pairing of
every pure tangent state, in both coordinates. The deformation corrections
vanish on such an input, leaving the proved ordinary adjoint relation. -/
theorem liftedSingularAdjoint_pairing_tangent (D : FirstOrderDeformation L43) (v : Q) :
    form43.form L43.vacuum (liftedSingularAdjoint D (0, v)).1 = 0 ∧
    form43.form L43.vacuum (liftedSingularAdjoint D (0, v)).2 = 0 := by
  simp only [liftedSingularAdjoint, LinearMap.sum_apply, LinearMap.smul_apply,
    liftedAdjointCurrentWord_tangent, Prod.fst_sum, Prod.snd_sum,
    Prod.smul_fst, Prod.smul_snd, smul_zero, Finset.sum_const_zero, map_zero,
    map_sum, map_smul, smul_eq_mul, singularAdjoint_pairing_zero, and_self]

/-- Apply two horizontal lowering modes to the lifted singular state. This
selects the opposite charge for pairing with its adjoint; it remains a pure
tangent state because the original singular state is zero in the quotient. -/
noncomputable def loweredLiftedSingularState (D : FirstOrderDeformation L43) : Q × Q :=
  liftedCurrentWord D [(colF, 0), (colF, 0)] (liftedSingularState D)

/-- Horizontal lowering does not restore a constant term to the singular lift. -/
theorem loweredLiftedSingularState_fst (D : FirstOrderDeformation L43) :
    (loweredLiftedSingularState D).1 = 0 := by
  rw [loweredLiftedSingularState, liftedCurrentWord_fst, liftedSingularState_fst, map_zero]

/-- An actual finite word obstruction for every deformation of L43: pair the
adjoint singular expression with the twice-lowered lifted singular expression.
Both coordinates vanish. Identifying this word calculation with a polynomial
in the tangent central level remains necessary to force the pole scalar to zero. -/
theorem actual_singular_pairing_obstruction (D : FirstOrderDeformation L43) :
    form43.form L43.vacuum
      (liftedSingularAdjoint D (loweredLiftedSingularState D)).1 = 0 ∧
    form43.form L43.vacuum
      (liftedSingularAdjoint D (loweredLiftedSingularState D)).2 = 0 := by
  have hx : loweredLiftedSingularState D = (0, (loweredLiftedSingularState D).2) := by
    exact Prod.ext (loweredLiftedSingularState_fst D) rfl
  rw [hx]
  exact liftedSingularAdjoint_pairing_tangent D _

end VOA.LQ43
