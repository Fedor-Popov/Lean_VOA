/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2GeneralNormalizedRepresentation

/-!
# Actual deformed singular words and their adjoint pairing

The ordinary singular state vanishes in the simple quotient. Its word expression
in lifted currents need not vanish: it is a pure tangent state. The adjoint word
expression, paired against the vacuum, annihilates every pure tangent state.
This provides a genuine identity for actual deformation operators. Computing
that identity from the normalized affine commutators remains a separate step.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.Inst Sl2Sing Deform VertexOperatorAlgebra
open Module (End)
variable (k : ℂ) (hk : k + 2 ≠ 0)
local notation "I" => QuotVOA.maxGradedIdeal (universal k hk)
local notation "Q" => WakModule k ⧸ I

/-- The original colour order (e,f,h), now as states of the simple quotient. -/
noncomputable def simpleCurrent (a : Fin 3) : Q := (I).mkQ (currentState k a)

/-- Quotient currents still have weight one. -/
theorem simpleCurrent_mem (a : Fin 3) : simpleCurrent k hk a ∈ (simple k hk).grading 1 :=
  Submodule.mem_map.mpr ⟨_, currentState_mem_grading k hk a, rfl⟩

/-- Current modes commute with the projection to the simple quotient. -/
theorem simpleCurrent_mode_mkQ (a : Fin 3) (n : ℤ) (v : WakModule k) :
    (simple k hk).smul (simpleCurrent k hk a) n ((I).mkQ v) = (I).mkQ (J k a n v) := by
  change (QuotVOA.quotientVOA (universal k hk) I
    (QuotVOA.maxGradedIdeal_isIdeal (universal k hk))
    (QuotVOA.maxGradedIdeal_isGradedIdeal (universal k hk))).smul _ n _ = _
  rw [simpleCurrent, QuotVOA.quotientVOA_mkQ_smul]
  exact congrArg (I).mkQ (smul_currentState_eq_J k hk a n v)

/-- Quasi-primarity descends to the simple quotient by lifting a weight-one state
through the homogeneous quotient map. -/
theorem simple_quasiPrimary (v : Q) (hv : v ∈ (simple k hk).grading 1) : (simple k hk).L 1 v = 0 := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
  change (I).mkQ ((universal k hk).L 1 x) = 0
  rw [LQ43.L1_grading_one k hk x hx, map_zero]

/-- The canonical normalized invariant form on the simple affine algebra. It is
constructed using its nonzero vacuum and the proved quasi-primarity condition. -/
noncomputable def simpleForm : InvariantForm (simple k hk) :=
  canonicalInvariantForm (simple_vacuum_ne_zero k hk) (simple_quasiPrimary k hk)

/-- An ordinary current word, with the leftmost letter acting last. -/
noncomputable def currentWord : List (Fin 3 × ℤ) → End ℂ Q
  | [] => 1
  | an :: l => mode ((simple k hk).Y (simpleCurrent k hk an.1)) an.2 * currentWord l

/-- The same ordered word in the actual lifted deformation operators. -/
noncomputable def liftedCurrentWord (D : FirstOrderDeformation (simple k hk)) :
    List (Fin 3 × ℤ) → End ℂ (Q × Q)
  | [] => 1
  | an :: l => liftedMode D (simpleCurrent k hk an.1) an.2 * liftedCurrentWord D l

/-- Ordinary adjoint words reverse the operator order, negate each index, and
supply a minus sign per weight-one current. -/
noncomputable def adjointCurrentWord : List (Fin 3 × ℤ) → End ℂ Q
  | [] => 1
  | an :: l => adjointCurrentWord l * (-mode ((simple k hk).Y (simpleCurrent k hk an.1)) (-an.2))

/-- The adjoint word expression evaluated in lifted currents. No deformed
invariant form is assumed: this is an explicit expression in known operators. -/
noncomputable def liftedAdjointCurrentWord (D : FirstOrderDeformation (simple k hk)) :
    List (Fin 3 × ℤ) → End ℂ (Q × Q)
  | [] => 1
  | an :: l => liftedAdjointCurrentWord D l * (-liftedMode D (simpleCurrent k hk an.1) (-an.2))

/-- Taking the constant coordinate of a lifted word recovers its ordinary action. -/
theorem liftedCurrentWord_fst (D : FirstOrderDeformation (simple k hk))
    (l : List (Fin 3 × ℤ)) (x : Q × Q) :
    (liftedCurrentWord k hk D l x).1 = currentWord k hk l x.1 := by
  induction l with
  | nil => rfl
  | cons an l ih =>
    change (simple k hk).smul _ _ (liftedCurrentWord k hk D l x).1 = _
    rw [ih]
    rfl

/-- On a pure tangent state, all deformation corrections disappear from a word. -/
theorem liftedCurrentWord_tangent (D : FirstOrderDeformation (simple k hk))
    (l : List (Fin 3 × ℤ)) (x : Q) :
    liftedCurrentWord k hk D l (0, x) = (0, currentWord k hk l x) := by
  induction l with
  | nil => rfl
  | cons an l ih =>
    simp only [liftedCurrentWord, Module.End.mul_apply, ih, liftedMode_apply,
      PreVertexAlgebra.smul_zero_right, FirstOrderDeformation.smul₁_zero_right, zero_add]
    rfl

/-- The same pure tangent rule for the reverse-order adjoint expression. -/
theorem liftedAdjointCurrentWord_tangent (D : FirstOrderDeformation (simple k hk))
    (l : List (Fin 3 × ℤ)) (x : Q) :
    liftedAdjointCurrentWord k hk D l (0, x) = (0, adjointCurrentWord k hk l x) := by
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
theorem simpleForm_currentWord (l : List (Fin 3 × ℤ)) (x y : Q) :
    (simpleForm k hk).form (currentWord k hk l x) y = (simpleForm k hk).form x (adjointCurrentWord k hk l y) := by
  have hB : (simpleForm k hk).IsFullyInvariant :=
    canonicalInvariantForm_isFullyInvariant (simple_vacuum_ne_zero k hk) (simple_quasiPrimary k hk)
  induction l generalizing x y with
  | nil => rfl
  | cons an l ih =>
    change (simpleForm k hk).form ((simple k hk).smul (simpleCurrent k hk an.1) an.2 (currentWord k hk l x)) y = _
    rw [LQ43.weightOne_adj hB (simpleCurrent_mem k hk an.1)
      (simple_quasiPrimary k hk _ (simpleCurrent_mem k hk an.1)), ih]
    change -(simpleForm k hk).form x (adjointCurrentWord k hk l
      ((simple k hk).smul (simpleCurrent k hk an.1) (-an.2) y)) =
      (simpleForm k hk).form x (adjointCurrentWord k hk l (-((simple k hk).smul (simpleCurrent k hk an.1) (-an.2) y)))
    rw [map_neg, map_neg]

/-- The canonical form assigns norm one to the simple vacuum at any
noncritical level. This fixes the normalization of all subsequent pairings. -/
theorem simpleForm_normalized : (simpleForm k hk).Normalized :=
  canonicalInvariantForm_normalized (simple_vacuum_ne_zero k hk) (simple_quasiPrimary k hk)

/-- Any ordinary finite current relation has zero adjoint vacuum row on every
state. This uses only the original invariant form, with no deformation of it. -/
theorem relation_adjoint_pairing_zero {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (w : ι → List (Fin 3 × ℤ))
    (hr : ∑ i, c i • currentWord k hk (w i) (simple k hk).vacuum = 0)
    (v : Q) :
    ∑ i, c i * (simpleForm k hk).form (simple k hk).vacuum
      (adjointCurrentWord k hk (w i) v) = 0 := by
  have h := congrArg (fun z : Q => (simpleForm k hk).form z v) hr
  simpa only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, map_zero, LinearMap.zero_apply, simpleForm_currentWord] using h

/-- Two ordinary relations give a vanishing actual first-order pairing: the
column relation lifts to a pure tangent state; the row relation annihilates its
vacuum pairing. The two relations may have different coefficients and words. -/
theorem actual_word_relation_obstruction (D : FirstOrderDeformation (simple k hk))
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℂ) (u : ι → List (Fin 3 × ℤ))
    (d : κ → ℂ) (w : κ → List (Fin 3 × ℤ))
    (hc : ∑ i, c i • currentWord k hk (u i) (simple k hk).vacuum = 0)
    (hd : ∑ j, d j • currentWord k hk (w j) (simple k hk).vacuum = 0) :
    let v := ∑ j, d j • liftedCurrentWord k hk D (w j) ((simple k hk).vacuum, 0)
    (simpleForm k hk).form (simple k hk).vacuum
      ((∑ i, c i • liftedAdjointCurrentWord k hk D (u i)) v).1 = 0 ∧
    (simpleForm k hk).form (simple k hk).vacuum
      ((∑ i, c i • liftedAdjointCurrentWord k hk D (u i)) v).2 = 0 := by
  dsimp only
  let v := ∑ j, d j • liftedCurrentWord k hk D (w j) ((simple k hk).vacuum, 0)
  have hv : v.1 = 0 := by
    simpa only [v, Prod.fst_sum, Prod.smul_fst, liftedCurrentWord_fst] using hd
  have he : v = (0, v.2) := Prod.ext hv rfl
  change (simpleForm k hk).form _ ((∑ i, c i • liftedAdjointCurrentWord k hk D (u i)) v).1 = 0 ∧
    (simpleForm k hk).form _ ((∑ i, c i • liftedAdjointCurrentWord k hk D (u i)) v).2 = 0
  rw [he]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, liftedAdjointCurrentWord_tangent,
    Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_zero,
    Finset.sum_const_zero, map_zero, map_sum, map_smul, smul_eq_mul,
    relation_adjoint_pairing_zero k hk c u hc, and_self]

end VOA.AffineSl2GeneralRigidity
