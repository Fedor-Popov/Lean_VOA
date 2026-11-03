/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroNormalOrdering
import VOA.Examples.VirasoroRigidityTangent

/-!
# Uniform actual vacuum-pairing polynomials

Normal ordering gives one polynomial for every finite mode word. Positive-weight
creation terms have zero vacuum pairing. The central powers act through the
actual dual scalar c+δt, so evaluating the polynomial gives BOTH coordinates of
the actual normalized pairing. No deformed invariant form is introduced.
-/
namespace VOA.VirDeformModes.NormalOrdering
open Module (End)
open VertexOperatorAlgebra Deform TrivSqZeroExt Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}

/-- Pair each coordinate with the ordinary vacuum and package the results as
a dual number. This uses an ordinary invariant form on the original algebra. -/
noncomputable def vacuumPair (B : InvariantForm W) : (V × V) →ₗ[ℂ] DualNumber ℂ where
  toFun x := inl (B.form W.vacuum x.1) + inr (B.form W.vacuum x.2)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- The coordinate formula for the dual-number vacuum pairing. -/
theorem vacuumPair_apply (B : InvariantForm W) (x : V × V) :
    vacuumPair B x = inl (B.form W.vacuum x.1) + inr (B.form W.vacuum x.2) := rfl

/-- Pairing intertwines actual dual-scalar block action with multiplication
of dual numbers, by ordinary bilinearity in each coordinate. -/
theorem vacuumPair_scalar (B : InvariantForm W) (z : DualNumber ℂ) (x : V × V) :
    vacuumPair B (dualScalarAction z x) = z * vacuumPair B x := by
  ext <;> simp [vacuumPair_apply, dualScalarAction_apply, smul_eq_mul] <;> ring

/-- A normalized creation word on the pure vacuum is homogeneous in both
coordinates, at the sum of its positive creation energies. -/
theorem creationWord_grading (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (β : ℂ) (w : List ℕ) :
    (creationWord (normalizedL D β) w (W.vacuum,0)).1 ∈ W.grading (VirModule.energyVir w) ∧
    (creationWord (normalizedL D β) w (W.vacuum,0)).2 ∈ W.grading (VirModule.energyVir w) := by
  induction w with
  | nil => exact ⟨W.vacuum_mem, Submodule.zero_mem _⟩
  | cons i w ih =>
    simp only [creationWord, List.map_cons, virWord, Module.End.mul_apply]
    have h := normalizedL_mem_grading D hD β (-(i:ℤ)-2) (VirModule.energyVir w)
      (creationWord (normalizedL D β) w (W.vacuum,0)) ih
    have he : (VirModule.energyVir (i::w) : ℤ) =
        (VirModule.energyVir w : ℤ) - (-(i:ℤ)-2) := by
      simp only [VirModule.energyVir_cons, Nat.cast_add, Nat.cast_ofNat]; omega
    rw [he]
    exact h

/-- Only the empty creation word has nonzero vacuum pairing. Every nonempty
word has positive weight, so ordinary graded orthogonality kills both coordinates. -/
theorem vacuumPair_creation (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (β : ℂ) (B : InvariantForm W) (hB : B.Normalized) (w : List ℕ) :
    vacuumPair B (creationWord (normalizedL D β) w (W.vacuum,0)) =
      if w=[] then 1 else 0 := by
  cases w with
  | nil =>
    change inl (B.form W.vacuum W.vacuum) + inr (B.form W.vacuum 0) = 1
    rw [hB, map_zero]
    simp
  | cons i w =>
    obtain ⟨h1,h2⟩ := creationWord_grading D hD β (i::w)
    have hn : (0:ℤ) ≠ (VirModule.energyVir (i::w):ℤ) := by
      simp only [VirModule.energyVir_cons, Nat.cast_add, Nat.cast_ofNat]; omega
    rw [vacuumPair_apply, B.orthogonal_of_ne hn W.vacuum_mem h1,
      B.orthogonal_of_ne hn W.vacuum_mem h2]
    simp

/-- Retain the empty-word central powers of a normal form as a polynomial.
All other terms are invisible to vacuum pairing, regardless of the charge. -/
noncomputable def centralPolynomial : NormalForm →ₗ[ℂ] Polynomial ℂ :=
  Finsupp.linearCombination ℂ (fun t => if t.2=[] then X^t.1 else 0)

/-- The vacuum-pairing polynomial of an arbitrary finite mode word. -/
noncomputable def wordPolynomial (w : List ℤ) : Polynomial ℂ :=
  centralPolynomial (wordNormal w)

/-- Evaluation of a normal form followed by actual vacuum pairing equals
polynomial evaluation at the actual dual central scalar. The creation terms
vanish by grading, and every central power contributes its dual scalar power. -/
theorem vacuumPair_evaluate (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (β : ℂ) (B : InvariantForm W) (hB : B.Normalized)
    (A : CentralVirasoroData (V × V)) (hA : A.L = normalizedL D β)
    (z : DualNumber ℂ) (hK : A.central = dualScalarAction z) (f : NormalForm) :
    vacuumPair B (evaluate A (W.vacuum,0) f) = (centralPolynomial f).aeval z := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t a =>
    rw [evaluate_single, map_smul]
    have hp : A.central^t.1 = dualScalarAction (z^t.1) := by rw [hK, map_pow]
    rw [hp, hA, vacuumPair_scalar, vacuumPair_creation D hD β B hB]
    simp only [centralPolynomial, Finsupp.linearCombination_single, map_smul]
    split_ifs <;> simp

/-- UNIFORM actual word-pairing formula, valid at every word length and
weight. Its right-hand side is a constructed polynomial evaluated on the dual
central scalar; this is not a determinant-preservation assumption. -/
theorem vacuumPair_word (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (β : ℂ) (B : InvariantForm W) (hB : B.Normalized)
    (A : CentralVirasoroData (V × V)) (hA : A.L = normalizedL D β)
    (z : DualNumber ℂ) (hK : A.central = dualScalarAction z) (w : List ℤ) :
    vacuumPair B (virWord (normalizedL D β) w (W.vacuum,0)) =
      (wordPolynomial w).aeval z := by
  have hv (n : ℤ) (hn : -1 ≤ n) : A.L n (W.vacuum,0) = 0 := by
    rw [hA]; exact normalizedL_vacuum D β n hn
  rw [← hA, ← evaluate_wordNormal A (W.vacuum,0) hv]
  exact vacuumPair_evaluate D hD β B hB A hA z hK _

/-- For every graded deformation of every simple Virasoro algebra, arbitrary
normalized word pairings have their canonical polynomial value at c+δt,
where δ=2α−βc is extracted from the actual conformal self-products. -/
theorem simple_normalized_word_pairing (c : ℂ)
    (D : FirstOrderDeformation (VirSimple.virasoroSimple c)) (hD : D.IsGraded)
    (α β : ℂ)
    (ha : D.smul₁ (VirSimple.virasoroSimple c).conformalVector 3
      (VirSimple.virasoroSimple c).conformalVector = α • (VirSimple.virasoroSimple c).vacuum)
    (hb : D.smul₁ (VirSimple.virasoroSimple c).conformalVector 1
      (VirSimple.virasoroSimple c).conformalVector = β • (VirSimple.virasoroSimple c).conformalVector)
    (w : List ℤ) :
    vacuumPair (VirQuotForm.Bsimp c)
      (virWord (normalizedL D β) w ((VirSimple.virasoroSimple c).vacuum,0)) =
        (wordPolynomial w).aeval (inl c + inr (2*α-β*c)) := by
  let A := normalizedData D hD (VirSimple.virasoroSimple_grading_one c) α β ha hb
  apply vacuumPair_word D hD β (VirQuotForm.Bsimp c) (VirQuotForm.Bsimp_normalized c) A rfl
  simp only [dualScalarAction, fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
    add_zero, zero_add, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, normalizedData]
  rfl

/-- Extracting the tangent coordinate gives the derivative of the same
uniform polynomial times the actual central variation. -/
theorem simple_normalized_word_tangent (c : ℂ)
    (D : FirstOrderDeformation (VirSimple.virasoroSimple c)) (hD : D.IsGraded)
    (α β : ℂ)
    (ha : D.smul₁ (VirSimple.virasoroSimple c).conformalVector 3
      (VirSimple.virasoroSimple c).conformalVector = α • (VirSimple.virasoroSimple c).vacuum)
    (hb : D.smul₁ (VirSimple.virasoroSimple c).conformalVector 1
      (VirSimple.virasoroSimple c).conformalVector = β • (VirSimple.virasoroSimple c).conformalVector)
    (w : List ℤ) :
    (VirQuotForm.Bsimp c).form (VirSimple.virasoroSimple c).vacuum
      (virWord (normalizedL D β) w ((VirSimple.virasoroSimple c).vacuum,0)).2 =
        (wordPolynomial w).derivative.eval c * (2*α-β*c) := by
  have h := congrArg TrivSqZeroExt.snd (simple_normalized_word_pairing c D hD α β ha hb w)
  rw [VirRigidTangent.aeval_dual] at h
  simpa [vacuumPair_apply] using h

/-- Scalar specialization agrees with the actual ordinary vacuum pairing
whenever weight one vanishes. Apply the universal construction to the zero
deformation; no existence of a nontrivial deformation is assumed. -/
theorem wordPolynomial_eval (h1 : W.grading 1 = ⊥)
    (B : InvariantForm W) (hB : B.Normalized) (w : List ℤ) :
    (wordPolynomial w).eval W.centralCharge = B.form W.vacuum (virWord W.L w W.vacuum) := by
  let D := zeroDeformation W
  have hD : D.IsGraded := by
    intro p q u hu v hv n
    exact Submodule.zero_mem _
  have ha : D.smul₁ W.conformalVector 3 W.conformalVector = (0:ℂ) • W.vacuum := by
    simp [D, FirstOrderDeformation.smul₁, zeroDeformation]
  have hb : D.smul₁ W.conformalVector 1 W.conformalVector = (0:ℂ) • W.conformalVector := by
    simp [D, FirstOrderDeformation.smul₁, zeroDeformation]
  let A := normalizedData D hD h1 0 0 ha hb
  have hK : A.central = dualScalarAction (inl W.centralCharge) := by
    simp only [dualScalarAction, fst_inl, snd_inl, zero_smul, add_zero,
      AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change W.centralCharge • 1 + (2*0-0*W.centralCharge) • tangentShift = _
    simp
  have h := congrArg TrivSqZeroExt.fst
    (vacuumPair_word D hD 0 B hB A rfl (inl W.centralCharge) hK w)
  have he : (wordPolynomial w).aeval (inl W.centralCharge : DualNumber ℂ) =
      inl ((wordPolynomial w).eval W.centralCharge) :=
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval _ _
  rw [he] at h
  simpa [vacuumPair_apply, virWord_fst] using h.symm

/-- The constructed word polynomials reproduce ordinary invariant-form
pairings of arbitrary universal Virasoro descendants. This identifies the
uniform construction with canonical Gram entries at every level. -/
theorem universal_gram_entry (c : ℂ) (u v : List ℤ) :
    (wordPolynomial (u.reverse.map Neg.neg ++ v)).eval c =
      (VirGram4.canB c).form
        (virWord (VirModule.virasoroVOA c).L u (VirModule.vacVec c))
        (virWord (VirModule.virasoroVOA c).L v (VirModule.vacVec c)) := by
  rw [virWord_adjoint, ← Module.End.mul_apply, ← virWord_append]
  exact wordPolynomial_eval (W := VirModule.virasoroVOA c)
    (VirDefLow.gradingVir_one_eq_bot c) (VirGram4.canB c) (VirGram4.canB_normalized c) _

end VOA.VirDeformModes.NormalOrdering
