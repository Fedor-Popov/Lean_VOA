/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2SingularLift
import VOA.Examples.AffineSl2SingularNorm
import VOA.Examples.AffineSl2RegularReconstruction

/-!
# Graded rigidity of the simple affine sl₂ algebra at level −4/3

The actual singular-word pairing vanishes in every deformation. Affine
commutation evaluates the same expression as 240 K (3 K + 4) (9 K + 26)
on the pure vacuum. For K = −4/3 + δ N with N² = 0, its tangent coefficient
is −13440 δ. The normalized vacuum pairing forces δ = 0. Regular reconstruction
then supplies the coboundary after the already proved weight-one normalization.
-/
namespace VOA.LQ43
open AffineVOA AffineVOA.Inst Sl2Sing Deform VertexOperatorAlgebra
open Module (End)
local notation "kk" => (-4 / 3 : ℂ)
local notation "I" => QuotVOA.maxGradedIdeal voaSl2Adm
local notation "Q" => WakModule kk ⧸ I

/-- The abstract normal-ordering current is exactly the actual lifted current
of the normalized deformation, in the original colour order. -/
theorem normalizedCurrentData_J (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : L43.grading 1, D.poleVec a b = (currentPairing a b * δ) • L43.vacuum)
    (a : Fin 3) (n : ℤ) :
    SingularNorm.J (L43_normalizedCurrentData D hD hnorm δ hδ) a n =
      liftedMode D (simpleCurrent a) n := by
  change liftedMode D (affineCurrent (basis a)) n = _
  rw [affineCurrent_basis]
  rfl

/-- Taylor evaluation of the computed cubic on the pure vacuum. The constant
term is zero at level −4/3; the tangent coefficient is the nonzero number −13440. -/
theorem singular_central_polynomial (δ : ℂ) (v : Q) :
    let K : End ℂ (Q × Q) := kk • 1 + δ • tangentShift
    (24960 : ℂ) • K (v, 0) + (27360 : ℂ) • (K ^ 2) (v, 0) +
      (6480 : ℂ) • (K ^ 3) (v, 0) = (0, (-13440 * δ) • v) := by
  dsimp only
  apply Prod.ext <;>
    simp [pow_succ, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      tangentShift, smul_add, smul_smul] <;> module

/-- The pole scalar of every normalized graded deformation is zero. The
singular-state relation, adjoint pairing identity and finite central polynomial
are all proved from the actual deformation rather than assumed as inputs. -/
theorem L43_normalized_pole_parameter_zero (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : L43.grading 1, D.poleVec a b = (currentPairing a b * δ) • L43.vacuum) :
    δ = 0 := by
  let A := L43_normalizedCurrentData D hD hnorm δ hδ
  have hJ (a : Fin 3) (n : ℤ) : SingularNorm.J A a n =
      liftedMode D (simpleCurrent a) n := normalizedCurrentData_J D hD hnorm δ hδ a n
  have hv (a : Fin 3) (n : ℤ) (hn : 0 ≤ n) :
      SingularNorm.J A a n (L43.vacuum, 0) = 0 := by
    rw [hJ]
    exact liftedMode_vacuum D n hn
  have hp := SingularNorm.singular_pairing_polynomial A (L43.vacuum, 0) hv
  have hs : SingularNorm.singularState A (L43.vacuum, 0) = liftedSingularState D := by
    simp only [SingularNorm.singularState, liftedSingularState, Fin.sum_univ_succ,
      Fin.sum_univ_zero, singularCoefficients, singularWords, Matrix.cons_val_zero,
      Matrix.cons_val_succ, liftedCurrentWord, Module.End.mul_apply, Module.End.one_apply,
      hJ, add_zero, colE, colF, colH]
    module
  have ha (x : Q × Q) : SingularNorm.adjointSingular A x = liftedSingularAdjoint D x := by
    simp only [SingularNorm.adjointSingular, liftedSingularAdjoint, Fin.sum_univ_succ,
      Fin.sum_univ_zero, singularCoefficients, singularWords, Matrix.cons_val_zero,
      Matrix.cons_val_succ, liftedAdjointCurrentWord, Module.End.mul_apply,
      Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      LinearMap.add_apply, map_neg, hJ, add_zero, colE, colF, colH, neg_neg]
    module
  rw [hs, ha, hJ] at hp
  change liftedSingularAdjoint D (loweredLiftedSingularState D) = _ at hp
  have hK : A.central = kk • (1 : End ℂ (Q × Q)) + δ • tangentShift := rfl
  rw [pow_one, hK, singular_central_polynomial] at hp
  have hz := (actual_singular_pairing_obstruction D).2
  rw [hp] at hz
  have hB : form43.form L43.vacuum L43.vacuum = 1 :=
    canonicalInvariantForm_normalized L43_vacuum_ne_zero L43_quasiPrimary
  simp only [map_smul, smul_eq_mul, hB] at hz
  linear_combination -hz / 13440

/-- The normalized pole-vanishing input for affine rigidity is
proved for every normalized graded deformation of the actual simple quotient. -/
theorem L43_normalisedPoleVanishes : NormalisedPoleVanishes L43 := by
  intro D hD hnorm a ha b hb
  obtain ⟨δ, hδ, _⟩ := L43_existsUnique_pole_parameter D hD hnorm
  have hz := L43_normalized_pole_parameter_zero D hD hnorm δ hδ
  simpa only [hz, mul_zero, zero_smul] using hδ ⟨a, ha⟩ ⟨b, hb⟩

/-- Every graded first-order deformation of L_{−4/3}(sl₂) is a coboundary.
Weight-one normalization, normalized pole vanishing and regular reconstruction
are all discharged by proved results; there is no residual rigidity input. -/
theorem L43_graded_rigidity : Deform.IsRigidGraded L43 :=
  L43_isRigidGraded_of_normalisedPoleVanishes L43_normalisedPoleVanishes

end VOA.LQ43
