/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroDeformationModes
import VOA.Examples.VirasoroQuotientForm
import VOA.Examples.LeeYangProper

/-!
# Actual weight-four vacuum pairings with a moving central charge

The computations retain the central operator K throughout. They therefore apply
to the actual first-order modes, not just to a formal substitution into a scalar
Gram determinant. Only the Virasoro commutators and vacuum annihilation are used.
-/
namespace VOA.VirDeformModes
open Module (End)
open VertexOperatorAlgebra Deform
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable (A : CentralVirasoroData E)

/-- Move a Virasoro mode past another while retaining the central operator. -/
theorem vir_push (m n : ℤ) (x : E) :
    A.L m (A.L n x) = A.L n (A.L m x) + ((m : ℂ)-n) • A.L (m+n) x +
      if m+n=0 then (((m : ℂ)^3-m)/12) • A.central x else 0 := by
  have h := LinearMap.congr_fun (A.comm m n) x
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h
  split_ifs at h ⊢ <;> simp only [LinearMap.smul_apply, LinearMap.zero_apply] at h
  all_goals rw [sub_eq_iff_eq_add] at h
  all_goals rw [h]; abel

/-- A central insertion can be moved through a Virasoro mode. -/
theorem vir_central (n : ℤ) (x : E) :
    A.L n (A.central x) = A.central (A.L n x) :=
  (LinearMap.congr_fun (A.central_comm n) x).symm

variable (v : E) (hv : ∀ n : ℤ, -1 ≤ n → A.L n v = 0)
include hv

/-- The weight of the one-part weight-two vacuum descendant is two. -/
theorem vir_zero_neg_two : A.L 0 (A.L (-2) v) = (2 : ℂ) • A.L (-2) v := by
  rw [vir_push]
  norm_num
  simp [hv]

/-- The lowest nonzero vacuum pairing is K/2, as an operator identity on the vacuum. -/
theorem vir_two_neg_two : A.L 2 (A.L (-2) v) = (1/2 : ℂ) • A.central v := by
  rw [vir_push]
  norm_num
  simp [hv]

/-- Lowering the weight-four one-part descendant by L₂ gives six times L₋₂v. -/
theorem vir_two_neg_four : A.L 2 (A.L (-4) v) = (6 : ℂ) • A.L (-2) v := by
  rw [vir_push]
  norm_num
  simp [hv]

/-- L₄ kills the weight-two descendant; this also checks the vacuum boundary. -/
theorem vir_four_neg_two : A.L 4 (A.L (-2) v) = 0 := by
  rw [vir_push]
  norm_num
  simp [hv]

/-- The diagonal pairing for L₋₄v is 5K. -/
theorem vir_four_neg_four : A.L 4 (A.L (-4) v) = (5 : ℂ) • A.central v := by
  rw [vir_push]
  norm_num
  simp [hv]

/-- One L₂ on the two-part descendant gives (8+K)L₋₂v. -/
theorem vir_two_double : A.L 2 (A.L (-2) (A.L (-2) v)) =
    (8 : ℂ) • A.L (-2) v + A.central (A.L (-2) v) := by
  rw [vir_push]
  norm_num
  rw [vir_two_neg_two A v hv, vir_zero_neg_two A v hv]
  simp only [map_smul, vir_central]
  module

/-- The first diagonal weight-four entry is K²/2+4K. -/
theorem vir_gram4_11 : A.L 2 (A.L 2 (A.L (-2) (A.L (-2) v))) =
    (1/2 : ℂ) • A.central (A.central v) + (4 : ℂ) • A.central v := by
  rw [vir_two_double A v hv]
  simp only [map_add, map_smul, vir_central, vir_two_neg_two A v hv]
  module

/-- The upper off-diagonal weight-four entry is 3K. -/
theorem vir_gram4_12 : A.L 2 (A.L 2 (A.L (-4) v)) = (3 : ℂ) • A.central v := by
  rw [vir_two_neg_four A v hv, map_smul, vir_two_neg_two A v hv]
  module

/-- The lower off-diagonal weight-four entry is independently computed as 3K. -/
theorem vir_gram4_21 : A.L 4 (A.L (-2) (A.L (-2) v)) = (3 : ℂ) • A.central v := by
  rw [vir_push]
  norm_num
  rw [vir_four_neg_two A v hv, map_zero, zero_add, vir_two_neg_two A v hv]
  module

/-- The integral Lee–Yang singular word is 5L₋₂²−3L₋₄. Its lifted value
need not vanish; only its ordinary coordinate vanishes in the simple quotient. -/
noncomputable def virSingular4 : E :=
  (5 : ℂ) • A.L (-2) (A.L (-2) v) - (3 : ℂ) • A.L (-4) v

/-- The adjoint word reverses the mode signs and the order of application. -/
noncomputable def virAdjoint4 : End ℂ E :=
  (5 : ℂ) • (A.L 2 * A.L 2) - (3 : ℂ) • A.L 4

/-- The actual singular-word pairing is (25K²/2+55K)v. This computes
operators before substituting a central charge, so it includes the tangent term. -/
theorem vir_singular4_polynomial :
    virAdjoint4 A (virSingular4 A v) =
      (25/2 : ℂ) • A.central (A.central v) + (55 : ℂ) • A.central v := by
  simp only [virAdjoint4, virSingular4, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_sub, map_smul]
  rw [vir_gram4_11 A v hv, vir_gram4_12 A v hv,
    vir_gram4_21 A v hv, vir_four_neg_four A v hv]
  module

omit hv

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}

/-- A zero ordinary weight-four singular word gives a zero adjoint vacuum row.
This uses only the ordinary invariant form and does not posit a deformed form. -/
theorem vir_singular4_row (B : InvariantForm W)
    (hs : (5 : ℂ) • W.L (-2) (W.L (-2) W.vacuum) -
      (3 : ℂ) • W.L (-4) W.vacuum = 0) (x : V) :
    B.form W.vacuum ((5 : ℂ) • W.L 2 (W.L 2 x) - (3 : ℂ) • W.L 4 x) = 0 := by
  have h := congrArg (fun z => B.form z x) hs
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    B.virasoro_adj, neg_neg, map_zero, LinearMap.zero_apply] at h ⊢
  exact h

/-- The constant coordinate of the actual singular lift is the ordinary word. -/
theorem vir_singular4_fst (D : FirstOrderDeformation W) (β : ℂ)
    (A : CentralVirasoroData (V × V)) (hA : A.L = normalizedL D β) :
    (virSingular4 A (W.vacuum, 0)).1 =
      (5 : ℂ) • W.L (-2) (W.L (-2) W.vacuum) - (3 : ℂ) • W.L (-4) W.vacuum := by
  simp [virSingular4, hA, normalizedL_apply]

/-- On pure tangent inputs the normalized adjoint word has no deformation
correction. The already known ordinary row relation therefore kills its pairing. -/
theorem vir_singular4_pairing_zero (D : FirstOrderDeformation W) (β : ℂ)
    (A : CentralVirasoroData (V × V)) (hA : A.L = normalizedL D β)
    (B : InvariantForm W)
    (hs : (5 : ℂ) • W.L (-2) (W.L (-2) W.vacuum) -
      (3 : ℂ) • W.L (-4) W.vacuum = 0) :
    B.form W.vacuum (virAdjoint4 A (virSingular4 A (W.vacuum, 0))).2 = 0 := by
  have hx : virSingular4 A (W.vacuum, 0) =
      (0, (virSingular4 A (W.vacuum, 0)).2) :=
    Prod.ext ((vir_singular4_fst D β A hA).trans hs) rfl
  rw [hx]
  simp only [virAdjoint4, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, hA, normalizedL_tangent, Prod.snd_sub, Prod.smul_snd]
  exact vir_singular4_row B hs _

/-- The Lee–Yang singular relation in the actual simple quotient, expressed
with its own Virasoro modes rather than universal-module representatives. -/
theorem leeYang_simple_singular4 :
    (5 : ℂ) • (VirSimple.virasoroSimple LeeYang.leeYangC).L (-2)
      ((VirSimple.virasoroSimple LeeYang.leeYangC).L (-2)
        (VirSimple.virasoroSimple LeeYang.leeYangC).vacuum) -
    (3 : ℂ) • (VirSimple.virasoroSimple LeeYang.leeYangC).L (-4)
      (VirSimple.virasoroSimple LeeYang.leeYangC).vacuum = 0 := by
  have h := LeeYang.mkQ_leeYangSingular_eq_zero
  simp only [LeeYang.leeYangSingular, map_add, map_smul] at h
  simp only [LeeYang.L2L2vac, LeeYang.L4vac, ← VirModule.virasoroVOA_L_eq_Lop,
    VirQuotForm.mkQ_L] at h
  simpa only [neg_smul, sub_eq_add_neg] using h

/-- Taylor evaluation of the actual weight-four singular polynomial at the
Lee–Yang central charge. Its derivative is −55, so it detects every nonzero
first-order central correction. -/
theorem leeYang_singular_central_polynomial (δ : ℂ) (v : V) :
    let K : End ℂ (V × V) := LeeYang.leeYangC • 1 + δ • tangentShift
    (25/2 : ℂ) • K (K (v, 0)) + (55 : ℂ) • K (v, 0) =
      (0, (-55 * δ) • v) := by
  dsimp only
  apply Prod.ext <;>
    simp [LeeYang.leeYangC, LinearMap.add_apply, LinearMap.smul_apply,
      tangentShift, smul_add, smul_smul] <;> module

/-- Every graded deformation of the actual Lee–Yang simple algebra has zero
normalized central-charge variation. Both the singular relation and its pairing
obstruction are proved here; no determinant-preservation hypothesis is supplied.
Reconstructing a coboundary from these fixed-charge modes is a separate step. -/
theorem leeYang_actual_central_variation_zero
    (D : FirstOrderDeformation (VirSimple.virasoroSimple LeeYang.leeYangC))
    (hD : D.IsGraded) (α β : ℂ)
    (ha : D.smul₁ (VirSimple.virasoroSimple LeeYang.leeYangC).conformalVector 3
      (VirSimple.virasoroSimple LeeYang.leeYangC).conformalVector =
        α • (VirSimple.virasoroSimple LeeYang.leeYangC).vacuum)
    (hb : D.smul₁ (VirSimple.virasoroSimple LeeYang.leeYangC).conformalVector 1
      (VirSimple.virasoroSimple LeeYang.leeYangC).conformalVector =
        β • (VirSimple.virasoroSimple LeeYang.leeYangC).conformalVector) :
    2*α - β*LeeYang.leeYangC = 0 := by
  let W := VirSimple.virasoroSimple LeeYang.leeYangC
  let A := normalizedData D hD (VirSimple.virasoroSimple_grading_one _) α β ha hb
  have hv (n : ℤ) (hn : -1 ≤ n) : A.L n (W.vacuum, 0) = 0 :=
    normalizedL_vacuum D β n hn
  have hp := vir_singular4_polynomial A (W.vacuum, 0) hv
  have hz := vir_singular4_pairing_zero D β A rfl
    (VirQuotForm.Bsimp _) leeYang_simple_singular4
  have hK : A.central = LeeYang.leeYangC • 1 +
      (2*α-β*LeeYang.leeYangC) • tangentShift := rfl
  rw [hK, leeYang_singular_central_polynomial] at hp
  rw [hp] at hz
  have hB : (VirQuotForm.Bsimp LeeYang.leeYangC).form W.vacuum W.vacuum = 1 :=
    VirQuotForm.Bsimp_normalized _
  change (VirQuotForm.Bsimp LeeYang.leeYangC).form W.vacuum
    ((-55 * (2*α-β*LeeYang.leeYangC)) • W.vacuum) = 0 at hz
  simp only [map_smul, smul_eq_mul, hB, mul_one] at hz
  linear_combination -hz / 55

/-- Every graded Lee–Yang deformation admits actual normalized Virasoro modes
whose center is exactly the original scalar charge, with no tangent correction. -/
theorem leeYang_exists_fixed_central_modes
    (D : FirstOrderDeformation (VirSimple.virasoroSimple LeeYang.leeYangC))
    (hD : D.IsGraded) :
    ∃ (β : ℂ) (A : CentralVirasoroData
      ((VirModule.VirUniv LeeYang.leeYangC ⧸ VirSimple.maxIdealVir LeeYang.leeYangC) ×
       (VirModule.VirUniv LeeYang.leeYangC ⧸ VirSimple.maxIdealVir LeeYang.leeYangC))),
      A.L = normalizedL D β ∧ A.central = LeeYang.leeYangC • 1 := by
  obtain ⟨α, β, A, ha, hb, hL, hK⟩ := virasoroSimple_exists_normalizedData _ D hD
  have hz := leeYang_actual_central_variation_zero D hD α β ha hb
  exact ⟨β, A, hL, by simpa only [hz, zero_smul, add_zero] using hK⟩

end VOA.VirDeformModes
