/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationCurrentModes

/-!
# The invariant current pairing of a normalized deformation

The pole of a graded first-order deformation is a bilinear pairing on weight one
with values in the vacuum line. After zero-mode normalization, linearized Jacobi
makes this pairing invariant under the weight-one Lie algebra. For an sl₂ basis,
invariance forces its entire matrix to be a multiple of the normalized Killing
form. This extracts the single level parameter from the actual deformation.
The singular-vector equations that must force that parameter to vanish are a
separate, still-open part of the affine rigidity argument.
-/
namespace VOA.Deform
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V} (D : FirstOrderDeformation W)

/-- The first positive correction product, as a bilinear map on the current space.
Its values are kept in the full state space so the definition needs no choice
of a coordinate on the vacuum line. -/
def currentPoleBilin : W.grading 1 →ₗ[ℂ] W.grading 1 →ₗ[ℂ] V where
  toFun a :=
    { toFun := fun b => D.smul₁ a 1 b
      map_add' := fun b c => D.smul₁_add_right a 1 b c
      map_smul' := fun r b => D.smul₁_smul_right a r 1 b }
  map_add' a b := by ext c; exact D.smul₁_add_left a b 1 c
  map_smul' r a := by ext b; exact D.smul₁_smul_left r a 1 b

/-- The bilinear pairing is exactly the deformation's pole vector. -/
@[simp] theorem currentPoleBilin_apply (a b : W.grading 1) :
    currentPoleBilin D a b = D.poleVec a b := rfl

/-- The zero/first-mode commutator applied to a third current says that the pole
pairing is invariant. Vacuum multiples disappear from zero modes by creation;
normalization removes the corrected Lie bracket. No invariance assumption is added. -/
theorem currentPoleBilin_invariant (hD : D.IsGraded) (hnorm : D.InPoleForm)
    (a b c : W.grading 1) :
    currentPoleBilin D ⁅a, b⁆ c + currentPoleBilin D b ⁅a, c⁆ = 0 := by
  have h := jacobi_mode_commutator D (a : V) b c 0 1
  rw [finsum_eq_single _ (0 : ℤ)
    (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])] at h
  have hbc := W.smul_mem_grading b.property c.property 1
  norm_num only at hbc
  rw [W.vacuum_grade] at hbc
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hbc
  obtain ⟨s, hs⟩ := D.exists_hasPoleCoeff hD b.property c.property
  change s • W.vacuum = D.smul₁ b 1 c at hs
  simp only [cbz_zero, one_smul, sub_zero, zero_add,
    hnorm a a.property b b.property, hnorm a a.property c c.property,
    PreVertexAlgebra.smul_zero_left, PreVertexAlgebra.smul_zero_right] at h
  rw [← hr, ← hs, D.smul₁_smul_right, PreVertexAlgebra.smul_smul_right,
    D.smul₁_vacuum_right _ _ (by omega),
    W.toPreVertexAlgebra.smul_vacuum_nonneg _ (by omega)] at h
  change D.smul₁ (W.smul a 0 b) 1 c + D.smul₁ b 1 (W.smul a 0 c) = 0
  simpa using (eq_neg_iff_add_eq_zero.mp (by simpa using h.symm))



section Sl2
variable {g : Type*} [LieRing g] [LieAlgebra ℂ g]

/-- Every invariant bilinear pairing on an sl₂ basis, with values in any complex
vector space, is determined by its value on (e,f). In the order (e,h,f) the only
nonzero matrix entries are (e,f), (f,e), and twice that value at (h,h).
Symmetry is a consequence; it is not an extra hypothesis. -/
theorem invariant_pairing_sl2_basis (b : Module.Basis (Fin 3) ℂ g)
    (ht : IsSl2Triple (b 1) (b 0) (b 2)) (B : g →ₗ[ℂ] g →ₗ[ℂ] V)
    (hinv : ∀ (a x y : g), B ⁅a, x⁆ y + B x ⁅a, y⁆ = 0) (i j : Fin 3) :
    B (b i) (b j) =
      (if i = 0 ∧ j = 2 ∨ i = 2 ∧ j = 0 then (1 : ℂ)
       else if i = 1 ∧ j = 1 then 2 else 0) • B (b 0) (b 2) := by
  have inv (a x y : Fin 3) := hinv (b a) (b x) (b y)
  have inv100 := inv 1 0 0
  have inv101 := inv 1 0 1
  have inv110 := inv 1 1 0
  have inv122 := inv 1 2 2
  have inv121 := inv 1 2 1
  have inv112 := inv 1 1 2
  have inv012 := inv 0 1 2
  have inv021 := inv 0 2 1
  simp only [Sl2Whitehead.br_he b ht, Sl2Whitehead.br_hf b ht,
    Sl2Whitehead.br_eh b ht, Sl2Whitehead.br_ef b ht,
    lie_self, map_zero, LinearMap.zero_apply, map_smul, LinearMap.smul_apply,
    map_neg, LinearMap.neg_apply, add_zero, zero_add] at inv100 inv101 inv110 inv122 inv121 inv112 inv012 inv021
  have hee : B (b 0) (b 0) = 0 := by
    have h : (4 : ℂ) • B (b 0) (b 0) = 0 := by
      calc _ = (2 : ℂ) • B (b 0) (b 0) + (2 : ℂ) • B (b 0) (b 0) := by module
           _ = 0 := inv100
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have heh : B (b 0) (b 1) = 0 :=
    (smul_eq_zero.mp (inv101)).resolve_left (by norm_num)
  have hhe : B (b 1) (b 0) = 0 :=
    (smul_eq_zero.mp (inv110)).resolve_left (by norm_num)
  have hff : B (b 2) (b 2) = 0 := by
    have h : (-4 : ℂ) • B (b 2) (b 2) = 0 := by
      calc _ = -((2 : ℂ) • B (b 2) (b 2)) + -((2 : ℂ) • B (b 2) (b 2)) := by module
           _ = 0 := inv122
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hfh : B (b 2) (b 1) = 0 := by
    have h : (2 : ℂ) • B (b 2) (b 1) = 0 := neg_eq_zero.mp (inv121)
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hhf : B (b 1) (b 2) = 0 := by
    have h : (2 : ℂ) • B (b 1) (b 2) = 0 := neg_eq_zero.mp (inv112)
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hhh : B (b 1) (b 1) = (2 : ℂ) • B (b 0) (b 2) := by
    apply eq_of_sub_eq_zero
    simpa only [sub_eq_add_neg, add_comm] using inv012
  have hhh' : B (b 1) (b 1) = (2 : ℂ) • B (b 2) (b 0) := by
    apply eq_of_sub_eq_zero
    simpa only [sub_eq_add_neg] using inv021
  have hfe : B (b 2) (b 0) = B (b 0) (b 2) :=
    smul_right_injective V (by norm_num : (2 : ℂ) ≠ 0) (hhh'.symm.trans hhh)
  fin_cases i <;> fin_cases j <;>
    simp [hee, heh, hhe, hff, hfh, hhf, hhh, hfe]
/-- Coordinates of the normalized invariant form in an (e,h,f) basis. It pairs
e with f in either order, pairs h with itself with coefficient two, and has no
other basis pairings. -/
noncomputable def sl2Pairing (b : Module.Basis (Fin 3) ℂ g) (x y : g) : ℂ :=
  b.repr x 0 * b.repr y 2 + 2 * b.repr x 1 * b.repr y 1 +
    b.repr x 2 * b.repr y 0

/-- Bilinearity extends the basis calculation to all elements of sl₂. Thus the
single value B(e,f) determines the entire invariant pairing, not just its matrix
entries on a selected set of generators. -/
theorem invariant_pairing_sl2 (b : Module.Basis (Fin 3) ℂ g)
    (ht : IsSl2Triple (b 1) (b 0) (b 2)) (B : g →ₗ[ℂ] g →ₗ[ℂ] V)
    (hinv : ∀ (a x y : g), B ⁅a, x⁆ y + B x ⁅a, y⁆ = 0) (x y : g) :
    B x y = sl2Pairing b x y • B (b 0) (b 2) := by
  conv_lhs => rw [Sl2Whitehead.basis_expand b x, Sl2Whitehead.basis_expand b y]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  rw [invariant_pairing_sl2_basis b ht B hinv 0 0,
    invariant_pairing_sl2_basis b ht B hinv 0 1,
    invariant_pairing_sl2_basis b ht B hinv 1 0,
    invariant_pairing_sl2_basis b ht B hinv 1 1,
    invariant_pairing_sl2_basis b ht B hinv 1 2,
    invariant_pairing_sl2_basis b ht B hinv 2 0,
    invariant_pairing_sl2_basis b ht B hinv 2 1,
    invariant_pairing_sl2_basis b ht B hinv 2 2]
  simp only [Fin.reduceEq,
    and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
    if_true, if_false, zero_smul, one_smul, smul_zero, zero_add, add_zero]
  unfold sl2Pairing
  module

end Sl2

/-- A normalized graded deformation of a VOA with sl₂ weight one has an actual
single scalar pole parameter. Its pairing on all currents is that scalar times
the standard invariant form times the vacuum. The parameter is obtained from
the (e,f) product of the given deformation; no new deformation hypothesis is used. -/
theorem exists_currentPole_sl2 (hD : D.IsGraded) (hnorm : D.InPoleForm)
    (b : Module.Basis (Fin 3) ℂ (W.grading 1))
    (ht : IsSl2Triple (b 1) (b 0) (b 2)) :
    ∃ δ : ℂ, ∀ a c : W.grading 1,
      D.poleVec a c = (sl2Pairing b a c * δ) • W.vacuum := by
  obtain ⟨δ, hδ⟩ := D.exists_hasPoleCoeff hD (b 0).property (b 2).property
  refine ⟨δ, fun a c => ?_⟩
  have h := invariant_pairing_sl2 b ht (currentPoleBilin D)
    (currentPoleBilin_invariant D hD hnorm) a c
  change δ • W.vacuum = D.poleVec (b 0) (b 2) at hδ
  simpa only [currentPoleBilin_apply, ← hδ, smul_smul] using h

end VOA.Deform
