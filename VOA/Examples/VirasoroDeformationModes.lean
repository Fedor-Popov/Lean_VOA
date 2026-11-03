/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationCentralModes
import VOA.Examples.VirasoroRigidityStructural

/-!
# The actual conformal-mode commutator of a graded deformation

On a Virasoro state space, weight one vanishes and weight two is the conformal
line. Thus the first and third self-products of the conformal vector have two
scalar corrections. Jacobi and antisymmetry determine the zero-product field;
no deformed translation law or deformed invariant form is assumed.
-/
namespace VOA.VirDeformModes
open VertexOperatorAlgebra Deform
open Module (End)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}

/-- The first-order commutator of two conformal modes, using VOA mode indices.
It contains one ordinary and one correction operator in each composition. -/
def mixedComm (D : FirstOrderDeformation W) (m n : ℤ) (x : V) : V :=
  D.smul₁ W.conformalVector m (W.smul W.conformalVector n x) +
    W.smul W.conformalVector m (D.smul₁ W.conformalVector n x) -
    (D.smul₁ W.conformalVector n (W.smul W.conformalVector m x) +
      W.smul W.conformalVector n (D.smul₁ W.conformalVector m x))

/-- The mixed commutator changes sign when its two mode indices are exchanged. -/
theorem mixedComm_swap (D : FirstOrderDeformation W) (m n : ℤ) (x : V) :
    mixedComm D m n x + mixedComm D n m x = 0 := by
  unfold mixedComm
  abel

/-- The two contributions of the unknown conformal zero-product field in
linearized Jacobi. This is a defined expression, not an extra deformation input. -/
def zeroProductField (D : FirstOrderDeformation W) (n : ℤ) (x : V) : V :=
  W.smul (D.smul₁ W.conformalVector 0 W.conformalVector) n x +
    D.smul₁ (W.smul W.conformalVector 0 W.conformalVector) n x

/-- The known first-product contribution, when the correction at mode one is
β times the conformal vector. The ordinary first product is twice that vector. -/
def firstProductField (D : FirstOrderDeformation W) (β : ℂ) (n : ℤ) (x : V) : V :=
  β • W.smul W.conformalVector n x + (2 : ℂ) • D.smul₁ W.conformalVector n x

/-- Grading extracts the two scalar self-product coefficients. This includes
central charge zero and does not require a nonzero conformal vector. -/
theorem exists_conformal_parameters (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (h2 : W.grading 2 = ℂ ∙ W.conformalVector) :
    ∃ α β : ℂ,
      D.smul₁ W.conformalVector 3 W.conformalVector = α • W.vacuum ∧
      D.smul₁ W.conformalVector 1 W.conformalVector = β • W.conformalVector := by
  have ha := hD 2 2 W.conformalVector W.conformal_mem W.conformalVector W.conformal_mem 3
  have hb := hD 2 2 W.conformalVector W.conformal_mem W.conformalVector W.conformal_mem 1
  norm_num only at ha hb
  rw [W.vacuum_grade] at ha
  rw [h2] at hb
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp hb
  exact ⟨α, β, hα.symm, hβ.symm⟩

/-- Only modes zero, one and three survive in the conformal self-commutator.
The second product lands in weight one, and higher products have negative weight. -/
theorem mixedComm_low (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (h1 : W.grading 1 = ⊥) (α β : ℂ)
    (ha : D.smul₁ W.conformalVector 3 W.conformalVector = α • W.vacuum)
    (hb : D.smul₁ W.conformalVector 1 W.conformalVector = β • W.conformalVector)
    (m n : ℤ) (x : V) :
    mixedComm D m n x = zeroProductField D (m+n) x +
      (m : ℂ) • firstProductField D β (m+n-1) x +
      if m+n=2 then (cbz m 3 * α) • x else 0 := by
  rw [mixedComm, jacobi_mode_commutator]
  let F : ℤ → V := fun i => cbz m i •
    (W.smul (D.smul₁ W.conformalVector i W.conformalVector) (m+n-i) x +
      D.smul₁ (W.smul W.conformalVector i W.conformalVector) (m+n-i) x)
  have high (i : ℤ) (hi : 4 ≤ i) :
      W.smul W.conformalVector i W.conformalVector = 0 ∧
      D.smul₁ W.conformalVector i W.conformalVector = 0 := by
    have h := W.smul_mem_grading W.conformal_mem W.conformal_mem i
    have hd := hD 2 2 _ W.conformal_mem _ W.conformal_mem i
    rw [W.positivity _ (by omega), Submodule.mem_bot] at h hd
    exact ⟨h, hd⟩
  have two : W.smul W.conformalVector 2 W.conformalVector = 0 ∧
      D.smul₁ W.conformalVector 2 W.conformalVector = 0 := by
    have h := W.smul_mem_grading W.conformal_mem W.conformal_mem 2
    have hd := hD 2 2 _ W.conformal_mem _ W.conformal_mem 2
    norm_num only at h hd
    rw [h1, Submodule.mem_bot] at h hd
    exact ⟨h, hd⟩
  have hsupp : Function.support F ⊆ (↑({0, 1, 3} : Finset ℤ) : Set ℤ) := by
    intro i hi
    by_contra hh
    have h0 : i ≠ 0 := fun h => hh (by simp [h])
    have h1' : i ≠ 1 := fun h => hh (by simp [h])
    have h3 : i ≠ 3 := fun h => hh (by simp [h])
    apply hi
    dsimp [F]
    by_cases hn : i < 0
    · rw [cbz_apply_neg m hn, zero_smul]
    · by_cases hi2 : i = 2
      · subst i
        rw [two.1, two.2, PreVertexAlgebra.smul_zero_left, D.smul₁_zero_left, add_zero, smul_zero]
      · rw [(high i (by omega)).1, (high i (by omega)).2,
          PreVertexAlgebra.smul_zero_left, D.smul₁_zero_left, add_zero, smul_zero]
  change (∑ᶠ i : ℤ, F i) = _
  rw [finsum_eq_sum_of_support_subset F hsupp]
  have hbin : cbz m 1 = (m : ℂ) := by simp [cbz, gBinom]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    show (0 : ℤ) ≠ 1 by decide, show (0 : ℤ) ≠ 3 by decide,
    show (1 : ℤ) ≠ 3 by decide, or_self, not_false_eq_true,
    Finset.sum_singleton, F, cbz_zero, one_smul, sub_zero, hbin,
    ha, hb, VirCDef.conformal_smul_one, VirCDef.conformal_smul_three,
    PreVertexAlgebra.smul_smul_left, D.smul₁_smul_left, D.smul₁_vacuum_left,
    smul_zero, add_zero, PreVertexAlgebra.smul_vacuum_left,
    zeroProductField, firstProductField]
  by_cases hmn : m+n=2
  · have hmode : m+n-3 = -1 := by omega
    simp only [hmode, hmn, if_true, smul_smul]
    abel
  · have hmode : m+n-3 ≠ -1 := by omega
    simp only [hmode, hmn, if_false, smul_zero, add_zero]

/-- Antisymmetry at indices zero and q determines the entire unknown
zero-product field. The possible central term vanishes there because q=2
would give binomial(2,3)=0. -/
theorem zeroProductField_eq (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (h1 : W.grading 1 = ⊥) (α β : ℂ)
    (ha : D.smul₁ W.conformalVector 3 W.conformalVector = α • W.vacuum)
    (hb : D.smul₁ W.conformalVector 1 W.conformalVector = β • W.conformalVector)
    (q : ℤ) (x : V) :
    zeroProductField D q x = (-(q : ℂ) / 2) • firstProductField D β (q-1) x := by
  have h := mixedComm_swap D 0 q x
  rw [mixedComm_low D hD h1 α β ha hb, mixedComm_low D hD h1 α β ha hb] at h
  have hz : (if q=2 then (cbz q 3 * α) • x else 0) = 0 := by
    split_ifs with hq
    · subst q
      rw [cbz_lt (by norm_num : (0 : ℤ) ≤ 2) (by norm_num : (2 : ℤ) < 3),
        zero_mul, zero_smul]
    · rfl
  simp only [zero_add, add_zero, Int.cast_zero, zero_smul, cbz_zero_left,
    show (3 : ℤ) ≠ 0 by decide, if_false, zero_mul, hz, ite_self, add_zero] at h
  apply (smul_right_injective _ (show (2 : ℂ) ≠ 0 by norm_num))
  calc
    (2 : ℂ) • zeroProductField D q x =
        -(q : ℂ) • firstProductField D β (q-1) x := by
      rw [two_smul, neg_smul, eq_neg_iff_add_eq_zero]
      convert h using 1 <;> abel
    _ = (2 : ℂ) • ((-(q : ℂ) / 2) • firstProductField D β (q-1) x) := by module

/-- The third generalized binomial at the shifted Virasoro index is the
cubic central coefficient, before dividing the central charge by two. -/
theorem cbz_virasoro_three (m : ℤ) :
    cbz (m+1) 3 = ((m : ℂ)^3 - m) / 6 := by
  rw [cbz_apply_nonneg _ (by norm_num : (0 : ℤ) ≤ 3)]
  change gBinom (m+1) 3 = _
  simp [gBinom, Finset.prod_range_succ]
  push_cast
  ring

/-- The full linearized Virasoro commutator, with both self-product parameters
retained. The β term measures a rescaling of the conformal vector. -/
theorem mixedComm_virasoro (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (h1 : W.grading 1 = ⊥) (α β : ℂ)
    (ha : D.smul₁ W.conformalVector 3 W.conformalVector = α • W.vacuum)
    (hb : D.smul₁ W.conformalVector 1 W.conformalVector = β • W.conformalVector)
    (m n : ℤ) (x : V) :
    mixedComm D (m+1) (n+1) x =
      ((m : ℂ)-n) • D.smul₁ W.conformalVector (m+n+1) x +
      (((m : ℂ)-n)*β/2) • W.L (m+n) x +
      if m+n=0 then (((m : ℂ)^3-m)/6*α) • x else 0 := by
  rw [mixedComm_low D hD h1 α β ha hb, zeroProductField_eq D hD h1 α β ha hb,
    cbz_virasoro_three]
  have hi : m+1+(n+1)-1 = m+n+1 := by omega
  have he : m+1+(n+1)=2 ↔ m+n=0 := by omega
  simp only [firstProductField, hi, he, Int.cast_add, Int.cast_one]
  change _ = ((m : ℂ)-n) • D.smul₁ W.conformalVector (m+n+1) x +
    (((m : ℂ)-n)*β/2) • W.smul W.conformalVector (m+n+1) x + _
  module

/-- Normalize the lifted conformal generator by subtracting β/2 times its
pure tangent copy. This adjusts the generator inside the actual extension;
it does not assume a new deformation or a change of its central charge. -/
noncomputable def normalizedL (D : FirstOrderDeformation W) (β : ℂ) (n : ℤ) : End ℂ (V × V) :=
  liftedMode D W.conformalVector (n+1) -
    (β/2) • (tangentShift * liftedMode D W.conformalVector (n+1))

/-- Block formula for the normalized lifted Virasoro mode. -/
theorem normalizedL_apply (D : FirstOrderDeformation W) (β : ℂ) (n : ℤ) (x : V × V) :
    normalizedL D β n x =
      (W.L n x.1, W.L n x.2 + D.smul₁ W.conformalVector (n+1) x.1 - (β/2) • W.L n x.1) := by
  apply Prod.ext <;>
    simp [normalizedL, liftedMode_apply, Module.End.mul_apply, tangentShift,
      L_def, PreVertexAlgebra.smul_def] <;> abel

/-- The normalized lifted modes satisfy the genuine Virasoro commutator.
Their central operator is c I + (2α−βc) N, so the two raw self-product
coefficients leave exactly one central-charge direction after normalization. -/
theorem normalizedL_comm (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (h1 : W.grading 1 = ⊥) (α β : ℂ)
    (ha : D.smul₁ W.conformalVector 3 W.conformalVector = α • W.vacuum)
    (hb : D.smul₁ W.conformalVector 1 W.conformalVector = β • W.conformalVector)
    (m n : ℤ) :
    ⁅normalizedL D β m, normalizedL D β n⁆ =
      ((m : ℂ)-n) • normalizedL D β (m+n) +
      if m+n=0 then (((m : ℂ)^3-m)/12) •
        (W.centralCharge • (1 : End ℂ (V × V)) +
          (2*α-β*W.centralCharge) • tangentShift) else 0 := by
  have hord (z : V) : W.L m (W.L n z) - W.L n (W.L m z) =
      ((m : ℂ)-n) • W.L (m+n) z +
      if m+n=0 then (((m : ℂ)^3-m)/12*W.centralCharge) • z else 0 := by
    have h := LinearMap.congr_fun (W.L_virasoro m n) z
    by_cases hmn : m+n=0 <;>
      simpa [hmn, LieRing.of_associative_ring_bracket, Module.End.mul_apply] using h
  by_cases hmn : m+n=0
  all_goals
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · simpa [hmn, LieRing.of_associative_ring_bracket, Module.End.mul_apply,
        normalizedL_apply, tangentShift, smul_smul] using hord x.1
    · simp only [hmn, if_true, if_false, LieRing.of_associative_ring_bracket,
        LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, normalizedL_apply,
        Prod.snd_sub, Prod.snd_add, LinearMap.smul_apply, Module.End.one_apply,
        LinearMap.zero_apply, Prod.smul_snd, Prod.snd_zero]
      try dsimp only [tangentShift, LinearMap.coe_mk, AddHom.coe_mk]
      calc
        _ = (W.L m (W.L n x.2) - W.L n (W.L m x.2)) +
            mixedComm D (m+1) (n+1) x.1 -
            β • (W.L m (W.L n x.1) - W.L n (W.L m x.1)) := by
          simp only [mixedComm, map_add, map_sub, map_smul]
          change _ = _ +
            (D.smul₁ W.conformalVector (m+1) (W.L n x.1) +
              W.L m (D.smul₁ W.conformalVector (n+1) x.1) -
              (D.smul₁ W.conformalVector (n+1) (W.L m x.1) +
                W.L n (D.smul₁ W.conformalVector (m+1) x.1))) - _
          module
        _ = _ := by
          rw [hord, hord, mixedComm_virasoro D hD h1 α β ha hb]
          simp only [hmn, if_true, if_false]
          module

/-- Normalized Virasoro modes kill the pure vacuum for indices at least −1,
including the translation mode. -/
theorem normalizedL_vacuum (D : FirstOrderDeformation W) (β : ℂ)
    (n : ℤ) (hn : -1 ≤ n) : normalizedL D β n (W.vacuum, 0) = 0 := by
  simp [normalizedL, Module.End.mul_apply, liftedMode_vacuum D (n+1) (by omega)]

/-- The normalized conformal state is obtained at mode −2. Its constant part
is the original conformal vector and its tangent part fixes the β rescaling. -/
theorem normalizedL_neg_two_vacuum (D : FirstOrderDeformation W) (β : ℂ) :
    normalizedL D β (-2) (W.vacuum, 0) =
      (W.conformalVector, -(β/2) • W.conformalVector) := by
  rw [normalizedL_apply, VirCDef.L_negTwo_vacuum]
  simp [D.smul₁_vacuum_right _ (-1) (by omega : (-1 : ℤ) ≤ -1)]

/-- On pure tangent states the normalized modes act by the ordinary Virasoro
operators. Both the deformation term and the normalization term disappear. -/
theorem normalizedL_tangent (D : FirstOrderDeformation W) (β : ℂ) (n : ℤ) (x : V) :
    normalizedL D β n (0, x) = (0, W.L n x) := by
  simp [normalizedL_apply]

/-- The square-zero parameter shift commutes with the normalized modes. -/
theorem normalizedL_shift_comm (D : FirstOrderDeformation W) (β : ℂ) (n : ℤ) :
    Commute (tangentShift : End ℂ (V × V)) (normalizedL D β n) := by
  apply LinearMap.ext
  intro x
  simp [Module.End.mul_apply, tangentShift, normalizedL_apply]

/-- Normalized lifted modes shift both coordinates by the expected weight.
This supplies grading control without assuming that the lifted L₀ already equals
an external grading operator on the whole first-order extension. -/
theorem normalizedL_mem_grading (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (β : ℂ) (n r : ℤ) (x : V × V)
    (hx : x.1 ∈ W.grading r ∧ x.2 ∈ W.grading r) :
    (normalizedL D β n x).1 ∈ W.grading (r-n) ∧
      (normalizedL D β n x).2 ∈ W.grading (r-n) := by
  have hL (y : V) (hy : y ∈ W.grading r) : W.L n y ∈ W.grading (r-n) := by
    have h := W.smul_mem_grading W.conformal_mem hy (n+1)
    convert h using 1 <;> congr 1 <;> omega
  have hD' : D.smul₁ W.conformalVector (n+1) x.1 ∈ W.grading (r-n) := by
    have h := hD 2 r _ W.conformal_mem _ hx.1 (n+1)
    convert h using 1 <;> congr 1 <;> omega
  rw [normalizedL_apply]
  exact ⟨hL _ hx.1, (W.grading (r-n)).sub_mem
    ((W.grading (r-n)).add_mem (hL _ hx.2) hD')
    ((W.grading (r-n)).smul_mem _ (hL _ hx.1))⟩

/-- Virasoro modes with an operator-valued center. This is the complete
mode presentation, allowing the central charge to have a tangent part. -/
structure CentralVirasoroData (E : Type*) [AddCommGroup E] [Module ℂ E] where
  L : ℤ → End ℂ E
  central : End ℂ E
  comm : ∀ m n, ⁅L m, L n⁆ = ((m : ℂ)-n) • L (m+n) +
    if m+n=0 then (((m : ℂ)^3-m)/12) • central else 0
  central_comm : ∀ n, Commute central (L n)

/-- The mode data are constructed from the actual deformation once its two
self-product scalars have been extracted. No Virasoro relation is an input. -/
noncomputable def normalizedData (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (h1 : W.grading 1 = ⊥) (α β : ℂ)
    (ha : D.smul₁ W.conformalVector 3 W.conformalVector = α • W.vacuum)
    (hb : D.smul₁ W.conformalVector 1 W.conformalVector = β • W.conformalVector) :
    CentralVirasoroData (V × V) where
  L := normalizedL D β
  central := W.centralCharge • 1 + (2*α-β*W.centralCharge) • tangentShift
  comm := normalizedL_comm D hD h1 α β ha hb
  central_comm n := by
    change (W.centralCharge • (1 : End ℂ (V × V)) +
        (2*α-β*W.centralCharge) • tangentShift) * normalizedL D β n = _
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [normalizedL_shift_comm D β n]

/-- Every graded deformation of every simple Virasoro algebra supplies normalized
Virasoro modes with one actual central-charge direction, δ=2α−βc. This theorem
does not assert that the central-charge direction vanishes. -/
theorem virasoroSimple_exists_normalizedData (c : ℂ)
    (D : FirstOrderDeformation (VirSimple.virasoroSimple c)) (hD : D.IsGraded) :
    ∃ (α β : ℂ) (A : CentralVirasoroData
        ((VirModule.VirUniv c ⧸ VirSimple.maxIdealVir c) ×
          (VirModule.VirUniv c ⧸ VirSimple.maxIdealVir c))),
      D.smul₁ (VirSimple.virasoroSimple c).conformalVector 3
        (VirSimple.virasoroSimple c).conformalVector = α • (VirSimple.virasoroSimple c).vacuum ∧
      D.smul₁ (VirSimple.virasoroSimple c).conformalVector 1
        (VirSimple.virasoroSimple c).conformalVector = β • (VirSimple.virasoroSimple c).conformalVector ∧
      A.L = normalizedL D β ∧
      A.central = c • 1 + (2*α-β*c) • tangentShift := by
  obtain ⟨α, β, ha, hb⟩ := exists_conformal_parameters D hD
    (VirRigidStruct.virasoroSimple_grading_two c)
  have h1 : (VirSimple.virasoroSimple c).grading 1 = ⊥ := by
    rw [VirSimple.virasoroSimple_grading]
    change (VirModule.gradingVir c 1).map (VirSimple.maxIdealVir c).mkQ = ⊥
    rw [VirDefLow.gradingVir_one_eq_bot, Submodule.map_bot]
  exact ⟨α, β, normalizedData D hD h1 α β ha hb, ha, hb, rfl, rfl⟩

end VOA.VirDeformModes
