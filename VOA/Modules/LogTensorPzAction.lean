/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Huang.PzTensorTauHat
import VOA.Huang.AssocJacobiBoundary

/-!
# The logarithmic `P(1)` action on compatible bilinear forms

The source modules here are arbitrary weak modules; in particular they may be generalized
modules with nonsemisimple `L(0)`. We construct the actual homogeneous coproduct twist,
assemble it on all VOA states, and prove that every stable lower-truncated compatible
space carries a genuine weak VOA module structure. This is the algebraic part of HLZ IV
Theorem 5.44 without any rationality or semisimplicity hypothesis.
-/

namespace VOA.LogTensor.Pz
open Module (End)
open scoped BigOperators
open VOA.Huang.PzTensorRho VOA.Huang.AssocJacobiBoundary
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]

abbrev BilinearDual := M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ

/-- The twisted coproduct, linear as an operator on the full algebraic tensor dual. -/
noncomputable def tauEnd (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (d : ℤ) (u : V) (n : ℤ) : End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) :=
  (-1:ℂ)^d • ∑ j ∈ Finset.range (d.toNat+1), (j.factorial:ℂ)⁻¹ •
    rhoL A₁ A₂ ((W.L 1 ^ j) u) (2*d-n-2-j)

@[simp] theorem tauEnd_apply (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (d : ℤ) (u : V) (n : ℤ) (b : BilinearDual (M₁ := M₁) (M₂ := M₂)) :
    tauEnd A₁ A₂ d u n b = tauHat A₁ A₂ d u n b := by
  simp only [tauEnd, tauHat, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]

/-- HLZ compatibility together with invariance under all homogeneous twisted modes.
These are concrete conditions on subspaces of the genuine algebraic tensor dual. -/
structure CompatibleSpace (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂) where
  carrier : Submodule ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂))
  stable : ∀ (d : ℤ) (u : V), u ∈ W.grading d → ∀ (n : ℤ) (b), b ∈ carrier →
    tauHat A₁ A₂ d u n b ∈ carrier
  truncated : ∀ b ∈ carrier, ∀ (d : ℤ) (u : V), u ∈ W.grading d → TruncAt A₁ A₂ u b
  compatible : ∀ b ∈ carrier, ∀ (d : ℤ) (u : V), u ∈ W.grading d → CompatAt A₁ A₂ u b

variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}

/-- A homogeneous state acts linearly on a compatible space. -/
noncomputable def CompatibleSpace.homogeneousAction (S : CompatibleSpace A₁ A₂)
    (n d : ℤ) : W.grading d →ₗ[ℂ] End ℂ S.carrier where
  toFun u := (tauEnd A₁ A₂ d u n).restrict (fun b hb => by
    rw [tauEnd_apply]; exact S.stable d u u.2 n b hb)
  map_add' u v := by
    ext b x y
    simp only [LinearMap.restrict_apply, LinearMap.add_apply, Submodule.coe_add,
      tauEnd_apply, tauHat, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
      map_add, smul_eq_mul, Submodule.coe_add]
    simp only [rhoL_add_state, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    ext b x y
    simp only [LinearMap.restrict_apply, LinearMap.smul_apply, Submodule.coe_smul,
      tauEnd_apply, tauHat, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
      map_smul, smul_eq_mul, RingHom.id_apply, Submodule.coe_smul]
    simp only [rhoL_smul_state, Finset.mul_sum]
    congr 1
    funext j
    ring

/-- The actual mode action on arbitrary states, assembled from the VOA's internal grading. -/
noncomputable def CompatibleSpace.action (S : CompatibleSpace A₁ A₂) (n : ℤ) :
    V →ₗ[ℂ] End ℂ S.carrier :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (S.homogeneousAction n)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

theorem CompatibleSpace.action_homogeneous (S : CompatibleSpace A₁ A₂) (n : ℤ)
    {d : ℤ} {u : V} (hu : u ∈ W.grading d) (b : S.carrier) :
    (S.action n u b : BilinearDual (M₁ := M₁) (M₂ := M₂)) = tauHat A₁ A₂ d u n b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have h : S.action n u = S.homogeneousAction n d ⟨u,hu⟩ := by
    change (DFinsupp.lsum ℂ (S.homogeneousAction n)) (DirectSum.decompose W.grading u) = _
    rw [DirectSum.decompose_of_mem W.grading hu]
    exact DFinsupp.lsum_single ℂ (S.homogeneousAction n) d ⟨u,hu⟩
  rw [h]
  exact tauEnd_apply A₁ A₂ d u n b

/-- The state-field map of the compatible-space module. -/
noncomputable def CompatibleSpace.field (S : CompatibleSpace A₁ A₂) :
    V →ₗ[ℂ] (End ℂ S.carrier)⟦z^±⟧ where
  toFun u := fun p => S.action (-p-1) u
  map_add' u v := by funext p; exact (S.action (-p-1)).map_add u v
  map_smul' c u := by funext p; exact (S.action (-p-1)).map_smul c u

@[simp] theorem CompatibleSpace.field_apply (S : CompatibleSpace A₁ A₂) (u : V) (p : ℤ) :
    S.field u p = S.action (-p-1) u := rfl

@[simp] theorem CompatibleSpace.mode_field (S : CompatibleSpace A₁ A₂) (u : V) (n : ℤ) :
    mode (S.field u) n = S.action n u := by
  rw [mode_apply, S.field_apply, show -(-n-1)-1 = n by ring]

/-- Lower truncation follows from the lower truncation of the transposed coproduct.
The finite `L(1)` tower gives a single bound for every homogeneous state. -/
theorem CompatibleSpace.action_truncated (S : CompatibleSpace A₁ A₂) : Truncated S.field := by
  intro u b
  have hu : u ∈ ⨆ d, W.grading d := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction W.grading
    (motive := fun u => ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (S.field u) n b = 0) hu ?_ ?_ ?_
  · intro d u hu
    choose P hP using fun j : ℕ =>
      S.truncated b b.2 (d-j) ((W.L 1 ^ j) u) (VertexOperatorAlgebra.L_one_pow_mem W hu j)
    let bound : ℤ := ∑ j ∈ Finset.range (d.toNat+1), |P j|
    refine ⟨2*d+bound, fun n hn => ?_⟩
    apply Subtype.ext
    rw [S.mode_field, S.action_homogeneous n hu]
    simp only [tauHat]
    apply smul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j hj
    have hle : |P j| ≤ bound := Finset.single_le_sum (fun j _ => abs_nonneg (P j)) hj
    rw [hP j _ (by have := neg_abs_le (P j); omega), smul_zero]
  · exact ⟨0, fun n _ => by simp⟩
  · rintro u v ⟨N,hN⟩ ⟨K,hK⟩
    exact ⟨max N K, fun n hn => by
      rw [map_add, mode_add, LinearMap.add_apply, hN n (le_trans (le_max_left _ _) hn),
        hK n (le_trans (le_max_right _ _) hn), add_zero]⟩

/-- The coproduct has the expected vacuum normalization on the full tensor dual. -/
theorem rho_vacuum (b : BilinearDual (M₁ := M₁) (M₂ := M₂)) (p : ℤ) :
    rhoL A₁ A₂ W.vacuum p b = if p = -1 then b else 0 := by
  ext x y
  rw [rhoL_apply]
  have hsum : (∑ᶠ r : ℤ, cbz p r * b (mode (A₁.YM W.vacuum) r x) y) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro r
    by_cases hr : r = -1
    · subst r
      rw [cbz_apply_neg p (by norm_num), zero_mul]
    · rw [A₁.vacuum_YM, mode_one, if_neg hr, LinearMap.zero_apply, map_zero,
        LinearMap.zero_apply, mul_zero]
  rw [hsum, add_zero, A₂.vacuum_YM, mode_one]
  by_cases hp : p = -1
  · simp only [if_pos hp, Module.End.one_apply]
  · simp only [if_neg hp, LinearMap.zero_apply, map_zero]

/-- The contragredient twist preserves the vacuum field. -/
theorem tau_vacuum (b : BilinearDual (M₁ := M₁) (M₂ := M₂)) (n : ℤ) :
    tauHat A₁ A₂ 0 W.vacuum n b = if n = -1 then b else 0 := by
  simp only [tauHat, Int.toNat_zero, zero_add, Finset.sum_range_succ,
    Finset.sum_range_zero, add_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_smul, zpow_zero, pow_zero, Module.End.one_apply, Nat.cast_zero, zero_mul,
    zero_sub, sub_zero]
  rw [rho_vacuum]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exfalso; apply h₂; omega
  · exfalso; apply h₁; omega
  · rfl

/-- The actual field on a compatible space has the vacuum normalization. -/
theorem CompatibleSpace.field_vacuum (S : CompatibleSpace A₁ A₂) :
    S.field W.vacuum = 1 := by
  refine FormalDist.ext fun p => ?_
  ext b : 1
  apply Subtype.ext
  have h := S.action_homogeneous (-p-1) W.vacuum_mem_grading_zero b
  change ((S.action (-p-1) W.vacuum b : S.carrier) : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] ℂ) = _
  rw [h, tau_vacuum, FormalDist.one_apply]
  by_cases hp : p = 0
  · subst p; simp
  · rw [if_neg (by omega), if_neg hp]
    rfl

/-- Evaluation at an input pair is a linear functional on a compatible space. -/
noncomputable def CompatibleSpace.eval (S : CompatibleSpace A₁ A₂) (x : M₁) (y : M₂) :
    S.carrier →ₗ[ℂ] ℂ where
  toFun b := b.1 x y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The homogeneous Borcherds identity holds for the actual assembled field. -/
theorem CompatibleSpace.field_borcherds_homogeneous (S : CompatibleSpace A₁ A₂)
    {p q : ℤ} {u v : V} (hu : u ∈ W.grading p) (hv : v ∈ W.grading q)
    (b : S.carrier) (ell m n : ℤ) :
    BL S.field u v b ell m n = BR W S.field u v b ell m n := by
  have htr := S.action_truncated
  rw [BL_as_finsum htr]
  have hL : (Function.support fun i : ℤ => (negOnePow i * cbz ell i) •
    (mode (S.field u) (ell+m-i) (mode (S.field v) (n+i) b) -
      negOnePow ell • mode (S.field v) (ell+n-i) (mode (S.field u) (m+i) b))).Finite := by
    refine ((Puv_fin htr u v b ell m n).union (Pvu_fin htr u v b ell m n)).subset ?_
    intro i hi
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc hi
    apply hi
    rw [smul_sub, hc.1, smul_comm, hc.2, smul_zero, sub_zero]
  apply Subtype.ext
  ext x y
  have hR := BR_fin (W := W) (YM := S.field) u v b ell m n
  change S.eval x y (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
    (mode (S.field u) (ell+m-i) (mode (S.field v) (n+i) b) -
      negOnePow ell • mode (S.field v) (ell+n-i) (mode (S.field u) (m+i) b))) =
    S.eval x y (∑ᶠ i : ℤ, cbz m i •
      mode (S.field (W.smul u (ell+i) v)) (m+n-i) b)
  rw [map_finsum (S.eval x y) hL, map_finsum (S.eval x y) hR]
  simp only [map_smul, map_sub, smul_eq_mul, CompatibleSpace.eval,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp only [S.mode_field]
  simp_rw [S.action_homogeneous _ hu, S.action_homogeneous _ hv,
    S.action_homogeneous _ (W.smul_mem_grading hu hv _)]
  simp_rw [S.action_homogeneous _ hu]
  exact tauHat_jacobi_pt A₁ A₂
    (fun c d hc => S.truncated b b.2 d c hc)
    (fun c d hc => S.compatible b b.2 d c hc) hu hv ell m n x y

/-- Full Jacobi, extended from homogeneous VOA states by their finite decomposition. -/
theorem CompatibleSpace.field_jacobi (S : CompatibleSpace A₁ A₂) (u v : V)
    (b : S.carrier) (ell m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      (mode (S.field u) (ell+m-i) (mode (S.field v) (n+i) b) -
        negOnePow ell • mode (S.field v) (ell+n-i) (mode (S.field u) (m+i) b))) =
      ∑ᶠ i : ℤ, cbz m i • mode (S.field (W.smul u (ell+i) v)) (m+n-i) b := by
  rw [← BL_as_finsum S.action_truncated]
  exact borcherdsAt_of_homogeneous S.action_truncated b ell m n
    (fun p q u v hu hv => S.field_borcherds_homogeneous hu hv b ell m n) u v

/-- The HLZ compatible-space construction yields a genuine weak VOA module, including
full Jacobi, with no ordinary-module or rationality hypothesis. -/
noncomputable def CompatibleSpace.weakModule (S : CompatibleSpace A₁ A₂) : WeakModule W S.carrier where
  YM := S.field
  vacuum_YM := S.field_vacuum
  truncation := S.action_truncated
  jacobi := S.field_jacobi

end VOA.LogTensor.Pz
