/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperNearVOA

/-!
# Even automorphisms of a super vertex operator algebra

An automorphism of a super VOA is an invertible complex-linear map which preserves every
integer-labelled mode product, the vacuum, the conformal vector, and each parity summand.  The
last condition is the mathematical meaning of **even** here.  Conformal-weight preservation is
not an additional field: fixing the conformal vector and preserving its first mode makes the map
commute with `L₀`, and the internal weight grading identifies its pieces with the `L₀`
eigenspaces.

The canonical parity automorphism `parityAut W` is induced by the basis-independent involution
`(-1)^F`.  Its mode law is proved first on homogeneous inputs from
`parSign (p+q) = parSign p * parSign q`, then extended using the internal parity decomposition.
Thus no relation between conformal weight and parity is used.

The parity automorphism always has order dividing two.  It has exact order two when the odd
summand is nonzero, while on a purely even algebra it is the identity; stating unconditional
exact order two would therefore be false.
-/

namespace VOA

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Elementary parity-involution facts -/

namespace ParityGrading

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Applying the parity involution twice is the identity. -/
theorem parityInvol_involutive (P : ParityGrading M) : Function.Involutive P.parityInvol := by
  intro x
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := P.exists_parity_decomp x
  simp only [map_add, P.parityInvol_even hx₀, P.parityInvol_odd hx₁, map_neg,
    neg_neg]

/-- The parity involution, bundled as a complex-linear equivalence. -/
noncomputable def parityLinearEquiv (P : ParityGrading M) : M ≃ₗ[ℂ] M :=
  LinearEquiv.ofBijective P.parityInvol P.parityInvol_involutive.bijective

@[simp] theorem parityLinearEquiv_apply (P : ParityGrading M) (x : M) :
    P.parityLinearEquiv x = P.parityInvol x := rfl

@[simp] theorem parityLinearEquiv_symm_apply (P : ParityGrading M) (x : M) :
    P.parityLinearEquiv.symm x = P.parityInvol x := by
  apply P.parityLinearEquiv.injective
  rw [LinearEquiv.apply_symm_apply, parityLinearEquiv_apply, parityInvol_involutive]

end ParityGrading

/-! ## Bilinearity of super mode products -/

namespace SuperVertexAlgebra

@[simp] theorem smul_add_left (V : SuperVertexAlgebra 𝒱) (u₁ u₂ : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul (u₁ + u₂) n v = V.smul u₁ n v + V.smul u₂ n v := by
  simp only [smul_def, map_add, mode_add, LinearMap.add_apply]

@[simp] theorem smul_smul_left (V : SuperVertexAlgebra 𝒱) (c : ℂ) (u : 𝒱)
    (n : ℤ) (v : 𝒱) : V.smul (c • u) n v = c • V.smul u n v := by
  simp only [smul_def, map_smul, mode_smul, LinearMap.smul_apply]

@[simp] theorem smul_add_right (V : SuperVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v₁ v₂ : 𝒱) :
    V.smul u n (v₁ + v₂) = V.smul u n v₁ + V.smul u n v₂ :=
  map_add (mode (V.Y u) n) v₁ v₂

@[simp] theorem smul_smul_right (V : SuperVertexAlgebra 𝒱) (u : 𝒱) (c : ℂ)
    (n : ℤ) (v : 𝒱) : V.smul u n (c • v) = c • V.smul u n v :=
  map_smul (mode (V.Y u) n) c v

end SuperVertexAlgebra

/-! ## The even automorphism group -/

/-- An **even automorphism** of a super vertex operator algebra: a complex-linear equivalence
preserving all mode products, the vacuum, the conformal vector, and both parity pieces.

Parity preservation is stated as an iff.  Besides making the inverse law transparent, this says
that each parity summand is carried *onto* itself, rather than merely into itself. -/
structure SuperAut (W : SuperVertexOperatorAlgebra 𝒱) where
  /-- The underlying complex-linear equivalence. -/
  toLinearEquiv : 𝒱 ≃ₗ[ℂ] 𝒱
  /-- Every integer-labelled mode product is preserved. -/
  map_smul' : ∀ (u : 𝒱) (n : ℤ) (v : 𝒱),
    toLinearEquiv (W.smul u n v) = W.smul (toLinearEquiv u) n (toLinearEquiv v)
  /-- The vacuum is fixed. -/
  map_vacuum : toLinearEquiv W.vacuum = W.vacuum
  /-- The conformal vector is fixed. -/
  map_omega : toLinearEquiv W.conformalVector = W.conformalVector
  /-- The automorphism is even: each parity piece is carried onto itself. -/
  map_parity' : ∀ (p : ZMod 2) (u : 𝒱),
    toLinearEquiv u ∈ W.parity p ↔ u ∈ W.parity p

namespace SuperAut

variable {W : SuperVertexOperatorAlgebra 𝒱}

instance : CoeFun (SuperAut W) (fun _ => 𝒱 → 𝒱) := ⟨fun α => α.toLinearEquiv⟩

@[simp] theorem coe_toLinearEquiv (α : SuperAut W) (v : 𝒱) :
    α.toLinearEquiv v = α v := rfl

@[ext] theorem ext {α β : SuperAut W} (h : α.toLinearEquiv = β.toLinearEquiv) : α = β := by
  cases α
  cases β
  cases h
  rfl

/-- Product preservation in the coercion API. -/
theorem map_smul (α : SuperAut W) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    α (W.smul u n v) = W.smul (α u) n (α v) := α.map_smul' u n v

/-- Forward parity preservation. -/
theorem map_mem_parity (α : SuperAut W) {p : ZMod 2} {u : 𝒱}
    (hu : u ∈ W.parity p) : α u ∈ W.parity p := (α.map_parity' p u).2 hu

/-- Reflection of parity membership. -/
theorem mem_parity_of_map_mem (α : SuperAut W) {p : ZMod 2} {u : 𝒱}
    (hu : α u ∈ W.parity p) : u ∈ W.parity p := (α.map_parity' p u).1 hu

/-- Composition of even super-VOA automorphisms (the right factor acts first). -/
def comp (α β : SuperAut W) : SuperAut W where
  toLinearEquiv := β.toLinearEquiv.trans α.toLinearEquiv
  map_smul' u n v := by
    simp only [LinearEquiv.trans_apply, β.map_smul', α.map_smul']
  map_vacuum := by simp only [LinearEquiv.trans_apply, β.map_vacuum, α.map_vacuum]
  map_omega := by simp only [LinearEquiv.trans_apply, β.map_omega, α.map_omega]
  map_parity' p u := (α.map_parity' p (β u)).trans (β.map_parity' p u)

/-- The identity even automorphism. -/
def id (W : SuperVertexOperatorAlgebra 𝒱) : SuperAut W where
  toLinearEquiv := LinearEquiv.refl ℂ 𝒱
  map_smul' _ _ _ := rfl
  map_vacuum := rfl
  map_omega := rfl
  map_parity' _ _ := Iff.rfl

/-- The inverse even automorphism. -/
def inverse (α : SuperAut W) : SuperAut W where
  toLinearEquiv := α.toLinearEquiv.symm
  map_smul' u n v := by
    refine α.toLinearEquiv.injective ?_
    simp only [LinearEquiv.apply_symm_apply, α.map_smul']
  map_vacuum := α.toLinearEquiv.injective (by
    rw [LinearEquiv.apply_symm_apply, α.map_vacuum])
  map_omega := α.toLinearEquiv.injective (by
    rw [LinearEquiv.apply_symm_apply, α.map_omega])
  map_parity' p u := by
    rw [← α.map_parity' p (α.toLinearEquiv.symm u), LinearEquiv.apply_symm_apply]

instance : Group (SuperAut W) where
  mul := comp
  one := id W
  inv := inverse
  mul_assoc α β γ := ext (LinearEquiv.ext fun _ => rfl)
  one_mul α := ext (LinearEquiv.ext fun _ => rfl)
  mul_one α := ext (LinearEquiv.ext fun _ => rfl)
  inv_mul_cancel α := ext (LinearEquiv.ext fun x => α.toLinearEquiv.symm_apply_apply x)

@[simp] theorem mul_apply (α β : SuperAut W) (v : 𝒱) : (α * β) v = α (β v) := rfl

@[simp] theorem one_apply (v : 𝒱) : (1 : SuperAut W) v = v := rfl

@[simp] theorem inv_apply (α : SuperAut W) (v : 𝒱) :
    α⁻¹ v = α.toLinearEquiv.symm v := rfl

/-- Fixing the conformal vector and preserving products makes every automorphism commute with
all Virasoro modes. -/
theorem map_L (α : SuperAut W) (n : ℤ) (v : 𝒱) : α (W.L n v) = W.L n (α v) := by
  change α (W.smul W.conformalVector (n + 1) v) =
    W.smul W.conformalVector (n + 1) (α v)
  rw [α.map_smul, α.map_omega]

/-- Conformal-weight preservation is a theorem, not automorphism data. -/
theorem map_mem_grading (α : SuperAut W) {h : ℂ} {v : 𝒱}
    (hv : v ∈ W.grading h) : α v ∈ W.grading h := by
  apply W.toSuperNearVOA.mem_grading_of_L0_eq
  change W.L 0 (α v) = h • α v
  rw [← α.map_L 0 v, W.L0_eigenvalue hv]
  exact α.toLinearEquiv.map_smul h v

/-- An automorphism carries each conformal-weight space onto itself. -/
theorem map_mem_grading_iff (α : SuperAut W) (h : ℂ) (v : 𝒱) :
    α v ∈ W.grading h ↔ v ∈ W.grading h := by
  constructor
  · intro hv
    have hinv := map_mem_grading (α := α⁻¹) hv
    simpa using hinv
  · exact α.map_mem_grading

end SuperAut

/-! ## The canonical parity automorphism -/

namespace SuperVertexOperatorAlgebra

/-- The parity grading bundled independently of the conformal-weight grading. -/
def parityGrading (W : SuperVertexOperatorAlgebra 𝒱) : ParityGrading 𝒱 where
  parity := W.parity
  isInternal := W.parity_isInternal

private theorem parityInvol_smul_homogeneous (W : SuperVertexOperatorAlgebra 𝒱)
    {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ W.parity p) (hv : v ∈ W.parity q) (n : ℤ) :
    W.parityGrading.parityInvol (W.smul u n v) =
      W.smul (W.parityGrading.parityInvol u) n (W.parityGrading.parityInvol v) := by
  rw [W.parityGrading.parityInvol_homog (W.smul_mem_parity hu hv n),
    W.parityGrading.parityInvol_homog hu, W.parityGrading.parityInvol_homog hv,
    W.smul_smul_left, W.smul_smul_right, smul_smul, ← parSign_add]

/-- The parity involution preserves all mode products. -/
theorem parityInvol_smul (W : SuperVertexOperatorAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    W.parityGrading.parityInvol (W.smul u n v) =
      W.smul (W.parityGrading.parityInvol u) n (W.parityGrading.parityInvol v) := by
  obtain ⟨u₀, hu₀, u₁, hu₁, hu⟩ := W.parityGrading.exists_parity_decomp u
  obtain ⟨v₀, hv₀, v₁, hv₁, hv⟩ := W.parityGrading.exists_parity_decomp v
  rw [← hu, ← hv]
  simp only [W.smul_add_left, W.smul_add_right, map_add]
  rw [parityInvol_smul_homogeneous W hu₀ hv₀ n,
    parityInvol_smul_homogeneous W hu₀ hv₁ n,
    parityInvol_smul_homogeneous W hu₁ hv₀ n,
    parityInvol_smul_homogeneous W hu₁ hv₁ n]

/-- The canonical parity automorphism `σ = (-1)^F`. -/
noncomputable def parityAut (W : SuperVertexOperatorAlgebra 𝒱) : SuperAut W where
  toLinearEquiv := W.parityGrading.parityLinearEquiv
  map_smul' := W.parityInvol_smul
  map_vacuum := W.parityGrading.parityInvol_even W.vacuum_parity
  map_omega := W.parityGrading.parityInvol_even W.conformal_parity
  map_parity' p u := by
    constructor
    · intro hu
      have hu' : W.parityGrading.parityInvol u ∈ W.parity p := by simpa using hu
      rw [← W.parityGrading.parityInvol_involutive u,
        W.parityGrading.parityInvol_homog hu']
      exact Submodule.smul_mem _ _ hu'
    · intro hu
      rw [W.parityGrading.parityLinearEquiv_apply,
        W.parityGrading.parityInvol_homog hu]
      exact Submodule.smul_mem _ _ hu

@[simp] theorem parityAut_apply (W : SuperVertexOperatorAlgebra 𝒱) (v : 𝒱) :
    W.parityAut v = W.parityGrading.parityInvol v := rfl

/-- On a homogeneous state, the parity automorphism is the expected sign. -/
theorem parityAut_homog (W : SuperVertexOperatorAlgebra 𝒱) {p : ZMod 2} {v : 𝒱}
    (hv : v ∈ W.parity p) : W.parityAut v = parSign p • v :=
  W.parityGrading.parityInvol_homog hv

/-- The parity automorphism squares to the identity. -/
@[simp] theorem parityAut_sq (W : SuperVertexOperatorAlgebra 𝒱) : W.parityAut ^ 2 = 1 := by
  apply SuperAut.ext
  apply LinearEquiv.ext
  intro v
  rw [pow_two, SuperAut.mul_apply, parityAut_apply, parityAut_apply,
    W.parityGrading.parityInvol_involutive, SuperAut.one_apply]

/-- In particular, the parity automorphism has finite order (dividing two). -/
theorem parityAut_isOfFinOrder (W : SuperVertexOperatorAlgebra 𝒱) :
    IsOfFinOrder W.parityAut := by
  rw [isOfFinOrder_iff_pow_eq_one]
  exact ⟨2, by norm_num, W.parityAut_sq⟩

/-- If the odd summand is nonzero, the parity automorphism is not the identity. -/
theorem parityAut_ne_one_of_odd_ne_bot (W : SuperVertexOperatorAlgebra 𝒱)
    (hodd : W.parity 1 ≠ ⊥) : W.parityAut ≠ 1 := by
  intro hsigma
  apply hodd
  rw [eq_bot_iff]
  intro v hv
  have hfun : W.parityAut v = (1 : SuperAut W) v := congrArg (fun α : SuperAut W => α v) hsigma
  rw [W.parityAut_homog hv, parSign_one, neg_one_smul, SuperAut.one_apply] at hfun
  have htwo : (2 : ℂ) • v = 0 := by
    rw [two_smul, ← neg_eq_iff_add_eq_zero]
    exact hfun
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- With a nonzero odd summand, the parity automorphism has exact order two. -/
theorem orderOf_parityAut_eq_two (W : SuperVertexOperatorAlgebra 𝒱)
    (hodd : W.parity 1 ≠ ⊥) : orderOf W.parityAut = 2 :=
  orderOf_eq_prime W.parityAut_sq (W.parityAut_ne_one_of_odd_ne_bot hodd)

/-- On a purely even super VOA, the parity automorphism is the identity. -/
theorem parityAut_eq_one_of_odd_eq_bot (W : SuperVertexOperatorAlgebra 𝒱)
    (heven : W.parity 1 = ⊥) : W.parityAut = 1 := by
  apply SuperAut.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨v₀, hv₀, v₁, hv₁, hv⟩ := W.parityGrading.exists_parity_decomp v
  have hv₁' : v₁ ∈ W.parity 1 := hv₁
  have hv₁0 : v₁ = 0 := by rw [heven, Submodule.mem_bot] at hv₁'; exact hv₁'
  rw [parityAut_apply, ← hv, hv₁0, add_zero,
    W.parityGrading.parityInvol_even hv₀, SuperAut.one_apply]

end SuperVertexOperatorAlgebra

end VOA
