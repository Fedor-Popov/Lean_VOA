/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3PBWSplit
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# The level-independence half of DLM3 induction, from the Euler operator

This file proves the `levels_iSupIndep` field of `DLM3.PBWFreeness` without a PBW theorem.
The operator is the adjoint action of the conformal zero mode `L₀ = ω(1)` on `U(V̂)`,
descended to the balanced induced module.  Every vector in level `k` lies in the eigenspace for
`k-n`, so distinct levels lie in distinct eigenspaces.

This does not prove `bottom_injective`.  That assertion is the remaining genuine PBW/freeness
input: level independence alone cannot show that the canonical map into the bottom level has
zero kernel.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

variable {W : VertexOperatorAlgebra 𝒱}

/-- The conformal degree element `L₀ = ω(1)` in `V̂`. -/
noncomputable def degreeElement (W : VertexOperatorAlgebra 𝒱) : VHatCarrier W :=
  gen W W.conformalVector 1

/-- The adjoint action of `L₀` on a homogeneous loop generator records its `V̂`-degree. -/
theorem lie_degreeElement_gen {w m : ℤ} {a : 𝒱} (ha : a ∈ W.grading w) :
    ⁅degreeElement W, gen W a m⁆ = ((w - m - 1 : ℤ) : ℂ) • gen W a m := by
  rw [bracket_eq, degreeElement, vhatBracket_gen W (bracketDescends W)]
  rw [finsum_eq_finsetSum_of_support_subset
    (fun i : ℕ => (gBinom (1 : ℤ) i) • gen W (W.smul W.conformalVector (i : ℤ) a)
      (1 + m - (i : ℤ))) (s := Finset.range 2) (by
      intro i hi
      rw [Function.mem_support] at hi
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra hlt
      have hge : 2 ≤ i := by omega
      have hz : gBinom (1 : ℤ) i = 0 := by
        rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl]
        exact gBinom_natCast_eq_zero (by omega)
      exact hi (by rw [hz, zero_smul]))]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num only [Nat.cast_zero, Nat.cast_one, add_zero, sub_zero, add_sub_cancel_left]
  have h0 : W.smul W.conformalVector (0 : ℤ) a = W.L (-1) a := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
    norm_num
  have h1 : W.smul W.conformalVector (1 : ℤ) a = W.L 0 a := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
    norm_num
  have hg1 : gBinom (1 : ℤ) 1 = 1 := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
      gBinom_natCast_eq_choose (show 1 ≤ 1 by omega)]
    norm_num
  rw [gBinom_zero, one_smul, h0, h1, W.L_zero_grading a ha, gen_Lneg1,
    gen_smul_left, hg1, one_smul]
  rw [show 1 + m - 1 = m by ring]
  push_cast
  module

/-- The adjoint action of `L₀` is scalar of eigenvalue `d` on `V̂(d)`. -/
theorem lie_degreeElement_of_mem_deg {d : ℤ} {x : VHatCarrier W} (hx : x ∈ deg W d) :
    ⁅degreeElement W, x⁆ = (d : ℂ) • x := by
  refine Submodule.span_induction
    (p := fun x _ => ⁅degreeElement W, x⁆ = (d : ℂ) • x) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨w, m, a, ha, hd, rfl⟩
    rw [lie_degreeElement_gen ha, hd]
  · change ⁅degreeElement W, (0 : VHatCarrier W)⁆ = (d : ℂ) • 0
    rw [bracket_eq, map_zero, smul_zero]
  · intro x y _ _ hx hy
    rw [lie_add, hx, hy, smul_add]
  · intro c x _ hx
    rw [bracket_eq] at hx ⊢
    rw [map_smul, hx, smul_smul]
    module

/-- The adjoint Euler operator on `U(V̂)`. -/
noncomputable def uenvDegreeOp (W : VertexOperatorAlgebra 𝒱) : End ℂ (UEnv W) :=
  { toFun := fun y => uι W (degreeElement W) * y - y * uι W (degreeElement W)
    map_add' := by
      intro y z
      noncomm_ring
    map_smul' := by
      intro c y
      simp only [mul_smul_comm, smul_mul_assoc, smul_sub, RingHom.id_apply] }

@[simp] theorem uenvDegreeOp_apply (W : VertexOperatorAlgebra 𝒱) (y : UEnv W) :
    uenvDegreeOp W y = uι W (degreeElement W) * y - y * uι W (degreeElement W) := by
  rfl

/-- The Euler operator is a derivation of the enveloping algebra. -/
theorem uenvDegreeOp_mul (W : VertexOperatorAlgebra 𝒱) (y z : UEnv W) :
    uenvDegreeOp W (y * z) = uenvDegreeOp W y * z + y * uenvDegreeOp W z := by
  simp only [uenvDegreeOp_apply]
  noncomm_ring

/-- On a Lie generator, the enveloping Euler operator is induced by the Lie bracket. -/
theorem uenvDegreeOp_uι_eq_lie (W : VertexOperatorAlgebra 𝒱) (x : VHatCarrier W) :
    uenvDegreeOp W (uι W x) = uι W ⁅degreeElement W, x⁆ := by
  rw [uenvDegreeOp_apply, ← Ring.lie_def, ← (uι W).map_lie]

/-- A homogeneous Lie element remains an Euler eigenvector after the enveloping inclusion. -/
theorem uenvDegreeOp_uι {d : ℤ} {x : VHatCarrier W} (hx : x ∈ deg W d) :
    uenvDegreeOp W (uι W x) = (d : ℂ) • uι W x := by
  rw [uenvDegreeOp_uι_eq_lie, lie_degreeElement_of_mem_deg hx, map_smul]

/-- Every length-`r`, degree-`d` word is an Euler eigenvector of eigenvalue `d`. -/
theorem uenvDegreeOp_eq_smul_of_mem_degLen (W : VertexOperatorAlgebra 𝒱) (r : ℕ) :
    ∀ {d : ℤ} {y : UEnv W}, y ∈ uenvDegLen W r d → uenvDegreeOp W y = (d : ℂ) • y := by
  induction r with
  | zero =>
      intro d y hy
      rw [uenvDegLen_zero] at hy
      by_cases hd : d = 0
      · rw [if_pos hd] at hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [map_smul]
        simp [uenvDegreeOp_apply, hd]
      · rw [if_neg hd, Submodule.mem_bot] at hy
        rw [hy, map_zero, smul_zero]
  | succ r ih =>
      intro d y hy
      rw [uenvDegLen_succ] at hy
      refine Submodule.iSup_induction (fun e : ℤ => uenvStep W e (uenvDegLen W r (d - e)))
        (motive := fun y => uenvDegreeOp W y = (d : ℂ) • y) hy ?_ ?_ ?_
      · intro e y hy'
        refine Submodule.span_induction
          (p := fun y _ => uenvDegreeOp W y = (d : ℂ) • y) ?_ ?_ ?_ ?_ hy'
        · rintro y ⟨x, hx, z, hz, rfl⟩
          rw [uenvDegreeOp_mul, uenvDegreeOp_uι hx, ih hz]
          rw [smul_mul_assoc, mul_smul_comm, ← add_smul]
          congr 1
          push_cast
          ring
        · change uenvDegreeOp W 0 = (d : ℂ) • (0 : UEnv W)
          rw [map_zero, smul_zero]
        · intro y₁ y₂ _ _ h₁ h₂
          rw [map_add, h₁, h₂, smul_add]
        · intro c y _ hy
          rw [map_smul, hy, smul_smul]
          module
      · change uenvDegreeOp W 0 = (d : ℂ) • (0 : UEnv W)
        rw [map_zero, smul_zero]
      · intro y₁ y₂ h₁ h₂
        rw [map_add, h₁, h₂, smul_add]

/-- Every element of `U(V̂)_d` is an Euler eigenvector of eigenvalue `d`. -/
theorem uenvDegreeOp_eq_smul_of_mem_deg {d : ℤ} {y : UEnv W} (hy : y ∈ uenvDeg W d) :
    uenvDegreeOp W y = (d : ℂ) • y := by
  refine Submodule.iSup_induction (fun r : ℕ => uenvDegLen W r d)
    (motive := fun y => uenvDegreeOp W y = (d : ℂ) • y) hy ?_ ?_ ?_
  · intro r y hyr
    exact uenvDegreeOp_eq_smul_of_mem_degLen W r hyr
  · change uenvDegreeOp W 0 = (d : ℂ) • (0 : UEnv W)
    rw [map_zero, smul_zero]
  · intro y₁ y₂ h₁ h₂
    rw [map_add, h₁, h₂, smul_add]

namespace DLM3

variable {n : ℕ} {U : Type u} [AddCommGroup U] [Module ℂ U]

/-- The Euler bracket of a parabolic element lies in the deep part.  Degree-zero generators are
killed, while the remaining parabolic generators already have degree at most `-n-1`. -/
theorem lie_degreeElement_parabolic_mem_deep (_P : ParabolicRep W n U) (g : Pn W n) :
    ⁅degreeElement W, (g : VHatCarrier W)⁆ ∈ deepPart W n := by
  have hg : (g : VHatCarrier W) ∈ degSpan W (parabolicSet n) := g.2
  refine Submodule.span_induction
    (p := fun x _ => ⁅degreeElement W, x⁆ ∈ deepPart W n) ?_ ?_ ?_ ?_ hg
  · rintro x ⟨w, m, a, ha, hd, rfl⟩
    rw [lie_degreeElement_gen ha]
    rcases hd with hd | hd
    · rw [hd]
      norm_num
    · exact Submodule.smul_mem _ _ (gen_mem_deepPart W n ha hd)
  · change ⁅degreeElement W, (0 : VHatCarrier W)⁆ ∈ deepPart W n
    rw [bracket_eq, map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [lie_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [bracket_eq] at hx ⊢
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

/-- The Euler bracket, bundled again as a parabolic element. -/
noncomputable def degreeBracketPn (P : ParabolicRep W n U) (g : Pn W n) : Pn W n :=
  ⟨⁅degreeElement W, (g : VHatCarrier W)⁆,
    deepPart_le_parabolic W n (lie_degreeElement_parabolic_mem_deep P g)⟩

@[simp] theorem degreeBracketPn_coe (P : ParabolicRep W n U) (g : Pn W n) :
    ((degreeBracketPn P g : Pn W n) : VHatCarrier W) =
      ⁅degreeElement W, (g : VHatCarrier W)⁆ := rfl

/-- The parabolic action kills the Euler bracket. -/
theorem act_degreeBracketPn_eq_zero (P : ParabolicRep W n U) (g : Pn W n) :
    P.act (degreeBracketPn P g) = 0 :=
  P.deep_zero (degreeBracketPn P g) (lie_degreeElement_parabolic_mem_deep P g)

/-- The Euler operator on the tensor cover. -/
noncomputable def coverDegreeOp (W : VertexOperatorAlgebra 𝒱) (U : Type u)
    [AddCommGroup U] [Module ℂ U] : End ℂ (IndCover W U) :=
  LinearMap.rTensor U (uenvDegreeOp W)

@[simp] theorem coverDegreeOp_tmul (y : UEnv W) (u : U) :
    coverDegreeOp W U (y ⊗ₜ[ℂ] u) = uenvDegreeOp W y ⊗ₜ[ℂ] u := rfl

/-- The balancing submodule is homogeneous for the Euler operator. -/
theorem balancing_degree_stable (P : ParabolicRep W n U) :
    ∀ t ∈ balancing P, coverDegreeOp W U t ∈ balancing P := by
  intro t ht
  refine Submodule.span_induction
    (p := fun t _ => coverDegreeOp W U t ∈ balancing P) ?_ ?_ ?_ ?_ ht
  · rintro t ⟨y, g, u, rfl⟩
    have hmain :
        (uenvDegreeOp W y * uι W (g : VHatCarrier W)) ⊗ₜ[ℂ] u
            - uenvDegreeOp W y ⊗ₜ[ℂ] (P.act g u) ∈ balancing P :=
      Submodule.subset_span ⟨uenvDegreeOp W y, g, u, rfl⟩
    have hbr :
        (y * uι W ((degreeBracketPn P g : Pn W n) : VHatCarrier W)) ⊗ₜ[ℂ] u
            - y ⊗ₜ[ℂ] (P.act (degreeBracketPn P g) u) ∈ balancing P :=
      Submodule.subset_span ⟨y, degreeBracketPn P g, u, rfl⟩
    rw [act_degreeBracketPn_eq_zero, LinearMap.zero_apply, TensorProduct.tmul_zero, sub_zero] at hbr
    change coverDegreeOp W U
      ((y * uι W (g : VHatCarrier W)) ⊗ₜ[ℂ] u
        - y ⊗ₜ[ℂ] (P.act g u)) ∈ balancing P
    rw [map_sub, coverDegreeOp_tmul, coverDegreeOp_tmul, uenvDegreeOp_mul,
      TensorProduct.add_tmul, uenvDegreeOp_uι_eq_lie, ← degreeBracketPn_coe P g]
    have hadd := Submodule.add_mem (balancing P) hmain hbr
    convert hadd using 1
    abel
  · change coverDegreeOp W U (0 : IndCover W U) ∈ balancing P
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro t₁ t₂ _ _ h₁ h₂
    rw [map_add]
    exact Submodule.add_mem _ h₁ h₂
  · intro c t _ ht
    rw [map_smul]
    exact Submodule.smul_mem _ _ ht

/-- The Euler operator descended to the balanced induced module. -/
noncomputable def indDegreeOp (P : ParabolicRep W n U) : End ℂ (IndMod P) :=
  Submodule.mapQ (balancing P) (balancing P) (coverDegreeOp W U)
    (fun t ht => balancing_degree_stable P t ht)

@[simp] theorem indDegreeOp_mk (P : ParabolicRep W n U) (y : UEnv W) (u : U) :
    indDegreeOp P (indMk P (y ⊗ₜ[ℂ] u)) =
      indMk P (uenvDegreeOp W y ⊗ₜ[ℂ] u) := rfl

/-- A pure tensor with enveloping degree `d` is an Euler eigenvector of eigenvalue `d`. -/
theorem indDegreeOp_mk_eq_smul_of_mem_uenvDeg (P : ParabolicRep W n U) {d : ℤ}
    {y : UEnv W} (hy : y ∈ uenvDeg W d) (u : U) :
    indDegreeOp P (indMk P (y ⊗ₜ[ℂ] u)) =
      (d : ℂ) • indMk P (y ⊗ₜ[ℂ] u) := by
  rw [indDegreeOp_mk, uenvDegreeOp_eq_smul_of_mem_deg hy, ← TensorProduct.smul_tmul',
    map_smul]

/-- Level `k` lies in the Euler eigenspace of eigenvalue `k-n`. -/
theorem levCover_le_eigenspace (P : ParabolicRep W n U) (k : ℤ) :
    levCover P k ≤ Module.End.eigenspace (indDegreeOp P) ((k - (n : ℤ) : ℤ) : ℂ) := by
  rw [levCover, Submodule.span_le]
  rintro z ⟨y, hy, u, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr
    (indDegreeOp_mk_eq_smul_of_mem_uenvDeg P hy u)

/-- **The levels of the induced module are independent, without PBW.**  They lie in distinct
eigenspaces of the descended Euler operator. -/
theorem levCover_iSupIndep (P : ParabolicRep W n U) : iSupIndep (levCover P) := by
  let μ : ℤ → ℂ := fun k => ((k - (n : ℤ) : ℤ) : ℂ)
  have hμ : Function.Injective μ := by
    intro a b hab
    have hab' : a - (n : ℤ) = b - (n : ℤ) := Int.cast_injective hab
    omega
  have heig : iSupIndep (fun k : ℤ => Module.End.eigenspace (indDegreeOp P) (μ k)) := by
    simpa only [Function.comp_apply] using
      (Module.End.eigenspaces_iSupIndep (indDegreeOp P)).comp hμ
  exact heig.mono (fun k => levCover_le_eigenspace P k)

/-- A faithful equivariant realization of the parabolic module separates the canonical bottom
inside the induced module.  This is the representation-theoretic route to the remaining
`bottom_injective` assertion: the universal `indLift` is a left inverse on bottom vectors. -/
theorem indBottom_injective_of_equivariant_embedding
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    (P : ParabolicRep W n U) (rho : VHatRep W M) (phi : U →ₗ[ℂ] M)
    (hphi : ∀ (g : Pn W n) (u : U),
      phi (P.act g u) = rho (g : VHatCarrier W) (phi u))
    (hphi_injective : Function.Injective phi) : Function.Injective (indBottom P) := by
  intro u₁ u₂ hbottom
  apply hphi_injective
  rw [← indLift_bottom P rho phi hphi u₁, ← indLift_bottom P rho phi hphi u₂,
    hbottom]

/-- Consequently `PBWFreeness` is reduced to bottom injectivity alone. -/
theorem pbwFreeness_of_bottom_injective (P : ParabolicRep W n U)
    (hinj : Function.Injective (indBottom P)) : PBWFreeness P :=
  ⟨hinj, levCover_iSupIndep P⟩

/-- Exact reduction: the two-field PBW package is equivalent to injectivity of the bottom map. -/
theorem pbwFreeness_iff_bottom_injective (P : ParabolicRep W n U) :
    PBWFreeness P ↔ Function.Injective (indBottom P) :=
  ⟨PBWFreeness.bottom_injective, pbwFreeness_of_bottom_injective P⟩

section LevelZero

variable {Q : ParabolicRep W 0 U}

/-- At level zero, bottom injectivity alone constructs the full bottom projection. -/
noncomputable def bottomProjectionOfInjective (Q : ParabolicRep W 0 U)
    (hinj : Function.Injective (indBottom Q)) : BottomProjection Q :=
  (pbwFreeness_of_bottom_injective Q hinj).bottomProjection

@[simp] theorem bottomProjectionOfInjective_bottom (hinj : Function.Injective (indBottom Q))
    (u : U) : (bottomProjectionOfInjective Q hinj).proj (indBottom Q u) = u :=
  (bottomProjectionOfInjective Q hinj).proj_bottom u

end LevelZero

end DLM3

end VHat
end VOA
