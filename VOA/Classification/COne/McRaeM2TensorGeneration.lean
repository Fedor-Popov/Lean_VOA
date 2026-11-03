/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2TensorRepresenting
import VOA.Modules.LogTensorTwist

/-! # The actual canonical tensor modes span the tensor carrier

A homogeneous annihilating functional transports by genuine double duality
to an actual maximal-compatible vector. Its literal zeroth tensor pairing
forces that vector to vanish, so the homogeneous mode span is the whole piece.
The genuine internal weight decomposition yields the whole tensor carrier.
-/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open Classification.COne VOA.LogTensor VOA.LogTensor.Pz
open Module (Dual)
universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)

/-- The literal genuine zeroth logarithmic tensor mode values. -/
def tensorZeroModeValues : Set (RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW) :=
  Set.range (fun p : ℂ × M₁ × M₂ =>
    (tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 p.1 0 p.2.1 p.2.2)

/-- Every actual generalized tensor weight is linearly spanned by genuine zero modes. -/
theorem tensor_weight_le_zeroMode_span (c : ℂ) :
    (tensorModule hC2 N₁ N₂ h₁ h₂).weight c ≤
      Submodule.span ℂ (tensorZeroModeValues hC2 N₁ N₂ h₁ h₂) := by
  let S := tensorDual hC2 N₁ N₂ h₁ h₂
  let T := tensorModule hC2 N₁ N₂ h₁ h₂
  let η := tensorIntertwiner hC2 N₁ N₂ h₁ h₂
  let P := Submodule.span ℂ (tensorZeroModeValues hC2 N₁ N₂ h₁ h₂)
  let Pc := P.comap (T.weight c).subtype
  have hPc : Pc = ⊤ := by
    apply (Submodule.dualAnnihilator_eq_bot_iff).mp
    rw [Submodule.eq_bot_iff]
    intro f hf
    let φ : RestrictedDual T.toGW := DirectSum.lof ℂ ℂ (fun a => Dual ℂ (T.weight a)) c f
    have hφ : φ ∈ (contraLog (contraLog S)).weight c := ⟨f,rfl⟩
    let s := (doubleDualInverseHom S).toLinearMap φ
    have hs : s ∈ S.weight c := Contra.hom_mem_weight (contraLog (contraLog S)) S
      (doubleDualInverseHom S) hφ
    have hsval : s.1 = 0 := by
      apply bilinear_ext_homogeneous N₁ N₂
      intro a b x y hx hy
      let n := a+b-c-1
      have hc : c=a+b-n-1 := by dsimp [n]; ring
      have hq : η.1 n 0 x y ∈ T.weight c := by
        rw [hc]
        exact η.2.mem_weight hx hy n 0
      let q : T.weight c := ⟨η.1 n 0 x y,hq⟩
      have hqP : q ∈ Pc := Submodule.subset_span ⟨(n,x,y),rfl⟩
      have hfq : f q = 0 := (Submodule.mem_dualAnnihilator f).mp hf q hqP
      have hp : dualPairing T.toGW (η.1 n 0 x y) φ = f q := by
        change dualPairing T.toGW (η.1 n 0 x y)
          (DirectSum.lof ℂ ℂ (fun a => Dual ℂ (T.weight a)) c f) = _
        erw [dualPairing_lof_self T.toGW hq f]
        rfl
      have hb : dualPairing S.toGW s (η.1 n 0 x y) = s.1 x y := by
        change dualPairing S.toGW s ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y) = _
        rw [tensorIntertwiner_logZero,pair_baseModes N₁ N₂ S
          (tensorInclusion hC2 N₁ N₂ h₁ h₂).1 n hx hy hs]
        simp only [if_pos hc,tensorInclusion_apply]
      have hi : dualPairing S.toGW s (η.1 n 0 x y) = dualPairing T.toGW (η.1 n 0 x y) φ :=
        doubleDualInverseHom_pair S φ (η.1 n 0 x y)
      change s.1 x y = 0
      exact hb.symm.trans (hi.trans (hp.trans hfq))
    have hs0 : s=0 := Subtype.ext hsval
    have hφ0 : φ=0 := by
      have hi := LinearEquiv.apply_symm_apply (doubleDualEquiv S) φ
      change iota S.toGW s=φ at hi
      rw [hs0,map_zero] at hi
      exact hi.symm
    have hf0 := congrArg (DirectSum.component ℂ ℂ (fun a => Dual ℂ (T.weight a)) c) hφ0
    dsimp only [φ] at hf0
    erw [DirectSum.component.lof_self,map_zero] at hf0
    exact hf0
  intro q hq
  have hm : (⟨q,hq⟩ : T.weight c) ∈ Pc := hPc ▸ Submodule.mem_top
  exact hm

/-- The LINEAR span of actual canonical zeroth-log tensor modes is the whole carrier. -/
theorem tensor_zeroMode_span_eq_top :
    Submodule.span ℂ (tensorZeroModeValues hC2 N₁ N₂ h₁ h₂) = ⊤ := by
  apply top_unique
  rw [← LogFin.iSup_weight_eq_top (tensorModule hC2 N₁ N₂ h₁ h₂)]
  exact iSup_le (tensor_weight_le_zeroMode_span hC2 N₁ N₂ h₁ h₂)

/-- Literal canonical zeroth modes on genuinely homogeneous source vectors. -/
def tensorHomogeneousZeroModeValues : Set (RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW) :=
  {q | ∃ (n a b : ℂ) (x : M₁) (y : M₂), x ∈ N₁.weight a ∧ y ∈ N₂.weight b ∧
    q=(tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y}

/-- Homogeneous source coefficients already linearly span the actual whole tensor carrier. -/
theorem tensor_homogeneousZeroMode_span_eq_top :
    Submodule.span ℂ (tensorHomogeneousZeroModeValues hC2 N₁ N₂ h₁ h₂) = ⊤ := by
  let η := tensorIntertwiner hC2 N₁ N₂ h₁ h₂
  let P := Submodule.span ℂ (tensorHomogeneousZeroModeValues hC2 N₁ N₂ h₁ h₂)
  have hall : ∀ n x y, η.1 n 0 x y ∈ P := by
    intro n x y
    refine LogFin.induction_on N₁ (C := fun x => η.1 n 0 x y ∈ P) x ?_ ?_ ?_
    · intro a x hx
      refine LogFin.induction_on N₂ (C := fun y => η.1 n 0 x y ∈ P) y ?_ ?_ ?_
      · intro b y hy
        exact Submodule.subset_span ⟨n,a,b,x,y,hx,hy,rfl⟩
      · dsimp only
        rw [map_zero]
        exact P.zero_mem
      · intro y z hy hz
        dsimp only at hy hz ⊢
        rw [map_add]
        exact P.add_mem hy hz
    · dsimp only
      rw [map_zero,LinearMap.zero_apply]
      exact P.zero_mem
    · intro x z hx hz
      dsimp only at hx hz ⊢
      rw [map_add,LinearMap.add_apply]
      exact P.add_mem hx hz
  have hle : Submodule.span ℂ (tensorZeroModeValues hC2 N₁ N₂ h₁ h₂) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨n,x,y⟩,rfl⟩
    exact hall n x y
  rw [tensor_zeroMode_span_eq_top] at hle
  exact top_unique hle

/-- Consequently the literal all-log canonical tensor modes linearly span the carrier. -/
theorem tensor_allMode_span_eq_top :
    Submodule.span ℂ (Set.range (fun p : ℂ × ℕ × M₁ × M₂ =>
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 p.1 p.2.1 p.2.2.1 p.2.2.2)) = ⊤ := by
  apply top_unique
  rw [← tensor_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂]
  apply Submodule.span_mono
  rintro _ ⟨⟨n,x,y⟩,rfl⟩
  exact ⟨(n,0,x,y),rfl⟩

/-- Arbitrary linear maps out of the actual tensor are determined by literal zero modes. -/
theorem tensor_linearMap_ext {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW →ₗ[ℂ] X}
    (h : ∀ n x y, f ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y) =
      g ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y)) : f=g := by
  apply LinearMap.ext_on (tensor_zeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂)
  rintro q ⟨⟨n,x,y⟩,rfl⟩
  exact h n x y

/-- Homogeneous literal zero modes determine every actual linear tensor map. -/
theorem tensor_linearMap_ext_homogeneous {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW →ₗ[ℂ] X}
    (h : ∀ n a b x y, x ∈ N₁.weight a → y ∈ N₂.weight b →
      f ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y) =
        g ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 n 0 x y)) : f=g := by
  apply LinearMap.ext_on (tensor_homogeneousZeroMode_span_eq_top hC2 N₁ N₂ h₁ h₂)
  rintro q ⟨n,a,b,x,y,hx,hy,rfl⟩
  exact h n a b x y hx hy

end VOA.C2Rigid.LocalInjective
