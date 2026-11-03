/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzCompatibleLift

/-! # Actual completed evaluation transposed to the restricted dual

At z=1, log(1)=0, an actual logarithmic operator gives a linear map from the
actual contragredient of its target into the algebraic tensor dual. The current
commutator makes its matrix coefficients intertwine the genuine P(1) action.
-/

namespace VOA.LogTensor.Pz
open Module (End Dual)
open scoped BigOperators
open VOA.Huang.PzTensorRho
universe u
variable {V M₁ M₂ R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}

private noncomputable def completedComponentPair (N : LogVModule W R) (c : ℂ) :
    Dual ℂ (N.weight c) →ₗ[ℂ] Completion N →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f t => f (t c))
    (fun f g t => rfl) (fun s f t => rfl)
    (fun f t z => f.map_add _ _) (fun s f t => f.map_smul _ _)

/-- The genuine pairing of the restricted dual with the product completion. -/
noncomputable def completedPair (N : LogVModule W R) :
    C2Rigid.RestrictedDual N.toGW →ₗ[ℂ] Completion N →ₗ[ℂ] ℂ :=
  DirectSum.toModule ℂ ℂ (Completion N →ₗ[ℂ] ℂ) (completedComponentPair N)

theorem completedPair_lof (N : LogVModule W R) (c : ℂ) (f : Dual ℂ (N.weight c)) (t : Completion N) :
    completedPair N (DirectSum.lof ℂ ℂ (fun c => Dual ℂ (N.weight c)) c f) t = f (t c) := by
  exact congrArg (fun g : Completion N →ₗ[ℂ] ℂ => g t)
    (DirectSum.toModule_lof (R := ℂ) (φ := completedComponentPair N) c f)

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N : LogVModule W R)
variable (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N.toWeakModule)

/-- Actual logarithmic evaluation, transposed along the genuine completion pairing. -/
noncomputable def forward : C2Rigid.RestrictedDual N.toGW →ₗ[ℂ]
    BilinearDual (M₁ := M₁) (M₂ := M₂) where
  toFun r := LinearMap.mk₂ ℂ (fun x y => completedPair N r (evaluateOne N₁ N₂ N Y x y))
    (fun x z y => by dsimp only; simp)
    (fun s x y => by dsimp only; simp)
    (fun x y z => by dsimp only; simp)
    (fun s x y => by dsimp only; simp)
  map_add' r s := by ext x y; simp only [LinearMap.mk₂_apply,map_add,LinearMap.add_apply]
  map_smul' s r := by
    ext x y
    simp only [LinearMap.mk₂_apply,map_smul,LinearMap.smul_apply,RingHom.id_apply]

/-- The actual dual matrix coefficient on a homogeneous triple. -/
theorem forward_homogeneous {a b c : ℂ} {x : M₁} {y : M₂}
    {r : C2Rigid.RestrictedDual N.toGW}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (hr : r ∈ (contraLog N).weight c) :
    forward N₁ N₂ N Y r x y =
      C2Rigid.dualPairing N.toGW (Y.1 (a+b-c-1) 0 x y) r := by
  obtain ⟨f,rfl⟩ := hr
  simp only [forward,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.mk₂_apply]
  erw [completedPair_lof N c f]
  erw [C2Rigid.dualPairing_lof N.toGW (Y.1 (a+b-c-1) 0 x y) c f]
  have hmem : Y.1 (a+b-c-1) 0 x y ∈ N.weight c := by
    have h := Y.2.mem_weight hx hy (a+b-c-1) 0
    convert h using 1 <;> ring
  have hval := evaluateOne_homogeneous N₁ N₂ N Y hx hy c
  apply congrArg f
  apply Subtype.ext
  rw [hval,C2Rigid.internalProjTo_coe_mem N.toGW hmem]

/-- Current action on the paired logarithmic zeroth mode equals the actual untwisted
P(1) coproduct, at the unique weight-compatible exponent. -/
theorem paired_current_logZero {d : ℤ} {u : V} (hu : u ∈ W.grading d)
    (p : ℤ) (n : ℂ) {a b c : ℂ} {x : M₁} {y : M₂}
    {r : C2Rigid.RestrictedDual N.toGW}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (hr : r ∈ (contraLog N).weight c)
    (hc : c = a+b+d-p-n-2) :
    C2Rigid.dualPairing N.toGW (mode (N.YM u) p (Y.1 n 0 x y)) r =
      rhoL N₁.toWeakModule N₂.toWeakModule u p (forward N₁ N₂ N Y r) x y := by
  have hcomm := Y.2.commutator u x y p n 0
  have he : mode (N.YM u) p (Y.1 n 0 x y) =
      Y.1 n 0 x (mode (N₂.YM u) p y) +
        ∑ᶠ i : ℤ, cbz p i • Y.1 (p+n-i) 0 (mode (N₁.YM u) i x) y := by
    rw [← hcomm]
    abel
  have hp := congrArg (C2Rigid.dualPairingFlip N.toGW r) he
  have hfin : (Function.support (fun i : ℤ =>
      cbz p i • Y.1 (p+n-i) 0 (mode (N₁.YM u) i x) y)).Finite := by
    have h := IsLogIntertwining.jacR_support_finite (A₁ := N₁.toWeakModule) Y.1 u x y 0 p n 0
    change (Function.support (fun i : ℤ =>
      cbz p i • Y.1 (p+n-i) 0 (mode (N₁.YM u) (0+i) x) y)).Finite at h
    simpa only [zero_add] using h
  rw [map_add,map_finsum (C2Rigid.dualPairingFlip N.toGW r) hfin] at hp
  simp only [map_smul,C2Rigid.dualPairingFlip_apply,smul_eq_mul] at hp
  rw [hp,rhoL_apply,forward_homogeneous N₁ N₂ N Y hx (N₂.mode_mem_weight hu hy p) hr]
  have hn : a+(b+d-p-1)-c-1 = n := by rw [hc]; ring
  rw [hn]
  congr 1
  apply finsum_congr
  intro i
  rw [forward_homogeneous N₁ N₂ N Y (N₁.mode_mem_weight hu hx i) hy hr]
  have hn' : (a+d-i-1)+b-c-1 = p+n-i := by rw [hc]; ring
  rw [hn']

/-- The actual transpose of completed evaluation intertwines every homogeneous
contragredient target mode with the genuine twisted coproduct. -/
theorem forward_map_mode (d : ℤ) (u : V) (hu : u ∈ W.grading d) (p : ℤ)
    (r : C2Rigid.RestrictedDual N.toGW) :
    forward N₁ N₂ N Y (mode ((contraLog N).YM u) p r) =
      tauHat N₁.toWeakModule N₂.toWeakModule d u p (forward N₁ N₂ N Y r) := by
  refine LogFin.induction_on (contraLog N)
    (C := fun r => forward N₁ N₂ N Y (mode ((contraLog N).YM u) p r) =
      tauHat N₁.toWeakModule N₂.toWeakModule d u p (forward N₁ N₂ N Y r)) r ?_ ?_ ?_
  · intro c r hr
    apply bilinear_ext_homogeneous N₁ N₂
    intro a b x y hx hy
    have hmr := (contraLog N).mode_mem_weight hu hr p
    rw [forward_homogeneous N₁ N₂ N Y hx hy hmr]
    let n : ℂ := a+b-(c+d-p-1)-1
    have hm : Y.1 n 0 x y ∈ N.weight (c+d-p-1) := by
      have h := Y.2.mem_weight hx hy n 0
      convert h using 1 <;> dsimp [n] <;> ring
    change C2Rigid.dualPairing N.toGW (Y.1 n 0 x y) (mode (C2Rigid.YMdual N.toGW u) p r) = _
    rw [C2Rigid.dualPairing_mode_dualAdj N.toGW hu p r hm,
      C2Rigid.dualAdj_clean N.toGW hu p hm]
    change C2Rigid.dualPairingFlip N.toGW r
      ((-1:ℂ)^d • ∑ j ∈ Finset.range (d.toNat+1), (j.factorial:ℂ)⁻¹ •
        mode (N.YM ((W.L 1 ^ j) u)) (2*d-p-2-j) (Y.1 n 0 x y)) = _
    rw [map_smul,map_sum]
    simp only [map_smul,C2Rigid.dualPairingFlip_apply,smul_eq_mul]
    simp only [tauHat,LinearMap.smul_apply,LinearMap.coe_sum,Finset.sum_apply,smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [paired_current_logZero N₁ N₂ N Y (VertexOperatorAlgebra.L_one_pow_mem W hu j)
      (2*d-p-2-j) n hx hy hr (by dsimp [n]; push_cast; ring)]
  · simp only [map_zero]
    rw [← tauEnd_apply,map_zero]
  · intro r s hr hs
    simp only [map_add,hr,hs]
    simp only [← tauEnd_apply,map_add]

end VOA.LogTensor.Pz
