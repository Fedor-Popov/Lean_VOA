/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzForward
import VOA.Modules.LogTensorPzMapTruncation

/-! # Genuine logarithmic Jacobi gives P(1) compatibility

The m=0 Jacobi slice at the unique weight-compatible exponent is exactly the
compatibility condition. Finite homogeneous decomposition extends it to all vectors.
-/

namespace VOA.LogTensor.Pz
open scoped BigOperators
open VOA.Huang.PzTensorRho
universe u
variable {V M₁ M₂ R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N : LogVModule W R)
variable (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N.toWeakModule)

/-- Completed evaluation is uniformly lower truncated under the genuine coproduct. -/
theorem forward_truncated (r : C2Rigid.RestrictedDual N.toGW) (d : ℤ) (u : V)
    (hu : u ∈ W.grading d) :
    TruncAt N₁.toWeakModule N₂.toWeakModule u (forward N₁ N₂ N Y r) :=
  mapMode_truncated N₁.toWeakModule N₂.toWeakModule (contraLog N).toWeakModule
    (forward N₁ N₂ N Y) (forward_map_mode N₁ N₂ N Y) r d u hu

private theorem dsl_add_left {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {beta : BilinearDual (M₁ := M₁) (M₂ := M₂)} {u : V}
    (htr : TruncAt A₁ A₂ u beta) (m ell : ℤ) (x z : M₁) (y : M₂) :
    Dsl A₁ A₂ u m ell beta (x+z) y =
      Dsl A₁ A₂ u m ell beta x y + Dsl A₁ A₂ u m ell beta z y := by
  unfold Dsl Out InL InR
  simp only [map_add,LinearMap.add_apply,mul_add]
  rw [finsum_add_distrib (Out_fin _ _ htr m ell x y) (Out_fin _ _ htr m ell z y),
    finsum_add_distrib (InL_fin _ u m ell beta x y) (InL_fin _ u m ell beta z y),
    finsum_add_distrib (InR_fin _ u m ell beta x y) (InR_fin _ u m ell beta z y)]
  ring

private theorem dsl_add_right {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {beta : BilinearDual (M₁ := M₁) (M₂ := M₂)} {u : V}
    (htr : TruncAt A₁ A₂ u beta) (m ell : ℤ) (x : M₁) (y z : M₂) :
    Dsl A₁ A₂ u m ell beta x (y+z) =
      Dsl A₁ A₂ u m ell beta x y + Dsl A₁ A₂ u m ell beta x z := by
  unfold Dsl Out InL InR
  simp only [map_add,LinearMap.add_apply,mul_add]
  rw [finsum_add_distrib (Out_fin _ _ htr m ell x y) (Out_fin _ _ htr m ell x z),
    finsum_add_distrib (InL_fin _ u m ell beta x y) (InL_fin _ u m ell beta x z),
    finsum_add_distrib (InR_fin _ u m ell beta x y) (InR_fin _ u m ell beta x z)]
  ring

/-- On a homogeneous triple the actual logarithmic Jacobi identity is precisely the
compatibility slice of its completed matrix coefficient. -/
theorem forward_compatible_homogeneous {d : ℤ} {u : V} (hu : u ∈ W.grading d)
    (ell : ℤ) {a b c : ℂ} {x : M₁} {y : M₂} {r : C2Rigid.RestrictedDual N.toGW}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (hr : r ∈ (contraLog N).weight c) :
    Dsl N₁.toWeakModule N₂.toWeakModule u 0 ell (forward N₁ N₂ N Y r) x y = 0 := by
  let n : ℂ := a+b+d-ell-c-2
  have hj := Y.2.jacobi u x y ell 0 n 0
  have hp := congrArg (C2Rigid.dualPairingFlip N.toGW r) hj
  change C2Rigid.dualPairingFlip N.toGW r
      (∑ᶠ i, IsLogIntertwining.jacL N₂.toWeakModule N.toWeakModule Y.1 u x y ell 0 n 0 i) =
    C2Rigid.dualPairingFlip N.toGW r
      (∑ᶠ i, IsLogIntertwining.jacR N₁.toWeakModule Y.1 u x y ell 0 n 0 i) at hp
  rw [map_finsum (C2Rigid.dualPairingFlip N.toGW r)
      (IsLogIntertwining.jacL_support_finite Y.2.truncation u x y ell 0 n 0),
    map_finsum (C2Rigid.dualPairingFlip N.toGW r)
      (IsLogIntertwining.jacR_support_finite Y.1 u x y ell 0 n 0)] at hp
  have hL : ∀ i : ℤ, C2Rigid.dualPairingFlip N.toGW r
      (IsLogIntertwining.jacL N₂.toWeakModule N.toWeakModule Y.1 u x y ell 0 n 0 i) =
      (negOnePow i * cbz ell i) *
        (rhoL N₁.toWeakModule N₂.toWeakModule u (ell-i) (forward N₁ N₂ N Y r) x y -
          negOnePow ell * forward N₁ N₂ N Y r x (mode (N₂.YM u) i y)) := by
    intro i
    simp only [IsLogIntertwining.jacL,map_smul,map_sub,C2Rigid.dualPairingFlip_apply,
      smul_eq_mul,add_zero,zero_add]
    rw [paired_current_logZero N₁ N₂ N Y hu (ell-i) (n+i) hx hy hr
      (by dsimp [n]; push_cast; ring)]
    rw [forward_homogeneous N₁ N₂ N Y hx (N₂.mode_mem_weight hu hy i) hr]
    have hn : a+(b+d-i-1)-c-1 = ell+n-i := by dsimp [n]; ring
    rw [hn]
  have hR : ∀ i : ℤ, C2Rigid.dualPairingFlip N.toGW r
      (IsLogIntertwining.jacR N₁.toWeakModule Y.1 u x y ell 0 n 0 i) =
      cbz 0 i * forward N₁ N₂ N Y r (mode (N₁.YM u) (ell+i) x) y := by
    intro i
    simp only [IsLogIntertwining.jacR,map_smul,C2Rigid.dualPairingFlip_apply,
      smul_eq_mul,zero_add]
    rw [forward_homogeneous N₁ N₂ N Y (N₁.mode_mem_weight hu hx (ell+i)) hy hr]
    have hn : (a+d-((ell+i:ℤ):ℂ)-1)+b-c-1 = n-i := by dsimp [n]; push_cast; ring
    rw [hn]
    simp only [Int.cast_zero,zero_add]
  rw [finsum_congr hL,finsum_congr hR] at hp
  have hsign : ∀ i : ℤ, negOnePow i * negOnePow ell = negOnePow (ell-i) := by
    intro i
    rw [← negOnePow_add,show i+ell = (ell-i)+2*i by ring,negOnePow_add]
    have hi : negOnePow (2*i) = 1 := by unfold negOnePow; rw [if_pos (even_two_mul i)]
    rw [hi,mul_one]
  have he : ∀ i : ℤ, (negOnePow i * cbz ell i) *
      (rhoL N₁.toWeakModule N₂.toWeakModule u (ell-i) (forward N₁ N₂ N Y r) x y -
        negOnePow ell * forward N₁ N₂ N Y r x (mode (N₂.YM u) i y)) =
      (negOnePow i * cbz ell i) *
        rhoL N₁.toWeakModule N₂.toWeakModule u (ell-i) (forward N₁ N₂ N Y r) x y -
      (cbz ell i * negOnePow (ell-i)) * forward N₁ N₂ N Y r x (mode (N₂.YM u) i y) := by
    intro i
    rw [mul_sub,mul_assoc,← hsign i]
    ring
  rw [finsum_congr he] at hp
  have htr := forward_truncated N₁ N₂ N Y r d u hu
  have hfinO := Out_fin N₁.toWeakModule N₂.toWeakModule htr 0 ell x y
  have hfinR := InR_fin N₂.toWeakModule u 0 ell (forward N₁ N₂ N Y r) x y
  simp only [zero_add] at hfinO hfinR
  rw [finsum_sub_distrib hfinO hfinR] at hp
  unfold Dsl Out InL InR
  simp only [zero_add]
  linear_combination hp

/-- Every genuine logarithmic operator gives an actual compatible module map into
the algebraic tensor dual; no ordinary-module or semisimplicity premise is used. -/
theorem forward_compatibleMap :
    CompatibleMap N₁ N₂ (contraLog N) (forward N₁ N₂ N Y) := by
  refine ⟨forward_map_mode N₁ N₂ N Y,forward_truncated N₁ N₂ N Y,?_⟩
  intro r d u hu ell x y
  have hregular : ∀ r : C2Rigid.RestrictedDual N.toGW,
      forward N₁ N₂ N Y r ∈ regularForms N₁.toWeakModule N₂.toWeakModule := by
    intro r
    refine LogFin.induction_on (contraLog N)
      (C := fun r => forward N₁ N₂ N Y r ∈ regularForms N₁.toWeakModule N₂.toWeakModule)
      r ?_ ?_ ?_
    · intro c r hr dd v hv
      refine ⟨forward_truncated N₁ N₂ N Y r dd v hv,?_⟩
      intro L xx yy
      have htr := forward_truncated N₁ N₂ N Y r dd v hv
      refine LogFin.induction_on N₁ (C := fun xx =>
        Dsl N₁.toWeakModule N₂.toWeakModule v 0 L (forward N₁ N₂ N Y r) xx yy = 0)
        xx ?_ ?_ ?_
      · intro a xx hx
        refine LogFin.induction_on N₂ (C := fun yy =>
          Dsl N₁.toWeakModule N₂.toWeakModule v 0 L (forward N₁ N₂ N Y r) xx yy = 0)
          yy ?_ ?_ ?_
        · intro b yy hy
          exact forward_compatible_homogeneous N₁ N₂ N Y hv L hx hy hr
        · simp [Dsl,Out,InL,InR]
        · intro yy zz hyy hzz
          rw [dsl_add_right htr, hyy,hzz,add_zero]
      · simp [Dsl,Out,InL,InR]
      · intro xx zz hxx hzz
        rw [dsl_add_left htr,hxx,hzz,add_zero]
    · simpa only [map_zero] using (regularForms N₁.toWeakModule N₂.toWeakModule).zero_mem
    · intro r s hr hs
      simpa only [map_add] using
        (regularForms N₁.toWeakModule N₂.toWeakModule).add_mem hr hs
  exact (hregular r d u hu).2 ell x y

end VOA.LogTensor.Pz
