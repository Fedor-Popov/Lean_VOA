/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSCyclotomicAssembly
import VOA.Huang.NgSchauenburgIndicatorGalois

/-!
# Galois action on mixed generalized indicators

* `trace_zpow_galois`: if `E^K = 1` and the field automorphism `τ` of `ℂ` acts as `z ↦ z^c`
  on the `K`-th roots of unity, then `τ (Tr E^l) = Tr E^{l c}` for every integer `l`.
* `ringEquiv_eq_of_mem_adjoin`: two automorphisms of `ℂ` agreeing on `g` agree on `ℚ[g]`.
* `mixed_indicatorAll_galois`: on a mixed object `X_i ⊠ X_j` of a modular category, with
  `N = twistOrder`, `τ (ν_{m,l}) = ν_{m,l c}` for `m ≠ 0` whenever `τ` acts as `z ↦ z^c` on the
  `|m| N`-th roots of unity (the rotation has order dividing `|m| N` by the mixed twist identity).
* `mixed_indicatorInt_add_mul_degree`: `ν_{n+1, l + k(n+1)} = t^{-k} ν_{n+1,l}` with
  `t = θ_i/θ_j`.

All statements are unconditional (no residual hypotheses).
-/

noncomputable section
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace VOA.Huang.NSGaloisCore

open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence
open Polynomial

section Trace

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Integer powers of a root of unity only depend on the exponent modulo the order. -/
theorem zpow_eq_zpow_emod_of_pow_eq_one {ζ : ℂ} {K : ℕ} (hK : 0 < K) (hζ : ζ ^ K = 1) (n : ℤ) :
    ζ ^ n = ζ ^ (n % (K : ℤ)) := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hK.ne'] at hζ; exact zero_ne_one hζ
  conv_lhs => rw [← Int.emod_add_mul_ediv n K]
  rw [zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

/-- **The Galois action on traces of a finite-order operator.** -/
theorem trace_zpow_galois (E : W ≃ₗ[ℂ] W) {K : ℕ} (hK : 0 < K)
    (hE : E.toLinearMap ^ K = 1) (τ : ℂ ≃+* ℂ) (c : ℤ)
    (hτ : ∀ z : ℂ, z ^ K = 1 → τ z = z ^ c) (l : ℤ) :
    τ (LinearMap.trace ℂ W (E ^ l).toLinearMap) =
      LinearMap.trace ℂ W (E ^ (l * c)).toLinearMap := by
  let f := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ℂ) (M := W)
  have hf : ∀ g : W ≃ₗ[ℂ] W, f g = g.toLinearMap := fun _ => rfl
  have hE' : E ^ K = 1 := by
    apply LinearEquiv.toLinearMap_injective
    rw [← hf, map_pow, hf, hE]; rfl
  have hK0 : K ≠ 0 := hK.ne'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / K) with hζdef
  have hζ : IsPrimitiveRoot ζ K := Complex.isPrimitiveRoot_exp K hK0
  obtain ⟨p, hp⟩ := exists_trace_power_polynomial E.toLinearMap hK hE hζ
  have key : ∀ n : ℤ, LinearMap.trace ℂ W (E ^ n).toLinearMap = aeval (ζ ^ n) p := by
    intro n
    set r : ℕ := (n % (K : ℤ)).toNat with hrdef
    have hr : (r : ℤ) = n % (K : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hK0))
    have h1 : E ^ n = E ^ r := by
      rw [zpow_eq_zpow_emod' n hE', ← hr, zpow_natCast]
    have h2 : ζ ^ n = ζ ^ r := by
      rw [zpow_eq_zpow_emod_of_pow_eq_one hK hζ.pow_eq_one n, ← hr, zpow_natCast]
    rw [h1, h2, ← hp r, ← hf, map_pow, hf]
  have hroot : (ζ ^ l) ^ K = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
  rw [key, key]
  calc τ (aeval (ζ ^ l) p) = (τ : ℂ →+* ℂ).toRatAlgHom (aeval (ζ ^ l) p) := rfl
    _ = aeval ((τ : ℂ →+* ℂ).toRatAlgHom (ζ ^ l)) p := (aeval_algHom_apply _ _ _).symm
    _ = aeval (τ (ζ ^ l)) p := rfl
    _ = _ := by rw [hτ _ hroot, ← zpow_mul]

end Trace

/-- Two automorphisms of `ℂ` that agree on `g` agree on `ℚ[g]`. -/
theorem ringEquiv_eq_of_mem_adjoin (σ τ : ℂ ≃+* ℂ) {g : ℂ} (h : σ g = τ g) {x : ℂ}
    (hx : x ∈ Algebra.adjoin ℚ ({g} : Set ℂ)) : σ x = τ x := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact h
  | algebraMap r =>
    rw [show algebraMap ℚ ℂ r = (r : ℂ) from rfl, map_ratCast, map_ratCast]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]

section Mixed

universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

theorem mixed_twistRatio_ne_zero (F : SphericalFusion C) (M : Modular F) (i j : F.Label) :
    M.twistScalar i / M.twistScalar j ≠ 0 :=
  div_ne_zero (M.toRibbon.twistScalar_ne_zero i) (M.toRibbon.twistScalar_ne_zero j)

theorem mixed_twistRatio_pow (F : SphericalFusion C) (M : Modular F) (i j : F.Label) :
    (M.twistScalar i / M.twistScalar j) ^ M.toRibbon.twistOrder = 1 := by
  rw [div_pow, twistScalar_pow_twistOrder, twistScalar_pow_twistOrder, div_one]

theorem mixed_j_eq (F : SphericalFusion C) (M : Modular F) (i j : F.Label) :
    (F.j (mixedCenter (F.simple i) (F.simple j)).1).hom =
      (M.twistScalar i / M.twistScalar j) •
        centralDrinfeldMorphism (mixedCenter (F.simple i) (F.simple j)) :=
  mixedTwistIdentity_holds F M i j

/-- The Galois action on a positive-degree mixed indicator. -/
theorem mixed_indicatorInt_galois (F : SphericalFusion C) (M : Modular F) (i j : F.Label)
    (V : C) (n : ℕ) (τ : ℂ ≃+* ℂ) (c : ℤ)
    (hτ : ∀ z : ℂ, z ^ ((n + 1) * M.toRibbon.twistOrder) = 1 → τ z = z ^ c) (l : ℤ) :
    τ (generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple i) (F.simple j)) V n l) =
      generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple i) (F.simple j)) V n (l * c) := by
  letI := F.homFinite (mixedCenter (F.simple i) (F.simple j)).1 (tensorPower V (n + 1))
  have hrot := generalizedRotation_pow_mul_eq_one F.toPivotal
    (mixedCenter (F.simple i) (F.simple j)) V n M.toRibbon.twistOrder
    (mixed_twistRatio_ne_zero F M i j) (mixed_j_eq F M i j) (mixed_twistRatio_pow F M i j)
  exact trace_zpow_galois _ (Nat.mul_pos (Nat.succ_pos n) M.toRibbon.finite_twist.1)
    hrot τ c hτ l

/-- **The Galois action on a mixed generalized indicator with nonzero first index.** -/
theorem mixed_indicatorAll_galois (F : SphericalFusion C) (M : Modular F) (i j : F.Label)
    (V : C) (m : ℤ) (hm : m ≠ 0) (τ : ℂ ≃+* ℂ) (c : ℤ)
    (hτ : ∀ z : ℂ, z ^ (m.natAbs * M.toRibbon.twistOrder) = 1 → τ z = z ^ c) (l : ℤ) :
    τ (generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) V m l) =
      generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) V m (l * c) := by
  have hpos : 0 < m.natAbs := Int.natAbs_pos.mpr hm
  have hsucc : m.natAbs - 1 + 1 = m.natAbs := Nat.sub_add_cancel hpos
  rcases lt_or_gt_of_ne hm with hneg | hposm
  · simp only [generalizedIndicatorAll, show ¬ (0 < m) from not_lt.mpr hneg.le, if_false, hm]
    have hτ' : ∀ z : ℂ, z ^ ((m.natAbs - 1 + 1) * M.toRibbon.twistOrder) = 1 → τ z = z ^ c := by
      rw [hsucc]; exact hτ
    rw [mixed_indicatorInt_galois F M i j Vᘁ (m.natAbs - 1) τ c hτ' (-l), neg_mul]
  · simp only [generalizedIndicatorAll, hposm, if_true]
    have he : m.toNat = m.natAbs := by omega
    have hτ' : ∀ z : ℂ, z ^ ((m.toNat - 1 + 1) * M.toRibbon.twistOrder) = 1 → τ z = z ^ c := by
      rw [he, hsucc]; exact hτ
    exact mixed_indicatorInt_galois F M i j V (m.toNat - 1) τ c hτ' l

/-- The T move along a positive row: shifting the second index by `k` degrees multiplies by
`t^{-k}`, `t = θ_i/θ_j`. -/
theorem mixed_indicatorInt_add_mul_degree (F : SphericalFusion C) (M : Modular F)
    (i j : F.Label) (V : C) (n : ℕ) (l k : ℤ) :
    generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple i) (F.simple j)) V n
        (l + k * (n + 1 : ℕ)) =
      ((M.twistScalar i / M.twistScalar j) ^ k)⁻¹ *
        generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple i) (F.simple j)) V n l := by
  have ht := mixed_twistRatio_ne_zero F M i j
  have hadd := generalizedIndicatorInt_add_degree F (mixedCenter (F.simple i) (F.simple j)) V n
    ht (mixed_j_eq F M i j)
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show l + ((k : ℤ) + 1) * (n + 1 : ℕ) = (l + (k : ℤ) * (n + 1 : ℕ)) + (n + 1 : ℕ) by ring,
      hadd, ih, zpow_add_one₀ ht]
    rw [mul_inv, ← mul_assoc, mul_comm (M.twistScalar i / M.twistScalar j)⁻¹]
  | pred k ih =>
    have h := hadd (l + (-(k : ℤ) - 1) * (n + 1 : ℕ))
    rw [show l + (-(k : ℤ) - 1) * (n + 1 : ℕ) + (n + 1 : ℕ) = l + (-(k : ℤ)) * (n + 1 : ℕ) by
      ring, ih] at h
    rw [zpow_sub_one₀ ht]
    have ht' : (M.twistScalar i / M.twistScalar j)⁻¹ ≠ 0 := inv_ne_zero ht
    rw [mul_inv, inv_inv]
    calc generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple i) (F.simple j)) V n
          (l + (-(k : ℤ) - 1) * (n + 1 : ℕ))
        = (M.twistScalar i / M.twistScalar j) *
            ((M.twistScalar i / M.twistScalar j)⁻¹ *
              generalizedIndicatorInt F.toPivotal (mixedCenter (F.simple i) (F.simple j)) V n
                (l + (-(k : ℤ) - 1) * (n + 1 : ℕ))) := by
          rw [← mul_assoc, mul_inv_cancel₀ ht, one_mul]
      _ = _ := by rw [← h]; ring

end Mixed

end VOA.Huang.NSGaloisCore
