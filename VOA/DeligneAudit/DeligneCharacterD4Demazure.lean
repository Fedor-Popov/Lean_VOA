/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Functional

/-!
# Demazure operators on `R = 𝕜[x^±, z^±]` (layer 5)

The isobaric Demazure operators of `D₄` act on the `z`-exponents (coordinates `1..4` of `V`) by the
string formula; the affine operator `π₀` (level one, `e^δ = q`, `e^{-α₀} = q⁻¹z^θ`) likewise.

* `piR_div` (division formula): `(1 - z^{-α}) π_α f = f - z^{-α} s_α(f)`;
* `pi0R_div`: `(1 - q⁻¹z^θ) π₀ f = f - q⁻²z^{2θ} (s_θ f)(q^{-θ} z)`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-- The Euclidean pairing of the `z`-parts. -/
def dotZ (v w : V) : ℤ := ∑ j : Fin 4, v j.succ * w j.succ

/-- `v ↦ v - (v, α) α`. -/
def reflV (α : V) : V →+ V where
  toFun v := v - dotZ v α • α
  map_zero' := by simp [dotZ]
  map_add' v w := by
    simp only [dotZ, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_smul]; abel

theorem reflV_apply (α v : V) : reflV α v = v - dotZ v α • α := rfl

/-- The string formula for `π_α` on one monomial. -/
def piStr (α : V) (v : V) : R :=
  if 0 ≤ dotZ v α then ∑ k ∈ Finset.range ((dotZ v α).toNat + 1), mon (v - (k : ℤ) • α) 1
  else -∑ k ∈ Finset.range ((-dotZ v α).toNat - 1), mon (v + ((k : ℤ) + 1) • α) 1

/-- The isobaric Demazure operator `π_α`. -/
def piR (α : V) : R →ₗ[Kq] R := Finsupp.linearCombination Kq (piStr α)

theorem piR_mon (α v : V) (c : Kq) : piR α (mon v c) = c • piStr α v := by
  change (Finsupp.linearCombination Kq _) (Finsupp.single v c) = _
  rw [Finsupp.linearCombination_single]

theorem mon_smul (v : V) (c : Kq) : c • mon v 1 = mon v c := by
  rw [mon, mon, AddMonoidAlgebra.smul_single', mul_one]

/-- **Division formula** for `π_α`. -/
theorem piR_div (α : V) (f : R) :
    (1 - mon (-α) 1) * piR α f = f - mon (-α) 1 * domHom (reflV α) f := by
  have : LinearMap.mulLeft Kq (1 - mon (-α) 1) ∘ₗ piR α =
      LinearMap.id - LinearMap.mulLeft Kq (mon (-α) 1) ∘ₗ (domHom (reflV α)).toLinearMap := by
    apply Finsupp.lhom_ext
    intro v c
    change (1 - mon (-α) 1) * piR α (mon v c) =
      mon v c - mon (-α) 1 * domHom (reflV α) (mon v c)
    rw [piR_mon, domHom_mon, mon_mul_mon, mul_smul_comm, reflV_apply, one_mul, piStr]
    split_ifs with hn
    · -- `n ≥ 0`: telescoping `∑ (z^{v-kα} - z^{v-(k+1)α})`
      set n := dotZ v α
      have ht : (1 - mon (-α) 1) * ∑ k ∈ Finset.range (n.toNat + 1), mon (v - (k : ℤ) • α) 1 =
          ∑ k ∈ Finset.range (n.toNat + 1),
            (mon (v - (k : ℤ) • α) 1 - mon (v - ((k + 1 : ℕ) : ℤ) • α) 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sub_mul, one_mul, mon_mul_mon, mul_one]
        congr 2
        push_cast; module
      rw [ht, Finset.sum_range_sub' (fun k : ℕ => mon (v - (k : ℤ) • α) 1)]
      simp only [Nat.cast_zero, zero_smul, sub_zero, Nat.cast_add, Nat.cast_one]
      rw [smul_sub, mon_smul, mon_smul, Int.toNat_of_nonneg hn]
      congr 2
      module
    · -- `n < 0`
      set n := dotZ v α
      have ht : (1 - mon (-α) 1) * ∑ k ∈ Finset.range ((-n).toNat - 1),
            mon (v + ((k : ℤ) + 1) • α) 1 =
          ∑ k ∈ Finset.range ((-n).toNat - 1),
            (mon (v + ((k + 1 : ℕ) : ℤ) • α) 1 - mon (v + (k : ℤ) • α) 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sub_mul, one_mul, mon_mul_mon, mul_one]
        congr 2; module
      rw [mul_neg, ht, Finset.sum_range_sub (fun k : ℕ => mon (v + (k : ℤ) • α) 1)]
      simp only [Nat.cast_zero, zero_smul, add_zero]
      have hm : (((-n).toNat - 1 : ℕ) : ℤ) = -n - 1 := by omega
      rw [hm, smul_neg, smul_sub, mon_smul, mon_smul, neg_sub]
      congr 2
      module
  have h := congrArg (fun φ : R →ₗ[Kq] R => φ f) this
  simpa using h

/-- `θ = e₁ + e₂` in `z`-coordinates. -/
def thetaV : V := zv 0 + zv 1

theorem chiTheta_eq_dotZ (v : V) : chiTheta v = dotZ v thetaV := by
  simp [chiTheta, dotZ, thetaV, zv, Fin.sum_univ_four, Pi.single_apply]

theorem dotZ_thetaV_thetaV : dotZ thetaV thetaV = 2 := by decide

/-- The string formula for the affine `π₀` at level one. -/
def pi0Str (v : V) : R :=
  if 0 ≤ 1 - dotZ v thetaV then
    ∑ k ∈ Finset.range ((1 - dotZ v thetaV).toNat + 1), mon (v + (k : ℤ) • thetaV) (qq ^ (-(k : ℤ)))
  else -∑ k ∈ Finset.range ((-(1 - dotZ v thetaV)).toNat - 1),
    mon (v - ((k : ℤ) + 1) • thetaV) (qq ^ ((k : ℤ) + 1))

/-- The affine Demazure operator `π₀`. -/
def pi0R : R →ₗ[Kq] R := Finsupp.linearCombination Kq pi0Str

theorem pi0R_mon (v : V) (c : Kq) : pi0R (mon v c) = c • pi0Str v := by
  change (Finsupp.linearCombination Kq _) (Finsupp.single v c) = _
  rw [Finsupp.linearCombination_single]

theorem smul_mon (a : Kq) (v : V) (c : Kq) : a • mon v c = mon v (a * c) := by
  rw [mon, mon, AddMonoidAlgebra.smul_single']

theorem dotZ_sub_smul (v w α : V) (k : ℤ) : dotZ (v - k • α) w = dotZ v w - k * dotZ α w := by
  simp only [dotZ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]

/-- **Division formula** for `π₀`: `(1 - q⁻¹z^θ) π₀ f = f - q⁻²z^{2θ} (s_θ f)(q^{-θ}z)`. -/
theorem pi0R_div (f : R) :
    (1 - mon thetaV qq⁻¹) * pi0R f = f - mon ((2 : ℤ) • thetaV) (qq ^ (-2 : ℤ)) *
      twist chiTheta qq⁻¹ (inv_ne_zero qq_ne_zero) (domHom (reflV thetaV) f) := by
  have hq := qq_ne_zero
  have : LinearMap.mulLeft Kq (1 - mon thetaV qq⁻¹) ∘ₗ pi0R =
      LinearMap.id - LinearMap.mulLeft Kq (mon ((2 : ℤ) • thetaV) (qq ^ (-2 : ℤ))) ∘ₗ
        (twist chiTheta qq⁻¹ (inv_ne_zero qq_ne_zero)).toLinearMap ∘ₗ
        (domHom (reflV thetaV)).toLinearMap := by
    apply Finsupp.lhom_ext
    intro v c
    change (1 - mon thetaV qq⁻¹) * pi0R (mon v c) = mon v c - mon ((2 : ℤ) • thetaV)
      (qq ^ (-2 : ℤ)) * twist chiTheta qq⁻¹ _ (domHom (reflV thetaV) (mon v c))
    rw [pi0R_mon, domHom_mon, twist_mon, mon_mul_mon, mul_smul_comm, reflV_apply,
      chiTheta_eq_dotZ, dotZ_sub_smul, dotZ_thetaV_thetaV, pi0Str]
    split_ifs with hn
    · set n := 1 - dotZ v thetaV with hndef
      have ht : (1 - mon thetaV qq⁻¹) * ∑ k ∈ Finset.range (n.toNat + 1),
            mon (v + (k : ℤ) • thetaV) (qq ^ (-(k : ℤ))) =
          ∑ k ∈ Finset.range (n.toNat + 1),
            (mon (v + (k : ℤ) • thetaV) (qq ^ (-(k : ℤ))) -
              mon (v + ((k + 1 : ℕ) : ℤ) • thetaV) (qq ^ (-((k + 1 : ℕ) : ℤ)))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sub_mul, one_mul, mon_mul_mon]
        congr 2
        · push_cast; module
        · push_cast; rw [← zpow_neg_one, ← zpow_add₀ hq]; ring_nf
      rw [ht, Finset.sum_range_sub' (fun k : ℕ => mon (v + (k : ℤ) • thetaV) (qq ^ (-(k : ℤ))))]
      simp only [Nat.cast_zero, zero_smul, add_zero, neg_zero, zpow_zero]
      rw [smul_sub, smul_mon, smul_mon, mul_one]
      have hN : ((n.toNat + 1 : ℕ) : ℤ) = 2 - dotZ v thetaV := by
        push_cast; rw [Int.toNat_of_nonneg hn, hndef]; ring
      rw [hN]
      congr 2
      · module
      · rw [inv_zpow', mul_comm c, ← mul_assoc, ← zpow_add₀ hq]; ring_nf
    · set n := 1 - dotZ v thetaV with hndef
      have ht : (1 - mon thetaV qq⁻¹) * ∑ k ∈ Finset.range ((-n).toNat - 1),
            mon (v - ((k : ℤ) + 1) • thetaV) (qq ^ ((k : ℤ) + 1)) =
          ∑ k ∈ Finset.range ((-n).toNat - 1),
            (mon (v - ((k + 1 : ℕ) : ℤ) • thetaV) (qq ^ ((k + 1 : ℕ) : ℤ)) -
              mon (v - (k : ℤ) • thetaV) (qq ^ (k : ℤ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sub_mul, one_mul, mon_mul_mon]
        congr 2
        · push_cast; module
        · rw [← zpow_neg_one, ← zpow_add₀ hq]; ring_nf
      rw [mul_neg, ht, Finset.sum_range_sub (fun k : ℕ => mon (v - (k : ℤ) • thetaV) (qq ^ (k : ℤ)))]
      simp only [Nat.cast_zero, zero_smul, sub_zero, zpow_zero]
      have hm : (((-n).toNat - 1 : ℕ) : ℤ) = -n - 1 := by omega
      rw [hm, smul_neg, smul_sub, smul_mon, smul_mon, neg_sub, mul_one]
      congr 2
      · rw [hndef]; module
      · rw [inv_zpow', mul_comm c, ← mul_assoc, ← zpow_add₀ hq, hndef]; ring_nf
  have h := congrArg (fun φ : R →ₗ[Kq] R => φ f) this
  simpa using h

end

end VOA.DeligneAudit.DeligneCharacter.D4K
