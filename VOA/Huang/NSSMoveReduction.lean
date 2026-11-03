import VOA.Huang.NSCyclotomicAssembly

/-! # Reducing the mixed S step to positive products

This file proves implications, not the categorical S identity. Euclidean descent
derives charge symmetry from the same-sign S moves and the existing base charge.
Thus a separate general duality theorem is unnecessary for this reduction.
-/

noncomputable section
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
open scoped MatrixGroups

section Abstract
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Iteration of the T step for an arbitrary family of row functionals. -/
theorem rowT_zpow (σ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) (I : ℤ → ℤ → W → ℂ)
    (hT : ∀ m l z, I m (l + m) z = I m l (σ ModularGroup.T⁻¹ z))
    (m l k : ℤ) (z : W) :
    I m (l + k * m) z = I m l (σ (ModularGroup.T ^ (-k)) z) := by
  have hc (g h : SL(2, ℤ)) (w : W) : σ g (σ h w) = σ (g * h) w := by
    rw [map_mul, LinearEquiv.mul_apply]
  induction k using Int.induction_on generalizing z with
  | zero => simp
  | succ k ih =>
    rw [show l + ((k : ℤ) + 1) * m = (l + k * m) + m by ring, hT, ih, hc]
    congr 2
    rw [neg_add, zpow_add, zpow_neg_one]
  | pred k ih =>
    have ht := hT m (l + (-(k : ℤ) - 1) * m) (σ ModularGroup.T z)
    rw [show l + (-(k : ℤ) - 1) * m + m = l + -(k : ℤ) * m by ring,
      ih] at ht
    simp only [hc, inv_mul_cancel, map_one, le_one_apply] at ht
    rw [ht.symm]
    congr 2
    rw [show -(-(k : ℤ) - 1) = -(-(k : ℤ)) + 1 by ring, zpow_add, zpow_one]

/-- Same-sign S moves imply charge symmetry on all primitive rows with
nonzero first coordinate. The descent uses the remainder of the second index. -/
theorem primitiveCharge_of_sameSignSMove
    (σ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) (I : ℤ → ℤ → W → ℂ)
    (hT : ∀ m l z, I m (l + m) z = I m l (σ ModularGroup.T⁻¹ z))
    (hC : ∀ z, I (-1) 0 z = I 1 0 (σ (ModularGroup.S ^ 2) z))
    (hS : ∀ m l, 0 < m * l → IsCoprime m l → ∀ z,
      I l (-m) z = I m l (σ ModularGroup.S⁻¹ z)) :
    ∀ m l, m ≠ 0 → IsCoprime m l → ∀ z,
      I (-m) (-l) z = I m l (σ (ModularGroup.S ^ 2) z) := by
  have hc (g h : SL(2, ℤ)) (w : W) : σ g (σ h w) = σ (g * h) w := by
    rw [map_mul, LinearEquiv.mul_apply]
  have hct (k : ℤ) : ModularGroup.S ^ 2 * ModularGroup.T ^ k =
      ModularGroup.T ^ k * ModularGroup.S ^ 2 := by
    have h : Commute (ModularGroup.S ^ 2) ModularGroup.T := by
      change ModularGroup.S ^ 2 * ModularGroup.T = ModularGroup.T * ModularGroup.S ^ 2
      decide
    exact (h.zpow_right k).eq
  have hcs : (ModularGroup.S⁻¹ * ModularGroup.S ^ 2 * ModularGroup.S : SL(2, ℤ)) =
      ModularGroup.S ^ 2 := by decide
  have hcc : (ModularGroup.S ^ 2 * ModularGroup.S ^ 2 : SL(2, ℤ)) = 1 := by decide
  have hshift (m r k : ℤ)
      (h : ∀ z, I (-m) (-r) z = I m r (σ (ModularGroup.S ^ 2) z)) (z : W) :
      I (-m) (-(r + k * m)) z =
        I m (r + k * m) (σ (ModularGroup.S ^ 2) z) := by
    rw [show -(r + k * m) = -r + k * -m by ring,
      rowT_zpow σ I hT, h, rowT_zpow σ I hT, hc, hc, hct]
  have hpos : ∀ n : ℕ, ∀ l : ℤ, 0 < n → IsCoprime (n : ℤ) l → ∀ z,
      I (-(n : ℤ)) (-l) z = I n l (σ (ModularGroup.S ^ 2) z) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hn hcop z
      have hn' : (0 : ℤ) < n := by exact_mod_cast hn
      have hr0 := Int.emod_nonneg l hn'.ne'
      have hrlt := Int.emod_lt_of_pos l hn'
      have hr : IsCoprime (n : ℤ) (l % n) := by
        have he := hcop.add_mul_right_right (-(l / n))
        have eq : l + -(l / n) * (n : ℤ) = l % n := by
          have := Int.emod_add_ediv_mul l (n : ℤ)
          linear_combination -this
        rwa [eq] at he
      have hrem : ∀ w, I (-(n : ℤ)) (-(l % n)) w =
          I n (l % n) (σ (ModularGroup.S ^ 2) w) := by
        by_cases hz : l % (n : ℤ) = 0
        · have hn1 : (n : ℤ) = 1 := by
            rw [hz] at hr
            rcases Int.isUnit_iff.mp (isCoprime_zero_right.mp hr) with h | h <;> omega
          simpa [hz, hn1] using hC
        · have hrpos : 0 < l % (n : ℤ) := by omega
          have hsmall : (l % (n : ℤ)).toNat < n := by omega
          have hi := ih (l % (n : ℤ)).toNat hsmall (-(n : ℤ)) (by omega)
            (by simpa only [Int.toNat_of_nonneg hr0] using hr.symm.neg_right)
          intro w
          have hsneg := hS (-(n : ℤ)) (-(l % n)) (by nlinarith)
            hr.neg_left.neg_right (σ ModularGroup.S w)
          simp only [neg_neg, hc, inv_mul_cancel, map_one, le_one_apply] at hsneg
          rw [← hsneg]
          have hi' := hi (σ ModularGroup.S w)
          simp only [Int.toNat_of_nonneg hr0, neg_neg] at hi'
          rw [hi', hS (n : ℤ) (l % n) (mul_pos hn' hrpos) hr, hc, hc, hcs]
      have he := hshift (n : ℤ) (l % n) (l / n) hrem z
      rwa [Int.emod_add_ediv_mul] at he
  intro m l hm hcop z
  by_cases hp : 0 < m
  · simpa only [Int.toNat_of_nonneg hp.le] using
      hpos m.toNat l (by omega) (by simpa only [Int.toNat_of_nonneg hp.le] using hcop) z
  · have hn : 0 < -m := by omega
    have he := hpos (-m).toNat (-l) (by omega)
      (by simpa only [Int.toNat_of_nonneg hn.le] using hcop.neg_left.neg_right)
      (σ (ModularGroup.S ^ 2) z)
    simpa only [Int.toNat_of_nonneg hn.le, neg_neg, hc, hcc, map_one, le_one_apply]
      using he.symm

end Abstract

universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- The remaining S identity for primitive rows of positive product. Both
coordinates may be negative. This is a restriction of `MixedNonzeroSMove`. -/
def MixedSameSignSMove (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ →
    ∀ (a : F.Label) (m l : ℤ), 0 < m * l → IsCoprime m l →
      ∀ z : F.Label × F.Label → ℂ,
        mixedRow F a l (-m) z = mixedRow F a m l (mixedRepresentation ρ ModularGroup.S⁻¹ z)

open Classical in
/-- The positive-product case alone suffices; charge symmetry follows by
Euclidean descent rather than being added as another categorical assumption. -/
theorem mixedNonzeroSMove_of_sameSign (F : SphericalFusion C) (M : Modular F)
    (hS : MixedSameSignSMove F M) : MixedNonzeroSMove F M := by
  intro ρ hr a m l hm hl hcop z
  by_cases hpos : 0 < m * l
  · exact hS ρ hr a m l hpos hcop z
  · have hc := primitiveCharge_of_sameSignSMove (mixedRepresentation ρ)
      (fun m l z => mixedRow F a m l z) (mixedTMove_holds F M ρ hr a)
      (chargeSymmetry_one_zero F M ρ hr a) (hS ρ hr a)
    have hs := hS ρ hr a (-l) m (by
      have hne := mul_ne_zero hm hl
      have hneg : m * l < 0 := by omega
      simpa only [neg_mul, mul_neg, mul_comm] using neg_pos.mpr hneg)
      hcop.symm.neg_left (mixedRepresentation ρ ModularGroup.S⁻¹ z)
    simp only [← LinearEquiv.mul_apply, ← map_mul] at hs
    have he : (ModularGroup.S⁻¹ * ModularGroup.S⁻¹ : SL(2, ℤ)) =
        ModularGroup.S ^ 2 := by decide
    rw [he] at hs
    have hcharge := hc (-l) m (neg_ne_zero.mpr hl) hcop.symm.neg_left z
    simpa only [neg_neg] using hcharge.trans hs.symm

/-- Exact equivalence, with no independent charge-symmetry premise. -/
theorem mixedNonzeroSMove_iff_sameSign (F : SphericalFusion C) (M : Modular F) :
    MixedNonzeroSMove F M ↔ MixedSameSignSMove F M := by
  constructor
  · intro h ρ hr a m l hp hcop z
    exact h ρ hr a m l (by intro h; simp [h] at hp)
      (by intro h; simp [h] at hp) hcop z
  · exact mixedNonzeroSMove_of_sameSign F M

end VOA.Huang.NSCongruence
