import VOA.Examples.AffineSl2AdmissiblePrimitive
import VOA.Examples.AffineSl2BoundaryMaximalIdeal

/-! # Actual Sugawara energy of affine highest vectors

The normal ordered Sugawara sum on a positive-loop primitive retains only
its horizontal Casimir. This constrains possible primitive degrees in the
actual universal affine vacuum module.
-/
namespace VOA.AffineVOA.SugawaraCov
noncomputable section
open scoped BigOperators
open Module (End)
set_option maxHeartbeats 1200000

/-- Only zero modes survive on a positive-loop primitive. -/
theorem sug0Term_primitive (k : ℂ) (v : WakModule k)
    (hp : ∀ a n, 0 < n → J k a n v = 0) (a b : Fin 3) :
    (∑ᶠ p : ℤ, sug0TermJ k a b p v) = J k b 0 (J k a 0 v) := by
  rw [finsum_eq_single _ (-1)]
  · norm_num [sug0TermJ_apply]
  · intro p hne
    rw [sug0TermJ_apply]
    split_ifs with h
    · rw [hp b (p+1) (by omega), map_zero]
    · rw [hp a (-p-1) (by omega), map_zero]

/-- The horizontal Casimir on an actual highest vector of charge h. -/
theorem horizontalCasimir_highest (k h : ℂ) (v : WakModule k)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = h • v) :
    (∑ a : Fin 3, ∑ b : Fin 3, kappaInv a b • J k b 0 (J k a 0 v)) =
      (h + h^2/2) • v := by
  have hc := LinearMap.congr_fun (J_bracket k 0 1 0 0) v
  norm_num [Fin.sum_univ_succ, fabc, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at hc
  rw [he, map_zero, sub_zero, hh] at hc
  norm_num [Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, kappaInv]
  change J k 1 0 (J k 0 0 v) + (J k 0 0 (J k 1 0 v) +
    (1/2:ℂ) • J k 2 0 (J k 2 0 v)) = _
  simp only [he, hh, hc, map_zero, map_smul, zero_add, smul_smul]
  module

/-- The Sugawara eigenvalue is determined by the actual highest charge. -/
theorem Lsug0_highest_state (k h : ℂ) (v : WakModule k)
    (hp : ∀ a n, 0 < n → J k a n v = 0)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = h • v) :
    Lsug k 0 v = (h*(h+2)/(4*(k+2))) • v := by
  rw [Lsug0_apply]
  simp_rw [sug0Term_primitive k v hp]
  rw [horizontalCasimir_highest k h v he hh, smul_smul]
  congr 1
  simp only [c0, dualCoxeter, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Any nonzero homogeneous affine highest vector satisfies the Casimir equation. -/
theorem highest_energy_constraint (k h : ℂ) (hk : k+2 ≠ 0)
    (n : ℤ) (v : WakModule k) (hv : v ≠ 0) (hn : v ∈ gradingZA k n)
    (hp : ∀ a j, 0 < j → J k a j v = 0)
    (he : J k 0 0 v = 0) (hh : J k 2 0 v = h • v) :
    4*(k+2)*(n:ℂ) = h*(h+2) := by
  have hs := Lsug0_highest_state k h v hp he hh
  rw [Lsug0_eq_negEll0OpA k hk, LinearMap.neg_apply] at hs
  rw [gradingZA_def, Module.End.mem_eigenspace_iff] at hn
  rw [hn, neg_smul, neg_neg] at hs
  have heq := (smul_left_injective ℂ hv) hs
  have hm := (eq_div_iff (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) hk)).mp heq
  simpa only [mul_comm] using hm

/-- The boundary levels force triangular primitive energies. -/
theorem boundary_highest_energy (b : ℕ) (r n : ℤ)
    (v : WakModule (AffineSl2BoundarySingularFamily.level b)) (hv : v ≠ 0)
    (hn : v ∈ gradingZA _ n)
    (hp : ∀ a j, 0 < j → J _ a j v = 0)
    (he : J _ 0 0 v = 0) (hh : J _ 2 0 v = (2*(r:ℂ)) • v) :
    2*n = (AffineSl2BoundarySingularFamily.denominator b : ℤ)*r*(r+1) := by
  have h := highest_energy_constraint _ _
    (AffineSl2BoundarySingularFamily.level_noncritical b) n v hv hn hp he hh
  rw [AffineSl2BoundarySingularFamily.level_add_two] at h
  have hd := AffineSl2BoundarySingularFamily.denominator_cast_ne_zero b
  field_simp [hd] at h
  have hc : (2:ℂ)*(n:ℂ) =
      (AffineSl2BoundarySingularFamily.denominator b:ℂ)*(r:ℂ)*((r:ℂ)+1) := by
    linear_combination h / 2
  exact_mod_cast hc

/-- The same Sugawara computation survives every actual current-intertwining
linear image, including singular-vector quotients. Primitivity is required
only in the image, not of the chosen representative. -/
theorem Lsug0_highest_image {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k h : ℂ) (Φ : WakModule k →ₗ[ℂ] V) (j : Fin 3 → ℤ → End ℂ V)
    (hΦ : ∀ a n x, Φ (J k a n x) = j a n (Φ x)) (v : WakModule k)
    (hp : ∀ a n, 0 < n → j a n (Φ v) = 0)
    (he : j 0 0 (Φ v) = 0) (hh : j 2 0 (Φ v) = h • Φ v) :
    Φ (Lsug k 0 v) = (h*(h+2)/(4*(k+2))) • Φ v := by
  have ht (a b : Fin 3) :
      Φ (∑ᶠ p : ℤ, sug0TermJ k a b p v) = j b 0 (j a 0 (Φ v)) := by
    rw [map_finsum Φ (sug0TermJ_support_finite k a b v)]
    rw [finsum_eq_single _ (-1)]
    · norm_num [sug0TermJ_apply, hΦ]
    · intro p hne
      rw [sug0TermJ_apply]
      split_ifs with h
      · rw [hΦ, hΦ, hp b (p+1) (by omega), map_zero]
      · rw [hΦ, hΦ, hp a (-p-1) (by omega), map_zero]
  have hc := congrArg Φ (LinearMap.congr_fun (J_bracket k 0 1 0 0) v)
  norm_num [Fin.sum_univ_succ, fabc, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at hc
  simp only [hΦ, he, map_zero, sub_zero, hh] at hc
  rw [Lsug0_apply, map_smul]
  simp only [map_sum, map_smul, ht]
  norm_num [Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, kappaInv]
  change c0 k • j 1 0 (j 0 0 (Φ v)) + (c0 k • j 0 0 (j 1 0 (Φ v)) +
    c0 k • (1/2:ℂ) • j 2 0 (j 2 0 (Φ v))) = _
  simp only [he, hh, hc, map_zero, map_smul, smul_smul]
  simp only [c0, dualCoxeter, div_eq_mul_inv, mul_inv_rev]
  module

/-- A primitive class in any current quotient obeys the same actual energy
constraint, even when its representative is not primitive. -/
theorem highest_image_energy_constraint {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k h : ℂ) (hk : k+2 ≠ 0) (Φ : WakModule k →ₗ[ℂ] V)
    (j : Fin 3 → ℤ → End ℂ V)
    (hΦ : ∀ a n x, Φ (J k a n x) = j a n (Φ x))
    (n : ℤ) (v : WakModule k) (hv : Φ v ≠ 0) (hn : v ∈ gradingZA k n)
    (hp : ∀ a a', 0 < a' → j a a' (Φ v) = 0)
    (he : j 0 0 (Φ v) = 0) (hh : j 2 0 (Φ v) = h • Φ v) :
    4*(k+2)*(n:ℂ) = h*(h+2) := by
  have hs := Lsug0_highest_image k h Φ j hΦ v hp he hh
  rw [Lsug0_eq_negEll0OpA k hk, LinearMap.neg_apply] at hs
  rw [gradingZA_def, Module.End.mem_eigenspace_iff] at hn
  rw [hn, neg_smul, neg_neg, map_smul] at hs
  have heq := (smul_left_injective ℂ hv) hs
  have hm := (eq_div_iff (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) hk)).mp heq
  simpa only [mul_comm] using hm

/-- Boundary primitive classes in actual current images have triangular energy. -/
theorem boundary_highest_image_energy {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : ℕ) (Φ : WakModule (AffineSl2BoundarySingularFamily.level b) →ₗ[ℂ] V)
    (j : Fin 3 → ℤ → End ℂ V)
    (hΦ : ∀ a n x, Φ (J _ a n x) = j a n (Φ x))
    (n r : ℤ) (v : WakModule (AffineSl2BoundarySingularFamily.level b))
    (hv : Φ v ≠ 0) (hn : v ∈ gradingZA _ n)
    (hp : ∀ a a', 0 < a' → j a a' (Φ v) = 0)
    (he : j 0 0 (Φ v) = 0) (hh : j 2 0 (Φ v) = (2*(r:ℂ)) • Φ v) :
    2*n = (AffineSl2BoundarySingularFamily.denominator b:ℤ)*r*(r+1) := by
  have h := highest_image_energy_constraint _ _
    (AffineSl2BoundarySingularFamily.level_noncritical b) Φ j hΦ n v hv hn hp he hh
  rw [AffineSl2BoundarySingularFamily.level_add_two] at h
  have hd := AffineSl2BoundarySingularFamily.denominator_cast_ne_zero b
  field_simp [hd] at h
  have hc : (2:ℂ)*(n:ℂ) =
      (AffineSl2BoundarySingularFamily.denominator b:ℂ)*(r:ℂ)*((r:ℂ)+1) := by
    linear_combination h / 2
  exact_mod_cast hc

/-- The first two nonzero triangular energies are p and 3p. -/
theorem triangular_energy_gap (p n r : ℤ) (hp : 0 < p)
    (h : 2*n = p*r*(r+1)) : n = 0 ∨ n = p ∨ 3*p ≤ n := by
  by_cases hr0 : r = 0
  · left; subst r; omega
  by_cases hr1 : r = -1
  · left; subst r; omega
  by_cases hr2 : r = 1
  · right; left; subst r; nlinarith
  by_cases hr3 : r = -2
  · right; left; subst r; nlinarith
  right; right
  have hrr : 6 ≤ r*(r+1) := by
    have : r ≤ -3 ∨ 2 ≤ r := by omega
    rcases this with hle | hge <;> nlinarith
  have hh := mul_le_mul_of_nonneg_left hrr (le_of_lt hp)
  nlinarith

end
end VOA.AffineVOA.SugawaraCov


namespace VOA.AffineSl2BoundaryMaximalIdeal
noncomputable section
open AffineVOA AffineVOA.Inst SingVec
open AffineVOA.SugawaraCov

/-- Actual homogeneous affine primitives in the singular quotient satisfy
Sugawara's charge-energy constraint. -/
theorem singularQuotient_primitive_energy (k h : ℂ) (hk : k+2 ≠ 0)
    (s : WakModule k) (n : ℤ)
    (w : WakModule k ⧸ idealGen (affineSl2VOA_closed k hk) s)
    (hn : w ∈ (gradingZA k n).map (idealGen (affineSl2VOA_closed k hk) s).mkQ)
    (hw : SingularQuotientAffinePrimitive k hk s w)
    (hh : singularQuotientCurrentMode k hk s 2 0 w = h • w) :
    4*(k+2)*(n:ℂ) = h*(h+2) := by
  obtain ⟨v, hv, rfl⟩ := hn
  exact highest_image_energy_constraint k h hk
    (idealGen (affineSl2VOA_closed k hk) s).mkQ
    (singularQuotientCurrentMode k hk s)
    (fun a j x => (singularQuotient_mkQ_J k hk s a j x).symm)
    n v hw.1 hv hw.2.1 hw.2.2 hh

/-- In every actual boundary singular quotient, a primitive of integral
half-charge can occur only at a triangular energy. -/
theorem boundary_singularQuotient_primitive_energy (b : ℕ)
    (s : WakModule (AffineSl2BoundarySingularFamily.level b)) (n r : ℤ)
    (w : WakModule _ ⧸ idealGen (affineSl2VOA_closed _
      (AffineSl2BoundarySingularFamily.level_noncritical b)) s)
    (hn : w ∈ (gradingZA _ n).map (idealGen (affineSl2VOA_closed _
      (AffineSl2BoundarySingularFamily.level_noncritical b)) s).mkQ)
    (hw : SingularQuotientAffinePrimitive _
      (AffineSl2BoundarySingularFamily.level_noncritical b) s w)
    (hh : singularQuotientCurrentMode _
      (AffineSl2BoundarySingularFamily.level_noncritical b) s 2 0 w = (2*(r:ℂ)) • w) :
    2*n = (AffineSl2BoundarySingularFamily.denominator b:ℤ)*r*(r+1) := by
  obtain ⟨v, hv, rfl⟩ := hn
  exact boundary_highest_image_energy b _
    (singularQuotientCurrentMode _
      (AffineSl2BoundarySingularFamily.level_noncritical b) s)
    (fun a j x => (singularQuotient_mkQ_J _ _ s a j x).symm)
    n r v hw.1 hv hw.2.1 hw.2.2 hh

end
end VOA.AffineSl2BoundaryMaximalIdeal
