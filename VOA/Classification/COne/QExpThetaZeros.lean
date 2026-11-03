import VOA.Classification.COne.QExpThetaProduct

/-! # Product zero locus and torsion-point nonvanishing

These theorems concern the explicit product, not yet the theta series.
-/

open Complex
open scoped UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

theorem theta_unitSquare_not_lattice (τ : ℍ) {α β : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hab : ¬(α = 0 ∧ β = 0)) (m k : ℤ) :
    (α : ℂ) * τ + β ≠ (m : ℂ) + (k : ℂ) * τ := by
  intro he
  have hi := congrArg Complex.im he
  simp only [add_im, mul_im, ofReal_re, ofReal_im, intCast_re, intCast_im,
    zero_mul, add_zero, zero_add] at hi
  have hk : α = (k : ℝ) := (mul_right_cancel₀ τ.im_pos.ne' hi)
  have hk0 : 0 ≤ k := by exact_mod_cast (hk ▸ hα0)
  have hk1 : k < 1 := by exact_mod_cast (hk ▸ hα1)
  have hkz : k = 0 := by omega
  have hα : α = 0 := by simpa [hkz] using hk
  have hr := congrArg Complex.re he
  simp only [hα, hkz, ofReal_zero, Int.cast_zero, zero_mul, zero_add, add_zero,
    ofReal_re, intCast_re] at hr
  have hm0 : 0 ≤ m := by exact_mod_cast (hr ▸ hβ0)
  have hm1 : m < 1 := by exact_mod_cast (hr ▸ hβ1)
  have hmz : m = 0 := by omega
  exact hab ⟨hα, by simpa [hmz] using hr⟩

/-- Nonzero torsion indices avoid the lattice, also on the boundary `a=0`. -/
theorem theta_torsion_not_lattice {N : ℕ} (hN : 0 < N) (a b : Fin N)
    (hab : ¬(a.val = 0 ∧ b.val = 0)) (τ : ℍ) (m k : ℤ) :
    (a.val : ℂ) / N * τ + (b.val : ℂ) / N ≠ (m : ℂ) + (k : ℂ) * τ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (a.val : ℝ) / N < 1 := (div_lt_one hNR).mpr (by exact_mod_cast a.isLt)
  have hb : (b.val : ℝ) / N < 1 := (div_lt_one hNR).mpr (by exact_mod_cast b.isLt)
  have hn : ¬((a.val : ℝ) / N = 0 ∧ (b.val : ℝ) / N = 0) := by
    rintro ⟨ha0, hb0⟩
    apply hab
    constructor
    · exact_mod_cast (div_eq_zero_iff.mp ha0).resolve_right hNR.ne'
    · exact_mod_cast (div_eq_zero_iff.mp hb0).resolve_right hNR.ne'
  simpa only [ofReal_div, ofReal_natCast] using
    theta_unitSquare_not_lattice τ (α := (a.val : ℝ) / N) (β := (b.val : ℝ) / N)
      (by positivity) ha (by positivity) hb hn m k

theorem thetaShiftedProduct_torsion_ne_zero {N : ℕ} (hN : 0 < N) (a b : Fin N)
    (hab : ¬(a.val = 0 ∧ b.val = 0)) (τ : ℍ) :
    thetaShiftedProduct ((a.val : ℂ) / N * τ + (b.val : ℂ) / N) τ ≠ 0 :=
  thetaShiftedProduct_ne_zero τ _ (theta_torsion_not_lattice hN a b hab τ)

/-- The converse zero-locus inclusion: a lattice point kills an actual factor. -/
theorem thetaShiftedProduct_lattice_zero (τ : ℂ) (m k : ℤ) :
    thetaShiftedProduct ((m : ℂ) + (k : ℂ) * τ) τ = 0 := by
  unfold thetaShiftedProduct
  by_cases hk : k ≤ 0
  · have hn : ((-k).toNat : ℂ) = -(k : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (neg_nonneg.mpr hk), Int.cast_neg]
    have hf : thetaEulerProduct (thetaExp τ) (thetaExp ((m : ℂ) + (k : ℂ) * τ)) = 0 := by
      apply tprod_of_exists_eq_zero
      refine ⟨(-k).toNat, ?_⟩
      rw [← thetaExp_nat_mul, ← thetaExp_add, hn,
        show (m : ℂ) + k * τ + -k * τ = m by ring]
      rw [(thetaExp_eq_one_iff _).mpr ⟨m, rfl⟩, sub_self]
    rw [hf, zero_mul]
  · have hk1 : 0 ≤ k - 1 := by omega
    have hn : ((k - 1).toNat : ℂ) = (k : ℂ) - 1 := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hk1, Int.cast_sub, Int.cast_one]
    have hf : thetaEulerProduct (thetaExp τ)
        (thetaExp (τ - ((m : ℂ) + (k : ℂ) * τ))) = 0 := by
      apply tprod_of_exists_eq_zero
      refine ⟨(k - 1).toNat, ?_⟩
      rw [← thetaExp_nat_mul, ← thetaExp_add, hn,
        show τ - ((m : ℂ) + k * τ) + (k - 1) * τ = -m by ring]
      rw [(thetaExp_eq_one_iff _).mpr ⟨-m, by simp⟩, sub_self]
    rw [hf, mul_zero]

/-- Exact zero set of the convergent product. -/
theorem thetaShiftedProduct_eq_zero_iff (τ : ℍ) (x : ℂ) :
    thetaShiftedProduct x τ = 0 ↔ ∃ m k : ℤ, x = (m : ℂ) + (k : ℂ) * τ := by
  constructor
  · intro hz
    by_contra! hn
    exact thetaShiftedProduct_ne_zero τ x hn hz
  · rintro ⟨m, k, rfl⟩
    exact thetaShiftedProduct_lattice_zero τ m k

/-- Period one of the product. -/
theorem thetaShiftedProduct_add_one (x τ : ℂ) :
    thetaShiftedProduct (x + 1) τ = thetaShiftedProduct x τ := by
  have h1 : thetaExp 1 = 1 := (thetaExp_eq_one_iff _).mpr ⟨1, by simp⟩
  have hm1 : thetaExp (-1) = 1 := (thetaExp_eq_one_iff _).mpr ⟨-1, by simp⟩
  simp only [thetaShiftedProduct, thetaExp_add, h1, mul_one,
    show τ - (x + 1) = (τ - x) + -1 by ring, thetaExp_add, hm1]

/-- Quasi-period tau. This holds even at the zero lattice. -/
theorem thetaShiftedProduct_add_tau (x : ℂ) (τ : ℍ) :
    thetaShiftedProduct (x + τ) τ = -(thetaExp x)⁻¹ * thetaShiftedProduct x τ := by
  have hr := thetaExp_norm_lt_one τ.im_pos
  have hu := thetaExp_ne_zero x
  have hi : thetaExp (-x) = (thetaExp x)⁻¹ := by
    simp [thetaExp, Complex.exp_neg, mul_neg]
  have he : thetaExp ((τ : ℂ) - x) = (thetaExp x)⁻¹ * thetaExp τ := by
    rw [sub_eq_add_neg, thetaExp_add, hi, mul_comm]
  have hf := thetaEulerProduct_shift hr (thetaExp x)
  have hg := thetaEulerProduct_shift hr ((thetaExp x)⁻¹)
  simp only [thetaShiftedProduct, thetaExp_add,
    show (τ : ℂ) - (x + τ) = -x by ring, hi, he]
  rw [hf, hg]
  field_simp
  ring

end VOA.Classification.COne.SSHecke
