/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroODE

/-!
# Genus zero on the abstract interface: explicit solutions of the real linear ODE

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. On a connected open set `S` in the
upper half-plane, a holomorphic solution of

`(l z + m) α′(z) = l′ α(z) + m′`, `l, m, l′, m′ ∈ ℝ`, `(l, m) ≠ (0, 0)`,

is one of four explicit functions, each holomorphic on the whole upper half-plane
(`eqOn_explicit_of_real_linear_ode`), with `c = −m/l`:

* `l ≠ 0, l′ ≠ 0` (**power family**): `α z = K (z − c)^A + M₀`, `A = l′/l`, `M₀ = −m′/l′`;
* `l ≠ 0, l′ = 0` (**logarithmic family**): `α z = B log (z − c) + K`, `B = m′/l`;
* `l = 0, l′ ≠ 0` (**exponential family**): `α z = K exp (A z) + M₀`, `A = l′/m`, `M₀ = −m′/l′`;
* `l = 0, l′ = 0` (**affine family**): `α z = B z + K`, `B = m′/m`;

with `A, B, c, M₀` real and `K` complex (principal branches; `z − c` lies in the upper half-plane).
Uniqueness is proved with an integrating factor and `IsOpen.exists_is_const_of_deriv_eq_zero`.
-/

namespace VOA.Moonshine.ConwayNorton

open Filter Topology Set

/-! ### The four integrating-factor arguments -/

section Families

variable {α : ℂ → ℂ} {S : Set ℂ}

lemma sub_ofReal_mem_slitPlane {z : ℂ} (hz : 0 < z.im) (c : ℝ) : z - (c : ℂ) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hz.ne'))

lemma sub_ofReal_ne_zero {z : ℂ} (hz : 0 < z.im) (c : ℝ) : z - (c : ℂ) ≠ 0 :=
  Complex.slitPlane_ne_zero (sub_ofReal_mem_slitPlane hz c)

lemma exists_const_of_hasDerivAt_zero {h : ℂ → ℂ} (hSo : IsOpen S) (hSc : IsPreconnected S)
    (hd : ∀ z ∈ S, HasDerivAt h 0 z) : ∃ K : ℂ, ∀ z ∈ S, h z = K :=
  hSo.exists_is_const_of_deriv_eq_zero hSc
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt) (fun z hz => (hd z hz).deriv)

lemma hasDerivAt_of_differentiableOn (hSo : IsOpen S) (hα : DifferentiableOn ℂ α S) {z : ℂ}
    (hz : z ∈ S) : HasDerivAt α (_root_.deriv α z) z :=
  ((hα z hz).differentiableAt (hSo.mem_nhds hz)).hasDerivAt

/-- **Power family.** `(z − c) α′ = A (α − M₀)` on `S` forces `α = K (z − c)^A + M₀`. -/
theorem eqOn_power_of_ode (hSo : IsOpen S) (hSc : IsPreconnected S) (hSU : ∀ z ∈ S, 0 < z.im)
    (hα : DifferentiableOn ℂ α S) {c A M₀ : ℝ}
    (hode : ∀ z ∈ S, (z - c) * _root_.deriv α z = A * (α z - M₀)) :
    ∃ K : ℂ, ∀ z ∈ S, α z = K * (z - c) ^ (A : ℂ) + M₀ := by
  have hd : ∀ z ∈ S, HasDerivAt (fun z => (α z - M₀) * (z - c) ^ (-(A : ℂ))) 0 z := by
    intro z hz
    have hne := sub_ofReal_ne_zero (hSU z hz) c
    have hp := ((hasDerivAt_id' z).sub_const (c : ℂ)).cpow_const (c := -(A : ℂ))
      (sub_ofReal_mem_slitPlane (hSU z hz) c)
    have hm := ((hasDerivAt_of_differentiableOn hSo hα hz).sub_const (M₀ : ℂ)).mul hp
    convert hm using 1
    have hsplit : (z - (c : ℂ)) ^ (-(A : ℂ)) = (z - c) ^ (-(A : ℂ) - 1) * (z - c) := by
      conv_lhs => rw [show -(A : ℂ) = (-(A : ℂ) - 1) + 1 by ring]
      rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
    rw [hsplit]
    linear_combination (-(z - (c : ℂ)) ^ (-(A : ℂ) - 1)) * hode z hz
  obtain ⟨K, hK⟩ := exists_const_of_hasDerivAt_zero hSo hSc hd
  refine ⟨K, fun z hz => ?_⟩
  have hne := sub_ofReal_ne_zero (hSU z hz) c
  have hpow0 : (z - (c : ℂ)) ^ (A : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hne h.1
  have h1 := hK z hz
  simp only at h1
  rw [Complex.cpow_neg] at h1
  have e : α z - M₀ = K * (z - c) ^ (A : ℂ) := by
    rw [← h1, mul_assoc, inv_mul_cancel₀ hpow0, mul_one]
  linear_combination e

/-- **Logarithmic family.** `(z − c) α′ = B` on `S` forces `α = B log (z − c) + K`. -/
theorem eqOn_log_of_ode (hSo : IsOpen S) (hSc : IsPreconnected S) (hSU : ∀ z ∈ S, 0 < z.im)
    (hα : DifferentiableOn ℂ α S) {c B : ℝ}
    (hode : ∀ z ∈ S, (z - c) * _root_.deriv α z = B) :
    ∃ K : ℂ, ∀ z ∈ S, α z = B * Complex.log (z - c) + K := by
  have hd : ∀ z ∈ S, HasDerivAt (fun z => α z - B * Complex.log (z - c)) 0 z := by
    intro z hz
    have hne := sub_ofReal_ne_zero (hSU z hz) c
    have hl := (((hasDerivAt_id' z).sub_const (c : ℂ)).clog
      (sub_ofReal_mem_slitPlane (hSU z hz) c)).const_mul (B : ℂ)
    have hm := (hasDerivAt_of_differentiableOn hSo hα hz).sub hl
    convert hm using 1
    have hd' : _root_.deriv α z = B / (z - c) := by
      rw [eq_div_iff hne]
      linear_combination hode z hz
    rw [hd']
    ring
  obtain ⟨K, hK⟩ := exists_const_of_hasDerivAt_zero hSo hSc hd
  exact ⟨K, fun z hz => by linear_combination hK z hz⟩

/-- **Exponential family.** `α′ = A (α − M₀)` on `S` forces `α = K exp (A z) + M₀`. -/
theorem eqOn_exp_of_ode (hSo : IsOpen S) (hSc : IsPreconnected S)
    (hα : DifferentiableOn ℂ α S) {A M₀ : ℝ}
    (hode : ∀ z ∈ S, _root_.deriv α z = A * (α z - M₀)) :
    ∃ K : ℂ, ∀ z ∈ S, α z = K * Complex.exp (A * z) + M₀ := by
  have hd : ∀ z ∈ S, HasDerivAt (fun z => (α z - M₀) * Complex.exp (-(A : ℂ) * z)) 0 z := by
    intro z hz
    have he := ((hasDerivAt_id' z).const_mul (-(A : ℂ))).cexp
    have hm := ((hasDerivAt_of_differentiableOn hSo hα hz).sub_const (M₀ : ℂ)).mul he
    convert hm using 1
    linear_combination (-Complex.exp (-(A : ℂ) * z)) * hode z hz
  obtain ⟨K, hK⟩ := exists_const_of_hasDerivAt_zero hSo hSc hd
  refine ⟨K, fun z hz => ?_⟩
  have h1 := hK z hz
  simp only at h1
  have e : α z - M₀ = K * Complex.exp (A * z) := by
    rw [← h1, mul_assoc, ← Complex.exp_add, show -(A : ℂ) * z + A * z = 0 by ring,
      Complex.exp_zero, mul_one]
  linear_combination e

/-- **Affine family.** `α′ = B` on `S` forces `α = B z + K`. -/
theorem eqOn_affine_of_ode (hSo : IsOpen S) (hSc : IsPreconnected S)
    (hα : DifferentiableOn ℂ α S) {B : ℝ} (hode : ∀ z ∈ S, _root_.deriv α z = B) :
    ∃ K : ℂ, ∀ z ∈ S, α z = B * z + K := by
  have hd : ∀ z ∈ S, HasDerivAt (fun z => α z - B * z) 0 z := by
    intro z hz
    have hm := (hasDerivAt_of_differentiableOn hSo hα hz).sub ((hasDerivAt_id' z).const_mul (B : ℂ))
    convert hm using 1
    rw [hode z hz]
    ring
  obtain ⟨K, hK⟩ := exists_const_of_hasDerivAt_zero hSo hSc hd
  exact ⟨K, fun z hz => by linear_combination hK z hz⟩

end Families

/-! ### The dispatcher -/

/-- **Explicit solutions of the real linear ODE**. On a connected open subset `S` of the upper
half-plane, a holomorphic solution of `(l z + m) α′ = l′ α + m′` (`l, m, l′, m′` real,
`(l, m) ≠ 0`) lies in the power, logarithmic, exponential or affine family. -/
theorem eqOn_explicit_of_real_linear_ode {α : ℂ → ℂ} {S : Set ℂ} (hSo : IsOpen S)
    (hSc : IsPreconnected S) (hSU : ∀ z ∈ S, 0 < z.im) (hα : DifferentiableOn ℂ α S)
    {l m l' m' : ℝ} (hlm : l ≠ 0 ∨ m ≠ 0)
    (hode : ∀ z ∈ S, ((l : ℂ) * z + m) * _root_.deriv α z = l' * α z + m') :
    (∃ (c A M₀ : ℝ) (K : ℂ), A ≠ 0 ∧ ∀ z ∈ S, α z = K * (z - c) ^ (A : ℂ) + M₀) ∨
    (∃ (c B : ℝ) (K : ℂ), ∀ z ∈ S, α z = B * Complex.log (z - c) + K) ∨
    (∃ (A M₀ : ℝ) (K : ℂ), A ≠ 0 ∧ ∀ z ∈ S, α z = K * Complex.exp (A * z) + M₀) ∨
    (∃ (B : ℝ) (K : ℂ), ∀ z ∈ S, α z = B * z + K) := by
  by_cases hl : l = 0
  · have hm : m ≠ 0 := hlm.resolve_left (not_not.mpr hl)
    have hmc : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
    by_cases hl' : l' = 0
    · -- affine
      right; right; right
      obtain ⟨K, hK⟩ := eqOn_affine_of_ode (B := m' / m) hSo hSc hα (fun z hz => by
        have h1 := hode z hz
        rw [hl, hl'] at h1
        push_cast at h1 ⊢
        rw [eq_div_iff hmc]
        linear_combination h1)
      exact ⟨m' / m, K, hK⟩
    · -- exponential
      right; right; left
      have hl'c : (l' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl'
      obtain ⟨K, hK⟩ := eqOn_exp_of_ode (A := l' / m) (M₀ := -(m' / l')) hSo hSc hα
        (fun z hz => by
          have h1 := hode z hz
          rw [hl] at h1
          push_cast at h1 ⊢
          field_simp
          linear_combination h1)
      exact ⟨l' / m, -(m' / l'), K, div_ne_zero hl' hm, hK⟩
  · have hlc : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
    by_cases hl' : l' = 0
    · -- logarithmic
      right; left
      obtain ⟨K, hK⟩ := eqOn_log_of_ode (c := -(m / l)) (B := m' / l) hSo hSc hSU hα
        (fun z hz => by
          have h1 := hode z hz
          rw [hl'] at h1
          push_cast at h1 ⊢
          field_simp
          linear_combination h1)
      exact ⟨-(m / l), m' / l, K, hK⟩
    · -- power
      left
      have hl'c : (l' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl'
      obtain ⟨K, hK⟩ := eqOn_power_of_ode (c := -(m / l)) (A := l' / l) (M₀ := -(m' / l'))
        hSo hSc hSU hα (fun z hz => by
          have h1 := hode z hz
          push_cast at h1 ⊢
          field_simp
          linear_combination h1)
      exact ⟨-(m / l), l' / l, -(m' / l'), K, div_ne_zero hl' hl, hK⟩

end VOA.Moonshine.ConwayNorton
