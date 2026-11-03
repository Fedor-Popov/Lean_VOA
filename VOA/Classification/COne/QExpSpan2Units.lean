/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpSpanAlgebra

/-!
# Coefficient rings `ℤ[1/M][ζ]` for the cusp-localized Cramer frame

`frameRing M ζ = ℤ[1/M][ζ] ⊂ ℂ`. For `ω^N = 1`, `ω ≠ 1` the identity
`(1 - ω) · Σ_{j<N} j ω^j = -N` shows `1/(1 - ω) ∈ ℤ[ζ, 1/N]`; this is the only cyclotomic
input. Every constant term of a normalized weight-one Eisenstein series lies in
`ℤ[ζ, 1/(2N)]`, and the specific values used as pivots are units there.
-/

open Complex

noncomputable section

namespace VOA.Classification.COne.SSHecke

/-- The coefficient ring `ℤ[1/M][ζ]`. -/
abbrev frameRing (M : ℕ) (ζ : ℂ) : Subalgebra (zInv M) ℂ :=
  Algebra.adjoin (zInv M) {ζ}

theorem frameRing_fg {M N : ℕ} (hN : 0 < N) {ζ : ℂ} (hζ : ζ ^ N = 1) :
    (frameRing M ζ).toSubmodule.FG :=
  (isIntegral_of_pow_eq_one_R hN hζ).fg_adjoin_singleton

theorem zeta_mem_frameRing (M : ℕ) (ζ : ℂ) : ζ ∈ frameRing M ζ :=
  Algebra.subset_adjoin rfl

theorem natCast_mem_frameRing (M : ℕ) (ζ : ℂ) (n : ℕ) : (n : ℂ) ∈ frameRing M ζ :=
  (frameRing M ζ).natCast_mem n

theorem intCast_mem_frameRing (M : ℕ) (ζ : ℂ) (n : ℤ) : (n : ℂ) ∈ frameRing M ζ :=
  (frameRing M ζ).intCast_mem n

theorem zeta_pow_mem_frameRing (M : ℕ) (ζ : ℂ) (n : ℕ) : ζ ^ n ∈ frameRing M ζ :=
  (frameRing M ζ).pow_mem (zeta_mem_frameRing M ζ) n

/-- `ℤ[1/M] ⊂ ℤ[1/M][ζ]`. -/
theorem zInv_mem_frameRing {M : ℕ} (ζ : ℂ) {z : ℂ} (hz : z ∈ zInv M) : z ∈ frameRing M ζ := by
  simpa using (frameRing M ζ).algebraMap_mem (⟨z, hz⟩ : zInv M)

/-- `1/d ∈ ℤ[1/M]` for a divisor `d` of `M`. -/
theorem inv_natCast_mem_zInv {M d : ℕ} (hM : M ≠ 0) (hd : d ∣ M) : ((d : ℂ))⁻¹ ∈ zInv M := by
  obtain ⟨m, rfl⟩ := hd
  have h0 : d ≠ 0 := fun h => hM (by simp [h])
  have hm : m ≠ 0 := fun h => hM (by simp [h])
  have hM' : ((d * m : ℕ) : ℂ)⁻¹ ∈ zInv (d * m) := Algebra.subset_adjoin rfl
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h0
  have : ((d : ℂ))⁻¹ = (m : ℂ) * ((d * m : ℕ) : ℂ)⁻¹ := by
    push_cast; field_simp
  rw [this]
  exact (zInv (d * m)).mul_mem ((zInv (d * m)).natCast_mem m) hM'

theorem inv_natCast_mem_frameRing {M d : ℕ} (ζ : ℂ) (hM : M ≠ 0) (hd : d ∣ M) :
    ((d : ℂ))⁻¹ ∈ frameRing M ζ :=
  zInv_mem_frameRing ζ (inv_natCast_mem_zInv hM hd)

/-- The basic cyclotomic identity `(1-ω) Σ_{j<n} j ω^j = Σ_{j<n} ω^j - 1 - (n-1) ω^n`. -/
theorem one_sub_mul_weighted_geom (ω : ℂ) (n : ℕ) :
    (1 - ω) * ∑ j ∈ Finset.range n, (j : ℂ) * ω ^ j =
      ∑ j ∈ Finset.range n, ω ^ j - 1 - ((n : ℂ) - 1) * ω ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- `(1-ω) Σ_{j<N} j ω^j = -N` when `ω^N = 1`, `ω ≠ 1`. -/
theorem one_sub_mul_weighted_geom_root {N : ℕ} {ω : ℂ} (hω : ω ^ N = 1) (h1 : ω ≠ 1) :
    (1 - ω) * ∑ j ∈ Finset.range N, (j : ℂ) * ω ^ j = -N := by
  rw [one_sub_mul_weighted_geom, hω]
  have hg : ∑ j ∈ Finset.range N, ω ^ j = 0 := by
    have h := mul_geom_sum ω N
    rw [hω, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h1)
  rw [hg]
  ring

/-- `1/(1-ω) ∈ ℤ[1/M][ζ]` for `ω = ζ^b`, `ω^N = 1`, `ω ≠ 1`, `N ∣ M`. -/
theorem inv_one_sub_mem_frameRing {M N : ℕ} {ζ : ℂ} (hM : M ≠ 0) (hNM : N ∣ M) (hN : 0 < N)
    (hζ : ζ ^ N = 1) (b : ℕ) (h1 : ζ ^ b ≠ 1) : (1 - ζ ^ b)⁻¹ ∈ frameRing M ζ := by
  have hω : (ζ ^ b) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hid := one_sub_mul_weighted_geom_root hω h1
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsub : (1 - ζ ^ b) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have heq : (1 - ζ ^ b)⁻¹ =
      -((N : ℂ))⁻¹ * ∑ j ∈ Finset.range N, (j : ℂ) * (ζ ^ b) ^ j := by
    field_simp
    linear_combination hid
  rw [heq]
  refine (frameRing M ζ).mul_mem ((frameRing M ζ).neg_mem
    (inv_natCast_mem_frameRing ζ hM hNM)) ((frameRing M ζ).sum_mem fun j _ => ?_)
  exact (frameRing M ζ).mul_mem (natCast_mem_frameRing M ζ j)
    ((frameRing M ζ).pow_mem (zeta_pow_mem_frameRing M ζ b) j)

/-- An element whose inverse is also in a subalgebra is a unit there. -/
theorem isUnit_of_inv_mem {R : Type*} [CommRing R] [Algebra R ℂ] {A : Subalgebra R ℂ}
    {x : ℂ} (hx : x ∈ A) (hxi : x⁻¹ ∈ A) (h0 : x ≠ 0) : IsUnit (⟨x, hx⟩ : A) := by
  refine ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hxi⟩, ?_, ?_⟩, rfl⟩ <;>
    apply Subtype.ext <;> simp [h0]

end VOA.Classification.COne.SSHecke
