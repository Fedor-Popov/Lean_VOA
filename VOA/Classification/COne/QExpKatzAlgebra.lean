/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkQExpAway
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Algebra for a localized q-expansion principle

This file proves the algebraic steps, not the arithmetic existence of modular forms.
Finite modules over `zInv M` descend to `awaySat M` of finite integer modules.
Division by a power of q times a unit preserves coefficient modules, including after
a finite extension of `zInv M`. The unit condition is essential: division by `5 + q`
introduces arbitrarily large powers of 5 in the denominators.

The last identity is the squared-determinant form of Cramer's rule; it requires no
invertibility hypothesis. These are the algebraic operations used in the cusp-frame
route.
-/

noncomputable section

namespace VOA.Classification.COne.SSHecke

/-- Saturation is closed under scalars from `ℤ[1/M]`. -/
theorem awaySat_zInv_smul {M : ℕ} (hM : M ≠ 0) (L : Submodule ℤ ℂ)
    (r : zInv M) {z : ℂ} (hz : z ∈ awaySat M L) :
    r • z ∈ awaySat M L := by
  obtain ⟨a, e, ha⟩ := mem_zInv hM r.property
  obtain ⟨f, hf⟩ := hz
  refine ⟨e + f, ?_⟩
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have heq : (M : ℂ) ^ (e + f) * (r • z) = a • ((M : ℂ) ^ f * z) := by
    change (M : ℂ) ^ (e + f) * ((r : ℂ) * z) = _
    rw [ha, zsmul_eq_mul]
    field_simp
    ring
  rw [heq]
  exact L.smul_mem a hf

/-- A finite `ℤ[1/M]`-module of complex numbers has a finite integer lattice of generators. -/
theorem fg_zInv_exists_lattice {M : ℕ} (hM : M ≠ 0)
    {K : Submodule (zInv M) ℂ} (hK : K.FG) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ z ∈ K, z ∈ awaySat M L := by
  obtain ⟨s, hs⟩ := hK
  refine ⟨Submodule.span ℤ (s : Set ℂ), Submodule.fg_span s.finite_toSet, ?_⟩
  intro z hz
  rw [← hs] at hz
  induction hz using Submodule.span_induction with
  | mem z hz => exact mem_awaySat_of_mem (Submodule.subset_span hz)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r z _ hz => exact awaySat_zInv_smul hM _ r hz

/-- Multiplication by an `A`-valued power series preserves coefficients in an `A`-module. -/
theorem coeff_mul_map_mem {R : Type*} [CommRing R] [Algebra R ℂ]
    {L : Submodule R ℂ} {b : PowerSeries ℂ} (t : PowerSeries R)
    (hb : ∀ n, PowerSeries.coeff n b ∈ L) (n : ℕ) :
    PowerSeries.coeff n (b * PowerSeries.map (algebraMap R ℂ) t) ∈ L := by
  rw [PowerSeries.coeff_mul]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [PowerSeries.coeff_map, mul_comm, ← Algebra.smul_def]
  exact L.smul_mem _ (hb x.1)

/-- Division by a unit power series preserves any coefficient module. -/
theorem coeff_mem_of_mul_unit {R : Type*} [CommRing R] [Algebra R ℂ]
    {L : Submodule R ℂ} {a : PowerSeries ℂ} (t : PowerSeries R)
    (ht : IsUnit (PowerSeries.constantCoeff t))
    (h : ∀ n, PowerSeries.coeff n (a * PowerSeries.map (algebraMap R ℂ) t) ∈ L)
    (n : ℕ) : PowerSeries.coeff n a ∈ L := by
  obtain ⟨u, hu⟩ := ht
  let s := PowerSeries.invOfUnit t u
  have hts : t * s = 1 := PowerSeries.mul_invOfUnit t u hu.symm
  have ha : a = (a * PowerSeries.map (algebraMap R ℂ) t) *
      PowerSeries.map (algebraMap R ℂ) s := by
    rw [mul_assoc, ← map_mul, hts, map_one, mul_one]
  rw [ha]
  exact coeff_mul_map_mem s h n

/-- A positive q-order of the denominator causes no difficulty: remove the q-power first. -/
theorem coeff_mem_of_mul_shift_unit {R : Type*} [CommRing R] [Algebra R ℂ]
    {L : Submodule R ℂ} {a : PowerSeries ℂ} (v : ℕ) (t : PowerSeries R)
    (ht : IsUnit (PowerSeries.constantCoeff t))
    (h : ∀ n, PowerSeries.coeff n
      ((PowerSeries.X ^ v * PowerSeries.map (algebraMap R ℂ) t) * a) ∈ L)
    (n : ℕ) : PowerSeries.coeff n a ∈ L := by
  apply coeff_mem_of_mul_unit t ht _ n
  intro j
  have hj := h (j + v)
  rw [mul_assoc, mul_comm (PowerSeries.map _ t) a,
    PowerSeries.coeff_X_pow_mul] at hj
  exact hj

/-- Finite extensions of the localized integers also give finite integer lattices. -/
theorem fg_extension_exists_lattice {M : ℕ} (hM : M ≠ 0)
    (A : Subalgebra (zInv M) ℂ) (hA : A.toSubmodule.FG)
    {L : Submodule A ℂ} (hL : L.FG) :
    ∃ K : Submodule ℤ ℂ, K.FG ∧ ∀ z ∈ L, z ∈ awaySat M K := by
  letI : Module.Finite (zInv M) A := Module.Finite.of_fg hA
  exact fg_zInv_exists_lattice hM (hL.restrictScalars (R := zInv M))

/-- Squared-determinant Cramer identity, valid even for singular matrices. -/
theorem cramer_det_sq {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (H : Matrix ι ι R) (b : ι → R) (j : ι) :
    H.det ^ 2 * b j = ∑ i, H j i * (H.det * Matrix.cramer H b i) := by
  have h := congrFun (Matrix.mulVec_cramer H b) j
  change (∑ i, H j i * Matrix.cramer H b i) = H.det * b j at h
  calc
    H.det ^ 2 * b j = H.det * (H.det * b j) := by ring
    _ = H.det * ∑ i, H j i * Matrix.cramer H b i := by rw [h]
    _ = _ := by rw [Finset.mul_sum]; congr 1; ext i; ring

end VOA.Classification.COne.SSHecke
