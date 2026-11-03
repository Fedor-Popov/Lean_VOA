/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkIntegral

/-!
# Serre–Stark S6: bounded coefficients from the integral-weight `q`-expansion principle

The last Serre–Stark residual `SSHecke.SerreStarkBoundedCoeff24` (coefficients of every
`g ∈ M_{1/2}(N, χ)`, `24 ∣ N`, lie in a finitely generated `ℤ`-submodule of `ℂ`) is reduced here
to the standard **`q`-expansion principle with bounded denominators** for Mathlib's integral-weight
modular forms on `Γ₁(N)`:

* `QExpPrinciple24 k`: for `24 ∣ N`, the `q`-expansion coefficients of every
  `F ∈ M_k(Γ₁(N))` (a Mathlib `ModularForm`) lie in a finitely generated `ℤ`-submodule of `ℂ`.

Main results:

* `mem_of_mul_map_int`: if `t ∈ ℤ⟦q⟧` has constant term `1` and the coefficients of `a · t` lie in
  a `ℤ`-submodule `L`, so do those of `a` (`t` is a unit of `ℤ⟦q⟧`);
* `thetaRef_coeff`: `θ = Σ q^{n²}` has integer `q`-expansion with constant term `1`;
* `qExpansion_weightOneForm`: the `q`-expansion of `g θ ∈ M_1(Γ₁(N))` is the product of those of
  `g` and `θ`;
* `boundedCoeff24_of_qExpPrinciple24`: for every `k ≥ 1`,
  `QExpPrinciple24 k → SerreStarkBoundedCoeff24` (through `g θ^{2k-1} ∈ M_k(Γ₁(N))`).

`QExpPrinciple24 k` is TRUE for every `k ≥ 1`: `M_k(Γ₁(N))` has a basis of forms with integer
`q`-expansions (Shimura, *Introduction to the arithmetic theory of automorphic functions*,
Thm 3.52, for the cusp forms, together with the explicit Eisenstein basis; for all `k ≥ 1`
Diamond–Im, *Modular forms and modular curves*, §12.3, via Katz's `q`-expansion principle), and a
form is a finite `ℂ`-combination of basis forms. It is *not* implied by Serre–Stark's Theorem A
(it is a statement about all of `M_k(Γ₁(N))`), so no in-library certificate is offered; it is a
mainstream published theorem in Mathlib's own language.
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## Power series with an integral unit factor -/

/-- Coefficients of `b · t` lie in `L` when those of `b` do and `t` is integral. -/
theorem coeff_mul_map_int_mem {L : Submodule ℤ ℂ} {b : PowerSeries ℂ} (t : PowerSeries ℤ)
    (hb : ∀ n, PowerSeries.coeff n b ∈ L) (n : ℕ) :
    PowerSeries.coeff n (b * PowerSeries.map (Int.castRingHom ℂ) t) ∈ L := by
  rw [PowerSeries.coeff_mul]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [PowerSeries.coeff_map, eq_intCast, mul_comm, ← zsmul_eq_mul]
  exact L.smul_mem _ (hb x.1)

/-- **Division by an integral unit.** If `t ∈ ℤ⟦q⟧` has constant term `1` and every coefficient
of `a · t` lies in `L`, then every coefficient of `a` lies in `L`. -/
theorem mem_of_mul_map_int {L : Submodule ℤ ℂ} {a : PowerSeries ℂ} (t : PowerSeries ℤ)
    (ht : PowerSeries.constantCoeff t = 1)
    (h : ∀ n, PowerSeries.coeff n (a * PowerSeries.map (Int.castRingHom ℂ) t) ∈ L) (n : ℕ) :
    PowerSeries.coeff n a ∈ L := by
  set s := PowerSeries.invOfUnit t 1 with hs
  have hts : t * s = 1 := PowerSeries.mul_invOfUnit t 1 (by simp [ht])
  have ha : a = (a * PowerSeries.map (Int.castRingHom ℂ) t) * PowerSeries.map (Int.castRingHom ℂ) s
      := by
    rw [mul_assoc, ← map_mul, hts, map_one, mul_one]
  rw [ha]
  exact coeff_mul_map_int_mem s h n

/-! ## The `q`-expansion of `θ` -/

/-- The trivial character modulo `1`. -/
theorem triv_apply (x : ZMod 1) : (1 : DirichletCharacter ℂ 1) x = 1 := by
  rw [Subsingleton.elim x 1, map_one]

theorem thetaRef_eq_charTheta (τ : ℂ) : thetaRef τ = charTheta 1 1 1 τ := by
  simp only [thetaRef, rankOneTheta, rankOneThetaTerm, charTheta, thetaExp, triv_apply, one_mul]
  refine tsum_congr fun m => ?_
  simp

theorem isThetaTypeForm_thetaRef {N : ℕ} (h24 : 24 ∣ N) : IsThetaTypeForm N thetaRef := by
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have := isThetaTypeForm_rankOneTheta h24 0 (r := 1) (t := 1) one_pos one_pos (by simpa using h4)
  exact this.congr fun τ _ => (thetaRef_eq_rankOneTheta_nat τ).symm

theorem thetaTypeCoeff_thetaRef {N : ℕ} (h24 : 24 ∣ N) (k : ℕ) :
    thetaTypeCoeff thetaRef k = charThetaCoeff 1 1 1 k :=
  (isThetaTypeForm_thetaRef h24).coeff_eq_of_hasSum
    (fun τ hτ => by
      rw [thetaRef_eq_charTheta]
      have := hasSum_charTheta (1 : DirichletCharacter ℂ 1) (t := 1) le_rfl hτ
      rwa [Nat.cast_one] at this) k

theorem charThetaCoeff_triv_int (k : ℕ) : ∃ z : ℤ, charThetaCoeff 1 1 1 k = z := by
  have hmem := charThetaCoeff_mem (1 : DirichletCharacter ℂ 1) le_rfl k
  have hrange : Set.range (1 : DirichletCharacter ℂ 1) = {1} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ triv_apply y, fun hx => ⟨0, hx ▸ triv_apply 0⟩⟩
  rw [hrange, Submodule.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, by rw [← hz, zsmul_eq_mul, mul_one]⟩

theorem charThetaCoeff_triv_zero : charThetaCoeff 1 1 1 0 = 1 := by
  have hset : sqIdx 1 ⁻¹' {0} = ↑({0} : Finset ℤ) := by
    ext b
    simp [sqIdx]
  rw [charThetaCoeff, tsum_congr_set_coe (fun b : ℤ => (1 : DirichletCharacter ℂ 1) (b : ZMod 1))
    hset, Finset.tsum_subtype' ({0} : Finset ℤ) (fun b : ℤ => (1 : DirichletCharacter ℂ 1)
    (b : ZMod 1)), Finset.sum_singleton, triv_apply]

/-- The integer power series `Σ_{n ∈ ℤ} q^{n²}`. -/
def thetaInt : PowerSeries ℤ :=
  PowerSeries.mk fun k => (charThetaCoeff_triv_int k).choose

theorem map_thetaInt_coeff (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.map (Int.castRingHom ℂ) thetaInt) =
      charThetaCoeff 1 1 1 k := by
  rw [PowerSeries.coeff_map, thetaInt, PowerSeries.coeff_mk, eq_intCast]
  exact (charThetaCoeff_triv_int k).choose_spec.symm

theorem constantCoeff_thetaInt : PowerSeries.constantCoeff thetaInt = 1 := by
  have h := map_thetaInt_coeff 0
  rw [charThetaCoeff_triv_zero, PowerSeries.coeff_map, eq_intCast] at h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact_mod_cast h

/-- **`θ` has integral `q`-expansion with constant term `1`.** -/
theorem qExpansion_thetaRef {N : ℕ} (h24 : 24 ∣ N) :
    UpperHalfPlane.qExpansion 1 (fun τ : ℍ => thetaRef τ) =
      PowerSeries.map (Int.castRingHom ℂ) thetaInt := by
  ext k
  rw [map_thetaInt_coeff, ← thetaTypeCoeff_thetaRef h24 k]
  rfl

/-! ## `q`-expansions of `g θ^{2k-1}` -/

theorem qExpansion_weightOneForm {N : ℕ} (h4 : 4 ∣ N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    (hθ : IsThetaTypeForm N thetaRef) :
    UpperHalfPlane.qExpansion 1 (IsThetaTypeForm.weightOneForm h4 hf) =
      UpperHalfPlane.qExpansion 1 (fun τ : ℍ => f τ) *
        UpperHalfPlane.qExpansion 1 (fun τ : ℍ => thetaRef τ) := by
  have e : ((IsThetaTypeForm.weightOneForm h4 hf : ℍ → ℂ)) =
      (fun τ : ℍ => f τ) * (fun τ : ℍ => thetaRef τ) := rfl
  rw [e]
  exact UpperHalfPlane.qExpansion_mul hf.analyticAt hθ.analyticAt

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

/-! ## The integral-weight `q`-expansion principle and the reduction -/

/-- **`q`-expansion principle with bounded denominators, weight `k`, `Γ₁(N)`, `24 ∣ N`.**

TRUE for `k ≥ 1`: `M_k(Γ₁(N))` has a basis of forms with integer `q`-expansions (Shimura,
*Introduction to the arithmetic theory of automorphic functions*, Thm 3.52, plus the explicit
Eisenstein basis; Diamond–Im, *Modular forms and modular curves*, §12.3, all `k ≥ 1`). -/
def QExpPrinciple24 (k : ℤ) : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (_h24 : 24 ∣ N)
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k),
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 F) ∈ L

/-- **The weight-`k` multiple.** `g θ^{2k−1} = (g θ)(θ²)^{k−1} ∈ M_k(Γ₁(N))`, `k ≥ 1`. -/
def thetaMultiple {N : ℕ} (h4 : 4 ∣ N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    (hθ : IsThetaTypeForm N thetaRef) (j : ℕ) :
    ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (1 + j) :=
  ModularForm.mcast (by ring)
    ((IsThetaTypeForm.weightOneForm h4 hf).mul ((IsThetaTypeForm.weightOneForm h4 hθ).pow j))

theorem qExpansion_thetaMultiple {N : ℕ} (h24 : 24 ∣ N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    (j : ℕ) :
    UpperHalfPlane.qExpansion 1
        (thetaMultiple ((show 4 ∣ 24 by norm_num).trans h24) hf (isThetaTypeForm_thetaRef h24) j) =
      UpperHalfPlane.qExpansion 1 (fun τ : ℍ => f τ) *
        PowerSeries.map (Int.castRingHom ℂ) (thetaInt ^ (2 * j + 1)) := by
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have hθ := isThetaTypeForm_thetaRef h24
  have hP := one_mem_strictPeriods_Gamma1 N
  change UpperHalfPlane.qExpansion 1 ((IsThetaTypeForm.weightOneForm h4 hf).mul
    ((IsThetaTypeForm.weightOneForm h4 hθ).pow j)) = _
  rw [ModularForm.qExpansion_mul one_pos hP, ModularForm.qExpansion_pow one_pos hP,
    qExpansion_weightOneForm h4 hf hθ, qExpansion_weightOneForm h4 hθ hθ, qExpansion_thetaRef h24,
    map_pow]
  ring

/-- **Reduction.** For every `k ≥ 1`, the integral-weight `q`-expansion principle in weight `k`
gives `SerreStarkBoundedCoeff24` (through `g θ^{2k−1} ∈ M_k(Γ₁(N))` and division by the integral
unit `θ^{2k−1} ∈ 1 + q ℤ⟦q⟧`). -/
theorem boundedCoeff24_of_qExpPrinciple24 (j : ℕ) (hQ : QExpPrinciple24 (1 + j)) :
    SerreStarkBoundedCoeff24 := by
  intro N hN h24 χ g
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have hf := (extH_of_mem g.2).thetaType
  obtain ⟨L, hL, hcoeff⟩ := hQ N hN h24
    (thetaMultiple h4 hf (isThetaTypeForm_thetaRef h24) j)
  refine ⟨L, hL, fun n => ?_⟩
  rw [qExpansion_thetaMultiple h24 hf j] at hcoeff
  have ht : PowerSeries.constantCoeff (thetaInt ^ (2 * j + 1)) = 1 := by
    rw [map_pow, constantCoeff_thetaInt, one_pow]
  exact mem_of_mul_map_int _ ht hcoeff n

/-- Weight one (`g ↦ g θ`). -/
theorem boundedCoeff24_of_qExpPrinciple24_one (hQ : QExpPrinciple24 1) :
    SerreStarkBoundedCoeff24 :=
  boundedCoeff24_of_qExpPrinciple24 0 (by simpa using hQ)

/-- Weight two (`g ↦ g θ³`). -/
theorem boundedCoeff24_of_qExpPrinciple24_two (hQ : QExpPrinciple24 2) :
    SerreStarkBoundedCoeff24 :=
  boundedCoeff24_of_qExpPrinciple24 1 (by simpa using hQ)

end SSHecke

end VOA.Classification.COne
