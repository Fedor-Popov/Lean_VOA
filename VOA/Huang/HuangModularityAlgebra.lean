/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.VerlindeEigen

/-!
# The balancing identity for Zhu's `ρ(S)` (finite linear algebra)

For a matrix `S`, a diagonal `t` and fusion multiplicities `N` such that

* the columns of `S` are common eigenvectors of the fusion matrices (`FusionEigen N S`, Huang's
  Theorem 5.2, proved in the library as `GenusOneG1f.fusionEigenInput_holds`), with the unit row
  `N_{a v0}^y = δ_ay`;
* the vacuum row and column agree, `S_{z v0} = S_{v0 z}`;
* `S` is symmetric;
* `ρ(T) ρ(S) ρ(T) ρ(S) ρ(T) = ρ(S)` (the `SL₂(ℤ)` relation `TSTST = S`, `modular_TSTST`),

we prove (`balancing_of_eigen`)

  `Σ_c N_{ab}^c t_c⁻¹ S_{c v0} = t_{v0} t_a⁻¹ t_b⁻¹ S_ab`,

the identity that matches the categorical balancing formula
`S̃_ab T_a T_b = Σ_c N_ab^c T_c dim X_c` (`HuangModularityTrace.sTilde_mul_T`) after complex
conjugation. The relation `TSTST = S` is checked in `SL₂(ℤ)` (`modular_TSTST`) and transported
along Zhu's representation (`rep_TSTST_apply`). No `sorry`, no axioms beyond Lean's.
-/

noncomputable section

namespace VOA.Huang.HuangModularity

open VOA VOA.Huang.VerlindeEigen Matrix

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ι → ι → ℕ} {S : ι → ι → ℂ}
  {t : ι → ℂ} {v0 : ι}

/-- The half of the balancing identity that needs no symmetry of `S`:
`Σ_c N_ab^c t_c⁻¹ S_{c v0} = t_{v0} Σ_z S_az t_z S_bz`. -/
theorem balancing_sum_of_eigen (hunit : ∀ a y, N a v0 y = if y = a then 1 else 0)
    (hE : FusionEigen N S) (hvac : ∀ z, S z v0 = S v0 z)
    (hrel : ∀ a b, t a * (∑ c, S a c * t c * S c b) * t b = S a b) (ht : ∀ a, t a ≠ 0)
    (a b : ι) :
    ∑ c, (N a b c : ℂ) * ((t c)⁻¹ * S c v0) = t v0 * ∑ z, S a z * t z * S b z := by
  have h1 : ∀ c, (t c)⁻¹ * S c v0 = t v0 * ∑ z, S c z * t z * S z v0 := by
    intro c
    rw [← hrel c v0]
    field_simp [ht c]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h2 : ∑ c, (N a b c : ℂ) * (t v0 * (S c z * t z * S z v0)) =
      t v0 * t z * S z v0 * ∑ c, (N a b c : ℂ) * S c z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [h2, eigval_spec hE a z b, hvac z]
  have h3 := eq_eigval_mul hunit hE a z
  rw [h3]
  ring

/-- **The balancing identity for a symmetric `S`.** -/
theorem balancing_of_eigen (hunit : ∀ a y, N a v0 y = if y = a then 1 else 0)
    (hE : FusionEigen N S) (hvac : ∀ z, S z v0 = S v0 z) (hsym : ∀ a b, S a b = S b a)
    (hrel : ∀ a b, t a * (∑ c, S a c * t c * S c b) * t b = S a b) (ht : ∀ a, t a ≠ 0)
    (a b : ι) :
    ∑ c, (N a b c : ℂ) * ((t c)⁻¹ * S c v0) = t v0 * (t a)⁻¹ * (t b)⁻¹ * S a b := by
  rw [balancing_sum_of_eigen hunit hE hvac hrel ht a b]
  have h := hrel a b
  simp_rw [hsym b] at h ⊢
  rw [← h]
  field_simp [ht a, ht b]

end Algebra

/-! ## The relation `TSTST = S` in `SL₂(ℤ)` and along Zhu's representation -/

/-- `T S T S T = S` in `SL₂(ℤ)`. -/
theorem modular_TSTST :
    ModularGroup.T * ModularGroup.S * ModularGroup.T * ModularGroup.S * ModularGroup.T =
      ModularGroup.S := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

section Rep

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem of_modularRepT_eq_diagonal (h : ι → ℂ) :
    Matrix.of (modularRepT W h) = Matrix.diagonal fun i => modularTEntry W (h i) := by
  ext i j
  simp only [Matrix.of_apply, modularRepT, Matrix.diagonal_apply]

/-- **`ρ(T) ρ(S) ρ(T) ρ(S) ρ(T) = ρ(S)`, entrywise**, for any Zhu modular data. -/
theorem rep_TSTST_apply (D : VOA.ModularData W ι) (a b : ι) :
    modularTEntry W (D.h a) * (∑ c, D.repS a c * modularTEntry W (D.h c) * D.repS c b) *
      modularTEntry W (D.h b) = D.repS a b := by
  have h := congrArg (fun M => M a b) (congrArg D.rep modular_TSTST)
  simp only [map_mul, D.rep_S, D.rep_T, of_modularRepT_eq_diagonal] at h
  rw [Matrix.of_apply] at h
  rw [← h]
  set d := Matrix.diagonal fun i => modularTEntry W (D.h i) with hd
  have hM : d * of D.repS * d * of D.repS * d = d * (of D.repS * d * of D.repS) * d := by
    simp only [Matrix.mul_assoc]
  rw [hM, hd, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.of_apply]

theorem modularTEntry_ne_zero (x : ℂ) : modularTEntry W x ≠ 0 := Complex.exp_ne_zero _

end Rep

end VOA.Huang.HuangModularity
