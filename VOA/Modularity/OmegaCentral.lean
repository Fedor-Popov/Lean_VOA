/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.HL0Scoped
import VOA.Modularity.SimpleAModFinite
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import VOA.Modules.FiniteGeneration

/-!
# `[ω]` is central in `A(𝒱)`, and Schur gives the `AMod.OmegaScalar` datum

Residual **(b)** builds Dong–Jiang's `L(U)` from an abstract simple `A(𝒱)`-module `U`, and
`Modularity.HL0Scoped.genHL0` reduces its grading datum `hL0` to `AMod.OmegaScalar U h`.  This file
supplies that: the Zhu class `[ω]` is **central** in `A(𝒱)`, so on a simple `U` — finite-dimensional
whenever `dim A(𝒱) < ∞`, which `C₂`-cofiniteness gives — Schur's lemma forces `[ω]` to act by a
scalar.

The centrality is Zhu's Lemma 2.1.3 (`zhu_comm_mod_O`, banked) at `u = ω ∈ 𝒱₂`: the residue term is
`Res_z (1+z) Y(ω,z)v = L₋₁v + L₀v`, which lies in `O(𝒱)` (`zhuLgen_mem_O`).

## Main results

* `resFull_one_zero_omega` — `Res_z (1+z) Y(ω,z)v = L₋₁v + L₀v`;
* `omega_mul_comm` — `[ω]·[v] = [v]·[ω]` in `A(𝒱)`;
* `omega_central` — `[ω]` commutes with everything in `A(𝒱)`;
* `exists_omegaScalar_of_isSimpleAMod` — **Schur**: `[ω]` acts on a simple `U` by a scalar.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- `Res_z (1+z) Y(ω,z)v = ω₍₀₎v + ω₍₁₎v = L₋₁v + L₀v`. -/
theorem resFull_one_zero_omega (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    resFull W 1 0 W.conformalVector v = W.L (-1) v + W.L 0 v := by
  have resFull_zero_delta : ∀ Q : ℤ,
      resFull W 0 Q W.conformalVector v = W.smul W.conformalVector (-Q) v := by
    intro Q
    rw [resFull]
    have hsingle : ∀ l : ℤ, l ≠ -Q →
        cbz 0 (l + Q) • W.smul W.conformalVector l v = 0 := by
      intro l hl
      rw [cbz_zero_left, if_neg (show l + Q ≠ 0 by omega), zero_smul]
    rw [finsum_eq_single
      (fun l : ℤ => cbz (0 : ℤ) (l + Q) • W.smul W.conformalVector l v) (-Q) hsingle]
    show cbz 0 (-Q + Q) • W.smul W.conformalVector (-Q) v = W.smul W.conformalVector (-Q) v
    rw [show (-Q + Q : ℤ) = 0 by ring, cbz_zero, one_smul]
  have hL1 : W.smul W.conformalVector (0 : ℤ) v = W.L (-1) v := by
    rw [PreVertexAlgebra.smul_def, L_def, show ((-1 : ℤ) + 1) = (0 : ℤ) by ring]
  have hL0 : W.smul W.conformalVector (1 : ℤ) v = W.L 0 v := by
    rw [PreVertexAlgebra.smul_def, L_def, show ((0 : ℤ) + 1) = (1 : ℤ) by ring]
  rw [resFull_pascal W 1 0 W.conformalVector v, show (1 : ℤ) - 1 = 0 by ring,
    resFull_zero_delta 0, resFull_zero_delta (0 - 1), neg_zero,
    show (-(0 - 1) : ℤ) = 1 by ring, hL1, hL0]

/-- **`[ω]` commutes with every class in `A(𝒱)`, at the level of representatives.** -/
theorem zhuMul_omega_comm_homog (W : VertexOperatorAlgebra 𝒱) {M : ℕ} {v : 𝒱}
    (hv : v ∈ W.grading (M : ℤ)) :
    zhuMul W W.conformalVector v - zhuMul W v W.conformalVector ∈ O W := by
  have h := zhu_comm_mod_O W (K := 2) (M := M) W.conformalVector_mem_grading_two hv
  rw [show (((2 : ℕ) : ℤ) - 1) = (1 : ℤ) by norm_num, resFull_one_zero_omega] at h
  have hsum := Submodule.add_mem _ h (zhuLgen_mem_O W v)
  have hrw : zhuMul W W.conformalVector v - zhuMul W v W.conformalVector
      - (W.L (-1) v + W.L 0 v) + (W.L (-1) v + W.L 0 v)
      = zhuMul W W.conformalVector v - zhuMul W v W.conformalVector := by abel
  rwa [hrw] at hsum

section Central

variable (W : VertexOperatorAlgebra 𝒱)

/-- **`[ω]·[v] = [v]·[ω]` for every `v`.** -/
theorem omega_mul_comm (v : 𝒱) :
    letI := instRingA W
    (mk W W.conformalVector : A W) * mk W v = mk W v * mk W W.conformalVector := by
  letI := instRingA W
  letI := instAlgebraA W
  set f : 𝒱 →ₗ[ℂ] A W :=
    (LinearMap.mulLeft ℂ (mk W W.conformalVector : A W)
      - LinearMap.mulRight ℂ (mk W W.conformalVector : A W)).comp (O W).mkQ with hf
  have hker : LinearMap.ker f = ⊤ := by
    rw [eq_top_iff, ← span_homog_eq_top W, Submodule.span_le]
    rintro x ⟨m, hx⟩
    rcases lt_or_ge m 0 with hm | hm
    · rw [W.positivity m hm, Submodule.mem_bot] at hx
      subst hx
      exact LinearMap.mem_ker.mpr (map_zero f)
    · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, by omega⟩
      refine LinearMap.mem_ker.mpr ?_
      have hz := zhuMul_omega_comm_homog W hx
      show (mk W W.conformalVector : A W) * mk W x - mk W x * mk W W.conformalVector = 0
      have h1 : (mk W W.conformalVector : A W) * mk W x
          = mk W (zhuMul W W.conformalVector x) := by
        show Amul (zhuRingData_holds W) (mk W W.conformalVector) (mk W x) = _
        rw [Amul_mk]
      have h2 : (mk W x : A W) * mk W W.conformalVector
          = mk W (zhuMul W x W.conformalVector) := by
        show Amul (zhuRingData_holds W) (mk W x) (mk W W.conformalVector) = _
        rw [Amul_mk]
      rw [h1, h2, sub_eq_zero, mk_eq_iff]
      exact hz
  have := LinearMap.mem_ker.mp (hker ▸ Submodule.mem_top : v ∈ LinearMap.ker f)
  have h2 : (mk W W.conformalVector : A W) * mk W v - mk W v * mk W W.conformalVector = 0 := this
  linear_combination (norm := module) h2

/-- **`[ω]` is central in `A(𝒱)`.** -/
theorem omega_central (a : letI := instRingA W; A W) :
    letI := instRingA W
    (mk W W.conformalVector : A W) * a = a * mk W W.conformalVector := by
  letI := instRingA W
  refine Submodule.Quotient.induction_on (O W) a (fun v => ?_)
  exact omega_mul_comm W v

end Central

/-- `[ω]` commutes with every representative, at the level of `𝒱`. -/
theorem zhuMul_omega_comm (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    zhuMul W W.conformalVector v - zhuMul W v W.conformalVector ∈ O W := by
  letI := instRingA W
  have h := omega_mul_comm W v
  have h1 : (mk W W.conformalVector : A W) * mk W v
      = mk W (zhuMul W W.conformalVector v) := by
    show Amul (zhuRingData_holds W) (mk W W.conformalVector) (mk W v) = _
    rw [Amul_mk]
  have h2 : (mk W v : A W) * mk W W.conformalVector
      = mk W (zhuMul W v W.conformalVector) := by
    show Amul (zhuRingData_holds W) (mk W v) (mk W W.conformalVector) = _
    rw [Amul_mk]
  rw [h1, h2, mk_eq_iff] at h
  exact h

/-! ## Schur -/

/-- **Schur's lemma for `[ω]`.**  On a simple `A(𝒱)`-module — finite-dimensional whenever
`dim A(𝒱) < ∞` — the central class `[ω]` acts by a single scalar.  This is the
`AMod.OmegaScalar` datum that `Modularity.HL0Scoped.genHL0` consumes. -/
theorem exists_omegaScalar_of_isSimpleAMod {W : VertexOperatorAlgebra 𝒱}
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    (U : AMod W) (hU : IsSimpleAMod U) : ∃ h : ℂ, U.OmegaScalar h := by
  classical
  letI := instRingA W
  haveI := hfd
  haveI : FiniteDimensional ℂ U.carrier := finiteDimensional_of_isSimpleAMod hfd U hU
  haveI : Nontrivial U.carrier := hU.1
  set φ : Module.End ℂ U.carrier := U.ρ (mk W W.conformalVector) with hφ
  obtain ⟨h, hh⟩ := Module.End.exists_eigenvalue φ
  obtain ⟨x₀, hx₀mem, hx₀ne⟩ := hh.exists_hasEigenvector
  refine ⟨h, ?_⟩
  -- `[ω]` commutes with the whole action
  have hcomm : ∀ (a : A W) (y : U.carrier), φ (U.ρ a y) = U.ρ a (φ y) := by
    intro a y
    refine Submodule.Quotient.induction_on (O W) a (fun b => ?_)
    have h3 : (mk W (zhuMul W W.conformalVector b) : A W)
        = mk W (zhuMul W b W.conformalVector) :=
      (mk_eq_iff W).mpr (zhuMul_omega_comm W b)
    have heq : U.ρ (mk W W.conformalVector) * U.ρ (mk W b)
        = U.ρ (mk W b) * U.ρ (mk W W.conformalVector) := by
      rw [← U.ρ_mul, ← U.ρ_mul, h3]
    have hap := congrArg (fun t : Module.End ℂ U.carrier => t y) heq
    simpa [hφ, Module.End.mul_apply] using hap
  -- membership in the eigenspace, stated pointwise
  have hmemK : ∀ y : U.carrier,
      y ∈ LinearMap.ker (φ - h • (1 : Module.End ℂ U.carrier)) ↔ φ y = h • y := by
    intro y
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero]
  set K : AModSubmodule U :=
    { carrier := LinearMap.ker (φ - h • (1 : Module.End ℂ U.carrier))
      ρ_mem := by
        intro a y hy
        rw [hmemK] at hy ⊢
        rw [hcomm a y, hy, map_smul] } with hK
  have hx₀K : x₀ ∈ K.carrier := (hmemK x₀).mpr (Module.End.HasEigenvector.apply_eq_smul
    ⟨hx₀mem, hx₀ne⟩)
  have hne : K.carrier ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at hx₀K
    exact hx₀ne hx₀K
  rcases hU.2 K with hb | ht
  · exact absurd hb hne
  · refine LinearMap.ext (fun y => ?_)
    have hyK : y ∈ K.carrier := by rw [ht]; trivial
    rw [hmemK] at hyK
    show U.ρ (mk W W.conformalVector) y = (h • (1 : Module.End ℂ U.carrier)) y
    rw [LinearMap.smul_apply, Module.End.one_apply]
    exact hyK

end VOA
