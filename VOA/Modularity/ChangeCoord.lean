/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuRecursion
import VOA.Core.Automorphism

/-!
# The change-of-coordinate operator `T_f`  (Gannon 5.3.15, 5.3.16)

GOAL C2.  A holomorphic change of coordinate `f` with `f(0) = 0`, `f′(0) = 1`, acts on a VOA by
`T_f = exp(A_f)` with `A_f = Σ_{k ≥ 1} a_k L_k`, where `f(z) = exp(Σ_{k≥1} a_k z^{k+1} ∂_z) z`.

## Why this is finite (no analysis, no general formal exponential)

Two independent finiteness facts, both already in the VOA axioms:

* **The inner sum is locally finite** — VA5 `regularity` kills `L_{k+1} x` for large `k`
  (`coordGen_support_finite`), so `A_f` is a genuine `finsum` (the `vSqZ`/`gradedExpL0` pattern).
* **`A_f` is locally nilpotent** — VA1 `grading_mode` makes `L_k` lower the `L₀`-grade by exactly `k`
  (`L_mem_grading`), so `A_f` strictly lowers the filtration `𝒱^{≤d}` (`coordGen_mem_gradeLE`); and
  since the grading is **bounded below** (`positivity`: `𝒱ₙ = ⊥` for `n < 0`, so `𝒱^{≤d} = ⊥` for
  `d < 0`), iterating drives every vector to `0` (`coordGen_isLocNilp`).

So `T_f := expEquiv` of the repo's banked locally-nilpotent exponential (`Core/Automorphism.expLN`,
`expEquiv`) — **reused, not rebuilt** — is a genuine linear **equivalence** `𝒱 ≃ₗ[ℂ] 𝒱`.

The construction is done for an **arbitrary** coefficient family `a : ℕ → ℂ` (`a k` playing `a_{k+1}`),
which contains the cylinder→torus case `f = e^z − 1` as an instantiation; the specific coefficients for
that `f` are separate (purely scalar) data.

## Status
`changeCoord` is **built** and is an equivalence (`pbw`-free, axiom-clean): the generator, its local
finiteness, the grade-lowering, the local nilpotence, and the resulting `≃ₗ`.  The transformation law
(C3) is the named residual.

## References
* Gannon §5.3.4–5, eqs. (5.3.15)–(5.3.16); Zhu, J. AMS 9 (1996) §4.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `L_k` lowers the grade by `k` (VA1) -/

/-- **`L_m` lowers the `L₀`-grade by `m`**: `L_m : 𝒱_ℓ → 𝒱_{ℓ−m}`.  Immediate from VA1
`grading_mode` with `ω ∈ 𝒱₂` and `L m = mode (Y ω) (m+1)`: the target grade is
`2 + ℓ − (m+1) − 1 = ℓ − m`. -/
theorem L_mem_grading (W : VertexOperatorAlgebra 𝒱) {ℓ : ℤ} {v : 𝒱} (hv : v ∈ W.grading ℓ)
    (m : ℤ) : W.L m v ∈ W.grading (ℓ - m) := by
  have h := W.grading_mode W.conformalVector W.conformal_mem v hv (m + 1)
  rw [show (2 + ℓ - (m + 1) - 1) = ℓ - m from by ring] at h
  exact h

/-! ## The filtration by grades `≤ d` -/

/-- `𝒱^{≤d} = ⨆_{j ≤ d} 𝒱ⱼ` — the filtration the local-nilpotence argument runs on. -/
noncomputable def gradeLE (W : VertexOperatorAlgebra 𝒱) (d : ℤ) : Submodule ℂ 𝒱 :=
  ⨆ j : {j : ℤ // j ≤ d}, W.grading (j : ℤ)

theorem mem_gradeLE_of_mem_grading (W : VertexOperatorAlgebra 𝒱) {j d : ℤ} (hjd : j ≤ d)
    {x : 𝒱} (hx : x ∈ W.grading j) : x ∈ gradeLE W d :=
  Submodule.mem_iSup_of_mem (⟨j, hjd⟩ : {j : ℤ // j ≤ d}) hx

theorem gradeLE_mono (W : VertexOperatorAlgebra 𝒱) {d e : ℤ} (h : d ≤ e) :
    gradeLE W d ≤ gradeLE W e :=
  iSup_le fun j => le_iSup_of_le (⟨(j : ℤ), le_trans j.2 h⟩ : {j : ℤ // j ≤ e}) le_rfl

/-- **The filtration starts at `0`**: `𝒱^{≤d} = ⊥` for `d < 0` (VOA `positivity`). -/
theorem gradeLE_eq_bot (W : VertexOperatorAlgebra 𝒱) {d : ℤ} (hd : d < 0) : gradeLE W d = ⊥ := by
  refine le_antisymm (iSup_le fun j => ?_) bot_le
  rw [W.positivity (j : ℤ) (by have := j.2; omega)]

/-- **Every vector has a top grade**: `x ∈ 𝒱^{≤d}` for some `d` (from `W.isInternal`). -/
theorem exists_mem_gradeLE (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) : ∃ d : ℤ, x ∈ gradeLE W d := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  obtain ⟨M, hM⟩ := Finset.exists_le (DirectSum.decompose W.grading x).support
  refine ⟨M, ?_⟩
  have hx : x = ∑ j ∈ (DirectSum.decompose W.grading x).support,
      ((DirectSum.decompose W.grading x) j : 𝒱) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose W.grading x]
  rw [hx]
  exact Submodule.sum_mem _ (fun j hj =>
    mem_gradeLE_of_mem_grading W (hM j hj) ((DirectSum.decompose W.grading x) j).2)

/-! ## The generator `A_f = Σ_{k ≥ 1} a_k L_k` -/

/-- Local finiteness of the generator's defining sum — VA5 `regularity`. -/
theorem coordGen_support_finite (W : VertexOperatorAlgebra 𝒱) (a : ℕ → ℂ) (x : 𝒱) :
    (Function.support fun k : ℕ => a k • W.L ((k : ℤ) + 1) x).Finite := by
  obtain ⟨N, hN⟩ := W.regularity W.conformalVector x
  refine Set.Finite.subset (Set.finite_Iio N.toNat) ?_
  intro k hk
  simp only [Function.mem_support, ne_eq] at hk
  simp only [Set.mem_Iio]
  by_contra hc
  push_neg at hc
  exact hk (by rw [VertexOperatorAlgebra.L_def, hN ((k : ℤ) + 1 + 1) (by omega), smul_zero])

/-- **The change-of-coordinate generator** `A_f = Σ_{k ≥ 1} a_k L_k` (here `a k` plays `a_{k+1}`), a
locally finite `finsum`. -/
noncomputable def coordGen (W : VertexOperatorAlgebra 𝒱) (a : ℕ → ℂ) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun x := ∑ᶠ k : ℕ, a k • W.L ((k : ℤ) + 1) x
  map_add' x y := by
    simp only [map_add, smul_add]
    rw [finsum_add_distrib (coordGen_support_finite W a x) (coordGen_support_finite W a y)]
  map_smul' c x := by
    show (∑ᶠ k : ℕ, a k • W.L ((k : ℤ) + 1) (c • x)) = c • ∑ᶠ k : ℕ, a k • W.L ((k : ℤ) + 1) x
    rw [smul_finsum' c (coordGen_support_finite W a x)]
    exact finsum_congr (fun k => by rw [map_smul, smul_comm])

@[simp] theorem coordGen_apply (W : VertexOperatorAlgebra 𝒱) (a : ℕ → ℂ) (x : 𝒱) :
    coordGen W a x = ∑ᶠ k : ℕ, a k • W.L ((k : ℤ) + 1) x := rfl

/-- **The generator strictly lowers the filtration**: `A_f : 𝒱^{≤d} → 𝒱^{≤d−1}` (each `L_{k+1}`
drops the grade by `k+1 ≥ 1`). -/
theorem coordGen_mem_gradeLE (W : VertexOperatorAlgebra 𝒱) (a : ℕ → ℂ) {d : ℤ} {x : 𝒱}
    (hx : x ∈ gradeLE W d) : coordGen W a x ∈ gradeLE W (d - 1) := by
  induction hx using Submodule.iSup_induction' with
  | mem jj y hy =>
      have hfin := coordGen_support_finite W a y
      rw [coordGen_apply, finsum_eq_finsetSum_of_support_subset _
        (le_of_eq (Set.Finite.coe_toFinset hfin).symm)]
      refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
      exact mem_gradeLE_of_mem_grading W (by have := jj.2; omega)
        (L_mem_grading W hy ((k : ℤ) + 1))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- **The generator is locally nilpotent** — grade-lowering plus the bounded-below grading. -/
theorem coordGen_isLocNilp (W : VertexOperatorAlgebra 𝒱) (a : ℕ → ℂ) :
    IsLocNilp (coordGen W a) := by
  intro v
  obtain ⟨d, hd⟩ := exists_mem_gradeLE W v
  have key : ∀ n : ℕ, ((coordGen W a) ^ n) v ∈ gradeLE W (d - (n : ℤ)) := by
    intro n
    induction n with
    | zero => simpa using hd
    | succ m ih =>
        have hstep : ((coordGen W a) ^ (m + 1)) v = coordGen W a (((coordGen W a) ^ m) v) := by
          rw [pow_succ']; rfl
        rw [hstep]
        have h := coordGen_mem_gradeLE W a ih
        refine gradeLE_mono W ?_ h
        push_cast
        omega
  refine ⟨(d + 1).toNat, ?_⟩
  have hb := key (d + 1).toNat
  rw [gradeLE_eq_bot W (show d - (((d + 1).toNat : ℤ)) < 0 by omega)] at hb
  exact (Submodule.mem_bot ℂ).mp hb

/-- **The change-of-coordinate operator** `T_f = exp(A_f)` as a linear **equivalence**
(Gannon 5.3.15): built from the repo's banked locally-nilpotent exponential `expEquiv`. -/
noncomputable def changeCoord (W : VertexOperatorAlgebra 𝒱) (a : ℕ → ℂ) : 𝒱 ≃ₗ[ℂ] 𝒱 :=
  expEquiv (coordGen_isLocNilp W a)

@[simp] theorem changeCoord_apply (W : VertexOperatorAlgebra 𝒱) (a : ℕ → ℂ) (v : 𝒱) :
    changeCoord W a v = expFun (coordGen_isLocNilp W a) v := rfl

/-- `T_f` fixes any vector killed by the generator (e.g. the vacuum, when all `a_k L_k 𝟙 = 0`). -/
theorem changeCoord_of_apply_eq_zero (W : VertexOperatorAlgebra 𝒱) (a : ℕ → ℂ) {v : 𝒱}
    (hv : coordGen W a v = 0) : changeCoord W a v = v :=
  expFun_of_apply_eq_zero (coordGen_isLocNilp W a) hv

/-! ## Residual — (C3) the transformation law

What remains of GOAL C is the conjugation law `T_f Y(v,z) T_f⁻¹ = Y(v,z)·f′(z)^k` on primaries
(5.3.15d) and, on the stress tensor, the same with the Schwarzian term `(c/12)·{f;z}` (5.3.15e–f) —
which for the cylinder→torus coordinate is the constant `−c/24` by `schwarzian_expMinusOne`, i.e.
exactly the `ω̃ = ω − (c/24)𝟙` shift already built into `Lsq`.

The consequences that the Zhu-modularity route needs are proved independently of (C3): the
Virasoro relation (`Lsq_virasoro`, cocycle route) and the arbitrary-state commutator
`[L[0], a[j]] = (L[0]a)[j] - (j+1)a[j]` (`Lsq_zero_sqMode_comm`, `Modularity.SqModeWeight`).  So
(C3) is **not** a prerequisite of Zhu's theorem; it remains open only as the general
coordinate-change API recorded here.
-/

end VOA
