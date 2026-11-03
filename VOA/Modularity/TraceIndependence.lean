/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockSpanning

/-!
# `TraceIndependent` from the `T`-eigenvalues

`Modularity.BlockSpanning` proves Zhu's modularity for every `A ∈ SL₂(ℤ)` from two named data,
`TraceSpanning` and `TraceIndependent`.  This file discharges the **second** one under a sharp
and standard hypothesis: that the modules have **pairwise distinct `T`-eigenvalues**
`λ_i = e^{2πi(h_i − c/24)}`, i.e. pairwise distinct conformal weights *modulo `ℤ`*.

## The mechanism

`realisesLaw_T` (unconditional, already proved) says each trace function is a `T`-eigenvector:

  `S_i(v, τ+1) = λ_i · S_i(v, τ)`,   `λ_i = e^{2πi(h_i − c/24)}`.

So a vanishing combination `Σ_j c_j S_j(v, ·) = 0` stays vanishing after every translation, and
evaluating at `T^k · τ` gives the **moment equations**

  `Σ_j λ_j^k · (c_j S_j(v,τ)) = 0`  for every `k : ℕ`.

Because these hold for *all* `k`, no Vandermonde determinant is needed: applying them to the
coefficients of the Lagrange polynomial `P_i = Π_{k ≠ i} (X − λ_k)` — which vanishes at every
`λ_j`, `j ≠ i`, and not at `λ_i` — isolates a single term.  Hence
`c_i · S_i(v,τ) = 0` for each `i` (`tEigen_lagrange_isolate`, `coeff_mul_traceFun_eq_zero`), and
`c_i = 0` as soon as `S_i` is not identically zero (`TraceNonvanishing`).

## Contents

* `tEigen` — the `T`-eigenvalue `λ_i`, and `traceFun_T_smul` / `traceFun_T_pow_smul`.
* `tEigen_lagrange_isolate` — the moment-to-Lagrange step, in the abstract.
* `coeff_mul_traceFun_eq_zero` — `c_i · S_i(v,τ) = 0` for each `i`.
* **`traceIndependent_of_tEigen_injective`** — `TraceIndependent Mfam h`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  The two hypotheses are named and sharp:
`Function.Injective (tEigen W h)` (distinct conformal weights mod `ℤ`) and `TraceNonvanishing`
(each module has a trace function that is somewhere nonzero — for `v = 𝟙` this is the character,
positive at `τ = it`, `t ≫ 0`, once summability is in hand).
-/

namespace VOA

open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}

/-! ## The `T`-eigenvalues -/

/-- The **`T`-eigenvalue** `λ_i = e^{2πi(h_i − c/24)}` of the `i`-th trace function. -/
noncomputable def tEigen (W : VertexOperatorAlgebra 𝒱) (h : ι → ℂ) (i : ι) : ℂ :=
  modularTEntry W (h i)

variable (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- Each trace function is a `T`-eigenvector (`realisesLaw_T`, specialised by diagonality). -/
theorem traceFun_T_smul (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) {n : ℕ} {v : 𝒱}
    (hv : v ∈ sqWeightSpace W (n : ℂ)) (i : ι) (τ : UpperHalfPlane) :
    traceFun Mfam h i v (ModularGroup.T • τ) = tEigen W h i * traceFun Mfam h i v τ := by
  have hlaw := realisesLaw_T Mfam h hcw n v hv i τ
  rw [autFactor_T, one_pow, one_mul,
    Finset.sum_eq_single i (fun j _ hj => by rw [modularRepT_off_diag W h (Ne.symm hj), zero_mul])
      (fun hi => absurd (Finset.mem_univ i) hi), modularRepT_diag] at hlaw
  exact hlaw

/-- Iterating: `S_i(v, T^k·τ) = λ_i^k · S_i(v, τ)`. -/
theorem traceFun_T_pow_smul (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) {n : ℕ} {v : 𝒱}
    (hv : v ∈ sqWeightSpace W (n : ℂ)) (i : ι) (τ : UpperHalfPlane) (k : ℕ) :
    traceFun Mfam h i v ((ModularGroup.T ^ k) • τ) = tEigen W h i ^ k * traceFun Mfam h i v τ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_smul, traceFun_T_smul Mfam h hcw hv i _, ih]
      ring

/-! ## Isolating one term from the moment equations -/

/-- **Lagrange isolation.**  If a finite family of scalars `x` satisfies all the moment
equations `Σ_j λ_j^k x_j = 0`, then `(Π_{k ≠ i} (λ_i − λ_k)) · x_i = 0`.

The Lagrange polynomial `P_i = Π_{k ≠ i} (X − λ_k)` vanishes at every `λ_j` with `j ≠ i`, so
expanding `P_i` in powers of `X` and feeding the moment equations kills everything but `i`. -/
theorem tEigen_lagrange_isolate (lam : ι → ℂ) (x : ι → ℂ)
    (hmom : ∀ k : ℕ, ∑ j, lam j ^ k * x j = 0) (i : ι) :
    (∏ k ∈ Finset.univ.erase i, (lam i - lam k)) * x i = 0 := by
  classical
  set P : Polynomial ℂ := ∏ k ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (lam k))
    with hP
  -- `Σ_j P(λ_j) x_j = 0`, by expanding `P` in powers and using the moment equations
  have hsum : ∑ j, P.eval (lam j) * x j = 0 := by
    have hexp : ∀ j : ι, P.eval (lam j)
        = ∑ m ∈ Finset.range (P.natDegree + 1), P.coeff m * lam j ^ m := by
      intro j
      rw [Polynomial.eval_eq_sum_range]
    simp_rw [hexp, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    have : ∑ j, P.coeff m * lam j ^ m * x j = P.coeff m * ∑ j, lam j ^ m * x j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, hmom m, mul_zero]
  -- only `j = i` survives
  have hzero : ∀ j : ι, j ≠ i → P.eval (lam j) = 0 := by
    intro j hj
    rw [hP, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) ?_
    simp
  have hval : P.eval (lam i) = ∏ k ∈ Finset.univ.erase i, (lam i - lam k) := by
    rw [hP, Polynomial.eval_prod]
    exact Finset.prod_congr rfl (fun k _ => by simp)
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [hzero j hj, zero_mul])
    (fun hi => absurd (Finset.mem_univ i) hi), hval] at hsum
  exact hsum

/-- **Each term of a vanishing combination vanishes.**  If the `T`-eigenvalues are pairwise
distinct, a vanishing combination of trace functions vanishes termwise. -/
theorem coeff_mul_traceFun_eq_zero (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hinj : Function.Injective (tEigen W h)) (c : ι → ℂ)
    (hc : ∀ (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ τ : UpperHalfPlane,
      ∑ j, c j * traceFun Mfam h j v τ = 0)
    {n : ℕ} {v : 𝒱} (hv : v ∈ sqWeightSpace W (n : ℂ)) (τ : UpperHalfPlane) (i : ι) :
    c i * traceFun Mfam h i v τ = 0 := by
  classical
  have hmom : ∀ k : ℕ, ∑ j, tEigen W h j ^ k * (c j * traceFun Mfam h j v τ) = 0 := by
    intro k
    have := hc n v hv ((ModularGroup.T ^ k) • τ)
    rw [← this]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [traceFun_T_pow_smul Mfam h hcw hv j τ k]
    ring
  have hiso := tEigen_lagrange_isolate (tEigen W h) (fun j => c j * traceFun Mfam h j v τ) hmom i
  have hprod : (∏ k ∈ Finset.univ.erase i, (tEigen W h i - tEigen W h k)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    exact sub_ne_zero_of_ne (fun hcon => hki (hinj hcon.symm))
  exact (mul_eq_zero.mp hiso).resolve_left hprod

/-! ## `TraceIndependent` -/

/-- **Trace nonvanishing**: each module has *some* homogeneous `v` and *some* `τ` at which its
trace function is nonzero.  For `v = 𝟙` this is the character `χ_{M_i}`, which has nonnegative
coefficients with a positive leading one, hence is positive at `τ = it` for `t ≫ 0` once
summability is available (`subexponentialCoeffs_of_ordered`). -/
def TraceNonvanishing (Mfam : ι → IrrModule W) (h : ι → ℂ) : Prop :=
  ∀ i : ι, ∃ (n : ℕ) (v : 𝒱) (_ : v ∈ sqWeightSpace W (n : ℂ)) (τ : UpperHalfPlane),
    traceFun Mfam h i v τ ≠ 0

/-- **`TraceIndependent` from distinct `T`-eigenvalues.**  If the conformal weights are
pairwise distinct modulo `ℤ` (equivalently, the `T`-eigenvalues `e^{2πi(h_i − c/24)}` are
pairwise distinct) and no trace function vanishes identically, then the trace functions are
linearly independent — the second of the two data feeding `zhu_modularity_of_spanning`. -/
theorem traceIndependent_of_tEigen_injective
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hinj : Function.Injective (tEigen W h)) (hnz : TraceNonvanishing Mfam h) :
    TraceIndependent Mfam h := by
  intro c hc
  funext i
  obtain ⟨n, v, hv, τ, hne⟩ := hnz i
  have := coeff_mul_traceFun_eq_zero Mfam h hcw hinj c hc hv τ i
  exact (mul_eq_zero.mp this).resolve_right hne

/-- **Zhu's modularity needs only `TraceSpanning`**, once the weights are distinct mod `ℤ`. -/
theorem zhu_modularity_of_traceSpanning (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hinj : Function.Injective (tEigen W h)) (hnz : TraceNonvanishing Mfam h)
    (hsp : TraceSpanning Mfam h) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h hsp (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnz) hcw) :=
  zhu_modularity_of_spanning Mfam h hsp
    (traceIndependent_of_tEigen_injective Mfam h hcw hinj hnz) hcw

/-! ## The general form: isolating a whole eigenvalue fibre

Dropping the injectivity of `λ` isolates the **fibre** `{j | λ_j = λ_i}` instead of a single
index — the Lagrange polynomial is taken over the *distinct* eigenvalues.  This is the sharpest
form of the argument: what survives is exactly the statement that, *within one `T`-eigenvalue
class*, the trace functions are independent, i.e. the top-level `A(𝒱)`-character separation. -/

/-- **Fibre isolation.**  From all the moment equations, the sum of `x` over each fibre of
`λ` vanishes.  No injectivity is needed. -/
theorem lagrange_fibre_isolate (lam : ι → ℂ) (x : ι → ℂ)
    (hmom : ∀ k : ℕ, ∑ j, lam j ^ k * x j = 0) (i : ι) :
    ∑ j ∈ Finset.univ.filter (fun j => lam j = lam i), x j = 0 := by
  classical
  set D : Finset ℂ := (Finset.univ.image lam).erase (lam i) with hD
  set P : Polynomial ℂ := ∏ μ ∈ D, (Polynomial.X - Polynomial.C μ) with hP
  have hsum : ∑ j, P.eval (lam j) * x j = 0 := by
    have hexp : ∀ j : ι, P.eval (lam j)
        = ∑ m ∈ Finset.range (P.natDegree + 1), P.coeff m * lam j ^ m := by
      intro j
      rw [Polynomial.eval_eq_sum_range]
    simp_rw [hexp, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    have hstep : ∑ j, P.coeff m * lam j ^ m * x j = P.coeff m * ∑ j, lam j ^ m * x j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hstep, hmom m, mul_zero]
  have hval : ∀ j : ι, P.eval (lam j) = if lam j = lam i then ∏ μ ∈ D, (lam i - μ) else 0 := by
    intro j
    rw [hP, Polynomial.eval_prod]
    by_cases hj : lam j = lam i
    · rw [if_pos hj, hj]
      exact Finset.prod_congr rfl (fun μ _ => by simp)
    · rw [if_neg hj]
      refine Finset.prod_eq_zero (i := lam j) ?_ (by simp)
      rw [hD]
      exact Finset.mem_erase.mpr ⟨hj, Finset.mem_image_of_mem lam (Finset.mem_univ j)⟩
  have hne : (∏ μ ∈ D, (lam i - μ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun μ hμ => ?_)
    have hμD : μ ∈ D := hμ
    rw [hD, Finset.mem_erase] at hμD
    exact sub_ne_zero_of_ne (fun hcon => hμD.1 hcon.symm)
  simp_rw [hval] at hsum
  have hcollect : ∑ j, (if lam j = lam i then (∏ μ ∈ D, (lam i - μ)) else 0) * x j
      = (∏ μ ∈ D, (lam i - μ)) * ∑ j ∈ Finset.univ.filter (fun j => lam j = lam i), x j := by
    rw [Finset.mul_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring)
  rw [hcollect] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left hne

/-- **Each `T`-eigenvalue fibre of a vanishing combination vanishes**, with no distinctness
hypothesis at all. -/
theorem traceFun_fibre_sum_eq_zero (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (c : ι → ℂ)
    (hc : ∀ (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ τ : UpperHalfPlane,
      ∑ j, c j * traceFun Mfam h j v τ = 0)
    {n : ℕ} {v : 𝒱} (hv : v ∈ sqWeightSpace W (n : ℂ)) (τ : UpperHalfPlane) (i : ι) :
    ∑ j ∈ Finset.univ.filter (fun j => tEigen W h j = tEigen W h i),
      c j * traceFun Mfam h j v τ = 0 := by
  classical
  have hmom : ∀ k : ℕ, ∑ j, tEigen W h j ^ k * (c j * traceFun Mfam h j v τ) = 0 := by
    intro k
    have := hc n v hv ((ModularGroup.T ^ k) • τ)
    rw [← this]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [traceFun_T_pow_smul Mfam h hcw hv j τ k]
    ring
  exact lagrange_fibre_isolate (tEigen W h) (fun j => c j * traceFun Mfam h j v τ) hmom i

/-- **Fibre independence**: within each `T`-eigenvalue class, the trace functions are linearly
independent.  This is the top-level `A(𝒱)`-character separation of Zhu's Thm 5.3.3, and by
`traceIndependent_of_fibreIndependent` it is *all* that `TraceIndependent` needs. -/
def FibreIndependent (Mfam : ι → IrrModule W) (h : ι → ℂ) : Prop :=
  ∀ (i : ι) (c : ι → ℂ),
    (∀ (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ τ : UpperHalfPlane,
      ∑ j ∈ Finset.univ.filter (fun j => tEigen W h j = tEigen W h i),
        c j * traceFun Mfam h j v τ = 0) →
    ∀ j ∈ Finset.univ.filter (fun j => tEigen W h j = tEigen W h i), c j = 0

/-- **`TraceIndependent` from fibre independence** — no distinctness hypothesis.  Together
with `traceFun_fibre_sum_eq_zero`, this reduces Zhu's independence theorem exactly to its
`T`-eigenvalue-class-local content. -/
theorem traceIndependent_of_fibreIndependent (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hfib : FibreIndependent Mfam h) : TraceIndependent Mfam h := by
  classical
  intro c hc
  funext i
  refine hfib i c (fun n v hv τ => traceFun_fibre_sum_eq_zero Mfam h hcw c hc hv τ i) i ?_
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩

end VOA
