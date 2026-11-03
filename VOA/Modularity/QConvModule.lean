/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.QEvalConv
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# `qConv` is a `PowerSeries ℂ`-action — residual (c-i)

Without this, "the `R`-span of the block values" cannot even be *stated*: `qConv` is the only
multiplication available on `FormalQSeries`, and it was not known to be associative.

**The ring is `PowerSeries ℂ`, not a new construction.**  `PowerSeries ℂ` *is* `(ℕ → ℂ, ⋆)`, it is
already a `CommRing` in Mathlib, and `PowerSeries.coeff_mul` *is* the Cauchy product.  So the action
is `psSMul F χ := qConv (fun n => coeff n F) χ`, and associativity is a triangle re-index.

⚠ **The support hypothesis is essential and is carried by the type.**  For an arbitrary
`χ : ℂ → ℂ` the defining `∑ᶠ` need not have finite support and associativity is false.  ⚠ It is also
not enough to require vanishing at `h + i` for `i < 0` (the form of `qConv_apply_of_support`): that
constrains `χ` only on the coset `h + ℤ`, while `qConv f χ e` for `e ∉ h + ℤ` still sums infinitely
many unconstrained values.  The right object is `QSeriesAt h` — series supported **on** `h + ℕ` —
for which `qConv` is well behaved at *every* point of `ℂ`, and which is exactly what a formal
`q`-series based at `h` means.

## Main results

* `QSeriesAt` — the submodule of series supported on `h + ℕ`, and `qConv_mem_QSeriesAt`;
* `sum_triangle_swap` — the two ways of summing over `{(n,k) : n + k ≤ N}`;
* `psSMul_one`, `psSMul_mul` — unitality (unconditional) and **associativity**;
* `instModulePowerSeriesQSeriesAt` — `QSeriesAt h` is a `PowerSeries ℂ`-module, so
  `Submodule (PowerSeries ℂ) (QSeriesAt h)` — the `R`-span — is statable.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

/-- Summing `A n k` over the triangle `{(n,k) : n + k ≤ N}` by rows, versus by antidiagonals. -/
theorem sum_triangle_swap {β : Type*} [AddCommMonoid β] (A : ℕ → ℕ → β) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N - n + 1), A n k
      = ∑ P ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (P + 1), A a (P - a) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hinner : ∀ n ∈ Finset.range (N + 1),
          ∑ k ∈ Finset.range (N + 1 - n + 1), A n k
            = (∑ k ∈ Finset.range (N - n + 1), A n k) + A n (N + 1 - n) := by
        intro n hn
        have hle : n ≤ N := by have := Finset.mem_range.mp hn; omega
        have hstep : N + 1 - n + 1 = (N - n + 1) + 1 := by omega
        rw [hstep, Finset.sum_range_succ]
        congr 2
        omega
      have hlast : ∑ k ∈ Finset.range (N + 1 - (N + 1) + 1), A (N + 1) k = A (N + 1) 0 := by
        simp
      have hRlast : ∑ a ∈ Finset.range (N + 1 + 1), A a (N + 1 - a)
          = (∑ a ∈ Finset.range (N + 1), A a (N + 1 - a)) + A (N + 1) 0 := by
        rw [Finset.sum_range_succ]
        congr 2
        omega
      rw [Finset.sum_range_succ, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, hlast,
        Finset.sum_range_succ (f := fun P => ∑ a ∈ Finset.range (P + 1), A a (P - a)), hRlast, ih]
      abel

/-- **Formal `q`-series based at `h`**: those supported on `h + ℕ`. -/
def QSeriesAt (h : ℂ) : Submodule ℂ FormalQSeries where
  carrier := {χ : FormalQSeries | ∀ e : ℂ, (∀ n : ℕ, e ≠ h + (n : ℂ)) → χ e = 0}
  add_mem' := fun {a b} hχ hψ e he => by
    change a e + b e = 0
    rw [hχ e he, hψ e he, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c a hχ e he => by
    change c • a e = 0
    rw [hχ e he, smul_zero]

theorem mem_QSeriesAt_iff {h : ℂ} {χ : FormalQSeries} :
    χ ∈ QSeriesAt h ↔ ∀ e : ℂ, (∀ n : ℕ, e ≠ h + (n : ℂ)) → χ e = 0 := Iff.rfl

/-- A series based at `h` vanishes at the negative integer offsets — the hypothesis form used by
the banked `qConv_apply_of_support`. -/
theorem QSeriesAt.support_neg {h : ℂ} {χ : FormalQSeries} (hχ : χ ∈ QSeriesAt h) :
    ∀ i : ℤ, i < 0 → χ (h + (i : ℂ)) = 0 := by
  intro i hi
  refine hχ _ (fun n hn => ?_)
  have hcast : (i : ℂ) = (n : ℂ) := by linear_combination hn
  have hz : i = (n : ℤ) := by exact_mod_cast hcast
  omega

/-- `qConv` preserves the base point. -/
theorem qConv_mem_QSeriesAt (f : ℕ → ℂ) {h : ℂ} {χ : FormalQSeries} (hχ : χ ∈ QSeriesAt h) :
    qConv f χ ∈ QSeriesAt h := by
  intro e he
  have hz : ∀ n : ℕ, f n * χ (e - (n : ℂ)) = 0 := by
    intro n
    have hχ0 : χ (e - (n : ℂ)) = 0 := by
      refine hχ _ (fun m hm => ?_)
      exact he (m + n) (by push_cast; linear_combination hm)
    rw [hχ0, mul_zero]
  rw [qConv]
  simp only [hz, finsum_zero]

/-- Two series based at `h` that agree on `h + ℕ` are equal. -/
theorem QSeriesAt.ext {h : ℂ} {χ ψ : FormalQSeries} (hχ : χ ∈ QSeriesAt h) (hψ : ψ ∈ QSeriesAt h)
    (heq : ∀ N : ℕ, χ (h + (N : ℂ)) = ψ (h + (N : ℂ))) : χ = ψ := by
  funext e
  by_cases he : ∃ n : ℕ, e = h + (n : ℂ)
  · obtain ⟨N, rfl⟩ := he
    exact heq N
  · push_neg at he
    rw [hχ e he, hψ e he]

/-! ## The `PowerSeries ℂ`-action -/

/-- **The action**: `PowerSeries ℂ` *is* `(ℕ → ℂ, ⋆)`, and it acts on formal `q`-series by
`qConv`. -/
noncomputable def psSMul (F : PowerSeries ℂ) (χ : FormalQSeries) : FormalQSeries :=
  qConv (fun n => PowerSeries.coeff n F) χ

theorem psSMul_apply_coset (F : PowerSeries ℂ) {h : ℂ} {χ : FormalQSeries}
    (hχ : χ ∈ QSeriesAt h) (N : ℕ) :
    psSMul F χ (h + (N : ℂ))
      = ∑ n ∈ Finset.range (N + 1),
          PowerSeries.coeff n F * χ (h + ((N - n : ℕ) : ℂ)) :=
  qConv_apply_of_support _ _ h (QSeriesAt.support_neg hχ) N

theorem psSMul_mem (F : PowerSeries ℂ) {h : ℂ} {χ : FormalQSeries} (hχ : χ ∈ QSeriesAt h) :
    psSMul F χ ∈ QSeriesAt h := qConv_mem_QSeriesAt _ hχ

/-- **Unitality** — and it needs no support hypothesis. -/
theorem psSMul_one (χ : FormalQSeries) : psSMul 1 χ = χ := by
  classical
  funext e
  rw [psSMul, qConv]
  have hsub : (Function.support fun n : ℕ =>
      PowerSeries.coeff n (1 : PowerSeries ℂ) * χ (e - (n : ℂ))) ⊆ ({0} : Finset ℕ) := by
    intro n hn
    by_contra hnot
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hnot
    refine hn ?_
    change PowerSeries.coeff n (1 : PowerSeries ℂ) * χ (e - (n : ℂ)) = 0
    rw [PowerSeries.coeff_one, if_neg hnot, zero_mul]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  simp

/-- **Associativity** — the Cauchy product of `PowerSeries ℂ` is exactly the composition of
two `qConv`s.  This is what makes `Submodule (PowerSeries ℂ) (QSeriesAt h)` — the `R`-span — a
statable object. -/
theorem psSMul_mul (F G : PowerSeries ℂ) {h : ℂ} {χ : FormalQSeries} (hχ : χ ∈ QSeriesAt h) :
    psSMul (F * G) χ = psSMul F (psSMul G χ) := by
  classical
  refine QSeriesAt.ext (psSMul_mem _ hχ) (psSMul_mem _ (psSMul_mem _ hχ)) (fun N => ?_)
  rw [psSMul_apply_coset _ hχ N, psSMul_apply_coset _ (psSMul_mem G hχ) N]
  have hinner : ∀ n ∈ Finset.range (N + 1),
      PowerSeries.coeff n F * psSMul G χ (h + ((N - n : ℕ) : ℂ))
        = ∑ k ∈ Finset.range (N - n + 1),
            PowerSeries.coeff n F * PowerSeries.coeff k G * χ (h + ((N - n - k : ℕ) : ℂ)) := by
    intro n _
    rw [psSMul_apply_coset _ hχ (N - n), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_assoc]
  rw [Finset.sum_congr rfl hinner,
    sum_triangle_swap (fun n k => PowerSeries.coeff n F * PowerSeries.coeff k G
      * χ (h + ((N - n - k : ℕ) : ℂ))) N]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hPN : P ≤ N := by have := Finset.mem_range.mp hP; omega
  rw [PowerSeries.coeff_mul, Finset.sum_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun a ha => ?_
  have haP : a ≤ P := by have := Finset.mem_range.mp ha; omega
  have hcast : N - a - (P - a) = N - P := by omega
  rw [hcast, mul_assoc]

theorem psSMul_zero_left (χ : FormalQSeries) : psSMul 0 χ = 0 := by
  rw [psSMul]
  have : (fun n : ℕ => PowerSeries.coeff n (0 : PowerSeries ℂ)) = 0 := by
    funext n; simp
  rw [this, qConv_zero_left]

theorem psSMul_zero_right (F : PowerSeries ℂ) : psSMul F 0 = 0 := by
  rw [psSMul, qConv_zero_right]

theorem psSMul_add_left (F G : PowerSeries ℂ) {h : ℂ} {χ : FormalQSeries}
    (hχ : χ ∈ QSeriesAt h) : psSMul (F + G) χ = psSMul F χ + psSMul G χ := by
  refine QSeriesAt.ext (psSMul_mem _ hχ)
    (Submodule.add_mem _ (psSMul_mem _ hχ) (psSMul_mem _ hχ)) (fun N => ?_)
  change _ = psSMul F χ (h + (N : ℂ)) + psSMul G χ (h + (N : ℂ))
  rw [psSMul_apply_coset _ hχ N, psSMul_apply_coset _ hχ N, psSMul_apply_coset _ hχ N,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by rw [map_add]; ring

theorem psSMul_add_right (F : PowerSeries ℂ) {h : ℂ} {χ ψ : FormalQSeries}
    (hχ : χ ∈ QSeriesAt h) (hψ : ψ ∈ QSeriesAt h) :
    psSMul F (χ + ψ) = psSMul F χ + psSMul F ψ := by
  refine QSeriesAt.ext (psSMul_mem _ (Submodule.add_mem _ hχ hψ))
    (Submodule.add_mem _ (psSMul_mem _ hχ) (psSMul_mem _ hψ)) (fun N => ?_)
  change _ = psSMul F χ (h + (N : ℂ)) + psSMul F ψ (h + (N : ℂ))
  rw [psSMul_apply_coset _ (Submodule.add_mem _ hχ hψ) N, psSMul_apply_coset _ hχ N,
    psSMul_apply_coset _ hψ N, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  change PowerSeries.coeff n F * (χ (h + ((N - n : ℕ) : ℂ)) + ψ (h + ((N - n : ℕ) : ℂ))) = _
  ring

/-! ## `QSeriesAt h` as a `PowerSeries ℂ`-module -/

noncomputable instance instSMulPowerSeriesQSeriesAt (h : ℂ) :
    SMul (PowerSeries ℂ) ↥(QSeriesAt h) where
  smul F χ := ⟨psSMul F (χ : FormalQSeries), psSMul_mem F χ.2⟩

@[simp] theorem coe_psSMul (h : ℂ) (F : PowerSeries ℂ) (χ : ↥(QSeriesAt h)) :
    ((F • χ : ↥(QSeriesAt h)) : FormalQSeries) = psSMul F (χ : FormalQSeries) := rfl

/-- **`QSeriesAt h` is a `PowerSeries ℂ`-module.**  Hence `Submodule (PowerSeries ℂ)
(QSeriesAt h)` — "the `R`-span of the block values" — is a statable object. -/
noncomputable instance instModulePowerSeriesQSeriesAt (h : ℂ) :
    Module (PowerSeries ℂ) ↥(QSeriesAt h) where
  one_smul χ := Subtype.ext (psSMul_one _)
  mul_smul F G χ := Subtype.ext (psSMul_mul F G χ.2)
  smul_zero F := Subtype.ext (psSMul_zero_right F)
  smul_add F χ ψ := Subtype.ext (psSMul_add_right F χ.2 ψ.2)
  add_smul F G χ := Subtype.ext (psSMul_add_left F G χ.2)
  zero_smul χ := Subtype.ext (psSMul_zero_left _)

end VOA
