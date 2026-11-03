/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.QEvalShift

/-!
# `qEvalAt` is linear in the series, and summability descends across a vanishing segment

Two small lemmas the peeling argument of residual **(d)** needs and that the repo does not have.

* `qEvalAt` of a finite linear combination is that combination of the `qEvalAt`s — proved by
  induction on the `Finset`, so no `tsum`/`Finset.sum` interchange lemma is required.
* Summability at a base point descends to a **lower** base point across an initial segment of
  vanishing coefficients — the companion of `qEvalAt_shift`, needed to *apply* it.

## Main results

* `QSummableAt.add/.const_mul/.finsetSum`, `qEvalAt_add`, `qEvalAt_const_mul`, `qEvalAt_finsetSum`;
* `qSummableAt_of_lower`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

theorem QSummableAt.add {χ ψ : FormalQSeries} {d : ℂ} {τ : UpperHalfPlane}
    (hχ : QSummableAt χ d τ) (hψ : QSummableAt ψ d τ) :
    QSummableAt (fun e => χ e + ψ e) d τ :=
  Summable.congr (Summable.add hχ hψ)
    (fun n => by change _ = (χ (d + n) + ψ (d + n)) * (qParam τ) ^ n; ring)

theorem QSummableAt.const_mul {χ : FormalQSeries} {d : ℂ} {τ : UpperHalfPlane} (c : ℂ)
    (hχ : QSummableAt χ d τ) : QSummableAt (fun e => c * χ e) d τ :=
  Summable.congr (Summable.mul_left c hχ)
    (fun n => by change _ = (c * χ (d + n)) * (qParam τ) ^ n; ring)

theorem QSummableAt.finsetSum {κ : Type*} (J : Finset κ) (f : κ → FormalQSeries)
    (cc : κ → ℂ) (d : ℂ) (τ : UpperHalfPlane) (hsum : ∀ j ∈ J, QSummableAt (f j) d τ) :
    QSummableAt (fun e => ∑ j ∈ J, cc j * f j e) d τ := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa [QSummableAt] using summable_zero
  | insert j J hj ih =>
      have hjmem : QSummableAt (f j) d τ := hsum j (Finset.mem_insert_self j J)
      have hrest := ih (fun k hk => hsum k (Finset.mem_insert_of_mem hk))
      refine Summable.congr (QSummableAt.add (hjmem.const_mul (cc j)) hrest) (fun n => ?_)
      change (cc j * f j (d + n) + ∑ k ∈ J, cc k * f k (d + n)) * (qParam τ) ^ n
        = (∑ k ∈ insert j J, cc k * f k (d + n)) * (qParam τ) ^ n
      rw [Finset.sum_insert hj]

theorem qEvalAt_add {χ ψ : FormalQSeries} {d : ℂ} {τ : UpperHalfPlane}
    (hχ : QSummableAt χ d τ) (hψ : QSummableAt ψ d τ) :
    qEvalAt (fun e => χ e + ψ e) d τ = qEvalAt χ d τ + qEvalAt ψ d τ := by
  have hterm : (fun n : ℕ => (χ (d + n) + ψ (d + n)) * (qParam τ) ^ n)
      = fun n : ℕ => χ (d + n) * (qParam τ) ^ n + ψ (d + n) * (qParam τ) ^ n := by
    funext n; ring
  rw [qEvalAt, qEvalAt, qEvalAt]
  change _ * ∑' n : ℕ, (χ (d + n) + ψ (d + n)) * (qParam τ) ^ n = _
  rw [hterm, Summable.tsum_add hχ hψ]
  ring

theorem qEvalAt_const_mul (χ : FormalQSeries) (c : ℂ) (d : ℂ) (τ : UpperHalfPlane) :
    qEvalAt (fun e => c * χ e) d τ = c * qEvalAt χ d τ := by
  have hterm : (fun n : ℕ => (c * χ (d + n)) * (qParam τ) ^ n)
      = fun n : ℕ => c * (χ (d + n) * (qParam τ) ^ n) := by
    funext n; ring
  rw [qEvalAt, qEvalAt]
  change _ * ∑' n : ℕ, (c * χ (d + n)) * (qParam τ) ^ n = _
  rw [hterm, tsum_mul_left]
  ring

/-- `qEvalAt` of a finite linear combination. -/
theorem qEvalAt_finsetSum {κ : Type*} (J : Finset κ) (f : κ → FormalQSeries)
    (cc : κ → ℂ) (d : ℂ) (τ : UpperHalfPlane) (hsum : ∀ j ∈ J, QSummableAt (f j) d τ) :
    qEvalAt (fun e => ∑ j ∈ J, cc j * f j e) d τ = ∑ j ∈ J, cc j * qEvalAt (f j) d τ := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, qEvalAt]
      simp
  | insert j J hj ih =>
      have hjmem : QSummableAt (f j) d τ := hsum j (Finset.mem_insert_self j J)
      have hrest : ∀ k ∈ J, QSummableAt (f k) d τ := fun k hk =>
        hsum k (Finset.mem_insert_of_mem hk)
      have hsr : QSummableAt (fun e => ∑ k ∈ J, cc k * f k e) d τ :=
        QSummableAt.finsetSum J f cc d τ hrest
      have heq : (fun e => ∑ k ∈ insert j J, cc k * f k e)
          = fun e => cc j * f j e + ∑ k ∈ J, cc k * f k e := by
        funext e; rw [Finset.sum_insert hj]
      rw [heq, qEvalAt_add (hjmem.const_mul (cc j)) hsr, qEvalAt_const_mul,
        ih hrest, Finset.sum_insert hj]

/-- Summability descends to a lower base across a vanishing initial segment.  (The vanishing is
not needed for summability itself — only for the *value*, via `qEvalAt_shift`.) -/
theorem qSummableAt_of_lower (χ : FormalQSeries) (d : ℂ) (k : ℕ) (τ : UpperHalfPlane)
    (hsum : QSummableAt χ (d + (k : ℂ)) τ) : QSummableAt χ d τ := by
  rw [QSummableAt, ← summable_nat_add_iff k]
  have hterm : ∀ n : ℕ, χ (d + ((n + k : ℕ) : ℂ)) * (qParam τ) ^ (n + k)
      = (χ ((d + (k : ℂ)) + (n : ℂ)) * (qParam τ) ^ n) * (qParam τ) ^ k := by
    intro n
    have hc : d + ((n + k : ℕ) : ℂ) = (d + (k : ℂ)) + (n : ℂ) := by push_cast; ring
    rw [hc, pow_add]; ring
  exact Summable.congr (Summable.mul_right ((qParam τ) ^ k) hsum) (fun n => (hterm n).symm)

end VOA
