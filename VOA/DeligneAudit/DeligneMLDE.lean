/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterTypes
import VOA.DeligneAudit.A2CharacterInterface

/-!
# The Arakawa–Kawasetsu recurrence: coefficient form, uniqueness, and the character targets

For the Deligne series at `k = -1 - h∨/6` the normalised vacuum character
`f = q^{-c/24} ∑ d_N q^N` (`c = -2(h∨+1)`) satisfies the second-order modular linear differential
equation (Arakawa–Kawasetsu, arXiv:1610.05865, §7)

  `(θ - E₂/6) θ f = ((h²-1)/144) E₄ f`,      `θ = q d/dq`,  `h = h∨`.

Read coefficientwise it is the recurrence `mldeCoeff h` (`DeligneCharacterTypes`):

  `N(6N + h) d_N = ∑_{r=1}^{N} [10(h²-1)σ₃(r) - (24(N-r) + 2(h+1))σ₁(r)] d_{N-r}`.

This file is the purely formal half of the MLDE route.  It proves:

* `mldeCoeff_recurrence` — the AK coefficients satisfy their recurrence (an unfolding lemma);
* `eq_mldeCoeff_of_isAKSolution` — **uniqueness**: every sequence over a field of characteristic
  zero with `d₀ = 1` satisfying the recurrence is `mldeCoeff h`.  The leading factor `N(6N+h)` never
  vanishes for `N ≥ 1`, so there is nothing analytic here;
* `targetLowerBoundQ_of_isAKSolution` — if the graded dimensions of a VOA satisfy the recurrence,
  the character target `TargetLowerBoundQ W (mldeCoeff h)` holds (with equality);
* `A2.kacWakimotoLowerBound_of_isAKSolution` — the A₂ Kac–Wakimoto input from the recurrence for
  `L_{-3/2}(sl₃)` plus the q-series identity `A2ProductMLDE` (`∏(1+q^r)^8` solves the `h = 3`
  recurrence).  Both inputs are proved: `A2.vacuumQuarticRelation` gives the recurrence
  (`DeligneVacuumRelationA2.lean`) and `A2.a2ProductMLDE` the product identity
  (`DeligneMLDEProduct.lean`).

The VOA-side input (the graded dimensions satisfy the recurrence) is reduced to a single weight-four
statement about the torus one-point function in `DeligneMLDEBlock`.
-/

namespace VOA.DeligneAudit.DeligneMLDE

open VertexOperatorAlgebra DeligneCharacter

/-! ## The recurrence -/

/-- The kernel of the AK recurrence: the coefficient of `d_{N-r}` on the right-hand side. -/
def akKernel (h N r : ℕ) : ℚ :=
  10 * ((h : ℚ) ^ 2 - 1) * sigmaK 3 r - (24 * ((N : ℚ) - r) + 2 * ((h : ℚ) + 1)) * sigmaK 1 r

/-- **A normalised solution of the AK recurrence** with `h = h∨`, over a field of characteristic
zero: `d₀ = 1` and `N(6N+h) d_N = ∑_{r=1}^{N} akKernel h N r · d_{N-r}` for `N ≥ 1`. -/
structure IsAKSolution {K : Type*} [Field K] [CharZero K] (h : ℕ) (d : ℕ → K) : Prop where
  zero : d 0 = 1
  step : ∀ N : ℕ, 1 ≤ N →
    (N : K) * (6 * N + h) * d N
      = ∑ r ∈ Finset.range N, (akKernel h N (r + 1) : K) * d (N - (r + 1))

theorem mldeList_length (h : ℕ) : ∀ n, (mldeList h n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [mldeList, mldeList_length h n]

theorem mldeList_getD (h : ℕ) : ∀ n i, i ≤ n → (mldeList h n).getD i 0 = mldeCoeff h i := by
  intro n
  induction n with
  | zero => intro i hi; obtain rfl : i = 0 := by omega
            rfl
  | succ n ih =>
      intro i hi
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · have hl : i < (mldeList h n).length := by rw [mldeList_length]; exact hlt
        rw [show mldeList h (n + 1) = mldeList h n ++ _ from rfl, List.getD_append _ _ _ _ hl]
        exact ih i (by omega)
      · obtain rfl : i = n + 1 := by omega
        rfl

/-- The last entry of `mldeList h (n+1)` is the recurrence expression. -/
theorem mldeCoeff_succ (h n : ℕ) :
    mldeCoeff h (n + 1)
      = (∑ r ∈ Finset.range (n + 1), akKernel h (n + 1) (r + 1) * mldeCoeff h (n + 1 - (r + 1)))
        / (((n + 1 : ℕ) : ℚ) * (6 * ((n + 1 : ℕ) : ℚ) + h)) := by
  have hl : (mldeList h n).length = n + 1 := mldeList_length h n
  rw [mldeCoeff, show mldeList h (n + 1) = mldeList h n ++ _ from rfl,
    List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [Finset.mem_range] at hr
  rw [mldeList_getD h n _ (by omega), akKernel]
  push_cast
  ring

/-- **The AK coefficients solve the recurrence.** -/
theorem mldeCoeff_isAKSolution (h : ℕ) : IsAKSolution (K := ℚ) h (mldeCoeff h) where
  zero := rfl
  step := by
    intro N hN
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [mldeCoeff_succ]
    have hne : (((n + 1 : ℕ) : ℚ) * (6 * ((n + 1 : ℕ) : ℚ) + h)) ≠ 0 := by positivity
    field_simp
    simp only [Rat.cast_id]

/-- **Uniqueness of the normalised solution.** -/
theorem eq_mldeCoeff_of_isAKSolution {K : Type*} [Field K] [CharZero K] {h : ℕ} {d : ℕ → K}
    (hd : IsAKSolution h d) : ∀ N, d N = (mldeCoeff h N : K) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [hd.zero]; simp [mldeCoeff, mldeList]
    · have hrec := hd.step N hN
      have hrecQ := (mldeCoeff_isAKSolution h).step N hN
      have hne : (N : K) * (6 * N + h) ≠ 0 := by
        have h1 : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
        have h2 : (6 * (N : K) + h) ≠ 0 := by
          have : (6 * (N : K) + h) = ((6 * N + h : ℕ) : K) := by push_cast; ring
          rw [this]; exact_mod_cast (by omega : 6 * N + h ≠ 0)
        exact mul_ne_zero h1 h2
      have hsum : ∑ r ∈ Finset.range N, (akKernel h N (r + 1) : K) * d (N - (r + 1))
          = ((∑ r ∈ Finset.range N, akKernel h N (r + 1) * mldeCoeff h (N - (r + 1)) : ℚ) : K) := by
        push_cast
        refine Finset.sum_congr rfl (fun r hr => ?_)
        rw [Finset.mem_range] at hr
        rw [ih _ (by omega)]
      simp only [Rat.cast_id] at hrecQ
      rw [hsum, ← hrecQ] at hrec
      push_cast at hrec
      exact mul_left_cancel₀ hne hrec

/-! ## From the recurrence to the character targets -/

section Targets

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **The graded dimensions are the AK coefficients**, if they solve the recurrence. -/
theorem finrank_eq_mldeCoeff_of_isAKSolution (W : VertexOperatorAlgebra V) {h : ℕ}
    (hW : IsAKSolution h (fun N : ℕ => (Module.finrank ℂ (W.grading N) : ℂ))) (N : ℕ) :
    (Module.finrank ℂ (W.grading N) : ℚ) = mldeCoeff h N := by
  have h1 := eq_mldeCoeff_of_isAKSolution hW N
  have h2 : ((Module.finrank ℂ (W.grading N) : ℚ) : ℂ) = ((mldeCoeff h N : ℚ) : ℂ) := by
    push_cast; exact h1
  exact_mod_cast h2

/-- **the target lower bound from the recurrence** (type-generic; with equality). -/
theorem targetLowerBoundQ_of_isAKSolution (W : VertexOperatorAlgebra V) {h : ℕ}
    (hW : IsAKSolution h (fun N : ℕ => (Module.finrank ℂ (W.grading N) : ℂ))) :
    TargetLowerBoundQ W (mldeCoeff h) :=
  ⟨fun N => (finrank_eq_mldeCoeff_of_isAKSolution W hW N).symm.le⟩

end Targets

end VOA.DeligneAudit.DeligneMLDE

/-! ## A₂: the Kac–Wakimoto input from the recurrence -/

namespace VOA.DeligneAudit.A2

open VOA.DeligneAudit.DeligneMLDE VOA.DeligneAudit.DeligneCharacter

/-- **The A₂ q-series identity**: `∏_{r≥1}(1+q^r)^8` solves the `h∨ = 3` AK recurrence, i.e.
`q^{1/3}∏(1+q^r)^8 = (η(2τ)/η(τ))^8` satisfies `(θ - E₂/6)θ f = (1/18) E₄ f`.  Equivalent to the
`Γ₀(2)` identity `(2E₂(2τ) - E₂(τ))² = (E₄(τ) + 4E₄(2τ))/5` together with Ramanujan's
`θE₂ = (E₂² - E₄)/12`.  Proved: `A2.a2ProductMLDE` (`DeligneMLDEProduct.lean`). -/
structure A2ProductMLDE : Prop where
  sol : IsAKSolution (K := ℚ) 3 (fun N => (productCoeff N : ℚ))

/-- The product identity in coefficient form: `[q^N]∏(1+q^r)^8 = mldeCoeff 3 N`. -/
theorem productCoeff_eq_mldeCoeff (hprod : A2ProductMLDE) (N : ℕ) :
    (productCoeff N : ℚ) = mldeCoeff 3 N := by
  simpa using eq_mldeCoeff_of_isAKSolution hprod.sol N

/-- **The Kac–Wakimoto lower bound from the AK recurrence.**  If the graded dimensions of
`L_{-3/2}(sl₃)` solve the `h∨ = 3` AK recurrence and `∏(1+q^r)^8` does too, then
`[q^N]∏(1+q^r)^8 = dim L_{-3/2}(sl₃)_N` for all `N`; in particular `KacWakimotoLowerBound`. -/
theorem kacWakimotoLowerBound_of_isAKSolution
    (hW : IsAKSolution 3 (fun N : ℕ => (Module.finrank ℂ (W.grading N) : ℂ)))
    (hprod : A2ProductMLDE) : KacWakimotoLowerBound :=
  ⟨fun N => by
    have h1 := finrank_eq_mldeCoeff_of_isAKSolution W hW N
    have h2 := productCoeff_eq_mldeCoeff hprod N
    have : (productCoeff N : ℚ) = (Module.finrank ℂ (W.grading N) : ℚ) := by rw [h1, h2]
    exact (Nat.cast_injective this).le⟩

/-- The first coefficients of the `h∨ = 3` AK solution: `1, 8, 36, 128`, matching
`productCoeff_small`. -/
theorem mldeCoeff_A2_small : (List.range 4).map (mldeCoeff 3) = [1, 8, 36, 128] := by
  decide +kernel

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneMLDE.mldeCoeff_isAKSolution
#print axioms VOA.DeligneAudit.DeligneMLDE.eq_mldeCoeff_of_isAKSolution
#print axioms VOA.DeligneAudit.DeligneMLDE.targetLowerBoundQ_of_isAKSolution
#print axioms VOA.DeligneAudit.A2.kacWakimotoLowerBound_of_isAKSolution
#print axioms VOA.DeligneAudit.A2.mldeCoeff_A2_small
end AxiomAudit
