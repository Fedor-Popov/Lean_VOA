/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.RRLowerAndrews

/-!
# The second Rogers–Ramanujan identity, coefficientwise, in Rocha-Caridi form

Letting `n → ∞` in Andrews' polynomial identity (`Ecoef_eq_Rcoef`) — concretely, taking
`n = 7N + 7`, where every Gaussian coefficient that contributes to `q^N` has already stabilised
(`qc_box`) — gives, for every `N`,

`Σ_{j ≥ 0} #{partitions of N - j(j+1) into parts ≤ j}  =  Σ_{k ∈ ℤ} (-1)^k p(N - k(5k+3)/2)`.

The left side is the coefficient of `q^N` in `Σ_j q^{j(j+1)} / (q)_j`, the generating function
of partitions into parts `≥ 2` with adjacent difference `≥ 2`; the right side is the coefficient
of `q^N` in the Rocha-Caridi alternating sum `(q)_∞⁻¹ Σ_k (-1)^k q^{k(5k+3)/2}`, the vacuum
character of the `(2,5)` minimal model.  **No Jacobi triple product and no infinite product is
needed**: the Rocha-Caridi side is already an alternating sum of partition numbers.

* `gapSum N`, `rc N` — the two sides;
* `gapSum_eq_rc : gapSum N = rc N`;
* `card_wt` — the multiplicity-tuple count used by the Lee–Yang coefficient
  `gapTwoCoefficient` equals `pc`.

All proved, no hypotheses.
-/

namespace VOA.RRLower

open Finset

noncomputable section

/-- The gap-two side: `Σ_j #{partitions of N - j(j+1) into parts ≤ j}`. -/
def gapSum (N : ℕ) : ℤ := ∑ j ∈ range (N + 1), pc j ((N : ℤ) - (j : ℤ) * ((j : ℤ) + 1))

/-- The Rocha-Caridi side: `Σ_k (-1)^k p(N - k(5k+3)/2)` (terms with `|k| > N` vanish). -/
def rc (N : ℕ) : ℤ := ∑ k ∈ Ico (-(N : ℤ) - 1) ((N : ℤ) + 1), sgn k * pp ((N : ℤ) - ee k)

theorem Ecoef_large (N n : ℕ) (hn : 3 * N ≤ n) : Ecoef n N = gapSum N := by
  unfold Ecoef gapSum
  have hterm : ∀ j ∈ range (n + 1),
      qc (n - j) (j : ℤ) ((N : ℤ) - (j : ℤ) * ((j : ℤ) + 1)) =
        pc j ((N : ℤ) - (j : ℤ) * ((j : ℤ) + 1)) := by
    intro j _
    rcases lt_or_ge ((N : ℤ) - (j : ℤ) * ((j : ℤ) + 1)) 0 with h | h
    · rw [qc_of_neg_N _ _ h, pc_of_neg _ h]
    · have h1 : (j : ℤ) ≤ N := by nlinarith
      have hjN : j ≤ N := by exact_mod_cast h1
      have h2 : (N : ℤ) - (j : ℤ) * ((j : ℤ) + 1) ≤ N := by nlinarith
      rw [show n - j = j + (n - 2 * j) by omega]
      refine qc_box j (n - 2 * j) _ ?_
      rw [Nat.cast_sub (by omega)]
      push_cast
      omega
  rw [Finset.sum_congr rfl hterm]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j _ hj'
    simp only [Finset.mem_range, not_lt] at hj'
    apply pc_of_neg
    have : (N : ℤ) + 1 ≤ j := by exact_mod_cast hj'
    nlinarith

theorem Rterm_large (N n : ℕ) (hn : 7 * N + 7 ≤ n) (k : ℤ) :
    Rterm n k N = sgn k * pp ((N : ℤ) - ee k) := by
  unfold Rterm
  congr 1
  rcases lt_or_ge ((N : ℤ) - ee k) 0 with h | h
  · rw [qc_of_neg_N _ _ h, pp_of_neg h]
  · have hk := abs_le_ee k
    have hk1 : -(N : ℤ) ≤ k := by
      rcases le_or_gt 0 k with h0 | h0
      · omega
      · rw [abs_of_neg h0] at hk; omega
    have hk2 : k ≤ N := by
      rcases le_or_gt 0 k with h0 | h0
      · rw [abs_of_nonneg h0] at hk; omega
      · omega
    have hee := ee_nonneg k
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = ((n : ℤ) - 5 * k) / 2 :=
      ⟨(((n : ℤ) - 5 * k) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨b, hb⟩ : ∃ b : ℕ, n + 1 = m + b := ⟨n + 1 - m, by omega⟩
    rw [← hm, hb, qc_box m b _ (by omega), pc_eq_pp m (by omega)]

theorem Rcoef_large (N n : ℕ) (hn : 7 * N + 7 ≤ n) : Rcoef n N = rc N := by
  unfold Rcoef rc
  rw [Finset.sum_congr rfl (fun k _ => Rterm_large N n hn k)]
  symm
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_Ico] at hk ⊢
    omega
  · intro k _ hk
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
    have h := abs_le_ee k
    rw [pp_of_neg, mul_zero]
    rcases hk with hk | hk
    · rw [abs_of_neg (by omega)] at h; omega
    · rw [abs_of_nonneg (by omega)] at h; omega

/-- **The second Rogers–Ramanujan identity, coefficientwise, in Rocha-Caridi form.** -/
theorem gapSum_eq_rc (N : ℕ) : gapSum N = rc N := by
  rw [← Ecoef_large N (7 * N + 7) (by omega), Ecoef_eq_Rcoef, Rcoef_large N _ le_rfl]

/-! ## Multiplicity tuples -/

/-- The number of multiplicity tuples `a : Fin r → Fin (B+1)` of weight
`Σ_j (j+1) a_j = M` is `pc r M`, as soon as `M ≤ B`. -/
theorem card_wt : ∀ (B r : ℕ) (M : ℤ), M ≤ B →
    (Fintype.card {a : Fin r → Fin (B + 1) //
      ∑ j : Fin r, ((j : ℕ) + 1 : ℤ) * ((a j : ℕ) : ℤ) = M} : ℤ) = pc r M
  | B, 0, M, _ => by
      classical
      rw [pc_zero]
      by_cases h : M = 0
      · subst h
        rw [if_pos rfl, Nat.cast_eq_one, Fintype.card_eq_one_iff]
        refine ⟨⟨Fin.elim0, by simp⟩, fun a => Subtype.ext (funext fun i => Fin.elim0 i)⟩
      · rw [if_neg h, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
        exact ⟨fun a => h (by simpa using a.2.symm)⟩
  | B, r + 1, M, hM => by
      classical
      let e : Fin (B + 1) × (Fin r → Fin (B + 1)) ≃ (Fin (r + 1) → Fin (B + 1)) :=
        Fin.snocEquiv (fun _ => Fin (B + 1))
      have hwt : ∀ p : Fin (B + 1) × (Fin r → Fin (B + 1)),
          ∑ j : Fin (r + 1), ((j : ℕ) + 1 : ℤ) * (((e p) j : ℕ) : ℤ) =
            ∑ j : Fin r, ((j : ℕ) + 1 : ℤ) * ((p.2 j : ℕ) : ℤ) +
              ((r : ℤ) + 1) * ((p.1 : ℕ) : ℤ) := by
        intro p
        simp only [e, Fin.snocEquiv_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
      rw [← Fintype.card_congr (e.subtypeEquiv (fun p => Iff.rfl)), Fintype.card_subtype,
        Finset.card_filter, Fintype.sum_prod_type]
      simp only [hwt]
      push_cast
      have hinner : ∀ t : Fin (B + 1),
          (∑ y : Fin r → Fin (B + 1),
              if ∑ j : Fin r, ((j : ℕ) + 1 : ℤ) * ((y j : ℕ) : ℤ) +
                  ((r : ℤ) + 1) * ((t : ℕ) : ℤ) = M
              then (1 : ℤ) else 0) =
            pc r (M - ((r : ℤ) + 1) * ((t : ℕ) : ℤ)) := by
        intro t
        rw [← card_wt B r (M - ((r : ℤ) + 1) * ((t : ℕ) : ℤ)) (by
          have : (0 : ℤ) ≤ ((r : ℤ) + 1) * ((t : ℕ) : ℤ) := by positivity
          omega), Fintype.card_subtype, Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun y _ => ?_
        congr 1
        apply propext
        constructor <;> intro h <;> omega
      rw [Finset.sum_congr rfl (fun t _ => hinner t)]
      rw [pc_succ_range r M B hM]
      exact Fin.sum_univ_eq_sum_range (fun t => pc r (M - ((r : ℤ) + 1) * (t : ℤ))) (B + 1)

end

end VOA.RRLower
