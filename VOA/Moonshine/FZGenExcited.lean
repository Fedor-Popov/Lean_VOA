/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FockSpanCharged

/-!
# The charged excited spanning argument, for an arbitrary charge and target

`FockSpanCharged.lean` proves `ExcitedSpanned` for `V₀⁺`: every `P(p ⊗ e^γ)`, `γ ∈ Λ₀ ∖ 0`,
Fock weight `≥ 1`, is a combination of weight-raising products.  The proof uses its target
`Tsub hγ n` **only** through one closure property (`quadF_mem_Tsub`): the modes `m ≤ 0` of the
quadratic Heisenberg states `h_a(-i-1)h_b(-j-1)𝟙` on lower-weight charge-`γ` states land in it.
And it uses the charge only through `γ ≠ 0` in the even lattice `Λ` (so `|γ|² ≥ 4` is even).

Here the argument is restated for **any** `γ ∈ Λ ∖ 0` (in particular for `γ` in the coset
`Λ ∖ Λ₀`, the charges of `V₃⁺`) and **any** family of subspaces `T : ℤ → Submodule ℂ Fk` with that
closure property (`QuadClosed`):

`gradingWN_le_of_quadClosed : γ ≠ 0 → QuadClosed γ T → 1 ≤ w → (Fock weight w) ≤ T (w + ½|γ|²)`.

The proofs are those of `FockSpanCharged` / `FockSpanBase.step_quad` verbatim, with
`quadF_mem_Tsub` replaced by the hypothesis.

## Main results
* `QuadClosed`, `step_quadT`, `charged_deg_one_zeroT`, `charged_deg_oneT`, `charged_baseT`.
* `gradingWN_le_of_quadClosed`.

## Status
`sorry`-free; no project axiom.  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.FZGen

open VOA VOA.Moonshine VOA.Moonshine.SigmaExist VOA.Moonshine.ZhuGen VOA.Moonshine.FockSpan LatGen
  IntegralLattice HeisenbergN MvPolynomial
open Submodule

/-- The closure property of a family of target subspaces used by the charged spanning argument:
every mode `m ≤ 0` of a quadratic Heisenberg state of weight `< n` on a charge-`γ` Fock state of
weight `< n` (total weight `n`) lies in `T n`. -/
def QuadClosed (γ : leech.carrier) (T : ℤ → Submodule ℂ Fk) : Prop :=
  ∀ (i j : ℕ) (a b : Fin (rank leech)) (n m : ℤ), m ≤ 0 → ∀ (w : ℕ) (p : Fk),
    p ∈ gradingWN (rank leech) w → (i : ℤ) + j + 2 < n → (w : ℤ) + LatGen.halfNorm leech γ < n →
    ((i : ℤ) + j + 2) + ((w : ℤ) + LatGen.halfNorm leech γ) - m - 1 = n →
    quadF γ a i b j (-m - 1) p ∈ T n

section

variable {γ : leech.carrier} {T : ℤ → Submodule ℂ Fk}

theorem step_quadT (hT : QuadClosed γ T) (n : ℤ) (D : ℕ) (w : ℕ)
    (hn : n = (w : ℤ) + LatGen.halfNorm leech γ)
    (IH : Fdw D w ≤ T n) (v1 v2 : ℕ × Fin (rank leech)) (s' : (ℕ × Fin (rank leech)) →₀ ℕ)
    (hdeg : s'.degree + 1 = D) (hw : (v1.1 : ℤ) + v2.1 + 2 + (wt s' : ℤ) = w)
    (hpos : 1 ≤ (wt s' : ℤ) + LatGen.halfNorm leech γ) :
    (X v1 * X v2 * monomial s' 1 : Fk) ∈ T n := by
  have hp := monomial_mem_Fdw s'
  have hlead := quadF_lead γ v1.2 v1.1 v2.2 v2.1 hp
  have hmem := hT v1.1 v2.1 v1.2 v2.2 n (-1) (by norm_num) _ _
    (monomial_mem_gradingWN s') (by omega) (by omega) (by omega)
  rw [show -(-1 : ℤ) - 1 = 0 by norm_num] at hmem
  have hR : quadF γ v1.2 v1.1 v2.2 v2.1 0 (monomial s' 1) - X (v1.1, v1.2) * X (v2.1, v2.2) *
      monomial s' 1 ∈ T n := by
    apply IH
    rw [← hdeg]
    convert hlead using 2
    omega
  have := sub_mem hmem hR
  rwa [sub_sub_cancel] at this

theorem charged_deg_one_zeroT (hT : QuadClosed γ T) (hγ0 : γ ≠ 0) (c : Fin (rank leech)) :
    (X (0, c) : Fk) ∈ T (1 + LatGen.halfNorm leech γ) := by
  have hh := two_le_halfNorm hγ0
  set U := T (1 + LatGen.halfNorm leech γ)
  have hR : ∀ a b, U.mkQ (chargeCoord leech γ b • (X (0, a) : Fk) + chargeCoord leech γ a •
      (X (0, b) : Fk)) = 0 := by
    intro a b
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have := hT 0 0 a b (1 + LatGen.halfNorm leech γ) 0 le_rfl 0 1
      one_mem_gradingWN (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    rwa [show -(0 : ℤ) - 1 = -1 by norm_num, quadF_D_one] at this
  have := vanish_of_sym (fun b => chargeCoord leech γ b) (fun a => U.mkQ (X (0, a) : Fk))
    (fun a b => by rw [← map_smul, ← map_smul, ← map_add]; exact hR a b)
    (exists_chargeCoord_ne_zero hγ0) c
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

/-- Charged degree one, for any charge `γ ≠ 0` and any `QuadClosed` target. -/
theorem charged_deg_oneT (hT : QuadClosed γ T) (hγ0 : γ ≠ 0) (t : ℕ) (c : Fin (rank leech)) :
    (X (t, c) : Fk) ∈ T ((t : ℤ) + 1 + LatGen.halfNorm leech γ) := by
  rcases t with _ | τ
  · simpa using charged_deg_one_zeroT hT hγ0 c
  have hh := two_le_halfNorm hγ0
  set n : ℤ := ((τ + 1 : ℕ) : ℤ) + 1 + LatGen.halfNorm leech γ with hn
  set U := T n
  set g : Fin (rank leech) → ℂ := fun b => chargeCoord leech γ b with hg
  set φ : Fin (rank leech) → Fk ⧸ U := fun a => U.mkQ (X (τ + 1, a) : Fk) with hφ
  have hL : ∀ a c, U.mkQ (X (0, a) * X (τ, c) : Fk)
      = -(((-1 : ℂ) ^ τ * g c) • φ a + (((τ : ℂ) + 1) * g a) • φ c) := by
    intro a c
    have := hT 0 τ a c n (-1) (by norm_num) 0 1 one_mem_gradingWN
      (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    rw [show -(-1 : ℤ) - 1 = 0 by norm_num, quadF_lead_one, add_assoc] at this
    rw [eq_neg_iff_add_eq_zero]
    simp only [hφ, hg, ← map_smul, ← map_add]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact this
  have hR : ∀ a b c, ((if c = b then ((τ : ℂ) + 1) • φ a else 0)
      + (if c = a then ((τ : ℂ) + 1) • φ b else 0))
      - ((-1 : ℂ) ^ τ * g c) • (g b • φ a + g a • φ b)
      - (2 * ((τ : ℂ) + 1) * g a * g b) • φ c = 0 := by
    intro a b c
    have h := hT 0 0 a b n 0 le_rfl _ _ (X_mem_gradingWN (τ, c))
      (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    rw [show -(0 : ℤ) - 1 = -1 by norm_num, ← mul_one (X (τ, c) : Fk), quadD_X, quadF_D_one]
      at h
    have h0 := (Submodule.Quotient.mk_eq_zero U).mpr h
    rw [← Submodule.mkQ_apply] at h0
    simp only [map_add, mul_add, mul_smul_comm, apply_ite U.mkQ, map_zero, mul_one,
      LinearMap.map_smul_of_tower] at h0
    rw [mul_comm (X (τ, c) : Fk) (X (0, a)), mul_comm (X (τ, c) : Fk) (X (0, b)), hL, hL] at h0
    split_ifs at h0 ⊢ with h1 h2 h2 <;> (try subst h1) <;> (try subst h2) <;>
      (simp only [hφ, hg] at h0 ⊢; linear_combination (norm := module) h0)
  have hT' := charged_algebra g φ ((τ : ℂ) + 1) ((-1 : ℂ) ^ τ) ((leech.form γ γ : ℤ) : ℂ)
    (sum_chargeCoord_sq γ) hR (coeff_ne_zero_one τ _ (form_ge_four hγ0))
    (coeff_ne_zero_two τ _ (form_ge_four hγ0) ⟨LatGen.halfNorm leech γ, by
      have := two_mul_halfNorm γ; omega⟩) (exists_chargeCoord_ne_zero hγ0) c
  simpa only [hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hT'

theorem charged_baseT (hT : QuadClosed γ T) (hγ0 : γ ≠ 0) (w : ℕ) (hw : 1 ≤ w) :
    Fdw 1 w ≤ T ((w : ℤ) + LatGen.halfNorm leech γ) := by
  refine (Fdw_le_span 1 w).trans (span_le.mpr ?_)
  rintro _ ⟨s, hsd, hsw, rfl⟩
  rcases Nat.eq_zero_or_pos s.degree with h0 | h0
  · rw [eq_zero_of_degree_eq_zero h0, wt, map_zero] at hsw
    omega
  · obtain ⟨v, s', rfl⟩ := exists_single_add (s := s) h0
    rw [degree_single_add] at hsd
    obtain rfl : s' = 0 := eq_zero_of_degree_eq_zero (by omega)
    rw [wt_single_add, wt, map_zero] at hsw
    rw [SetLike.mem_coe, monomial_single_add_one, monomial_zero', C_1, mul_one]
    have := charged_deg_oneT hT hγ0 v.1 v.2
    rw [show ((v.1 : ℤ) + 1) = w by push_cast at hsw; omega] at this
    exact this

/-- **The charged excited spanning theorem, generic form.**  For `γ ∈ Λ ∖ 0` and any
`QuadClosed` family `T`, every Fock state of weight `w ≥ 1` lies in `T (w + ½|γ|²)`. -/
theorem gradingWN_le_of_quadClosed (hT : QuadClosed γ T) (hγ0 : γ ≠ 0) {w : ℕ} (hw : 1 ≤ w) :
    gradingWN (rank leech) w ≤ T ((w : ℤ) + LatGen.halfNorm leech γ) := by
  have hh := two_le_halfNorm hγ0
  refine gradingWN_le_of_Fdw (fun D => ?_)
  refine Fdw_le_of_ascent _ w 1 le_rfl (charged_baseT hT hγ0 _ hw)
    (fun D' _ IH v1 v2 s' hdeg hwt => step_quadT hT _ D' w rfl IH v1 v2 s' hdeg hwt
      (by omega)) D

end

end VOA.Moonshine.FZGen
