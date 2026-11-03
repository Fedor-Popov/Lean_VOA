/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FockSpanOps

/-!
# Quadratic products inside `V₀⁺` and the ascent in total degree  (Moonshine step M8g, R-gen)

`Tsub hγ n` is the space of Fock states `p` with `P(p ⊗ e^γ) ∈ span (lowerProd V0P n)`.

* `V0P_smul_quad` — the quadratic states `X(i,a)X(j,b) ⊗ e^0` are `θ`-even, so their products
  in `V₀⁺` are computed by `quadF` (via `thetaLat_mode`).
* `quadF_mem_Tsub` — every mode `m ≤ 0` of a quadratic state of weight `< n` on a charged
  state of weight `< n` (total weight `n`) lies in `Tsub`.
* `Fdw_le_of_ascent` — the induction on the total degree: if `Tsub` contains the weight-`w`
  states of degree `≤ d₀`, and each degree-`(D+1)` monomial `X v₁ X v₂ m'` lies in `Tsub` once all
  weight-`w` states of degree `≤ D` do, then `Tsub` contains the whole weight-`w` space.
* `step_quad` — that step, from `quadF_lead`, whenever `m' ⊗ e^γ` has positive weight.
* `quadD_X`, `quadN_X` — the weight-two modes `(h_ah_b)₍₀₎`, `(h_ah_b)₍₋₁₎` in normal form;
  `vanish_of_sym`.

## Status
`sorry`-free; no project axiom.  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.FockSpan

open VOA VOA.Moonshine VOA.Moonshine.SigmaExist VOA.Moonshine.ZhuGen LatGen IntegralLattice
  HeisenbergN MvPolynomial
open Submodule

/-! ## §1  Products with the quadratic states inside `V₀⁺` -/

/-- The Fock states `p` whose projected charge-`γ` state `P(p ⊗ e^γ)` is a combination of
weight-raising products of lower-weight states of `V₀⁺` (target weight `n`). -/
noncomputable def Tsub {γ : leech.carrier} (hγ : γ ∈ lambda0) (n : ℤ) : Submodule ℂ Fk :=
  (span ℂ (lowerProd V0P n)).comap (excitedV0 hγ)

theorem sigmaN_quad (i j : ℕ) (a b : Fin (rank leech)) :
    sigmaN (rank leech) (X (i, a) * X (j, b) : Fk) = X (i, a) * X (j, b) := by
  rw [sigmaN_mul, sigmaN_X, sigmaN_X, neg_mul_neg]

theorem thetaLat_quad (i j : ℕ) (a b : Fin (rank leech)) :
    thetaLat leech (latStateGen leech (X (i, a) * X (j, b) : Fk) 0)
      = latStateGen leech (X (i, a) * X (j, b) : Fk) 0 := by
  rw [thetaLat_latStateGen, sigmaN_quad, neg_zero]

theorem excitedV0_quad_coe (i j : ℕ) (a b : Fin (rank leech)) :
    (((excitedV0 lambda0.zero_mem (X (i, a) * X (j, b) : Fk) : V0Sub.carrier) : VPlus)
      : LatModuleGen leech) = latStateGen leech (X (i, a) * X (j, b) : Fk) 0 := by
  rw [excitedV0_coe, plusProj_coe, thetaLat_quad, ← two_smul ℂ, smul_smul]
  norm_num

/-- **Products with a quadratic state in `V₀⁺`**:
`P(h_a(-i-1)h_b(-j-1)𝟙)₍ₙ₎ P(p ⊗ e^γ) = P(quadF(-n-1)(p) ⊗ e^γ)`. -/
theorem V0P_smul_quad (i j : ℕ) (a b : Fin (rank leech)) {γ : leech.carrier} (hγ : γ ∈ lambda0)
    (n : ℤ) (p : Fk) :
    V0P.smul (excitedV0 lambda0.zero_mem (X (i, a) * X (j, b) : Fk)) n (excitedV0 hγ p)
      = excitedV0 hγ (quadF γ a i b j (-n - 1) p) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [V0P_smul_coe, plus_smul_coe, excitedV0_quad_coe, excitedV0_coe, excitedV0_coe,
    plusProj_coe, plusProj_coe, ← smul_quad, PreVertexAlgebra.smul_smul_right,
    PreVertexAlgebra.smul_add_right]
  congr 2
  have h := thetaLat_mode leech leech_even leech_posDef
    (latStateGen leech (X (i, a) * X (j, b) : Fk) 0) n (latStateGen leech p γ)
  rw [thetaLat_quad] at h
  exact h.symm

theorem excitedV0_mem_grading {γ : leech.carrier} (hγ : γ ∈ lambda0) {w : ℕ} {p : Fk}
    (hp : p ∈ gradingWN (rank leech) w) :
    excitedV0 hγ p ∈ V0P.grading ((w : ℤ) + LatGen.halfNorm leech γ) := by
  rw [mem_V0P_grading_iff, excitedV0_coe]
  exact plusProj_mem_grading (latStateGen_mem_grading hp γ)

theorem X_mul_X_mem_gradingWN (i j : ℕ) (a b : Fin (rank leech)) :
    (X (i, a) * X (j, b) : Fk) ∈ gradingWN (rank leech) (i + j + 2) := by
  have := wordStateN_mem_gradingWN [(i, a), (j, b)]
  simp only [wordStateN_cons, wordStateN_nil, mul_one, wordWt_cons, wordWt_nil] at this
  convert this using 2
  omega

/-- **The basic spanning step**: a mode `m ≤ 0` of a quadratic state on a lower-weight
charge-`γ` state lies in `Tsub`. -/
theorem quadF_mem_Tsub (i j : ℕ) (a b : Fin (rank leech)) {γ : leech.carrier} (hγ : γ ∈ lambda0)
    {n m : ℤ} (hm : m ≤ 0) {w : ℕ} {p : Fk} (hp : p ∈ gradingWN (rank leech) w)
    (h1 : (i : ℤ) + j + 2 < n) (h2 : (w : ℤ) + LatGen.halfNorm leech γ < n)
    (h3 : ((i : ℤ) + j + 2) + ((w : ℤ) + LatGen.halfNorm leech γ) - m - 1 = n) :
    quadF γ a i b j (-m - 1) p ∈ Tsub hγ n := by
  rw [Tsub, mem_comap, ← V0P_smul_quad]
  refine subset_span ⟨(i : ℤ) + j + 2, (w : ℤ) + LatGen.halfNorm leech γ, m, h1, h2, hm, h3, _,
    ?_, _, excitedV0_mem_grading hγ hp, rfl⟩
  have := excitedV0_mem_grading lambda0.zero_mem (X_mul_X_mem_gradingWN i j a b)
  rwa [SigmaExist.halfNorm_zero, add_zero, show ((i + j + 2 : ℕ) : ℤ) = (i : ℤ) + j + 2 by push_cast; ring]
    at this

/-! ## §2  Monomials, and the ascent in the total degree -/

/-- The Fock weight of an exponent vector. -/
noncomputable abbrev wt (s : (ℕ × Fin (rank leech)) →₀ ℕ) : ℕ := Finsupp.weight weightFnN s

theorem monomial_mem_gradingWN (s : (ℕ × Fin (rank leech)) →₀ ℕ) :
    (monomial s 1 : Fk) ∈ gradingWN (rank leech) (wt s) :=
  isWeightedHomogeneous_monomial _ _ _ rfl

theorem monomial_mem_Fdw (s : (ℕ × Fin (rank leech)) →₀ ℕ) :
    (monomial s 1 : Fk) ∈ Fdw s.degree (wt s) := by
  rw [mem_Fdw]
  refine ⟨(totalDegree_monomial_le _ _).trans ?_, mem_gradingZN_of_gradingWN (monomial_mem_gradingWN s)⟩
  rw [Finsupp.degree_apply, Finsupp.sum]
  rfl

theorem gradingZN_eq_bot_or {w : ℤ} {p : Fk} (hp : p ∈ gradingZN (rank leech) w) :
    p = 0 ∨ (0 ≤ w ∧ p ∈ gradingWN (rank leech) w.toNat) := by
  rcases lt_or_ge w 0 with hw | hw
  · rw [gradingZN_of_neg hw, mem_bot] at hp
    exact Or.inl hp
  · rw [gradingZN_of_nonneg hw] at hp
    exact Or.inr ⟨hw, hp⟩

theorem Fdw_le_span (D : ℕ) (w : ℤ) :
    Fdw D w ≤ span ℂ {q | ∃ s : (ℕ × Fin (rank leech)) →₀ ℕ, s.degree ≤ D ∧ (wt s : ℤ) = w ∧
      q = monomial s 1} := by
  intro p hp
  rw [mem_Fdw] at hp
  rcases gradingZN_eq_bot_or hp.2 with h0 | ⟨hw, hpw⟩
  · rw [h0]; exact zero_mem _
  rw [p.as_sum]
  refine sum_mem fun s hs => ?_
  have hdw : wt s = w.toNat := hpw (mem_support_iff.mp hs)
  rw [show (monomial s (coeff s p) : Fk) = coeff s p • monomial s 1 by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  refine smul_mem _ _ (subset_span ⟨s, ?_, by omega, rfl⟩)
  refine le_trans ?_ (hp.1)
  have := le_totalDegree hs
  rw [Finsupp.degree_apply]
  exact this

theorem exists_single_add {s : (ℕ × Fin (rank leech)) →₀ ℕ} (hs : 1 ≤ s.degree) :
    ∃ v s', s = Finsupp.single v 1 + s' := by
  have hne : s ≠ 0 := by
    rintro rfl
    simp at hs
  obtain ⟨v, hv⟩ := Finsupp.ne_iff.mp hne
  refine ⟨v, s - Finsupp.single v 1, ?_⟩
  ext u
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hv
    omega
  · omega

theorem wt_single_add (v : ℕ × Fin (rank leech)) (s : (ℕ × Fin (rank leech)) →₀ ℕ) :
    wt (Finsupp.single v 1 + s) = v.1 + 1 + wt s := by
  rw [wt, map_add, Finsupp.weight_single, one_smul, weightFnN_apply]

theorem degree_single_add (v : ℕ × Fin (rank leech)) (s : (ℕ × Fin (rank leech)) →₀ ℕ) :
    (Finsupp.single v 1 + s).degree = 1 + s.degree := by
  rw [map_add, Finsupp.degree_single]

theorem monomial_single_add_one (v : ℕ × Fin (rank leech)) (s : (ℕ × Fin (rank leech)) →₀ ℕ) :
    (monomial (Finsupp.single v 1 + s) 1 : Fk) = X v * monomial s 1 := by
  rw [monomial_single_add, pow_one]

/-- **The ascent in the total degree.**  If `T` contains all weight-`w` states of degree
`≤ d₀`, and every degree-`(D+1)` monomial `X v₁ X v₂ m'` is in `T` once all weight-`w` states of
degree `≤ D` are, then `T` contains every weight-`w` state. -/
theorem Fdw_le_of_ascent (T : Submodule ℂ Fk) (w : ℤ) (d0 : ℕ) (hd0 : 1 ≤ d0)
    (hbase : Fdw d0 w ≤ T)
    (hstep : ∀ D : ℕ, d0 ≤ D → Fdw D w ≤ T → ∀ (v1 v2 : ℕ × Fin (rank leech))
      (s' : (ℕ × Fin (rank leech)) →₀ ℕ), s'.degree + 1 = D →
      (v1.1 : ℤ) + v2.1 + 2 + (wt s' : ℤ) = w → (X v1 * X v2 * monomial s' 1 : Fk) ∈ T) :
    ∀ D, Fdw D w ≤ T := by
  intro D
  induction D with
  | zero => exact (Fdw_mono (by omega) w).trans hbase
  | succ D ih =>
    by_cases hD : D + 1 ≤ d0
    · exact (Fdw_mono hD w).trans hbase
    refine (Fdw_le_span (D + 1) w).trans (span_le.mpr ?_)
    rintro _ ⟨s, hsd, hsw, rfl⟩
    by_cases hle : s.degree ≤ D
    · have := monomial_mem_Fdw s
      rw [← hsw] at ih
      exact ih (Fdw_mono hle _ this)
    · obtain ⟨v1, s1, rfl⟩ := exists_single_add (s := s) (by omega)
      rw [degree_single_add] at hsd hle
      obtain ⟨v2, s', rfl⟩ := exists_single_add (s := s1) (by omega)
      rw [degree_single_add] at hsd hle
      rw [wt_single_add, wt_single_add] at hsw
      rw [SetLike.mem_coe, monomial_single_add_one, monomial_single_add_one, ← mul_assoc]
      exact hstep D (by omega) ih v1 v2 s' (by omega) (by push_cast at hsw ⊢; omega)

theorem gradingWN_le_of_Fdw {T : Submodule ℂ Fk} {w : ℕ} (h : ∀ D, Fdw D w ≤ T) :
    gradingWN (rank leech) w ≤ T := by
  intro p hp
  exact h p.totalDegree (by rw [mem_Fdw]; exact ⟨le_rfl, mem_gradingZN_of_gradingWN hp⟩)

/-- **The quadratic step**: `X v₁ X v₂ m' ∈ Tsub` once every state of degree `≤ deg m' + 1`
and the same weight is, provided the source `m' ⊗ e^γ` has positive weight. -/
theorem step_quad {γ : leech.carrier} (hγ : γ ∈ lambda0) (n : ℤ) (D : ℕ) (w : ℕ)
    (hn : n = (w : ℤ) + LatGen.halfNorm leech γ)
    (IH : Fdw D w ≤ Tsub hγ n) (v1 v2 : ℕ × Fin (rank leech)) (s' : (ℕ × Fin (rank leech)) →₀ ℕ)
    (hdeg : s'.degree + 1 = D) (hw : (v1.1 : ℤ) + v2.1 + 2 + (wt s' : ℤ) = w)
    (hpos : 1 ≤ (wt s' : ℤ) + LatGen.halfNorm leech γ) :
    (X v1 * X v2 * monomial s' 1 : Fk) ∈ Tsub hγ n := by
  have hp := monomial_mem_Fdw s'
  have hlead := quadF_lead γ v1.2 v1.1 v2.2 v2.1 hp
  have hmem := quadF_mem_Tsub v1.1 v2.1 v1.2 v2.2 hγ (m := -1) (n := n) (by norm_num)
    (monomial_mem_gradingWN s') (by omega) (by omega) (by omega)
  rw [show -(-1 : ℤ) - 1 = 0 by norm_num] at hmem
  have hR : quadF γ v1.2 v1.1 v2.2 v2.1 0 (monomial s' 1) - X (v1.1, v1.2) * X (v2.1, v2.2) *
      monomial s' 1 ∈ Tsub hγ n := by
    apply IH
    rw [← hdeg]
    convert hlead using 2
    omega
  have := sub_mem hmem hR
  rwa [sub_sub_cancel] at this

/-! ## §3  The weight-two quadratic modes in normal form -/

/-- `[(h_ah_b)₍₀₎, X(t,c)] = (t+1)(δ_{cb} X(t+1,a) + δ_{ca} X(t+1,b))`. -/
theorem quadD_X (γ : leech.carrier) (a b : Fin (rank leech)) (t : ℕ) (c : Fin (rank leech))
    (p : Fk) :
    quadF γ a 0 b 0 (-1) (X (t, c) * p) = X (t, c) * quadF γ a 0 b 0 (-1) p
      + (if c = b then ((t : ℂ) + 1) • (X (t + 1, a) * p) else 0)
      + (if c = a then ((t : ℂ) + 1) • (X (t + 1, b) * p) else 0) := by
  rw [quadF_X_mul γ a b (by norm_num) t c p]
  simp only [show ((t : ℤ) + -1 + 2).toNat = t + 1 by omega]

/-- `[(h_ah_b)₍₋₁₎, X(t,c)] = (t+1)(δ_{cb} X(t+2,a) + δ_{ca} X(t+2,b))`. -/
theorem quadN_X (γ : leech.carrier) (a b : Fin (rank leech)) (t : ℕ) (c : Fin (rank leech))
    (p : Fk) :
    quadF γ a 0 b 0 0 (X (t, c) * p) = X (t, c) * quadF γ a 0 b 0 0 p
      + (if c = b then ((t : ℂ) + 1) • (X (t + 2, a) * p) else 0)
      + (if c = a then ((t : ℂ) + 1) • (X (t + 2, b) * p) else 0) := by
  rw [quadF_X_mul γ a b (by norm_num) t c p]
  simp only [show ((t : ℤ) + 0 + 2).toNat = t + 2 by omega]

theorem X_mem_gradingWN (v : ℕ × Fin (rank leech)) :
    (X v : Fk) ∈ gradingWN (rank leech) (v.1 + 1) := by
  have := isWeightedHomogeneous_X ℂ (weightFnN (r := rank leech)) v
  rwa [weightFnN_apply] at this

theorem one_mem_gradingWN : (1 : Fk) ∈ gradingWN (rank leech) 0 :=
  isWeightedHomogeneous_one ℂ weightFnN

/-- If `g_b φ_a + g_a φ_b = 0` for all `a, b` and some `g_b ≠ 0`, all `φ_a` vanish. -/
theorem vanish_of_sym {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*} (g : ι → ℂ)
    (φ : ι → M) (hS : ∀ a b, g b • φ a + g a • φ b = 0) (hg : ∃ b, g b ≠ 0) : ∀ a, φ a = 0 := by
  obtain ⟨b, hb⟩ := hg
  have hφb : φ b = 0 := by
    have h := hS b b
    rw [← two_smul ℂ, smul_smul] at h
    rcases smul_eq_zero.mp h with h0 | h0
    · exact absurd h0 (mul_ne_zero two_ne_zero hb)
    · exact h0
  intro a
  have h := hS a b
  rw [hφb, smul_zero, add_zero] at h
  rcases smul_eq_zero.mp h with h0 | h0
  · exact absurd h0 hb
  · exact h0

end VOA.Moonshine.FockSpan
