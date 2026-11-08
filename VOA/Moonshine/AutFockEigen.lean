/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergNVertex

/-!
# The quadratic Fock operators `N_ab` and their joint eigenvectors
(Aut(V♮) campaign, step 3, route C, node C3 of `Notes/MONSTER_AUT_PLAN.md`)

On the rank-`r` Fock space `FockN r = ℂ[X_{(k,a)}]` (`X_{(k,a)} ↔ h_a(−k−1)`), the zero mode of
`q_ab = h_a(−1)h_b(−1)𝟙` is, up to the momentum term, the operator

  `N_ab = nprod (α^a) (α^b) (−2) = Σ_{k ≥ 0} (k+1) (X_{(k,a)} ∂_{(k,b)} + X_{(k,b)} ∂_{(k,a)})`.

## Main results
* ⭐ `nprod_currentN_neg_two` — the closed form above, as a finite sum over any level bound `K`
  for the variables of the argument.
-/

set_option linter.style.longLine false

namespace VOA.HeisenbergN

open MvPolynomial

variable {r : ℕ}

/-- ⭐ **The Fock operator `N_ab` in closed form**: for `q` whose variables all have level `< K`,
`nprod (α^a) (α^b) (−2) q = Σ_{k<K} (k+1)(X_{(k,a)} ∂_{(k,b)} q + X_{(k,b)} ∂_{(k,a)} q)`. -/
theorem nprod_currentN_neg_two (a b : Fin r) (q : FockN r) (K : ℕ)
    (hK : ∀ v ∈ q.vars, v.1 < K) :
    nprod (currentN_isField r 1 a) (currentN_isField r 1 b) (-2) q
      = ∑ k ∈ Finset.range K, ((k : ℂ) + 1) •
          (X (k, a) * pderiv (k, b) q + X (k, b) * pderiv (k, a) q) := by
  classical
  rw [nprod_apply]
  set f : ℤ → FockN r := fun m => normalOrdered (currentN r 1 a) (currentN r 1 b) m (-2 - m) q
    with hf
  -- the creation-left terms `m = k ≥ 0`
  have hpos : ∀ k : ℕ, f (k : ℤ) = ((k : ℂ) + 1) • (X (k, a) * pderiv (k, b) q) := by
    intro k
    rw [hf]
    simp only
    rw [normalOrdered_apply, if_pos (by positivity), Module.End.mul_apply, currentN_apply,
      currentN_apply, oscN_apply_pos r 1 b (show (0 : ℤ) < -(-2 - (k : ℤ)) - 1 by omega),
      oscN_apply_neg r 1 a (show -(k : ℤ) - 1 < 0 by omega),
      show (-(-(k : ℤ) - 1) - 1).toNat = k by omega,
      show (-(-2 - (k : ℤ)) - 1 - 1).toNat = k by omega, one_smul, mul_smul_comm]
    congr 1
    push_cast
    ring
  -- the creation-right terms `m = −k−2`
  have hneg : ∀ k : ℕ, f (-(k : ℤ) - 2) = ((k : ℂ) + 1) • (X (k, b) * pderiv (k, a) q) := by
    intro k
    rw [hf]
    simp only
    rw [normalOrdered_apply, if_neg (by omega), Module.End.mul_apply, currentN_apply,
      currentN_apply, oscN_apply_pos r 1 a (show (0 : ℤ) < -(-(k : ℤ) - 2) - 1 by omega),
      oscN_apply_neg r 1 b (show -(-2 - (-(k : ℤ) - 2)) - 1 < 0 by omega),
      show (-(-(-2 - (-(k : ℤ) - 2)) - 1) - 1).toNat = k by omega,
      show (-(-(k : ℤ) - 2) - 1 - 1).toNat = k by omega, one_smul, mul_smul_comm]
    congr 1
    push_cast
    ring
  -- the middle term `m = −1` vanishes (Fock zero mode)
  have hm1 : f (-1) = 0 := by
    rw [hf]
    simp only
    have h0 : currentN r 1 a (-1) = 0 := by
      rw [currentN_apply, show -(-1 : ℤ) - 1 = 0 by ring, oscN_zero]
    rw [normalOrdered_apply, if_neg (by norm_num), Module.End.mul_apply, h0,
      LinearMap.zero_apply, map_zero]
  -- levels `≥ K` do not occur
  have hpd : ∀ (k : ℕ) (c : Fin r), K ≤ k → pderiv (k, c) q = 0 := fun k c hk =>
    pderiv_eq_zero_of_notMem_vars fun hv => absurd (hK _ hv) (by simp only; omega)
  let eP : ℕ ↪ ℤ := ⟨fun k => (k : ℤ), fun x y h => by simpa using h⟩
  let eN : ℕ ↪ ℤ := ⟨fun k => -(k : ℤ) - 2, fun x y h => by simp only at h; omega⟩
  have hdisj : Disjoint ((Finset.range K).map eP) ((Finset.range K).map eN) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    simp only [Finset.mem_map, Finset.mem_range, eP, eN, Function.Embedding.coeFn_mk] at hm hm'
    obtain ⟨x, -, rfl⟩ := hm
    obtain ⟨y, -, hy⟩ := hm'
    omega
  have hsupp : Function.support f ⊆ ↑((Finset.range K).map eP ∪ (Finset.range K).map eN) := by
    intro m hm
    rw [Function.mem_support] at hm
    simp only [Finset.coe_union, Finset.coe_map, Set.mem_union, Set.mem_image, Finset.mem_coe,
      Finset.mem_range, eP, eN, Function.Embedding.coeFn_mk]
    rcases lt_trichotomy m (-1) with hlt | heq | hgt
    · refine Or.inr ⟨(-m - 2).toNat, ?_, by omega⟩
      by_contra hk
      apply hm
      have hm' : m = -(((-m - 2).toNat : ℕ) : ℤ) - 2 := by omega
      rw [hm', hneg, hpd _ _ (by omega), mul_zero, smul_zero]
    · exact absurd (heq ▸ hm1) hm
    · refine Or.inl ⟨m.toNat, ?_, by omega⟩
      by_contra hk
      apply hm
      have hm' : m = ((m.toNat : ℕ) : ℤ) := by omega
      rw [hm', hpos, hpd _ _ (by omega), mul_zero, smul_zero]
  rw [finsum_eq_sum_of_support_subset f hsupp, Finset.sum_union hdisj, Finset.sum_map,
    Finset.sum_map, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [eP, eN, Function.Embedding.coeFn_mk]
  rw [hpos, hneg, smul_add]

/-! ## Coefficients of `X_u ∂_v p` -/

section Coeff

variable {σ : Type*} [DecidableEq σ]

/-- `coeff_s (∂_i p) = (s_i + 1) · coeff_{s + e_i} p`. -/
theorem coeff_pderiv (i : σ) (s : σ →₀ ℕ) (p : MvPolynomial σ ℂ) :
    coeff s (pderiv i p) = ((s i : ℂ) + 1) * coeff (s + Finsupp.single i 1) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial t a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases ht : t i = 0
    · have h1 : t - Finsupp.single i 1 = t := by
        ext j
        by_cases hj : j = i
        · subst hj; simp [ht]
        · simp [Finsupp.single_apply, Ne.symm hj]
      have h2 : t ≠ s + Finsupp.single i 1 := fun h => by
        have := congrArg (fun f : σ →₀ ℕ => f i) h
        simp [ht] at this
      rw [h1, if_neg h2, ht]
      split_ifs <;> simp
    · have hiff : t - Finsupp.single i 1 = s ↔ t = s + Finsupp.single i 1 := by
        constructor
        · rintro rfl
          ext j
          by_cases hj : j = i
          · subst hj; simp; omega
          · simp [Finsupp.single_apply, Ne.symm hj]
        · rintro rfl
          ext j
          simp
      by_cases hs : t = s + Finsupp.single i 1
      · rw [if_pos (hiff.2 hs), if_pos hs, hs]
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast
        ring
      · rw [if_neg (fun h => hs (hiff.1 h)), if_neg hs, mul_zero]
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/-- `coeff_s (X_u · ∂_v p)` for `u ≠ v`: a transfer of one quantum from `v` to `u`. -/
theorem coeff_X_mul_pderiv_ne {u v : σ} (huv : u ≠ v) (s : σ →₀ ℕ) (p : MvPolynomial σ ℂ) :
    coeff s (X u * pderiv v p)
      = if s u = 0 then 0
        else ((s v : ℂ) + 1) * coeff (s - Finsupp.single u 1 + Finsupp.single v 1) p := by
  rw [coeff_X_mul', coeff_pderiv]
  by_cases hs : s u = 0
  · rw [if_neg (by simpa [Finsupp.mem_support_iff] using hs), if_pos hs]
  · rw [if_pos (by simpa [Finsupp.mem_support_iff] using hs), if_neg hs]
    simp [Finsupp.single_apply, huv]

/-- `coeff_s (X_v · ∂_v p) = s_v · coeff_s p` (the Euler identity in one variable). -/
theorem coeff_X_mul_pderiv_self (v : σ) (s : σ →₀ ℕ) (p : MvPolynomial σ ℂ) :
    coeff s (X v * pderiv v p) = (s v : ℂ) * coeff s p := by
  rw [coeff_X_mul', coeff_pderiv]
  by_cases hs : s v = 0
  · rw [if_neg (by simpa [Finsupp.mem_support_iff] using hs), hs, Nat.cast_zero, zero_mul]
  · rw [if_pos (by simpa [Finsupp.mem_support_iff] using hs), tsub_add_cancel_of_le
      (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hs))]
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    congr 1
    push_cast [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hs)]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hs)]
    ring

end Coeff

/-! ## The joint-eigenvector lemma

`quadOp μ K a b` is the quadratic Fock operator with level weights `μ` (`μ k = k + 1` gives `N_ab`
by `nprod_currentN_neg_two`; `μ k = k + ½` is the twisted analogue).  A joint eigenvector of all
`quadOp μ K a b` (rank `≥ 2`) is a constant polynomial with all eigenvalues `0`. -/

section FockLemma

open Finsupp

/-- The quadratic Fock operator with level weights `μ` and level bound `K`. -/
noncomputable def quadOp (μ : ℕ → ℂ) (K : ℕ) (a b : Fin r) (q : FockN r) : FockN r :=
  ∑ k ∈ Finset.range K, μ k • (X (k, a) * pderiv (k, b) q + X (k, b) * pderiv (k, a) q)

/-- The `μ`-weighted level content of a monomial in direction `a`. -/
noncomputable def lvlWt (μ : ℕ → ℂ) (K : ℕ) (a : Fin r) (s : (ℕ × Fin r) →₀ ℕ) : ℂ :=
  ∑ k ∈ Finset.range K, μ k * (s (k, a) : ℂ)

theorem nprod_currentN_neg_two_eq_quadOp (a b : Fin r) (q : FockN r) (K : ℕ)
    (hK : ∀ v ∈ q.vars, v.1 < K) :
    nprod (currentN_isField r 1 a) (currentN_isField r 1 b) (-2) q
      = quadOp (fun k => (k : ℂ) + 1) K a b q :=
  nprod_currentN_neg_two a b q K hK

/-- Moving one quantum from `u` to `v`: the exponent at `w`, cast to `ℂ`. -/
theorem cast_shift_apply (s : (ℕ × Fin r) →₀ ℕ) (u v w : ℕ × Fin r) (hu : s u ≠ 0) :
    (((s - Finsupp.single u 1 + Finsupp.single v 1 : (ℕ × Fin r) →₀ ℕ) w : ℕ) : ℂ)
      = (s w : ℂ) - (if u = w then 1 else 0) + (if v = w then 1 else 0) := by
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  by_cases h1 : u = w
  · subst h1
    have h1' : 1 ≤ s u := Nat.one_le_iff_ne_zero.mpr hu
    rw [if_pos rfl, if_pos rfl]
    push_cast [Nat.cast_add, Nat.cast_sub h1']
    split_ifs <;> simp
  · rw [if_neg h1, if_neg h1, Nat.sub_zero]
    push_cast
    split_ifs <;> simp

theorem sum_mul_indicator (μ : ℕ → ℂ) (K : ℕ) (a : Fin r) (u : ℕ × Fin r) :
    ∑ k ∈ Finset.range K, μ k * (if u = (k, a) then (1 : ℂ) else 0)
      = if u.2 = a ∧ u.1 < K then μ u.1 else 0 := by
  obtain ⟨j, c⟩ := u
  simp only [Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  by_cases hc : c = a
  · subst hc
    simp only [and_true, true_and]
    simp only [Finset.sum_ite_eq, Finset.mem_range]
  · simp [hc]

/-- How `lvlWt` changes when one quantum moves from `u` to `v`. -/
theorem lvlWt_shift (μ : ℕ → ℂ) (K : ℕ) (a : Fin r) (s : (ℕ × Fin r) →₀ ℕ)
    (u v : ℕ × Fin r) (hu : s u ≠ 0) :
    lvlWt μ K a (s - Finsupp.single u 1 + Finsupp.single v 1)
      = lvlWt μ K a s - (if u.2 = a ∧ u.1 < K then μ u.1 else 0)
        + (if v.2 = a ∧ v.1 < K then μ v.1 else 0) := by
  unfold lvlWt
  rw [Finset.sum_congr rfl fun k _ => by rw [cast_shift_apply s u v (k, a) hu]]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_mul_indicator, sum_mul_indicator]

/-- The diagonal operator scales each monomial by twice its level weight. -/
theorem coeff_quadOp_self (μ : ℕ → ℂ) (K : ℕ) (a : Fin r) (q : FockN r)
    (s : (ℕ × Fin r) →₀ ℕ) :
    coeff s (quadOp μ K a a q) = 2 * lvlWt μ K a s * coeff s q := by
  unfold quadOp lvlWt
  rw [coeff_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_smul, coeff_add, coeff_X_mul_pderiv_self, smul_eq_mul]
  ring

/-- The off-diagonal operator in coefficients (`a ≠ b`). -/
theorem coeff_quadOp_ne (μ : ℕ → ℂ) (K : ℕ) {a b : Fin r} (hab : a ≠ b) (q : FockN r)
    (s : (ℕ × Fin r) →₀ ℕ) :
    coeff s (quadOp μ K a b q)
      = ∑ k ∈ Finset.range K, μ k *
          ((if s (k, a) = 0 then 0
            else ((s (k, b) : ℂ) + 1) * coeff (s - Finsupp.single (k, a) 1 + Finsupp.single (k, b) 1) q)
          + (if s (k, b) = 0 then 0
            else ((s (k, a) : ℂ) + 1) * coeff (s - Finsupp.single (k, b) 1 + Finsupp.single (k, a) 1) q)) := by
  unfold quadOp
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ((k, a) : ℕ × Fin r) ≠ (k, b) := fun h => hab (Prod.mk.inj h).2
  rw [coeff_smul, coeff_add, coeff_X_mul_pderiv_ne h1, coeff_X_mul_pderiv_ne h1.symm,
    smul_eq_mul]

/-- ⭐ **The joint-eigenvector lemma.**  If `q ≠ 0` is an eigenvector of every `quadOp μ K a b`
(levels of `q` below `K`, rank with two distinct directions, `μ` injective with `μ k + μ k' ≠ 0`),
then `q` is constant and every eigenvalue vanishes. -/
theorem quadOp_joint_eigen (μ : ℕ → ℂ) (hsum : ∀ k k', μ k + μ k' ≠ 0)
    (hinj : ∀ k k', μ k = μ k' → k = k') (hr : ∀ b : Fin r, ∃ a, a ≠ b) (K : ℕ)
    (q : FockN r) (hK : ∀ v ∈ q.vars, v.1 < K) (c : Fin r → Fin r → ℂ)
    (h : ∀ a b, quadOp μ K a b q = c a b • q) (hq : q ≠ 0) :
    (∀ a b, c a b = 0) ∧ q = MvPolynomial.C (coeff 0 q) := by
  classical
  have hμ0 : ∀ k, μ k ≠ 0 := fun k h0 => hsum k k (by rw [h0, add_zero])
  -- diagonal: every monomial of `q` has `2·lvlWt a = c a a`
  have hD : ∀ a s, coeff s q ≠ 0 → 2 * lvlWt μ K a s = c a a := by
    intro a s hs
    have := congrArg (coeff s) (h a a)
    rw [coeff_quadOp_self, coeff_smul, smul_eq_mul] at this
    exact mul_right_cancel₀ hs this
  -- monomials of `q` share the level weight of any fixed monomial of `q`
  have hsame : ∀ a s t, coeff s q ≠ 0 → lvlWt μ K a t ≠ lvlWt μ K a s → coeff t q = 0 := by
    intro a s t hs hne
    by_contra ht
    exact hne (by have h1 := hD a t ht; have h2 := hD a s hs
                  exact mul_left_cancel₀ two_ne_zero (h1.trans h2.symm))
  -- levels of monomials of `q` are below `K`
  have hlev : ∀ s, coeff s q ≠ 0 → ∀ v, s v ≠ 0 → v.1 < K := by
    intro s hs v hv
    exact hK v ((mem_vars v).2 ⟨s, MvPolynomial.mem_support_iff.2 hs, Finsupp.mem_support_iff.2 hv⟩)
  obtain ⟨s₀, hs₀⟩ := ne_zero_iff.1 hq
  -- off-diagonal eigenvalues vanish
  have hO : ∀ a b, a ≠ b → c a b = 0 := by
    intro a b hab
    have hc := congrArg (coeff s₀) (h a b)
    rw [coeff_quadOp_ne μ K hab, coeff_smul, smul_eq_mul] at hc
    have hz : ∀ k ∈ Finset.range K, μ k *
        ((if s₀ (k, a) = 0 then 0
          else ((s₀ (k, b) : ℂ) + 1) * coeff (s₀ - Finsupp.single (k, a) 1 + Finsupp.single (k, b) 1) q)
        + (if s₀ (k, b) = 0 then 0
          else ((s₀ (k, a) : ℂ) + 1) * coeff (s₀ - Finsupp.single (k, b) 1 + Finsupp.single (k, a) 1) q)) = 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hA : (if s₀ (k, a) = 0 then 0
          else ((s₀ (k, b) : ℂ) + 1) * coeff (s₀ - Finsupp.single (k, a) 1 + Finsupp.single (k, b) 1) q) = 0 := by
        split_ifs with h0
        · rfl
        · rw [hsame a s₀ _ hs₀ ?_, mul_zero]
          rw [lvlWt_shift μ K a s₀ _ _ h0, if_pos ⟨rfl, hk⟩, if_neg (by simp [Ne.symm hab])]
          intro he
          exact hμ0 k (by linear_combination -he)
      have hB : (if s₀ (k, b) = 0 then 0
          else ((s₀ (k, a) : ℂ) + 1) * coeff (s₀ - Finsupp.single (k, b) 1 + Finsupp.single (k, a) 1) q) = 0 := by
        split_ifs with h0
        · rfl
        · rw [hsame a s₀ _ hs₀ ?_, mul_zero]
          rw [lvlWt_shift μ K a s₀ _ _ h0, if_neg (by simp [Ne.symm hab]), if_pos ⟨rfl, hk⟩]
          intro he
          exact hμ0 k (by linear_combination he)
      rw [hA, hB, add_zero, mul_zero]
    rw [Finset.sum_eq_zero hz] at hc
    exact (mul_eq_zero.1 hc.symm).resolve_right hs₀
  have hZ : ∀ a b, a ≠ b → quadOp μ K a b q = 0 := fun a b hab => by
    rw [h a b, hO a b hab, zero_smul]
  -- no monomial of `q` contains a variable
  have hV : ∀ s, coeff s q ≠ 0 → s = 0 := by
    intro s hs
    by_contra hne
    obtain ⟨⟨k, b⟩, hkb⟩ : ∃ v, s v ≠ 0 := by
      by_contra hall
      exact hne (Finsupp.ext fun v => by
        by_contra hv
        exact hall ⟨v, hv⟩)
    have hk : k < K := hlev s hs (k, b) hkb
    obtain ⟨a, hab⟩ := hr b
    set t := s - Finsupp.single (k, b) 1 + Finsupp.single (k, a) 1 with ht
    have htw : lvlWt μ K a t = lvlWt μ K a s + μ k := by
      rw [ht, lvlWt_shift μ K a s _ _ hkb, if_neg (by simp [Ne.symm hab]), if_pos ⟨rfl, hk⟩,
        sub_zero]
    have hta : t (k, a) ≠ 0 := by
      rw [ht]; simp [hab]
    have htb : ((t (k, b) : ℕ) : ℂ) + 1 = (s (k, b) : ℂ) := by
      rw [ht, cast_shift_apply s _ _ _ hkb, if_pos rfl, if_neg (by simp [hab])]
      ring
    have hback : t - Finsupp.single (k, a) 1 + Finsupp.single (k, b) 1 = s := by
      rw [ht]
      ext w
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      by_cases h1 : (k, b) = w
      · subst h1
        rw [if_pos rfl, if_neg (by simp [hab])]
        have : 1 ≤ s (k, b) := Nat.one_le_iff_ne_zero.mpr hkb
        simp only [Nat.sub_zero, add_zero]; omega
      · rw [if_neg h1]
        by_cases h2 : (k, a) = w
        · subst h2; rw [if_pos rfl]; omega
        · rw [if_neg h2]; omega
    have hc := congrArg (coeff t) (hZ a b hab)
    rw [coeff_quadOp_ne μ K hab, coeff_zero] at hc
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.2 hk)] at hc
    · -- the `k`-term equals `μ_k · s(k,b) · coeff_s q ≠ 0`
      rw [if_neg hta, hback, htb] at hc
      have hB : (if t (k, b) = 0 then 0
          else ((t (k, a) : ℂ) + 1) * coeff (t - Finsupp.single (k, b) 1 + Finsupp.single (k, a) 1) q) = 0 := by
        split_ifs with h0
        · rfl
        · rw [hsame a s _ hs ?_, mul_zero]
          rw [lvlWt_shift μ K a t _ _ h0, if_neg (by simp [Ne.symm hab]), if_pos ⟨rfl, hk⟩, htw]
          intro he
          exact hsum k k (by linear_combination he)
      rw [hB, add_zero] at hc
      have hsk : (s (k, b) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hkb
      exact (mul_ne_zero (hμ0 k) (mul_ne_zero hsk hs)) hc
    · -- all other levels contribute zero
      intro k' hk' hkk'
      rw [Finset.mem_range] at hk'
      have hA : (if t (k', a) = 0 then 0
          else ((t (k', b) : ℂ) + 1) * coeff (t - Finsupp.single (k', a) 1 + Finsupp.single (k', b) 1) q) = 0 := by
        split_ifs with h0
        · rfl
        · rw [hsame a s _ hs ?_, mul_zero]
          rw [lvlWt_shift μ K a t _ _ h0, if_pos ⟨rfl, hk'⟩, if_neg (by simp [Ne.symm hab]), htw]
          intro he
          exact hkk' (hinj _ _ (by linear_combination he)).symm
      have hB : (if t (k', b) = 0 then 0
          else ((t (k', a) : ℂ) + 1) * coeff (t - Finsupp.single (k', b) 1 + Finsupp.single (k', a) 1) q) = 0 := by
        split_ifs with h0
        · rfl
        · rw [hsame a s _ hs ?_, mul_zero]
          rw [lvlWt_shift μ K a t _ _ h0, if_neg (by simp [Ne.symm hab]), if_pos ⟨rfl, hk'⟩, htw]
          intro he
          exact hsum k k' (by linear_combination he)
      rw [hA, hB, add_zero, mul_zero]
  -- conclusion
  have hconst : q = MvPolynomial.C (coeff 0 q) := by
    ext s
    rw [coeff_C]
    by_cases hs : s = 0
    · rw [if_pos hs.symm, hs]
    · rw [if_neg (Ne.symm hs)]
      by_contra hne
      exact hs (hV s hne)
  refine ⟨fun a b => ?_, hconst⟩
  by_cases hab : a = b
  · subst hab
    have h0 : coeff 0 q ≠ 0 := by
      intro h0; apply hq; rw [hconst, h0, MvPolynomial.C_0]
    have := hD a 0 h0
    rw [← this]
    simp [lvlWt]
  · exact hO a b hab

end FockLemma

end VOA.HeisenbergN
