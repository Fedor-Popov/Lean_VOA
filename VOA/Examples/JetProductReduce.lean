/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.JetProductModes
import VOA.Examples.JetProductLocal

/-!
# Reduction of the jet-side coefficients to local products

Fix `r`, a charge `k ≤ 2r`, and `l = 2r - k`.  For a multiset `λ` of `k` indices `≤ l` let
`m_λ = u_λ v_0^l` be the corresponding jet monomial.  The coefficient of `m_λ` in a product
`P_{w,a}` of `r` generator coefficients only sees the variables `u_0, …, u_l, v_0`; killing all
other variables (`rho l`) turns the generator series into

  `X ↦ ũ(s)²`, `Y ↦ ũ(s) v_0`, `Z ↦ v_0²`, `J ↦ ũ'(s) v_0`,   `ũ(s) = Σ_{j ≤ l} u_j s^j`.

* `coeff_mono_Pga` — the coefficient of `m_λ` in `P_{w,a}` is the coefficient of `u_λ` in
  `∏_i ell_{w_i, a_i}` (and zero unless the `v`-count of `w` is `l`);
* `Apol λ w` — the generating polynomial `Σ_a [m_λ] P_{w,a} t^a`, with
  `↑(Apol λ w) = Gam (lcoeff m_λ) w` (`coe_Apol`);
* `eval_Apol` — at a point `t`, `Apol λ w` evaluates to the coefficient of `u_λ` in the
  product of local forms `∏_i loc_{w_i}(t_i)` of `JetProductLocal`.

Everything is proved outright.
-/

namespace VOA.JetProduct

open MvPolynomial VOA.SymbolModel
open scoped BigOperators

noncomputable section

/-! ### Killing the variables outside `u_0, …, u_l, v_0` -/

/-- The `u`-index embedding `j ↦ u_j`. -/
def uIdx (j : ℕ) : Fin 2 × ℕ := (0, j)

theorem uIdx_injective : Function.Injective uIdx := fun _ _ h => (Prod.mk.inj h).2

/-- The kept variables. -/
def keep (l : ℕ) (x : Fin 2 × ℕ) : Prop := (x.1 = 0 ∧ x.2 ≤ l) ∨ x = (1, 0)

instance (l : ℕ) : DecidablePred (keep l) := fun x => by unfold keep; infer_instance

/-- Kill every variable except `u_0, …, u_l, v_0`. -/
def rho (l : ℕ) : JetPoly →ₐ[ℂ] JetPoly := aeval fun x => if keep l x then X x else 0

theorem rho_monomial (l : ℕ) (n : Fin 2 × ℕ →₀ ℕ) (c : ℂ) :
    rho l (monomial n c) = if (∀ x ∈ n.support, keep l x) then monomial n c else 0 := by
  rw [rho, aeval_monomial, monomial_eq]
  split_ifs with h
  · congr 1
    apply Finset.prod_congr rfl
    intro x hx
    simp only [if_pos (h x hx)]
  · push Not at h
    obtain ⟨x, hx, hk⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero hx, mul_zero]
    rw [if_neg hk, zero_pow (Finsupp.mem_support_iff.mp hx)]

/-- Coefficients of monomials in the kept variables are unchanged by `rho`. -/
theorem coeff_rho (l : ℕ) (m : Fin 2 × ℕ →₀ ℕ) (hm : ∀ x ∈ m.support, keep l x) (Q : JetPoly) :
    coeff m (rho l Q) = coeff m Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [rho_monomial]
    split_ifs with h
    · rfl
    · rw [coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact h hm
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq]

/-! ### The truncated column `ũ(s)` -/

/-- `ũ(s) = Σ_{j ≤ l} u_j s^j` as a polynomial with coefficients in `ℂ[u_j]`. -/
def uq (l : ℕ) : Polynomial UPoly :=
  ∑ j ∈ Finset.range (l + 1), Polynomial.monomial j (X j)

theorem coeff_uq (l j : ℕ) : (uq l).coeff j = if j ≤ l then X j else 0 := by
  rw [uq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases h : j ≤ l
  · rw [Finset.sum_eq_single j]
    · simp [h]
    · intro b _ hb; simp [hb]
    · intro hj; exact absurd (Finset.mem_range.mpr (by omega)) hj
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    have : b ≠ j := by have := Finset.mem_range.mp hb; omega
    simp [this]

/-- The reduced generator series. -/
def ellP (l : ℕ) (g : Fin 4) : Polynomial UPoly :=
  ![uq l ^ 2, uq l, 1, Polynomial.derivative (uq l)] g

/-- The number of `v`'s in a generator. -/
def vcount (g : Fin 4) : ℕ := ![0, 1, 2, 1] g

theorem rho_u (l j : ℕ) : rho l (X (0, j)) = rename uIdx ((uq l).coeff j) := by
  rw [coeff_uq, rho, aeval_X]
  by_cases h : j ≤ l
  · have hk : keep l (0, j) := Or.inl ⟨rfl, h⟩
    rw [if_pos hk, if_pos h, rename_X]; rfl
  · have hk : ¬ keep l (0, j) := by
      rintro (⟨-, h'⟩ | h')
      · exact h h'
      · simp at h'
    rw [if_neg hk, if_neg h, map_zero]

theorem rho_v (l j : ℕ) : rho l (X (1, j)) = if j = 0 then X (1, 0) else 0 := by
  rw [rho, aeval_X]
  by_cases h : j = 0
  · subst h
    have hk : keep l (1, 0) := Or.inr rfl
    rw [if_pos hk, if_pos rfl]
  · have hk : ¬ keep l (1, j) := by
      rintro (⟨h', -⟩ | h')
      · simp at h'
      · exact h (congrArg Prod.snd h')
    rw [if_neg hk, if_neg h]

theorem coeff_colSer (b : Fin 2) (j : ℕ) : PowerSeries.coeff j (colSer b) = X (b, j) := by
  rw [colSer, PowerSeries.coeff_mk]

theorem rho_genCoeff (l : ℕ) (g : Fin 4) (a : ℕ) :
    rho l (genCoeff g a) = X (1, 0) ^ vcount g * rename uIdx ((ellP l g).coeff a) := by
  fin_cases g
  · change rho l (PowerSeries.coeff a (colSer 0 * colSer 0)) = _
    simp only [vcount, ellP, Fin.zero_eta, Matrix.cons_val_zero, pow_zero, one_mul, sq,
      PowerSeries.coeff_mul, Polynomial.coeff_mul, map_sum, map_mul, coeff_colSer, rho_u]
  · change rho l (PowerSeries.coeff a (colSer 0 * colSer 1)) = _
    simp only [vcount, ellP, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, pow_one,
      PowerSeries.coeff_mul, map_sum, map_mul, coeff_colSer, rho_u, rho_v]
    rw [Finset.sum_eq_single (a, 0)]
    · simp [mul_comm]
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have : p.2 ≠ 0 := fun h => hne (Prod.ext (by omega) h)
      simp [this]
    · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h
  · change rho l (PowerSeries.coeff a (colSer 1 * colSer 1)) = _
    simp only [vcount, ellP, Fin.reduceFinMk, Matrix.cons_val, Polynomial.coeff_one,
      PowerSeries.coeff_mul, map_sum, map_mul, coeff_colSer, rho_v]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [sq]
    · rw [if_neg (by omega), map_zero, mul_zero]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      by_cases h1 : p.1 = 0
      · have : p.2 ≠ 0 := by omega
        simp [this]
      · simp [h1]
  · change rho l (PowerSeries.coeff a (dS (colSer 0) * colSer 1 - colSer 0 * dS (colSer 1))) = _
    simp only [vcount, ellP, Fin.reduceFinMk, Matrix.cons_val, pow_one, Polynomial.coeff_derivative,
      map_sub, PowerSeries.coeff_mul, map_sum, map_mul, PowerSeries.coeff_derivative,
      coeff_colSer, rho_u, rho_v]
    simp only [map_add, map_natCast, map_one, Nat.add_one_ne_zero, if_false, zero_mul,
      mul_zero, Finset.sum_const_zero, sub_zero]
    rw [Finset.sum_eq_single (a, 0)]
    · simp only [if_true]
      ring
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have : p.2 ≠ 0 := fun h => hne (Prod.ext (by omega) h)
      rw [if_neg this, mul_zero]
    · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

/-! ### Products and the monomial `u_λ v_0^l` -/

theorem rho_Pga {r : ℕ} (l : ℕ) (w : Fin r → Fin 4) (a : Fin r →₀ ℕ) :
    rho l (Pga w a) = X (1, 0) ^ (∑ i, vcount (w i)) *
      rename uIdx (∏ i, (ellP l (w i)).coeff (a i)) := by
  rw [Pga, map_prod]
  simp only [rho_genCoeff]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod]

/-- The jet monomial `u_λ v_0^l`. -/
def mono (ms : Multiset ℕ) (l : ℕ) : Fin 2 × ℕ →₀ ℕ :=
  (Multiset.toFinsupp ms).mapDomain uIdx + Finsupp.single (1, 0) l

theorem mapDomain_uIdx_v0 (u : ℕ →₀ ℕ) : u.mapDomain uIdx (1, 0) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨j, hj⟩
  simp [uIdx] at hj

theorem mono_v0 (ms : Multiset ℕ) (l : ℕ) : mono ms l (1, 0) = l := by
  simp [mono, mapDomain_uIdx_v0]

theorem coeff_mono_vpow (ms : Multiset ℕ) (l E : ℕ) (f : UPoly) :
    coeff (mono ms l) (X (1, 0) ^ E * rename uIdx f) =
      if E = l then coeff (Multiset.toFinsupp ms) f else 0 := by
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  by_cases hle : Finsupp.single ((1 : Fin 2), 0) E ≤ mono ms l
  · rw [if_pos hle, one_mul]
    have hEl : E ≤ l := by
      have := (Finsupp.single_le_iff).mp hle
      rwa [mono_v0] at this
    by_cases hE : E = l
    · subst hE
      rw [if_pos rfl, mono, add_tsub_cancel_right, coeff_rename_mapDomain _ uIdx_injective]
    · rw [if_neg hE]
      apply coeff_rename_eq_zero
      intro u hu
      exfalso
      have h := congrArg (fun d => d (1, 0)) hu
      simp only [mapDomain_uIdx_v0, Finsupp.tsub_apply, mono_v0, Finsupp.single_eq_same] at h
      omega
  · rw [if_neg hle, if_neg]
    rintro rfl
    exact hle ((Finsupp.single_le_iff).mpr (by rw [mono_v0]))

theorem keep_mono (ms : Multiset ℕ) (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l) :
    ∀ x ∈ (mono ms l).support, keep l x := by
  intro x hx
  rw [mono] at hx
  rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h)
    rw [Multiset.toFinsupp_support, Multiset.mem_toFinset] at hj
    exact Or.inl ⟨rfl, hms j hj⟩
  · rw [Finsupp.mem_support_iff] at h
    by_cases hx : x = (1, 0)
    · exact Or.inr hx
    · rw [Finsupp.single_apply, if_neg (Ne.symm hx)] at h
      exact absurd rfl h

/-- The coefficient of `u_λ v_0^l` in a product of generator coefficients. -/
theorem coeff_mono_Pga {r : ℕ} (ms : Multiset ℕ) (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l)
    (w : Fin r → Fin 4) (a : Fin r →₀ ℕ) :
    coeff (mono ms l) (Pga w a) = if ∑ i, vcount (w i) = l then
      coeff (Multiset.toFinsupp ms) (∏ i, (ellP l (w i)).coeff (a i)) else 0 := by
  rw [← coeff_rho l _ (keep_mono ms l hms), rho_Pga, coeff_mono_vpow]

/-! ### Degree bounds and evaluation of the reduced series -/

theorem coeff_uq_eq_zero (l j : ℕ) (h : l < j) : (uq l).coeff j = 0 := by
  rw [coeff_uq, if_neg (by omega)]

theorem ellP_coeff_eq_zero (l : ℕ) (g : Fin 4) (a : ℕ) (h : 2 * l < a) :
    (ellP l g).coeff a = 0 := by
  fin_cases g
  · simp only [ellP, Fin.zero_eta, Matrix.cons_val_zero, sq, Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    by_cases h1 : l < p.1
    · rw [coeff_uq_eq_zero l p.1 h1, zero_mul]
    · rw [coeff_uq_eq_zero l p.2 (by omega), mul_zero]
  · simp only [ellP, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact coeff_uq_eq_zero l a (by omega)
  · simp only [ellP, Fin.reduceFinMk, Matrix.cons_val, Polynomial.coeff_one]
    rw [if_neg (by omega)]
  · simp only [ellP, Fin.reduceFinMk, Matrix.cons_val, Polynomial.coeff_derivative]
    rw [coeff_uq_eq_zero l (a + 1) (by omega), zero_mul]

theorem natDegree_ellP_lt (l : ℕ) (g : Fin 4) : (ellP l g).natDegree < 2 * l + 1 := by
  have : (ellP l g).natDegree ≤ 2 * l :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ellP_coeff_eq_zero l g N hN
  omega

theorem eval_uq (l : ℕ) (t : ℂ) : (uq l).eval (MvPolynomial.C t) = ev l t := by
  rw [uq, Polynomial.eval_finsetSum, ev]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_monomial, map_pow, mul_comm]

theorem eval_duq (l : ℕ) (t : ℂ) :
    (Polynomial.derivative (uq l)).eval (MvPolynomial.C t) = evd l t := by
  rw [uq, map_sum, Polynomial.eval_finsetSum, evd]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.derivative_monomial, Polynomial.eval_monomial, map_mul, map_pow, map_natCast]
  ring

/-- The local forms attached to the four generators. -/
def locG (l : ℕ) (t : ℂ) (g : Fin 4) : UPoly := ![ev l t ^ 2, ev l t, 1, evd l t] g

theorem eval_ellP (l : ℕ) (t : ℂ) (g : Fin 4) :
    (ellP l g).eval (MvPolynomial.C t) = locG l t g := by
  fin_cases g
  · simp [ellP, locG, eval_uq]
  · simp [ellP, locG, eval_uq]
  · simp [ellP, locG]
  · simp [ellP, locG, eval_duq]

theorem sum_range_ellP (l : ℕ) (t : ℂ) (g : Fin 4) :
    ∑ a ∈ Finset.range (2 * l + 1), (ellP l g).coeff a * MvPolynomial.C (t ^ a) = locG l t g := by
  rw [← eval_ellP, Polynomial.eval_eq_sum_range' (natDegree_ellP_lt l g)]
  simp only [map_pow]


/-! ### The generating polynomials -/

/-- Functions to finitely supported functions on `Fin r`. -/
def toF {r : ℕ} (a : Fin r → ℕ) : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm a

@[simp] theorem toF_apply {r : ℕ} (a : Fin r → ℕ) (i : Fin r) : toF a i = a i := rfl

@[simp] theorem toF_coe {r : ℕ} (d : Fin r →₀ ℕ) : toF (⇑d) = d :=
  Finsupp.equivFunOnFinite.symm_apply_apply d

/-- The box of exponents `a_i ≤ 2l`. -/
def boxF (r l : ℕ) : Finset (Fin r → ℕ) := Fintype.piFinset fun _ => Finset.range (2 * l + 1)

/-- The generating polynomial `Σ_a [u_λ v_0^l] P_{w,a} t^a`. -/
def Apol {r : ℕ} (ms : Multiset ℕ) (l : ℕ) (w : Fin r → Fin 4) : MvPolynomial (Fin r) ℂ :=
  ∑ a ∈ boxF r l, monomial (toF a) (coeff (mono ms l) (Pga w (toF a)))

theorem coeff_mono_Pga_of_not_box {r : ℕ} (ms : Multiset ℕ) (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l)
    (w : Fin r → Fin 4) (d : Fin r →₀ ℕ) (hd : (⇑d) ∉ boxF r l) :
    coeff (mono ms l) (Pga w d) = 0 := by
  rw [boxF, Fintype.mem_piFinset] at hd
  push Not at hd
  obtain ⟨i, hi⟩ := hd
  rw [Finset.mem_range, not_lt] at hi
  rw [coeff_mono_Pga ms l hms, Finset.prod_eq_zero (Finset.mem_univ i)
    (ellP_coeff_eq_zero l (w i) (d i) (by omega)), coeff_zero, ite_self]

theorem coeff_Apol {r : ℕ} (ms : Multiset ℕ) (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l)
    (w : Fin r → Fin 4) (d : Fin r →₀ ℕ) :
    coeff d (Apol ms l w) = coeff (mono ms l) (Pga w d) := by
  rw [Apol, coeff_sum]
  simp only [coeff_monomial]
  by_cases hd : (⇑d) ∈ boxF r l
  · rw [Finset.sum_eq_single (⇑d)]
    · rw [toF_coe, if_pos rfl]
    · intro b _ hb
      rw [if_neg]
      intro h
      apply hb
      rw [← h]
      rfl
    · intro h; exact absurd hd h
  · rw [coeff_mono_Pga_of_not_box ms l hms w d hd]
    apply Finset.sum_eq_zero
    intro b hb
    rw [if_neg]
    rintro rfl
    exact hd hb

/-- The generating polynomial is the generating series of the coefficient functional. -/
theorem coe_Apol {r : ℕ} (ms : Multiset ℕ) (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l)
    (w : Fin r → Fin 4) :
    ((Apol ms l w : MvPolynomial (Fin r) ℂ) : MvPowerSeries (Fin r) ℂ) =
      Gam (lcoeff ℂ (mono ms l)) w := by
  ext d
  rw [MvPolynomial.coeff_coe, coeff_Apol ms l hms, coeff_Gam]
  rfl

/-- At a point `t`, the generating polynomial evaluates to the coefficient of `u_λ` in the
product of the local forms. -/
theorem eval_Apol {r : ℕ} (ms : Multiset ℕ) (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l)
    (w : Fin r → Fin 4) (t : Fin r → ℂ) :
    eval t (Apol ms l w) = if ∑ i, vcount (w i) = l then
      coeff (Multiset.toFinsupp ms) (∏ i, locG l (t i) (w i)) else 0 := by
  rw [Apol, map_sum]
  simp only [eval_monomial, coeff_mono_Pga ms l hms]
  split_ifs with hV
  · have hprod : ∏ i, locG l (t i) (w i) = ∑ a ∈ boxF r l,
        (∏ i, (ellP l (w i)).coeff (a i)) * MvPolynomial.C (∏ i, t i ^ a i) := by
      simp only [← sum_range_ellP l]
      rw [boxF, Finset.prod_univ_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [map_prod, ← Finset.prod_mul_distrib]
    rw [hprod, coeff_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp only [toF_apply]
    ring
  · simp

/-! ### Products of local forms along a list configuration -/

/-- The standard multiplicity-two point at `t`. -/
def stdPt (t : ℂ) : Pt := { t := t, β := 1, γ := 0, δ := 1, two := true }

/-- The local type of a generator: `X ↦ ev²`, `Y ↦ ev`, `Z ↦ 1`, `J ↦ ev'`. -/
def gtype (g : Fin 4) : Fin 4 := ![3, 1, 0, 2] g

theorem loc_stdPt (l : ℕ) (t : ℂ) (g : Fin 4) : loc l (stdPt t) (gtype g) = locG l t g := by
  fin_cases g <;> simp [loc, locG, stdPt, gtype]

theorem F_ofFn (l : ℕ) : ∀ (r : ℕ) (pts : Fin r → Pt) (xs : Fin r → Fin 4),
    F l (List.ofFn pts) (List.ofFn xs) = ∏ i, loc l (pts i) (xs i)
  | 0, _, _ => by simp [F]
  | r + 1, pts, xs => by
    rw [List.ofFn_succ, List.ofFn_succ, F_cons, F_ofFn l r, Fin.prod_univ_succ]

theorem prod_locG_eq_F (l r : ℕ) (t : Fin r → ℂ) (w : Fin r → Fin 4) :
    ∏ i, locG l (t i) (w i) =
      F l (List.ofFn fun i => stdPt (t i)) (List.ofFn fun i => gtype (w i)) := by
  rw [F_ofFn]
  simp only [loc_stdPt]


end

end VOA.JetProduct
