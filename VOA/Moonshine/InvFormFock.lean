/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedEOps

/-!
# The invariant bilinear form on the twisted Fock space `S[θ]`  (Moonshine step M8c, form part 1)

On `FockT r = ℂ[X_{(n,i)}]` (`X_{(n,i)} = h_i(−n−½)`, `TwistedHeisenberg.lean`) the bilinear form

  `F(X^d, X^e) = δ_{d,e} ∏_{(n,i)} (−(n+½))^{d_{n,i}} · d_{n,i}!`   (`fockForm`, `fockWt`)

is the one forced by the FHL contragredient for weight-one fields:
`Y(h,z)ᵗ = −z⁻² Y(h,z⁻¹)`, i.e. `h(m)ᵗ = −h(−m)`.  Note the sign: it is **not** the positive
(Hermitian-type) Fock form, which would satisfy `h(m)ᵗ = +h(−m)`.

* `fockForm_symm`, `fockForm_one` (`F(1,q)` = constant term), `fockWt_add_single`.
* `fockForm_X_mul` — `F(X_v p, q) = c_v F(p, ∂_v q)`, `c_v = −(n+½)`.
* `fockForm_modeT` — `F(h_i(k/2) p, q) = −F(p, h_i(−k/2) q)` for every `k`.
* `fockForm_DD` — `F(DD v a y, y') = F(y, DD v (−a) y')`: the dressing `E⁻(−v,w)E⁺(−v,w)` is
  transposed to `E⁻(−v,w⁻¹)E⁺(−v,w⁻¹)` (no sign, no `v ↦ −v`).  Proof: double induction on
  monomials using only `modeT_comm_DD`, `fockForm_modeT`, `DD_one`, and the constant terms
  `coeff_zero_sMz` (`= δ_{a,0}`).

Numerical cross-check (before formalizing; sympy, rank 2, three oscillator levels, `v` rational):
`F(DD a y, y') = F(y, DD (−a) y')` holds on all test pairs for `|a| ≤ 4`, and fails with the
positive form (sign `+(n+½)`), which instead transposes `DD v` to `DD (−v)`.

## Status
All declarations proved; no `sorry`/axioms.  Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.InvForm
open MvPolynomial VOA.TwistedHeisenberg VOA.Moonshine.LatticeTwisted
variable {r : ℕ}

/-- The scalar `c_v = −(n + ½)` attached to the variable `v = (n, i)`. -/
noncomputable def cVar (v : ℕ × Fin r) : ℂ := -((v.1 : ℂ) + 1 / 2)

/-- The norm `F(X^d, X^d) = ∏_v c_v^{d_v} d_v!`. -/
noncomputable def fockWt (d : (ℕ × Fin r) →₀ ℕ) : ℂ :=
  d.prod fun v m => cVar v ^ m * (m.factorial : ℂ)

/-- **The invariant form on `S[θ]`**: monomials orthogonal, `F(X^d,X^d) = fockWt d`. -/
noncomputable def fockForm (r : ℕ) : LinearMap.BilinForm ℂ (FockT r) :=
  Finsupp.lsum ℂ fun d => LinearMap.smulRight LinearMap.id (fockWt d • lcoeff ℂ d)

theorem fockForm_monomial (d : (ℕ × Fin r) →₀ ℕ) (a : ℂ) (q : FockT r) :
    fockForm r (monomial d a) q = a * (fockWt d * coeff d q) := by
  rw [fockForm]
  erw [Finsupp.lsum_single]
  simp

theorem fockForm_monomial_monomial (d e : (ℕ × Fin r) →₀ ℕ) (a b : ℂ) :
    fockForm r (monomial d a) (monomial e b) = if d = e then a * b * fockWt d else 0 := by
  rw [fockForm_monomial, coeff_monomial]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · ring

theorem fockForm_symm (p q : FockT r) : fockForm r p q = fockForm r q p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    induction q using MvPolynomial.induction_on' with
    | monomial e b =>
      rw [fockForm_monomial_monomial, fockForm_monomial_monomial]
      by_cases h : d = e
      · subst h; simp only [if_true]; ring
      · rw [if_neg h, if_neg (Ne.symm h)]
    | add q₁ q₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, LinearMap.add_apply]
  | add p₁ p₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, h₁, h₂, map_add]

theorem fockWt_zero : fockWt (0 : (ℕ × Fin r) →₀ ℕ) = 1 := by
  simp [fockWt]

theorem fockForm_one (q : FockT r) : fockForm r 1 q = coeff 0 q := by
  rw [show (1 : FockT r) = monomial 0 1 from rfl, fockForm_monomial, fockWt_zero, one_mul, one_mul]

theorem fockWt_add_single (d : (ℕ × Fin r) →₀ ℕ) (v : ℕ × Fin r) :
    fockWt (d + Finsupp.single v 1) = cVar v * ((d v : ℂ) + 1) * fockWt d := by
  have hg : ∀ w : ℕ × Fin r, (fun w m => cVar w ^ m * (m.factorial : ℂ)) w 0 = 1 := by
    intro w; simp
  rw [fockWt, fockWt, ← Finsupp.mul_prod_erase' _ v _ hg, ← Finsupp.mul_prod_erase' d v _ hg]
  have he : Finsupp.erase v (d + Finsupp.single v 1) = Finsupp.erase v d := by
    rw [Finsupp.erase_add, Finsupp.erase_single, add_zero]
  rw [he]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ, Nat.factorial_succ]
  push_cast
  ring


/-- **Creation is adjoint to annihilation**: `F(X_v p, q) = c_v F(p, ∂_v q)`. -/
theorem fockForm_X_mul (v : ℕ × Fin r) (p q : FockT r) :
    fockForm r (X v * p) q = cVar v * fockForm r p (pderiv v q) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    induction q using MvPolynomial.induction_on' with
    | monomial e b =>
      rw [X, monomial_mul, one_mul, pderiv_monomial, fockForm_monomial_monomial,
        fockForm_monomial_monomial]
      by_cases h : Finsupp.single v 1 + d = e
      · subst h
        have h2 : d = Finsupp.single v 1 + d - Finsupp.single v 1 := by
          ext w; simp
        rw [if_pos rfl, if_pos h2, add_comm (Finsupp.single v 1) d, fockWt_add_single]
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast; ring
      · rw [if_neg h]
        by_cases hev : e v = 0
        · simp [hev]
        · rw [if_neg]
          · simp
          · rintro rfl
            apply h
            ext w
            simp only [Finsupp.add_apply, Finsupp.tsub_apply]
            by_cases hw : w = v
            · subst hw; simp; omega
            · simp [Ne.symm hw]
    | add q₁ q₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂, mul_add]
  | add p₁ p₂ h₁ h₂ => rw [mul_add, map_add, LinearMap.add_apply, h₁, h₂, map_add,
      LinearMap.add_apply, mul_add]


theorem fockForm_modeT_creation (i : Fin r) (n : ℕ) (p q : FockT r) :
    fockForm r (modeT r i (-(2 * n + 1)) p) q = -fockForm r p (modeT r i (2 * n + 1) q) := by
  rw [modeT_creation, fockForm_X_mul, modeT_annihilation, map_smul, smul_eq_mul, cVar]
  push_cast
  ring

/-- **The twisted oscillators are anti-adjoint**: `F(h_i(k/2) p, q) = −F(p, h_i(−k/2) q)`
(all `k`; even `k` gives `0 = 0`). -/
theorem fockForm_modeT (i : Fin r) (k : ℤ) (p q : FockT r) :
    fockForm r (modeT r i k p) q = -fockForm r p (modeT r i (-k) q) := by
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · rw [modeT_even r i hk, modeT_even r i (by omega)]
    simp
  · rcases lt_or_gt_of_ne (show k ≠ 0 by omega) with hneg | hpos
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -(2 * n + 1) := ⟨((-k - 1) / 2).toNat, by omega⟩
      rw [fockForm_modeT_creation, neg_neg]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 2 * n + 1 := ⟨((k - 1) / 2).toNat, by omega⟩
      rw [fockForm_symm, fockForm_symm p, fockForm_modeT_creation, neg_neg]


/-! ## The dressing `DD` is self-adjoint up to `a ↦ −a` -/

theorem modeT_DD_apply (v : Fin r → ℂ) (i : Fin r) {K : ℤ} (hK : Odd K) (a : ℤ) (y : FockT r) :
    modeT r i K (DD v a y) = DD v a (modeT r i K y) + v i • DD v (a - K) y := by
  have h := congrArg (fun T : Module.End ℂ (FockT r) => T y) (modeT_comm_DD v i hK a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [← h]; abel

theorem DD_one (v : Fin r → ℂ) (a : ℤ) : DD v a 1 = sMz v a := by
  rw [DD_apply_range v a 1 1 (fun q hq => by
    rw [show (1 : FockT r) = C 1 from rfl, EpC_C, if_neg (by omega)])]
  rw [Finset.sum_range_one, show (1 : FockT r) = C 1 from rfl, EpC_C, if_pos rfl]
  simp

theorem constantCoeff_dM (v : Fin r → ℂ) (k : ℕ) : constantCoeff (dM v k) = 0 := by
  unfold dM vVarT
  split_ifs <;> simp [map_sum, constantCoeff_X]

theorem constantCoeff_sM_succ (v : Fin r → ℂ) (p : ℕ) : constantCoeff (sM v (p + 1)) = 0 := by
  have h := congrArg constantCoeff (nexp_rec (dM v) p)
  simp only [map_sum, map_mul, constantCoeff_dM, zero_mul, Finset.sum_const_zero] at h
  have hp : ((p : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  exact (mul_eq_zero.mp h).resolve_left hp

theorem coeff_zero_sMz (v : Fin r → ℂ) (a : ℤ) : coeff 0 (sMz v a) = if a = 0 then 1 else 0 := by
  rw [← constantCoeff_eq]
  by_cases ha : a < 0
  · rw [sMz_of_neg v ha, map_zero, if_neg (by omega)]
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, a = p := ⟨a.toNat, by omega⟩
  rw [sMz_natCast]
  rcases p with _ | p
  · simp
  · rw [constantCoeff_sM_succ, if_neg (by omega)]

theorem modeT_one_pos (i : Fin r) {K : ℤ} (hK : 0 < K) : modeT r i K 1 = 0 :=
  modeT_vacT r i hK

theorem fockForm_one_modeT_creation (i : Fin r) (n : ℕ) (z : FockT r) :
    fockForm r 1 (modeT r i (-(2 * n + 1)) z) = 0 := by
  rw [fockForm_symm, fockForm_modeT, neg_neg, modeT_one_pos i (by omega), map_zero, neg_zero]

theorem X_mul_eq_modeT (x : ℕ × Fin r) (y : FockT r) :
    y * X x = modeT r x.2 (-(2 * x.1 + 1)) y := by
  rw [modeT_creation, mul_comm]

theorem odd_creation (n : ℕ) : Odd (-(2 * (n : ℤ) + 1)) := ⟨-(n : ℤ) - 1, by ring⟩

theorem fockForm_DD_vac (v : Fin r → ℂ) (y' : FockT r) (a : ℤ) :
    fockForm r (DD v a 1) y' = fockForm r 1 (DD v (-a) y') := by
  induction y' using MvPolynomial.induction_on generalizing a with
  | C c =>
    rw [show (C c : FockT r) = c • (1 : FockT r) by rw [smul_eq_C_mul, mul_one], map_smul,
      map_smul, map_smul, DD_one, DD_one, fockForm_symm, fockForm_one, fockForm_one, smul_eq_mul,
      smul_eq_mul, coeff_zero_sMz, coeff_zero_sMz]
    by_cases ha : a = 0
    · subst ha; simp
    · rw [if_neg ha, if_neg (by omega)]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X y x hy =>
    obtain ⟨n, i⟩ := x
    rw [X_mul_eq_modeT]
    simp only
    have hK : Odd (-(2 * (n : ℤ) + 1)) := odd_creation n
    -- left side
    rw [fockForm_symm, fockForm_modeT, neg_neg, modeT_DD_apply v i ⟨n, by ring⟩,
      modeT_one_pos i (by omega), map_zero, zero_add, map_smul, smul_eq_mul, fockForm_symm, hy]
    -- right side
    have h2 := modeT_DD_apply v i hK (-a) y
    rw [show DD v (-a) (modeT r i (-(2 * n + 1)) y)
        = modeT r i (-(2 * n + 1)) (DD v (-a) y) - v i • DD v (-a - -(2 * n + 1)) y by
      rw [h2]; abel, map_sub, fockForm_one_modeT_creation, map_smul, smul_eq_mul, zero_sub]
    rw [show -(a - (2 * (n : ℤ) + 1)) = -a - -(2 * n + 1) by ring]

/-- **`E⁻E⁺` is self-adjoint up to inversion**: `F(DD v a y, y') = F(y, DD v (−a) y')`, i.e.
`(E⁻(−v,w)E⁺(−v,w))ᵗ = E⁻(−v,w⁻¹)E⁺(−v,w⁻¹)` for the form with `h(n)ᵗ = −h(−n)`. -/
theorem fockForm_DD (v : Fin r → ℂ) (a : ℤ) (y y' : FockT r) :
    fockForm r (DD v a y) y' = fockForm r y (DD v (-a) y') := by
  induction y using MvPolynomial.induction_on generalizing a y' with
  | C c =>
    rw [show (C c : FockT r) = c • (1 : FockT r) by rw [smul_eq_C_mul, mul_one]]
    simp only [map_smul, LinearMap.smul_apply, fockForm_DD_vac]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X y x hy =>
    obtain ⟨n, i⟩ := x
    rw [X_mul_eq_modeT]
    simp only
    have hK : Odd (-(2 * (n : ℤ) + 1)) := odd_creation n
    have h1 := modeT_DD_apply v i hK a y
    rw [show DD v a (modeT r i (-(2 * n + 1)) y)
        = modeT r i (-(2 * n + 1)) (DD v a y) - v i • DD v (a - -(2 * n + 1)) y by
      rw [h1]; abel, map_sub, LinearMap.sub_apply, fockForm_modeT, neg_neg, map_smul,
      LinearMap.smul_apply, smul_eq_mul, hy, hy, fockForm_modeT, neg_neg,
      modeT_DD_apply v i ⟨n, by ring⟩, map_add, map_smul, smul_eq_mul]
    rw [show -(a - -(2 * (n : ℤ) + 1)) = -a - (2 * n + 1) by ring]
    ring

end VOA.Moonshine.InvForm
