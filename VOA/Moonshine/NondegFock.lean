/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenBosonCharge
import VOA.Moonshine.LatticeInvolution

/-!
# The invariant bilinear form on the untwisted Fock space  (Moonshine step M8c, `hnd` part 1)

On `FockN r = ℂ[X_{(m,b)}]` (`X_{(m,b)} = h_b(−m−1)`) the bilinear form

  `F(X^d, X^e) = δ_{d,e} ∏_{(m,b)} (−(m+1))^{d_{m,b}} · d_{m,b}!`   (`uForm`, `uWt`)

is the one forced by the FHL contragredient for weight-one fields, `h(n)ᵗ = −h(−n)`
(`uForm_oscN`).  As in the twisted case (`InvForm.fockForm`) this is the **negative** Fock form.

* `uForm_symm`, `uForm_one` (`F(1,q)` = constant term), `uForm_X_mul`.
* `uForm_oscN` — `F(h_b(n) p, q) = −F(p, h_b(−n) q)` for every `n ∈ ℤ`.
* `uForm_EEVec` — the lattice dressing `EE(γ,z) = E⁻(γ,z)E⁺(γ,z)` is transposed to
  `EE(γ,z⁻¹)`: `F(EE(γ)ₜ p, q) = F(p, EE(γ)₋ₜ q)`.  Proof: double induction on monomials using
  only the current/dressing commutator `alphaFieldGen_comm_EEVec` and `EE(γ)ₜ 1 = vSchur`.
* `uForm_sigmaN` — the Fock involution `σ` is an isometry.
* `uForm_orth_gradingZN` — distinct Fock weights are orthogonal.
* `uWt_ne_zero` — monomials have nonzero norm.

## Status
All declarations proved; no `sorry`/axioms.  Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.Nondeg

open MvPolynomial VOA VOA.IntegralLattice VOA.LatGen HeisenbergN
open Module (End)

variable {r : ℕ}

/-- The scalar `−(m+1)` attached to the variable `X_{(m,b)} = h_b(−m−1)`. -/
noncomputable def uVar (v : ℕ × Fin r) : ℂ := -((v.1 : ℂ) + 1)

/-- The norm `F(X^d,X^d) = ∏_v uVar_v^{d_v} d_v!`. -/
noncomputable def uWt (d : (ℕ × Fin r) →₀ ℕ) : ℂ :=
  d.prod fun v m => uVar v ^ m * (m.factorial : ℂ)

/-- **The invariant form on the untwisted Fock space** `FockN r`. -/
noncomputable def uForm (r : ℕ) : LinearMap.BilinForm ℂ (FockN r) :=
  Finsupp.lsum ℂ fun d => LinearMap.smulRight LinearMap.id (uWt d • lcoeff ℂ d)

theorem uForm_monomial (d : (ℕ × Fin r) →₀ ℕ) (a : ℂ) (q : FockN r) :
    uForm r (monomial d a) q = a * (uWt d * coeff d q) := by
  rw [uForm]
  erw [Finsupp.lsum_single]
  simp

theorem uForm_monomial_monomial (d e : (ℕ × Fin r) →₀ ℕ) (a b : ℂ) :
    uForm r (monomial d a) (monomial e b) = if d = e then a * b * uWt d else 0 := by
  rw [uForm_monomial, coeff_monomial]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · ring

theorem uForm_symm (p q : FockN r) : uForm r p q = uForm r q p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    induction q using MvPolynomial.induction_on' with
    | monomial e b =>
      rw [uForm_monomial_monomial, uForm_monomial_monomial]
      by_cases h : d = e
      · subst h; simp only [if_true]; ring
      · rw [if_neg h, if_neg (Ne.symm h)]
    | add q₁ q₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, LinearMap.add_apply]
  | add p₁ p₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, h₁, h₂, map_add]

theorem uWt_zero : uWt (0 : (ℕ × Fin r) →₀ ℕ) = 1 := by
  simp [uWt]

theorem uForm_one (q : FockN r) : uForm r 1 q = coeff 0 q := by
  rw [show (1 : FockN r) = monomial 0 1 from rfl, uForm_monomial, uWt_zero, one_mul, one_mul]

theorem uWt_add_single (d : (ℕ × Fin r) →₀ ℕ) (v : ℕ × Fin r) :
    uWt (d + Finsupp.single v 1) = uVar v * ((d v : ℂ) + 1) * uWt d := by
  have hg : ∀ w : ℕ × Fin r, (fun w m => uVar w ^ m * (m.factorial : ℂ)) w 0 = 1 := by
    intro w; simp
  rw [uWt, uWt, ← Finsupp.mul_prod_erase' _ v _ hg, ← Finsupp.mul_prod_erase' d v _ hg]
  have he : Finsupp.erase v (d + Finsupp.single v 1) = Finsupp.erase v d := by
    rw [Finsupp.erase_add, Finsupp.erase_single, add_zero]
  rw [he]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ, Nat.factorial_succ]
  push_cast
  ring

/-- **Creation is adjoint to annihilation**: `F(X_v p, q) = uVar_v F(p, ∂_v q)`. -/
theorem uForm_X_mul (v : ℕ × Fin r) (p q : FockN r) :
    uForm r (X v * p) q = uVar v * uForm r p (pderiv v q) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    induction q using MvPolynomial.induction_on' with
    | monomial e b =>
      rw [X, monomial_mul, one_mul, pderiv_monomial, uForm_monomial_monomial,
        uForm_monomial_monomial]
      by_cases h : Finsupp.single v 1 + d = e
      · subst h
        have h2 : d = Finsupp.single v 1 + d - Finsupp.single v 1 := by
          ext w; simp
        rw [if_pos rfl, if_pos h2, add_comm (Finsupp.single v 1) d, uWt_add_single]
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

theorem uForm_oscN_creation (b : Fin r) (m : ℕ) (p q : FockN r) :
    uForm r (oscN r 1 b (-((m : ℤ) + 1)) p) q = -uForm r p (oscN r 1 b ((m : ℤ) + 1) q) := by
  rw [oscN_apply_neg r 1 b (by omega), oscN_apply_pos r 1 b (by omega),
    show (-(-((m : ℤ) + 1)) - 1).toNat = m by omega, show ((m : ℤ) + 1 - 1).toNat = m by omega,
    uForm_X_mul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, uVar]
  push_cast
  ring

/-- **The oscillators are anti-adjoint**: `F(h_b(n) p, q) = −F(p, h_b(−n) q)`. -/
theorem uForm_oscN (b : Fin r) (n : ℤ) (p q : FockN r) :
    uForm r (oscN r 1 b n p) q = -uForm r p (oscN r 1 b (-n) q) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
    rw [uForm_oscN_creation, neg_neg]
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    rw [uForm_symm, uForm_symm p, uForm_oscN_creation, neg_neg]

/-! ## The Fock involution is an isometry -/

theorem constantCoeff_sigmaN (q : FockN r) : constantCoeff (sigmaN r q) = constantCoeff q := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    rw [sigmaN_apply, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp => rw [sigmaN_mul, sigmaN_X, map_mul, map_mul, hp]; simp

/-- `σ` is an isometry of `F`. -/
theorem uForm_sigmaN (p q : FockN r) : uForm r (sigmaN r p) (sigmaN r q) = uForm r p q := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C a =>
    have h : sigmaN r (MvPolynomial.C a) = MvPolynomial.C a := by
      rw [sigmaN_apply, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    rw [h, show (MvPolynomial.C a : FockN r) = a • (1 : FockN r) by rw [smul_eq_C_mul, mul_one],
      map_smul, LinearMap.smul_apply, LinearMap.smul_apply, uForm_one, uForm_one,
      ← constantCoeff_eq, constantCoeff_sigmaN]
  | add p₁ p₂ h₁ h₂ => rw [map_add, map_add, LinearMap.add_apply, h₁, h₂, map_add,
      LinearMap.add_apply]
  | mul_X p v hp =>
    rw [sigmaN_mul, sigmaN_X, mul_neg, map_neg, LinearMap.neg_apply, mul_comm (sigmaN r p),
      uForm_X_mul, mul_comm p, uForm_X_mul]
    have h1 : pderiv v (sigmaN r q) = -sigmaN r (pderiv v q) := by
      rw [sigmaN_pderiv, neg_neg]
    rw [h1, map_neg, hp]
    ring

/-! ## Orthogonality and norms -/

/-- Distinct Fock weights are `F`-orthogonal. -/
theorem uForm_orth_gradingWN {w w' : ℕ} (hww : w ≠ w') {p q : FockN r} (hp : p ∈ gradingWN r w)
    (hq : q ∈ gradingWN r w') : uForm r p q = 0 := by
  rw [p.as_sum, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hdw : Finsupp.weight weightFnN d = w := hp (mem_support_iff.mp hd)
  have hq0 : coeff d q = 0 := by
    by_contra hc
    exact hww (hdw.symm.trans (hq hc))
  rw [uForm_monomial, hq0, mul_zero, mul_zero]

theorem uForm_orth_gradingZN {w w' : ℤ} (hww : w ≠ w') {p q : FockN r} (hp : p ∈ gradingZN r w)
    (hq : q ∈ gradingZN r w') : uForm r p q = 0 := by
  by_cases hw : 0 ≤ w
  · by_cases hw' : 0 ≤ w'
    · rw [gradingZN_of_nonneg hw] at hp
      rw [gradingZN_of_nonneg hw'] at hq
      exact uForm_orth_gradingWN (by omega) hp hq
    · rw [gradingZN_of_neg (by omega), Submodule.mem_bot] at hq
      rw [hq, map_zero]
  · rw [gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, map_zero, LinearMap.zero_apply]

theorem uVar_ne_zero (v : ℕ × Fin r) : uVar v ≠ 0 := by
  rw [uVar, neg_ne_zero]
  exact_mod_cast Nat.succ_ne_zero v.1

theorem uWt_ne_zero (d : (ℕ × Fin r) →₀ ℕ) : uWt d ≠ 0 := by
  rw [uWt, Finsupp.prod]
  refine Finset.prod_ne_zero_iff.mpr fun v _ => mul_ne_zero (pow_ne_zero _ (uVar_ne_zero v)) ?_
  exact_mod_cast Nat.factorial_ne_zero _

/-! ## The lattice dressing `EE(γ,z)` is self-adjoint up to `z ↦ z⁻¹` -/

section Dressing

variable (L : IntegralLattice)

/-- Operator form of `alphaFieldGen_comm_EEVec`: for `n ≠ 0`,
`h_a(n) EE(γ)ₜ = EE(γ)ₜ h_a(n) + c_a(γ) EE(γ)_{t−n}`. -/
theorem oscN_EEVec_apply (a : Fin (rank L)) (γ : L.carrier) {n : ℤ} (hn : n ≠ 0) (t : ℤ)
    (y : FockN (rank L)) :
    oscN (rank L) 1 a n (EEVec L γ t y)
      = EEVec L γ t (oscN (rank L) 1 a n y) + chargeCoord L γ a • EEVec L γ (t - n) y := by
  have h := congrArg (fun T : End ℂ (FockN (rank L)) => T y)
    (alphaFieldGen_comm_EEVec L a γ (-n - 1) t)
  simp only [bracketDist_apply, currentN_apply, LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [if_neg (by omega), show -(-n - 1) - 1 = n by ring, show t + (-n - 1) + 1 = t - n by ring,
    LinearMap.smul_apply] at h
  rw [← h]; abel

theorem constantCoeff_vVar (γ : L.carrier) (m : ℕ) : constantCoeff (vVar L γ m) = 0 := by
  simp [vVar, map_sum]

theorem constantCoeff_vSchur_succ (γ : L.carrier) (N : ℕ) :
    constantCoeff (vSchur L γ (N + 1)) = 0 := by
  rw [vSchur_succ, smul_eq_C_mul, map_mul, map_sum]
  simp [constantCoeff_vVar]

theorem coeff_zero_EEVec_one (γ : L.carrier) (t : ℤ) :
    coeff 0 (EEVec L γ t 1) = if t = 0 then 1 else 0 := by
  have h := EEVec_vacuum L γ t
  rw [vacuumN] at h
  rw [h, ← constantCoeff_eq]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    obtain ⟨N, rfl⟩ : ∃ N : ℕ, t = N := ⟨t.toNat, by omega⟩
    rcases N with _ | N
    · simp [vSchur_zero]
    · rw [Int.toNat_natCast, constantCoeff_vSchur_succ, if_neg (by omega)]
  · rw [if_neg ht, if_neg (by omega), map_zero]

theorem X_mul_eq_oscN (m : ℕ) (b : Fin (rank L)) (y : FockN (rank L)) :
    y * X (m, b) = oscN (rank L) 1 b (-((m : ℤ) + 1)) y := by
  rw [oscN_apply_neg _ 1 b (by omega), show (-(-((m : ℤ) + 1)) - 1).toNat = m by omega, mul_comm]

theorem oscN_one_nonneg (b : Fin (rank L)) {n : ℤ} (hn : 0 ≤ n) :
    oscN (rank L) 1 b n (1 : FockN (rank L)) = 0 :=
  oscN_vacuum (rank L) 1 b n hn

theorem uForm_one_oscN_creation (b : Fin (rank L)) (m : ℕ) (z : FockN (rank L)) :
    uForm (rank L) 1 (oscN (rank L) 1 b (-((m : ℤ) + 1)) z) = 0 := by
  rw [uForm_symm, uForm_oscN, neg_neg, oscN_one_nonneg L b (by omega), map_zero, neg_zero]

theorem uForm_EEVec_vac (γ : L.carrier) (y' : FockN (rank L)) (t : ℤ) :
    uForm (rank L) (EEVec L γ t 1) y' = uForm (rank L) 1 (EEVec L γ (-t) y') := by
  induction y' using MvPolynomial.induction_on generalizing t with
  | C c =>
    rw [show (MvPolynomial.C c : FockN (rank L)) = c • (1 : FockN (rank L)) by rw [smul_eq_C_mul, mul_one],
      map_smul, map_smul, map_smul, uForm_symm, uForm_one, uForm_one, smul_eq_mul, smul_eq_mul,
      coeff_zero_EEVec_one, coeff_zero_EEVec_one]
    by_cases ht : t = 0
    · subst ht; simp
    · rw [if_neg ht, if_neg (by omega)]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X y x hy =>
    obtain ⟨m, b⟩ := x
    rw [X_mul_eq_oscN]
    have hn : ((m : ℤ) + 1) ≠ 0 := by omega
    have hL : uForm (rank L) (EEVec L γ t 1) (oscN (rank L) 1 b (-((m : ℤ) + 1)) y)
        = -(chargeCoord L γ b * uForm (rank L) 1 (EEVec L γ (-(t - ((m : ℤ) + 1))) y)) := by
      rw [uForm_symm, uForm_oscN, neg_neg, oscN_EEVec_apply L b γ hn,
        oscN_one_nonneg L b (by omega), map_zero, zero_add, map_smul, smul_eq_mul, uForm_symm, hy]
    have hR : uForm (rank L) 1 (EEVec L γ (-t) (oscN (rank L) 1 b (-((m : ℤ) + 1)) y))
        = -(chargeCoord L γ b * uForm (rank L) 1 (EEVec L γ (-t - -((m : ℤ) + 1)) y)) := by
      rw [show EEVec L γ (-t) (oscN (rank L) 1 b (-((m : ℤ) + 1)) y)
          = oscN (rank L) 1 b (-((m : ℤ) + 1)) (EEVec L γ (-t) y)
            - chargeCoord L γ b • EEVec L γ (-t - -((m : ℤ) + 1)) y by
        rw [oscN_EEVec_apply L b γ (by omega)]; abel,
        map_sub, uForm_one_oscN_creation, map_smul, smul_eq_mul, zero_sub]
    rw [hL, hR, show -t - -((m : ℤ) + 1) = -(t - ((m : ℤ) + 1)) by ring]

/-- **`E⁻E⁺` is self-adjoint up to inversion**: `F(EE(γ)ₜ y, y') = F(y, EE(γ)₋ₜ y')`, i.e.
`(E⁻(γ,z)E⁺(γ,z))ᵗ = E⁻(γ,z⁻¹)E⁺(γ,z⁻¹)` for the form with `h(n)ᵗ = −h(−n)`. -/
theorem uForm_EEVec (γ : L.carrier) (t : ℤ) (y y' : FockN (rank L)) :
    uForm (rank L) (EEVec L γ t y) y' = uForm (rank L) y (EEVec L γ (-t) y') := by
  induction y using MvPolynomial.induction_on generalizing t y' with
  | C c =>
    rw [show (MvPolynomial.C c : FockN (rank L)) = c • (1 : FockN (rank L)) by rw [smul_eq_C_mul, mul_one]]
    simp only [map_smul, LinearMap.smul_apply, uForm_EEVec_vac]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X y x hy =>
    obtain ⟨m, b⟩ := x
    rw [X_mul_eq_oscN]
    have hK : -((m : ℤ) + 1) ≠ 0 := by omega
    have hn : ((m : ℤ) + 1) ≠ 0 := by omega
    have hL : uForm (rank L) (EEVec L γ t (oscN (rank L) 1 b (-((m : ℤ) + 1)) y)) y'
        = -uForm (rank L) y (EEVec L γ (-t) (oscN (rank L) 1 b ((m : ℤ) + 1) y'))
          - chargeCoord L γ b * uForm (rank L) y (EEVec L γ (-(t - -((m : ℤ) + 1))) y') := by
      rw [show EEVec L γ t (oscN (rank L) 1 b (-((m : ℤ) + 1)) y)
          = oscN (rank L) 1 b (-((m : ℤ) + 1)) (EEVec L γ t y)
            - chargeCoord L γ b • EEVec L γ (t - -((m : ℤ) + 1)) y by
        rw [oscN_EEVec_apply L b γ hK]; abel,
        map_sub, LinearMap.sub_apply, uForm_oscN, neg_neg, map_smul, LinearMap.smul_apply,
        smul_eq_mul, hy, hy]
    have hR : uForm (rank L) (oscN (rank L) 1 b (-((m : ℤ) + 1)) y) (EEVec L γ (-t) y')
        = -uForm (rank L) y (EEVec L γ (-t) (oscN (rank L) 1 b ((m : ℤ) + 1) y'))
          - chargeCoord L γ b * uForm (rank L) y (EEVec L γ (-t - ((m : ℤ) + 1)) y') := by
      rw [uForm_oscN, neg_neg, oscN_EEVec_apply L b γ hn, map_add, map_smul, smul_eq_mul]
      ring
    rw [hL, hR, show -(t - -((m : ℤ) + 1)) = -t - ((m : ℤ) + 1) by ring]

end Dressing

end VOA.Moonshine.Nondeg
