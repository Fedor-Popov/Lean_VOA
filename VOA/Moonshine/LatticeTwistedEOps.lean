/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedExp
import VOA.Moonshine.TwistedHeisenberg

/-!
# Twisted oscillators and the operators `E^±(−α, z)` on `S[θ]`  (Moonshine step M6c)

On the twisted Fock space `S[θ] = FockT r` (`TwistedHeisenberg.lean`, modes `h_i(k/2)`, `k` odd,
form `δ_ij`) a charge vector `v : Fin r → ℂ` (for a lattice vector `α`, its orthonormal
coordinates) gives the twisted oscillators and the two halves of the twisted vertex operator of
`e^α` (FLM §9.1), written in the doubled variable `w = z^{1/2}`:

* `oscT v k = Σᵢ vᵢ h_i(k/2)`; `oscT_comm`: `[v(k/2), u(l/2)] = (k/2) ⟨v,u⟩ δ_{k+l,0}`.
* **`E⁻(−v, w) = exp(Σ_{k odd} (2/k) v(−k/2) wᵏ)`** is multiplication by the polynomials
  `sM v p` (coefficient of `wᵖ`), a Newton exponential (`LatticeTwistedExp.nexp`).
* **`E⁺(−v, w) = exp(−Σ_{k odd} (2/k) v(k/2) w⁻ᵏ)`** is the *translation*
  `X_{(n,i)} ↦ X_{(n,i)} − vᵢ w^{−(2n+1)}` (Taylor's formula for the commuting derivations
  `v(k/2) = (k/2)∂`): the algebra map `Ep v : FockT r →ₐ FockT r[u]`, `u = w⁻¹`; its
  coefficients are `EpC v q` (coefficient of `w^{−q}`).
* `EpC_sMz_mul` — **the `E⁺E⁻` reordering**:
  `E⁺_q(−v) ∘ E⁻_p(−u) = Σ_j fco(⟨v,u⟩)_j E⁻_{p−j}(−u) ∘ E⁺_{q−j}(−v)`, i.e.
  `E⁺(−v,w₁) E⁻(−u,w₂) = E⁻(−u,w₂) E⁺(−v,w₁) ((1 − w₂/w₁)/(1 + w₂/w₁))^{⟨v,u⟩}`.
* `DD v a` — the coefficient of `wᵃ` in `E⁻(−v,w) E⁺(−v,w)`; `modeT_comm_DD`:
  `[h_i(K/2), DD v a] = vᵢ · DD v (a − K)` for every odd `K`, i.e.
  `[h_i(m), E⁻E⁺(w)] = vᵢ w^{2m} E⁻E⁺(w) = vᵢ z^m E⁻E⁺(z)`.
* Charge conjugation: `sM_neg`, `EpC_neg`, `DD_neg` (`DD (−v) a = (−1)ᵃ DD v a`, i.e.
  `E^±(v, w) = E^±(−v, −w)`); the zero charge: `DD_zero_charge` (`DD 0 a = δ_{a,0}`).

The two-point function and the locality of the dressings are in `LatticeTwistedTwoPoint`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg
open Module (End)
open scoped BigOperators

variable {r : ℕ}

/-- Extending a `range` sum by vanishing terms. -/
theorem _root_.Finset.sum_range_eq_of_vanish' {M : Type*} [AddCommMonoid M] {f : ℕ → M}
    (K K' : ℕ) (hK : K ≤ K') (hf : ∀ i : ℕ, i < K' → K ≤ i → f i = 0) :
    ∑ i ∈ Finset.range K', f i = ∑ i ∈ Finset.range K, f i := by
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hK) fun i hi hni => hf i ?_ ?_
  · simpa using hi
  · simpa using hni

/-! ## Twisted oscillators -/

/-- The bilinear pairing `⟨v, u⟩ = Σ vᵢ uᵢ`. -/
def pair (v u : Fin r → ℂ) : ℂ := ∑ i, v i * u i

theorem pair_comm (v u : Fin r → ℂ) : pair v u = pair u v := by
  unfold pair; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The twisted oscillator `v(k/2) = Σᵢ vᵢ h_i(k/2)`. -/
noncomputable def oscT (v : Fin r → ℂ) (k : ℤ) : End ℂ (FockT r) := ∑ i, v i • modeT r i k

/-- **The twisted oscillator algebra**: `[v(k/2), u(l/2)] = (k/2) ⟨v,u⟩ δ_{k+l,0}`. -/
theorem oscT_comm (v u : Fin r → ℂ) {k l : ℤ} (hk : Odd k) (hl : Odd l) :
    oscT v k * oscT u l - oscT u l * oscT v k
      = (if k + l = 0 then (k : ℂ) / 2 * pair v u else 0) • LinearMap.id := by
  have hA : oscT v k * oscT u l = ∑ i, ∑ j, (v i * u j) • (modeT r i k * modeT r j l) := by
    simp only [oscT, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    rw [Finset.sum_comm]
  have hB : oscT u l * oscT v k = ∑ i, ∑ j, (v i * u j) • (modeT r j l * modeT r i k) := by
    simp only [oscT, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm (u j)]
  rw [hA, hB, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, ← smul_sub, modeT_comm r _ _ hk hl]
  by_cases hkl : k + l = 0
  · simp only [hkl, and_true, if_true, smul_smul]
    have h1 : ∀ x : Fin r, ∑ y, (v x * u y * if x = y then (k : ℂ) / 2 else 0)
        = (k : ℂ) / 2 * (v x * u x) := by
      intro x
      rw [Finset.sum_eq_single x (fun y _ hy => by rw [if_neg (Ne.symm hy), mul_zero])
        (by simp), if_pos rfl]
      ring
    simp only [← Finset.sum_smul, h1, ← Finset.mul_sum, pair]
  · simp [hkl]

/-! ## `E⁻(−v, w)`: the creation exponential -/

/-- The creation variable `v(−n−½) 1 = Σᵢ vᵢ X_{(n,i)}`. -/
noncomputable def vVarT (v : Fin r → ℂ) (n : ℕ) : FockT r := ∑ i, v i • X (n, i)

/-- The logarithmic coefficients of `E⁻(−v, w)`: `2 v(−k/2)` for odd `k`. -/
noncomputable def dM (v : Fin r → ℂ) : ℕ → FockT r :=
  fun k => if k % 2 = 1 then (2 : ℂ) • vVarT v (k / 2) else 0

/-- **`E⁻(−v, w) = Σ_p sM v p · wᵖ`** (multiplication operators). -/
noncomputable def sM (v : Fin r → ℂ) (p : ℕ) : FockT r := nexp (dM v) p

@[simp] theorem sM_zero (v : Fin r → ℂ) : sM v 0 = 1 := nexp_zero _

/-- `sM` extended by `0` to negative indices. -/
noncomputable def sMz (v : Fin r → ℂ) (p : ℤ) : FockT r := if 0 ≤ p then sM v p.toNat else 0

theorem sMz_of_neg (v : Fin r → ℂ) {p : ℤ} (hp : p < 0) : sMz v p = 0 := by
  rw [sMz, if_neg (by omega)]

theorem sMz_natCast (v : Fin r → ℂ) (p : ℕ) : sMz v p = sM v p := by
  rw [sMz, if_pos (by omega), Int.toNat_natCast]

theorem pderiv_vVarT (v : Fin r → ℂ) (n m : ℕ) (i : Fin r) :
    pderiv (n, i) (vVarT v m) = if m = n then C (v i) else 0 := by
  rw [vVarT, map_sum, Finset.sum_eq_single i]
  · rw [smul_eq_C_mul, pderiv_C_mul, pderiv_X, Pi.single_apply]
    by_cases h : m = n
    · subst h; simp
    · rw [if_neg (fun h' => h (Prod.ext_iff.mp h').1), if_neg h, mul_zero]
  · intro j _ hj
    rw [smul_eq_C_mul, pderiv_C_mul, pderiv_X, Pi.single_apply,
      if_neg (fun h' => hj (Prod.ext_iff.mp h').2), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `∂_{(n,i)} sM v p = (2vᵢ/(2n+1)) sM v (p − (2n+1))`. -/
theorem pderiv_sM (v : Fin r → ℂ) (n : ℕ) (i : Fin r) (p : ℕ) :
    pderiv (n, i) (sM v p)
      = if 2 * n + 1 ≤ p then C (2 * v i / (2 * n + 1 : ℂ)) * sM v (p - (2 * n + 1)) else 0 := by
  have h := nexp_derivation (pderiv (n, i)) (dM v) (2 * n + 1) (by omega)
    (C (2 * v i / (2 * n + 1 : ℂ))) (fun k => ?_) p
  · exact h
  · rw [dM]
    split_ifs with h1 h2 h2
    · subst h2
      rw [Derivation.map_smul, show (2 * n + 1) / 2 = n by omega, pderiv_vVarT, if_pos rfl,
        smul_eq_C_mul, smul_eq_C_mul, ← map_mul, ← map_mul]
      congr 1
      have hne : (2 * (n : ℂ) + 1) ≠ 0 := by exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
      push_cast
      field_simp
    · rw [Derivation.map_smul, pderiv_vVarT, if_neg (by omega), smul_zero]
    · omega
    · exact map_zero _

/-! ## `E⁺(−v, w)`: the annihilation exponential as a translation -/

/-- **`E⁺(−v, w)` as the translation** `X_{(n,i)} ↦ X_{(n,i)} − vᵢ u^{2n+1}` (`u = w⁻¹`). -/
noncomputable def Ep (v : Fin r → ℂ) : FockT r →ₐ[ℂ] Polynomial (FockT r) :=
  aeval fun x => Polynomial.C (X x) - v x.2 • Polynomial.X ^ (2 * x.1 + 1)

theorem Ep_X (v : Fin r → ℂ) (x : ℕ × Fin r) :
    Ep v (X x) = Polynomial.C (X x) - v x.2 • Polynomial.X ^ (2 * x.1 + 1) := by
  rw [Ep, aeval_X]

theorem Ep_C (v : Fin r → ℂ) (c : ℂ) : Ep v (C c) = Polynomial.C (C c) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]; rfl

/-- The coefficient `E⁺_q(−v)` of `w^{−q}`, as an endomorphism of `S[θ]`. -/
noncomputable def EpC (v : Fin r → ℂ) (q : ℕ) : End ℂ (FockT r) where
  toFun y := (Ep v y).coeff q
  map_add' a b := by rw [map_add, Polynomial.coeff_add]
  map_smul' c a := by rw [map_smul, Polynomial.coeff_smul]; rfl

theorem EpC_apply (v : Fin r → ℂ) (q : ℕ) (y : FockT r) : EpC v q y = (Ep v y).coeff q := rfl

theorem EpC_mul (v : Fin r → ℂ) (q : ℕ) (a b : FockT r) :
    EpC v q (a * b) = ∑ ij ∈ Finset.antidiagonal q, EpC v ij.1 a * EpC v ij.2 b := by
  rw [EpC_apply, map_mul, Polynomial.coeff_mul]; rfl

theorem EpC_C (v : Fin r → ℂ) (q : ℕ) (c : ℂ) : EpC v q (C c) = if q = 0 then C c else 0 := by
  rw [EpC_apply, Ep_C, Polynomial.coeff_C]

/-- The basic step: `E⁺_q (X_{(n,i)} y) = X_{(n,i)} E⁺_q y − vᵢ E⁺_{q−(2n+1)} y`. -/
theorem EpC_X_mul (v : Fin r → ℂ) (q : ℕ) (x : ℕ × Fin r) (y : FockT r) :
    EpC v q (X x * y) = X x * EpC v q y
      - if 2 * x.1 + 1 ≤ q then v x.2 • EpC v (q - (2 * x.1 + 1)) y else 0 := by
  rw [EpC_apply, map_mul, Ep_X, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    smul_mul_assoc, Polynomial.coeff_smul, Polynomial.coeff_X_pow_mul']
  split_ifs <;> simp [EpC_apply]

theorem EpC_mul_X (v : Fin r → ℂ) (q : ℕ) (x : ℕ × Fin r) (y : FockT r) :
    EpC v q (y * X x) = EpC v q y * X x
      - if 2 * x.1 + 1 ≤ q then v x.2 • EpC v (q - (2 * x.1 + 1)) y else 0 := by
  rw [mul_comm, EpC_X_mul, mul_comm]

/-- `E⁺_0 = id`. -/
theorem EpC_zero_apply (v : Fin r → ℂ) (y : FockT r) : EpC v 0 y = y := by
  induction y using MvPolynomial.induction_on with
  | C c => rw [EpC_C, if_pos rfl]
  | add a b ha hb => rw [map_add, ha, hb]
  | mul_X a x ha => rw [EpC_mul_X, ha, if_neg (by omega), sub_zero]

/-- `E⁺_q` commutes with the partial derivatives (annihilation modes). -/
theorem pderiv_EpC (v : Fin r → ℂ) (x' : ℕ × Fin r) (y : FockT r) :
    ∀ q : ℕ, pderiv x' (EpC v q y) = EpC v q (pderiv x' y) := by
  induction y using MvPolynomial.induction_on with
  | C c => intro q; rw [EpC_C, pderiv_C]; split_ifs <;> simp
  | add a b ha hb => intro q; rw [map_add, map_add, ha, hb, map_add, map_add]
  | mul_X a x ha =>
    intro q
    have hd : pderiv x' (X x : FockT r) = if x' = x then 1 else 0 := by
      rw [pderiv_X, Pi.single_apply]
      by_cases h : x' = x
      · subst h; simp
      · rw [if_neg (Ne.symm h), if_neg h]
    rw [EpC_mul_X, map_sub, Derivation.leibniz, Derivation.leibniz, hd, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_add, EpC_X_mul]
    simp only [← ha]
    by_cases hx : x' = x
    · simp only [if_pos hx, mul_one]
      split_ifs with hq
      · rw [Derivation.map_smul]; abel
      · simp
    · simp only [if_neg hx, mul_zero, map_zero, zero_add]
      split_ifs with hq
      · rw [Derivation.map_smul, mul_comm]
      · simp

/-- `E⁺_q(−v)` and `E⁺_{q'}(−u)` commute (translations commute). -/
theorem EpC_comm (v u : Fin r → ℂ) (y : FockT r) :
    ∀ q q' : ℕ, EpC v q (EpC u q' y) = EpC u q' (EpC v q y) := by
  induction y using MvPolynomial.induction_on with
  | C c =>
    intro q q'
    simp only [EpC_C]
    split_ifs <;> simp [EpC_C, *]
  | add a b ha hb => intro q q'; rw [map_add, map_add, ha, hb, map_add, map_add]
  | mul_X a x ha =>
    intro q q'
    rw [EpC_mul_X u q' x a, map_sub, EpC_mul_X v q x (EpC u q' a), EpC_mul_X v q x a, map_sub,
      EpC_mul_X u q' x (EpC v q a)]
    split_ifs with h1 h2 h2
    · rw [map_smul, map_smul]; simp only [ha]; abel
    · rw [map_smul]; simp only [ha]; simp
    · rw [map_smul]; simp only [ha]; simp
    · simp only [ha]; simp

/-- Lower truncation of `E⁺(−v, w)`: for each `y`, `E⁺_q y = 0` for `q ≫ 0`. -/
theorem EpC_eventually_zero (v : Fin r → ℂ) (y : FockT r) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → EpC v q y = 0 :=
  ⟨(Ep v y).natDegree + 1, fun q hq => by
    rw [EpC_apply]; exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)⟩

/-! ## The `E⁺E⁻` reordering -/

theorem Ep_vVarT (v u : Fin r → ℂ) (m : ℕ) :
    Ep v (vVarT u m) = Polynomial.C (vVarT u m) - pair v u • Polynomial.X ^ (2 * m + 1) := by
  rw [vVarT, map_sum, map_sum, pair, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Ep_X, smul_sub, mul_comm, mul_smul, Polynomial.smul_C, smul_comm (u i)]

theorem Ep_dM (v u : Fin r → ℂ) (k : ℕ) :
    Ep v (dM u k) = Polynomial.CAlgHom (R := ℂ) (dM u k)
      + Polynomial.X ^ k * algebraMap ℂ (Polynomial (FockT r)) (((-2 * pair v u) • oddc) k) := by
  rw [dM, Pi.smul_apply, oddc]
  split_ifs with h
  · rw [map_smul, Ep_vVarT, Polynomial.CAlgHom_apply, smul_eq_mul, mul_one,
      show 2 * (k / 2) + 1 = k by omega, smul_sub, Polynomial.smul_C,
      Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, mul_one, smul_smul]
    ring_nf
    rw [sub_eq_add_neg, ← neg_smul]
  · simp

/-- **`E⁺(−v)` applied to `E⁻(−u)`**:
`Ep v (sM u p) = Σ_{i+j=p} sM u i · fco(⟨v,u⟩)_j u^j`. -/
theorem Ep_sM (v u : Fin r → ℂ) (p : ℕ) :
    Ep v (sM u p) = ∑ ij ∈ Finset.antidiagonal p,
      Polynomial.C (sM u ij.1) * (fco (pair v u) ij.2 • Polynomial.X ^ ij.2) := by
  have h1 : (fun k => Ep v (dM u k)) = (fun k => Polynomial.CAlgHom (R := ℂ) (dM u k))
      + fun k => Polynomial.X ^ k *
          algebraMap ℂ (Polynomial (FockT r)) (((-2 * pair v u) • oddc) k) := by
    funext k; rw [Ep_dM]; rfl
  rw [sM, nexp_map, h1, ← coeff_nexpPS, nexpPS_add, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij _ => ?_
  have hA := nexp_map (Algebra.ofId ℂ (Polynomial (FockT r))) ((-2 * pair v u) • oddc) ij.2
  simp only [Algebra.ofId_apply] at hA
  rw [coeff_nexpPS, coeff_nexpPS, ← nexp_map, nexp_scale, ← hA]
  rw [Polynomial.CAlgHom_apply, Algebra.algebraMap_eq_smul_one, fco, mul_smul_comm, mul_one]
  rfl

/-- **The `E⁺E⁻` reordering, coefficient form**: for every `p : ℤ`,
`E⁺_q(−v) (E⁻_p(−u) y) = Σ_{j ≤ q} fco(⟨v,u⟩)_j E⁻_{p−j}(−u) E⁺_{q−j}(−v) y`. -/
theorem EpC_sMz_mul (v u : Fin r → ℂ) (q : ℕ) (p : ℤ) (y : FockT r) :
    EpC v q (sMz u p * y) = ∑ j ∈ Finset.range (q + 1),
      fco (pair v u) j • (sMz u (p - j) * EpC v (q - j) y) := by
  by_cases hp : p < 0
  · rw [sMz_of_neg u hp, zero_mul, map_zero]
    exact (Finset.sum_eq_zero fun j _ => by rw [sMz_of_neg u (by omega), zero_mul, smul_zero]).symm
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = P := ⟨p.toNat, by omega⟩
  set G : ℕ → FockT r := fun j => fco (pair v u) j • (sMz u ((P : ℤ) - j) * EpC v (q - j) y)
    with hG
  have hGv : ∀ j, P < j → G j = 0 := fun j hj => by
    simp only [hG]; rw [sMz_of_neg u (by omega), zero_mul, smul_zero]
  rw [sMz_natCast, EpC_apply, map_mul, Ep_sM, Finset.sum_mul, Polynomial.finsetSum_coeff]
  have hterm : ∀ ij ∈ Finset.antidiagonal P,
      (Polynomial.C (sM u ij.1) * (fco (pair v u) ij.2 • Polynomial.X ^ ij.2) * Ep v y).coeff q
        = if ij.2 ≤ q then G ij.2 else 0 := by
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    simp only [hG]
    rw [mul_assoc, Polynomial.coeff_C_mul, smul_mul_assoc, Polynomial.coeff_smul,
      Polynomial.coeff_X_pow_mul', show ((P : ℤ) - ij.2) = ((ij.1 : ℕ) : ℤ) by omega, sMz_natCast]
    split_ifs <;> simp [EpC_apply]
  rw [Finset.sum_congr rfl hterm,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun _ j => if j ≤ q then G j else 0) P,
    ← Finset.sum_range_reflect]
  have e1 : ∑ j ∈ Finset.range (P + 1), (if P - (P + 1 - 1 - j) ≤ q then G (P - (P + 1 - 1 - j))
      else 0) = ∑ j ∈ Finset.range (P + 1), (if j ≤ q then G j else 0) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_range] at hj; rw [show P - (P + 1 - 1 - j) = j by omega]
  rw [e1, Finset.sum_range_eq_of_vanish' (min P q + 1) (P + 1) (by omega)
      (fun j _ hj => by rw [if_neg (by omega)]),
    Finset.sum_range_eq_of_vanish' (min P q + 1) (q + 1) (by omega)
      (fun j hj1 hj => hGv j (by omega))]
  exact Finset.sum_congr rfl fun j hj => by rw [Finset.mem_range] at hj; rw [if_pos (by omega)]

/-! ## The normal-ordered dressing `E⁻(−v,w) E⁺(−v,w)` -/

/-- **The coefficient of `wᵃ` in `E⁻(−v, w) E⁺(−v, w)`**:
`DD v a = Σ_{p − q = a} E⁻_p(−v) E⁺_q(−v)`. -/
noncomputable def DD (v : Fin r → ℂ) (a : ℤ) : End ℂ (FockT r) :=
  Polynomial.lsum (fun q => LinearMap.mulLeft ℂ (sMz v (a + q))) ∘ₗ (Ep v).toLinearMap

/-- `DD` as an explicit finite sum, with any bound past the `E⁺` coefficients. -/
theorem DD_apply_range (v : Fin r → ℂ) (a : ℤ) (y : FockT r) (Q : ℕ)
    (hQ : ∀ q : ℕ, Q ≤ q → EpC v q y = 0) :
    DD v a y = ∑ q ∈ Finset.range Q, sMz v (a + q) * EpC v q y := by
  change (Ep v y).sum (fun q c => sMz v (a + q) * c) = _
  rw [Polynomial.sum_over_range' _ (fun n => mul_zero _) (max Q ((Ep v y).natDegree + 1))
    (by omega)]
  refine Finset.sum_range_eq_of_vanish' Q _ (le_max_left _ _) fun q _ hq => ?_
  change sMz v (a + q) * EpC v q y = 0
  rw [hQ q hq, mul_zero]

theorem pderiv_sMz (v : Fin r → ℂ) (n : ℕ) (i : Fin r) (p : ℤ) :
    pderiv (n, i) (sMz v p) = C (2 * v i / (2 * n + 1 : ℂ)) * sMz v (p - (2 * n + 1)) := by
  by_cases hp : p < 0
  · rw [sMz_of_neg v hp, sMz_of_neg v (by omega), map_zero, mul_zero]
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = P := ⟨p.toNat, by omega⟩
  rw [sMz_natCast, pderiv_sM]
  split_ifs with h
  · rw [show (P : ℤ) - (2 * n + 1) = ((P - (2 * n + 1) : ℕ) : ℤ) by omega, sMz_natCast]
  · rw [sMz_of_neg v (by omega), mul_zero]

/-- The annihilation modes against the dressing:
`∂(DD a y) = DD a (∂y) + (2vᵢ/(2n+1)) DD (a−(2n+1)) y`. -/
theorem pderiv_DD (v : Fin r → ℂ) (n : ℕ) (i : Fin r) (a : ℤ) (y : FockT r) :
    pderiv (n, i) (DD v a y) = DD v a (pderiv (n, i) y)
      + C (2 * v i / (2 * n + 1 : ℂ)) * DD v (a - (2 * n + 1)) y := by
  obtain ⟨Q, hQ⟩ := EpC_eventually_zero v y
  have hQ' : ∀ q, Q ≤ q → EpC v q (pderiv (n, i) y) = 0 := fun q hq => by
    rw [← pderiv_EpC, hQ q hq, map_zero]
  rw [DD_apply_range v a y Q hQ, DD_apply_range v a _ Q hQ', DD_apply_range v _ y Q hQ, map_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Derivation.leibniz, pderiv_sMz, pderiv_EpC, smul_eq_mul, smul_eq_mul,
    show a - (2 * n + 1) + q = a + q - (2 * n + 1) by ring]
  ring

/-- The creation modes against the dressing: `DD a (X y) = X · DD a y − vᵢ DD (a + 2n+1) y`. -/
theorem DD_X_mul (v : Fin r → ℂ) (x : ℕ × Fin r) (a : ℤ) (y : FockT r) :
    DD v a (X x * y) = X x * DD v a y - v x.2 • DD v (a + (2 * x.1 + 1)) y := by
  obtain ⟨Q, hQ⟩ := EpC_eventually_zero v y
  set k := 2 * x.1 + 1 with hk
  have hQX : ∀ q, k + Q ≤ q → EpC v q (X x * y) = 0 := fun q hq => by
    rw [EpC_X_mul, hQ q (by omega), mul_zero, zero_sub, if_pos (by omega), hQ _ (by omega),
      smul_zero, neg_zero]
  rw [DD_apply_range v a _ (k + Q) hQX, DD_apply_range v a y (k + Q) (fun q hq => hQ q (by omega)),
    DD_apply_range v _ y Q hQ, Finset.mul_sum, Finset.smul_sum]
  simp only [EpC_X_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun q _ => by ring
  · rw [Finset.sum_range_add]
    rw [Finset.sum_eq_zero (fun q hq => by
      rw [Finset.mem_range] at hq; rw [if_neg (by omega), mul_zero]), zero_add]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [if_pos (by omega), show k + q - k = q by omega, mul_smul_comm]
    congr 3
    rw [hk]; push_cast; ring

/-- **The twisted oscillators against the dressing**: for every odd `K`,
`[h_i(K/2), DD v a] = vᵢ · DD v (a − K)`, i.e. `[h_i(m), E⁻E⁺(−v, w)] = vᵢ w^{2m} E⁻E⁺(−v, w)`. -/
theorem modeT_comm_DD (v : Fin r → ℂ) (i : Fin r) {K : ℤ} (hK : Odd K) (a : ℤ) :
    modeT r i K * DD v a - DD v a * modeT r i K = v i • DD v (a - K) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply]
  rcases lt_or_gt_of_ne (show K ≠ 0 by rintro rfl; simp at hK) with hneg | hpos
  · -- creation
    rw [modeT_apply_neg r i hK hneg, modeT_apply_neg r i hK hneg, DD_X_mul]
    have : varT i K = (((-K - 1) / 2).toNat, i) := by
      simp only [varT, abs_of_neg hneg]
    rw [this]
    simp only
    have e : a + (2 * (((-K - 1) / 2).toNat : ℤ) + 1) = a - K := by
      obtain ⟨m, hm⟩ := hK; omega
    rw [e]
    abel
  · -- annihilation
    obtain ⟨n, hn⟩ : ∃ n : ℕ, K = 2 * n + 1 := ⟨(K / 2).toNat, by obtain ⟨m, hm⟩ := hK; omega⟩
    subst hn
    rw [modeT_annihilation, modeT_annihilation, map_smul, pderiv_DD, smul_add, add_sub_cancel_left,
      smul_eq_C_mul, smul_eq_C_mul, ← mul_assoc, ← map_mul]
    have hne : (2 * (n : ℂ) + 1) ≠ 0 := by exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
    congr 2
    push_cast
    field_simp

/-! ## Charge conjugation `v ↦ −v` -/

theorem vVarT_neg (v : Fin r → ℂ) (m : ℕ) : vVarT (-v) m = -vVarT v m := by
  simp [vVarT, neg_smul, Finset.sum_neg_distrib]

theorem dM_neg (v : Fin r → ℂ) (k : ℕ) : dM (-v) k = (-1 : FockT r) ^ k * dM v k := by
  unfold dM
  split_ifs with h
  · rw [vVarT_neg, smul_neg, Odd.neg_one_pow (Nat.odd_iff.mpr h), neg_one_mul]
  · rw [mul_zero]

/-- `E⁻(v, w) = E⁻(−v, −w)`: `sM (−v) p = (−1)ᵖ sM v p`. -/
theorem sM_neg (v : Fin r → ℂ) (p : ℕ) : sM (-v) p = (-1 : FockT r) ^ p * sM v p := by
  rw [sM, show dM (-v) = fun k => (-1 : FockT r) ^ k * dM v k from funext (dM_neg v), nexp_scale]
  rfl

theorem sMz_neg (v : Fin r → ℂ) (p : ℤ) : sMz (-v) p = (-1 : ℂ) ^ p • sMz v p := by
  by_cases hp : p < 0
  · rw [sMz_of_neg _ hp, sMz_of_neg _ hp, smul_zero]
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = P := ⟨p.toNat, by omega⟩
  rw [sMz_natCast, sMz_natCast, sM_neg, zpow_natCast, ← smul_eq_mul, neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two (R := ℂ)]
  rcases Nat.mod_two_eq_zero_or_one P with h | h <;> simp [h]

/-- `E⁺(v, w) = E⁺(−v, −w)`: `E⁺_q(v) = (−1)^q E⁺_q(−v)`. -/
theorem EpC_neg (v : Fin r → ℂ) (y : FockT r) :
    ∀ q : ℕ, EpC (-v) q y = (-1 : ℂ) ^ q • EpC v q y := by
  induction y using MvPolynomial.induction_on with
  | C c => intro q; rw [EpC_C, EpC_C]; split_ifs with h <;> simp [h]
  | add a b ha hb => intro q; rw [map_add, map_add, ha, hb, smul_add]
  | mul_X a x ha =>
    intro q
    rw [EpC_mul_X, EpC_mul_X, ha, smul_sub, smul_mul_assoc]
    congr 1
    split_ifs with h
    · rw [ha, Pi.neg_apply, smul_smul, smul_smul]
      congr 1
      obtain ⟨d, hd⟩ : ∃ d, q = d + (2 * x.1 + 1) := ⟨q - (2 * x.1 + 1), by omega⟩
      rw [hd, Nat.add_sub_cancel, pow_add, Odd.neg_one_pow ⟨x.1, rfl⟩]
      ring
    · rw [smul_zero]

/-- `DD (−v) a = (−1)ᵃ DD v a`: the dressing is odd/even under `w ↦ −w`. -/
theorem DD_neg (v : Fin r → ℂ) (a : ℤ) : DD (-v) a = (-1 : ℂ) ^ a • DD v a := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨Q, hQ⟩ := EpC_eventually_zero v y
  rw [LinearMap.smul_apply, DD_apply_range (-v) a y Q (fun q hq => by rw [EpC_neg, hQ q hq,
    smul_zero]), DD_apply_range v a y Q hQ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [sMz_neg, EpC_neg, smul_mul_smul_comm, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast,
    mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]

/-! ## The zero charge -/

theorem sM_zero_charge (p : ℕ) : sM (0 : Fin r → ℂ) p = if p = 0 then 1 else 0 := by
  have h0 : dM (0 : Fin r → ℂ) = 0 := by
    funext k; simp [dM, vVarT]
  rw [sM, h0, ← coeff_nexpPS, nexpPS_zero, PowerSeries.coeff_one]

theorem EpC_zero_charge (y : FockT r) :
    ∀ q : ℕ, EpC (0 : Fin r → ℂ) q y = if q = 0 then y else 0 := by
  induction y using MvPolynomial.induction_on with
  | C c => intro q; rw [EpC_C]
  | add a b ha hb => intro q; rw [map_add, ha, hb]; split_ifs <;> simp
  | mul_X a x ha =>
    intro q
    rw [EpC_mul_X, ha]
    split_ifs <;> simp

/-- `DD 0 a = δ_{a,0}`: the dressing of the zero charge is trivial. -/
theorem DD_zero_charge (a : ℤ) : DD (0 : Fin r → ℂ) a = if a = 0 then 1 else 0 := by
  refine LinearMap.ext fun y => ?_
  rw [DD_apply_range 0 a y 1 (fun q hq => by rw [EpC_zero_charge, if_neg (by omega)]),
    Finset.sum_range_one, EpC_zero_charge, if_pos rfl, Nat.cast_zero, add_zero, sMz]
  by_cases h0 : a = 0
  · subst h0; simp
  · rw [if_neg h0]
    split_ifs with h1
    · rw [sM_zero_charge, if_neg (by omega), zero_mul]; rfl
    · rw [zero_mul]; rfl

end VOA.Moonshine.LatticeTwisted
