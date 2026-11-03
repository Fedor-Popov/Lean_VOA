/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.LocalSystemJacobi
import VOA.Moonshine.HeisenbergTwistedModuleDefect
import Mathlib.RingTheory.Binomial

/-!
# Twisted Jacobi from untwisted locality: the rescaling reduction  (Moonshine step M6a)

For a fractional-mode map `YM u k = u₍k/N₎` and an offset `e : ℤ`, the **rescaled field**
`resc (YM u) N e` is the integral-moded field with `p`-th mode `u₍(Np+e)/N₎`; as a generating
series it is `z^{e/N} Y_M(u, z^{?})` after the substitution that clears the fractional exponents
of the residue class `e + Nℤ`.  The DLM twisted Jacobi identity for a pair `(u, v)`, on the
residue classes `k ∈ e + Nℤ`, `m ∈ e' + Nℤ`, is then *exactly* the ordinary two-sorted Borcherds
identity of the two rescaled fields (`Fld.field_jacobi_of_local`, Li's local-system layer), once
their integer field products are identified by the **twisted product formula**

  `(Ã₍ℓ₎B̃)₍ₛ₎ = Σ_{t ≥ 0} C(e/N, t) · Y_M(u₍ℓ₊ₜ₎v)₍(N(s−t)+e+e')/N₎`,

i.e. `Σ_ℓ (Ã₍ℓ₎B̃)(z₂) z₀^{−ℓ−1} = (1 + z₀/z₂)^{e/N} Ỹ(Y(u,z₀)v, z₂)`.  The fractional binomial
`C(k/N, i)` of the twisted Jacobi identity is recovered from `C(m, i)` of the untwisted one by the
complex Chu–Vandermonde identity `C(m + e/N, s) = Σ_{i+t=s} C(m,i) C(e/N,t)` (`cbinom_add`).

## Main results
* `resc`, `mode_resc`, `resc_isField`, `rescFld` — the rescaled fields.
* `cbinom_eq_ringChoose`, `cbinom_add` — `cbinom` is Mathlib's `Ring.choose`, and Vandermonde.
* `pf_of_inverse` — binomial inversion: the inverse formula `Q ℓ = Σᵢ C(−c,i) z^{−i} P(ℓ+i)`
  implies the product formula `P ℓ = Σₜ C(c,t) z^{−t} Q(ℓ+t)` (for families vanishing at large
  `ℓ`), via `C(c + (−c), k) = δ_{k0}`.
* `twisted_jacobi_of_local_pf` — **per pair `(u,v)` and residue classes `(e,e')`: untwisted
  locality of the rescaled fields + the twisted product formula ⇒ the twisted Jacobi identity at
  every `ℓ`, `k = Nm + e`, `m' = Nn + e'`.**
* `twisted_jacobi_of_local_pf_ge` — the same at a fixed `ℓ`, using the product formula only at
  `ℓ' ≥ ℓ` (so `ℓ ≥ 0` needs only the nonnegative, commutator, products).
* `twistedJacobi_of_local_pf` — the assembled form: given offsets `off j ≡ −j (mod N)`, if for
  every `u ∈ 𝒱ʲ` and every `v` the rescaled fields of offsets `off j` and `e' ∈ [0, N)` are local
  and satisfy the product formula, then `TwistedJacobi g N YM` holds.

This is a reduction, not an existence theorem: both hypotheses are consequences of the twisted
Jacobi identity, so they are the honest *targets* for a concrete twisted module.  Their content
for the Moonshine twisted Heisenberg module is the open part of M6.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

namespace TwistedReduction

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Fractional binomials -/

/-- `cbinom` is Mathlib's binomial-ring `Ring.choose` on `ℂ`. -/
theorem cbinom_eq_ringChoose (x : ℂ) (n : ℕ) : cbinom x n = Ring.choose x n := by
  rw [Ring.choose_eq_smul, ← Polynomial.eval₂_smulOneHom_eq_smeval,
    show (RingHom.smulOneHom : ℤ →+* ℂ) = Int.castRingHom ℂ from RingHom.ext_int _ _,
    ← Polynomial.eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range, cbinom,
    smul_eq_mul, div_eq_inv_mul]

/-- **Chu–Vandermonde** for the complex binomial `cbinom`. -/
theorem cbinom_add (x y : ℂ) (s : ℕ) :
    cbinom (x + y) s = ∑ ij ∈ Finset.antidiagonal s, cbinom x ij.1 * cbinom y ij.2 := by
  simp only [cbinom_eq_ringChoose]
  exact Ring.add_choose_eq s (Commute.all x y)

/-- The integer binomial `cbz m i` (`i ≥ 0`) is `cbinom (m : ℂ) i`. -/
theorem cbz_natCast (m : ℤ) (i : ℕ) : cbz m (i : ℤ) = cbinom (m : ℂ) i := by
  rw [cbz_apply_nonneg m (by positivity), Int.toNat_natCast]
  rfl

/-! ## Rescaled fields -/

/-- **The rescaled field** of a fractional-mode family `A k = u₍k/N₎` on the residue class
`e + Nℤ`: the integral-moded distribution whose `p`-th mode is `A (N p + e)`. -/
def resc (A : ℤ → End ℂ M) (N : ℕ) (e : ℤ) : FormalDist (End ℂ M) :=
  fun n => A (N * (-n - 1) + e)

@[simp] theorem mode_resc (A : ℤ → End ℂ M) (N : ℕ) (e p : ℤ) :
    mode (resc A N e) p = A (N * p + e) := by
  rw [mode_apply, resc]
  congr 1
  ring

/-- A lower-truncated fractional family gives a field. -/
theorem resc_isField {A : ℤ → End ℂ M} {N : ℕ} (hN : 0 < N)
    (htr : ∀ x : M, ∃ K : ℤ, ∀ k : ℤ, K ≤ k → A k x = 0) (e : ℤ) : IsField (resc A N e) := by
  intro x
  obtain ⟨K, hK⟩ := htr x
  refine ⟨-(K.natAbs : ℤ) - (e.natAbs : ℤ) - 1, fun n hn => hK _ ?_⟩
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have h1 : (0 : ℤ) ≤ -n - 1 := by omega
  have h2 : -n - 1 ≤ (N : ℤ) * (-n - 1) := le_mul_of_one_le_left h1 hN'
  rcases Int.natAbs_eq K with hK' | hK' <;> rcases Int.natAbs_eq e with he | he <;> omega

/-- The rescaled field as an element of the field space `Fld M`. -/
def rescFld {A : ℤ → End ℂ M} {N : ℕ} (hN : 0 < N)
    (htr : ∀ x : M, ∃ K : ℤ, ∀ k : ℤ, K ≤ k → A k x = 0) (e : ℤ) : Fld M :=
  ⟨resc A N e, resc_isField hN htr e⟩

@[simp] theorem rescFld_val {A : ℤ → End ℂ M} {N : ℕ} (hN : 0 < N)
    (htr : ∀ x : M, ∃ K : ℤ, ∀ k : ℤ, K ≤ k → A k x = 0) (e : ℤ) :
    (rescFld hN htr e).1 = resc A N e := rfl

/-! ## Finite resummation -/

omit [Module ℂ M] in
/-- Regrouping a square double sum along antidiagonals, when the summand vanishes off the
triangle `i + t < L`. -/
theorem sum_range_sq_eq_sum_antidiagonal (L : ℕ) (f : ℕ → ℕ → M)
    (hf : ∀ i t, L ≤ i + t → f i t = 0) :
    ∑ i ∈ Finset.range L, ∑ t ∈ Finset.range L, f i t
      = ∑ s ∈ Finset.range L, ∑ p ∈ Finset.antidiagonal s, f p.1 p.2 := by
  classical
  rw [← Finset.sum_product', Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => (x.2.1, x.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨s, i, t⟩ hx _
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hx
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  · rintro ⟨s, i, t⟩ hx _ ⟨s', i', t'⟩ hx' _ h
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx hx'
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : s = s' := by omega
    subst this
    rfl
  · rintro ⟨i, t⟩ hx hne
    simp only [Finset.mem_product, Finset.mem_range] at hx
    have hlt : i + t < L := by
      by_contra hc
      exact hne (hf i t (by omega))
    exact ⟨⟨i + t, i, t⟩, by simp [hlt], hne, rfl⟩
  · intro x _ _
    rfl

omit [Module ℂ M] in
/-- An integer-indexed `finsum` vanishing off `[0, L)` is the corresponding `range` sum. -/
theorem finsum_int_eq_sum_range (L : ℕ) (f : ℤ → M)
    (hf : ∀ i : ℤ, f i ≠ 0 → 0 ≤ i ∧ i < L) :
    ∑ᶠ i : ℤ, f i = ∑ i ∈ Finset.range L, f i := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := (Finset.range L).map Nat.castEmbedding) ?_,
    Finset.sum_map]
  · rfl
  · intro i hi
    obtain ⟨h0, hL⟩ := hf i hi
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Nat.castEmbedding_apply]
    exact ⟨i.toNat, by omega, by omega⟩

omit [Module ℂ M] in
/-- A natural-indexed `finsum` vanishing off `[0, L)` is the corresponding `range` sum. -/
theorem finsum_nat_eq_sum_range (L : ℕ) (f : ℕ → M) (hf : ∀ i : ℕ, L ≤ i → f i = 0) :
    ∑ᶠ i : ℕ, f i = ∑ i ∈ Finset.range L, f i := by
  refine finsum_eq_sum_of_support_subset f fun i hi => ?_
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hi (hf i (by omega))

/-! ## Binomial inversion of the product formula -/

/-- `C(0, k) = δ_{k,0}`. -/
theorem cbinom_zero_left (k : ℕ) : cbinom 0 k = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [if_neg hk.ne', cbinom, Finset.prod_eq_zero (Finset.mem_range.mpr hk) (by simp), zero_div]

omit [Module ℂ M] in
/-- A `ℕ`-indexed `finsum` of a family vanishing off `[0, K)`, regrouped as a `range` sum. -/
private theorem finsum_nat_range (K : ℕ) (f : ℕ → M) (hf : ∀ i, K ≤ i → f i = 0) :
    ∑ᶠ i : ℕ, f i = ∑ i ∈ Finset.range K, f i := finsum_nat_eq_sum_range K f hf

/-- **Binomial inversion of the twisted product formula.**  For two `ℤ × ℤ`-indexed families
vanishing for `ℓ ≥ L`, the inverse formula `Q ℓ s = Σᵢ C(−c, i) P (ℓ+i) (s−i)` implies the
product formula `P ℓ s = Σₜ C(c, t) Q (ℓ+t) (s−t)` (and, replacing `c` by `−c`, conversely).
This is how a definition of the twisted vertex operator by the *inverse* formula
(`Moonshine.Ywt`) feeds `twisted_jacobi_of_local_pf`. -/
theorem pf_of_inverse (c : ℂ) (P Q : ℤ → ℤ → M) (L : ℤ)
    (hP : ∀ ℓ s, L ≤ ℓ → P ℓ s = 0) (hQ : ∀ ℓ s, L ≤ ℓ → Q ℓ s = 0)
    (hinv : ∀ ℓ s, Q ℓ s = ∑ᶠ i : ℕ, cbinom (-c) i • P (ℓ + i) (s - i)) (ℓ s : ℤ) :
    P ℓ s = ∑ᶠ t : ℕ, cbinom c t • Q (ℓ + t) (s - t) := by
  set K : ℕ := (L - ℓ).toNat with hK
  rw [finsum_nat_range K _ (fun t ht => by rw [hQ _ _ (by omega), smul_zero])]
  have hQ' : ∀ t : ℕ, Q (ℓ + t) (s - t)
      = ∑ i ∈ Finset.range K, cbinom (-c) i • P (ℓ + t + i) (s - t - i) := by
    intro t
    rw [hinv, finsum_nat_range K _ (fun i hi => by rw [hP _ _ (by omega), smul_zero])]
  simp_rw [hQ', Finset.smul_sum, smul_smul]
  rw [sum_range_sq_eq_sum_antidiagonal K
    (fun t i => (cbinom c t * cbinom (-c) i) • P (ℓ + t + i) (s - t - i))
    (fun t i h => by
      change (cbinom c t * cbinom (-c) i) • P (ℓ + t + i) (s - t - i) = 0
      rw [hP _ _ (by omega), smul_zero])]
  have hk : ∀ k ∈ Finset.range K, (∑ p ∈ Finset.antidiagonal k,
      (cbinom c p.1 * cbinom (-c) p.2) • P (ℓ + p.1 + p.2) (s - p.1 - p.2))
      = (if k = 0 then (1 : ℂ) else 0) • P (ℓ + k) (s - k) := by
    intro k _
    rw [← cbinom_zero_left, ← add_neg_cancel c, cbinom_add, Finset.sum_smul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [← hp]
    congr 2 <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hk]
  rcases Nat.eq_zero_or_pos K with h0 | hpos
  · rw [h0, Finset.sum_range_zero]
    exact hP _ _ (by omega)
  · rw [Finset.sum_eq_single 0 (fun k _ hk => by rw [if_neg hk, zero_smul])
      (fun h => absurd (Finset.mem_range.mpr hpos) h)]
    simp

/-! ## The reduction -/

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Twisted Jacobi from untwisted locality and the twisted product formula** (one pair,
fixed residue classes).  Let `Ã`, `B̃` be the rescaled fields of `u` and `v` on the classes
`e + Nℤ` and `e' + Nℤ`.  If they are mutually local and their integer products are given by the
twisted product formula, then the DLM twisted Jacobi identity holds for `(u, v)` at every
`ℓ ∈ ℤ`, `k = N m + e`, `m' = N n + e'`. -/
theorem twisted_jacobi_of_local_pf_ge (W : VertexOperatorAlgebra 𝒱)
    (YM : 𝒱 →ₗ[ℂ] (ℤ → End ℂ M))
    {N : ℕ} (hN : 0 < N) (htr : ∀ (u : 𝒱) (x : M), ∃ K : ℤ, ∀ k : ℤ, K ≤ k → YM u k x = 0)
    (u v : 𝒱) (e e' : ℤ)
    (hloc : Local (resc (YM u) N e) (resc (YM v) N e')) (ℓ : ℤ)
    (hpf : ∀ (ℓ' s : ℤ) (x : M), ℓ ≤ ℓ' →
      mode (Fld.prod ℓ' (rescFld hN (htr u) e) (rescFld hN (htr v) e')).1 s x
        = ∑ᶠ t : ℕ, cbinom ((e : ℂ) / N) t •
            YM (W.smul u (ℓ' + t) v) (N * (s - t) + e + e') x)
    (x : M) (m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (YM u (ℓ * N + (N * m + e) - i * N) (YM v ((N * n + e') + i * N) x)
          - negOnePow ℓ • YM v (ℓ * N + (N * n + e') - i * N) (YM u ((N * m + e) + i * N) x)))
      = ∑ᶠ i : ℕ, cbinom (((N * m + e : ℤ) : ℂ) / N) i •
          YM (W.smul u (ℓ + i) v) ((N * m + e) + (N * n + e') - i * N) x := by
  have hJ := Fld.field_jacobi_of_local (a := rescFld hN (htr u) e) (b := rescFld hN (htr v) e')
    hloc x ℓ m n
  simp only [rescFld_val, mode_resc] at hJ
  -- the left sides agree up to index arithmetic
  have hL : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (YM u (ℓ * N + (N * m + e) - i * N) (YM v ((N * n + e') + i * N) x)
          - negOnePow ℓ • YM v (ℓ * N + (N * n + e') - i * N) (YM u ((N * m + e) + i * N) x)))
      = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (YM u (N * (ℓ + m - i) + e) (YM v (N * (n + i) + e') x)
          - negOnePow ℓ • YM v (N * (ℓ + n - i) + e') (YM u (N * (m + i) + e) x)) := by
    refine finsum_congr fun i => ?_
    rw [show ℓ * N + (N * m + e) - i * N = N * (ℓ + m - i) + e by ring,
      show (N * n + e') + i * N = N * (n + i) + e' by ring,
      show ℓ * N + (N * n + e') - i * N = N * (ℓ + n - i) + e' by ring,
      show (N * m + e) + i * N = N * (m + i) + e by ring]
  rw [hL, hJ]
  -- the right side: resum the two binomial expansions with Vandermonde
  obtain ⟨K, hK⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  set L : ℕ := (K - ℓ).toNat with hLdef
  set Y : ℕ → M := fun s => YM (W.smul u (ℓ + s) v) (N * (m + n - s) + e + e') x with hYdef
  have hY : ∀ s : ℕ, L ≤ s → Y s = 0 := by
    intro s hs
    simp only [hYdef]
    rw [hK (ℓ + s) (by omega), map_zero]
    rfl
  set c : ℂ := (e : ℂ) / N
  -- inner expansions
  have hinner : ∀ i : ℕ, mode (Fld.prod (ℓ + i) (rescFld hN (htr u) e)
      (rescFld hN (htr v) e')).1 (m + n - i) x
        = ∑ t ∈ Finset.range L, cbinom c t • Y (i + t) := by
    intro i
    rw [hpf _ _ _ (by omega), finsum_nat_eq_sum_range L _ (fun t ht => ?_)]
    · refine Finset.sum_congr rfl fun t _ => ?_
      simp only [hYdef]
      rw [show ℓ + (i : ℤ) + (t : ℤ) = ℓ + ((i + t : ℕ) : ℤ) by push_cast; ring,
        show m + n - (i : ℤ) - (t : ℤ) = m + n - ((i + t : ℕ) : ℤ) by push_cast; ring]
    · rw [show (ℓ + (i : ℤ) + (t : ℤ)) = ℓ + ((i + t : ℕ) : ℤ) by push_cast; ring,
        hK _ (by omega), map_zero]
      simp
  rw [finsum_int_eq_sum_range L _ (fun i hi => ?_)]
  · -- convert to the double sum and regroup
    have hcast : ∀ i : ℕ, (cbz m (i : ℤ) • mode (Fld.prod (ℓ + (i : ℤ)) (rescFld hN (htr u) e)
        (rescFld hN (htr v) e')).1 (m + n - (i : ℤ)) x)
          = ∑ t ∈ Finset.range L, (cbinom (m : ℂ) i * cbinom c t) • Y (i + t) := by
      intro i
      rw [hinner i, cbz_natCast, Finset.smul_sum]
      exact Finset.sum_congr rfl fun t _ => by rw [smul_smul]
    simp_rw [hcast]
    rw [sum_range_sq_eq_sum_antidiagonal L _ (fun i t h => by rw [hY _ h, smul_zero])]
    rw [finsum_nat_eq_sum_range L _ (fun s hs => ?_)]
    · refine Finset.sum_congr rfl fun s _ => ?_
      have hc : (((N * m + e : ℤ) : ℂ) / N) = (m : ℂ) + c := by
        have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
        simp only [c]
        push_cast
        field_simp
      rw [hc, cbinom_add, Finset.sum_smul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      rw [hp]
      simp only [hYdef]
      congr 3
      ring_nf
    · have := hY s hs
      simp only [hYdef] at this
      rw [show (N * m + e) + (N * n + e') - (s : ℤ) * N = N * (m + n - s) + e + e' by ring,
        this, smul_zero]
  · -- support of the outer sum
    by_contra hc
    rw [not_and_or] at hc
    apply hi
    rcases hc with hneg | hbig
    · rw [cbz_apply_neg m (by omega), zero_smul]
    · lift i to ℕ using (by
        by_contra hneg
        exact hi (by rw [cbz_apply_neg m (by omega), zero_smul]))
      rw [hinner i, Finset.sum_eq_zero (fun t _ => by rw [hY _ (by omega), smul_zero]), smul_zero]

/-- `twisted_jacobi_of_local_pf_ge` with the product formula at every `ℓ`. -/
theorem twisted_jacobi_of_local_pf (W : VertexOperatorAlgebra 𝒱) (YM : 𝒱 →ₗ[ℂ] (ℤ → End ℂ M))
    {N : ℕ} (hN : 0 < N) (htr : ∀ (u : 𝒱) (x : M), ∃ K : ℤ, ∀ k : ℤ, K ≤ k → YM u k x = 0)
    (u v : 𝒱) (e e' : ℤ)
    (hloc : Local (resc (YM u) N e) (resc (YM v) N e'))
    (hpf : ∀ (ℓ s : ℤ) (x : M),
      mode (Fld.prod ℓ (rescFld hN (htr u) e) (rescFld hN (htr v) e')).1 s x
        = ∑ᶠ t : ℕ, cbinom ((e : ℂ) / N) t •
            YM (W.smul u (ℓ + t) v) (N * (s - t) + e + e') x)
    (x : M) (ℓ m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (YM u (ℓ * N + (N * m + e) - i * N) (YM v ((N * n + e') + i * N) x)
          - negOnePow ℓ • YM v (ℓ * N + (N * n + e') - i * N) (YM u ((N * m + e) + i * N) x)))
      = ∑ᶠ i : ℕ, cbinom (((N * m + e : ℤ) : ℂ) / N) i •
          YM (W.smul u (ℓ + i) v) ((N * m + e) + (N * n + e') - i * N) x :=
  twisted_jacobi_of_local_pf_ge W YM hN htr u v e e' hloc ℓ (fun ℓ' s x _ => hpf ℓ' s x) x m n

/-- **The assembled reduction.**  Fix for every class `j` an offset `off j ≡ −j (mod N)`.
Suppose that for every `u ∈ 𝒱ʲ`, every `v`, and every residue `e' ∈ [0, N)`, the rescaled fields
of `u` (offset `off j`) and `v` (offset `e'`) are mutually local and satisfy the twisted product
formula.  Then the corrected twisted Jacobi identity `TwistedJacobi g N YM` holds. -/
theorem twistedJacobi_of_local_pf {W : VertexOperatorAlgebra 𝒱} (g : Aut W)
    (YM : 𝒱 →ₗ[ℂ] (ℤ → End ℂ M)) {N : ℕ} (hN : 0 < N)
    (htr : ∀ (u : 𝒱) (x : M), ∃ K : ℤ, ∀ k : ℤ, K ≤ k → YM u k x = 0)
    (off : ℕ → ℤ) (hoff : ∀ j : ℕ, (off j + j) % (N : ℤ) = 0)
    (hloc : ∀ (j : ℕ) (u : 𝒱), u ∈ g.twistedEigenspace N j → ∀ (v : 𝒱) (e' : ℤ),
      0 ≤ e' → e' < N → Local (resc (YM u) N (off j)) (resc (YM v) N e'))
    (hpf : ∀ (j : ℕ) (u : 𝒱), u ∈ g.twistedEigenspace N j → ∀ (v : 𝒱) (e' : ℤ),
      0 ≤ e' → e' < N → ∀ (ℓ s : ℤ) (x : M),
      mode (Fld.prod ℓ (rescFld hN (htr u) (off j)) (rescFld hN (htr v) e')).1 s x
        = ∑ᶠ t : ℕ, cbinom ((off j : ℂ) / N) t •
            YM (W.smul u (ℓ + t) v) (N * (s - t) + off j + e') x) :
    TwistedJacobi g N YM := by
  intro j u hu v x ℓ k m' hk
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  obtain ⟨q, hq⟩ : (N : ℤ) ∣ k - off j := by
    have h1 := Int.dvd_of_emod_eq_zero hk
    have h2 := Int.dvd_of_emod_eq_zero (hoff j)
    have := dvd_sub h1 h2
    rwa [show k + (j : ℤ) - (off j + j) = k - off j by ring] at this
  have hk' : k = N * q + off j := by linarith
  have hm' : m' = N * (m' / N) + m' % N := (Int.mul_ediv_add_emod m' N).symm
  have h0 : 0 ≤ m' % N := Int.emod_nonneg _ hN'.ne'
  have h1 : m' % N < N := Int.emod_lt_of_pos _ hN'
  have h := twisted_jacobi_of_local_pf W YM hN htr u v (off j) (m' % N)
    (hloc j u hu v _ h0 h1) (hpf j u hu v _ h0 h1) x ℓ q (m' / N)
  rw [← hk', ← hm'] at h
  exact h

end TwistedReduction

end VOA
