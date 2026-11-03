/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QPochhammer
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Formal q-series toolkit for theta-function identities

Infrastructure for the Jacobi-triple-product family of identities (`JacobiTripleGauss`,
`FourTriangular`), all over an arbitrary commutative ring and without any analytic input.

* `AgreeTo K f g` — `X^K ∣ f - g`, i.e. `f` and `g` agree in every degree `< K`.  It is a
  congruence for `+`, `-`, `*`, finite sums and products, ring homomorphisms that do not lower
  `X`-adic order (`expand`, `rescale`), and the Euler operator.  `eq_of_agreeTo` turns agreement
  in every degree into equality.  This is the only "limit" used anywhere.
* `eulerOp f = X · df/dX` (`θ`), a derivation that commutes with `rescale`.
* `infProd u = ∏_{k ≥ 0} u k` for factors with `u k ≡ 1 mod X^(k+1)`, with multiplicativity,
  powers, regrouping of consecutive factors, and transport along `expand`/`rescale`.
* `zSeries c e = ∑_{n ∈ ℤ} c n X^(e n)` for exponent maps with `|n| ≤ e n + 1`, with truncation
  lemmas reducing every coefficient to a finite `Finset` sum.
-/

namespace VOA.QSeries.JTP

open PowerSeries

open scoped BigOperators

noncomputable section

section Agree

variable {R : Type*} [CommRing R]

/-- `f` and `g` agree in every degree below `K`. -/
def AgreeTo (K : ℕ) (f g : PowerSeries R) : Prop := (X : PowerSeries R) ^ K ∣ f - g

namespace AgreeTo

variable {K : ℕ} {f g h f' g' : PowerSeries R}

theorem refl (K : ℕ) (f : PowerSeries R) : AgreeTo K f f := by simp [AgreeTo]

theorem of_eq (hfg : f = g) : AgreeTo K f g := hfg ▸ refl K f

theorem symm (hfg : AgreeTo K f g) : AgreeTo K g f := by
  unfold AgreeTo at *
  rw [← neg_sub]
  exact (dvd_neg).2 hfg

theorem trans (h₁ : AgreeTo K f g) (h₂ : AgreeTo K g h) : AgreeTo K f h := by
  unfold AgreeTo at *
  have := dvd_add h₁ h₂
  rwa [sub_add_sub_cancel] at this

theorem add (h₁ : AgreeTo K f g) (h₂ : AgreeTo K f' g') : AgreeTo K (f + f') (g + g') := by
  unfold AgreeTo at *
  have := dvd_add h₁ h₂
  convert this using 1
  ring

theorem sub (h₁ : AgreeTo K f g) (h₂ : AgreeTo K f' g') : AgreeTo K (f - f') (g - g') := by
  unfold AgreeTo at *
  have := dvd_sub h₁ h₂
  convert this using 1
  ring

theorem mul (h₁ : AgreeTo K f g) (h₂ : AgreeTo K f' g') : AgreeTo K (f * f') (g * g') := by
  unfold AgreeTo at *
  have e : f * f' - g * g' = (f - g) * f' + g * (f' - g') := by ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_left h₁ _) (dvd_mul_of_dvd_right h₂ _)

theorem mul_left (c : PowerSeries R) (hfg : AgreeTo K f g) : AgreeTo K (c * f) (c * g) :=
  (refl K c).mul hfg

theorem mul_right (c : PowerSeries R) (hfg : AgreeTo K f g) : AgreeTo K (f * c) (g * c) :=
  hfg.mul (refl K c)

theorem pow (hfg : AgreeTo K f g) (n : ℕ) : AgreeTo K (f ^ n) (g ^ n) := by
  induction n with
  | zero => exact refl K 1
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hfg

theorem mono {K' : ℕ} (hK : K' ≤ K) (hfg : AgreeTo K f g) : AgreeTo K' f g :=
  (pow_dvd_pow X hK).trans hfg

theorem X_pow_mul (hfg : AgreeTo K f g) (m : ℕ) :
    AgreeTo (K + m) (X ^ m * f) (X ^ m * g) := by
  unfold AgreeTo at *
  rw [← mul_sub, pow_add, mul_comm ((X : PowerSeries R) ^ K)]
  exact mul_dvd_mul_left _ hfg

theorem finset_prod {ι : Type*} (s : Finset ι) {u v : ι → PowerSeries R}
    (huv : ∀ i ∈ s, AgreeTo K (u i) (v i)) :
    AgreeTo K (∏ i ∈ s, u i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact refl K 1
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (huv a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => huv i (Finset.mem_insert_of_mem hi))

theorem finset_sum {ι : Type*} (s : Finset ι) {u v : ι → PowerSeries R}
    (huv : ∀ i ∈ s, AgreeTo K (u i) (v i)) :
    AgreeTo K (∑ i ∈ s, u i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact refl K 0
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (huv a (Finset.mem_insert_self a s)).add
        (ih fun i hi => huv i (Finset.mem_insert_of_mem hi))

theorem coeff_eq (hfg : AgreeTo K f g) {d : ℕ} (hd : d < K) : coeff d f = coeff d g := by
  have := (X_pow_dvd_iff).1 hfg d hd
  rwa [map_sub, sub_eq_zero] at this

theorem of_coeff (hfg : ∀ d, d < K → coeff d f = coeff d g) : AgreeTo K f g :=
  X_pow_dvd_iff.2 fun d hd => by rw [map_sub, hfg d hd, sub_self]

/-- Ring homomorphisms that send `X^K` into `X^L ⟦X⟧` transport agreement. -/
theorem map {S : Type*} [CommRing S] (φ : PowerSeries R →+* PowerSeries S) {L : ℕ}
    (hφ : (X : PowerSeries S) ^ L ∣ φ (X ^ K)) (hfg : AgreeTo K f g) :
    AgreeTo L (φ f) (φ g) := by
  unfold AgreeTo at *
  obtain ⟨c, hc⟩ := hfg
  rw [← map_sub, hc, map_mul]
  exact dvd_mul_of_dvd_left hφ _

end AgreeTo

/-- Agreement in every degree is equality. -/
theorem eq_of_agreeTo {f g : PowerSeries R} (h : ∀ N : ℕ, AgreeTo (N + 1) f g) : f = g := by
  ext d
  exact (h d).coeff_eq (Nat.lt_succ_self d)

/-- `expand p` multiplies agreement order by `p`. -/
theorem AgreeTo.expand {K : ℕ} {f g : PowerSeries R} (p : ℕ) (hp : p ≠ 0)
    (hfg : AgreeTo K f g) :
    AgreeTo (p * K) (PowerSeries.expand p hp f) (PowerSeries.expand p hp g) := by
  apply AgreeTo.map (PowerSeries.expand p hp).toRingHom _ hfg
  change (X : PowerSeries R) ^ (p * K) ∣ PowerSeries.expand p hp (X ^ K)
  rw [map_pow, expand_X, ← pow_mul]

/-- `rescale a` preserves agreement. -/
theorem AgreeTo.rescale {K : ℕ} {f g : PowerSeries R} (a : R)
    (hfg : AgreeTo K f g) : AgreeTo K (PowerSeries.rescale a f) (PowerSeries.rescale a g) := by
  apply AgreeTo.of_coeff
  intro d hd
  rw [coeff_rescale, coeff_rescale, hfg.coeff_eq hd]

/-- Cancelling a monomial factor. -/
theorem X_pow_mul_cancel {f g : PowerSeries R} (m : ℕ) (h : X ^ m * f = X ^ m * g) : f = g := by
  ext d
  have := congrArg (coeff (d + m)) h
  rw [coeff_X_pow_mul', coeff_X_pow_mul'] at this
  simpa using this

/-- Coefficients of a finite sum of monomials. -/
theorem coeff_sum_monomial {ι : Type*} (s : Finset ι) (c : ι → R) (E : ι → ℕ) (d : ℕ) :
    coeff d (∑ i ∈ s, C (c i) * X ^ (E i)) = ∑ i ∈ s with E i = d, c i := by
  classical
  rw [map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_C_mul_X_pow]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · rfl

/-- The product of two finite monomial sums is a finite monomial sum over pairs. -/
theorem sum_monomial_mul_sum_monomial {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → R) (b : κ → R) (E : ι → ℕ) (F : κ → ℕ) :
    (∑ i ∈ s, C (a i) * X ^ (E i)) * (∑ j ∈ t, C (b j) * X ^ (F j)) =
      ∑ p ∈ s ×ˢ t, C (a p.1 * b p.2) * X ^ (E p.1 + F p.2) := by
  rw [Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, pow_add]
  ring

end Agree

/-! ## The Euler operator `θ = X d/dX` -/

section EulerOp

variable {R : Type*} [CommRing R]

/-- The Euler operator `θ f = X f'`, defined coefficientwise. -/
def eulerOp (f : PowerSeries R) : PowerSeries R := mk fun n => (n : R) * coeff n f

@[simp] theorem coeff_eulerOp (f : PowerSeries R) (n : ℕ) :
    coeff n (eulerOp f) = (n : R) * coeff n f := by
  simp [eulerOp]

theorem eulerOp_add (f g : PowerSeries R) : eulerOp (f + g) = eulerOp f + eulerOp g := by
  ext n; simp [mul_add]

theorem eulerOp_sub (f g : PowerSeries R) : eulerOp (f - g) = eulerOp f - eulerOp g := by
  ext n; simp [mul_sub]

theorem eulerOp_C_mul (c : R) (f : PowerSeries R) : eulerOp (C c * f) = C c * eulerOp f := by
  ext n; simp [coeff_C_mul]; ring

theorem eulerOp_one : eulerOp (1 : PowerSeries R) = 0 := by
  ext n; rcases n with _ | n <;> simp [coeff_one]

theorem eulerOp_mul (f g : PowerSeries R) :
    eulerOp (f * g) = eulerOp f * g + f * eulerOp g := by
  ext n
  simp only [coeff_eulerOp, map_add, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  rw [← hp']
  push_cast
  ring

theorem eulerOp_pow_succ (f : PowerSeries R) (n : ℕ) :
    eulerOp (f ^ (n + 1)) = ((n + 1 : ℕ) : PowerSeries R) * f ^ n * eulerOp f := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, eulerOp_mul, ih]
      push_cast
      ring

theorem eulerOp_sq (f : PowerSeries R) : eulerOp (f ^ 2) = 2 * f * eulerOp f := by
  rw [eulerOp_pow_succ]; push_cast; ring

theorem eulerOp_X_pow (m : ℕ) : eulerOp (X ^ m : PowerSeries R) = (m : PowerSeries R) * X ^ m := by
  ext n
  rw [coeff_eulerOp, coeff_X_pow, ← map_natCast (C (R := R)), coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h; rfl
  · simp

theorem eulerOp_rescale (a : R) (f : PowerSeries R) :
    eulerOp (rescale a f) = rescale a (eulerOp f) := by
  ext n; simp [coeff_rescale]; ring

theorem AgreeTo.eulerOp {K : ℕ} {f g : PowerSeries R} (hfg : AgreeTo K f g) :
    AgreeTo K (JTP.eulerOp f) (JTP.eulerOp g) :=
  AgreeTo.of_coeff fun d hd => by simp [hfg.coeff_eq hd]

end EulerOp

/-! ## Infinite products -/

section InfProd

variable {R : Type*} [CommRing R]

/-- Factors admissible for an infinite product: `u k ≡ 1` below degree `k + 1`. -/
def ProdFactors (u : ℕ → PowerSeries R) : Prop := ∀ k, AgreeTo (k + 1) (u k) 1

/-- The infinite product `∏_{k ≥ 0} u k`, each coefficient read from a finite truncation. -/
def infProd (u : ℕ → PowerSeries R) : PowerSeries R :=
  mk fun d => coeff d (∏ k ∈ Finset.range d, u k)

theorem ProdFactors.mul {u v : ℕ → PowerSeries R} (hu : ProdFactors u) (hv : ProdFactors v) :
    ProdFactors fun k => u k * v k := fun k => by
  simpa using (hu k).mul (hv k)

theorem ProdFactors.pow {u : ℕ → PowerSeries R} (hu : ProdFactors u) (n : ℕ) :
    ProdFactors fun k => u k ^ n := fun k => by
  simpa using (hu k).pow n

/-- `1 ± c X^(e k)` is admissible when `e k > k`. -/
theorem prodFactors_one_add (c : R) (e : ℕ → ℕ) (he : ∀ k, k < e k) :
    ProdFactors fun k => (1 : PowerSeries R) + C c * X ^ e k := fun k => by
  unfold AgreeTo
  rw [add_sub_cancel_left]
  exact Dvd.dvd.mul_left (pow_dvd_pow X (he k)) _

theorem partialProd_agree {u : ℕ → PowerSeries R} (hu : ProdFactors u) {N M : ℕ} (h : N ≤ M) :
    AgreeTo (N + 1) (∏ k ∈ Finset.range M, u k) (∏ k ∈ Finset.range N, u k) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  induction r with
  | zero => exact AgreeTo.refl _ _
  | succ r ih =>
      rw [← add_assoc, Finset.prod_range_succ]
      have h1 : AgreeTo (N + 1) (u (N + r)) 1 := (hu (N + r)).mono (by omega)
      simpa using (ih (by omega)).mul h1

/-- The infinite product agrees with its `N`-th truncation below degree `N + 1`. -/
theorem agreeTo_infProd {u : ℕ → PowerSeries R} (hu : ProdFactors u) (N : ℕ) :
    AgreeTo (N + 1) (infProd u) (∏ k ∈ Finset.range N, u k) := by
  apply AgreeTo.of_coeff
  intro d hd
  rw [infProd, coeff_mk]
  exact ((partialProd_agree hu (show d ≤ N by omega)).coeff_eq (Nat.lt_succ_self d)).symm

@[simp] theorem constantCoeff_infProd (u : ℕ → PowerSeries R) :
    constantCoeff (infProd u) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, infProd, coeff_mk]
  simp

theorem isUnit_infProd (u : ℕ → PowerSeries R) : IsUnit (infProd u) :=
  isUnit_iff_constantCoeff.mpr (by simp)

/-- Uniqueness: a series agreeing with all truncations is the infinite product. -/
theorem eq_infProd_of_agree {u : ℕ → PowerSeries R} (hu : ProdFactors u) {f : PowerSeries R}
    (hf : ∀ N, AgreeTo (N + 1) f (∏ k ∈ Finset.range N, u k)) : f = infProd u :=
  eq_of_agreeTo fun N => (hf N).trans (agreeTo_infProd hu N).symm

theorem infProd_mul {u v : ℕ → PowerSeries R} (hu : ProdFactors u) (hv : ProdFactors v) :
    infProd u * infProd v = infProd fun k => u k * v k := by
  apply eq_infProd_of_agree (hu.mul hv)
  intro N
  rw [Finset.prod_mul_distrib]
  exact (agreeTo_infProd hu N).mul (agreeTo_infProd hv N)

theorem infProd_pow {u : ℕ → PowerSeries R} (hu : ProdFactors u) (n : ℕ) :
    infProd u ^ n = infProd fun k => u k ^ n := by
  apply eq_infProd_of_agree (hu.pow n)
  intro N
  rw [Finset.prod_pow]
  exact (agreeTo_infProd hu N).pow n

theorem infProd_congr {u v : ℕ → PowerSeries R} (h : ∀ k, u k = v k) :
    infProd u = infProd v := by
  rw [funext h]

/-- Regrouping consecutive pairs of factors. -/
theorem infProd_pairs {u : ℕ → PowerSeries R} (hu : ProdFactors u) :
    infProd (fun k => u (2 * k) * u (2 * k + 1)) = infProd u := by
  have hpair : ProdFactors fun k => u (2 * k) * u (2 * k + 1) := fun k => by
    have h1 := (hu (2 * k)).mono (show k + 1 ≤ 2 * k + 1 by omega)
    have h2 := (hu (2 * k + 1)).mono (show k + 1 ≤ 2 * k + 1 + 1 by omega)
    simpa using h1.mul h2
  have hpart : ∀ N, (∏ k ∈ Finset.range N, (u (2 * k) * u (2 * k + 1))) =
      ∏ k ∈ Finset.range (2 * N), u k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.prod_range_succ, ih, show 2 * (N + 1) = 2 * N + 1 + 1 by ring,
          Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc]
  symm
  apply eq_infProd_of_agree hpair
  intro N
  rw [hpart]
  exact ((agreeTo_infProd hu (2 * N)).mono (by omega))

/-- Transport along a ring endomorphism that does not lower `X`-adic order. -/
theorem map_infProd (φ : PowerSeries R →+* PowerSeries R)
    (hφ : ∀ K, (X : PowerSeries R) ^ K ∣ φ (X ^ K)) {u : ℕ → PowerSeries R}
    (hu : ProdFactors u) : φ (infProd u) = infProd fun k => φ (u k) := by
  have hφu : ProdFactors fun k => φ (u k) := fun k => by
    simpa using (hu k).map φ (hφ (k + 1))
  apply eq_infProd_of_agree hφu
  intro N
  rw [← map_prod]
  exact (agreeTo_infProd hu N).map φ (hφ (N + 1))

theorem expand_infProd (p : ℕ) (hp : p ≠ 0) {u : ℕ → PowerSeries R} (hu : ProdFactors u) :
    expand p hp (infProd u) = infProd fun k => expand p hp (u k) := by
  apply map_infProd (expand p hp).toRingHom _ hu
  intro K
  change (X : PowerSeries R) ^ K ∣ expand p hp (X ^ K)
  rw [map_pow, expand_X, ← pow_mul]
  exact pow_dvd_pow X (Nat.le_mul_of_pos_left K (Nat.pos_of_ne_zero hp))

theorem rescale_infProd (a : R) {u : ℕ → PowerSeries R} (hu : ProdFactors u) :
    rescale a (infProd u) = infProd fun k => rescale a (u k) := by
  apply map_infProd (rescale a) _ hu
  intro K
  rw [map_pow, rescale_X, mul_pow]
  exact dvd_mul_left _ _

end InfProd

/-! ## Sums over `ℤ` with finite fibres -/

section ZSeries

variable {R : Type*} [CommRing R]

/-- `∑_{n ∈ ℤ} c n X^(e n)`.  Meaningful when `n.natAbs ≤ e n + 1`, which puts each fibre
`e⁻¹(d)` inside `[-d-1, d+1]`. -/
def zSeries (c : ℤ → R) (e : ℤ → ℕ) : PowerSeries R :=
  mk fun d => ∑ n ∈ Finset.Icc (-(d : ℤ) - 1) (d + 1) with e n = d, c n

theorem coeff_zSeries (c : ℤ → R) (e : ℤ → ℕ) (d : ℕ) :
    coeff d (zSeries c e) = ∑ n ∈ Finset.Icc (-(d : ℤ) - 1) (d + 1) with e n = d, c n := by
  simp [zSeries]

/-- Any finite index set containing every `n` with `e n < K` computes `zSeries` below `K`. -/
theorem agreeTo_zSeries (c : ℤ → R) (e : ℤ → ℕ) (he : ∀ n, n.natAbs ≤ e n + 1) {K : ℕ}
    (I : Finset ℤ) (hI : ∀ n, e n < K → n ∈ I) :
    AgreeTo K (zSeries c e) (∑ n ∈ I, C (c n) * X ^ (e n)) := by
  apply AgreeTo.of_coeff
  intro d hd
  rw [coeff_zSeries, coeff_sum_monomial]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨_, hn⟩
    exact ⟨hI n (by omega), hn⟩
  · rintro ⟨_, hn⟩
    have := he n
    omega

theorem rescale_zSeries (a : R) (c : ℤ → R) (e : ℤ → ℕ) :
    rescale a (zSeries c e) = zSeries (fun n => a ^ (e n) * c n) e := by
  ext d
  rw [coeff_rescale, coeff_zSeries, coeff_zSeries, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [(Finset.mem_filter.mp hn).2]

theorem eulerOp_zSeries (c : ℤ → R) (e : ℤ → ℕ) :
    eulerOp (zSeries c e) = zSeries (fun n => (e n : R) * c n) e := by
  ext d
  rw [coeff_eulerOp, coeff_zSeries, coeff_zSeries, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [(Finset.mem_filter.mp hn).2]

end ZSeries

end

end VOA.QSeries.JTP
