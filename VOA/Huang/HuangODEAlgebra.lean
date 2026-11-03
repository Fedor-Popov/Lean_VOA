/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.Convergence
import VOA.Huang.MatrixCoeffODE

/-!
# The one-variable algebra behind Huang's regular-singular equations (algebra)

Huang (CCM 7 (2005), §§1–2) obtains the equations for products and iterates of intertwining
operators from a finitely generated module over `ℂ[z₁^{±1}, z₂^{±1}, (z₁−z₂)^{−1}]`, then refines it
(Thm 2.3) to get a regular singular point and selects the degree-0 part (one variable).  This file
is the VOA-free algebra of a **direct one-variable form** of that argument
(`Huang/HuangODEProduct.lean`):

* `ratRing a = ℂ[x, (1 − a x)⁻¹] ⊆ ℂ⟦x⟧` (`a = 1`: products, pole at `z₁ = z₂`;
  `a = −1`: iterates, pole at `z₁ = 0`), a Noetherian ring (`Algebra.adjoin` of two elements),
  whose elements have the form `p(x)/(1 − a x)^b` (`exists_poly_of_mem_ratRing`), and which contains
  the binomial series `Σ_i C(i,k) a^{i−k} x^i = x^k (1 − a x)^{−k−1}` (`binomSeries_mem`);
* `theta_iterate_mem` — membership of all `θ_ν^j H` in a `ℂ`-subspace does not depend on the
  twist `ν`;
* `ratFuchsian_of_fg` — **if all `θ_μ^j (X^K G)` lie in a finitely generated
  `ratRing a`-submodule of `ℂ⟦x⟧`, then `G` satisfies `RatFuchsian a λ` for every `λ`.**  This is
  Huang's Cor. 1.3 plus the *regularity* (the module lives in `ℂ⟦x⟧` and the ring has no `x⁻¹`, so the
  equation is monic in `θ` with coefficients holomorphic at `x = 0`: Thm 2.3) plus the degree-0
  selection (everything is already one-variable).
* `coeff_conv` — the coefficient form of `(PowerSeries.mk ρ) · X^d · H` used to match mode identities.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.HuangODEAlgebra

open PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open scoped BigOperators

/-! ## The ring `ℂ[x, (1 − a x)⁻¹]` -/

/-- The geometric series `(1 − a x)⁻¹ = Σ aⁿ xⁿ`. -/
noncomputable def geom (a : ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => a ^ n

theorem one_sub_mul_geom (a : ℂ) : (1 - PowerSeries.C a * X) * geom a = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc]
  rcases n with _ | n
  · simp [geom]
  · rw [coeff_C_mul, coeff_succ_X_mul]
    simp [geom, pow_succ]
    ring

/-- `ℂ[x, (1 − a x)⁻¹]` as a subalgebra of `ℂ⟦x⟧`. -/
noncomputable def ratRing (a : ℂ) : Subalgebra ℂ (PowerSeries ℂ) :=
  Algebra.adjoin ℂ ({X, geom a} : Set (PowerSeries ℂ))

instance (a : ℂ) : IsNoetherianRing (ratRing a) := by
  classical
  have hfg : (ratRing a).FG := by
    have := Subalgebra.fg_adjoin_finset (R := ℂ) ({X, geom a} : Finset (PowerSeries ℂ))
    simpa [ratRing] using this
  haveI : Algebra.FiniteType ℂ (ratRing a) := (Subalgebra.fg_iff_finiteType _).mp hfg
  exact Algebra.FiniteType.isNoetherianRing ℂ (ratRing a)

theorem X_mem_ratRing (a : ℂ) : (X : PowerSeries ℂ) ∈ ratRing a :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem geom_mem_ratRing (a : ℂ) : geom a ∈ ratRing a :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

/-- The polynomial `1 − a x`. -/
noncomputable def linPoly (a : ℂ) : Polynomial ℂ := 1 - Polynomial.C a * Polynomial.X

theorem coe_linPoly (a : ℂ) :
    ((linPoly a : Polynomial ℂ) : PowerSeries ℂ) = 1 - PowerSeries.C a * X := by
  simp [linPoly, Polynomial.coe_C, Polynomial.coe_X]

/-- Every element of `ratRing a` is `p(x)/(1 − a x)^b`. -/
theorem exists_poly_of_mem_ratRing {a : ℂ} {r : PowerSeries ℂ} (hr : r ∈ ratRing a) :
    ∃ (b : ℕ) (p : Polynomial ℂ), (1 - PowerSeries.C a * X) ^ b * r = (p : PowerSeries ℂ) := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨0, Polynomial.X, by simp [Polynomial.coe_X]⟩
    · exact ⟨1, 1, by rw [pow_one, one_sub_mul_geom]; simp⟩
  | algebraMap c => exact ⟨0, Polynomial.C c, by simp [Polynomial.coe_C]⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, p, hp⟩ := hx
    obtain ⟨b', p', hp'⟩ := hy
    refine ⟨b + b', linPoly a ^ b' * p + linPoly a ^ b * p', ?_⟩
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, coe_linPoly, ← hp,
      ← hp']
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨b, p, hp⟩ := hx
    obtain ⟨b', p', hp'⟩ := hy
    refine ⟨b + b', p * p', ?_⟩
    simp only [Polynomial.coe_mul, ← hp, ← hp']
    ring

/-- The binomial series `Σ_i C(i,k) a^{i−k} xⁱ` (`= x^k (1 − a x)^{−k−1}`). -/
noncomputable def binomSeries (a : ℂ) (k : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun i => (i.choose k : ℂ) * a ^ (i - k)

theorem binomSeries_zero (a : ℂ) : binomSeries a 0 = geom a := by
  ext n; simp [binomSeries, geom]

theorem one_sub_mul_binomSeries_succ (a : ℂ) (k : ℕ) :
    (1 - PowerSeries.C a * X) * binomSeries a (k + 1) = X * binomSeries a k := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc]
  rcases n with _ | n
  · simp [binomSeries]
  · rw [coeff_C_mul, coeff_succ_X_mul, coeff_succ_X_mul]
    simp only [binomSeries, coeff_mk]
    rw [Nat.choose_succ_succ', Nat.cast_add]
    rcases lt_or_ge n k with h | h
    · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : n < k + 1)]
      simp
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have e1 : k + d + 1 - (k + 1) = d := by omega
      have e2 : k + d - k = d := by omega
      rcases d with _ | d
      · simp
      · have e3 : k + (d + 1) - (k + 1) = d := by omega
        rw [e1, e2, e3, pow_succ]
        ring

theorem binomSeries_mul (a : ℂ) (k : ℕ) :
    (1 - PowerSeries.C a * X) ^ (k + 1) * binomSeries a k = X ^ k := by
  induction k with
  | zero => rw [binomSeries_zero, zero_add, pow_one, one_sub_mul_geom, pow_zero]
  | succ k ih =>
    rw [pow_succ, mul_assoc, one_sub_mul_binomSeries_succ, mul_left_comm, ih, pow_succ']

/-- `binomSeries a k = X^k · (1 − a x)^{−k−1} ∈ ratRing a`. -/
theorem binomSeries_eq (a : ℂ) (k : ℕ) : binomSeries a k = X ^ k * geom a ^ (k + 1) := by
  have h := congrArg (· * geom a ^ (k + 1)) (binomSeries_mul a k)
  simp only at h
  rw [← h, mul_comm, ← mul_assoc, ← mul_pow, mul_comm (geom a), one_sub_mul_geom, one_pow,
    one_mul]

theorem binomSeries_mem (a : ℂ) (k : ℕ) : binomSeries a k ∈ ratRing a := by
  rw [binomSeries_eq]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (X_mem_ratRing a) _)
    (Subalgebra.pow_mem _ (geom_mem_ratRing a) _)

theorem X_pow_mem (a : ℂ) (d : ℕ) : (X : PowerSeries ℂ) ^ d ∈ ratRing a :=
  Subalgebra.pow_mem _ (X_mem_ratRing a) _

/-! ## Twisted Euler operators -/

theorem thetaShift_add (μ d : ℂ) (H : PowerSeries ℂ) :
    thetaShift (μ + d) H = thetaShift μ H + d • H := by
  ext n
  simp only [coeff_thetaShift, map_add, map_smul, smul_eq_mul]
  ring

theorem thetaShift_X_pow_mul (μ : ℂ) (K : ℕ) (G : PowerSeries ℂ) :
    thetaShift μ (X ^ K * G) = X ^ K * thetaShift (μ + K) G := by
  ext n
  rw [coeff_thetaShift, coeff_X_pow_mul', coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_thetaShift, Nat.cast_sub h]; ring
  · simp

theorem thetaShift_iterate_X_pow_mul (μ : ℂ) (K : ℕ) (G : PowerSeries ℂ) (j : ℕ) :
    (thetaShift μ)^[j] (X ^ K * G) = X ^ K * (thetaShift (μ + K))^[j] G := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, thetaShift_X_pow_mul, Function.iterate_succ_apply']

theorem thetaShift_iterate_add (μ : ℂ) (i : ℕ) (x y : PowerSeries ℂ) :
    (thetaShift μ)^[i] (x + y) = (thetaShift μ)^[i] x + (thetaShift μ)^[i] y := by
  simp only [← Module.End.pow_apply, map_add]

theorem thetaShift_iterate_smul (μ : ℂ) (i : ℕ) (c : ℂ) (x : PowerSeries ℂ) :
    (thetaShift μ)^[i] (c • x) = c • (thetaShift μ)^[i] x := by
  simp only [← Module.End.pow_apply, map_smul]

/-- Membership of every `θ^j H` in a `ℂ`-subspace does not depend on the twist. -/
theorem theta_iterate_mem (S : Submodule ℂ (PowerSeries ℂ)) {μ : ℂ} :
    ∀ {H : PowerSeries ℂ}, (∀ i, (thetaShift μ)^[i] H ∈ S) →
      ∀ (ν : ℂ) (j : ℕ), (thetaShift ν)^[j] H ∈ S := by
  intro H hH ν j
  induction j generalizing H with
  | zero => simpa using hH 0
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    intro i
    have e : thetaShift ν H = thetaShift μ H + (ν - μ) • H := by
      rw [← thetaShift_add, add_sub_cancel]
    rw [e, thetaShift_iterate_add, thetaShift_iterate_smul, ← Function.iterate_succ_apply]
    exact S.add_mem (hH _) (S.smul_mem _ (hH _))

/-! ## The regular-singular equation from a finitely generated module -/

/-- **Huang's equation from finite generation (one-variable, regular form).**  If every
`θ_μ^j (X^K G)` lies in a finitely generated `ratRing a`-submodule of `ℂ⟦x⟧`, then `G` satisfies a
monic `θ_λ`-equation with coefficients `p(x)/(1 − a x)^b`, for every `λ`. -/
theorem ratFuchsian_of_fg {a : ℂ} (N : Submodule (ratRing a) (PowerSeries ℂ)) (hN : N.FG)
    {G : PowerSeries ℂ} {K : ℕ} {μ : ℂ}
    (h : ∀ j, (thetaShift μ)^[j] (X ^ K * G) ∈ N) (lam : ℂ) : RatFuchsian a lam G := by
  classical
  set H := X ^ K * G with hHdef
  -- the twist `lam − K` on `H` corresponds to `lam` on `G`
  have hmem : ∀ j, (thetaShift (lam - K))^[j] H ∈ N := by
    have := theta_iterate_mem (N.restrictScalars ℂ) (μ := μ) (H := H) h (lam - K)
    exact fun j => this j
  haveI : Module.Finite (ratRing a) N := Module.Finite.iff_fg.mpr hN
  obtain ⟨m, r, hr⟩ := VOA.Huang.MatrixCoeffODE.exists_monic_relation (R := ratRing a)
    (fun j => (⟨(thetaShift (lam - K))^[j] H, hmem j⟩ : N))
  have hr' : (thetaShift (lam - K))^[m] H
      = ∑ k ∈ Finset.range m, (r k : PowerSeries ℂ) * (thetaShift (lam - K))^[k] H := by
    have := congrArg Subtype.val hr
    simpa [Submodule.coe_sum, Subalgebra.smul_def] using this
  have hX : (X : PowerSeries ℂ) ^ K ≠ 0 := pow_ne_zero _ X_ne_zero
  have hG : (thetaShift lam)^[m] G
      = ∑ k ∈ Finset.range m, (r k : PowerSeries ℂ) * (thetaShift lam)^[k] G := by
    have e : lam - (K : ℂ) + K = lam := by ring
    rw [hHdef, thetaShift_iterate_X_pow_mul, e] at hr'
    simp_rw [thetaShift_iterate_X_pow_mul, e] at hr'
    apply mul_left_cancel₀ hX
    rw [hr', Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  choose b p hbp using fun k : Fin m => exists_poly_of_mem_ratRing (r k).2
  refine ⟨m, ∑ k : Fin m, b k, fun k => -(r k : PowerSeries ℂ),
    fun k => if hk : k < m then -(linPoly a ^ (∑ k : Fin m, b k - b ⟨k, hk⟩) * p ⟨k, hk⟩) else 0,
    fun k hk => ?_, ?_⟩
  · dsimp only; rw [dif_pos hk]
    have hle : b ⟨k, hk⟩ ≤ ∑ k : Fin m, b k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    simp only [Polynomial.coe_neg, Polynomial.coe_mul, Polynomial.coe_pow, coe_linPoly,
      ← hbp ⟨k, hk⟩]
    rw [← Nat.sub_add_cancel hle, pow_add]
    simp only [Nat.sub_add_cancel hle]
    ring
  · unfold FuchsianEq
    rw [hG, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun k _ => by ring

/-! ## Coefficients of `(PowerSeries.mk ρ) · X^d · H` -/

/-- The coefficient of `(mk ρ) · X^d · H` as a finite sum over `i < I`, for any `I > n`. -/
theorem coeff_conv (ρ : ℕ → ℂ) (d : ℕ) (H : PowerSeries ℂ) {n I : ℕ} (hI : n < I) :
    coeff n (PowerSeries.mk ρ * X ^ d * H)
      = ∑ i ∈ Finset.range I, if i + d ≤ n then ρ i * coeff (n - d - i) H else 0 := by
  rw [mul_assoc, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (PowerSeries.mk ρ) * coeff j (X ^ d * H))]
  rw [← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ I by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (n + 1) I) (fun i hi => by
    simp only [Finset.mem_Ico] at hi; rw [if_neg (by omega)]), add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [coeff_mk, coeff_X_pow_mul']
  split_ifs with h1 h2 h2
  · rw [show n - i - d = n - d - i by omega]
  · omega
  · omega
  · simp

end VOA.Huang.HuangODEAlgebra
