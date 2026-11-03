/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesBoxRelations

/-!
# The Grassmannian spanning lemma for symmetric polynomials

Pure algebra in `ℂ[y_1, …, y_m]`: **every symmetric polynomial is, modulo the span of the
products `h_q · g` (`q ≥ t`, `g` symmetric), a symmetric polynomial all of whose exponents are
`< t`** (`grassmann_span`).  This is the statement that the quotient
`Sym_m / (h_t, h_{t+1}, …)` — the cohomology of the Grassmannian `Gr(m, m + t - 1)` — is
spanned by the monomial symmetric functions in the `m × (t-1)` box.

The proof is the exact sequence of the Grassmannian, done by hand:

* `rho m` sets `y_0 = 0`; it maps `h_q` to `h_q` (`rho_hh`);
* `OS k β = Σ_σ σ(y^β)` (orbit sums over all permutations), and the explicit count
  `rho_OS_cons`: `rho (OS (m+1) (0, γ)) = (1 + #zeros(γ)) • OS m γ`, which gives a
  **symmetric lift** `liftS` with `rho ∘ liftS = id` on symmetric polynomials, preserving the box;
* the kernel of `rho` on symmetric polynomials is `e_m · Sym` (`eq_e_mul_of_rho_eq_zero`);
* `e_m · h_q` is a combination of `h_{q+1}, …, h_{q+m}` with symmetric coefficients
  (`e_mul_hh_mem`, from `Π(1 - y_i u) · Π 1/(1 - y_i u) = 1`).

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial

noncomputable section

/-! ### Setting `y_0 = 0` -/

/-- The restriction `y_0 ↦ 0`, `y_{i+1} ↦ y_i`. -/
def rho (m : ℕ) : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  aeval (Fin.cons 0 X)

theorem rho_X (m : ℕ) (j : Fin (m + 1)) :
    rho m (X j) = (Fin.cons 0 X : Fin (m + 1) → MvPolynomial (Fin m) ℂ) j := by
  simp [rho]

theorem rho_X_zero (m : ℕ) : rho m (X 0) = 0 := by simp [rho]

theorem rho_X_succ (m : ℕ) (i : Fin m) : rho m (X i.succ) = X i := by simp [rho]

/-! ### Orbit sums -/

/-- The orbit sum `Σ_σ σ(y^β)` over all permutations. -/
def OS (k : ℕ) (β : Fin k →₀ ℕ) : MvPolynomial (Fin k) ℂ :=
  ∑ σ : Equiv.Perm (Fin k), rename σ (monomial β 1)

theorem OS_isSymmetric (k : ℕ) (β : Fin k →₀ ℕ) : (OS k β).IsSymmetric := by
  intro e
  rw [OS, map_sum]
  simp_rw [rename_rename]
  exact Fintype.sum_equiv (Equiv.mulLeft e) _ _ fun σ => rfl

/-- The number of zero exponents. -/
def zc {m : ℕ} (γ : Fin m →₀ ℕ) : ℕ := (Finset.univ.filter fun i => γ i = 0).card

theorem rename_monomial_one_eq_prod {k : ℕ} (σ : Equiv.Perm (Fin k)) (β : Fin k →₀ ℕ) :
    rename σ (monomial β (1 : ℂ)) = ∏ j, X (σ j) ^ β j := by
  rw [← prod_X_pow_eq_monomial, map_prod]
  simp [rename_X]

theorem cons_X_swap_succ (m : ℕ) (p : Fin (m + 1)) (y : Fin m) :
    (Fin.cons 0 X : Fin (m + 1) → MvPolynomial (Fin m) ℂ) (Equiv.swap 0 p y.succ) =
      if y.succ = p then 0 else X y := by
  rw [Equiv.swap_apply_def, if_neg (Fin.succ_ne_zero y)]
  split_ifs with h
  · rfl
  · rfl

theorem rho_rename_cons_aux (m : ℕ) (p : Fin (m + 1)) (τ : Equiv.Perm (Fin m))
    (γ : Fin m →₀ ℕ) :
    rho m (rename (Equiv.Perm.decomposeFin.symm (p, τ)) (monomial (Finsupp.cons 0 γ) 1)) =
      ∏ x, (if (τ x).succ = p then 0 else X (τ x)) ^ γ x := by
  rw [rename_monomial_one_eq_prod, Fin.prod_univ_succ, Finsupp.cons_zero, pow_zero, one_mul,
    map_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finsupp.cons_succ, map_pow, rho_X, Equiv.Perm.decomposeFin_symm_apply_succ,
    cons_X_swap_succ]

theorem rho_rename_cons_zero (m : ℕ) (τ : Equiv.Perm (Fin m)) (γ : Fin m →₀ ℕ) :
    rho m (rename (Equiv.Perm.decomposeFin.symm (0, τ)) (monomial (Finsupp.cons 0 γ) 1)) =
      rename τ (monomial γ 1) := by
  rw [rho_rename_cons_aux, rename_monomial_one_eq_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [if_neg (Fin.succ_ne_zero _)]

theorem rho_rename_cons_succ (m : ℕ) (k : Fin m) (τ : Equiv.Perm (Fin m)) (γ : Fin m →₀ ℕ) :
    rho m (rename (Equiv.Perm.decomposeFin.symm (k.succ, τ)) (monomial (Finsupp.cons 0 γ) 1)) =
      if γ (τ.symm k) = 0 then rename τ (monomial γ 1) else 0 := by
  rw [rho_rename_cons_aux]
  split_ifs with h
  · rw [rename_monomial_one_eq_prod]
    refine Finset.prod_congr rfl fun x _ => ?_
    by_cases hx : τ x = k
    · have : x = τ.symm k := by rw [← hx, Equiv.symm_apply_apply]
      subst this
      rw [h, pow_zero, pow_zero]
    · rw [if_neg (fun h' => hx (Fin.succ_injective _ h'))]
  · refine Finset.prod_eq_zero (Finset.mem_univ (τ.symm k)) ?_
    rw [Equiv.apply_symm_apply, if_pos rfl, zero_pow h]

theorem sum_ite_perm_zero {m : ℕ} (τ : Equiv.Perm (Fin m)) (γ : Fin m →₀ ℕ)
    (v : MvPolynomial (Fin m) ℂ) :
    ∑ k : Fin m, (if γ (τ.symm k) = 0 then v else 0) = (zc γ : ℂ) • v := by
  rw [Fintype.sum_equiv τ.symm (fun k => if γ (τ.symm k) = 0 then v else 0)
    (fun x => if γ x = 0 then v else 0) (fun k => rfl), ← Finset.sum_filter, Finset.sum_const,
    zc, Nat.cast_smul_eq_nsmul]

/-- **The restriction of an orbit sum**: `rho (OS (m+1) (0, γ)) = (1 + #zeros γ) • OS m γ`. -/
theorem rho_OS_cons (m : ℕ) (γ : Fin m →₀ ℕ) :
    rho m (OS (m + 1) (Finsupp.cons 0 γ)) = ((1 + zc γ : ℕ) : ℂ) • OS m γ := by
  rw [OS, map_sum, ← Fintype.sum_equiv Equiv.Perm.decomposeFin.symm
    (fun pτ => rho m (rename (Equiv.Perm.decomposeFin.symm pτ) (monomial (Finsupp.cons 0 γ) 1)))
    _ (fun _ => rfl), Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp_rw [rho_rename_cons_zero, rho_rename_cons_succ]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin m)), ← Finset.sum_add_distrib, OS,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [sum_ite_perm_zero, Nat.cast_add, Nat.cast_one, add_smul, one_smul]

/-! ### The symmetric lift -/

theorem sum_rename_of_isSymmetric {m : ℕ} {g : MvPolynomial (Fin m) ℂ} (hg : g.IsSymmetric) :
    ∑ τ : Equiv.Perm (Fin m), rename τ g = ((m.factorial : ℕ) : ℂ) • g := by
  rw [Finset.sum_congr rfl fun τ _ => hg τ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul]

theorem sum_coeff_smul_OS {m : ℕ} (g : MvPolynomial (Fin m) ℂ) :
    ∑ γ ∈ g.support, coeff γ g • OS m γ = ∑ τ : Equiv.Perm (Fin m), rename τ g := by
  conv_rhs => rw [g.as_sum]
  simp_rw [OS, Finset.smul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun γ _ => ?_
  rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]

/-- A symmetric lift through `rho`. -/
def liftS (m : ℕ) (g : MvPolynomial (Fin m) ℂ) : MvPolynomial (Fin (m + 1)) ℂ :=
  ((m.factorial : ℂ)⁻¹) • ∑ γ ∈ g.support,
    (coeff γ g / ((1 + zc γ : ℕ) : ℂ)) • OS (m + 1) (Finsupp.cons 0 γ)

theorem liftS_mem_symmetric (m : ℕ) (g : MvPolynomial (Fin m) ℂ) :
    liftS m g ∈ symmetricSubalgebra (Fin (m + 1)) ℂ := by
  refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun γ _ => Subalgebra.smul_mem _ ?_ _) _
  exact (mem_symmetricSubalgebra _).mpr (OS_isSymmetric _ _)

/-- **`liftS` is a section of `rho` on symmetric polynomials.** -/
theorem rho_liftS {m : ℕ} {g : MvPolynomial (Fin m) ℂ} (hg : g.IsSymmetric) :
    rho m (liftS m g) = g := by
  rw [liftS, map_smul, map_sum]
  have h : ∀ γ ∈ g.support, rho m ((coeff γ g / ((1 + zc γ : ℕ) : ℂ)) •
      OS (m + 1) (Finsupp.cons 0 γ)) = coeff γ g • OS m γ := by
    intro γ _
    rw [map_smul, rho_OS_cons, smul_smul, div_mul_cancel₀]
    exact_mod_cast (show 1 + zc γ ≠ 0 by omega)
  rw [Finset.sum_congr rfl h, sum_coeff_smul_OS, sum_rename_of_isSymmetric hg, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m), one_smul]

theorem monomial_mem_restrictSupport {k : ℕ} {S : Set (Fin k →₀ ℕ)} {δ : Fin k →₀ ℕ}
    (h : δ ∈ S) (c : ℂ) : monomial δ c ∈ restrictSupport ℂ S := by
  rw [mem_restrictSupport_iff]
  intro x hx
  rw [Finset.mem_coe] at hx
  rw [Finset.mem_singleton.mp (support_monomial_subset hx)]
  exact h

/-- The polynomials all of whose exponents are `< t`. -/
abbrev boxSupp (k t : ℕ) : Submodule ℂ (MvPolynomial (Fin k) ℂ) :=
  restrictSupport ℂ {β | ∀ i, β i < t}

theorem OS_mem_boxSupp {k t : ℕ} {β : Fin k →₀ ℕ} (hβ : ∀ i, β i < t) : OS k β ∈ boxSupp k t := by
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [rename_monomial]
  refine monomial_mem_restrictSupport (fun i => ?_) 1
  rw [Finsupp.mapDomain_equiv_apply]
  exact hβ _

theorem liftS_mem_boxSupp {m t : ℕ} (ht : 1 ≤ t) {g : MvPolynomial (Fin m) ℂ}
    (hg : g ∈ boxSupp m t) : liftS m g ∈ boxSupp (m + 1) t := by
  rw [mem_restrictSupport_iff] at hg
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ hγ => Submodule.smul_mem _ _ ?_)
  refine OS_mem_boxSupp fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [Finsupp.cons_zero]; omega
  · rw [Finsupp.cons_succ]; exact hg hγ i

/-! ### The kernel of `rho` on symmetric polynomials -/

theorem rho_monomial (m : ℕ) (δ : Fin (m + 1) →₀ ℕ) (c : ℂ) :
    rho m (monomial δ c) = if δ 0 = 0 then monomial (Finsupp.tail δ) c else 0 := by
  rw [show monomial δ c = c • monomial δ (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, ← prod_X_pow_eq_monomial, map_prod, Fin.prod_univ_succ, map_pow, rho_X_zero]
  simp_rw [map_pow, rho_X_succ]
  split_ifs with h
  · rw [h, pow_zero, one_mul, show monomial (Finsupp.tail δ) c =
      c • monomial (Finsupp.tail δ) (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one],
      ← prod_X_pow_eq_monomial]
    rfl
  · rw [zero_pow h, zero_mul, smul_zero]

theorem coeff_tail_rho {m : ℕ} (g : MvPolynomial (Fin (m + 1)) ℂ) (β : Fin (m + 1) →₀ ℕ)
    (hβ : β 0 = 0) : coeff (Finsupp.tail β) (rho m g) = coeff β g := by
  induction g using MvPolynomial.induction_on' with
  | monomial δ c =>
    rw [rho_monomial]
    by_cases h1 : δ 0 = 0
    · rw [if_pos h1, coeff_monomial, coeff_monomial]
      by_cases h2 : δ = β
      · subst h2; simp
      · rw [if_neg h2, if_neg]
        intro h3
        apply h2
        rw [← Finsupp.cons_tail δ, ← Finsupp.cons_tail β, h1, hβ, h3]
    · rw [if_neg h1, coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact h1 hβ
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq]

/-- `e = y_0 ⋯ y_{k-1}`. -/
def eProd (k : ℕ) : MvPolynomial (Fin k) ℂ := ∏ i, X i

/-- The all-ones exponent. -/
def onesF (k : ℕ) : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

theorem eProd_eq (k : ℕ) : eProd k = monomial (onesF k) 1 := by
  rw [← prod_X_pow_eq_monomial, eProd]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [onesF]

theorem eProd_isSymmetric (k : ℕ) : (eProd k).IsSymmetric := by
  intro σ
  rw [eProd, map_prod]
  simp_rw [rename_X]
  exact Fintype.prod_equiv σ _ _ fun _ => rfl

theorem eProd_ne_zero (k : ℕ) : eProd k ≠ 0 := by
  rw [eProd_eq]; exact monomial_eq_zero.not.mpr one_ne_zero

theorem coeff_eq_of_isSymmetric {k : ℕ} {g : MvPolynomial (Fin k) ℂ} (hg : g.IsSymmetric)
    (σ : Equiv.Perm (Fin k)) (β : Fin k →₀ ℕ) :
    coeff (Finsupp.mapDomain σ β) g = coeff β g := by
  conv_lhs => rw [← hg σ]
  exact coeff_rename_mapDomain σ σ.injective g β

/-- **The kernel of `rho` on symmetric polynomials is `e · Sym`.** -/
theorem exists_eq_eProd_mul {m : ℕ} {g : MvPolynomial (Fin (m + 1)) ℂ} (hg : g.IsSymmetric)
    (h0 : rho m g = 0) : ∃ g', g'.IsSymmetric ∧ g = eProd (m + 1) * g' := by
  classical
  have hpos : ∀ β ∈ g.support, ∀ i, β i ≠ 0 := by
    intro β hβ i hi
    rw [mem_support_iff] at hβ
    apply hβ
    rw [← coeff_eq_of_isSymmetric hg (Equiv.swap 0 i) β, ← coeff_tail_rho, h0, coeff_zero]
    rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap, Equiv.swap_apply_left, hi]
  set g' := ∑ β ∈ g.support, monomial (β - onesF (m + 1)) (coeff β g) with hg'
  have heq : g = eProd (m + 1) * g' := by
    conv_lhs => rw [g.as_sum]
    rw [hg', Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hβ' : onesF (m + 1) + (β - onesF (m + 1)) = β := by
      ext i
      have := hpos β hβ i
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, onesF,
        Finsupp.equivFunOnFinite_symm_apply_apply]
      omega
    rw [eProd_eq, monomial_mul, one_mul, hβ']
  refine ⟨g', fun σ => ?_, heq⟩
  apply mul_left_cancel₀ (eProd_ne_zero (m + 1))
  rw [← heq, ← eProd_isSymmetric (m + 1) σ, ← map_mul, ← heq, hg σ]

/-! ### Complete and elementary symmetric polynomials -/

/-- The geometric series `Σ_k a^k u^k`. -/
def geomS {A : Type*} [CommSemiring A] (a : A) : PowerSeries A := PowerSeries.mk fun k => a ^ k

/-- The factor `1 - a u`. -/
def facS {A : Type*} [CommRing A] (a : A) : PowerSeries A :=
  1 - PowerSeries.C a * PowerSeries.X

theorem facS_mul_geomS {A : Type*} [CommRing A] (a : A) : facS a * geomS a = 1 := by
  ext k
  rw [facS, sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
  rcases k with _ | k
  · simp [geomS, PowerSeries.coeff_zero_X_mul]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [geomS, pow_succ, mul_comm]

theorem coeff_facS {A : Type*} [CommRing A] (a : A) (k : ℕ) :
    PowerSeries.coeff k (facS a) = if k = 0 then 1 else if k = 1 then -a else 0 := by
  rw [facS, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, PowerSeries.coeff_X]
  split_ifs <;> simp_all

theorem hh_eq_coeff_geom (m q : ℕ) :
    hh m q = PowerSeries.coeff q (∏ i : Fin m, geomS (X i : MvPolynomial (Fin m) ℂ)) := rfl

theorem map_geomS {A B : Type*} [CommSemiring A] [CommSemiring B] (f : A →+* B) (a : A) :
    PowerSeries.map f (geomS a) = geomS (f a) := by
  ext k; simp [geomS, PowerSeries.coeff_map]

theorem map_facS {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    PowerSeries.map f (facS a) = facS (f a) := by
  ext k; simp [coeff_facS, PowerSeries.coeff_map]; split_ifs <;> simp

theorem geomS_zero {A : Type*} [CommSemiring A] : geomS (0 : A) = 1 := by
  ext k; rcases k with _ | k <;> simp [geomS, PowerSeries.coeff_one]

/-- `rho` maps `h_q` to `h_q`. -/
theorem rho_hh (m q : ℕ) : rho m (hh (m + 1) q) = hh m q := by
  rw [hh_eq_coeff_geom, hh_eq_coeff_geom, ← AlgHom.coe_toRingHom, ← PowerSeries.coeff_map,
    map_prod, Fin.prod_univ_succ]
  simp_rw [map_geomS, AlgHom.coe_toRingHom, rho_X_zero, rho_X_succ, geomS_zero, one_mul]

theorem hh_isSymmetric (m q : ℕ) : (hh m q).IsSymmetric := by
  intro σ
  rw [hh_eq_coeff_geom, ← AlgHom.coe_toRingHom, ← PowerSeries.coeff_map, map_prod]
  simp_rw [map_geomS, AlgHom.coe_toRingHom, rename_X]
  congr 1
  exact Fintype.prod_equiv σ _ _ fun _ => rfl

/-- The coefficients of `Π_i (1 - y_i u)` (signed elementary symmetric polynomials). -/
def EE (m j : ℕ) : MvPolynomial (Fin m) ℂ :=
  PowerSeries.coeff j (∏ i : Fin m, facS (X i : MvPolynomial (Fin m) ℂ))

theorem EE_isSymmetric (m j : ℕ) : (EE m j).IsSymmetric := by
  intro σ
  rw [EE, ← AlgHom.coe_toRingHom, ← PowerSeries.coeff_map, map_prod]
  simp_rw [map_facS, AlgHom.coe_toRingHom, rename_X]
  congr 1
  exact Fintype.prod_equiv σ _ _ fun _ => rfl

theorem EE_eq_zero (m j : ℕ) (hj : m < j) : EE m j = 0 := by
  classical
  rw [EE, PowerSeries.coeff_prod]
  refine Finset.sum_eq_zero fun l hl => ?_
  rw [Finset.mem_finsuppAntidiag] at hl
  obtain ⟨i, hi⟩ : ∃ i, 2 ≤ l i := by
    by_contra h
    push Not at h
    have : ∑ i, l i ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum fun i _ => by have := h i; omega
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    have h1 : ∑ i, l i = j := hl.1
    omega
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [coeff_facS, if_neg (by omega), if_neg (by omega)]

theorem EE_self (m : ℕ) : EE m m = (-1) ^ m * eProd m := by
  classical
  rw [EE, PowerSeries.coeff_prod, Finset.sum_eq_single (onesF m)]
  · simp only [coeff_facS, onesF, Finsupp.equivFunOnFinite_symm_apply_apply, one_ne_zero,
      if_false, if_true]
    rw [Finset.prod_neg, eProd, Finset.card_univ, Fintype.card_fin]
  · intro l hl hne
    rw [Finset.mem_finsuppAntidiag] at hl
    have h1 : ∑ i, l i = m := hl.1
    by_cases h2 : ∃ i, 2 ≤ l i
    · obtain ⟨i, hi⟩ := h2
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [coeff_facS, if_neg (by omega), if_neg (by omega)]
    · push Not at h2
      exfalso
      apply hne
      by_contra hne'
      obtain ⟨i, hi⟩ : ∃ i, l i ≠ 1 := by
        by_contra h
        push Not at h
        apply hne'
        ext i
        simp [onesF, h i]
      have hlt : ∑ i, l i < ∑ _i : Fin m, 1 :=
        Finset.sum_lt_sum (fun i _ => by have := h2 i; omega) ⟨i, Finset.mem_univ i,
          by have := h2 i; omega⟩
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hlt
      omega
  · intro h
    exact absurd (Finset.mem_finsuppAntidiag.mpr ⟨by simp [onesF], Finset.subset_univ _⟩) h

/-- `Σ_{a + b = k} EE_a h_b = 0` for `k ≥ 1`. -/
theorem sum_EE_hh (m k : ℕ) (hk : 1 ≤ k) :
    ∑ p ∈ Finset.antidiagonal k, EE m p.1 * hh m p.2 = 0 := by
  have h : (∏ i : Fin m, facS (X i : MvPolynomial (Fin m) ℂ)) *
      ∏ i : Fin m, geomS (X i : MvPolynomial (Fin m) ℂ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => facS_mul_geomS _
  have := congrArg (PowerSeries.coeff k) h
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, if_neg (by omega)] at this
  exact this

/-! ### The ideal part -/

/-- The span of the products `h_q · g` with `q ≥ t` and `g` symmetric. -/
def jSym (m t : ℕ) : Submodule ℂ (MvPolynomial (Fin m) ℂ) :=
  Submodule.span ℂ {x | ∃ q g, t ≤ q ∧ IsSymmetric g ∧ x = hh m q * g}

theorem hh_mul_mem_jSym {m t q : ℕ} (hq : t ≤ q) {g : MvPolynomial (Fin m) ℂ}
    (hg : g.IsSymmetric) : hh m q * g ∈ jSym m t :=
  Submodule.subset_span ⟨q, g, hq, hg, rfl⟩

theorem jSym_mono {m t t' : ℕ} (h : t ≤ t') : jSym m t' ≤ jSym m t :=
  Submodule.span_mono fun _ ⟨q, g, hq, hg, hx⟩ => ⟨q, g, h.trans hq, hg, hx⟩

theorem isSymmetric_of_mem_jSym {m t : ℕ} {x : MvPolynomial (Fin m) ℂ} (hx : x ∈ jSym m t) :
    x.IsSymmetric := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, g, -, hg, rfl⟩ := hy
    exact (hh_isSymmetric m q).mul hg
  | zero => exact IsSymmetric.zero
  | add y z _ _ hy hz => exact hy.add hz
  | smul c y _ hy => exact hy.smul c

theorem mul_mem_jSym {m t : ℕ} {x : MvPolynomial (Fin m) ℂ} (hx : x ∈ jSym m t)
    {g : MvPolynomial (Fin m) ℂ} (hg : g.IsSymmetric) : x * g ∈ jSym m t := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, g', hq, hg', rfl⟩ := hy
    rw [mul_assoc]
    exact hh_mul_mem_jSym hq (hg'.mul hg)
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact add_mem hy hz
  | smul c y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hy

theorem eProd_mul_hh_mem (m q : ℕ) (hm : 1 ≤ m) : eProd m * hh m q ∈ jSym m (q + 1) := by
  have h := sum_EE_hh m (m + q) (by omega)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one,
    show m + q + 1 = m + (q + 1) by omega, Finset.sum_range_add, Finset.sum_range_succ'] at h
  have hz : ∑ k ∈ Finset.range q, EE m (m + (k + 1)) * hh m (m + q - (m + (k + 1))) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [EE_eq_zero m _ (by omega), zero_mul]
  rw [hz, zero_add, add_zero, Nat.add_sub_cancel_left] at h
  have hE : eProd m * hh m q = (-1) ^ m * (EE m m * hh m q) := by
    rw [EE_self, ← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
      one_mul]
  rw [hE, eq_neg_of_add_eq_zero_right h, mul_neg, Finset.mul_sum]
  refine neg_mem (Submodule.sum_mem _ fun k hk => ?_)
  rw [Finset.mem_range] at hk
  rw [mul_comm (EE m k), ← mul_assoc, mul_comm _ (hh m _), mul_assoc]
  exact hh_mul_mem_jSym (by omega) (IsSymmetric.mul (by
    intro σ; rw [map_pow, map_neg, map_one]) (EE_isSymmetric m k))

theorem eProd_mul_mem_jSym {m t : ℕ} (hm : 1 ≤ m) {x : MvPolynomial (Fin m) ℂ}
    (hx : x ∈ jSym m t) : eProd m * x ∈ jSym m (t + 1) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, g, hq, hg, rfl⟩ := hy
    rw [← mul_assoc]
    exact jSym_mono (by omega) (mul_mem_jSym (eProd_mul_hh_mem m q hm) hg)
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy

theorem hh_zero (m : ℕ) : hh m 0 = 1 := by
  rw [hh_eq_coeff_geom, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
  simp [geomS]

/-! ### `rho` and symmetry, and lifting the ideal part -/

/-- The permutation fixing `0` and acting by `τ` on the rest. -/
def permLift {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, τ)

theorem rho_rename_permLift {m : ℕ} (τ : Equiv.Perm (Fin m)) (f : MvPolynomial (Fin (m + 1)) ℂ) :
    rho m (rename (permLift τ) f) = rename τ (rho m f) := by
  have : (rho m).comp (rename (permLift τ)) = (rename τ).comp (rho m) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [permLift, rho_X_zero]
    · simp only [AlgHom.comp_apply, rename_X, rho_X_succ, permLift,
        Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
  exact congrArg (fun φ => φ f) this

theorem rho_isSymmetric {m : ℕ} {f : MvPolynomial (Fin (m + 1)) ℂ} (hf : f.IsSymmetric) :
    (rho m f).IsSymmetric := by
  intro τ
  rw [← rho_rename_permLift, hf]

theorem lift_jSym {m t : ℕ} {x : MvPolynomial (Fin m) ℂ} (hx : x ∈ jSym m t) :
    ∃ y ∈ jSym (m + 1) t, rho m y = x := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, g, hq, hg, rfl⟩ := hz
    refine ⟨hh (m + 1) q * liftS m g, hh_mul_mem_jSym hq ?_, ?_⟩
    · exact (mem_symmetricSubalgebra _).mp (liftS_mem_symmetric m g)
    · rw [map_mul, rho_hh, rho_liftS hg]
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨ya, hya, rfl⟩ := ha
    obtain ⟨yb, hyb, rfl⟩ := hb
    exact ⟨ya + yb, add_mem hya hyb, map_add _ _ _⟩
  | smul c a _ ha =>
    obtain ⟨ya, hya, rfl⟩ := ha
    exact ⟨c • ya, Submodule.smul_mem _ c hya, map_smul _ _ _⟩

theorem eProd_mul_mem_boxSupp {k t : ℕ} {p : MvPolynomial (Fin k) ℂ} (hp : p ∈ boxSupp k t) :
    eProd k * p ∈ boxSupp k (t + 1) := by
  rw [mem_restrictSupport_iff] at hp
  rw [p.as_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun β hβ => ?_
  rw [eProd_eq, monomial_mul, one_mul]
  refine monomial_mem_restrictSupport (fun i => ?_) _
  have := hp hβ i
  simp only [Finsupp.add_apply, onesF, Finsupp.equivFunOnFinite_symm_apply_apply]
  omega

/-- **The Grassmannian spanning lemma**: every symmetric polynomial in `m` variables is a
symmetric polynomial with all exponents `< t` plus an element of the span of the `h_q · g`
(`q ≥ t`, `g` symmetric). -/
theorem grassmann_span (m : ℕ) : ∀ (t : ℕ) (f : MvPolynomial (Fin m) ℂ), f.IsSymmetric →
    ∃ P, P.IsSymmetric ∧ P ∈ boxSupp m t ∧ f - P ∈ jSym m t := by
  induction m with
  | zero =>
    intro t f _
    refine ⟨f, ‹_›, ?_, by rw [sub_self]; exact zero_mem _⟩
    rw [mem_restrictSupport_iff]
    intro β _ i
    exact i.elim0
  | succ m ihm =>
    intro t
    induction t with
    | zero =>
      intro f hf
      refine ⟨0, IsSymmetric.zero, zero_mem _, ?_⟩
      rw [sub_zero, ← one_mul f, ← hh_zero]
      exact hh_mul_mem_jSym le_rfl hf
    | succ t iht =>
      intro f hf
      obtain ⟨Pb, hPb, hPbox, hjb⟩ := ihm (t + 1) (rho m f) (rho_isSymmetric hf)
      obtain ⟨j, hj, hrj⟩ := lift_jSym hjb
      set P := liftS m Pb with hP
      have hPs : P.IsSymmetric := (mem_symmetricSubalgebra _).mp (liftS_mem_symmetric m Pb)
      have hjs : j.IsSymmetric := isSymmetric_of_mem_jSym hj
      have hr : rho m (f - P - j) = 0 := by
        rw [map_sub, map_sub, hP, rho_liftS hPb, hrj, sub_self]
      obtain ⟨r', hr's, hr'⟩ := exists_eq_eProd_mul ((hf.sub hPs).sub hjs) hr
      obtain ⟨P', hP's, hP'box, hj'⟩ := iht r' hr's
      refine ⟨P + eProd (m + 1) * P', hPs.add ((eProd_isSymmetric _).mul hP's),
        add_mem (liftS_mem_boxSupp (by omega) hPbox) (eProd_mul_mem_boxSupp hP'box), ?_⟩
      have : f - (P + eProd (m + 1) * P') = j + eProd (m + 1) * (r' - P') := by
        rw [mul_sub, ← hr']; ring
      rw [this]
      exact add_mem hj (eProd_mul_mem_jSym (by omega) hj')

end

end VOA.TwoSeries.StrictModel
