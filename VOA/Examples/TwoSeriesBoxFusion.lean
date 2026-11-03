/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesBoxWords

/-!
# The fusion recursion: `SymBoxBound n` for every `n`

Work in `Sym_m = ℂ[y_1, …, y_m]^{S_m}` modulo

* `jSym m a` — the span of `h_q · g` (`q ≥ a`, `g` symmetric), and
* `Tsym m b` — the symmetric polynomials all of whose monomials have an exponent `≥ b`;

`RelF m a b = jSym m a ⊔ Tsym m b`.  With `S = q b + r` (`r < b`) and `a = S + 1 - m`, the
quotient `Sym_m / RelF m a b` is the weight space of the fusion product of `sl₂`-modules of
dimensions `bnd q r + 1` (the balanced partition of `S` into `b` parts).  The restriction `y_0 = 0`
and multiplication by `e_m = y_1 ⋯ y_m` give the recursion

  `dim (Sym_{m+1} / RelF)_D ≤ dim (Sym_m / RelF')_D + dim (Sym_{m+1} / RelF'')_{D-m-1}`,

whose word side is `wcF_succ`.  The one new identity is

* `e_mul_hh_mem_RelF` — `e · h_q ∈ RelF (m+1) a (B+1)` once `q` is large enough: the
  generating function `Π_i (1/(1 - y_i u) - 1)` expands over subsets, and each subset product is
  killed either by the `h`-relations or by the exponent bound.

Main results:

* `fusion_span` — every degree-`D` symmetric polynomial lies in the span of at most
  `wcF b q r m D` symmetric polynomials of degree `D`, modulo `RelF m (q b + r + 1 - m) b`;
* `symBoxBound` — **`SymBoxBound n` is proved for every `n ≥ 1`**;
* `boxCount_all` — **`BoxCount n r` for every `n ≥ 1` and every `r`**;
* `twoSeries_gradedUnitary_of_strictModel_incl` — Affine GU ⇒ GU of `M(2, 2n+3)`,
  conditional only on `hA`, detection `det` and the structural half `BoxInclusion`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SocleEval
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

/-! ### The truncation relations -/

/-- Symmetric polynomials all of whose monomials have an exponent `≥ b`. -/
def Tsym (m b : ℕ) : Submodule ℂ (MvPolynomial (Fin m) ℂ) :=
  Subalgebra.toSubmodule (symmetricSubalgebra (Fin m) ℂ) ⊓
    restrictSupport ℂ {γ | ∃ i, b ≤ γ i}

/-- All the relations. -/
def RelF (m a b : ℕ) : Submodule ℂ (MvPolynomial (Fin m) ℂ) := jSym m a ⊔ Tsym m b

theorem isSymmetric_of_mem_Tsym {m b : ℕ} {x : MvPolynomial (Fin m) ℂ} (hx : x ∈ Tsym m b) :
    x.IsSymmetric := (mem_symmetricSubalgebra _).mp hx.1

theorem isSymmetric_of_mem_RelF {m a b : ℕ} {x : MvPolynomial (Fin m) ℂ}
    (hx : x ∈ RelF m a b) : x.IsSymmetric := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  exact (isSymmetric_of_mem_jSym hy).add (isSymmetric_of_mem_Tsym hz)

theorem mem_Tsym_iff {m b : ℕ} {x : MvPolynomial (Fin m) ℂ} :
    x ∈ Tsym m b ↔ x.IsSymmetric ∧ ∀ γ ∈ x.support, ∃ i, b ≤ γ i := by
  rw [Tsym, Submodule.mem_inf, Subalgebra.mem_toSubmodule, mem_symmetricSubalgebra,
    mem_restrictSupport_iff]
  exact and_congr_right fun _ => ⟨fun h γ hγ => h hγ, fun h γ hγ => h γ hγ⟩

theorem mul_mem_Tsym {m b : ℕ} {x : MvPolynomial (Fin m) ℂ} (hx : x ∈ Tsym m b)
    {g : MvPolynomial (Fin m) ℂ} (hg : g.IsSymmetric) : x * g ∈ Tsym m b := by
  classical
  rw [mem_Tsym_iff] at hx ⊢
  refine ⟨hx.1.mul hg, fun γ hγ => ?_⟩
  obtain ⟨α, hα, β, -, rfl⟩ := Finset.mem_add.mp (support_mul x g hγ)
  obtain ⟨i, hi⟩ := hx.2 α hα
  exact ⟨i, le_trans hi (by simp)⟩

theorem mul_mem_RelF {m a b : ℕ} {x : MvPolynomial (Fin m) ℂ} (hx : x ∈ RelF m a b)
    {g : MvPolynomial (Fin m) ℂ} (hg : g.IsSymmetric) : x * g ∈ RelF m a b := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [add_mul]
  exact add_mem (Submodule.mem_sup_left (mul_mem_jSym hy hg))
    (Submodule.mem_sup_right (mul_mem_Tsym hz hg))

theorem eProd_mul_mem_Tsym {k b : ℕ} {x : MvPolynomial (Fin k) ℂ} (hx : x ∈ Tsym k b) :
    eProd k * x ∈ Tsym k (b + 1) := by
  classical
  rw [mem_Tsym_iff] at hx ⊢
  refine ⟨(eProd_isSymmetric k).mul hx.1, fun γ hγ => ?_⟩
  rw [eProd_eq] at hγ
  obtain ⟨α, hα, β, hβ, rfl⟩ := Finset.mem_add.mp (support_mul _ x hγ)
  rw [Finset.mem_singleton.mp (support_monomial_subset hα)]
  obtain ⟨i, hi⟩ := hx.2 β hβ
  refine ⟨i, ?_⟩
  simp only [Finsupp.add_apply, onesF, Finsupp.equivFunOnFinite_symm_apply_apply]
  omega

/-! ### Restriction and lifting of the truncation relations -/

theorem coeff_rho_eq_cons {m : ℕ} (x : MvPolynomial (Fin (m + 1)) ℂ) (γ : Fin m →₀ ℕ) :
    coeff γ (rho m x) = coeff (Finsupp.cons 0 γ) x := by
  rw [← coeff_tail_rho x (Finsupp.cons 0 γ) (Finsupp.cons_zero _ _), Finsupp.tail_cons]

theorem rho_mem_Tsym {m b : ℕ} (hb : 1 ≤ b) {x : MvPolynomial (Fin (m + 1)) ℂ}
    (hx : x ∈ Tsym (m + 1) b) : rho m x ∈ Tsym m b := by
  rw [mem_Tsym_iff] at hx ⊢
  refine ⟨rho_isSymmetric hx.1, fun γ hγ => ?_⟩
  rw [mem_support_iff, coeff_rho_eq_cons] at hγ
  obtain ⟨i, hi⟩ := hx.2 _ (mem_support_iff.mpr hγ)
  cases i using Fin.cases with
  | zero => rw [Finsupp.cons_zero] at hi; omega
  | succ j => exact ⟨j, by rwa [Finsupp.cons_succ] at hi⟩

theorem OS_mem_restrictSupport {k b : ℕ} {β : Fin k →₀ ℕ} (hβ : ∃ i, b ≤ β i) :
    OS k β ∈ restrictSupport ℂ {γ : Fin k →₀ ℕ | ∃ i, b ≤ γ i} := by
  obtain ⟨i, hi⟩ := hβ
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [rename_monomial]
  refine monomial_mem_restrictSupport ?_ 1
  rw [Set.mem_setOf_eq]
  refine ⟨σ i, ?_⟩
  rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply]
  exact hi

theorem liftS_mem_Tsym {m b : ℕ} {g : MvPolynomial (Fin m) ℂ} (hg : g ∈ Tsym m b) :
    liftS m g ∈ Tsym (m + 1) b := by
  rw [mem_Tsym_iff] at hg
  refine ⟨liftS_mem_symmetric m g, ?_⟩
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ hγ => Submodule.smul_mem _ _ ?_)
  obtain ⟨i, hi⟩ := hg.2 γ hγ
  exact OS_mem_restrictSupport ⟨i.succ, by rw [Finsupp.cons_succ]; exact hi⟩

theorem lift_RelF {m a b : ℕ} {x : MvPolynomial (Fin m) ℂ} (hx : x ∈ RelF m a b) :
    ∃ y ∈ RelF (m + 1) a b, rho m y = x := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u', hu', rfl⟩ := lift_jSym hu
  refine ⟨u' + liftS m v, add_mem (Submodule.mem_sup_left hu')
    (Submodule.mem_sup_right (liftS_mem_Tsym hv)), ?_⟩
  rw [map_add, rho_liftS (isSymmetric_of_mem_Tsym hv)]

/-! ### Homogeneous components -/

theorem degree_mapDomain_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (β : Fin k →₀ ℕ) :
    Finsupp.degree (Finsupp.mapDomain σ β) = Finsupp.degree β := by
  rw [degree_eq_sum, degree_eq_sum]
  simp_rw [Finsupp.mapDomain_equiv_apply]
  exact Fintype.sum_equiv σ.symm _ _ fun _ => rfl

theorem homogeneousComponent_monomial' {k : ℕ} (D : ℕ) (β : Fin k →₀ ℕ) (c : ℂ) :
    homogeneousComponent D (monomial β c) = if Finsupp.degree β = D then monomial β c else 0 := by
  rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
    (isHomogeneous_monomial c rfl))]
  split_ifs <;> simp_all [eq_comm]

theorem homogeneousComponent_rename {k : ℕ} (D : ℕ) (σ : Equiv.Perm (Fin k))
    (p : MvPolynomial (Fin k) ℂ) :
    homogeneousComponent D (rename σ p) = rename σ (homogeneousComponent D p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial β c =>
    rw [rename_monomial, homogeneousComponent_monomial', homogeneousComponent_monomial',
      degree_mapDomain_perm]
    split_ifs
    · rw [rename_monomial]
    · rw [map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

theorem isSymmetric_homogeneousComponent {k : ℕ} (D : ℕ) {p : MvPolynomial (Fin k) ℂ}
    (hp : p.IsSymmetric) : (homogeneousComponent D p).IsSymmetric := by
  intro σ
  rw [← homogeneousComponent_rename, hp σ]

theorem homogeneousComponent_mem_jSym {k a : ℕ} (D : ℕ) {x : MvPolynomial (Fin k) ℂ}
    (hx : x ∈ jSym k a) : homogeneousComponent D x ∈ jSym k a := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, g, hq, hg, rfl⟩ := hy
    conv => rw [← sum_homogeneousComponent g]
    rw [Finset.mul_sum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
      ((hh_isHomogeneous k q).mul (homogeneousComponent_isHomogeneous i g)))]
    split_ifs
    · exact hh_mul_mem_jSym hq (isSymmetric_homogeneousComponent i hg)
    · exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem homogeneousComponent_mem_Tsym {k b : ℕ} (D : ℕ) {x : MvPolynomial (Fin k) ℂ}
    (hx : x ∈ Tsym k b) : homogeneousComponent D x ∈ Tsym k b := by
  rw [mem_Tsym_iff] at hx ⊢
  refine ⟨isSymmetric_homogeneousComponent D hx.1, fun γ hγ => hx.2 γ ?_⟩
  rw [mem_support_iff, coeff_homogeneousComponent] at hγ
  rw [mem_support_iff]
  split_ifs at hγ
  · exact hγ
  · exact absurd rfl hγ

theorem homogeneousComponent_mem_RelF {k a b : ℕ} (D : ℕ) {x : MvPolynomial (Fin k) ℂ}
    (hx : x ∈ RelF k a b) : homogeneousComponent D x ∈ RelF k a b := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact add_mem (Submodule.mem_sup_left (homogeneousComponent_mem_jSym D hy))
    (Submodule.mem_sup_right (homogeneousComponent_mem_Tsym D hz))

theorem degree_cons_zero {m : ℕ} (γ : Fin m →₀ ℕ) :
    Finsupp.degree (Finsupp.cons 0 γ) = Finsupp.degree γ := by
  rw [degree_eq_sum, degree_eq_sum, Fin.sum_univ_succ, Finsupp.cons_zero, zero_add]
  simp_rw [Finsupp.cons_succ]

theorem rho_homogeneousComponent {m : ℕ} (D : ℕ) (x : MvPolynomial (Fin (m + 1)) ℂ) :
    rho m (homogeneousComponent D x) = homogeneousComponent D (rho m x) := by
  ext γ
  rw [coeff_rho_eq_cons, coeff_homogeneousComponent, coeff_homogeneousComponent,
    coeff_rho_eq_cons, degree_cons_zero]

theorem liftS_mem_homogeneous {m D : ℕ} {g : MvPolynomial (Fin m) ℂ}
    (hg : g ∈ homogeneousSubmodule (Fin m) ℂ D) :
    liftS m g ∈ homogeneousSubmodule (Fin m.succ) ℂ D := by
  rw [mem_homogeneousSubmodule] at hg
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ hγ => Submodule.smul_mem _ _ ?_)
  rw [mem_homogeneousSubmodule]
  have h := OS_isHomogeneous (m + 1) (Finsupp.cons 0 γ)
  have hd : Finsupp.degree γ = D := by
    rw [Finsupp.degree_eq_weight_one]; exact hg (mem_support_iff.mp hγ)
  rwa [degree_cons_zero, hd] at h

theorem homogeneousComponent_mul_homog {k a : ℕ} {φ : MvPolynomial (Fin k) ℂ}
    (hφ : φ.IsHomogeneous a) (g : MvPolynomial (Fin k) ℂ) (i : ℕ) :
    homogeneousComponent (i + a) (φ * g) = φ * homogeneousComponent i g := by
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [Finset.mul_sum, map_sum]
  have h : ∀ j ∈ Finset.range (g.totalDegree + 1),
      homogeneousComponent (i + a) (φ * homogeneousComponent j g) =
        if j = i then φ * homogeneousComponent i g else 0 := by
    intro j _
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
      (hφ.mul (homogeneousComponent_isHomogeneous j g)))]
    split_ifs with h1 h2 h2
    · subst h2; rfl
    · omega
    · omega
    · rfl
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with hi
  · rfl
  · rw [Finset.mem_range, not_lt] at hi
    rw [homogeneousComponent_eq_zero _ _ (by omega), mul_zero]

theorem eProd_isHomogeneous (k : ℕ) : (eProd k).IsHomogeneous k := by
  rw [eProd_eq]
  refine isHomogeneous_monomial _ ?_
  rw [degree_eq_sum]
  simp [onesF]

/-- If `e · g'` is homogeneous of degree `D`, so is `g'` of degree `D - k` (and `g' = 0` if
`D < k`). -/
theorem isHomogeneous_of_eProd_mul {k D : ℕ} {g' : MvPolynomial (Fin k) ℂ}
    (h : (eProd k * g').IsHomogeneous D) : g'.IsHomogeneous (D - k) ∧ (D < k → g' = 0) := by
  have hz : ∀ i, i + k ≠ D → homogeneousComponent i g' = 0 := by
    intro i hi
    have h1 := homogeneousComponent_mul_homog (eProd_isHomogeneous k) g' i
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr h), if_neg hi] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (eProd_ne_zero k)
  have hdeg : ∀ d ∈ g'.support, Finsupp.degree d + k = D := by
    intro d hd
    by_contra hne
    have h2 := congrArg (coeff d) (hz _ hne)
    rw [coeff_homogeneousComponent, if_pos rfl, coeff_zero] at h2
    exact (mem_support_iff.mp hd) h2
  refine ⟨fun d hd => ?_, fun hD => ?_⟩
  · have := hdeg d (mem_support_iff.mpr hd)
    have e : (Finsupp.weight 1) d = Finsupp.degree d := by
      rw [Finsupp.degree_eq_weight_one]; rfl
    omega
  · ext d
    rw [coeff_zero]
    by_contra hd
    have := hdeg d (mem_support_iff.mpr hd)
    omega

/-! ### Symmetrization and the key identity -/

/-- The symmetrization `(1/k!) Σ_σ σ(p)`. -/
def symz (k : ℕ) (p : MvPolynomial (Fin k) ℂ) : MvPolynomial (Fin k) ℂ :=
  ((k.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin k), rename σ p

theorem symz_isSymmetric (k : ℕ) (p : MvPolynomial (Fin k) ℂ) : (symz k p).IsSymmetric := by
  intro e
  rw [symz, map_smul, map_sum]
  simp_rw [rename_rename]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft e) _ _ fun σ => rfl

theorem symz_of_isSymmetric {k : ℕ} {p : MvPolynomial (Fin k) ℂ} (hp : p.IsSymmetric) :
    symz k p = p := by
  rw [symz, sum_rename_of_isSymmetric hp, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]

theorem symz_mul_symmetric {k : ℕ} (p : MvPolynomial (Fin k) ℂ) {h : MvPolynomial (Fin k) ℂ}
    (hh' : h.IsSymmetric) : symz k (p * h) = symz k p * h := by
  rw [symz, symz, smul_mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, hh' σ]

theorem support_mul_X_pow_subset {k B : ℕ} (p : MvPolynomial (Fin k) ℂ) (j : Fin k) :
    ∀ γ ∈ (p * X j ^ B).support, B ≤ γ j := by
  classical
  intro γ hγ
  obtain ⟨α, -, β, hβ, rfl⟩ := Finset.mem_add.mp (support_mul p _ hγ)
  rw [X_pow_eq_monomial] at hβ
  rw [Finset.mem_singleton.mp (support_monomial_subset hβ)]
  simp

/-- The ideal of `ℂ[y]` generated by the `h_k` (`k ≥ a`) and the `y_i^B`. -/
def idealF (M a B : ℕ) : Ideal (MvPolynomial (Fin M) ℂ) :=
  Ideal.span ({x | ∃ k, a ≤ k ∧ x = hh M k} ∪ {x | ∃ i, x = X i ^ B})

theorem symz_mul_mem_RelF {M a B : ℕ} {p : MvPolynomial (Fin M) ℂ} (hp : p ∈ idealF M a B) :
    ∀ c, symz M (c * p) ∈ RelF M a B := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    intro c
    rcases hx with ⟨k, hk, rfl⟩ | ⟨i, rfl⟩
    · rw [symz_mul_symmetric c (hh_isSymmetric M k), mul_comm]
      exact Submodule.mem_sup_left (hh_mul_mem_jSym hk (symz_isSymmetric M c))
    · refine Submodule.mem_sup_right ⟨(mem_symmetricSubalgebra _).mpr (symz_isSymmetric M _), ?_⟩
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => ?_)
      rw [mem_restrictSupport_iff, map_mul, map_pow, rename_X]
      intro γ hγ
      exact ⟨σ i, support_mul_X_pow_subset _ _ γ hγ⟩
  | zero =>
    intro c
    rw [mul_zero, symz]
    simp only [map_zero, Finset.sum_const_zero, smul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro c
    have h : symz M (c * (x + y)) = symz M (c * x) + symz M (c * y) := by
      simp only [symz, mul_add, map_add, Finset.sum_add_distrib, smul_add]
    rw [h]
    exact add_mem (hx c) (hy c)
  | smul d x _ hx =>
    intro c
    rw [smul_eq_mul, ← mul_assoc]
    exact hx (c * d)

theorem mem_RelF_of_mem_idealF {M a B : ℕ} {p : MvPolynomial (Fin M) ℂ}
    (hp : p ∈ idealF M a B) (hs : p.IsSymmetric) : p ∈ RelF M a B := by
  have := symz_mul_mem_RelF hp 1
  rwa [one_mul, symz_of_isSymmetric hs] at this

theorem geomS_sub_one {A : Type*} [CommRing A] (a : A) :
    geomS a - 1 = PowerSeries.X * (PowerSeries.C a * geomS a) := by
  ext k
  rcases k with _ | k
  · simp [geomS, PowerSeries.coeff_zero_X_mul]
  · rw [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
    simp [geomS, pow_succ, mul_comm]

theorem coeff_prod_facS_eq_zero {M : ℕ} (U : Finset (Fin M)) (j : ℕ) (hj : U.card < j) :
    PowerSeries.coeff j (∏ i ∈ U, facS (X i : MvPolynomial (Fin M) ℂ)) = 0 := by
  classical
  rw [PowerSeries.coeff_prod]
  refine Finset.sum_eq_zero fun l hl => ?_
  rw [Finset.mem_finsuppAntidiag] at hl
  obtain ⟨i, hiU, hi⟩ : ∃ i ∈ U, 2 ≤ l i := by
    by_contra h
    push Not at h
    have : ∑ i ∈ U, l i ≤ ∑ _i ∈ U, 1 := Finset.sum_le_sum fun i hi => by
      have := h i hi; omega
    rw [Finset.sum_const, smul_eq_mul, mul_one] at this
    have h1 : ∑ i ∈ U, l i = j := hl.1
    omega
  refine Finset.prod_eq_zero hiU ?_
  rw [coeff_facS, if_neg (by omega), if_neg (by omega)]

/-- **The key identity**: `e · h_q ∈ RelF M a B` as soon as, for every `s ≤ M`, either
`a ≤ q + s` or `s (B - 1) < q + M`. -/
theorem e_mul_hh_mem_RelF {M a B q : ℕ}
    (hcond : ∀ s ≤ M, a ≤ q + s ∨ s * (B - 1) < q + M) :
    eProd M * hh M q ∈ RelF M a B := by
  classical
  refine mem_RelF_of_mem_idealF ?_ ((eProd_isSymmetric M).mul (hh_isSymmetric M q))
  set G : Fin M → PowerSeries (MvPolynomial (Fin M) ℂ) := fun i => geomS (X i) with hG
  -- the generating function
  have hgen : eProd M * hh M q = PowerSeries.coeff (q + M) (∏ i, (G i - 1)) := by
    simp_rw [hG, geomS_sub_one]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← map_prod, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
      Nat.add_sub_cancel, PowerSeries.coeff_C_mul]
    rfl
  rw [hgen]
  simp_rw [sub_eq_add_neg]
  rw [Finset.prod_add, map_sum]
  refine Ideal.sum_mem _ fun T _ => ?_
  rw [Finset.prod_const, show ((-1 : PowerSeries (MvPolynomial (Fin M) ℂ))) ^
    (Finset.univ \ T).card = PowerSeries.C ((-1) ^ (Finset.univ \ T).card) by
      rw [map_pow, map_neg, map_one], PowerSeries.coeff_mul_C]
  refine Ideal.mul_mem_right _ _ ?_
  rcases hcond T.card (by simpa using Finset.card_le_univ T) with hA | hB
  · -- the `h`-relations
    have hsplit : ∏ i ∈ T, G i =
        (∏ i, G i) * ∏ i ∈ Finset.univ \ T, facS (X i : MvPolynomial (Fin M) ℂ) := by
      have h1 : ∏ i ∈ Finset.univ \ T, (facS (X i : MvPolynomial (Fin M) ℂ) * G i) = 1 :=
        Finset.prod_eq_one fun i _ => facS_mul_geomS _
      rw [Finset.prod_mul_distrib] at h1
      rw [← Finset.prod_sdiff (Finset.subset_univ T),
        mul_comm (∏ i ∈ Finset.univ \ T, G i) (∏ i ∈ T, G i), mul_assoc,
        mul_comm (∏ i ∈ Finset.univ \ T, G i), h1, mul_one]
    rw [hsplit, PowerSeries.coeff_mul]
    refine Ideal.sum_mem _ fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    by_cases hp2 : (Finset.univ \ T).card < p.2
    · rw [coeff_prod_facS_eq_zero _ _ hp2, mul_zero]; exact zero_mem _
    · push Not at hp2
      rw [Finset.card_univ_diff, Fintype.card_fin] at hp2
      refine Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl ⟨p.1, ?_, rfl⟩))
      have := Finset.card_le_univ T
      rw [Fintype.card_fin] at this
      omega
  · -- the exponent bound
    rw [PowerSeries.coeff_prod]
    refine Ideal.sum_mem _ fun l hl => ?_
    rw [Finset.mem_finsuppAntidiag] at hl
    obtain ⟨i, hiT, hi⟩ : ∃ i ∈ T, B ≤ l i := by
      by_contra h
      push Not at h
      have : ∑ i ∈ T, l i ≤ ∑ _i ∈ T, (B - 1) := Finset.sum_le_sum fun i hi => by
        have := h i hi; omega
      rw [Finset.sum_const, smul_eq_mul] at this
      have h1 : ∑ i ∈ T, l i = q + M := hl.1
      omega
    rw [← Finset.mul_prod_erase T _ hiT]
    refine Ideal.mul_mem_right _ _ ?_
    simp only [hG, geomS, PowerSeries.coeff_mk]
    rw [← Nat.sub_add_cancel hi, pow_add]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inr ⟨i, rfl⟩))

/-! ### The recursion -/

theorem fusion_hcond (B m q r k s : ℕ) (hS : m + 1 ≤ q * (B + 1) + r)
    (hk : q * B + (r - 1) + 1 - (m + 1) ≤ k) (_hs : s ≤ m + 1) :
    q * (B + 1) + r + 1 - (m + 1) ≤ k + s ∨ s * (B + 1 - 1) < k + (m + 1) := by
  rw [Nat.add_sub_cancel]
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hexp : q * (B + 1) = q * B + q := by ring
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hq : 1 ≤ q := by
      by_contra hq; push Not at hq
      interval_cases q; omega
    have hsq : s ≤ q - 1 := by omega
    have hsB : s * B ≤ (q - 1) * B := Nat.mul_le_mul_right B hsq
    have hqB : (q - 1) * B ≤ q * B := Nat.mul_le_mul_right B (by omega)
    omega
  · have hsq : s ≤ q := by omega
    have hsB : s * B ≤ q * B := Nat.mul_le_mul_right B hsq
    omega

theorem rot_S (B m q r : ℕ) (hr : r ≤ B) (hS : m + 1 ≤ q * (B + 1) + r) :
    (if 1 ≤ r then q else q - 1) * (B + 1) + (if 1 ≤ r then r - 1 else B) + 1 - m =
      q * (B + 1) + r + 1 - (m + 1) := by
  split_ifs with h
  · have : q * (B + 1) + (r - 1) + 1 = q * (B + 1) + r := by omega
    omega
  · have hr0 : r = 0 := by omega
    subst hr0
    have hq : 1 ≤ q := by
      by_contra hq; push Not at hq
      interval_cases q; omega
    have : (q - 1) * (B + 1) + B + 1 = q * (B + 1) := by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega

theorem mem_symDeg_iff {m D : ℕ} {f : MvPolynomial (Fin m) ℂ} :
    f ∈ symDeg m D ↔ f.IsSymmetric ∧ f.IsHomogeneous D := by
  rw [symDeg, Submodule.mem_inf, Subalgebra.mem_toSubmodule, mem_symmetricSubalgebra,
    mem_homogeneousSubmodule]

theorem rho_mem_symDeg {m D : ℕ} {f : MvPolynomial (Fin (m + 1)) ℂ} (hf : f ∈ symDeg (m + 1) D) :
    rho m f ∈ symDeg m D := by
  rw [mem_symDeg_iff] at hf ⊢
  refine ⟨rho_isSymmetric hf.1, ?_⟩
  have h : homogeneousComponent D f = f := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hf.2), if_pos rfl]
  rw [← h, rho_homogeneousComponent]
  exact homogeneousComponent_isHomogeneous D _

theorem eProd_mul_mem_RelF {m a'' a B : ℕ}
    (hcond : ∀ k, a'' ≤ k → ∀ s ≤ m + 1, a ≤ k + s ∨ s * (B + 1 - 1) < k + (m + 1))
    {x : MvPolynomial (Fin (m + 1)) ℂ} (hx : x ∈ RelF (m + 1) a'' B) :
    eProd (m + 1) * x ∈ RelF (m + 1) a (B + 1) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  clear hx
  rw [mul_add]
  refine add_mem ?_ (Submodule.mem_sup_right (eProd_mul_mem_Tsym hv))
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, g, hk, hg, rfl⟩ := hy
    rw [← mul_assoc]
    exact mul_mem_RelF (e_mul_hh_mem_RelF (hcond k hk)) hg
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy

theorem fusion_span_zero (B q r D : ℕ) :
    ∃ s : Finset (MvPolynomial (Fin 0) ℂ), (∀ z ∈ s, z ∈ symDeg 0 D) ∧ s.card ≤ wcF B q r 0 D ∧
      ∀ f ∈ symDeg 0 D, f ∈ Submodule.span ℂ (s : Set (MvPolynomial (Fin 0) ℂ)) ⊔
        RelF 0 (q * B + r + 1 - 0) B := by
  classical
  by_cases hD : D = 0
  · subst hD
    refine ⟨{1}, fun z hz => ?_, ?_, fun f hf => ?_⟩
    · rw [Finset.mem_singleton] at hz
      subst hz
      exact mem_symDeg_iff.mpr ⟨IsSymmetric.one, isHomogeneous_one _ _⟩
    · rw [Finset.card_singleton, wcF]
      refine Finset.card_pos.mpr ⟨0, ?_⟩
      rw [Finset.mem_filter, mem_wordsF]
      refine ⟨⟨fun j => Nat.zero_le _, by simp⟩, ?_⟩
      simp [statF, minS, invF]
    · refine Submodule.mem_sup_left ?_
      have h1 : f = coeff 0 f • (1 : MvPolynomial (Fin 0) ℂ) := by
        conv_lhs => rw [eq_C_of_isEmpty f]
        rw [smul_eq_C_mul, mul_one]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · refine ⟨∅, fun z hz => absurd hz (Finset.notMem_empty z), by simp, fun f hf => ?_⟩
    have hf0 : f = 0 := by
      rw [mem_symDeg_iff] at hf
      rw [eq_C_of_isEmpty f]
      by_contra h
      have hc : coeff 0 f ≠ 0 := by
        intro hc; apply h; rw [hc, map_zero]
      have := hf.2 hc
      simp at this
      exact hD this.symm
    rw [hf0]
    exact zero_mem _

theorem liftS_mem_symDeg {m D : ℕ} {z : MvPolynomial (Fin m) ℂ} (hz : z ∈ symDeg m D) :
    liftS m z ∈ symDeg (m + 1) D :=
  ⟨liftS_mem_symmetric m z, liftS_mem_homogeneous (mem_symDeg_iff.mp hz).2⟩

theorem eProd_mul_mem_symDeg {k D : ℕ} {z : MvPolynomial (Fin k) ℂ} (hz : z ∈ symDeg k (D - k))
    (hD : k ≤ D) : eProd k * z ∈ symDeg k D := by
  rw [mem_symDeg_iff] at hz ⊢
  refine ⟨(eProd_isSymmetric k).mul hz.1, ?_⟩
  have := (eProd_isHomogeneous k).mul hz.2
  rwa [Nat.add_sub_cancel' hD] at this

/-- The common step: restrict, lift, and divide by `e`. -/
theorem fusion_step {m B a D : ℕ} (s₁ : Finset (MvPolynomial (Fin m) ℂ))
    (hs₁ : ∀ z ∈ s₁, z ∈ symDeg m D)
    (hsp₁ : ∀ f ∈ symDeg m D, f ∈ Submodule.span ℂ (s₁ : Set (MvPolynomial (Fin m) ℂ)) ⊔
      RelF m a B)
    {f : MvPolynomial (Fin (m + 1)) ℂ} (hf : f ∈ symDeg (m + 1) D) :
    ∃ r', r' ∈ symDeg (m + 1) (D - (m + 1)) ∧ (D < m + 1 → r' = 0) ∧
      f - eProd (m + 1) * r' ∈ Submodule.span ℂ ((s₁.image (liftS m) : Finset _) :
        Set (MvPolynomial (Fin (m + 1)) ℂ)) ⊔ RelF (m + 1) a B := by
  classical
  obtain ⟨u, hu, jb, hjb, hsum⟩ := Submodule.mem_sup.mp (hsp₁ (rho m f) (rho_mem_symDeg hf))
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hu
  obtain ⟨y, hy, hρy⟩ := lift_RelF hjb
  set u' := ∑ z ∈ s₁, c z • liftS m z with hu'
  have hu'span : u' ∈ Submodule.span ℂ ((s₁.image (liftS m) : Finset _) :
      Set (MvPolynomial (Fin (m + 1)) ℂ)) :=
    Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hz)))
  have hu'symDeg : u' ∈ symDeg (m + 1) D :=
    Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (liftS_mem_symDeg (hs₁ z hz))
  have hρu' : rho m u' = u := by
    rw [hu', map_sum, ← hc]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [map_smul, rho_liftS (mem_symDeg_iff.mp (hs₁ z hz)).1]
  have husymDeg : u ∈ symDeg m D := by
    rw [← hc]
    exact Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (hs₁ z hz)
  have hjbD : jb ∈ symDeg m D := by
    rw [← add_sub_cancel_left u jb, hsum]
    exact sub_mem (rho_mem_symDeg hf) husymDeg
  have hjbhc : homogeneousComponent D jb = jb := by
    rw [homogeneousComponent_of_mem (mem_symDeg_iff.mp hjbD).2 |>.trans (if_pos rfl)]
  set rD := f - u' - homogeneousComponent D y with hrD
  have hyD : homogeneousComponent D y ∈ RelF (m + 1) a B := homogeneousComponent_mem_RelF D hy
  have hyhom : homogeneousComponent D y ∈ symDeg (m + 1) D :=
    mem_symDeg_iff.mpr ⟨isSymmetric_of_mem_RelF hyD, homogeneousComponent_isHomogeneous D y⟩
  have hrDmem : rD ∈ symDeg (m + 1) D := sub_mem (sub_mem hf hu'symDeg) hyhom
  have hρr : rho m rD = 0 := by
    rw [hrD, map_sub, map_sub, hρu', rho_homogeneousComponent, hρy, hjbhc, ← hsum]
    ring
  obtain ⟨r', hr's, hrr'⟩ := exists_eq_eProd_mul (mem_symDeg_iff.mp hrDmem).1 hρr
  have hhom := isHomogeneous_of_eProd_mul (hrr' ▸ (mem_symDeg_iff.mp hrDmem).2)
  refine ⟨r', mem_symDeg_iff.mpr ⟨hr's, hhom.1⟩, hhom.2, ?_⟩
  rw [← hrr', hrD, show f - (f - u' - homogeneousComponent D y) =
    u' + homogeneousComponent D y by ring]
  exact add_mem (Submodule.mem_sup_left hu'span) (Submodule.mem_sup_right hyD)

/-- **The fusion spanning lemma.** -/
theorem fusion_span : ∀ (B m q r D : ℕ), r ≤ B - 1 →
    ∃ s : Finset (MvPolynomial (Fin m) ℂ), (∀ z ∈ s, z ∈ symDeg m D) ∧
      s.card ≤ wcF B q r m D ∧
      ∀ f ∈ symDeg m D, f ∈ Submodule.span ℂ (s : Set (MvPolynomial (Fin m) ℂ)) ⊔
        RelF m (q * B + r + 1 - m) B := by
  classical
  intro B
  induction B with
  | zero =>
    intro m q r D _
    cases m with
    | zero => exact fusion_span_zero 0 q r D
    | succ m =>
      refine ⟨∅, by simp, by simp, fun f hf => Submodule.mem_sup_right
        (Submodule.mem_sup_right ?_)⟩
      rw [mem_Tsym_iff]
      exact ⟨(mem_symDeg_iff.mp hf).1, fun γ _ => ⟨0, Nat.zero_le _⟩⟩
  | succ B ihB =>
    intro m
    induction m with
    | zero => intro q r D _; exact fusion_span_zero (B + 1) q r D
    | succ m ihm =>
      intro q r D hr
      have hr' : r ≤ B := by simpa using hr
      by_cases hS : q * (B + 1) + r ≤ m
      · refine ⟨∅, by simp, by simp, fun f hf => Submodule.mem_sup_right
          (Submodule.mem_sup_left ?_)⟩
        have h0 : q * (B + 1) + r + 1 - (m + 1) = 0 := by omega
        rw [h0, ← one_mul f, ← hh_zero (m + 1)]
        exact hh_mul_mem_jSym le_rfl (mem_symDeg_iff.mp hf).1
      push Not at hS
      have hS1 : m + 1 ≤ q * (B + 1) + r := hS
      have hqr : 1 ≤ q ∨ 1 ≤ r := by
        by_contra h
        push Not at h
        have hq0 : q = 0 := by omega
        have hr0 : r = 0 := by omega
        subst hq0 hr0
        omega
      obtain ⟨s₁, hs₁, hc₁, hsp₁⟩ := ihm (if 1 ≤ r then q else q - 1)
        (if 1 ≤ r then r - 1 else B) D (by split_ifs <;> omega)
      rw [rot_S B m q r hr' hS1] at hsp₁
      have hrec := wcF_succ B q r m D hr' hqr
      by_cases hD : m + 1 ≤ D
      · obtain ⟨s₂, hs₂, hc₂, hsp₂⟩ := ihB (m + 1) q (r - 1) (D - (m + 1)) (by omega)
        refine ⟨s₁.image (liftS m) ∪ s₂.image (eProd (m + 1) * ·), fun z hz => ?_, ?_,
          fun f hf => ?_⟩
        · rcases Finset.mem_union.mp hz with hz | hz
          · obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_image.mp hz
            exact liftS_mem_symDeg (hs₁ z₁ hz₁)
          · obtain ⟨z₂, hz₂, rfl⟩ := Finset.mem_image.mp hz
            exact eProd_mul_mem_symDeg (hs₂ z₂ hz₂) hD
        · rw [hrec, if_pos hD]
          refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
          · exact Finset.card_image_le.trans hc₁
          · exact Finset.card_image_le.trans hc₂
        · obtain ⟨r', hr'D, -, hdiff⟩ := fusion_step s₁ hs₁ hsp₁ hf
          obtain ⟨v, hv, j', hj', hvj⟩ := Submodule.mem_sup.mp (hsp₂ r' hr'D)
          obtain ⟨d, -, hd⟩ := Submodule.mem_span_finset.mp hv
          have hev : eProd (m + 1) * v ∈ Submodule.span ℂ
              ((s₂.image (eProd (m + 1) * ·) : Finset _) :
                Set (MvPolynomial (Fin (m + 1)) ℂ)) := by
            rw [← hd, Finset.mul_sum]
            refine Submodule.sum_mem _ fun z hz => ?_
            rw [mul_smul_comm]
            exact Submodule.smul_mem _ _ (Submodule.subset_span
              (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hz)))
          have hej : eProd (m + 1) * j' ∈ RelF (m + 1) (q * (B + 1) + r + 1 - (m + 1)) (B + 1) :=
            eProd_mul_mem_RelF (fun k hk s hs => fusion_hcond B m q r k s hS1 hk hs) hj'
          have hf' : f = (f - eProd (m + 1) * r') + eProd (m + 1) * v + eProd (m + 1) * j' := by
            rw [← hvj]; ring
          rw [hf']
          refine add_mem (add_mem ?_ ?_) (Submodule.mem_sup_right hej)
          · refine Submodule.mem_sup.mpr ?_
            obtain ⟨a1, ha1, b1, hb1, hab⟩ := Submodule.mem_sup.mp hdiff
            exact ⟨a1, Submodule.span_mono (by simp) ha1, b1, hb1, hab⟩
          · exact Submodule.mem_sup_left (Submodule.span_mono (by simp) hev)
      · refine ⟨s₁.image (liftS m), fun z hz => ?_, ?_, fun f hf => ?_⟩
        · obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_image.mp hz
          exact liftS_mem_symDeg (hs₁ z₁ hz₁)
        · rw [hrec, if_neg hD, add_zero]
          exact Finset.card_image_le.trans hc₁
        · obtain ⟨r', -, hr0, hdiff⟩ := fusion_step s₁ hs₁ hsp₁ hf
          rw [hr0 (by omega), mul_zero, sub_zero] at hdiff
          exact hdiff

/-! ### `SymBoxBound n` and `BoxCount n` for every `n` -/

theorem RelF_le_boxRel (n N m : ℕ) : RelF m ((n - 1) * N + 0 + 1 - m) N ≤ boxRel n N m := by
  refine sup_le ?_ ?_
  · rw [jSym, Submodule.span_le]
    rintro _ ⟨q, g, hq, -, rfl⟩
    exact Submodule.subset_span (Or.inl ⟨q, g, by omega, rfl⟩)
  · intro x hx
    rw [mem_Tsym_iff] at hx
    rw [x.as_sum]
    refine Submodule.sum_mem _ fun γ hγ => Submodule.subset_span (Or.inr ⟨γ, _, hx.2 γ hγ, rfl⟩)

/-- **`SymBoxBound n` holds for every `n ≥ 1`.** -/
theorem symBoxBound (n : ℕ) (hn : 1 ≤ n) : SymBoxBound n := by
  classical
  intro N m D _
  obtain ⟨s, hs, hc, hsp⟩ := fusion_span N m (n - 1) 0 D (Nat.zero_le _)
  set W := (boxRel n N m).comap (symDeg m D).subtype with hW
  let g : s → (↥(symDeg m D) ⧸ W) := fun z => W.mkQ ⟨z.1, hs z.1 z.2⟩
  have htop : (⊤ : Submodule ℂ (↥(symDeg m D) ⧸ W)) ≤ Submodule.span ℂ (Set.range g) := by
    rintro x -
    obtain ⟨⟨f, hf⟩, rfl⟩ := W.mkQ_surjective x
    obtain ⟨u, hu, j, hj, huj⟩ := Submodule.mem_sup.mp (hsp f hf)
    obtain ⟨c, -, hcu⟩ := Submodule.mem_span_finset.mp hu
    have huD : u ∈ symDeg m D := by
      rw [← hcu]
      exact Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (hs z hz)
    have hmk : W.mkQ ⟨f, hf⟩ = W.mkQ ⟨u, huD⟩ := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hW,
        Submodule.mem_comap]
      have : f - u = j := by rw [← huj]; ring
      simp only [Submodule.subtype_apply, AddSubgroupClass.coe_sub]
      rw [this]
      exact RelF_le_boxRel n N m hj
    rw [hmk]
    have hsum : (⟨u, huD⟩ : ↥(symDeg m D)) =
        ∑ z ∈ s.attach, c z.1 • (⟨z.1, hs z.1 z.2⟩ : ↥(symDeg m D)) := by
      apply Subtype.ext
      change u = ((∑ z ∈ s.attach, c z.1 • (⟨z.1, hs z.1 z.2⟩ : ↥(symDeg m D)) :
        ↥(symDeg m D)) : MvPolynomial (Fin m) ℂ)
      rw [Submodule.coe_sum]
      simp only [SetLike.val_smul]
      rw [← hcu]
      exact (Finset.sum_attach s (fun z => c z • z)).symm
    rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun z _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, rfl⟩)
  calc Module.rank ℂ (↥(symDeg m D) ⧸ W)
      = Module.rank ℂ (⊤ : Submodule ℂ (↥(symDeg m D) ⧸ W)) := (rank_top _ _).symm
    _ ≤ Module.rank ℂ (Submodule.span ℂ (Set.range g)) := Submodule.rank_mono htop
    _ ≤ Cardinal.mk (Set.range g) := rank_span_le _
    _ ≤ Cardinal.mk s := Cardinal.mk_range_le
    _ = s.card := Cardinal.mk_coe_finset
    _ ≤ (wcF N (n - 1) 0 m D : Cardinal) := by exact_mod_cast hc
    _ ≤ _ := by exact_mod_cast wcF_le_socleCount n N m D hn

/-- **`BoxCount n r` holds for every `n ≥ 1` and every `r`.** -/
theorem boxCount_all (n : ℕ) (hn : 1 ≤ n) (r : ℕ) : BoxCount n r :=
  boxCount_of_symBoxBound (symBoxBound n hn) r

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional only on `hA`,
detection `det` and the structural half `BoxInclusion n r`; the counting half `BoxCount` is
proved for every `n` (`boxCount_all`). -/
theorem twoSeries_gradedUnitary_of_strictModel_incl (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (incl : ∀ r, BoxInclusion n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_box n hn hA det incl (boxCount_all n hn)

end

end VOA.TwoSeries.StrictModel
