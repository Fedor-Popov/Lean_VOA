/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesLiftDegN

/-!
# Jet-ideal calculus on `ℂ[T_j]`

Pure algebra in `ℂ[T_0, T_1, …]` and its jet ideal `J_n = (jets of Tⁿ)`, used by the model route
to the high slots (`TwoSeriesHighModel`, `TwoSeriesHighReduce`, `TwoSeriesHighEndpoint`).

* `jg_isWH` — the jet `(Tⁿ)_j` is weighted homogeneous for every affine weight `m ↦ a + b m`;
* `wc_mem_jetIdealT` — every weighted homogeneous component of an element of `J_n` (for such a
  weight) lies in `J_n`; in particular the `T`-degree and the conformal-weight components;
* `wc_pderiv` — weighted components commute with `∂/∂T_m` (with the weight shift);
* `pderiv_jg` — `∂/∂T_M (T^{n+1})_i = (n + 1) (Tⁿ)_{i - M}`;
* `pderiv_shiftJ_sub` — **the jet shift**: shifting every jet index of an element of `J_{n+1}`
  by `a` turns `∂/∂T_{M-a}` into `∂/∂T_M`, modulo `J_{n+1}`;
* `euler_sum` — the weighted Euler identity over a finite set of variables;
* `JetPoincare n N k e` — **the jet-ideal Poincaré lemma** in the slot `(N, k, e)`: a `T`-polynomial
  of degree `k` and weight `e` whose derivatives `∂/∂T_M`, `M ≥ N`, all lie in `J_n` is congruent
  modulo `J_n` to a polynomial in `T_0, …, T_{N-1}`;
* `jetPoincare_zero`, `jetPoincare_one` — the cases `N = 0` (Euler) and `N = 1` (Euler for the
  index sum `T_m ↦ m`, for which `J_n` is homogeneous).

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial

noncomputable section

namespace HighJet

open InclLow SingTailDiag LiftDegN TailWitt

/-- The jet `(Tⁿ)_j`. -/
abbrev jg (n j : ℕ) : TPoly := PowerSeries.coeff j (tSer ^ n)

theorem jetIdealT_eq (n : ℕ) : jetIdealT n = Ideal.span (Set.range (jg n)) := rfl

theorem jg_mem (n j : ℕ) : jg n j ∈ jetIdealT n := Ideal.subset_span ⟨j, rfl⟩

/-! ### Weighted homogeneity of the jets -/

/-- The jet `(Tⁿ)_j` is weighted homogeneous for the affine weight `m ↦ a + b m`. -/
theorem jg_isWH (a b : ℕ) : ∀ n j : ℕ,
    IsWeightedHomogeneous (fun m => a + b * m) (jg n j) (n * a + b * j)
  | 0, j => by
    simp only [jg, pow_zero, PowerSeries.coeff_one]
    split_ifs with h
    · subst h; simpa using isWeightedHomogeneous_one ℂ (fun m => a + b * m)
    · exact isWeightedHomogeneous_zero ℂ _ _
  | n + 1, j => by
    rw [jg, pow_succ, PowerSeries.coeff_mul]
    refine IsWeightedHomogeneous.sum _ _ _ fun p hp => ?_
    have hpj := Finset.mem_antidiagonal.mp hp
    rw [tSer, PowerSeries.coeff_mk]
    have := (jg_isWH a b n p.1).mul (isWeightedHomogeneous_X ℂ (fun m => a + b * m) p.2)
    convert this using 1
    rw [← hpj]; ring

/-! ### Weighted components preserve the jet ideal -/

theorem wc_mul_mem {w : ℕ → ℕ} {v : TPoly} {dv : ℕ} (hv : IsWeightedHomogeneous w v dv)
    {I : Ideal TPoly} (hvI : v ∈ I) (E : ℕ) (c : TPoly) :
    weightedHomogeneousComponent w E (c * v) ∈ I := by
  rw [as_sum c, Finset.sum_mul, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  have h := (isWeightedHomogeneous_monomial w s (coeff s c) rfl).mul hv
  by_cases hE : E = Finsupp.weight w s + dv
  · rw [hE, h.weightedHomogeneousComponent_same]; exact I.mul_mem_left _ hvI
  · rw [h.weightedHomogeneousComponent_ne E hE]; exact I.zero_mem

/-- **Weighted components of elements of `J_n` lie in `J_n`** (affine weights). -/
theorem wc_mem_jetIdealT (a b : ℕ) {n : ℕ} (E : ℕ) {F : TPoly} (hF : F ∈ jetIdealT n) :
    weightedHomogeneousComponent (fun m => a + b * m) E F ∈ jetIdealT n := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hF
  rw [Finsupp.sum, map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [smul_eq_mul]
  exact wc_mul_mem (jg_isWH a b n j) (jg_mem n j) E _

/-- The `T`-degree components preserve `J_n`. -/
theorem hc_mem_jetIdealT {n : ℕ} (k : ℕ) {F : TPoly} (hF : F ∈ jetIdealT n) :
    homogeneousComponent k F ∈ jetIdealT n := by
  have h := wc_mem_jetIdealT 1 0 k hF
  have hw : (fun m : ℕ => 1 + 0 * m) = (1 : ℕ → ℕ) := by funext m; simp
  rw [hw] at h
  exact h

/-- The conformal-weight components (`T_m ↦ m + 1`) preserve `J_n`. -/
theorem pw_mem_jetIdealT {n : ℕ} (E : ℕ) {F : TPoly} (hF : F ∈ jetIdealT n) :
    pw E F ∈ jetIdealT n := by
  have h := wc_mem_jetIdealT 1 1 E hF
  have hw : (fun m : ℕ => 1 + 1 * m) = wT := by funext m; simp [wT]; ring
  rw [hw] at h
  exact h

/-! ### Weighted components and partial derivatives -/

theorem weight_sub_single {w : ℕ → ℕ} {s : ℕ →₀ ℕ} {m : ℕ} (hs : 1 ≤ s m) :
    Finsupp.weight w (s - Finsupp.single m 1) + w m = Finsupp.weight w s := by
  have hle : Finsupp.single m 1 ≤ s := by
    intro i
    rw [Finsupp.single_apply]
    split_ifs with h
    · subst h; exact hs
    · exact Nat.zero_le _
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, Finsupp.weight_apply (f := Finsupp.single m 1), Finsupp.sum_single_index (by simp)]
  simp

/-- Weighted components commute with `∂/∂T_m`, up to the weight shift `w m`. -/
theorem wc_pderiv (w : ℕ → ℕ) (m E : ℕ) (F : TPoly) :
    weightedHomogeneousComponent w E (pderiv m F) =
      pderiv m (weightedHomogeneousComponent w (E + w m) F) := by
  classical
  conv_lhs => rw [as_sum F]
  conv_rhs => rw [as_sum F]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pderiv_monomial]
  by_cases hs : s m = 0
  · rw [hs, Nat.cast_zero, mul_zero, monomial_zero, map_zero]
    by_cases hE : Finsupp.weight w s = E + w m
    · rw [(isWeightedHomogeneous_monomial w s (coeff s F) hE).weightedHomogeneousComponent_same,
        pderiv_monomial, hs, Nat.cast_zero, mul_zero, monomial_zero]
    · rw [(isWeightedHomogeneous_monomial w s (coeff s F) rfl).weightedHomogeneousComponent_ne
        (E + w m) (Ne.symm hE), map_zero]
  · have hs1 : 1 ≤ s m := Nat.one_le_iff_ne_zero.mpr hs
    have hw := weight_sub_single (w := w) hs1
    by_cases hE : Finsupp.weight w s = E + w m
    · have hE' : Finsupp.weight w (s - Finsupp.single m 1) = E := by omega
      rw [(isWeightedHomogeneous_monomial w _ _ hE').weightedHomogeneousComponent_same,
        (isWeightedHomogeneous_monomial w s (coeff s F) hE).weightedHomogeneousComponent_same,
        pderiv_monomial]
    · have hE' : Finsupp.weight w (s - Finsupp.single m 1) ≠ E := by omega
      rw [(isWeightedHomogeneous_monomial w _ _ rfl).weightedHomogeneousComponent_ne E
          (Ne.symm hE'),
        (isWeightedHomogeneous_monomial w s (coeff s F) rfl).weightedHomogeneousComponent_ne
          (E + w m) (Ne.symm hE), map_zero]

/-! ### Derivatives of the jets -/

theorem serG_pderiv_tSer (M : ℕ) : serG (pderiv M) tSer = PowerSeries.X ^ M := by
  ext i
  rw [coeff_serG, tSer, PowerSeries.coeff_mk, pderiv_X, PowerSeries.coeff_X_pow, Pi.single_apply]

theorem serG_pow (D : Derivation ℂ TPoly TPoly) (f : PowerSeries TPoly) :
    ∀ n : ℕ, serG D (f ^ (n + 1)) = ((n + 1 : ℕ) : PowerSeries TPoly) * f ^ n * serG D f
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, serG_mul, serG_pow D f n]
    push_cast; ring

/-- `∂/∂T_M (T^{n+1})_i = (n + 1) (Tⁿ)_{i - M}` (zero for `M > i`). -/
theorem pderiv_jg (M n i : ℕ) :
    pderiv M (jg (n + 1) i) = if M ≤ i then ((n + 1 : ℕ) : TPoly) * jg n (i - M) else 0 := by
  have h := congrArg (PowerSeries.coeff i) (serG_pow (pderiv M) tSer n)
  rw [coeff_serG, serG_pderiv_tSer, mul_assoc, ← map_natCast (PowerSeries.C (R := TPoly)),
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow'] at h
  rw [jg, h]
  split_ifs <;> simp

/-! ### The jet shift -/

/-- `Σ_j h_j (Tⁿ)_{j + a}`. -/
def shiftJ (n a : ℕ) (c : ℕ →₀ TPoly) : TPoly := c.sum fun j h => h * jg n (j + a)

theorem shiftJ_mem (n a : ℕ) (c : ℕ →₀ TPoly) : shiftJ n a c ∈ jetIdealT n :=
  Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (jg_mem n (j + a))

theorem shiftJ_zero (n : ℕ) (c : ℕ →₀ TPoly) :
    shiftJ n 0 c = c.sum fun j h => h • jg n j := by
  simp [shiftJ, smul_eq_mul]

/-- **The jet shift.** For `a ≤ M`, `∂/∂T_M` of the shifted element agrees with `∂/∂T_{M-a}` of
the original one modulo `J_{n+1}`. -/
theorem pderiv_shiftJ_sub (n a M : ℕ) (ha : a ≤ M) (c : ℕ →₀ TPoly) :
    pderiv M (shiftJ (n + 1) a c) - pderiv (M - a) (shiftJ (n + 1) 0 c) ∈ jetIdealT (n + 1) := by
  simp only [shiftJ, Finsupp.sum, map_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun j _ => ?_
  have h1 : pderiv M (c j * jg (n + 1) (j + a)) =
      c j * pderiv M (jg (n + 1) (j + a)) + jg (n + 1) (j + a) * pderiv M (c j) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have h2 : pderiv (M - a) (c j * jg (n + 1) (j + 0)) =
      c j * pderiv (M - a) (jg (n + 1) (j + 0)) +
        jg (n + 1) (j + 0) * pderiv (M - a) (c j) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have h3 : pderiv M (jg (n + 1) (j + a)) = pderiv (M - a) (jg (n + 1) (j + 0)) := by
    rw [pderiv_jg, pderiv_jg]
    have hcond : (M ≤ j + a) ↔ (M - a ≤ j + 0) := by omega
    have hidx : j + a - M = j + 0 - (M - a) := by omega
    simp only [hcond, hidx]
  rw [h1, h2, h3]
  have : c j * pderiv (M - a) (jg (n + 1) (j + 0)) + jg (n + 1) (j + a) * pderiv M (c j) -
      (c j * pderiv (M - a) (jg (n + 1) (j + 0)) + jg (n + 1) (j + 0) * pderiv (M - a) (c j)) =
      pderiv M (c j) * jg (n + 1) (j + a) - pderiv (M - a) (c j) * jg (n + 1) (j + 0) := by ring
  rw [this]
  exact sub_mem (Ideal.mul_mem_left _ _ (jg_mem _ _)) (Ideal.mul_mem_left _ _ (jg_mem _ _))

/-! ### The weighted Euler identity -/

theorem X_mul_pderiv_monomial (m : ℕ) (s : ℕ →₀ ℕ) (c : ℂ) :
    MvPolynomial.X m * pderiv m (monomial s c) = ((s m : ℕ) : TPoly) * monomial s c := by
  rw [pderiv_monomial]
  by_cases hs : s m = 0
  · rw [hs]; simp
  · have hle : Finsupp.single m 1 ≤ s := by
      intro i
      rw [Finsupp.single_apply]
      split_ifs with h
      · subst h; exact Nat.one_le_iff_ne_zero.mpr hs
      · exact Nat.zero_le _
    rw [show (MvPolynomial.X m : TPoly) = monomial (Finsupp.single m 1) 1 from rfl, monomial_mul,
      one_mul, add_comm, tsub_add_cancel_of_le hle, ← map_natCast (MvPolynomial.C : ℂ →+* TPoly),
      C_mul_monomial, mul_comm]

/-- **The weighted Euler identity** over any finite set of variables containing `vars F`. -/
theorem euler_sum (w : ℕ → ℕ) (F : TPoly) (S : Finset ℕ) (hS : F.vars ⊆ S) :
    ∑ m ∈ S, ((w m : ℕ) : TPoly) * (MvPolynomial.X m * pderiv m F) =
      ∑ s ∈ F.support, ((Finsupp.weight w s : ℕ) : TPoly) * monomial s (coeff s F) := by
  conv_lhs => rw [as_sum F]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [X_mul_pderiv_monomial, ← mul_assoc, ← Finset.sum_mul]
  congr 1
  have hsub : s.support ⊆ S := fun i hi =>
    hS ((mem_vars_iff_mem_support i).mpr ⟨s, hs, hi⟩)
  rw [Finsupp.weight_apply, Finsupp.sum_of_support_subset s hsub _ (fun i _ => by simp),
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]; push_cast; ring

/-- The weighted Euler identity for a weighted homogeneous polynomial. -/
theorem euler_isWH {w : ℕ → ℕ} {F : TPoly} {d : ℕ} (hF : IsWeightedHomogeneous w F d) :
    ∑ m ∈ F.vars, ((w m : ℕ) : TPoly) * (MvPolynomial.X m * pderiv m F) =
      ((d : ℕ) : TPoly) * F := by
  rw [euler_sum w F F.vars subset_rfl]
  conv_rhs => rw [as_sum F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hF (mem_support_iff.mp hs)]

/-! ### `T`-monomial spans and homogeneity -/

theorem isWH_listProd_aff (a b : ℕ) : ∀ l : List ℕ,
    IsWeightedHomogeneous (fun m => a + b * m) ((l.map MvPolynomial.X).prod : TPoly)
      (l.length * a + b * l.sum)
  | [] => by simpa using isWeightedHomogeneous_one (R := ℂ) (fun m : ℕ => a + b * m)
  | x :: l => by
    rw [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons]
    have := (isWeightedHomogeneous_X ℂ (fun m => a + b * m) x).mul (isWH_listProd_aff a b l)
    convert this using 1
    ring

theorem sum_map_succ (l : List ℕ) : (l.map fun m => m + 1).sum = l.sum + l.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- `T`-monomials of degree `k` and weight `E` are weighted homogeneous for `m ↦ a + b m`. -/
theorem tMonW_isWH (a b : ℕ) {k E : ℕ} {F : TPoly} (hF : F ∈ tMonW TPoly MvPolynomial.X k (E : ℤ)) :
    IsWeightedHomogeneous (fun m => a + b * m) F (k * a + b * (E - k)) := by
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, he, rfl⟩ := hP
    have h := isWH_listProd_aff a b l
    have he' : (l.map fun m => m + 1).sum = E := by exact_mod_cast he
    rw [sum_map_succ] at he'
    have : k * a + b * (E - k) = l.length * a + b * l.sum := by
      rw [hl]; congr 2; omega
    rw [this]; exact h
  | zero => exact isWeightedHomogeneous_zero ℂ _ _
  | add P Q _ _ hP hQ => exact hP.add hQ
  | smul c P _ hP => exact (weightedHomogeneousSubmodule ℂ _ _).smul_mem c hP

theorem homogeneous_of_tMonW {k E : ℕ} {F : TPoly}
    (hF : F ∈ tMonW TPoly MvPolynomial.X k (E : ℤ)) : F.IsHomogeneous k := by
  have h := tMonW_isWH 1 0 hF
  have hw : (fun m : ℕ => 1 + 0 * m) = (1 : ℕ → ℕ) := by funext m; simp
  rw [hw] at h
  simpa using h

/-! ### Monomials as list products -/

theorem prod_map_X_toMultiset (s : ℕ →₀ ℕ) :
    ((Finsupp.toMultiset s).map (MvPolynomial.X : ℕ → TPoly)).prod = monomial s 1 := by
  induction s using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, ih, Finsupp.toMultiset_single,
      Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton, Multiset.prod_singleton,
      X_pow_eq_monomial, monomial_mul, one_mul]

theorem sum_map_toMultiset (g : ℕ → ℕ) (s : ℕ →₀ ℕ) :
    ((Finsupp.toMultiset s).map g).sum = Finsupp.weight g s := by
  induction s using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.sum_add, ih, Finsupp.toMultiset_single,
      Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton,
      map_add]
    congr 1
    rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]

/-- A monomial of degree `k` and weight `E` lies in `tMonW`. -/
theorem monomial_mem_tMonW {k E : ℕ} (s : ℕ →₀ ℕ) (c : ℂ) (hk : Finsupp.degree s = k)
    (hE : Finsupp.weight wT s = E) :
    monomial s c ∈ tMonW TPoly MvPolynomial.X k (E : ℤ) := by
  have h1 : monomial s c = c • monomial s (1 : ℂ) := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h1]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(Finsupp.toMultiset s).toList, ?_, ?_, ?_⟩)
  · have h := sum_map_toMultiset (fun _ => 1) s
    rw [← Finsupp.degree_eq_weight_one, hk, Multiset.map_const', Multiset.sum_replicate,
      smul_eq_mul, mul_one] at h
    rw [Multiset.length_toList, h]
  · have h := sum_map_toMultiset wT s
    rw [hE] at h
    rw [← h]
    conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset s)]
    rw [Multiset.map_coe, Multiset.sum_coe]
  · rw [← prod_map_X_toMultiset]
    conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset s)]
    rw [Multiset.map_coe, Multiset.prod_coe]

/-- A polynomial homogeneous of degree `k` and weight `E` lies in `tMonW`: the projection of
any polynomial to `T`-degree `k` and weight `E` does. -/
theorem proj_mem_tMonW (k E : ℕ) (G : TPoly) :
    pw E (homogeneousComponent k G) ∈ tMonW TPoly MvPolynomial.X k (E : ℤ) := by
  classical
  rw [as_sum (pw E (homogeneousComponent k G))]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hc := mem_support_iff.mp hs
  rw [coeff_weightedHomogeneousComponent] at hc
  split_ifs at hc with hE
  · rw [coeff_homogeneousComponent] at hc
    split_ifs at hc with hk
    · exact monomial_mem_tMonW s _ hk hE
    · exact absurd rfl hc
  · exact absurd rfl hc

theorem mem_tMonW_of_isWH {k E : ℕ} {F : TPoly} (hk : F.IsHomogeneous k)
    (hE : IsWeightedHomogeneous wT F E) : F ∈ tMonW TPoly MvPolynomial.X k (E : ℤ) := by
  have h1 : homogeneousComponent k F = F := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hk), if_pos rfl]
  have h2 : pw E F = F := hE.weightedHomogeneousComponent_same
  have := proj_mem_tMonW k E F
  rwa [h1, h2] at this

/-- A `T`-polynomial in `T_0, …, T_{N-1}` maps into the box of `R_n`. -/
theorem mk_mem_boxW_of_vars {n N k E : ℕ} {F : TPoly}
    (hF : F ∈ tMonW TPoly MvPolynomial.X k (E : ℤ)) (hv : ∀ m ∈ F.vars, m < N) :
    Ideal.Quotient.mk (jetIdealT n) F ∈ boxW (tn n) N k (E : ℤ) := by
  have h := cut_tMonW_le_boxW N k (E : ℤ) (Submodule.mem_map.mpr ⟨F, hF, rfl⟩)
  rw [AlgHom.toLinearMap_apply, cut_eq_self hv] at h
  have := boxW_map n N k (E : ℤ) (Submodule.mem_map.mpr ⟨F, h, rfl⟩)
  rwa [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] at this

theorem mem_of_natCast_mul_mem {n d : ℕ} (hd : d ≠ 0) {F : TPoly}
    (h : ((d : ℕ) : TPoly) * F ∈ jetIdealT n) : F ∈ jetIdealT n := by
  have hc : ((d : ℕ) : TPoly) = MvPolynomial.C ((d : ℕ) : ℂ) := by simp
  rw [hc] at h
  have h2 := Ideal.mul_mem_left (jetIdealT n) (MvPolynomial.C ((d : ℂ)⁻¹)) h
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hd), map_one, one_mul] at h2

/-! ### The jet-ideal Poincaré lemma -/

/-- **The jet-ideal Poincaré lemma** in the slot `(N, k, E)`: a `T`-polynomial of degree `k` and
weight `E` all of whose derivatives `∂/∂T_M` with `M ≥ N` lie in the jet ideal `J_n` is, modulo
`J_n`, a polynomial in `T_0, …, T_{N-1}` (it lands in the box of `R_n`). -/
def JetPoincare (n N k E : ℕ) : Prop :=
  ∀ F ∈ tMonW TPoly MvPolynomial.X k (E : ℤ), (∀ M, N ≤ M → pderiv M F ∈ jetIdealT n) →
    Ideal.Quotient.mk (jetIdealT n) F ∈ boxW (tn n) N k (E : ℤ)

/-- **`N = 0`**: the Euler identity. -/
theorem jetPoincare_zero (n k E : ℕ) : JetPoincare n 0 k E := by
  intro F hF hder
  have hwh := tMonW_isWH 1 0 hF
  have hmem : ∑ m ∈ F.vars, (((1 + 0 * m : ℕ)) : TPoly) * (MvPolynomial.X m * pderiv m F) ∈
      jetIdealT n :=
    Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hder m (by omega)))
  rw [euler_isWH hwh] at hmem
  by_cases hk : k * 1 + 0 * (E - k) = 0
  · refine mk_mem_boxW_of_vars hF fun m hm => ?_
    exfalso
    obtain ⟨s, hs, hms⟩ := (mem_vars_iff_mem_support m).mp hm
    have hw := hwh (mem_support_iff.mp hs)
    rw [hk, Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at hw
    have := hw m hms
    rw [smul_eq_mul, show 1 + 0 * m = 1 by ring, mul_one] at this
    exact Finsupp.mem_support_iff.mp hms this
  · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (mem_of_natCast_mul_mem hk hmem)]
    exact Submodule.zero_mem _

/-- **`N = 1`**: the Euler identity for the index sum `T_m ↦ m`, for which `J_n` is homogeneous
(`(Tⁿ)_j` has index sum `j`); the term `m = 0` drops out. -/
theorem jetPoincare_one (n k E : ℕ) : JetPoincare n 1 k E := by
  intro F hF hder
  have hwh := tMonW_isWH 0 1 hF
  have hmem : ∑ m ∈ F.vars, (((0 + 1 * m : ℕ)) : TPoly) * (MvPolynomial.X m * pderiv m F) ∈
      jetIdealT n := by
    refine Ideal.sum_mem _ fun m _ => ?_
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hder m h))
  rw [euler_isWH hwh] at hmem
  by_cases hk : k * 0 + 1 * (E - k) = 0
  · refine mk_mem_boxW_of_vars hF fun m hm => ?_
    obtain ⟨s, hs, hms⟩ := (mem_vars_iff_mem_support m).mp hm
    have hw := hwh (mem_support_iff.mp hs)
    rw [hk, Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at hw
    have := hw m hms
    simp only [smul_eq_mul, zero_add, one_mul, mul_eq_zero] at this
    rcases this with h | h
    · exact absurd h (Finsupp.mem_support_iff.mp hms)
    · omega
  · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (mem_of_natCast_mul_mem hk hmem)]
    exact Submodule.zero_mem _

end HighJet

end

end VOA.TwoSeries.StrictModel
