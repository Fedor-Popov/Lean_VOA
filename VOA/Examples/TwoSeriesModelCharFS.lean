/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharBlocks

/-!
# Feigin–Stoyanovsky functionals on `R_n = ℂ[T_j]/(jets of Tⁿ)`

For a symmetric polynomial `F(x_1, …, x_s)` define the functional `ψ_F` on `ℂ[T_j]` by

  `ψ_F (T_{j_1} ⋯ T_{j_s}) = [x^j] F`,   `ψ_F = 0` on monomials of degree `≠ s`,

so that `Σ_j ψ_F(T_{j_1} ⋯ T_{j_s}) x^j = F` is the generating function of `ψ_F` on the product
`T(x_1) ⋯ T(x_s)` (`ψF_prod_X`).

* `exists_perm_of_monoOf_eq` — two exponent vectors with the same monomial differ by a
  permutation (fibre-wise bijections);
* `ψF_jet_eq_zero` — **if `F` is divisible by `x_1 - x_2`, then `ψ_F` kills the jet ideal of
  `T²`**, hence of `Tⁿ` for every `n ≥ 2` (`jetIdealT_le_two`), and descends to
  `ψbar : R_n → ℂ` (`ψbar_mk`);
* `lowDeg k p` — every monomial of `p` has `T`-degree `≥ k`; `ψF_eq_zero_of_lowDeg` and
  `Φ_ψF_eq_zero` — `ψ_F` (applied coefficientwise) kills `T`-degree `≥ s + 1`.
* `vdm s = Π_{i ≠ j} (x_i - x_j)` — symmetric, divisible by `x_0 - x_1`, nonzero, homogeneous of
  degree `s(s-1)`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.SymbolModel VOA.TwoSeries.StrictModel VOA.JetProduct
open scoped BigOperators

noncomputable section

/-! ### Monomials of exponent vectors -/

/-- The exponent of `T_{j_1} ⋯ T_{j_s}`. -/
def monoOf {s : ℕ} (j : Fin s → ℕ) : ℕ →₀ ℕ := ∑ i, Finsupp.single (j i) 1

theorem monoOf_apply {s : ℕ} (j : Fin s → ℕ) (v : ℕ) :
    monoOf j v = (Finset.univ.filter fun i => j i = v).card := by
  rw [monoOf, Finsupp.finsetSum_apply, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finsupp.single_apply]

theorem degree_monoOf {s : ℕ} (j : Fin s → ℕ) : (monoOf j).degree = s := by
  simp [monoOf, map_sum]

theorem monoOf_cons {s : ℕ} (a : ℕ) (j : Fin s → ℕ) :
    monoOf (Fin.cons a j : Fin (s + 1) → ℕ) = Finsupp.single a 1 + monoOf j := by
  simp [monoOf, Fin.sum_univ_succ]

theorem prod_X_eq_monomial {s : ℕ} (j : Fin s → ℕ) :
    (∏ i, X (j i) : TPoly) = monomial (monoOf j) 1 := by
  rw [monoOf, monomial_sum_one]
  rfl

/-- Every exponent of degree `d` is the monomial of an exponent vector of length `d`. -/
theorem exists_monoOf : ∀ (d : ℕ) (e : ℕ →₀ ℕ), e.degree = d → ∃ j : Fin d → ℕ, monoOf j = e
  | 0, e, he => ⟨Fin.elim0, by
      rw [(Finsupp.degree_eq_zero_iff e).mp he]; simp [monoOf]⟩
  | d + 1, e, he => by
    have hne : e ≠ 0 := by rintro rfl; simp at he
    obtain ⟨k, hk⟩ : ∃ k, e k ≠ 0 := by
      by_contra h; push Not at h; exact hne (Finsupp.ext h)
    have hle : Finsupp.single k 1 ≤ e := by
      intro i
      rw [Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · exact Nat.zero_le _
    have hsplit : e = Finsupp.single k 1 + (e - Finsupp.single k 1) :=
      (add_tsub_cancel_of_le hle).symm
    have hdeg : (e - Finsupp.single k 1).degree = d := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single] at this
      omega
    obtain ⟨j, hj⟩ := exists_monoOf d _ hdeg
    exact ⟨Fin.cons k j, by rw [monoOf_cons, hj, ← hsplit]⟩

/-- Two exponent vectors with the same monomial differ by a permutation. -/
theorem exists_perm_of_monoOf_eq {s : ℕ} {j j' : Fin s → ℕ} (h : monoOf j = monoOf j') :
    ∃ σ : Equiv.Perm (Fin s), ∀ i, j' i = j (σ i) := by
  classical
  have hc : ∀ v, Fintype.card {i // j' i = v} = Fintype.card {i // j i = v} := by
    intro v
    have := congrArg (· v) h
    simp only [monoOf_apply] at this
    rw [Fintype.card_subtype, Fintype.card_subtype, this]
  let e : ∀ v, {i // j' i = v} ≃ {i // j i = v} := fun v => Fintype.equivOfCardEq (hc v)
  refine ⟨(Equiv.sigmaFiberEquiv j').symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv j)), fun i => ?_⟩
  simp only [Equiv.trans_apply, Equiv.sigmaFiberEquiv, Equiv.coe_fn_symm_mk,
    Equiv.sigmaCongrRight_apply, Equiv.coe_fn_mk]
  exact ((e (j' i)) ⟨i, rfl⟩).2.symm

/-! ### The functional `ψ_F` -/

variable {s : ℕ}

open Classical in
/-- The value of `ψ_F` on a monomial. -/
def cF (F : MvPolynomial (Fin s) ℂ) (e : ℕ →₀ ℕ) : ℂ :=
  if h : ∃ j : Fin s → ℕ, monoOf j = e then coeff (toF h.choose) F else 0

/-- Symmetry of a polynomial. -/
def Symm (F : MvPolynomial (Fin s) ℂ) : Prop := ∀ σ : Equiv.Perm (Fin s), rename σ F = F

theorem coeff_toF_perm {F : MvPolynomial (Fin s) ℂ} (hF : Symm F) (j : Fin s → ℕ)
    (σ : Equiv.Perm (Fin s)) : coeff (toF (fun i => j (σ i))) F = coeff (toF j) F := by
  have h := coeff_rename_mapDomain σ σ.injective F (toF (fun i => j (σ i)))
  rw [hF σ] at h
  rw [← h]
  congr 1
  ext k
  rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply]
  simp

theorem cF_monoOf {F : MvPolynomial (Fin s) ℂ} (hF : Symm F) (j : Fin s → ℕ) :
    cF F (monoOf j) = coeff (toF j) F := by
  have h : ∃ j' : Fin s → ℕ, monoOf j' = monoOf j := ⟨j, rfl⟩
  rw [cF, dif_pos h]
  obtain ⟨σ, hσ⟩ := exists_perm_of_monoOf_eq h.choose_spec
  have h2 := coeff_toF_perm hF h.choose σ
  rw [← h2, show (fun i => h.choose (σ i)) = j from funext fun i => (hσ i).symm]

theorem cF_eq_zero {F : MvPolynomial (Fin s) ℂ} {e : ℕ →₀ ℕ} (he : e.degree ≠ s) :
    cF F e = 0 := by
  rw [cF, dif_neg]
  rintro ⟨j, rfl⟩
  exact he (degree_monoOf j)

/-- The Feigin–Stoyanovsky functional `ψ_F` on `ℂ[T_j]`. -/
def ψF (F : MvPolynomial (Fin s) ℂ) : TPoly →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ (cF F)

theorem ψF_monomial (F : MvPolynomial (Fin s) ℂ) (e : ℕ →₀ ℕ) (a : ℂ) :
    ψF F (monomial e a) = a * cF F e := by
  rw [ψF, ← single_eq_monomial]
  erw [Finsupp.linearCombination_single]
  rw [smul_eq_mul]

theorem ψF_apply (F : MvPolynomial (Fin s) ℂ) (p : TPoly) :
    ψF F p = ∑ e ∈ p.support, coeff e p * cF F e := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun e _ => ψF_monomial F e _

/-- The generating function: `ψ_F (T_{j_1} ⋯ T_{j_s}) = [x^j] F`. -/
theorem ψF_prod_X {F : MvPolynomial (Fin s) ℂ} (hF : Symm F) (j : Fin s → ℕ) :
    ψF F (∏ i, X (j i)) = coeff (toF j) F := by
  rw [prod_X_eq_monomial, ψF_monomial, one_mul, cF_monoOf hF]

/-! ### Lower bounds on the `T`-degree -/

/-- Every monomial of `p` has degree `≥ k`. -/
def lowDeg (k : ℕ) (p : TPoly) : Prop := ∀ e ∈ p.support, k ≤ e.degree

theorem lowDeg_zero_left (p : TPoly) : lowDeg 0 p := fun _ _ => Nat.zero_le _

theorem lowDeg_zero (k : ℕ) : lowDeg k 0 := by simp [lowDeg]

theorem lowDeg_add {k : ℕ} {p q : TPoly} (hp : lowDeg k p) (hq : lowDeg k q) :
    lowDeg k (p + q) := fun e he => by
  rcases Finset.mem_union.mp (support_add he) with h | h
  exacts [hp e h, hq e h]

theorem lowDeg_neg {k : ℕ} {p : TPoly} (hp : lowDeg k p) : lowDeg k (-p) := by
  intro e he; rw [support_neg] at he; exact hp e he

theorem lowDeg_sub {k : ℕ} {p q : TPoly} (hp : lowDeg k p) (hq : lowDeg k q) :
    lowDeg k (p - q) := by
  rw [sub_eq_add_neg]; exact lowDeg_add hp (lowDeg_neg hq)

theorem lowDeg_smul {k : ℕ} {p : TPoly} (c : ℂ) (hp : lowDeg k p) : lowDeg k (c • p) :=
  fun e he => hp e (support_smul he)

theorem lowDeg_sum {k : ℕ} {ι : Type*} (S : Finset ι) (f : ι → TPoly)
    (h : ∀ i ∈ S, lowDeg k (f i)) : lowDeg k (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [lowDeg_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact lowDeg_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lowDeg_mul {a b : ℕ} {p q : TPoly} (hp : lowDeg a p) (hq : lowDeg b q) :
    lowDeg (a + b) (p * q) := by
  classical
  intro e he
  obtain ⟨e1, h1, e2, h2, rfl⟩ := Finset.mem_add.mp (support_mul p q he)
  rw [map_add]
  exact Nat.add_le_add (hp e1 h1) (hq e2 h2)

theorem lowDeg_mono {k k' : ℕ} (h : k ≤ k') {p : TPoly} (hp : lowDeg k' p) : lowDeg k p :=
  fun e he => h.trans (hp e he)

theorem lowDeg_X (j : ℕ) : lowDeg 1 (X j : TPoly) := by
  intro e he
  rw [support_X, Finset.mem_singleton] at he
  subst he
  simp

theorem lowDeg_one : lowDeg 0 (1 : TPoly) := lowDeg_zero_left _

/-- `ψ_F` kills `T`-degree `≥ s + 1`. -/
theorem ψF_eq_zero_of_lowDeg (F : MvPolynomial (Fin s) ℂ) {p : TPoly} (hp : lowDeg (s + 1) p) :
    ψF F p = 0 := by
  rw [ψF_apply]
  refine Finset.sum_eq_zero fun e he => ?_
  rw [cF_eq_zero (by have := hp e he; omega), mul_zero]

/-! ### Lower bounds on the `T`-degree of the coefficients -/

/-- Every coefficient (in `u_j, v_j`) has `T`-degree `≥ k`. -/
def LowM (k : ℕ) (Q : MPoly TPoly) : Prop := ∀ m, lowDeg k (coeff m Q)

theorem LowM.add {k : ℕ} {P Q : MPoly TPoly} (hP : LowM k P) (hQ : LowM k Q) : LowM k (P + Q) :=
  fun m => by rw [coeff_add]; exact lowDeg_add (hP m) (hQ m)

theorem LowM.sub {k : ℕ} {P Q : MPoly TPoly} (hP : LowM k P) (hQ : LowM k Q) : LowM k (P - Q) :=
  fun m => by rw [coeff_sub]; exact lowDeg_sub (hP m) (hQ m)

theorem LowM.smul {k : ℕ} {P : MPoly TPoly} (c : ℂ) (hP : LowM k P) : LowM k (c • P) :=
  fun m => by rw [coeff_smul]; exact lowDeg_smul c (hP m)

theorem LowM.zero (k : ℕ) : LowM k (0 : MPoly TPoly) := fun m => by
  rw [coeff_zero]; exact lowDeg_zero k

theorem LowM.sum {k : ℕ} {ι : Type*} (S : Finset ι) (f : ι → MPoly TPoly)
    (h : ∀ i ∈ S, LowM k (f i)) : LowM k (∑ i ∈ S, f i) := fun m => by
  rw [coeff_sum]; exact lowDeg_sum S _ fun i hi => h i hi m

theorem LowM.mul {a b : ℕ} {P Q : MPoly TPoly} (hP : LowM a P) (hQ : LowM b Q) :
    LowM (a + b) (P * Q) := by
  classical
  intro m
  rw [coeff_mul]
  exact lowDeg_sum _ _ fun p _ => lowDeg_mul (hP p.1) (hQ p.2)

theorem LowM.mono {k k' : ℕ} (h : k ≤ k') {P : MPoly TPoly} (hP : LowM k' P) : LowM k P :=
  fun m => lowDeg_mono h (hP m)

theorem LowM.C {k : ℕ} {p : TPoly} (hp : lowDeg k p) : LowM k (MvPolynomial.C p) := by
  intro m
  rw [coeff_C]
  split_ifs
  · exact hp
  · exact lowDeg_zero k

theorem LowM.C_mul_ι {k : ℕ} {p : TPoly} (hp : lowDeg k p) (P : JetPoly) :
    LowM k (MvPolynomial.C p * ι TPoly P) := by
  have h := LowM.mul (LowM.C hp) (fun m => lowDeg_zero_left (coeff m (ι TPoly P)))
  simpa using h

theorem LowM.ι (P : JetPoly) : LowM 0 (ι TPoly P) := fun _ => lowDeg_zero_left _

/-- `ψ_F`, applied coefficientwise, kills `T`-degree `≥ s + 1`. -/
theorem Φ_ψF_eq_zero (F : MvPolynomial (Fin s) ℂ) {Q : MPoly TPoly} (hQ : LowM (s + 1) Q) :
    VOA.TwoSeries.StrictModel.Φ TPoly (ψF F) Q = 0 := by
  ext m
  rw [VOA.TwoSeries.StrictModel.coeff_Φ, coeff_zero]
  exact ψF_eq_zero_of_lowDeg F (hQ m)

/-! ### The jet ideal -/

theorem coeff_tSer_sq (m : ℕ) :
    PowerSeries.coeff m (tSer ^ 2) = ∑ p ∈ Finset.antidiagonal m, X p.1 * X p.2 := by
  rw [pow_two, PowerSeries.coeff_mul]
  simp [tSer]

/-- The jet ideal of `Tⁿ` lies in that of `T²` for `n ≥ 2`. -/
theorem jetIdealT_le_two {n : ℕ} (hn : 2 ≤ n) : jetIdealT n ≤ jetIdealT 2 := by
  rw [jetIdealT, Ideal.span_le]
  rintro _ ⟨m, rfl⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
  rw [SetLike.mem_coe]
  dsimp only
  rw [pow_add, PowerSeries.coeff_mul]
  refine Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨p.1, rfl⟩)

theorem toF_cons_cons_sub (a b : ℕ) {s' : ℕ} (j : Fin s' → ℕ) :
    toF (Fin.cons (a + 1) (Fin.cons b j : Fin (s' + 1) → ℕ) : Fin (s' + 2) → ℕ) -
        Finsupp.single 0 1 = toF (Fin.cons a (Fin.cons b j : Fin (s' + 1) → ℕ)) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem toF_cons_cons_sub' (a b : ℕ) {s' : ℕ} (j : Fin s' → ℕ) :
    toF (Fin.cons a (Fin.cons (b + 1) j : Fin (s' + 1) → ℕ) : Fin (s' + 2) → ℕ) -
        Finsupp.single 1 1 = toF (Fin.cons a (Fin.cons b j : Fin (s' + 1) → ℕ)) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · simp only [Finsupp.coe_tsub, Pi.sub_apply, toF_apply, Fin.cons_succ, Finsupp.single_apply]
      rw [if_neg (by intro h; exact absurd (congrArg Fin.val h) (by simp))]
      simp

/-- The coefficient of `x_0 · G` and `x_1 · G` at a cons-exponent. -/
theorem coeff_X0_mul (G : MvPolynomial (Fin (s + 2)) ℂ) (a b : ℕ) (j : Fin s → ℕ) :
    coeff (toF (Fin.cons a (Fin.cons b j : Fin (s + 1) → ℕ) : Fin (s + 2) → ℕ)) (X 0 * G) =
      if 1 ≤ a then coeff (toF (Fin.cons (a - 1) (Fin.cons b j : Fin (s + 1) → ℕ))) G
      else 0 := by
  classical
  rw [coeff_X_mul']
  split_ifs with h1 h2 h2
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [toF_cons_cons_sub, Nat.add_sub_cancel]
  · exfalso; apply h2
    have : (toF (Fin.cons a (Fin.cons b j : Fin (s + 1) → ℕ) : Fin (s + 2) → ℕ)) 0 ≠ 0 :=
      Finsupp.mem_support_iff.mp h1
    simp at this; omega
  · exfalso; apply h1
    rw [Finsupp.mem_support_iff]; simp; omega
  · rfl

theorem coeff_X1_mul (G : MvPolynomial (Fin (s + 2)) ℂ) (a b : ℕ) (j : Fin s → ℕ) :
    coeff (toF (Fin.cons a (Fin.cons b j : Fin (s + 1) → ℕ) : Fin (s + 2) → ℕ)) (X 1 * G) =
      if 1 ≤ b then coeff (toF (Fin.cons a (Fin.cons (b - 1) j : Fin (s + 1) → ℕ))) G
      else 0 := by
  classical
  rw [coeff_X_mul']
  have hv : (toF (Fin.cons a (Fin.cons b j : Fin (s + 1) → ℕ) : Fin (s + 2) → ℕ)) 1 = b := by
    simp
  split_ifs with h1 h2 h2
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [toF_cons_cons_sub', Nat.add_sub_cancel]
  · exfalso; apply h2
    have := Finsupp.mem_support_iff.mp h1
    rw [hv] at this; omega
  · exfalso; apply h1
    rw [Finsupp.mem_support_iff, hv]; omega
  · rfl

/-- The telescoping core of the kernel property. -/
theorem sum_antidiagonal_X01 (G : MvPolynomial (Fin (s + 2)) ℂ) (m : ℕ) (j : Fin s → ℕ) :
    ∑ p ∈ Finset.antidiagonal m,
      coeff (toF (Fin.cons p.1 (Fin.cons p.2 j : Fin (s + 1) → ℕ) : Fin (s + 2) → ℕ))
        ((X 0 - X 1) * G) = 0 := by
  simp only [sub_mul, coeff_sub, Finset.sum_sub_distrib, coeff_X0_mul, coeff_X1_mul]
  cases m with
  | zero => simp
  | succ m =>
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
    simp

/-- Divisibility by `x_0 - x_1` (for `s ≥ 2`). -/
def DivX01 (F : MvPolynomial (Fin s) ℂ) : Prop :=
  ∀ h : 2 ≤ s, ∃ G : MvPolynomial (Fin s) ℂ,
    F = (X ⟨0, by omega⟩ - X ⟨1, by omega⟩) * G

/-- **The kernel property**: if `F` is symmetric and divisible by `x_0 - x_1`, then `ψ_F`
kills `coeff_m(T(z)²) · p` for every `p`. -/
theorem ψF_jet_mul_eq_zero {F : MvPolynomial (Fin s) ℂ} (hF : Symm F)
    (hdiv : DivX01 F) (m : ℕ) (p : TPoly) :
    ψF F (PowerSeries.coeff m (tSer ^ 2) * p) = 0 := by
  classical
  by_cases hs : s < 2
  · apply ψF_eq_zero_of_lowDeg
    refine lowDeg_mono (by omega : s + 1 ≤ 2 + 0) (lowDeg_mul ?_ (lowDeg_zero_left p))
    rw [coeff_tSer_sq]
    exact lowDeg_sum _ _ fun q _ => lowDeg_mul (lowDeg_X q.1) (lowDeg_X q.2)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
  obtain ⟨G, hG'⟩ := hdiv (by omega)
  simp only [Fin.zero_eta, Fin.mk_one] at hG'
  conv_lhs => rw [p.as_sum]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [coeff_tSer_sq, Finset.sum_mul, map_sum]
  by_cases he : e.degree = s'
  · obtain ⟨j, rfl⟩ := exists_monoOf s' e he
    have hterm : ∀ q ∈ Finset.antidiagonal m,
        ψF F (X q.1 * X q.2 * monomial (monoOf j) (coeff (monoOf j) p)) =
          coeff (monoOf j) p * coeff (toF (Fin.cons q.1 (Fin.cons q.2 j : Fin (s' + 1) → ℕ) :
            Fin (s' + 2) → ℕ)) F := by
      intro q _
      have hm : X q.1 * X q.2 * monomial (monoOf j) (coeff (monoOf j) p) =
          monomial (monoOf (Fin.cons q.1 (Fin.cons q.2 j : Fin (s' + 1) → ℕ) :
            Fin (s' + 2) → ℕ)) (coeff (monoOf j) p) := by
        rw [monoOf_cons, monoOf_cons, X, X, monomial_mul, monomial_mul, one_mul, one_mul,
          add_assoc]
      rw [hm, ψF_monomial, cF_monoOf hF]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hG', sum_antidiagonal_X01, mul_zero]
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [X, X, monomial_mul, monomial_mul, ψF_monomial, cF_eq_zero, mul_zero]
    rw [map_add, map_add, Finsupp.degree_single, Finsupp.degree_single]
    omega

/-- `ψ_F` kills the jet ideal of `T²`. -/
theorem ψF_jetIdeal_two {F : MvPolynomial (Fin s) ℂ} (hF : Symm F)
    (hdiv : DivX01 F) {x : TPoly} (hx : x ∈ jetIdealT 2) :
    ψF F x = 0 := by
  have key : ∀ y, ψF F (y * x) = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨m, rfl⟩ y
      rw [mul_comm]
      exact ψF_jet_mul_eq_zero hF hdiv m y
    · intro y; rw [mul_zero, map_zero]
    · intro a b _ _ ha hb y; rw [mul_add, map_add, ha, hb, add_zero]
    · intro a b _ hb y; rw [smul_eq_mul, ← mul_assoc]; exact hb _
  simpa using key 1

/-- The descended functional `ψbar : R_n → ℂ` (`n ≥ 2`). -/
def ψbar {n : ℕ} (hn : 2 ≤ n) (F : MvPolynomial (Fin s) ℂ) (hF : Symm F)
    (hdiv : DivX01 F) : Rn n →ₗ[ℂ] ℂ :=
  (Submodule.liftQ ((jetIdealT n).restrictScalars ℂ) (ψF F) (fun _ hx =>
    LinearMap.mem_ker.mpr (ψF_jetIdeal_two hF hdiv (jetIdealT_le_two hn hx)))) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℂ (jetIdealT n)).symm.toLinearMap

theorem ψbar_mk {n : ℕ} (hn : 2 ≤ n) (F : MvPolynomial (Fin s) ℂ) (hF : Symm F)
    (hdiv : DivX01 F) (p : TPoly) :
    ψbar hn F hF hdiv (Ideal.Quotient.mk (jetIdealT n) p) = ψF F p :=
  rfl

end

end VOA.TwoSeries.ModelChar
