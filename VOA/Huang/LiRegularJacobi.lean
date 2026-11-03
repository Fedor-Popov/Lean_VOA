import VOA.Huang.LiRegularD

/-! # `(D_{P(z)}, Y^R)` is a weak module (Li, Theorem 3.17)

For an opposite mode system `Bs` on `M` and `z ≠ 0`, the regularized action `Y^R` on the
space `D = D_{P(z)}` of `P(z)`-linear functionals satisfies the Jacobi identity
(`yRres_jacobi`, with arbitrary Laurent-polynomial test functions), the vacuum property
and lower truncation, so `(D, Y^R)` is a genuine `WeakModule` (`weakModuleR`).

The proof replaces Li's formal-series argument by a Chinese-remainder decomposition of the
test functions: every Laurent polynomial is `φ₁ + φ₂` with `φ₁` divisible by `(x − z)^K`
and `φ₂ ∈ x^P ℂ[x]`.  On the `φ₂` parts both sides of the Jacobi identity vanish by lower
truncation (with bounds that are uniform over the finitely many relevant inner
functionals); on the `φ₁ ⊗ ψ₁` part `Y^R = Y*` termwise (Li, Lemma 3.9 and the uniform
pole bound of Proposition 3.6), and the Jacobi identity is that of `Y*`, which comes from
the opposite Jacobi identity of the base (`OppBase.ys_jacobi_apply`).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.Huang.LiConverse LaurentPolynomial
open scoped BigOperators Polynomial

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Divided derivatives lower the `x`-adic order by at most `i`. -/
theorem dd_shift (i : ℕ) (e : ℤ) (p : ℂ[X]) :
    ∃ p' : ℂ[X], dd i (T e * Polynomial.toLaurent p) = T (e - i) * Polynomial.toLaurent p' := by
  rw [dd_mul]
  have hterm : ∀ s ∈ Finset.range (i + 1), ∃ r : ℂ[X],
      dd s (T e) * dd ((i : ℤ) - s) (Polynomial.toLaurent p)
        = T (e - i) * Polynomial.toLaurent r := by
    intro s hs
    rw [Finset.mem_range] at hs
    have hsi : s ≤ i := by omega
    rw [show (i : ℤ) - (s : ℤ) = ((i - s : ℕ) : ℤ) by omega, dd_toLaurent, dd_T]
    refine ⟨Polynomial.C (cbz e s) * Polynomial.X ^ (i - s) * Polynomial.hasseDeriv (i - s) p, ?_⟩
    have e1 : (T (e - s) : ℂ[T;T⁻¹]) = T (e - i) * T ((i - s : ℕ) : ℤ) := by
      rw [← T_add]; congr 1; push_cast [Nat.cast_sub hsi]; ring
    rw [e1]
    simp only [map_mul, Polynomial.toLaurent_C, toLaurent_X_pow']
    ring
  choose r hr using hterm
  refine ⟨∑ s ∈ (Finset.range (i + 1)).attach, r s.1 s.2, ?_⟩
  rw [← Finset.sum_attach]
  simp only [Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => hr s.1 s.2

namespace OppBase

variable {W : VertexOperatorAlgebra V} {M : Type v} [AddCommGroup M] [Module ℂ M]
variable {Bs : OppBase W M} {z : ℂ}

/-! ## Elementary properties of `Y^R` on test functions -/

theorem yR_zero_right (hz : z ≠ 0) (a : V) (n : ℤ) : Bs.yR z hz a n 0 = 0 := by
  rw [yR_eq_common hz (wit_zero (Bs := Bs) (z := z) a 0 0) n, map_zero]

theorem yRres_zero_right (hz : z ≠ 0) (a : V) (φ : ℂ[T;T⁻¹]) : Bs.yRres z hz a φ 0 = 0 := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [yRres_add, hp, hq, add_zero]
  | C_mul_T n c => rw [yRres_CT, yR_zero_right, smul_zero]

theorem yRres_add_right (hz : z ≠ 0) {α β : Module.Dual ℂ M} (hα : Bs.InD z α)
    (hβ : Bs.InD z β) (a : V) (φ : ℂ[T;T⁻¹]) :
    Bs.yRres z hz a φ (α + β) = Bs.yRres z hz a φ α + Bs.yRres z hz a φ β := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [yRres_add, yRres_add, yRres_add, hp, hq]; abel
  | C_mul_T n c => rw [yRres_CT, yRres_CT, yRres_CT, yR_add hz hα hβ, smul_add]

theorem yRres_smul_right (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (c : ℂ) (a : V)
    (φ : ℂ[T;T⁻¹]) : Bs.yRres z hz a φ (c • α) = c • Bs.yRres z hz a φ α := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [yRres_add, yRres_add, hp, hq, smul_add]
  | C_mul_T n d => rw [yRres_CT, yRres_CT, yR_smul hz hα, smul_comm]

theorem inD_yRres (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a : V)
    (φ : ℂ[T;T⁻¹]) : Bs.InD z (Bs.yRres z hz a φ α) := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [yRres_add]; exact inD_add hp hq
  | C_mul_T n c => rw [yRres_CT]; exact inD_smul c (inD_yR hz hα a n)

theorem yRres_zero_a (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (φ : ℂ[T;T⁻¹]) :
    Bs.yRres z hz 0 φ α = 0 := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [yRres_add, hp, hq, add_zero]
  | C_mul_T n c =>
    rw [yRres_CT, show (0 : V) = (0 : ℂ) • (0 : V) by simp, yR_smul_a hz hα, zero_smul,
      smul_zero]

/-- Lower truncation of `Y^R` on test functions supported in degrees `≥ N`. -/
theorem yRres_trunc (hz : z ≠ 0) {a : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ}
    (hW : Bs.Wit z a α k N) {e : ℤ} (he : N ≤ e) (p : ℂ[X]) :
    Bs.yRres z hz a (T e * Polynomial.toLaurent p) α = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, yRres_add, hp, hq, add_zero]
  | monomial j c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, Polynomial.toLaurent_C, toLaurent_X_pow',
      show T e * (LC c * T (j : ℤ)) = LC c * T (e + j) by rw [T_add]; ring, yRres_CT,
      yR_trunc hz hW (by omega), smul_zero]

theorem yRres_eq_ys' (hz : z ≠ 0) {a : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ}
    (hW : Bs.Wit z a α k N) {K : ℕ} (hK : k ≤ K) (ψ : ℂ[T;T⁻¹]) :
    Bs.yRres z hz a (Polynomial.toLaurent (lz z ^ K) * ψ) α
      = Bs.ys a (Polynomial.toLaurent (lz z ^ K) * ψ) α :=
  yRres_eq_ys hz (hW.mono hK le_rfl) ψ

/-! ## The Jacobi sums for `Y^R` -/

variable (Bs z) in
/-- Left summand of the `Y^R` Jacobi identity. -/
noncomputable def rJacL (hz : z ≠ 0) (a b : V) (α : Module.Dual ℂ M) (l : ℤ)
    (f g : ℂ[T;T⁻¹]) (j : ℤ) : Module.Dual ℂ M :=
  (negOnePow j * cbz l j) •
    (Bs.yRres z hz a (T (l - j) * f) (Bs.yRres z hz b (T j * g) α)
      - negOnePow l • Bs.yRres z hz b (T (l - j) * g) (Bs.yRres z hz a (T j * f) α))

variable (Bs z) in
/-- Right summand of the `Y^R` Jacobi identity. -/
noncomputable def rJacR (hz : z ≠ 0) (a b : V) (α : Module.Dual ℂ M) (l : ℤ)
    (f g : ℂ[T;T⁻¹]) (i : ℤ) : Module.Dual ℂ M :=
  Bs.yRres z hz (W.smul a (l + i) b) (dd i f * g) α

/-- For `α ∈ D`, `Y^R(a, xʲ f) α = 0` for `j ≫ 0`. -/
theorem yRres_shift_eventually_zero (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α)
    (a : V) (f : ℂ[T;T⁻¹]) : ∃ J : ℤ, ∀ j : ℤ, J ≤ j → Bs.yRres z hz a (T j * f) α = 0 := by
  obtain ⟨e, p, rfl⟩ := exists_T_mul_toLaurent f
  obtain ⟨k, N, hW⟩ := hα a
  refine ⟨N - e, fun j hj => ?_⟩
  rw [← mul_assoc, ← T_add]
  exact yRres_trunc hz hW (by omega) p

theorem rJacL_support_finite (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a b : V)
    (l : ℤ) (f g : ℂ[T;T⁻¹]) : (Function.support (Bs.rJacL z hz a b α l f g)).Finite := by
  obtain ⟨J₁, hJ₁⟩ := yRres_shift_eventually_zero hz hα b g
  obtain ⟨J₂, hJ₂⟩ := yRres_shift_eventually_zero hz hα a f
  apply (Set.finite_Icc 0 (max J₁ J₂)).subset
  intro j hj
  rw [Function.mem_support] at hj
  refine ⟨not_lt.mp fun h => hj ?_, not_lt.mp fun h => hj ?_⟩
  · simp [rJacL, cbz_apply_neg l h]
  · rw [rJacL, hJ₁ j (le_trans (le_max_left _ _) h.le), hJ₂ j (le_trans (le_max_right _ _) h.le),
      yRres_zero_right, yRres_zero_right, smul_zero, sub_zero, smul_zero]

theorem rJacR_support_finite (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a b : V)
    (l : ℤ) (f g : ℂ[T;T⁻¹]) : (Function.support (Bs.rJacR z hz a b α l f g)).Finite := by
  obtain ⟨N, hN⟩ := W.regularity a b
  apply (Set.finite_Icc 0 (N - l)).subset
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [rJacR, dd_neg h, zero_mul, yRres_zero]
  · have h0 : W.smul a (l + i) b = 0 := hN _ (by omega)
    rw [rJacR, h0, yRres_zero_a hz hα]

variable (Bs z) in
/-- The Jacobi defect. -/
noncomputable def jacDef (hz : z ≠ 0) (a b : V) (α : Module.Dual ℂ M) (l : ℤ)
    (f g : ℂ[T;T⁻¹]) : Module.Dual ℂ M :=
  (∑ᶠ j : ℤ, Bs.rJacL z hz a b α l f g j) - ∑ᶠ i : ℤ, Bs.rJacR z hz a b α l f g i

theorem jacDef_add_left (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a b : V)
    (l : ℤ) (f f' g : ℂ[T;T⁻¹]) :
    Bs.jacDef z hz a b α l (f + f') g = Bs.jacDef z hz a b α l f g + Bs.jacDef z hz a b α l f' g := by
  have hL : ∀ j, Bs.rJacL z hz a b α l (f + f') g j
      = Bs.rJacL z hz a b α l f g j + Bs.rJacL z hz a b α l f' g j := by
    intro j
    simp only [rJacL, mul_add, yRres_add,
      yRres_add_right hz (inD_yRres hz hα a _) (inD_yRres hz hα a _)]
    module
  have hR : ∀ i, Bs.rJacR z hz a b α l (f + f') g i
      = Bs.rJacR z hz a b α l f g i + Bs.rJacR z hz a b α l f' g i := by
    intro i; simp only [rJacR, map_add, add_mul, yRres_add]
  unfold jacDef
  rw [finsum_congr hL, finsum_congr hR,
    finsum_add_distrib (rJacL_support_finite hz hα a b l f g)
      (rJacL_support_finite hz hα a b l f' g),
    finsum_add_distrib (rJacR_support_finite hz hα a b l f g)
      (rJacR_support_finite hz hα a b l f' g)]
  abel

theorem jacDef_add_right (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a b : V)
    (l : ℤ) (f g g' : ℂ[T;T⁻¹]) :
    Bs.jacDef z hz a b α l f (g + g') = Bs.jacDef z hz a b α l f g + Bs.jacDef z hz a b α l f g' := by
  have hL : ∀ j, Bs.rJacL z hz a b α l f (g + g') j
      = Bs.rJacL z hz a b α l f g j + Bs.rJacL z hz a b α l f g' j := by
    intro j
    simp only [rJacL, mul_add, yRres_add,
      yRres_add_right hz (inD_yRres hz hα b _) (inD_yRres hz hα b _)]
    module
  have hR : ∀ i, Bs.rJacR z hz a b α l f (g + g') i
      = Bs.rJacR z hz a b α l f g i + Bs.rJacR z hz a b α l f g' i := by
    intro i; simp only [rJacR, mul_add, yRres_add]
  unfold jacDef
  rw [finsum_congr hL, finsum_congr hR,
    finsum_add_distrib (rJacL_support_finite hz hα a b l f g)
      (rJacL_support_finite hz hα a b l f g'),
    finsum_add_distrib (rJacR_support_finite hz hα a b l f g)
      (rJacR_support_finite hz hα a b l f g')]
  abel

/-! ## The three cases of the Chinese-remainder argument -/

/-- Case `g ∈ x^P ℂ[x]`, `P ≫ 0`: the Jacobi defect vanishes. -/
theorem jacDef_trunc_right (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a b : V)
    (l : ℤ) (f : ℂ[T;T⁻¹]) : ∃ P : ℤ, ∀ (e : ℤ) (p : ℂ[X]), P ≤ e →
      Bs.jacDef z hz a b α l f (T e * Polynomial.toLaurent p) = 0 := by
  obtain ⟨ef, pf, rfl⟩ := exists_T_mul_toLaurent f
  obtain ⟨kb, Nb, hWb⟩ := hα b
  obtain ⟨Jf, hJf⟩ := yRres_shift_eventually_zero hz hα a (T ef * Polynomial.toLaurent pf)
  choose kβ Nβ hWβ using fun j : ℕ =>
    inD_yRres hz hα a (T (j : ℤ) * (T ef * Polynomial.toLaurent pf)) b
  obtain ⟨B₁, hB₁⟩ := exists_bound_range Jf.toNat (fun j => Nβ j - l + j)
  obtain ⟨R₀, hR₀⟩ := W.regularity a b
  choose kR NR hWR using fun i : ℕ => hα (W.smul a (l + i) b)
  obtain ⟨B₂, hB₂⟩ := exists_bound_range (R₀ - l).toNat (fun i => NR i - (ef - i))
  refine ⟨max Nb (max B₁ B₂), fun e p he => ?_⟩
  have hL : ∀ j, Bs.rJacL z hz a b α l (T ef * Polynomial.toLaurent pf)
      (T e * Polynomial.toLaurent p) j = 0 := by
    intro j
    rcases lt_or_ge j 0 with hj | hj
    · simp [rJacL, cbz_apply_neg l hj]
    have h1 : Bs.yRres z hz b (T j * (T e * Polynomial.toLaurent p)) α = 0 := by
      rw [← mul_assoc, ← T_add]
      exact yRres_trunc hz hWb (by omega) p
    have h2 : Bs.yRres z hz b (T (l - j) * (T e * Polynomial.toLaurent p))
        (Bs.yRres z hz a (T j * (T ef * Polynomial.toLaurent pf)) α) = 0 := by
      rcases le_or_gt Jf j with hjJ | hjJ
      · rw [hJf j hjJ, yRres_zero_right]
      · obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' := ⟨j.toNat, by omega⟩
        rw [← mul_assoc, ← T_add]
        exact yRres_trunc hz (hWβ j') (by have := hB₁ j' (by omega); omega) p
    rw [rJacL, h1, yRres_zero_right, h2, smul_zero, sub_zero, smul_zero]
  have hR : ∀ i, Bs.rJacR z hz a b α l (T ef * Polynomial.toLaurent pf)
      (T e * Polynomial.toLaurent p) i = 0 := by
    intro i
    rcases lt_or_ge i 0 with hi | hi
    · rw [rJacR, dd_neg hi, zero_mul, yRres_zero]
    rcases le_or_gt (R₀ - l) i with hiR | hiR
    · rw [rJacR, show W.smul a (l + i) b = 0 from hR₀ _ (by omega), yRres_zero_a hz hα]
    obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, by omega⟩
    obtain ⟨p', hp'⟩ := dd_shift i' ef pf
    rw [rJacR, hp', show T (ef - i') * Polynomial.toLaurent p' * (T e * Polynomial.toLaurent p)
        = T (ef - i' + e) * Polynomial.toLaurent (p' * p) by rw [T_add, map_mul]; ring]
    exact yRres_trunc hz (hWR i') (by have := hB₂ i' (by omega); omega) _
  unfold jacDef
  rw [finsum_congr hL, finsum_congr hR]
  simp

/-- Case `f ∈ x^P ℂ[x]`, `P ≫ 0`: the Jacobi defect vanishes. -/
theorem jacDef_trunc_left (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a b : V)
    (l : ℤ) (g : ℂ[T;T⁻¹]) : ∃ P : ℤ, ∀ (e : ℤ) (p : ℂ[X]), P ≤ e →
      Bs.jacDef z hz a b α l (T e * Polynomial.toLaurent p) g = 0 := by
  obtain ⟨eg, pg, rfl⟩ := exists_T_mul_toLaurent g
  obtain ⟨ka, Na, hWa⟩ := hα a
  obtain ⟨Jg, hJg⟩ := yRres_shift_eventually_zero hz hα b (T eg * Polynomial.toLaurent pg)
  choose kβ Nβ hWβ using fun j : ℕ =>
    inD_yRres hz hα b (T (j : ℤ) * (T eg * Polynomial.toLaurent pg)) a
  obtain ⟨B₁, hB₁⟩ := exists_bound_range Jg.toNat (fun j => Nβ j - l + j)
  obtain ⟨R₀, hR₀⟩ := W.regularity a b
  choose kR NR hWR using fun i : ℕ => hα (W.smul a (l + i) b)
  obtain ⟨B₂, hB₂⟩ := exists_bound_range (R₀ - l).toNat (fun i => NR i + i - eg)
  refine ⟨max Na (max B₁ B₂), fun e p he => ?_⟩
  have hL : ∀ j, Bs.rJacL z hz a b α l (T e * Polynomial.toLaurent p)
      (T eg * Polynomial.toLaurent pg) j = 0 := by
    intro j
    rcases lt_or_ge j 0 with hj | hj
    · simp [rJacL, cbz_apply_neg l hj]
    have h1 : Bs.yRres z hz a (T j * (T e * Polynomial.toLaurent p)) α = 0 := by
      rw [← mul_assoc, ← T_add]
      exact yRres_trunc hz hWa (by omega) p
    have h2 : Bs.yRres z hz a (T (l - j) * (T e * Polynomial.toLaurent p))
        (Bs.yRres z hz b (T j * (T eg * Polynomial.toLaurent pg)) α) = 0 := by
      rcases le_or_gt Jg j with hjJ | hjJ
      · rw [hJg j hjJ, yRres_zero_right]
      · obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' := ⟨j.toNat, by omega⟩
        rw [← mul_assoc, ← T_add]
        exact yRres_trunc hz (hWβ j') (by have := hB₁ j' (by omega); omega) p
    rw [rJacL, h1, yRres_zero_right, h2, smul_zero, zero_sub, smul_neg, smul_zero, neg_zero]
  have hR : ∀ i, Bs.rJacR z hz a b α l (T e * Polynomial.toLaurent p)
      (T eg * Polynomial.toLaurent pg) i = 0 := by
    intro i
    rcases lt_or_ge i 0 with hi | hi
    · rw [rJacR, dd_neg hi, zero_mul, yRres_zero]
    rcases le_or_gt (R₀ - l) i with hiR | hiR
    · rw [rJacR, show W.smul a (l + i) b = 0 from hR₀ _ (by omega), yRres_zero_a hz hα]
    obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, by omega⟩
    obtain ⟨p', hp'⟩ := dd_shift i' e p
    rw [rJacR, hp', show T (e - i') * Polynomial.toLaurent p' * (T eg * Polynomial.toLaurent pg)
        = T (e - i' + eg) * Polynomial.toLaurent (p' * pg) by rw [T_add, map_mul]; ring]
    exact yRres_trunc hz (hWR i') (by have := hB₂ i' (by omega); omega) _
  unfold jacDef
  rw [finsum_congr hL, finsum_congr hR]
  simp

/-- `Y^R = Y*` on any test function with a factor `(x − z)^K`, `K` at least a pole bound. -/
theorem yRres_eq_ys_of (hz : z ≠ 0) {a : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ}
    (hW : Bs.Wit z a α k N) {K : ℕ} (hK : k ≤ K) {φ : ℂ[T;T⁻¹]}
    (hφ : ∃ ψ, φ = Polynomial.toLaurent (lz z ^ K) * ψ) :
    Bs.yRres z hz a φ α = Bs.ys a φ α := by
  obtain ⟨ψ, rfl⟩ := hφ
  exact yRres_eq_ys' hz hW hK ψ

/-- Case `f, g ∈ (x − z)^K ℂ[x, x⁻¹]`, `K ≫ 0`: `Y^R = Y*` termwise, and the Jacobi identity
is that of `Y*`. -/
theorem jacDef_lz (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a b : V) (l : ℤ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ F G : ℂ[T;T⁻¹],
      Bs.jacDef z hz a b α l (Polynomial.toLaurent (lz z ^ K) * F)
        (Polynomial.toLaurent (lz z ^ K) * G) = 0 := by
  obtain ⟨ka, Na, hWa⟩ := hα a
  obtain ⟨kb, Nb, hWb⟩ := hα b
  obtain ⟨Kab, hKab⟩ := wit_ys hα b a
  obtain ⟨Kba, hKba⟩ := wit_ys hα a b
  obtain ⟨R₀, hR₀⟩ := W.regularity a b
  choose kR NR hWR using fun i : ℕ => hα (W.smul a (l + i) b)
  obtain ⟨B, hB⟩ := exists_bound_range_nat (R₀ - l).toNat kR
  refine ⟨max (max ka kb) (max (max Kab Kba) B), fun K hK F G => ?_⟩
  have hka : ka ≤ K := by omega
  have hkb : kb ≤ K := by omega
  have hKab' : Kab ≤ K := by omega
  have hKba' : Kba ≤ K := by omega
  set f := Polynomial.toLaurent (lz z ^ K) * F
  set g := Polynomial.toLaurent (lz z ^ K) * G
  have hfac : ∀ (j : ℤ) (H : ℂ[T;T⁻¹]),
      ∃ ψ, T j * (Polynomial.toLaurent (lz z ^ K) * H) = Polynomial.toLaurent (lz z ^ K) * ψ :=
    fun j H => ⟨T j * H, by ring⟩
  have hL : ∀ j, Bs.rJacL z hz a b α l f g j = Bs.ysJacL a b α l f g j := by
    intro j
    simp only [rJacL, ysJacL]
    rw [yRres_eq_ys_of hz hWb hkb (hfac j G), yRres_eq_ys_of hz hWa hka (hfac j F)]
    obtain ⟨N₁, hN₁⟩ := hKab (T j * g)
    obtain ⟨N₂, hN₂⟩ := hKba (T j * f)
    rw [yRres_eq_ys_of hz hN₁ hKab' (hfac (l - j) F), yRres_eq_ys_of hz hN₂ hKba' (hfac (l - j) G)]
  have hR : ∀ i, Bs.rJacR z hz a b α l f g i = Bs.ysJacR a b α l f g i := by
    intro i
    simp only [rJacR, ysJacR]
    rcases lt_or_ge i 0 with hi | hi
    · rw [dd_neg hi, zero_mul, yRres_zero, Bs.ys_zero]
    rcases le_or_gt (R₀ - l) i with hiR | hiR
    · rw [show W.smul a (l + i) b = 0 from hR₀ _ (by omega), yRres_zero_a hz hα, Bs.ys_zero_a]
    obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, by omega⟩
    have hBK : B ≤ K := by omega
    exact yRres_eq_ys_of hz (hWR i') (le_trans (hB i' (by omega)) hBK)
      ⟨dd (i' : ℤ) f * G, by ring⟩
  have hLfin : (Function.support (Bs.ysJacL a b α l f g)).Finite := by
    have := rJacL_support_finite hz hα a b l f g
    rwa [show Bs.rJacL z hz a b α l f g = Bs.ysJacL a b α l f g from funext hL] at this
  have hRfin := Bs.ysJacR_support_finite a b α l f g
  unfold jacDef
  rw [finsum_congr hL, finsum_congr hR, sub_eq_zero]
  ext w
  have h1 := map_finsum (LinearMap.applyₗ (R := ℂ) (M := M) (M₂ := ℂ) w) hLfin
  have h2 := map_finsum (LinearMap.applyₗ (R := ℂ) (M := M) (M₂ := ℂ) w) hRfin
  simp only [LinearMap.applyₗ_apply_apply] at h1 h2
  rw [h1, h2]
  exact Bs.ys_jacobi_apply a b α l f g w

/-- **The Jacobi identity for `Y^R`** (Li, Theorem 3.17), with arbitrary
Laurent-polynomial test functions, on every `P(z)`-linear functional. -/
theorem yRres_jacobi (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a b : V) (l : ℤ)
    (f g : ℂ[T;T⁻¹]) :
    (∑ᶠ j : ℤ, Bs.rJacL z hz a b α l f g j) = ∑ᶠ i : ℤ, Bs.rJacR z hz a b α l f g i := by
  rw [← sub_eq_zero]
  change Bs.jacDef z hz a b α l f g = 0
  obtain ⟨K₀, hK₀⟩ := jacDef_lz hz hα a b l
  obtain ⟨P₁, hP₁⟩ := jacDef_trunc_right hz hα a b l f
  obtain ⟨eg, pg, rfl⟩ := exists_T_mul_toLaurent g
  set L₁ := (P₁ - eg).toNat
  obtain ⟨A₁, B₁, h₁⟩ := bezout hz L₁ K₀
  have h₁' := congrArg Polynomial.toLaurent h₁
  simp only [map_add, map_mul, map_one, toLaurent_X_pow'] at h₁'
  have hg : T eg * Polynomial.toLaurent pg
      = Polynomial.toLaurent (lz z ^ K₀) * (T eg * Polynomial.toLaurent (pg * B₁))
        + T (eg + L₁) * Polynomial.toLaurent (pg * A₁) := by
    rw [T_add]
    simp only [map_mul]
    linear_combination (-(T eg * Polynomial.toLaurent pg)) * h₁'
  rw [hg, jacDef_add_right hz hα, hP₁ _ _ (by omega), add_zero]
  set G₁ := T eg * Polynomial.toLaurent (pg * B₁)
  obtain ⟨P₂, hP₂⟩ := jacDef_trunc_left hz hα a b l (Polynomial.toLaurent (lz z ^ K₀) * G₁)
  obtain ⟨ef, pf, rfl⟩ := exists_T_mul_toLaurent f
  set L₂ := (P₂ - ef).toNat
  obtain ⟨A₂, B₂, h₂⟩ := bezout hz L₂ K₀
  have h₂' := congrArg Polynomial.toLaurent h₂
  simp only [map_add, map_mul, map_one, toLaurent_X_pow'] at h₂'
  have hf : T ef * Polynomial.toLaurent pf
      = Polynomial.toLaurent (lz z ^ K₀) * (T ef * Polynomial.toLaurent (pf * B₂))
        + T (ef + L₂) * Polynomial.toLaurent (pf * A₂) := by
    rw [T_add]
    simp only [map_mul]
    linear_combination (-(T ef * Polynomial.toLaurent pf)) * h₂'
  rw [hf, jacDef_add_left hz hα, hP₂ _ _ (by omega), add_zero]
  exact hK₀ K₀ le_rfl _ _

/-! ## The vacuum -/

theorem ys_vacuum_T (n : ℤ) (α : Module.Dual ℂ M) :
    Bs.ys W.vacuum (T n) α = if n = -1 then α else 0 := by
  ext w
  rw [ys_apply, bres_T, Bs.vacuum]
  split_ifs <;> simp

theorem wit_vacuum (α : Module.Dual ℂ M) : Bs.Wit z W.vacuum α 0 0 := by
  intro q
  rw [T_zero, one_mul, pow_zero, one_mul]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Bs.ys_add, hp, hq, add_zero]
  | monomial j c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, Polynomial.toLaurent_C, toLaurent_X_pow',
      Bs.ys_CT, ys_vacuum_T, if_neg (by omega), smul_zero]

theorem yR_vacuum (hz : z ≠ 0) (n : ℤ) (α : Module.Dual ℂ M) :
    Bs.yR z hz W.vacuum n α = if n = -1 then α else 0 := by
  rcases le_or_gt 0 n with hn | hn
  · rw [yR_trunc hz (wit_vacuum α) hn, if_neg (by omega)]
  obtain ⟨L, hL⟩ : ∃ L : ℕ, n + L = 0 := ⟨(-n).toNat, by omega⟩
  obtain ⟨A, B, hAB⟩ := bezout hz L 0
  rw [yR_eq hz (wit_vacuum α) n L (by omega) A B hAB]
  have hB : B * lz z ^ 0 = 1 - A * Polynomial.X ^ L := by linear_combination hAB
  rw [hB, map_sub, map_one, mul_sub, mul_one, Bs.ys_sub, map_mul, toLaurent_X_pow', ← mul_assoc,
    mul_comm (T n), mul_assoc, ← T_add, hL, ys_vacuum_T]
  have h0 : Bs.ys W.vacuum (Polynomial.toLaurent A * T 0) α = 0 := by
    have := wit_vacuum (Bs := Bs) (z := z) α A
    rwa [T_zero, one_mul, pow_zero, one_mul, ← mul_one (Polynomial.toLaurent A), ← T_zero] at this
  rw [h0, sub_zero]

/-! ## `(D, Y^R)` as a weak module -/

theorem coe_finsum_of {F : ℤ → Bs.Dsub z} {G : ℤ → Module.Dual ℂ M}
    (h : ∀ i, (F i : Module.Dual ℂ M) = G i) (hfin : (Function.support G).Finite) :
    ((∑ᶠ i, F i : Bs.Dsub z) : Module.Dual ℂ M) = ∑ᶠ i, G i := by
  have hF : (Function.support F).Finite := hfin.subset fun i hi => by
    rw [Function.mem_support] at hi ⊢
    rwa [← h i, ne_eq, ZeroMemClass.coe_eq_zero]
  rw [← Submodule.subtype_apply, map_finsum _ hF]
  exact finsum_congr h

variable (Bs z) in
/-- **Li's Theorem 3.17**: the space `D_{P(z)}` of `P(z)`-linear functionals with the
regularized action `Y^R` is a weak `V`-module. -/
noncomputable def weakModuleR (hz : z ≠ 0) : WeakModule W (Bs.Dsub z) where
  YM :=
    { toFun := fun a => (fun k : ℤ => Bs.yRL z hz a (-k - 1) : FormalDist (Module.End ℂ (Bs.Dsub z)))
      map_add' := fun a b => by
        funext k
        exact LinearMap.ext fun α => Subtype.ext (yR_add_a hz α.2 a b _)
      map_smul' := fun c a => by
        funext k
        exact LinearMap.ext fun α => Subtype.ext (yR_smul_a hz α.2 c a _) }
  vacuum_YM := by
    funext k
    refine LinearMap.ext fun α => Subtype.ext ?_
    change Bs.yR z hz W.vacuum (-k - 1) α = _
    rw [yR_vacuum]
    change _ = (((if k = 0 then (1 : Module.End ℂ (Bs.Dsub z)) else 0) α : Bs.Dsub z) : Module.Dual ℂ M)
    by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg (by omega), if_neg hk]; rfl
  truncation := fun a α => by
    obtain ⟨k, N, hW⟩ := α.2 a
    refine ⟨N, fun n hn => Subtype.ext ?_⟩
    change Bs.yR z hz a (-(-n - 1) - 1) α = 0
    exact yR_trunc hz hW (by omega)
  jacobi := fun a b α l m n => by
    have hmode : ∀ (c : V) (p : ℤ) (β : Bs.Dsub z),
        ((mode (fun k : ℤ => Bs.yRL z hz c (-k - 1) : FormalDist (Module.End ℂ (Bs.Dsub z))) p β
          : Bs.Dsub z) : Module.Dual ℂ M) = Bs.yR z hz c p β := by
      intro c p β
      change Bs.yR z hz c (-(-p - 1) - 1) β = _
      congr 1; ring
    refine Subtype.ext ?_
    have hL : ∀ i : ℤ, (((negOnePow i * cbz l i) •
        (mode (fun k : ℤ => Bs.yRL z hz a (-k - 1) : FormalDist (Module.End ℂ (Bs.Dsub z)))
            (l + m - i)
            (mode (fun k : ℤ => Bs.yRL z hz b (-k - 1) : FormalDist (Module.End ℂ (Bs.Dsub z)))
              (n + i) α)
          - negOnePow l •
            mode (fun k : ℤ => Bs.yRL z hz b (-k - 1) : FormalDist (Module.End ℂ (Bs.Dsub z)))
              (l + n - i)
              (mode (fun k : ℤ => Bs.yRL z hz a (-k - 1) : FormalDist (Module.End ℂ (Bs.Dsub z)))
                (m + i) α)) : Bs.Dsub z) : Module.Dual ℂ M)
        = Bs.rJacL z hz a b α l (T m) (T n) i := by
      intro i
      simp only [Submodule.coe_smul, Submodule.coe_sub, hmode, rJacL, ← T_add, yRres_T]
      rw [show l - i + m = l + m - i by ring, show i + n = n + i by ring,
        show l - i + n = l + n - i by ring, show i + m = m + i by ring]
    have hR : ∀ i : ℤ, ((cbz m i •
        mode (fun k : ℤ => Bs.yRL z hz (W.smul a (l + i) b) (-k - 1) :
          FormalDist (Module.End ℂ (Bs.Dsub z))) (m + n - i) α : Bs.Dsub z) : Module.Dual ℂ M)
        = Bs.rJacR z hz a b α l (T m) (T n) i := by
      intro i
      simp only [Submodule.coe_smul, hmode, rJacR, dd_T, mul_assoc, ← T_add, yRres_CT]
      rw [show m - i + n = m + n - i by ring]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [coe_finsum_of hL (rJacL_support_finite hz α.2 a b l _ _),
      coe_finsum_of hR (rJacR_support_finite hz α.2 a b l _ _)]
    exact yRres_jacobi hz α.2 a b l (T m) (T n)

theorem weakModuleR_mode (hz : z ≠ 0) (a : V) (n : ℤ) (α : Bs.Dsub z) :
    ((mode ((Bs.weakModuleR z hz).YM a) n α : Bs.Dsub z) : Module.Dual ℂ M)
      = Bs.yR z hz a n α := by
  change Bs.yR z hz a (-(-n - 1) - 1) α = _
  congr 1; ring

end OppBase

end VOA.Huang.LiRegular
