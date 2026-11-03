import Mathlib

/-!
# The `sl₂` Weyl-module ideal `J_m` and the shift lemma (Chari–Pressley Lemma 6.5)

`R = ℂ[z₀, z₁, …]` (`MvPolynomial ℕ ℂ`), `Z(u) = ∑ zᵢ uⁱ`, `x(r,s) = [uˢ] Z(u)^r`, and
`J_m = (x(r,s) : r ≥ 1, r + s ≥ m + 1)`.  The Garland identities (`Garland.garland`) say exactly that
`x(r,s)` kills the generator of the `sl₂` local Weyl module `W(m)`.

* `sigma_x`: `σ x(r,s) = ∑_j binom(r,j) (−z₀)^{r−j} x(j, r+s)` for the shift `σ : zᵢ ↦ z_{i+1}`;
* `shift_le` (CP Lemma 6.5, `j = 1`): `σ(J_{m−1}) ⊆ J_m`.
-/

namespace VOA.DeligneAudit.Sl2Weyl



noncomputable section

/-- The polynomial ring `ℂ[z₀, z₁, …]`. -/
abbrev R := MvPolynomial ℕ ℂ

/-- The variable `zᵢ`. -/
abbrev z (i : ℕ) : R := MvPolynomial.X i

/-- `Z(u) = ∑ zᵢ uⁱ`. -/
def Zs : PowerSeries R := PowerSeries.mk fun i => z i

/-- `x(r,s) = [uˢ] Z(u)^r`. -/
def xx (r s : ℕ) : R := PowerSeries.coeff s (Zs ^ r)

/-- The ideal `J_m`. -/
def J (m : ℕ) : Ideal R := Ideal.span {p | ∃ r s, 1 ≤ r ∧ m + 1 ≤ r + s ∧ p = xx r s}

theorem xx_mem_J {m r s : ℕ} (hr : 1 ≤ r) (h : m + 1 ≤ r + s) : xx r s ∈ J m :=
  Ideal.subset_span ⟨r, s, hr, h, rfl⟩

/-- The shift `σ : zᵢ ↦ z_{i+1}`. -/
def sigma : R →ₐ[ℂ] R := MvPolynomial.rename (· + 1)

theorem sigma_z (i : ℕ) : sigma (z i) = z (i + 1) := by simp [sigma, z]

/-- `u · σZ(u) = Z(u) − z₀`. -/
theorem X_mul_map_sigma :
    PowerSeries.X * PowerSeries.map sigma.toRingHom Zs = Zs - PowerSeries.C (z 0) := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | n
  · simp [Zs]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [Zs, sigma_z, PowerSeries.coeff_C]

theorem coeff_X_pow_mul' (r s : ℕ) (f : PowerSeries R) :
    PowerSeries.coeff (s + r) (PowerSeries.X ^ r * f) = PowerSeries.coeff s f := by
  rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel]

/-- `σ x(r,s) = ∑_j binom(r,j) (−z₀)^{r−j} x(j, r+s)`. -/
theorem sigma_xx (r s : ℕ) :
    sigma (xx r s) = ∑ j ∈ Finset.range (r + 1),
      ((r.choose j : ℂ) • (-(z 0)) ^ (r - j)) * xx j (s + r) := by
  have h1 : sigma (xx r s) = PowerSeries.coeff s ((PowerSeries.map sigma.toRingHom Zs) ^ r) := by
    rw [xx, ← map_pow, PowerSeries.coeff_map]; rfl
  rw [h1, ← coeff_X_pow_mul' r s, ← mul_pow, X_mul_map_sigma, sub_eq_add_neg, add_pow]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [show (-(PowerSeries.C (z 0)) : PowerSeries R) = PowerSeries.C (-(z 0)) by simp,
    ← map_pow, mul_comm (Zs ^ j), mul_assoc, ← map_natCast (PowerSeries.C (R := R)),
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, ← xx, Nat.cast_smul_eq_nsmul ℂ, nsmul_eq_mul]
  ring

/-- **Shift lemma** (Chari–Pressley Lemma 6.5, `j = 1`): `σ(J_{m−1}) ⊆ J_m`. -/
theorem shift_le (m : ℕ) : Ideal.map sigma (J m) ≤ J (m + 1) := by
  rw [Ideal.map_le_iff_le_comap, J, Ideal.span_le]
  rintro _ ⟨r, s, hr, hrs, rfl⟩
  change sigma (xx r s) ∈ J (m + 1)
  rw [sigma_xx]
  refine Ideal.sum_mem _ fun j hj => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have : xx 0 (s + r) = 0 := by
      rw [xx, pow_zero, PowerSeries.coeff_one, if_neg (by omega)]
    rw [this, mul_zero]; exact Ideal.zero_mem _
  · exact Ideal.mul_mem_left _ _ (xx_mem_J hj0 (by omega))

/-! ## `Y(u) = Z(u) − z₀` and the expansion of `x(q,w)` -/

/-- `Y(u) = ∑_{i ≥ 1} zᵢ uⁱ`. -/
def Ys : PowerSeries R := PowerSeries.mk fun i => if i = 0 then 0 else z i

/-- `y(r,n) = [uⁿ] Y(u)^r`. -/
def yy (r n : ℕ) : R := PowerSeries.coeff n (Ys ^ r)

theorem Zs_eq : Zs = PowerSeries.C (z 0) + Ys := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | n <;> simp [Zs, Ys, PowerSeries.coeff_C]

theorem X_mul_map_sigma' : PowerSeries.X * PowerSeries.map sigma.toRingHom Zs = Ys := by
  rw [X_mul_map_sigma, Zs_eq]; ring

/-- `σ x(r,s) = y(r, r+s)`. -/
theorem sigma_xx' (r s : ℕ) : sigma (xx r s) = yy r (s + r) := by
  have h1 : sigma (xx r s) = PowerSeries.coeff s ((PowerSeries.map sigma.toRingHom Zs) ^ r) := by
    rw [xx, ← map_pow, PowerSeries.coeff_map]; rfl
  rw [h1, ← coeff_X_pow_mul' r s, ← mul_pow, X_mul_map_sigma', yy]

/-- `x(q,w) = ∑_i binom(q,i) z₀^{q−i} y(i,w)`. -/
theorem xx_expand (q w : ℕ) :
    xx q w = ∑ i ∈ Finset.range (q + 1), (q.choose i : R) * z 0 ^ (q - i) * yy i w := by
  rw [xx, Zs_eq, add_comm, add_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow, mul_comm (Ys ^ i), mul_assoc, ← map_natCast (PowerSeries.C (R := R)),
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, ← yy]
  ring

theorem yy_zero (n : ℕ) (hn : 1 ≤ n) : yy 0 n = 0 := by
  rw [yy, pow_zero, PowerSeries.coeff_one, if_neg (by omega)]

theorem yy_eq_zero_of_lt {r n : ℕ} (h : n < r) : yy r n = 0 := by
  rw [yy, ← X_mul_map_sigma', mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem J_anti (m : ℕ) : J (m + 1) ≤ J m := by
  rw [J, Ideal.span_le]
  rintro _ ⟨r, s, hr, hrs, rfl⟩
  exact xx_mem_J hr (by omega)

/-- `y(r,n) ∈ J_m` once `n ≥ m` (and `r ≥ 1`). -/
theorem yy_mem_J {m r n : ℕ} (hr : 1 ≤ r) (hn : m ≤ n) : yy r n ∈ J m := by
  by_cases hrn : r ≤ n
  · obtain ⟨s, rfl⟩ : ∃ s, n = s + r := ⟨n - r, by omega⟩
    rw [← sigma_xx']
    have key : ∀ m', m' + 1 ≤ s + r → sigma (xx r s) ∈ J (m' + 1) := fun m' hm' =>
      shift_le m' (Ideal.mem_map_of_mem _ (xx_mem_J hr (by omega)))
    rcases m with _ | m
    · exact J_anti 0 (key 0 (by omega))
    · exact key m (by omega)
  · rw [yy_eq_zero_of_lt (by omega)]; exact Ideal.zero_mem _

/-! ## The binomial matrix (Chari–Pressley Lemma 6.6, as injectivity) -/

/-- `pb b` evaluates to `binom(x, b+1)` at natural `x`. -/
def pb (b : ℕ) : Polynomial ℂ := (((b + 1).factorial : ℂ))⁻¹ • descPochhammer ℂ (b + 1)

theorem eval_pb (b x : ℕ) : (pb b).eval (x : ℂ) = (x.choose (b + 1) : ℂ) := by
  rw [pb, Polynomial.eval_smul, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, smul_eq_mul]
  push_cast
  rw [inv_mul_cancel_left₀ (by exact_mod_cast Nat.factorial_ne_zero _)]

theorem natDegree_pb (b : ℕ) : (pb b).natDegree ≤ b + 1 :=
  (Polynomial.natDegree_smul_le _ _).trans (descPochhammer_natDegree _ _).le

/-- The matrix `(binom(t+1+a, b+1))_{a,b < n}` is injective. -/
theorem binom_inj (t n : ℕ) (c : ℕ → ℂ)
    (h : ∀ a < n, ∑ b ∈ Finset.range n, ((t + 1 + a).choose (b + 1) : ℂ) * c b = 0) :
    ∀ b < n, c b = 0 := by
  set P : Polynomial ℂ := ∑ b ∈ Finset.range n, c b • pb b with hP
  have hev : ∀ x : ℕ, P.eval (x : ℂ) = ∑ b ∈ Finset.range n, (x.choose (b + 1) : ℂ) * c b := by
    intro x
    rw [hP, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun b _ => by rw [Polynomial.eval_smul, eval_pb, smul_eq_mul, mul_comm]
  have hdeg : P.natDegree ≤ n := by
    rw [hP]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
    rw [Finset.mem_range] at hb
    exact (Polynomial.natDegree_smul_le _ _).trans ((natDegree_pb b).trans (by omega))
  have hzero : P = 0 := by
    let f : Fin (n + 1) → ℂ := fun i => if (i : ℕ) = 0 then 0 else ((t + i : ℕ) : ℂ)
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := f) ?_ ?_ (by simp; omega)
    · intro i j hij
      simp only [f] at hij
      apply Fin.ext
      split_ifs at hij with hi hj hj <;> first | omega | (norm_cast at hij; omega)
    · intro i
      simp only [f]
      split_ifs with hi
      · rw [show (0 : ℂ) = ((0 : ℕ) : ℂ) by simp, hev]
        rw [Nat.cast_zero]
        exact Finset.sum_eq_zero fun b _ => by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      · rw [hev, show t + (i : ℕ) = t + 1 + ((i : ℕ) - 1) by omega]
        exact h _ (by omega)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  have h0 := hev (j + 1)
  rw [hzero, Polynomial.eval_zero, Finset.sum_eq_single j] at h0
  · simpa using h0.symm
  · intro b hb hbj
    rw [Finset.mem_range] at hb
    rcases Nat.lt_or_gt_of_ne hbj with hlt | hgt
    · rw [ih b hlt hb, mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  · intro hj'; exact absurd (Finset.mem_range.mpr hj) hj'

/-- Solving a linear system with the binomial matrix inside a submodule. -/
theorem binom_solve {M : Type*} [AddCommGroup M] [Module ℂ M] (W : Submodule ℂ M) (t n : ℕ)
    (v : ℕ → M) (h : ∀ a < n, ∑ b ∈ Finset.range n, ((t + 1 + a).choose (b + 1) : ℂ) • v b ∈ W) :
    ∀ b < n, v b ∈ W := by
  classical
  let A : Matrix (Fin n) (Fin n) ℂ := fun a b => ((t + 1 + (a : ℕ)).choose ((b : ℕ) + 1) : ℂ)
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hAc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hc
    funext b
    have := binom_inj t n (fun j => if hj : j < n then c ⟨j, hj⟩ else 0) (fun a ha => by
      have := congrFun hAc ⟨a, ha⟩
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, A] at this
      have e : ∑ j ∈ Finset.range n, ((t + 1 + a).choose (j + 1) : ℂ) *
          (if hj : j < n then c ⟨j, hj⟩ else 0) =
          ∑ x : Fin n, ((t + 1 + a).choose ((x : ℕ) + 1) : ℂ) * c x := by
        rw [Finset.sum_range (fun j => ((t + 1 + a).choose (j + 1) : ℂ) *
          (if hj : j < n then c ⟨j, hj⟩ else 0))]
        simp
      rw [e]; exact this) b b.2
    simpa using this
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet)
  intro b hb
  have hw : ∀ a : Fin n, ∑ b' : Fin n, A a b' • v b' ∈ W := fun a => by
    have := h a a.2
    rwa [Finset.sum_range (fun j => ((t + 1 + (a : ℕ)).choose (j + 1) : ℂ) • v j)] at this
  have key : v b = ∑ a : Fin n, A⁻¹ ⟨b, hb⟩ a • ∑ b' : Fin n, A a b' • v b' := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have : ∀ b' : Fin n, (∑ a : Fin n, A⁻¹ ⟨b, hb⟩ a * A a b') = (1 : Matrix (Fin n) (Fin n) ℂ) ⟨b, hb⟩ b' := by
      intro b'; rw [← hinv, Matrix.mul_apply]
    simp only [this, Matrix.one_apply]
    rw [Finset.sum_eq_single ⟨b, hb⟩]
    · simp
    · intro b' _ hb'; rw [if_neg (Ne.symm hb'), zero_smul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  rw [key]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hw a)

/-- The "good" part: `z₀`-powers below `e`, times `y(i,n)`. -/
def Good (e n : ℕ) : Submodule ℂ R :=
  Submodule.span ℂ {p | ∃ a i, a < e ∧ p = z 0 ^ a * yy i n}

/-- **Chari–Pressley Lemma 6.7 (variant)**: if `1 ≤ m − n ≤ k`, then `z₀^k y(r,n)` lies in
`J_m + span{z₀^a y(i,n) : a < m − n}`. -/
theorem lemmaY (m n k r : ℕ) (hr : 1 ≤ r) (hn1 : 1 ≤ n) (hnm : n < m) (hk : m ≤ n + k) :
    z 0 ^ k * yy r n ∈ (J m).restrictScalars ℂ ⊔ Good (m - n) n := by
  set t := m - n with ht
  set L := k + r with hL
  set W := (J m).restrictScalars ℂ ⊔ Good t n
  let v : ℕ → R := fun b => z 0 ^ (L - (b + 1)) * yy (b + 1) n
  have hgood : ∀ i, L - t < i → z 0 ^ (L - i) * yy i n ∈ W := fun i hi =>
    Submodule.mem_sup_right (Submodule.subset_span ⟨L - i, i, by omega, rfl⟩)
  have hrel : ∀ a < L - t, ∑ b ∈ Finset.range (L - t), ((t + 1 + a).choose (b + 1) : ℂ) • v b ∈ W := by
    intro a ha
    set q := t + 1 + a with hq
    -- the relation `z₀^{L−q} x(q,n) ∈ J_m`
    have hJ : z 0 ^ (L - q) * xx q n ∈ W :=
      Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (xx_mem_J (by omega) (by omega)))
    rw [xx_expand, Finset.mul_sum] at hJ
    -- split off the terms `i > L − t` (good) and `i = 0` (zero)
    let f : ℕ → R := fun i => (q.choose i : ℂ) • (z 0 ^ (L - i) * yy i n)
    have hterm : ∀ i ∈ Finset.range (q + 1),
        z 0 ^ (L - q) * ((q.choose i : R) * z 0 ^ (q - i) * yy i n) = f i := by
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [f, Algebra.smul_def, map_natCast]
      rw [show L - i = (L - q) + (q - i) by omega, pow_add]
      ring
    rw [Finset.sum_congr rfl hterm] at hJ
    have hext : ∑ i ∈ Finset.range (q + 1), f i = ∑ i ∈ Finset.range (L + 1), f i := by
      refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i hi hi' => ?_
      simp only [Finset.mem_range] at hi hi'
      simp [f, Nat.choose_eq_zero_of_lt (show q < i by omega)]
    have h0 : f 0 = 0 := by simp [f, yy_zero n hn1]
    rw [hext, Finset.sum_range_succ', h0, add_zero,
      ← Finset.sum_range_add_sum_Ico _ (show L - t ≤ L by omega)] at hJ
    have h2 : ∑ j ∈ Finset.Ico (L - t) L, f (j + 1) ∈ W :=
      Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
        (hgood (j + 1) (by rw [Finset.mem_Ico] at hj; omega))
    have h3 := W.sub_mem hJ h2
    rw [add_sub_cancel_right] at h3
    exact h3
  have := binom_solve W t (L - t) v hrel (r - 1) (by omega)
  simp only [v, show r - 1 + 1 = r by omega, show L - r = k by omega] at this
  exact this

/-! ## Box monomials -/

/-- The box condition: every index `i` used satisfies `i + deg ≤ m`. -/
def BoxP (m : ℕ) (f : ℕ →₀ ℕ) : Prop := ∀ i ∈ f.support, i + Finsupp.degree f ≤ m

/-- Box monomials with at most `k` zeros. -/
def Bk (m k : ℕ) : Submodule ℂ R :=
  Submodule.span ℂ {p | ∃ f, BoxP m f ∧ f 0 ≤ k ∧ p = MvPolynomial.monomial f 1}

/-- The target `Bk m k + J_m`. -/
def T (m k : ℕ) : Submodule ℂ R := Bk m k ⊔ (J m).restrictScalars ℂ

theorem Bk_mono (m : ℕ) {k k' : ℕ} (h : k ≤ k') : Bk m k ≤ Bk m k' :=
  Submodule.span_mono fun _ ⟨f, hb, hk, hp⟩ => ⟨f, hb, hk.trans h, hp⟩

theorem T_mono (m : ℕ) {k k' : ℕ} (h : k ≤ k') : T m k ≤ T m k' := sup_le_sup_right (Bk_mono m h) _

theorem degree_mapDomain_succ (f : ℕ →₀ ℕ) :
    Finsupp.degree (Finsupp.mapDomain (· + 1) f) = Finsupp.degree f := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
      rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
        Finsupp.degree_single, Finsupp.degree_single]

theorem mapDomain_succ_zero (f : ℕ →₀ ℕ) : Finsupp.mapDomain (· + 1) f 0 = 0 :=
  Finsupp.mapDomain_notin_range _ _ (by simp)

theorem mapDomain_succ_apply (f : ℕ →₀ ℕ) (i : ℕ) : Finsupp.mapDomain (· + 1) f (i + 1) = f i :=
  Finsupp.mapDomain_apply (fun a b h => by simpa using h) f i

/-- `z₀^k σ(box monomial of J_{m−k−1})` is a box monomial of `J_m` with `k` zeros. -/
theorem shift_box {m k : ℕ} (hk : k < m) {f : ℕ →₀ ℕ} (hf : BoxP (m - k - 1) f) :
    z 0 ^ k * sigma (MvPolynomial.monomial f 1) ∈ Bk m k := by
  refine Submodule.subset_span ⟨Finsupp.single 0 k + Finsupp.mapDomain (· + 1) f, ?_, ?_, ?_⟩
  · intro i hi
    rw [map_add, Finsupp.degree_single, degree_mapDomain_succ]
    have hdeg : Finsupp.degree f ≤ m - k - 1 ∨ f = 0 := by
      by_cases hf0 : f = 0
      · exact Or.inr hf0
      · obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hf0
        exact Or.inl (by have := hf j hj; omega)
    rcases i with _ | i
    · rcases hdeg with h | rfl
      · omega
      · simp; omega
    · have : f i ≠ 0 := by
        intro h0
        apply Finsupp.mem_support_iff.mp hi
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega), mapDomain_succ_apply, h0]
        rfl
      have := hf i (Finsupp.mem_support_iff.mpr this)
      omega
  · rw [Finsupp.add_apply, Finsupp.single_eq_same, mapDomain_succ_zero]; simp
  · rw [sigma, MvPolynomial.rename_monomial]
    rw [show z 0 ^ k = MvPolynomial.monomial (Finsupp.single 0 k) 1 by
      rw [z, MvPolynomial.X_pow_eq_monomial]]
    rw [MvPolynomial.monomial_mul, one_mul]

/-! ## Chari–Pressley Proposition 6.1 -/

theorem yy_eq_sigma (i n : ℕ) : ∃ h, yy i n = sigma h := by
  by_cases hin : i ≤ n
  · exact ⟨xx i (n - i), by rw [sigma_xx', Nat.sub_add_cancel hin]⟩
  · exact ⟨0, by rw [yy_eq_zero_of_lt (by omega), map_zero]⟩

theorem yy_one (p : ℕ) (hp : 1 ≤ p) : yy 1 p = z p := by
  simp [yy, Ys, if_neg (show p ≠ 0 by omega)]

theorem xx_zero_right (k : ℕ) : xx k 0 = z 0 ^ k := by
  rw [xx, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
  simp [Zs]

theorem J_mem_T {m k : ℕ} {x : R} (hx : x ∈ J m) : x ∈ T m k := Submodule.mem_sup_right hx

/-- The core reduction, assuming the Claim for fewer zeros. -/
theorem core {m k : ℕ} (IH : ∀ e < k, ∀ h, z 0 ^ e * sigma h ∈ T m e) {n r : ℕ} (a : R)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hmk : m ≤ n + k) : z 0 ^ k * (sigma a * yy r n) ∈ T m k := by
  by_cases hmn : m ≤ n
  · exact J_mem_T (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (yy_mem_J hr hmn)))
  · obtain ⟨j, hj, g, hg, hjg⟩ := Submodule.mem_sup.mp (lemmaY m n k r hr hn (by omega) hmk)
    rw [show z 0 ^ k * (sigma a * yy r n) = sigma a * (z 0 ^ k * yy r n) by ring, ← hjg, mul_add]
    clear hjg
    refine Submodule.add_mem _ (J_mem_T (Ideal.mul_mem_left _ _ hj)) ?_
    induction hg using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨e, i, he, rfl⟩ := hx
        obtain ⟨h, hh⟩ := yy_eq_sigma i n
        rw [hh, show sigma a * (z 0 ^ e * sigma h) = z 0 ^ e * sigma (a * h) by rw [map_mul]; ring]
        exact T_mono m (by omega) (IH e (by omega) _)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem sigma_C (c : ℂ) : sigma (MvPolynomial.C c) = MvPolynomial.C c := sigma.commutes c

/-- **The Claim** of Chari–Pressley Prop. 6.1: `z₀^k σ(h) ∈ Bk m k + J_m`, given the
proposition for smaller `m`. -/
theorem claim {m : ℕ} (HP : ∀ m' < m, ∀ p : R, p ∈ T m' m') :
    ∀ k h, z 0 ^ k * sigma h ∈ T m k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro h
  by_cases hk : k < m
  · obtain ⟨b, hb, j, hj, rfl⟩ := Submodule.mem_sup.mp (HP (m - k - 1) (by omega) h)
    rw [map_add, mul_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) ?_
    · induction hb using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨f, hf, -, rfl⟩ := hx
          exact shift_box hk hf
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, mul_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul, mul_smul_comm]; exact Submodule.smul_mem _ _ hx
    · -- `j ∈ J_{m−k−1}`
      have key : ∀ x ∈ J (m - k - 1), ∀ a, z 0 ^ k * sigma (a * x) ∈ T m k := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
            obtain ⟨r, s, hr, hrs, rfl⟩ := hx
            intro a
            rw [map_mul, sigma_xx']
            exact core IH a (by omega) hr (by omega)
        | zero => intro a; simp
        | add x y _ _ hx hy => intro a; rw [mul_add, map_add, mul_add]; exact Submodule.add_mem _ (hx a) (hy a)
        | smul c x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx (a * c)
      simpa using key j hj 1
  · -- `k ≥ m`: split off the constant term
    have hdec : ∀ h : R, h - MvPolynomial.C (MvPolynomial.constantCoeff h) ∈
        Ideal.span (Set.range (MvPolynomial.X : ℕ → R)) := by
      intro h
      induction h using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
          rw [map_add, map_add, add_sub_add_comm]; exact Ideal.add_mem _ hp hq
      | mul_X p n _ =>
          rw [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, rfl⟩)
    have hI : ∀ x ∈ Ideal.span (Set.range (MvPolynomial.X : ℕ → R)), ∀ a,
        z 0 ^ k * sigma (a * x) ∈ T m k := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          intro a
          rw [map_mul, show sigma (MvPolynomial.X i) = yy 1 (i + 1) by
            rw [yy_one _ (by omega)]; exact sigma_z i]
          exact core IH a (by omega) le_rfl (by omega)
      | zero => intro a; simp
      | add x y _ _ hx hy => intro a; rw [mul_add, map_add, mul_add]; exact Submodule.add_mem _ (hx a) (hy a)
      | smul c x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx (a * c)
    have hsplit : h = MvPolynomial.C (MvPolynomial.constantCoeff h) +
        (h - MvPolynomial.C (MvPolynomial.constantCoeff h)) := by ring
    rw [hsplit, map_add, mul_add]
    refine Submodule.add_mem _ ?_ (by simpa using hI _ (hdec h) 1)
    rw [sigma_C, show z 0 ^ k * MvPolynomial.C (MvPolynomial.constantCoeff h) =
      (MvPolynomial.constantCoeff h) • z 0 ^ k by rw [MvPolynomial.smul_eq_C_mul, mul_comm]]
    refine Submodule.smul_mem _ _ ?_
    rcases Nat.lt_or_ge m k with hmk | hmk
    · exact J_mem_T (by rw [← xx_zero_right]; exact xx_mem_J (by omega) (by omega))
    · obtain rfl : k = m := by omega
      refine Submodule.mem_sup_left (Submodule.subset_span ⟨Finsupp.single 0 k, ?_, by simp, ?_⟩)
      · intro i hi
        rw [Finsupp.degree_single]
        rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hi
        split_ifs at hi with h0
        · omega
        · exact absurd rfl hi
      · rw [z, MvPolynomial.X_pow_eq_monomial]

/-- **Chari–Pressley Proposition 6.1**: box monomials span `R/J_m`. -/
theorem box_span : ∀ m (p : R), p ∈ T m m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m HP =>
  have hcl := claim HP
  -- every polynomial is a combination of `z₀^k σ(h)`
  let S : Set R := {p | ∃ k h, p = z 0 ^ k * sigma h}
  have hS : ∀ p : R, p ∈ Submodule.span ℂ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact Submodule.subset_span ⟨0, MvPolynomial.C a, by rw [sigma_C]; simp⟩
    | add p q hp hq => exact Submodule.add_mem _ hp hq
    | mul_X p n hp =>
        induction hp using Submodule.span_induction with
        | mem x hx =>
            obtain ⟨k, h, rfl⟩ := hx
            rcases n with _ | i
            · exact Submodule.subset_span ⟨k + 1, h, by rw [pow_succ]; ring⟩
            · exact Submodule.subset_span ⟨k, h * MvPolynomial.X i, by
                rw [map_mul, sigma_z]; ring⟩
        | zero => simp
        | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  have hle : ∀ k, T m k ≤ T m m := by
    intro k
    refine sup_le_sup_right (Submodule.span_mono ?_) _
    rintro x ⟨f, hb, -, hx⟩
    refine ⟨f, hb, ?_, hx⟩
    by_cases h0 : f 0 = 0
    · omega
    · have := hb 0 (Finsupp.mem_support_iff.mpr h0)
      have : f 0 ≤ Finsupp.degree f := Finsupp.le_degree 0 f
      omega
  intro p
  refine Submodule.span_le.mpr ?_ (hS p)
  rintro _ ⟨k, h, rfl⟩
  exact hle k (hcl k h)

/-! ## The graded refinement (bidegree = (length, `t`-degree)) -/

/-- The bigrading weight `zᵢ ↦ (1, i)`. -/
def om : ℕ → ℕ × ℕ := fun i => (1, i)

theorem xx_hom (r s : ℕ) : MvPolynomial.IsWeightedHomogeneous om (xx r s) (r, s) := by
  induction r generalizing s with
  | zero =>
      rw [xx, pow_zero, PowerSeries.coeff_one]
      split_ifs with h
      · subst h; exact MvPolynomial.isWeightedHomogeneous_one ℂ om
      · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  | succ r ih =>
      rw [xx, pow_succ, PowerSeries.coeff_mul]
      refine (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun x hx => ?_)
      rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
      rw [Finset.mem_antidiagonal] at hx
      have h1 := ih x.1
      have h2 : MvPolynomial.IsWeightedHomogeneous om (PowerSeries.coeff x.2 Zs) (1, x.2) := by
        simp only [Zs, PowerSeries.coeff_mk, z]
        exact MvPolynomial.isWeightedHomogeneous_X ℂ om x.2
      have := h1.mul h2
      convert this using 1
      simp [Prod.ext_iff]; omega

theorem comp_mem_J (m : ℕ) (n : ℕ × ℕ) {x : R} (hx : x ∈ J m) :
    MvPolynomial.weightedHomogeneousComponent om n x ∈ J m := by
  have key : ∀ x ∈ J m, ∀ a : R, ∀ n, MvPolynomial.weightedHomogeneousComponent om n (a * x) ∈ J m := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨r, s, hr, hrs, rfl⟩ := hg
        intro a n
        induction a using MvPolynomial.induction_on' with
        | monomial f c =>
            have hh := (MvPolynomial.isWeightedHomogeneous_monomial om f c rfl).mul (xx_hom r s)
            by_cases hn : n = Finsupp.weight om f + (r, s)
            · rw [hn, hh.weightedHomogeneousComponent_same]
              exact Ideal.mul_mem_left _ _ (xx_mem_J hr hrs)
            · rw [hh.weightedHomogeneousComponent_ne n hn]; exact Ideal.zero_mem _
        | add p q hp hq => rw [add_mul, map_add]; exact Ideal.add_mem _ hp hq
    | zero => intro a n; simp
    | add x y _ _ hx hy => intro a n; rw [mul_add, map_add]; exact Ideal.add_mem _ (hx a n) (hy a n)
    | smul c x _ hx => intro a n; rw [smul_eq_mul, ← mul_assoc]; exact hx (a * c) n
  simpa using key x hx 1 n

/-- **Graded box spanning**: a bihomogeneous polynomial lies in the span of the box monomials
of the same bidegree, modulo `J_m`. -/
theorem box_span_graded (m : ℕ) {p : R} {n : ℕ × ℕ} (hp : MvPolynomial.IsWeightedHomogeneous om p n) :
    p ∈ Submodule.span ℂ {q | ∃ f, BoxP m f ∧ Finsupp.weight om f = n ∧
        q = MvPolynomial.monomial f 1} ⊔ (J m).restrictScalars ℂ := by
  obtain ⟨b, hb, j, hj, hbj⟩ := Submodule.mem_sup.mp (box_span m p)
  rw [← hp.weightedHomogeneousComponent_same, ← hbj, map_add]
  refine Submodule.add_mem_sup ?_ (comp_mem_J m n hj)
  clear hbj
  induction hb using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨f, hf, -, rfl⟩ := hx
      have hh := MvPolynomial.isWeightedHomogeneous_monomial om f (1 : ℂ) rfl
      by_cases hn : n = Finsupp.weight om f
      · rw [hn, hh.weightedHomogeneousComponent_same]
        exact Submodule.subset_span ⟨f, hf, rfl, rfl⟩
      · rw [hh.weightedHomogeneousComponent_ne n hn]; exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end

end VOA.DeligneAudit.Sl2Weyl

section AxiomAudit
#print axioms VOA.DeligneAudit.Sl2Weyl.shift_le
end AxiomAudit

section AxiomAudit2
#print axioms VOA.DeligneAudit.Sl2Weyl.box_span
end AxiomAudit2
