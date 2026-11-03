import VOA.Huang.LiRegularLeft

/-! # `Y^L` and `Y^R` commute (Li, Proposition 3.24)

The translated base `Ts = Y°(·, x + z)` and the original base `Bs = Y°` do not commute;
their commutator is a "mixed residue"

  `[Ts(a,p), Bs(b,q)] = − Σᵢ C(p,i) Mix(a₍ᵢ₎b, p − i, q)`,
  `Mix(c, p, q) = Σₖ C(p,k) (−z)ᵏ c°_{p+q−k} = Res_y (y − z)^p y^q Y°(c, y)`

(`transB_comm`).  When the test functions carry the factors `(x + z)^K` and `(y − z)^{K'}`,
the mixed residue is an ordinary residue of a polynomial divisible by
`y^{K−i} (y − z)^{K'−…}`, which every `P(z)`-linear functional kills
(`mres_eq_bres`).  Choosing the Bézout data of `Y^L` and `Y^R` with large exponents gives
`yL_yR_comm`: `Y^L(a)_m Y^R(b)_n α = Y^R(b)_n Y^L(a)_m α` on `D_{P(z)}(M)`.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiConverse LaurentPolynomial
open scoped BigOperators Polynomial

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Binomial bookkeeping -/

theorem ff_add (p : ℤ) (k i : ℕ) : ff p k * ff (p - k) i = ff p (k + i) := by
  rw [ff, ff, ff, Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast; ring

/-- The trinomial identity `C(p,k) C(p−k,i) = C(p,i) C(p−i,k)`. -/
theorem cbz_trinomial (p : ℤ) (k i : ℕ) :
    cbz p k * cbz (p - k) i = cbz p i * cbz (p - i) k := by
  rw [← ff_div_factorial, ← ff_div_factorial, ← ff_div_factorial, ← ff_div_factorial]
  rw [div_mul_div_comm, div_mul_div_comm, ff_add, ff_add, add_comm k i, mul_comm (k.factorial : ℂ)]

/-! ## The mixed residue -/

namespace OppBase

variable (Bs : OppBase W M) (z : ℂ)

/-- The summands of `Mix(c,p,q) = Σₖ C(p,k)(−z)ᵏ c°_{p+q−k}`. -/
noncomputable def mixTerm (c : V) (p q : ℤ) (w : M) (k : ℕ) : M :=
  (cbz p k * (-z) ^ k) • Bs.B c (p + q - k) w

theorem mixTerm_eventually_zero (c : V) (p q : ℤ) (w : M) :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → Bs.mixTerm z c p q w k = 0 := by
  obtain ⟨K, hK⟩ := Bs.trunc c w
  refine ⟨(p + q - K).toNat, fun k hk => ?_⟩
  rw [mixTerm, hK _ (by omega), smul_zero]

theorem mixTerm_support_finite (c : V) (p q : ℤ) (w : M) :
    (Function.support (Bs.mixTerm z c p q w)).Finite := by
  obtain ⟨K₀, hK₀⟩ := Bs.mixTerm_eventually_zero z c p q w
  exact (Finset.range K₀).finite_toSet.subset fun k hk => by
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h; exact hk (hK₀ k (not_lt.mp h))

/-- **The mixed residue** `Mix(c,p,q) = Res_y (y − z)^p y^q Y°(c,y)` (expanded at `∞`). -/
noncomputable def mixOp (c : V) (p q : ℤ) : Module.End ℂ M where
  toFun w := ∑ᶠ k : ℕ, Bs.mixTerm z c p q w k
  map_add' w w' := by
    rw [← finsum_add_distrib (Bs.mixTerm_support_finite z c p q w)
      (Bs.mixTerm_support_finite z c p q w')]
    exact finsum_congr fun k => by simp [mixTerm, smul_add]
  map_smul' d w := by
    rw [RingHom.id_apply, smul_finsum]
    exact finsum_congr fun k => by simp [mixTerm, smul_comm d]

theorem mixOp_eq_sum (c : V) (p q : ℤ) (w : M) {K₀ : ℕ}
    (hK₀ : ∀ k : ℕ, K₀ ≤ k → Bs.mixTerm z c p q w k = 0) :
    Bs.mixOp z c p q w = ∑ k ∈ Finset.range K₀, Bs.mixTerm z c p q w k :=
  finsum_eq_sum_of_support_subset _ fun k hk => by
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h; exact hk (hK₀ k (not_lt.mp h))

/-- Pascal's rule for the mixed residue: multiplying the test function by `y − z`. -/
theorem mixOp_pascal (c : V) (p q : ℤ) (w : M) :
    Bs.mixOp z c p (q + 1) w - z • Bs.mixOp z c p q w = Bs.mixOp z c (p + 1) q w := by
  obtain ⟨K₁, h₁⟩ := Bs.mixTerm_eventually_zero z c p (q + 1) w
  obtain ⟨K₂, h₂⟩ := Bs.mixTerm_eventually_zero z c p q w
  obtain ⟨K₃, h₃⟩ := Bs.mixTerm_eventually_zero z c (p + 1) q w
  set K := max K₁ (max K₂ K₃) + 1
  rw [Bs.mixOp_eq_sum z c p (q + 1) w (K₀ := K) (fun k hk => h₁ k (by omega)),
    Bs.mixOp_eq_sum z c p q w (K₀ := K) (fun k hk => h₂ k (by omega)),
    Bs.mixOp_eq_sum z c (p + 1) q w (K₀ := K) (fun k hk => h₃ k (by omega))]
  -- `z • Σ_{k<K} = Σ_{k<K} (shifted)`, using `C(p+1,k) = C(p,k) + C(p,k−1)`
  have hshift : z • ∑ k ∈ Finset.range K, Bs.mixTerm z c p q w k
      = - ∑ k ∈ Finset.range (K + 1), (cbz p ((k : ℤ) - 1) * (-z) ^ k) •
          Bs.B c (p + 1 + q - k) w := by
    rw [Finset.sum_range_succ' _ K]
    simp only [CharP.cast_eq_zero, zero_sub, cbz_apply_neg p (show (-1 : ℤ) < 0 by norm_num),
      zero_mul, zero_smul, add_zero, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mixTerm, smul_smul, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring,
      show p + 1 + q - ((k + 1 : ℕ) : ℤ) = p + q - k by push_cast; ring, ← neg_smul]
    congr 1
    rw [pow_succ]; ring
  have hlast : (cbz p ((K : ℤ) - 1) * (-z) ^ K) • Bs.B c (p + 1 + q - K) w = 0 := by
    have := h₂ (K - 1) (by omega)
    rw [mixTerm, show ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 by omega,
      show p + q - ((K : ℤ) - 1) = p + 1 + q - K by ring] at this
    rcases eq_or_ne (cbz p ((K : ℤ) - 1) * (-z) ^ (K - 1)) 0 with h | h
    · rw [show (-z) ^ K = (-z) ^ (K - 1) * (-z) by
          rw [← pow_succ, Nat.sub_add_cancel (by omega)], ← mul_assoc, h, zero_mul, zero_smul]
    · rw [smul_eq_zero] at this
      rcases this with h' | h'
      · exact absurd h' h
      · rw [h', smul_zero]
  rw [hshift, sub_neg_eq_add, Finset.sum_range_succ (fun k : ℕ =>
    (cbz p ((k : ℤ) - 1) * (-z) ^ k) • Bs.B c (p + 1 + q - k) w) K, hlast, add_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mixTerm, mixTerm, show p + (q + 1) - k = p + 1 + q - k by ring, ← add_smul,
    cbz_pascal_up p k]
  congr 1
  ring

theorem mixOp_zero_p (c : V) (q : ℤ) : Bs.mixOp z c 0 q = Bs.B c q := by
  ext w
  have hK : ∀ k : ℕ, 1 ≤ k → Bs.mixTerm z c 0 q w k = 0 := fun k hk => by
    rw [mixTerm, cbz_lt (p := 0) (c := (k : ℤ)) le_rfl (by omega), zero_mul, zero_smul]
  rw [Bs.mixOp_eq_sum z c 0 q w hK]
  simp [mixTerm]

theorem mixOp_nonneg (c : V) (p : ℕ) (q : ℤ) :
    Bs.mixOp z c p q = Bs.bres c (Polynomial.toLaurent (lz z ^ p) * T q) := by
  induction p generalizing q with
  | zero => rw [Nat.cast_zero, mixOp_zero_p, pow_zero, map_one, one_mul, bres_T]
  | succ p ih =>
    ext w
    have h := Bs.mixOp_pascal z c p q w
    push_cast
    rw [← h, ih, ih]
    have e : Polynomial.toLaurent (lz z ^ (p + 1)) * T q
        = Polynomial.toLaurent (lz z ^ p) * T (q + 1)
          - z • (Polynomial.toLaurent (lz z ^ p) * T q) := by
      rw [pow_succ, map_mul, lz, map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C, T_add,
        smul_eq_C_mul]
      ring
    rw [e, Bs.bres_sub, Bs.bres_smul, LinearMap.sub_apply, LinearMap.smul_apply]

/-- `Mix` paired with a Laurent test function in `y`. -/
noncomputable def mixRes (c : V) (p : ℤ) (ψ : ℂ[T;T⁻¹]) : Module.End ℂ M :=
  Finsupp.linearCombination ℂ (fun q => Bs.mixOp z c p q) ψ

theorem mixRes_CT (c : V) (p : ℤ) (d : ℂ) (q : ℤ) :
    Bs.mixRes z c p (LC d * T q) = d • Bs.mixOp z c p q := by
  rw [mixRes, ← single_eq_C_mul_T, Finsupp.linearCombination_single]

theorem mixRes_add (c : V) (p : ℤ) (ψ ψ' : ℂ[T;T⁻¹]) :
    Bs.mixRes z c p (ψ + ψ') = Bs.mixRes z c p ψ + Bs.mixRes z c p ψ' := map_add _ _ _

/-- Absorbing a factor `y − z` of the test function into the exponent `p`. -/
theorem mixRes_lz (c : V) (p : ℤ) (Ψ : ℂ[T;T⁻¹]) :
    Bs.mixRes z c p (Polynomial.toLaurent (lz z) * Ψ) = Bs.mixRes z c (p + 1) Ψ := by
  induction Ψ using LaurentPolynomial.induction_on' with
  | add f g hf hg => rw [mul_add, mixRes_add, mixRes_add, hf, hg]
  | C_mul_T q d =>
    ext w
    have e : Polynomial.toLaurent (lz z) * (LC d * T q) = LC d * T (q + 1) - LC (z * d) * T q := by
      rw [lz, map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C, T_add, map_mul]; ring
    rw [e, sub_eq_add_neg, ← neg_one_smul ℂ (LC (z * d) * T q), smul_eq_C_mul, ← mul_assoc,
      ← map_mul, mixRes_add, mixRes_CT, mixRes_CT, mixRes_CT, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      ← Bs.mixOp_pascal z c p q w]
    simp only [smul_sub, smul_smul]
    rw [show (-1 * (z * d)) = -(d * z) by ring, neg_smul, ← sub_eq_add_neg]

theorem mixRes_lz_pow (c : V) (p : ℤ) (K : ℕ) (Ψ : ℂ[T;T⁻¹]) :
    Bs.mixRes z c p (Polynomial.toLaurent (lz z ^ K) * Ψ) = Bs.mixRes z c (p + K) Ψ := by
  induction K generalizing p with
  | zero => simp
  | succ K ih =>
    rw [pow_succ', map_mul, mul_assoc, mixRes_lz, ih]
    congr 1; push_cast; ring

theorem mixRes_nonneg (c : V) (p : ℕ) (Ψ : ℂ[T;T⁻¹]) :
    Bs.mixRes z c p Ψ = Bs.bres c (Polynomial.toLaurent (lz z ^ p) * Ψ) := by
  induction Ψ using LaurentPolynomial.induction_on' with
  | add f g hf hg => rw [mixRes_add, hf, hg, mul_add, Bs.bres_add]
  | C_mul_T q d =>
    rw [mixRes_CT, mixOp_nonneg, show Polynomial.toLaurent (lz z ^ p) * (LC d * T q)
      = d • (Polynomial.toLaurent (lz z ^ p) * T q) by rw [smul_eq_C_mul]; ring, Bs.bres_smul]

/-- The mixed residue paired with test functions in both variables. -/
noncomputable def mres (c : V) (F ψ : ℂ[T;T⁻¹]) : Module.End ℂ M :=
  Finsupp.linearCombination ℂ (fun p => Bs.mixRes z c p ψ) F

theorem mres_add (c : V) (F F' ψ : ℂ[T;T⁻¹]) :
    Bs.mres z c (F + F') ψ = Bs.mres z c F ψ + Bs.mres z c F' ψ := map_add _ _ _

theorem mres_add_right (c : V) (F ψ ψ' : ℂ[T;T⁻¹]) :
    Bs.mres z c F (ψ + ψ') = Bs.mres z c F ψ + Bs.mres z c F ψ' := by
  induction F using LaurentPolynomial.induction_on' with
  | add f g hf hg => rw [mres_add, mres_add, mres_add, hf, hg]; abel
  | C_mul_T p d =>
    rw [mres, mres, mres, ← single_eq_C_mul_T, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, Finsupp.linearCombination_single, mixRes_add, smul_add]

theorem mres_CT (c : V) (d : ℂ) (p : ℤ) (ψ : ℂ[T;T⁻¹]) :
    Bs.mres z c (LC d * T p) ψ = d • Bs.mixRes z c p ψ := by
  rw [mres, ← single_eq_C_mul_T, Finsupp.linearCombination_single]

/-- **The mixed residue becomes an ordinary residue** once the `(y − z)`-factor of the second
test function absorbs the pole of the first at `x = 0`. -/
theorem mres_eq_bres (c : V) (e : ℤ) (f : ℂ[X]) (K : ℕ) (Ψ : ℂ[T;T⁻¹]) (he : 0 ≤ e + K) :
    Bs.mres z c (T e * Polynomial.toLaurent f) (Polynomial.toLaurent (lz z ^ K) * Ψ)
      = Bs.bres c (Polynomial.toLaurent (lz z ^ (e + K).toNat *
          f.comp (Polynomial.X - Polynomial.C z)) * Ψ) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, mul_add, mres_add, hf, hg, Polynomial.add_comp, mul_add, map_add, add_mul,
      Bs.bres_add]
  | monomial j d =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, Polynomial.toLaurent_C, toLaurent_X_pow',
      show T e * (LC d * T (j : ℤ)) = LC d * T (e + j) by rw [T_add]; ring, mres_CT,
      mixRes_lz_pow, show e + j + K = (((e + K).toNat + j : ℕ) : ℤ) by push_cast; omega,
      mixRes_nonneg, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp]
    rw [show lz z ^ (e + K).toNat * (Polynomial.C d * (Polynomial.X - Polynomial.C z) ^ j)
        = Polynomial.C d * lz z ^ ((e + K).toNat + j) by rw [pow_add]; ring,
      map_mul, Polynomial.toLaurent_C, mul_assoc, ← smul_eq_C_mul, Bs.bres_smul]

/-- The opposite commutator formula, as a finite sum. -/
theorem opp_commutator (a b : V) (m q : ℤ) (w : M) {R : ℕ}
    (hR : ∀ i : ℕ, R ≤ i → W.smul a i b = 0) :
    Bs.B a m (Bs.B b q w) - Bs.B b q (Bs.B a m w)
      = -∑ i ∈ Finset.range R, cbz m i • Bs.B (W.smul a i b) (m + q - i) w := by
  have h := Bs.jacobi a b w 0 m q
  have h1 : negOnePow (0 : ℤ) = 1 := by simp [negOnePow]
  rw [finsum_eq_single _ 0 (fun i hi => by
    rcases lt_or_gt_of_ne hi with h' | h'
    · rw [cbz_apply_neg 0 h', mul_zero, zero_smul]
    · rw [cbz_lt (p := 0) (c := i) le_rfl h', mul_zero, zero_smul])] at h
  simp only [h1, cbz_zero, mul_one, one_smul, add_zero, zero_add, sub_zero, zero_sub] at h
  rw [← neg_sub, h, finsum_eq_sum_of_support_subset (s := (Finset.range R).map Nat.castEmbedding)]
  · rw [Finset.sum_map]; rfl
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_map, Nat.castEmbedding_apply, Finset.coe_range, Set.mem_image,
      Set.mem_Iio]
    rcases lt_or_ge i 0 with h' | h'
    · exact absurd (by rw [cbz_apply_neg m h', zero_smul]) hi
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j := ⟨i.toNat, by omega⟩
      refine ⟨j, ?_, rfl⟩
      by_contra hj
      exact hi (by rw [hR j (not_lt.mp hj), map_zero, Pi.zero_apply, LinearMap.zero_apply,
        smul_zero])

end OppBase

/-! ## The mixed commutator for an ordinary module -/

section Mixed

namespace OppBase

variable (Bs : OppBase W M) (S : Bs.Shift) (z : ℂ)

theorem tB_eq_mix (a : V) (p : ℤ) (y : M) :
    (Bs.tBase S (-z)).B a p y = Bs.mixOp z a p 0 y := by
  rw [tBase_B]
  refine finsum_congr fun k => ?_
  rw [OppBase.mixTerm, add_zero]

/-- **The mixed commutator** `[Y°(a, x + z)ₚ, Y°(b, y)_q] = − Σᵢ C(p,i) Mix(a₍ᵢ₎b, p − i, q)`. -/
theorem tB_comm (a b : V) (p q : ℤ) (w : M) {R : ℕ}
    (hR : ∀ i : ℕ, R ≤ i → W.smul a i b = 0) :
    (Bs.tBase S (-z)).B a p (Bs.B b q w)
        - Bs.B b q ((Bs.tBase S (-z)).B a p w)
      = -∑ i ∈ Finset.range R, cbz p i • Bs.mixOp z (W.smul a i b) (p - i) q w := by
  obtain ⟨K₁, h₁⟩ := Bs.mixTerm_eventually_zero z a p 0 (Bs.B b q w)
  obtain ⟨K₂, h₂⟩ := Bs.mixTerm_eventually_zero z a p 0 w
  choose K₃ h₃ using fun i : ℕ => Bs.mixTerm_eventually_zero z (W.smul a i b) (p - i) q w
  obtain ⟨K₄, hK₄⟩ := OppBase.exists_bound_range_nat R K₃
  set K := max K₁ (max K₂ K₄)
  rw [tB_eq_mix, tB_eq_mix, Bs.mixOp_eq_sum z a p 0 _ (K₀ := K)
      (fun k hk => h₁ k (by omega)),
    Bs.mixOp_eq_sum z a p 0 w (K₀ := K) (fun k hk => h₂ k (by omega)), map_sum,
    ← Finset.sum_sub_distrib]
  have hinner : ∀ k ∈ Finset.range K, Bs.mixTerm z a p 0 (Bs.B b q w) k
      - Bs.B b q (Bs.mixTerm z a p 0 w k)
      = -∑ i ∈ Finset.range R, (cbz p k * (-z) ^ k * cbz (p - k) i) •
          Bs.B (W.smul a i b) (p - k + q - i) w := by
    intro k _
    rw [OppBase.mixTerm, OppBase.mixTerm, map_smul, ← smul_sub, add_zero,
      Bs.opp_commutator a b (p - k) q w hR, smul_neg, Finset.smul_sum]
    simp only [smul_smul]
  rw [Finset.sum_congr rfl hinner, Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Bs.mixOp_eq_sum z (W.smul a i b) (p - i) q w (K₀ := K)
    (fun k hk => h₃ i k (le_trans (hK₄ i hi) (by omega))), Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [OppBase.mixTerm, smul_smul, show p - k + q - i = p - i + q - k by ring]
  congr 1
  rw [show cbz p k * (-z) ^ k * cbz (p - k) i = (cbz p k * cbz (p - k) i) * (-z) ^ k by ring,
    cbz_trinomial]
  ring

/-- The mixed commutator with test functions. -/
theorem tBres_comm (a b : V) (φ ψ : ℂ[T;T⁻¹]) (w : M) {R : ℕ}
    (hR : ∀ i : ℕ, R ≤ i → W.smul a i b = 0) :
    (Bs.tBase S (-z)).bres a φ (Bs.bres b ψ w)
        - Bs.bres b ψ ((Bs.tBase S (-z)).bres a φ w)
      = -∑ i ∈ Finset.range R, Bs.mres z (W.smul a i b) (dd i φ) ψ w := by
  induction φ using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    simp only [OppBase.bres_add, LinearMap.add_apply, map_add, OppBase.mres_add,
      Finset.sum_add_distrib, neg_add]
    rw [← hf, ← hg]; abel
  | C_mul_T p c =>
    induction ψ using LaurentPolynomial.induction_on' with
    | add f g hf hg =>
      simp only [OppBase.bres_add, LinearMap.add_apply, map_add, OppBase.mres_add_right,
        Finset.sum_add_distrib, neg_add]
      rw [← hf, ← hg]; abel
    | C_mul_T q d =>
      rw [OppBase.bres_CT, OppBase.bres_CT]
      simp only [LinearMap.smul_apply, map_smul, smul_smul]
      rw [mul_comm d c, ← smul_sub, tB_comm Bs S z a b p q w hR, smul_neg, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dd_CT, OppBase.mres_CT, OppBase.mixRes_CT, smul_smul, LinearMap.smul_apply,
        LinearMap.smul_apply, smul_smul]
      congr 1
      ring

/-- **`Y^L` and `Y^R` commute** on `D_{P(z)}(M)` (Li, Proposition 3.24). -/
theorem yL_yR_comm_gen (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a b : V)
    (m n : ℤ) :
    (Bs.tBase S (-z)).yR (-z) (neg_ne_zero.2 hz) a m (Bs.yR z hz b n α)
      = Bs.yR z hz b n ((Bs.tBase S (-z)).yR (-z) (neg_ne_zero.2 hz) a m α) := by
  set Ts := Bs.tBase S (-z)
  have hz' : -z ≠ 0 := neg_ne_zero.2 hz
  set β₁ := Bs.yR z hz b n α
  set β₂ := Ts.yR (-z) hz' a m α
  have hβ₁ : Bs.InD z β₁ := OppBase.inD_yR hz hα b n
  have hαT : Ts.InD (-z) α := (inD_iff_tBase Bs S α).1 hα
  have hβ₁T : Ts.InD (-z) β₁ := (inD_iff_tBase Bs S β₁).1 hβ₁
  have hβ₂T : Ts.InD (-z) β₂ := OppBase.inD_yR hz' hαT a m
  have hβ₂ : Bs.InD z β₂ := (inD_iff_tBase Bs S β₂).2 hβ₂T
  -- regularity bound for `a₍ᵢ₎b`
  obtain ⟨R₀, hR₀⟩ := W.regularity a b
  set R : ℕ := R₀.toNat
  have hR : ∀ i : ℕ, R ≤ i → W.smul a i b = 0 := fun i hi => hR₀ i (by omega)
  -- witnesses
  obtain ⟨kL₁, NL₁, hL₁⟩ := hαT a
  obtain ⟨kL₂, NL₂, hL₂⟩ := hβ₁T a
  obtain ⟨kR₁, NR₁, hR₁⟩ := hα b
  obtain ⟨kR₂, NR₂, hR₂⟩ := hβ₂ b
  choose ki Ni hWi using fun i : ℕ => hα (W.smul a i b)
  obtain ⟨B₁, hB₁⟩ := OppBase.exists_bound_range R (fun i => Ni i + i - n)
  obtain ⟨B₂, hB₂⟩ := OppBase.exists_bound_range_nat R (fun i => ki i + i)
  set KL : ℕ := max (max kL₁ kL₂) (max B₁.toNat R)
  set NL : ℤ := max NL₁ NL₂
  set KR : ℕ := max (max kR₁ kR₂) (B₂ + R + (-m).toNat)
  set NR : ℤ := max NR₁ NR₂
  have hKLR : R ≤ KL := le_trans (le_max_right _ _) (le_max_right _ _)
  have hKLB : B₁.toNat ≤ KL := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKRB : B₂ + R + (-m).toNat ≤ KR := le_max_right _ _
  have hmtn : -m ≤ ((-m).toNat : ℤ) := Int.self_le_toNat (-m)
  have hB₁t : B₁ ≤ (B₁.toNat : ℤ) := Int.self_le_toNat B₁
  have hWL₁ : Ts.Wit (-z) a α KL NL := hL₁.mono (by omega) (le_max_left _ _)
  have hWL₂ : Ts.Wit (-z) a β₁ KL NL := hL₂.mono (by omega) (le_max_right _ _)
  have hWR₁ : Bs.Wit z b α KR NR := hR₁.mono (by omega) (le_max_left _ _)
  have hWR₂ : Bs.Wit z b β₂ KR NR := hR₂.mono (by omega) (le_max_right _ _)
  obtain ⟨AL, BL, hABL⟩ := bezout hz' (NL - m).toNat KL
  obtain ⟨AR, BR, hABR⟩ := bezout hz (NR - n).toNat KR
  set φ := T m * Polynomial.toLaurent (BL * lz (-z) ^ KL)
  set ψ := T n * Polynomial.toLaurent (BR * lz z ^ KR)
  have e₁ : Ts.yR (-z) hz' a m β₁ = Ts.ys a φ β₁ :=
    OppBase.yR_eq hz' hWL₂ m _ (by omega) AL BL hABL
  have e₂ : β₂ = Ts.ys a φ α := OppBase.yR_eq hz' hWL₁ m _ (by omega) AL BL hABL
  have e₃ : β₁ = Bs.ys b ψ α := OppBase.yR_eq hz hWR₁ n _ (by omega) AR BR hABR
  have e₄ : Bs.yR z hz b n β₂ = Bs.ys b ψ β₂ := OppBase.yR_eq hz hWR₂ n _ (by omega) AR BR hABR
  rw [e₁, e₄]
  rw [e₂, e₃]
  ext w
  simp only [OppBase.ys_apply]
  rw [← sub_eq_zero, ← map_sub, ← neg_sub, map_neg, neg_eq_zero, tBres_comm Bs S z a b φ ψ w hR,
    map_neg, neg_eq_zero, map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  -- the `i`-th mixed residue is an ordinary residue killed by `α`
  obtain ⟨q', hq'⟩ := dd_ideal (z := -z) i m KL BL (by omega)
  have hφ : dd i φ = T (m - i) * Polynomial.toLaurent (lz (-z) ^ (KL - i) * q') := by
    rw [← hq', show φ = T m * Polynomial.toLaurent (lz (-z) ^ KL * BL) by
      simp only [φ]; rw [mul_comm BL]]
  have hψ : ψ = Polynomial.toLaurent (lz z ^ KR) * (T n * Polynomial.toLaurent BR) := by
    simp only [ψ, map_mul]; ring
  rw [hφ, hψ, OppBase.mres_eq_bres _ z _ _ _ _ _ (by omega)]
  have hcomp : (lz (-z) ^ (KL - i) * q').comp (Polynomial.X - Polynomial.C z)
      = Polynomial.X ^ (KL - i) * q'.comp (Polynomial.X - Polynomial.C z) := by
    simp only [lz, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp,
      Polynomial.X_comp, Polynomial.C_comp, map_neg, Polynomial.neg_comp]
    ring
  rw [hcomp]

  have hfinal : Polynomial.toLaurent (lz z ^ (m - i + KR).toNat *
        (Polynomial.X ^ (KL - i) * q'.comp (Polynomial.X - Polynomial.C z)))
          * (T n * Polynomial.toLaurent BR)
      = T (Ni i) * Polynomial.toLaurent (lz z ^ ki i * (Polynomial.X ^ (n + (KL - i) - Ni i).toNat
          * lz z ^ ((m - i + KR).toNat - ki i) * (q'.comp (Polynomial.X - Polynomial.C z) * BR))) := by
    have h1 : (T n : ℂ[T;T⁻¹]) * T ((KL - i : ℕ) : ℤ) = T (Ni i) * T ((n + (KL - i) - Ni i).toNat) := by
      rw [← T_add, ← T_add]; congr 1
      have := hB₁ i hi
      have : (B₁.toNat : ℤ) ≥ B₁ := Int.self_le_toNat B₁
      omega
    have h2 : lz z ^ (m - i + KR).toNat = lz z ^ ki i * lz z ^ ((m - i + KR).toNat - ki i) := by
      rw [← pow_add]; congr 1
      have := hB₂ i hi
      omega
    rw [h2]
    simp only [map_mul, toLaurent_X_pow']
    linear_combination (Polynomial.toLaurent (lz z ^ ki i) *
      Polynomial.toLaurent (lz z ^ ((m - i + KR).toNat - ki i)) *
      Polynomial.toLaurent (q'.comp (Polynomial.X - Polynomial.C z)) *
      Polynomial.toLaurent BR) * h1
  rw [hfinal]
  exact LinearMap.congr_fun (hWi i _) w

end OppBase

variable (N : OrdVModule W M) (z : ℂ)

theorem transB_eq_mix (a : V) (p : ℤ) (y : M) :
    (transBase N (-z)).B a p y = (oppBase N).mixOp z a p 0 y :=
  (oppBase N).tB_eq_mix (oppShift N) z a p y

/-- **`Y^L` and `Y^R` commute** on `D_{P(z)}(M)` (Li, Proposition 3.24). -/
theorem yL_yR_comm (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : (oppBase N).InD z α) (a b : V)
    (m n : ℤ) :
    (transBase N (-z)).yR (-z) (neg_ne_zero.2 hz) a m ((oppBase N).yR z hz b n α)
      = (oppBase N).yR z hz b n ((transBase N (-z)).yR (-z) (neg_ne_zero.2 hz) a m α) :=
  (oppBase N).yL_yR_comm_gen (oppShift N) z hz hα a b m n

end Mixed

end VOA.Huang.LiRegular
