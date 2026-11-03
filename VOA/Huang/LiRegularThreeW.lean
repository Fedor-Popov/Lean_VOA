import VOA.Huang.LiRegularComm

/-! # The three-way relation among `Y*`, `Y^R` and `Y^L` (Li, Proposition 3.22)

For `α ∈ D_{P(z)}(M)` and every state `a`, the residue theorem on `P¹` with the three
points `∞` (the base `Y*`), `0` (`Y^R`) and `z` (`Y^L`) and the test function
`(x − z)^l x^m` gives

  `Mix(a,l,m) α − Σᵢ C(l,i)(−z)^{l−i} Y^R(a)_{m+i} α = Σᵢ C(m,i) z^{m−i} Y^L(a)_{l+i} α`,

where `Mix(a,l,m) = Σᵢ C(l,i)(−z)ⁱ a°_{l+m−i}` is the expansion at `∞` (`OppBase.mixOp`).

* `trunc_binom_dvd` — the truncated-binomial congruence;
* `OppBase.boundary_gen` (generic), `boundary_R` (`l = 0`), `boundary_M` (`m = 0`);
* `sumR_pascal`, `pascal_vanish_z` — Pascal propagation with scale `z`;
* `OppBase.threeWay_gen` — the full relation for every opposite base with a translation
  datum (in particular `oppBase N`, and the translated bases used in `LiConverseFinal`).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiConverse LaurentPolynomial
open scoped BigOperators Polynomial

universe u

/-- The truncated binomial expansion `Σ_{i<I} C(l,i) c^{l−i} Yⁱ` of `(Y + c)^l` at `Y = 0`. -/
noncomputable def truncBinom (l : ℤ) (c : ℂ) (I : ℕ) : ℂ[X] :=
  ∑ i ∈ Finset.range I, Polynomial.C (cbz l i * c ^ (l - i)) * Polynomial.X ^ i

/-- **The truncated binomial congruence**: `(Y+c)^s · trunc((Y+c)^l) ≡ (Y+c)^{s+l}`
modulo `Y^I`, for `s + l ≥ 0`. -/
theorem trunc_binom_dvd {c : ℂ} (hc : c ≠ 0) (l : ℤ) (s : ℕ) (hsl : 0 ≤ (s : ℤ) + l) (I : ℕ) :
    (Polynomial.X : ℂ[X]) ^ I ∣ (Polynomial.X + Polynomial.C c) ^ s * truncBinom l c I
      - (Polynomial.X + Polynomial.C c) ^ ((s : ℤ) + l).toNat := by
  rw [Polynomial.X_pow_dvd_iff]
  intro t ht
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_C_pow, truncBinom, Finset.mul_sum,
    Polynomial.finset_sum_coeff, sub_eq_zero]
  set n₀ : ℕ := ((s : ℤ) + l).toNat
  have hn₀ : (n₀ : ℤ) = s + l := Int.toNat_of_nonneg hsl
  -- coefficient of each summand, in a uniform `zpow` form
  have hterm : ∀ i ∈ Finset.range I, ((Polynomial.X + Polynomial.C c) ^ s *
      (Polynomial.C (cbz l i * c ^ (l - i)) * Polynomial.X ^ i)).coeff t
      = if i ≤ t then c ^ ((n₀ : ℤ) - t) * (cbz l i * cbz (s : ℤ) ((t : ℤ) - i)) else 0 := by
    intro i _
    have e : (Polynomial.X + Polynomial.C c) ^ s *
        (Polynomial.C (cbz l i * c ^ (l - i)) * Polynomial.X ^ i)
        = Polynomial.C (cbz l i * c ^ (l - i)) * ((Polynomial.X + Polynomial.C c) ^ s *
          Polynomial.X ^ i) := by ring
    rw [e, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    split_ifs with hit
    · rw [Polynomial.coeff_X_add_C_pow]
      rcases le_or_gt (t - i) s with hts | hts
      · rw [show ((t : ℤ) - i) = ((t - i : ℕ) : ℤ) by omega, cbz_natCast_eq_choose hts]
        have hp : c ^ (l - i) * c ^ (s - (t - i)) = c ^ ((n₀ : ℤ) - t) := by
          rw [← zpow_natCast c (s - (t - i)), ← zpow_add₀ hc]
          congr 1; push_cast [Nat.cast_sub hts, Nat.cast_sub hit]; omega
        rw [← hp]; ring
      · rw [Nat.choose_eq_zero_of_lt hts, show ((t : ℤ) - i) = ((t - i : ℕ) : ℤ) by omega,
          cbz_lt (p := (s : ℤ)) (c := ((t - i : ℕ) : ℤ)) (by positivity) (by omega)]
        simp
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_range_add_sum_Ico _ (show t + 1 ≤ I by omega),
    Finset.sum_eq_zero (s := Finset.Ico (t + 1) I) (fun i hi => by
      rw [Finset.mem_Ico] at hi; rw [if_neg (by omega)]), add_zero,
    Finset.sum_congr rfl (fun i hi => if_pos (by rw [Finset.mem_range] at hi; omega)),
    ← Finset.mul_sum, vandermonde_range]
  rcases le_or_gt t n₀ with htn | htn
  · rw [show l + (s : ℤ) = ((n₀ : ℕ) : ℤ) by omega, cbz_natCast_eq_choose htn,
      ← zpow_natCast c (n₀ - t), show ((n₀ : ℤ) - t) = ((n₀ - t : ℕ) : ℤ) by omega]
  · rw [Nat.choose_eq_zero_of_lt htn, cbz_lt (p := l + s) (c := (t : ℤ)) (by omega) (by omega)]
    simp

/-- Divisibility by `X^N (X − z)^k` from separate divisibility (coprimality). -/
theorem dvd_X_pow_lz_pow {z : ℂ} (hz : z ≠ 0) {N k : ℕ} {Q : ℂ[X]}
    (hX : (Polynomial.X : ℂ[X]) ^ N ∣ Q) (hL : lz z ^ k ∣ Q) :
    ∃ q : ℂ[X], Q = Polynomial.X ^ N * (lz z ^ k * q) := by
  obtain ⟨q, hq⟩ := (isCoprime_X_pow_lz_pow hz N k).mul_dvd hX hL
  exact ⟨q, by rw [hq]; ring⟩

/-- `(X − z)^k ∣ X^s Q ⟹ (X − z)^k ∣ Q`. -/
theorem lz_pow_dvd_of_X_pow_mul {z : ℂ} (hz : z ≠ 0) {k s : ℕ} {Q : ℂ[X]}
    (h : lz z ^ k ∣ Polynomial.X ^ s * Q) : lz z ^ k ∣ Q :=
  ((isCoprime_X_pow_lz_pow hz s k).symm).dvd_of_dvd_mul_left h

/-- `X^N ∣ (X − z)^s Q ⟹ X^N ∣ Q`. -/
theorem X_pow_dvd_of_lz_pow_mul {z : ℂ} (hz : z ≠ 0) {N s : ℕ} {Q : ℂ[X]}
    (h : (Polynomial.X : ℂ[X]) ^ N ∣ lz z ^ s * Q) : Polynomial.X ^ N ∣ Q :=
  (isCoprime_X_pow_lz_pow hz N s).dvd_of_dvd_mul_left h

namespace OppBase

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

theorem ys_T_eq (Bs : OppBase W M) (a : V) (n : ℤ) (α : Module.Dual ℂ M) :
    Bs.ys a (T n) α = (Bs.B a n).dualMap α := by
  ext w; simp [Bs.bres_T]

/-- A polynomial divisible by `X^N (X − z)^k` is killed by a `(k,N)`-witnessed functional. -/
theorem ys_poly_eq_zero (Bs : OppBase W M) {z : ℂ} {a : V} {α : Module.Dual ℂ M} {k N : ℕ}
    (hW : Bs.Wit z a α k N) {Q : ℂ[X]} (hQ : ∃ q : ℂ[X], Q = Polynomial.X ^ N * (lz z ^ k * q)) :
    Bs.ys a (Polynomial.toLaurent Q) α = 0 := by
  obtain ⟨q, rfl⟩ := hQ
  rw [map_mul, toLaurent_X_pow']
  exact hW q

end OppBase

section Boundary

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M)

theorem lz_neg_comp (z : ℂ) : (lz (-z)).comp (Polynomial.X - Polynomial.C z) = Polynomial.X := by
  simp [lz]

/-- **The boundary relation, generic form**: for two opposite mode systems related by the
translation `y ↦ y − z` on polynomial test functions,
`B₁*(a)_m α − Y^R_{B₁}(a)_m α = Σᵢ C(m,i) z^{m−i} Y^R_{B₂}(a)_i α`. -/
theorem OppBase.boundary_gen (Bs Ts : OppBase W M) {z : ℂ} (hz : z ≠ 0) {α : Module.Dual ℂ M}
    (hα : Bs.InD z α) (hαT : Ts.InD (-z) α)
    (htr : ∀ (a : V) (p : ℂ[X]), Ts.ys a (Polynomial.toLaurent p) α
      = Bs.ys a (Polynomial.toLaurent (p.comp (Polynomial.X - Polynomial.C z))) α)
    (a : V) (m : ℤ) :
    Bs.ys a (T m) α - Bs.yR z hz a m α
      = ∑ᶠ i : ℕ, (cbz m i * z ^ (m - i)) • Ts.yR (-z) (neg_ne_zero.2 hz) a i α := by
  have hz' : -z ≠ 0 := neg_ne_zero.2 hz
  obtain ⟨kR, NR₀, hWR₀⟩ := hα a
  obtain ⟨kL, NL₀, hWL₀⟩ := hαT a
  set NR : ℕ := NR₀.toNat
  set NL : ℕ := NL₀.toNat
  have hWR : Bs.Wit z a α kR NR := hWR₀.mono le_rfl (Int.self_le_toNat _)
  have hWL : Ts.Wit (-z) a α kL NL := hWL₀.mono le_rfl (Int.self_le_toNat _)
  set I : ℕ := max NL kR
  -- the finsum is a finite sum
  have hfin : ∑ᶠ i : ℕ, (cbz m i * z ^ (m - i)) • Ts.yR (-z) hz' a i α
      = ∑ i ∈ Finset.range I, (cbz m i * z ^ (m - i)) • Ts.yR (-z) hz' a i α := by
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hi (by rw [OppBase.yR_trunc hz' hWL (by simp only [I] at h; push_cast; omega), smul_zero])
  rw [hfin]
  -- regularized modes as `Y*`-residues
  set LR : ℕ := ((NR : ℤ) - m).toNat + (-m).toNat
  obtain ⟨AR, BR, hABR⟩ := bezout hz LR kR
  have hR : Bs.yR z hz a m α = Bs.ys a (T m * Polynomial.toLaurent (BR * lz z ^ kR)) α :=
    OppBase.yR_eq hz hWR m LR (by simp only [LR]; omega) AR BR hABR
  set KL : ℕ := max kL NR
  set LL : ℕ := max NL kR
  obtain ⟨AL, BL, hABL⟩ := bezout hz' LL KL
  have hL : ∀ i : ℕ, Ts.yR (-z) hz' a i α
      = Bs.ys a (Polynomial.toLaurent ((Polynomial.X ^ i * (BL * lz (-z) ^ KL)).comp
          (Polynomial.X - Polynomial.C z))) α := by
    intro i
    rw [OppBase.yR_eq hz' (hWL.mono (le_max_left _ _) le_rfl) i LL (by simp only [LL]; omega)
      AL BL hABL, show (T (i : ℤ) : ℂ[T;T⁻¹]) = T ((i : ℕ) : ℤ) from rfl, T_mul_toLaurent_nat,
      htr]
  simp only [hL]
  -- both sides are single `Y*`-residues of polynomials
  set s : ℕ := (-m).toNat
  set P : ℂ[X] := (truncBinom m z I).comp (Polynomial.X - Polynomial.C z)
  have hmLR : 0 ≤ m + LR := by simp only [LR]; omega
  have hLHS : Bs.ys a (T m) α - Bs.ys a (T m * Polynomial.toLaurent (BR * lz z ^ kR)) α
      = Bs.ys a (Polynomial.toLaurent (Polynomial.X ^ (m + LR).toNat * AR)) α := by
    rw [← OppBase.ys_sub, show BR * lz z ^ kR = 1 - AR * Polynomial.X ^ LR by
      linear_combination hABR]
    congr 1
    rw [map_mul, toLaurent_X_pow', map_sub, map_one, map_mul, toLaurent_X_pow',
      Int.toNat_of_nonneg hmLR, T_add]
    ring
  have hRHS : ∑ i ∈ Finset.range I, (cbz m i * z ^ (m - i)) •
      Bs.ys a (Polynomial.toLaurent ((Polynomial.X ^ i * (BL * lz (-z) ^ KL)).comp
        (Polynomial.X - Polynomial.C z))) α
      = Bs.ys a (Polynomial.toLaurent (P * (BL.comp (Polynomial.X - Polynomial.C z) *
          Polynomial.X ^ KL))) α := by
    rw [show P * (BL.comp (Polynomial.X - Polynomial.C z) * Polynomial.X ^ KL)
        = ∑ i ∈ Finset.range I, Polynomial.C (cbz m i * z ^ (m - i)) *
          (Polynomial.X ^ i * (BL * lz (-z) ^ KL)).comp (Polynomial.X - Polynomial.C z) by
      simp only [P, truncBinom, Polynomial.sum_comp, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
        lz_neg_comp]
      ring]
    rw [map_sum, OppBase.ys_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Polynomial.toLaurent_C, ← smul_eq_C_mul, OppBase.ys_smul]
  rw [hR, hLHS, hRHS, ← sub_eq_zero, ← OppBase.ys_sub, ← map_sub]
  -- the difference is divisible by `X^NR (X − z)^kR`
  apply OppBase.ys_poly_eq_zero Bs hWR
  apply dvd_X_pow_lz_pow hz
  · refine dvd_sub ?_ ?_
    · exact (pow_dvd_pow _ (by simp only [LR]; omega)).mul_right _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
        (pow_dvd_pow Polynomial.X (show NR ≤ KL from le_max_right _ _)) _) _
  · apply lz_pow_dvd_of_X_pow_mul hz (s := s)
    -- composed Bézout identities
    have hBL : BL.comp (Polynomial.X - Polynomial.C z) * Polynomial.X ^ KL
        = 1 - AL.comp (Polynomial.X - Polynomial.C z) * lz z ^ LL := by
      have := congrArg (fun p : ℂ[X] => p.comp (Polynomial.X - Polynomial.C z)) hABL
      simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
        Polynomial.X_comp, lz_neg_comp, Polynomial.one_comp] at this
      simp only [lz]; linear_combination this
    have hXLR : Polynomial.X ^ s * (Polynomial.X ^ (m + LR).toNat * AR)
        = Polynomial.X ^ (s + m).toNat * (1 - BR * lz z ^ kR) := by
      rw [show BR * lz z ^ kR = 1 - AR * Polynomial.X ^ LR by linear_combination hABR,
        sub_sub_cancel, ← mul_assoc, ← pow_add, show s + (m + LR).toNat = ((s : ℤ) + m).toNat + LR by
          simp only [s, LR]; omega, pow_add]
      ring
    obtain ⟨d, hd⟩ := trunc_binom_dvd hz m s (by simp only [s]; omega) I
    have hd' := congrArg (fun p : ℂ[X] => p.comp (Polynomial.X - Polynomial.C z)) hd
    simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, sub_add_cancel] at hd'
    rw [mul_sub, hXLR, ← mul_assoc, hBL]
    have hsplit : Polynomial.X ^ (s + m).toNat * (1 - BR * lz z ^ kR)
        - Polynomial.X ^ s * P * (1 - AL.comp (Polynomial.X - Polynomial.C z) * lz z ^ LL)
        = -((Polynomial.X ^ s * P - Polynomial.X ^ (s + m).toNat))
          - Polynomial.X ^ (s + m).toNat * BR * lz z ^ kR
          + Polynomial.X ^ s * P * AL.comp (Polynomial.X - Polynomial.C z) * lz z ^ LL := by ring
    rw [hsplit]
    refine dvd_add (dvd_sub (dvd_neg.2 ?_) ?_) ?_
    · rw [show Polynomial.X ^ s * P - Polynomial.X ^ (s + m).toNat
          = ((Polynomial.X + Polynomial.C z) ^ s * truncBinom m z I
            - (Polynomial.X + Polynomial.C z) ^ ((s : ℤ) + m).toNat).comp
              (Polynomial.X - Polynomial.C z) by
          simp only [P, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp,
            Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, sub_add_cancel]]
      rw [hd, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
      exact (pow_dvd_pow _ (le_max_right _ _)).mul_right _
    · exact (dvd_mul_left _ _)
    · exact (pow_dvd_pow _ (le_max_right _ _)).mul_left _

namespace OppBase

variable (Bs : OppBase W M) (S : Bs.Shift)

/-- **Boundary `l = 0` of the three-way relation**:
`Y*(a)_m α − Y^R(a)_m α = Σᵢ C(m,i) z^{m−i} Y^L(a)_i α`. -/
theorem boundary_R_gen {z : ℂ} (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α)
    (a : V) (m : ℤ) :
    Bs.ys a (T m) α - Bs.yR z hz a m α
      = ∑ᶠ i : ℕ, (cbz m i * z ^ (m - i)) •
          (Bs.tBase S (-z)).yR (-z) (neg_ne_zero.2 hz) a i α :=
  OppBase.boundary_gen _ _ hz hα ((inD_iff_tBase Bs S α).1 hα)
    (fun a p => by rw [ys_tBase_poly, map_neg, ← sub_eq_add_neg]) a m

theorem yR_congr {w z : ℂ} (h : w = z) (hw : w ≠ 0) (hz : z ≠ 0) :
    Bs.yR w hw = Bs.yR z hz := by subst h; rfl

/-- **Boundary `m = 0` of the three-way relation**:
`Y*_{(z)}(a)_l α − Σᵢ C(l,i)(−z)^{l−i} Y^R(a)_i α = Y^L(a)_l α`, where `Y*_{(z)}` is the
transposed translated base. -/
theorem boundary_M_gen {z : ℂ} (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α)
    (a : V) (l : ℤ) :
    (Bs.tBase S (-z)).ys a (T l) α
      - ∑ᶠ i : ℕ, (cbz l i * (-z) ^ (l - i)) • Bs.yR z hz a i α
      = (Bs.tBase S (-z)).yR (-z) (neg_ne_zero.2 hz) a l α := by
  have hz' : -z ≠ 0 := neg_ne_zero.2 hz
  have h := OppBase.boundary_gen (Bs.tBase S (-z)) Bs hz' ((inD_iff_tBase Bs S α).1 hα)
    (by rw [neg_neg]; exact hα) (fun a p => by
      rw [ys_tBase_poly, Polynomial.comp_assoc]
      congr 3
      simp [sub_eq_add_neg]) a l
  rw [Bs.yR_congr (neg_neg z) _ hz] at h
  rw [← h]; abel

end OppBase

theorem boundary_R {z : ℂ} (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : (oppBase N).InD z α)
    (a : V) (m : ℤ) :
    (oppBase N).ys a (T m) α - (oppBase N).yR z hz a m α
      = ∑ᶠ i : ℕ, (cbz m i * z ^ (m - i)) •
          (transBase N (-z)).yR (-z) (neg_ne_zero.2 hz) a i α :=
  (oppBase N).boundary_R_gen (oppShift N) hz hα a m

theorem boundary_M {z : ℂ} (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : (oppBase N).InD z α)
    (a : V) (l : ℤ) :
    (transBase N (-z)).ys a (T l) α
      - ∑ᶠ i : ℕ, (cbz l i * (-z) ^ (l - i)) • (oppBase N).yR z hz a i α
      = (transBase N (-z)).yR (-z) (neg_ne_zero.2 hz) a l α :=
  (oppBase N).boundary_M_gen (oppShift N) hz hα a l

end Boundary


/-! ## Pascal propagation and the full three-way relation -/

section Pascal

variable {G : Type*} [AddCommGroup G] [Module ℂ G]

/-- The binomially weighted sum `Σᵢ C(l,i) c^{l−i} r(m+i)`. -/
noncomputable def sumR (c : ℂ) (r : ℤ → G) (l m : ℤ) : G :=
  ∑ᶠ i : ℕ, (cbz l i * c ^ (l - i)) • r (m + i)

theorem sumR_eq (c : ℂ) (r : ℤ → G) {K : ℤ} (hr : ∀ n, K ≤ n → r n = 0) (l m : ℤ) (J : ℕ)
    (hJ : K ≤ m + J) :
    sumR c r l m = ∑ i ∈ Finset.range J, (cbz l i * c ^ (l - i)) • r (m + i) := by
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  rw [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hi (by rw [hr _ (by omega), smul_zero])

/-- Pascal's rule for `sumR`. -/
theorem sumR_pascal {c : ℂ} (hc : c ≠ 0) (r : ℤ → G) {K : ℤ} (hr : ∀ n, K ≤ n → r n = 0)
    (l m : ℤ) : sumR c r (l + 1) m = c • sumR c r l m + sumR c r l (m + 1) := by
  set J := (K - m).toNat
  rw [sumR_eq c r hr (l + 1) m (J + 1) (by omega), sumR_eq c r hr l m (J + 1) (by omega),
    sumR_eq c r hr l (m + 1) J (by omega), Finset.smul_sum]
  simp only [cbz_pascal_up l, add_mul, add_smul, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, show l + 1 - (i : ℤ) = (l - i) + 1 by ring, zpow_add_one₀ hc]
    congr 1; ring
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_sub, cbz_apply_neg l (show (-1 : ℤ) < 0 by norm_num),
      zero_mul, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) by push_cast; ring,
      show l + 1 - ((i + 1 : ℕ) : ℤ) = l - i by push_cast; ring,
      show m + ((i + 1 : ℕ) : ℤ) = m + 1 + i by push_cast; ring]

theorem sumR_zero_left (c : ℂ) (r : ℤ → G) (m : ℤ) : sumR c r 0 m = r m := by
  rw [sumR, finsum_eq_single _ 0 (fun i hi => by
    rw [cbz_lt (p := 0) (c := (i : ℤ)) le_rfl (by omega), zero_mul, zero_smul])]
  simp

/-- Pascal propagation with a scale `z`: vanishing on both axes propagates everywhere. -/
theorem pascal_vanish_z {z : ℂ} (hz : z ≠ 0) (f : ℤ → ℤ → G)
    (hrec : ∀ l m, f (l + 1) m = f l (m + 1) - z • f l m)
    (h0 : ∀ m, f 0 m = 0) (hm : ∀ l, f l 0 = 0) : ∀ l m, f l m = 0 := by
  have hpos : ∀ n : ℕ, ∀ m, f n m = 0 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => intro m; push_cast; rw [hrec, ih, ih, smul_zero, sub_zero]
  have hneg : ∀ n : ℕ, ∀ m, f (-(n : ℤ)) m = 0 := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have hstep : ∀ m, f (-((n + 1 : ℕ) : ℤ)) (m + 1) = z • f (-((n + 1 : ℕ) : ℤ)) m := by
        intro m
        have := hrec (-((n + 1 : ℕ) : ℤ)) m
        rw [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring, ih] at this
        exact sub_eq_zero.1 this.symm
      intro m
      induction m using Int.induction_on with
      | zero => exact hm _
      | succ k ihk => rw [hstep, ihk, smul_zero]
      | pred k ihk =>
        have := hstep (-(k : ℤ) - 1)
        rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring, ihk, eq_comm, smul_eq_zero] at this
        exact this.resolve_left hz
  intro l m
  rcases le_or_gt 0 l with hl | hl
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, l = n := ⟨l.toNat, (Int.toNat_of_nonneg hl).symm⟩
    exact hpos n m
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, l = -(n : ℤ) := ⟨(-l).toNat, by omega⟩
    exact hneg n m

end Pascal

section ThreeWay

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

namespace OppBase

variable (Bs : OppBase W M) (S : Bs.Shift)

/-- The right regularized modes `n ↦ Y^R(a)_n α`. -/
noncomputable def rModes {z : ℂ} (hz : z ≠ 0) (a : V) (α : Module.Dual ℂ M) (n : ℤ) :
    Module.Dual ℂ M :=
  Bs.yR z hz a n α

/-- The left regularized modes `n ↦ Y^L(a)_n α`. -/
noncomputable def lModes {z : ℂ} (hz : z ≠ 0) (a : V) (α : Module.Dual ℂ M) (n : ℤ) :
    Module.Dual ℂ M :=
  (Bs.tBase S (-z)).yR (-z) (neg_ne_zero.2 hz) a n α

theorem rModes_trunc {z : ℂ} (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α)
    (a : V) : ∃ K : ℤ, ∀ n, K ≤ n → Bs.rModes hz a α n = 0 := by
  obtain ⟨k, K, hW⟩ := hα a
  exact ⟨K, fun n hn => OppBase.yR_trunc hz hW hn⟩

theorem lModes_trunc {z : ℂ} (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α)
    (a : V) : ∃ K : ℤ, ∀ n, K ≤ n → Bs.lModes S hz a α n = 0 := by
  obtain ⟨k, K, hW⟩ := ((inD_iff_tBase Bs S α).1 hα) a
  exact ⟨K, fun n hn => OppBase.yR_trunc _ hW hn⟩

/-- **The three-way relation** (Li, math/9909007, Proposition 3.22; the component form of
the `P(z)`-Jacobi identity on `D_{P(z)}(M)`): for all `l, m ∈ ℤ`,

  `Mix(a,l,m)* α − Σᵢ C(l,i)(−z)^{l−i} Y^R(a)_{m+i} α = Σᵢ C(m,i) z^{m−i} Y^L(a)_{l+i} α`. -/
theorem threeWay_gen {z : ℂ} (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α)
    (a : V) (l m : ℤ) :
    (Bs.mixOp z a l m).dualMap α - sumR (-z) (Bs.rModes hz a α) l m
      = sumR z (Bs.lModes S hz a α) m l := by
  obtain ⟨KR, hKR⟩ := Bs.rModes_trunc hz hα a
  obtain ⟨KL, hKL⟩ := Bs.lModes_trunc S hz hα a
  let f : ℤ → ℤ → Module.Dual ℂ M := fun l m =>
    (Bs.mixOp z a l m).dualMap α - sumR (-z) (Bs.rModes hz a α) l m
      - sumR z (Bs.lModes S hz a α) m l
  suffices h : ∀ l m, f l m = 0 from sub_eq_zero.1 (h l m)
  refine pascal_vanish_z hz f (fun l m => ?_) (fun m => ?_) (fun l => ?_)
  · have hM : (Bs.mixOp z a (l + 1) m).dualMap α
        = (Bs.mixOp z a l (m + 1)).dualMap α
          - z • (Bs.mixOp z a l m).dualMap α := by
      ext w
      simp only [LinearMap.dualMap_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        ← OppBase.mixOp_pascal, map_sub, map_smul, smul_eq_mul]
    have hR := sumR_pascal (neg_ne_zero.2 hz) (Bs.rModes hz a α) hKR l m
    have hL := sumR_pascal hz (Bs.lModes S hz a α) hKL m l
    simp only [f]
    rw [hM, hR, eq_sub_of_add_eq' hL.symm]
    simp only [smul_sub, neg_smul]
    abel
  · simp only [f]
    rw [OppBase.mixOp_zero_p, sumR_zero_left, sumR, sub_eq_zero]
    have h := Bs.boundary_R_gen S hz hα a m
    rw [OppBase.ys_T_eq] at h
    simp only [rModes, lModes, zero_add]
    exact h
  · simp only [f]
    rw [sumR_zero_left, sumR, sub_eq_zero]
    have h := Bs.boundary_M_gen S hz hα a l
    have hT : (Bs.mixOp z a l 0).dualMap α = (Bs.tBase S (-z)).ys a (T l) α := by
      ext w
      simp [Bs.tB_eq_mix S, OppBase.bres_T]
    rw [hT]
    simp only [rModes, lModes, zero_add]
    exact h

end OppBase

end ThreeWay

end VOA.Huang.LiRegular
