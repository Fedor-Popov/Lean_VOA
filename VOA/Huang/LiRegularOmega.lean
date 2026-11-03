import VOA.Huang.LiRegularComm
import VOA.Huang.LiConverseZhuLaws

/-! # Functionals vanishing on `O(M)` are lowest-weight vectors of the regular representation

Li, *The regular representation, Zhu's A(V)-theory and induced modules* (math/9909007),
Proposition 3.8 and Theorem 3.9, at `z = −1` (where `O(M, −1)` is Frenkel–Zhu's `O(M)`).
For a functional `λ` on an ordinary module `M` with `λ(O(M)) = 0`:

* `inD_of_perp` — `λ ∈ D_{P(−1)}(M)`;
* `yR_lower_of_perp` — `Y^R(v)ₙ λ = 0` for `n ≥ wt v` (`λ ∈ Ω` for `Y^R`), and
  `yR_zero_of_perp` — `Y^R(v)_{wt v − 1} λ = λ(θ(v) ∗ ·)` with the Frenkel–Zhu left action and
  `θ(v) = (−1)^{wt v} e^{L(1)} v`.

The opposite modes are rewritten as residues of the module vertex operator with twisted
states (`oppBase_bres_eq`), and every higher-order term is a Frenkel–Zhu generator of
`O(M)` (`gen_mem_good`).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiConverse VOA.FZ LaurentPolynomial
open scoped BigOperators Polynomial

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

section Omega

variable (N : OrdVModule W M)

/-- The opposite residue as a sum of twisted module residues (inverted test function). -/
theorem oppBase_bres_eq {wt : ℤ} {v : V} (hv : v ∈ W.grading wt) (φ : ℂ[T;T⁻¹]) (w : M) :
    (oppBase N).bres v φ w = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
      ((j.factorial : ℂ)⁻¹) •
        LiConverse.res N.toWeakModule ((W.L 1 ^ j) v) w (T (2 * wt - 2 - j) * invert φ) := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [OppBase.bres_add, LinearMap.add_apply, hp, hq, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, mul_add, map_add, smul_add]
  | C_mul_T s c =>
    rw [OppBase.bres_CT, LinearMap.smul_apply]
    change c • oppB N v s w = _
    rw [oppB_homog N hv, LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, smul_smul,
      Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : T (2 * wt - 2 - (j : ℤ)) * invert (LaurentPolynomial.C c * T s)
        = LaurentPolynomial.C c * T (2 * wt - s - 2 - (j : ℤ)) := by
      rw [map_mul, invert_C, invert_T, ← mul_assoc, mul_comm (T _) (LaurentPolynomial.C c),
        mul_assoc, ← T_add]
      congr 2; ring
    rw [e, res_CT, LinearMap.smul_apply]
    simp only [smul_smul]
    congr 1
    ring

/-- A generator family of `good r`. -/
theorem T_mul_pow_mem_good (r : ℕ) (K : ℕ) (hK : r ≤ K) (e : ℤ) (he : e ≤ -2 - ((K - r : ℕ) : ℤ)) :
    T e * (1 + z) ^ K ∈ good N.toWeakModule (r : ℤ) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, e = -2 - (((K - r) + d : ℕ) : ℤ) := ⟨(-2 - (K - r : ℕ) - e).toNat,
    by push_cast; omega⟩
  have h := gen_mem_good N.toWeakModule r d (K - r)
  rw [show r + (K - r) = K by omega] at h
  rw [hd, mul_comm]
  exact h

theorem invert_one_add_pow (K : ℕ) :
    invert (Polynomial.toLaurent (lz (-1) ^ K)) = T (-(K : ℤ)) * (1 + z) ^ K := by
  have h1 : Polynomial.toLaurent (lz (-1)) = T 1 + 1 := by
    rw [lz, map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C, map_neg, map_one,
      sub_neg_eq_add]
  rw [map_pow, map_pow, h1, map_add, invert_T, map_one,
    show (T (-(K : ℤ)) : ℂ[T;T⁻¹]) = T (-1) ^ K by rw [T_pow]; congr 1; ring, ← mul_pow]
  congr 1
  rw [mul_add, mul_one, ← T_add]; simp

/-- The test functions of `Y^R`-modes with `n ≥ wt v` are Frenkel–Zhu generators. -/
theorem test_mem_good (w₀ j : ℕ) (hj : j ≤ w₀) (n : ℤ) (hn : (w₀ : ℤ) ≤ n) (K : ℕ)
    (hK : w₀ ≤ K) (B : ℂ[X]) :
    T (2 * (w₀ : ℤ) - 2 - j - n - K) * (1 + z) ^ K * invert (Polynomial.toLaurent B)
      ∈ good N.toWeakModule ((w₀ - j : ℕ) : ℤ) := by
  induction B using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, mul_add]; exact Submodule.add_mem _ hp hq
  | monomial s b =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, Polynomial.toLaurent_C, toLaurent_X_pow',
      map_mul, invert_C, invert_T]
    have h := T_mul_pow_mem_good N (w₀ - j) K (by omega) (2 * (w₀ : ℤ) - 2 - j - n - K - s)
      (by push_cast [Nat.cast_sub (show j ≤ w₀ by omega), Nat.cast_sub (show w₀ - j ≤ K by omega)]
          omega)
    rw [show T (2 * (w₀ : ℤ) - 2 - j - n - K) * (1 + z) ^ K * (LC b * T (-(s : ℤ)))
      = b • (T (2 * (w₀ : ℤ) - 2 - j - n - K - s) * (1 + z) ^ K) by
        rw [smul_eq_C_mul, sub_eq_add_neg _ (s : ℤ), T_add]; ring]
    exact Submodule.smul_mem _ b h

variable {N}

/-- `Y^R`-type residues of a functional vanishing on `O(M)`. -/
theorem perp_bres_zero {lam : Module.Dual ℂ M}
    (hlam : ∀ x ∈ fzO N.toWeakModule, lam x = 0) {w₀ : ℕ} {v : V}
    (hv : v ∈ W.grading (w₀ : ℤ)) {n : ℤ} (hn : (w₀ : ℤ) ≤ n) {K : ℕ} (hK : w₀ ≤ K) (B : ℂ[X])
    (w : M) :
    lam ((oppBase N).bres v (T n * Polynomial.toLaurent (B * lz (-1) ^ K)) w) = 0 := by
  rw [oppBase_bres_eq N hv, map_smul, map_sum]
  refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun j hj => ?_)
  rw [Finset.mem_range, Int.toNat_natCast] at hj
  rw [map_smul]
  refine smul_eq_zero_of_right _ (hlam _ ?_)
  have hcast : ((w₀ : ℤ) - j) = ((w₀ - j : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : j ≤ w₀)]; ring
  have hstate : (W.L 1 ^ j) v ∈ W.grading ((w₀ - j : ℕ) : ℤ) := by
    have := L_one_pow_mem W hv j
    rwa [hcast] at this
  refine test_mem_good N w₀ j (by omega) n hn K hK B _ hstate w |> fun h => ?_
  convert h using 2
  rw [map_mul, map_mul, map_mul, invert_T, invert_one_add_pow]
  rw [show (2 * (w₀ : ℤ) - 2 - j - n - K) = (2 * (w₀ : ℤ) - 2 - j) + -n + -(K : ℤ) by ring,
    T_add, T_add]
  ring

theorem neg_one_ne_zero' : (-1 : ℂ) ≠ 0 := by norm_num

/-- **Functionals vanishing on `O(M)` are `P(−1)`-linear** (Li, Proposition 3.8). -/
theorem inD_of_perp {lam : Module.Dual ℂ M} (hlam : ∀ x ∈ fzO N.toWeakModule, lam x = 0) :
    (oppBase N).InD (-1) lam := by
  intro a
  refine reduce_homogeneous W (P := fun a => ∃ (k : ℕ) (N₀ : ℤ), (oppBase N).Wit (-1) a lam k N₀)
    ?_ ⟨0, 0, fun q => by ext w; simp [OppBase.bres_zero_a]⟩ ?_ a
  · intro wt v hv
    rcases lt_or_ge wt 0 with hw | hw
    · have hv0 : v = 0 := by
        have := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W hv (j := 0) (by omega)
        simpa using this
      subst hv0
      exact ⟨0, 0, fun q => by ext w; simp [OppBase.bres_zero_a]⟩
    obtain ⟨w₀, rfl⟩ : ∃ w₀ : ℕ, wt = w₀ := ⟨wt.toNat, (Int.toNat_of_nonneg hw).symm⟩
    refine ⟨w₀, w₀, fun q => ?_⟩
    ext w
    rw [OppBase.ys_apply, mul_comm (lz (-1) ^ w₀) q]
    exact perp_bres_zero hlam hv le_rfl le_rfl q w
  · rintro a b ⟨k, N₁, h₁⟩ ⟨k', N₂, h₂⟩
    exact ⟨max k k', max N₁ N₂, OppBase.Wit.add_a (h₁.mono (le_max_left _ _) (le_max_left _ _))
      (h₂.mono (le_max_right _ _) (le_max_right _ _))⟩

/-- **Lowest-weight condition for `Y^R`**: `Y^R(v)ₙ λ = 0` for `n ≥ wt v`. -/
theorem yR_lower_of_perp {lam : Module.Dual ℂ M} (hlam : ∀ x ∈ fzO N.toWeakModule, lam x = 0)
    {w₀ : ℕ} {v : V} (hv : v ∈ W.grading (w₀ : ℤ)) {n : ℤ} (hn : (w₀ : ℤ) ≤ n) :
    (oppBase N).yR (-1) neg_one_ne_zero' v n lam = 0 := by
  have hW : (oppBase N).Wit (-1) v lam w₀ w₀ := fun q => by
    ext w
    rw [OppBase.ys_apply, mul_comm (lz (-1) ^ w₀) q]
    exact perp_bres_zero hlam hv le_rfl le_rfl q w
  obtain ⟨A, B, hAB⟩ := bezout neg_one_ne_zero' 0 w₀
  rw [OppBase.yR_eq neg_one_ne_zero' hW n 0 (by omega) A B hAB]
  ext w
  rw [OppBase.ys_apply]
  exact perp_bres_zero hlam hv hn le_rfl B w

variable (N) in
/-- `T^{-1-K'} (1+T)^{r+K'} ≡ T^{-1} (1+T)^r` modulo `good r`. -/
theorem left_shift_mem_good (r K' : ℕ) :
    T (-1 - (K' : ℤ)) * (1 + z) ^ (r + K') - T (-1) * (1 + z) ^ r
      ∈ good N.toWeakModule (r : ℤ) := by
  induction K' with
  | zero => simp
  | succ K' ih =>
    have hg := T_mul_pow_mem_good N r (r + K') (by omega) (-2 - (K' : ℤ))
      (by push_cast [show r + K' - r = K' by omega]; omega)
    have he : T (-1 - ((K' + 1 : ℕ) : ℤ)) * (1 + z) ^ (r + (K' + 1)) - T (-1) * (1 + z) ^ r
        = T (-2 - (K' : ℤ)) * (1 + z) ^ (r + K')
          + (T (-1 - (K' : ℤ)) * (1 + z) ^ (r + K') - T (-1) * (1 + z) ^ r) := by
      have h1 : (T (-1 - ((K' + 1 : ℕ) : ℤ)) : ℂ[T;T⁻¹]) = T (-2 - (K' : ℤ)) := by
        congr 1; push_cast; ring
      have h2 : (T (-2 - (K' : ℤ)) : ℂ[T;T⁻¹]) * z = T (-1 - (K' : ℤ)) := by
        rw [z, ← T_add]; congr 1; ring
      rw [h1, show r + (K' + 1) = (r + K') + 1 by ring, pow_succ]
      linear_combination (1 + z) ^ (r + K') * h2
    rw [he]
    exact Submodule.add_mem _ hg ih

/-- **The zero mode of `Y^R`** on a functional vanishing on `O(M)` is the Frenkel–Zhu left
action of `θ(v) = (−1)^{wt v} e^{L(1)} v`. -/
theorem yR_zero_of_perp {lam : Module.Dual ℂ M} (hlam : ∀ x ∈ fzO N.toWeakModule, lam x = 0)
    {w₀ : ℕ} {v : V} (hv : v ∈ W.grading (w₀ : ℤ)) (w : M) :
    (oppBase N).yR (-1) neg_one_ne_zero' v ((w₀ : ℤ) - 1) lam w
      = (-1 : ℂ) ^ (w₀ : ℤ) * ∑ j ∈ Finset.range (w₀ + 1), ((j.factorial : ℂ)⁻¹) *
          lam (fzLeft N.toWeakModule (w₀ - j) ((W.L 1 ^ j) v) w) := by
  have hW : (oppBase N).Wit (-1) v lam w₀ w₀ := fun q => by
    ext w
    rw [OppBase.ys_apply, mul_comm (lz (-1) ^ w₀) q]
    exact perp_bres_zero hlam hv le_rfl le_rfl q w
  obtain ⟨A, B, hAB⟩ := bezout neg_one_ne_zero' 1 w₀
  rw [OppBase.yR_eq neg_one_ne_zero' hW ((w₀ : ℤ) - 1) 1 (by omega) A B hAB, OppBase.ys_apply]
  -- `B = 1 + X·B'`
  have hB0 : B.coeff 0 = 1 := by
    have := congrArg (Polynomial.eval 0) hAB
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa [lz] using this
  have hBsplit : B = Polynomial.C 1 + Polynomial.X * B.divX := by
    rw [← hB0, add_comm, Polynomial.X_mul_divX_add]
  have hsplit : T ((w₀ : ℤ) - 1) * Polynomial.toLaurent (B * lz (-1) ^ w₀)
      = T ((w₀ : ℤ) - 1) * Polynomial.toLaurent (lz (-1) ^ w₀)
        + T (w₀ : ℤ) * Polynomial.toLaurent (B.divX * lz (-1) ^ w₀) := by
    conv_lhs => rw [hBsplit]
    simp only [map_mul, map_add, map_one, Polynomial.toLaurent_X]
    rw [show (T (w₀ : ℤ) : ℂ[T;T⁻¹]) = T ((w₀ : ℤ) - 1) * T 1 by rw [← T_add]; congr 1; ring]
    ring
  rw [hsplit, OppBase.bres_add, LinearMap.add_apply, map_add,
    perp_bres_zero hlam hv le_rfl le_rfl B.divX w, add_zero, oppBase_bres_eq N hv, map_smul,
    map_sum, smul_eq_mul, Int.toNat_natCast]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [map_smul, smul_eq_mul]
  congr 1
  have hcast : ((w₀ : ℤ) - j) = ((w₀ - j : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : j ≤ w₀)]; ring
  have hstate : (W.L 1 ^ j) v ∈ W.grading ((w₀ - j : ℕ) : ℤ) := by
    have := L_one_pow_mem W hv j
    rwa [hcast] at this
  have htest : T (2 * (w₀ : ℤ) - 2 - j) * invert (T ((w₀ : ℤ) - 1) *
      Polynomial.toLaurent (lz (-1) ^ w₀)) = T (-1 - (j : ℤ)) * (1 + z) ^ ((w₀ - j) + j) := by
    rw [map_mul, invert_T, invert_one_add_pow, show (w₀ - j) + j = w₀ by omega, ← mul_assoc,
      ← mul_assoc, ← T_add, ← T_add]
    congr 2; ring
  rw [htest, fzLeft_eq_res, mul_comm ((1 + z) ^ (w₀ - j)) (T (-1))]
  have hg := left_shift_mem_good N (w₀ - j) j
  have := hlam _ (hg _ hstate w)
  rw [map_sub, map_sub] at this
  exact sub_eq_zero.1 this

/-! ### The left action -/

theorem neg_neg_one_ne_zero : -(-1 : ℂ) ≠ 0 := by norm_num

theorem trans_bres_poly_perp {lam : Module.Dual ℂ M} (hlam : ∀ x ∈ fzO N.toWeakModule, lam x = 0)
    {w₀ : ℕ} {v : V} (hv : v ∈ W.grading (w₀ : ℤ)) (p : ℂ[X]) (w : M) :
    lam ((transBase N (-(-1 : ℂ))).bres v (Polynomial.toLaurent p) w)
      = lam ((oppBase N).bres v (Polynomial.toLaurent (p.comp (Polynomial.X + Polynomial.C 1))) w) := by
  rw [bres_trans_poly, neg_neg]

/-- The canonical `Y^L`-witness of a functional vanishing on `O(M)`. -/
theorem trans_wit_of_perp {lam : Module.Dual ℂ M} (hlam : ∀ x ∈ fzO N.toWeakModule, lam x = 0)
    {w₀ : ℕ} {v : V} (hv : v ∈ W.grading (w₀ : ℤ)) :
    (transBase N (-(-1 : ℂ))).Wit (-(-1 : ℂ)) v lam w₀ w₀ := fun q => by
  ext w
  rw [OppBase.ys_apply, show (T (w₀ : ℤ) : ℂ[T;T⁻¹]) = T ((w₀ : ℕ) : ℤ) from rfl,
    T_mul_toLaurent_nat, trans_bres_poly_perp hlam hv]
  have e : (Polynomial.X ^ w₀ * (lz (-(-1 : ℂ)) ^ w₀ * q)).comp (Polynomial.X + Polynomial.C 1)
      = Polynomial.X ^ w₀ * (q.comp (Polynomial.X + Polynomial.C 1) * lz (-1) ^ w₀) := by
    simp only [lz, neg_neg, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.sub_comp, Polynomial.C_comp, map_neg, sub_neg_eq_add]
    ring
  rw [e, ← T_mul_toLaurent_nat]
  exact perp_bres_zero hlam hv le_rfl le_rfl _ w

/-- **Lowest-weight condition for `Y^L`**: `Y^L(v)ₙ λ = 0` for `n ≥ wt v`. -/
theorem yL_lower_of_perp {lam : Module.Dual ℂ M} (hlam : ∀ x ∈ fzO N.toWeakModule, lam x = 0)
    {w₀ : ℕ} {v : V} (hv : v ∈ W.grading (w₀ : ℤ)) {n : ℤ} (hn : (w₀ : ℤ) ≤ n) :
    (transBase N (-(-1 : ℂ))).yR (-(-1 : ℂ)) neg_neg_one_ne_zero v n lam = 0 := by
  obtain ⟨A, B, hAB⟩ := bezout neg_neg_one_ne_zero 0 w₀
  rw [OppBase.yR_eq neg_neg_one_ne_zero (trans_wit_of_perp hlam hv) n 0 (by omega) A B hAB]
  ext w
  obtain ⟨n', rfl⟩ : ∃ n' : ℕ, n = n' := ⟨n.toNat, by omega⟩
  rw [OppBase.ys_apply, T_mul_toLaurent_nat, trans_bres_poly_perp hlam hv]
  have e : (Polynomial.X ^ n' * (B * lz (-(-1 : ℂ)) ^ w₀)).comp (Polynomial.X + Polynomial.C 1)
      = Polynomial.X ^ w₀ * (B.comp (Polynomial.X + Polynomial.C 1) * lz (-1) ^ n') := by
    simp only [lz, neg_neg, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.sub_comp, Polynomial.C_comp, map_neg, sub_neg_eq_add]
    ring
  rw [e, ← T_mul_toLaurent_nat]
  exact perp_bres_zero hlam hv le_rfl (by omega) _ w

/-- **The zero mode of `Y^L`** on a functional vanishing on `O(M)` is the Frenkel–Zhu right
action. -/
theorem yL_zero_of_perp {lam : Module.Dual ℂ M} (hlam : ∀ x ∈ fzO N.toWeakModule, lam x = 0)
    {w₀ : ℕ} (hw₀ : 1 ≤ w₀) {v : V} (hv : v ∈ W.grading (w₀ : ℤ)) (w : M) :
    (transBase N (-(-1 : ℂ))).yR (-(-1 : ℂ)) neg_neg_one_ne_zero v ((w₀ : ℤ) - 1) lam w
      = lam (fzRight N.toWeakModule w₀ v w) := by
  obtain ⟨A, B, hAB⟩ := bezout neg_neg_one_ne_zero 1 w₀
  rw [OppBase.yR_eq neg_neg_one_ne_zero (trans_wit_of_perp hlam hv) ((w₀ : ℤ) - 1) 1
    (by omega) A B hAB, OppBase.ys_apply,
    show ((w₀ : ℤ) - 1) = ((w₀ - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hw₀]; ring,
    T_mul_toLaurent_nat, trans_bres_poly_perp hlam hv]
  -- `B(0) (−1)^{w₀} = 1`
  have hB0 : B.eval 0 * (-1 : ℂ) ^ w₀ = 1 := by
    have := congrArg (Polynomial.eval 0) hAB
    simpa [lz] using this
  set β := B.eval 0
  obtain ⟨G, hG⟩ : ∃ G : ℂ[X], B.comp (Polynomial.X + Polynomial.C 1)
      = Polynomial.C β + (Polynomial.X + Polynomial.C 1) * G := by
    have h := Polynomial.X_sub_C_dvd_sub_C_eval (p := B.comp (Polynomial.X + Polynomial.C 1))
      (a := -1)
    obtain ⟨G, hG⟩ := h
    refine ⟨G, ?_⟩
    rw [map_neg, sub_neg_eq_add] at hG
    rw [← hG]
    simp [β, Polynomial.eval_comp]
  have e : (Polynomial.X ^ (w₀ - 1) * (B * lz (-(-1 : ℂ)) ^ w₀)).comp
        (Polynomial.X + Polynomial.C 1)
      = Polynomial.X ^ w₀ * (Polynomial.C β * lz (-1) ^ (w₀ - 1))
        + Polynomial.X ^ w₀ * (G * lz (-1) ^ w₀) := by
    simp only [lz, neg_neg, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.sub_comp, Polynomial.C_comp, map_neg, sub_neg_eq_add, hG]
    rw [show (w₀ : ℕ) = (w₀ - 1) + 1 by omega]
    simp only [Nat.add_sub_cancel]
    ring
  rw [e, map_add, OppBase.bres_add, LinearMap.add_apply, map_add, ← T_mul_toLaurent_nat,
    ← T_mul_toLaurent_nat, perp_bres_zero hlam hv le_rfl le_rfl G w, add_zero,
    oppBase_bres_eq N hv, map_smul, map_sum, smul_eq_mul, Int.toNat_natCast]
  have htest : ∀ j : ℕ, T (2 * (w₀ : ℤ) - 2 - j) * invert (T (w₀ : ℤ) *
      Polynomial.toLaurent (Polynomial.C β * lz (-1) ^ (w₀ - 1)))
      = β • (T (-1 - (j : ℤ)) * (1 + z) ^ (w₀ - 1)) := by
    intro j
    rw [map_mul, map_mul, Polynomial.toLaurent_C, map_mul, invert_C, invert_T,
      invert_one_add_pow, smul_eq_C_mul]
    have h1 : (T (2 * (w₀ : ℤ) - 2 - j) : ℂ[T;T⁻¹]) * T (-(w₀ : ℤ)) * T (-((w₀ - 1 : ℕ) : ℤ))
        = T (-1 - (j : ℤ)) := by
      rw [← T_add, ← T_add]; congr 1; push_cast [Nat.cast_sub hw₀]; ring
    linear_combination (LC β * (1 + z) ^ (w₀ - 1)) * h1
  rw [Finset.sum_eq_single 0]
  · rw [htest, map_smul, map_smul, smul_eq_mul]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply,
      CharP.cast_eq_zero, sub_zero, one_mul]
    rw [map_smul, smul_eq_mul, mul_comm (T (-1)), ← fzRight_eq_res N.toWeakModule hw₀,
      ← mul_assoc, mul_comm ((-1 : ℂ) ^ (w₀ : ℤ)) β, zpow_natCast, hB0, one_mul]
  · intro j hj hj0
    rw [Finset.mem_range] at hj
    rw [map_smul, htest, map_smul, map_smul]
    have hcast : ((w₀ : ℤ) - j) = ((w₀ - j : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : j ≤ w₀)]; ring
    have hstate : (W.L 1 ^ j) v ∈ W.grading ((w₀ - j : ℕ) : ℤ) := by
      have := L_one_pow_mem W hv j
      rwa [hcast] at this
    have hg := T_mul_pow_mem_good N (w₀ - j) (w₀ - 1) (by omega) (-1 - (j : ℤ))
      (by push_cast [Nat.cast_sub (show w₀ - j ≤ w₀ - 1 by omega), Nat.cast_sub hw₀,
        Nat.cast_sub (show j ≤ w₀ by omega)]; omega)
    rw [hlam _ (hg _ hstate w), smul_zero, smul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

end Omega

end VOA.Huang.LiRegular
