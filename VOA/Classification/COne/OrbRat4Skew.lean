import VOA.Classification.COne.OrbRat3Residual
import VOA.Core.SkewSymmetry

/-! # The weight-nine generator through skew-symmetry

`OrbRat3` evaluates `U₍N₎ x` for `U = J₍₋₂₎E − E₍₋₂₎J` by the finite iterate formula for both
summands.  The second summand produces the terms `J₍N₋₂₋ᵢ₎ E₍ᵢ₎ x`, in which `E₍ᵢ₎ x` is a
neutral state of weight up to `12`: its kernel evaluation is far beyond the memory budget.

Here the second summand is first rewritten by skew-symmetry,

  `E₍₋₂₎J = ∑_{j<6} (1/j!) (-1)^{1-j} Tʲ (J₍ⱼ₋₂₎E)`   (`J₍ₖ₎E = 0` for `k ≥ 4`),

so that `U₍N₎ x` is a combination of `(J₍ℓ₎E)₍M₎ x` only (`ell_expand`).  Each of these is then
expanded by the finite iterate formula with `J` on the left (`JE_iter`): the only states that
occur are `J₍ᵢ₎ x` followed by `E` down to the target weight, and `E₍ₘ₎ x` of tiny weight followed
by `J`.  `assemble` packages the result as a rational multiple of `h(-1)1`, given tables of
the individual products.
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e LatMod
  OrbRat3 VertexOperatorAlgebra

local notation "W" => V2m 4 four_ge_one

/-! ## Rational coefficients -/

/-- The sign `(-1)^ℓ` as a rational. -/
def sQ (l : ℤ) : ℚ := if l % 2 = 0 then 1 else -1

theorem sgn_eq_sQ (l : ℤ) : VOA.sgn l = ((sQ l : ℚ) : ℂ) := by
  unfold VOA.sgn sQ
  by_cases h : l % 2 = 0
  · rw [if_pos (Int.even_iff.mpr h), if_pos h]; simp
  · rw [if_neg (fun h' => h (Int.even_iff.mp h')), if_neg h]; simp

theorem zpow_eq_sQ (l : ℤ) : (-1 : ℂ) ^ l = ((sQ l : ℚ) : ℂ) := by
  unfold sQ
  by_cases h : l % 2 = 0
  · rw [if_pos h, (Int.even_iff.mpr h).neg_one_zpow]; simp
  · rw [if_neg h, (Int.not_even_iff_odd.mp (fun h' => h (Int.even_iff.mp h'))).neg_one_zpow]
    simp

/-- The generalized binomial coefficient, rationally. -/
def gQ (l : ℤ) : ℕ → ℚ
  | 0 => 1
  | i + 1 => gQ l i * ((l : ℚ) - i) / (i + 1)

theorem gBinom_eq_gQ (l : ℤ) (i : ℕ) : gBinom l i = ((gQ l i : ℚ) : ℂ) := by
  induction i with
  | zero => simp [gQ]
  | succ i ih =>
    have h1 : gBinom l (i + 1) = gBinom l i * (((l : ℂ) - i) / (i + 1)) := by
      unfold gBinom
      rw [Finset.prod_range_succ, Nat.factorial_succ]
      push_cast
      have : ((i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
      have : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
      field_simp
    rw [h1, ih, gQ]
    push_cast
    ring

/-- `∏_{i<j} -(N-i)`, rationally. -/
def pQ (N : ℤ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => pQ N j * (-((N : ℚ) - j))

theorem prod_eq_pQ (N : ℤ) (j : ℕ) :
    (((∏ i ∈ Finset.range j, (-(N - (i : ℤ)))) : ℤ) : ℂ) = ((pQ N j : ℚ) : ℂ) := by
  induction j with
  | zero => simp [pQ]
  | succ j ih =>
    rw [Finset.prod_range_succ, Int.cast_mul, ih, pQ]
    push_cast
    ring

/-- The skew coefficient `(1/j!) (-1)^{1-j} ∏_{i<j} -(N-i)`. -/
def kQ (N : ℤ) (j : ℕ) : ℚ := (j.factorial : ℚ)⁻¹ * sQ (1 - j) * pQ N j

/-! ## The charged generator as an executable state -/

/-- `E = e^{β} + e^{-β}` as a multi-sector state. -/
def Est : St := [(1, [(1, [])]), (-1, [(1, [])])]

theorem evalSt_Est : evalSt Est = Ec := by
  have h1 : evRc (a0 4) (cα 4) [((1 : ℚ), ([] : List ℕ))] = (1 : FockN (rank (latP 4))) := by
    rw [evRc_cons, evRc_nil, evalWordC_nil]; simp
  simp only [Est, evalSt_cons, evalSt_nil, add_zero, h1]
  rfl

theorem JE_zero_low (k : ℤ) (hk : k ∈ [4, 5, 6, 7]) :
    (V2m 4 four_ge_one).smul Jc k Ec = 0 := by
  rw [← evalSt_Est, actJ_sound]
  have h : actJ k Est = [(1, []), (-1, [])] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    all_goals decide +kernel
  rw [h]
  simp [evalSt_cons, evRc_nil, sector, latStateGen]

theorem JE_zero (k : ℤ) (hk : 4 ≤ k) : (V2m 4 four_ge_one).smul Jc k Ec = 0 := by
  by_cases h8 : 8 ≤ k
  · exact OrbC2f.smul_eq_zero_of_weights _ Jc_mem Ec_mem (by omega)
  · apply JE_zero_low
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

/-! ## Skew-symmetry for `E₍₋₂₎J` -/

theorem smul_sum_left {ι : Type*} (s : Finset ι) (f : ι → LatModuleGen (latP 4)) (n : ℤ)
    (x : LatModuleGen (latP 4)) :
    (V2m 4 four_ge_one).smul (∑ j ∈ s, f j) n x = ∑ j ∈ s, (V2m 4 four_ge_one).smul (f j) n x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, PreVertexAlgebra.smul_add_left, ih]

theorem EJ_skew : (V2m 4 four_ge_one).smul Ec (-2) Jc =
    ∑ j ∈ Finset.range 6, (((j.factorial : ℂ)⁻¹) * VOA.sgn (1 - j)) •
      (((V2m 4 four_ge_one).toPreVertexAlgebra.T ^ j) ((V2m 4 four_ge_one).smul Jc (j - 2) Ec)) := by
  rw [skew_mode]
  have hterm : ∀ j : ℕ, ((j.factorial : ℂ)⁻¹) • (VOA.sgn (-(-2) - 1 - j)) •
      (((V2m 4 four_ge_one).toPreVertexAlgebra.T ^ j)
        (((V2m 4 four_ge_one).Y Jc) (-(-2) - 1 - j) Ec)) =
      (((j.factorial : ℂ)⁻¹) * VOA.sgn (1 - j)) •
      (((V2m 4 four_ge_one).toPreVertexAlgebra.T ^ j) ((V2m 4 four_ge_one).smul Jc (j - 2) Ec)) := by
    intro j
    rw [smul_smul, PreVertexAlgebra.smul_eq_coeff]
    congr 3
    ring_nf
  simp only [hterm]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Function.mem_support] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hj
  rw [JE_zero _ (by omega), map_zero, smul_zero]

/-- `U₍N₎ x` as a combination of `(J₍ℓ₎E)₍M₎ x`. -/
theorem ell_expand (N : ℤ) (x : LatModuleGen (latP 4)) :
    (V2m 4 four_ge_one).smul Uc N x =
      (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul Jc (-2) Ec) N x -
        ∑ j ∈ Finset.range 6, ((kQ N j : ℚ) : ℂ) •
          (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul Jc ((j : ℤ) - 2) Ec) (N - j) x := by
  have hsub (a b : LatModuleGen (latP 4)) :
      (V2m 4 four_ge_one).smul (a - b) N x =
        (V2m 4 four_ge_one).smul a N x - (V2m 4 four_ge_one).smul b N x := by
    rw [sub_eq_add_neg, PreVertexAlgebra.smul_add_left, ← neg_one_smul ℂ b,
      PreVertexAlgebra.smul_smul_left, neg_one_smul, ← sub_eq_add_neg]
  rw [Uc_eq, hsub, EJ_skew, smul_sum_left]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [PreVertexAlgebra.smul_smul_left, smul_Tpow, ← Int.cast_smul_eq_zsmul ℂ, smul_smul,
    prod_eq_pQ, kQ, sgn_eq_sQ]
  congr 1
  push_cast
  ring

/-! ## The iterate with `J` on the left -/

/-- The finite iterate of `(J₍ℓ₎E)₍M₎` on an executable state, through the evaluator. -/
theorem JE_iter (l M : ℤ) (B : ℕ) (Z : St) {r : ℤ}
    (hZ : evalSt Z ∈ (V2m 4 four_ge_one).grading r) (hB₁ : 4 + r ≤ B) (hB₂ : 4 + r - M ≤ B) :
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul Jc l Ec) M (evalSt Z) =
      ∑ i ∈ Finset.range B, ((gQ l i : ℚ) : ℂ) • (((sQ i : ℚ) : ℂ) •
        (evalSt (actJ (l - i) (actE (M + i) Z)) -
          ((sQ l : ℚ) : ℂ) • evalSt (actE (l + M - i) (actJ i Z)))) := by
  rw [OrbC2f.mode_iterate_finite _ Jc_mem Ec_mem hZ l M B hB₁ hB₂]
  apply Finset.sum_congr rfl
  intro i _
  rw [actE_sound, actJ_sound, actJ_sound, actE_sound, gBinom_eq_gQ, zpow_eq_sQ,
    ← zpow_natCast, zpow_eq_sQ, smul_smul, mul_comm]

/-! ## Assembly -/

/-- The scalar of one `(J₍ℓ₎E)₍M₎` iterate, from tables `a i` (the `J E` terms) and `t i`
(the `E J` terms). -/
def iterQ (l : ℤ) (B : ℕ) (a t : ℕ → ℚ) : ℚ :=
  ((List.range B).map fun i => gQ l i * (sQ i * (a i - sQ l * t i))).sum

/-- The total scalar of `U₍N₎ x`. -/
def outerQ (N : ℤ) (B : ℕ) (a : ℕ → ℕ → ℚ) (t : ℕ → ℚ) : ℚ :=
  iterQ (-2) B (a 0) t -
    ((List.range 6).map fun j => kQ N j * iterQ ((j : ℤ) - 2) B (a j) t).sum

theorem list_range_sum' {M : Type*} [AddCommMonoid M] (B : ℕ) (f : ℕ → M) :
    ((List.range B).map f).sum = ∑ i ∈ Finset.range B, f i := by
  induction B with
  | zero => simp
  | succ B ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem iter_value (l M : ℤ) (B : ℕ) (Z : St) {r : ℤ}
    (hZ : evalSt Z ∈ (V2m 4 four_ge_one).grading r) (hB₁ : 4 + r ≤ B) (hB₂ : 4 + r - M ≤ B)
    (a t : ℕ → ℚ)
    (hA : ∀ i < B, evalSt (actJ (l - i) (actE (M + i) Z)) = ((a i : ℚ) : ℂ) • hV)
    (hT : ∀ i < B, evalSt (actE (l + M - i) (actJ i Z)) = ((t i : ℚ) : ℂ) • hV) :
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul Jc l Ec) M (evalSt Z) =
      ((iterQ l B a t : ℚ) : ℂ) • hV := by
  rw [JE_iter l M B Z hZ hB₁ hB₂, iterQ, list_range_sum', Rat.cast_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [hA i hi', hT i hi']
  simp only [smul_smul, ← sub_smul]
  congr 1
  push_cast
  ring

/-- `U₍N₎ x` is a rational multiple of `h(-1)1`, given the tables of the elementary
products. -/
theorem assemble (N : ℤ) (B : ℕ) (Z : St) {r : ℤ}
    (hZ : evalSt Z ∈ (V2m 4 four_ge_one).grading r) (hB₁ : 4 + r ≤ B) (hB₂ : 4 + r - N + 5 ≤ B)
    (a : ℕ → ℕ → ℚ) (t : ℕ → ℚ)
    (hA : ∀ j : ℕ, j < 6 → ∀ i : ℕ, i < B →
      evalSt (actJ ((j : ℤ) - 2 - i) (actE (N - j + i) Z)) = ((a j i : ℚ) : ℂ) • hV)
    (hT : ∀ i < B, evalSt (actE (N - 2 - i) (actJ i Z)) = ((t i : ℚ) : ℂ) • hV) :
    (V2m 4 four_ge_one).smul Uc N (evalSt Z) = ((outerQ N B a t : ℚ) : ℂ) • hV := by
  rw [ell_expand]
  have h0 := iter_value (-2) N B Z hZ hB₁ (by omega) (a 0) t
    (fun i hi => by simpa using hA 0 (by norm_num) i hi)
    (fun i hi => by rw [show (-2 : ℤ) + N - i = N - 2 - i by ring]; exact hT i hi)
  rw [h0]
  have hj : ∀ j : ℕ, j ∈ Finset.range 6 → ((kQ N j : ℚ) : ℂ) •
      (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul Jc ((j : ℤ) - 2) Ec) (N - j) (evalSt Z) =
      ((kQ N j * iterQ ((j : ℤ) - 2) B (a j) t : ℚ) : ℂ) • hV := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [iter_value ((j : ℤ) - 2) (N - j) B Z hZ hB₁ (by omega) (a j) t
      (fun i hi => hA j hj' i hi)
      (fun i hi => by rw [show (j : ℤ) - 2 + (N - j) - i = N - 2 - i by ring]; exact hT i hi),
      smul_smul]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hj, ← Finset.sum_smul, ← sub_smul, outerQ, list_range_sum',
    Rat.cast_sub, Rat.cast_sum]

end VOA.Classification.COne.OrbRat4
