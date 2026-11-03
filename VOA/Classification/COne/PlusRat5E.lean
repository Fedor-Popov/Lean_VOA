import VOA.Classification.COne.PlusRat5Comm

/-! # The `E`-lowerings of an `M(1)⁺`-top lift (replaces Abe's fusion-rule step, Lemma 7.5)

Let `u` be a vector of a weak `V_{2m}⁺`-module with `L(0)u = h u`, `L(k)u = 0` (`k ≥ 1`),
`o(H⁴)u = a₄ u`, and put `Y(ℓ) = E₍ₘ₋₁₊ℓ₎ u` (lowering by `ℓ`).  If `Y(ℓ) = 0` for all `ℓ > n` then
(`oH4_Y`, `K = 2m`)

  `(2K²-5K+2) o(H⁴) Y(n) = ((2K²-5K+2) a₄ - 2n((m+n)² - 4mh)) Y(n)`.

This is the lowering counterpart of `PlusRat3.oG_H4_v`.  It is used by downward induction on `n`:
the virtual eigenvalue is negative for a charged or half quotient, outside the spectrum of
`o(H⁴)` on an untwisted kernel.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat5
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3 PlusRat4

section ELow
variable (m : ℕ) (hm : 1 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M) {u : M} {h : ℂ}

theorem negOnePow_neg_one' : negOnePow (-1) = -1 := by
  rw [negOnePow, if_neg (by decide)]

theorem negOnePow_neg_two' : negOnePow (-2) = 1 := by
  rw [negOnePow, if_pos (by decide)]

/-- The `E`-lowering by `ℓ`. -/
abbrev Ylow (u : M) (ℓ : ℤ) : M := mode (A.YM (EP m hm)) ((m : ℤ) - 1 + ℓ) u

variable (hL : L0 A u = h • u)
  (hLk : ∀ k : ℤ, 1 ≤ k → mode (A.YM (V2mPlus m hm).conformalVector) (k + 1) u = 0)

/-- `E₍q₋₁₎ L(-1)u = (q-1)... `: the translation term, given the higher lowerings vanish. -/
theorem E_Lm1 (n : ℤ) (hY1 : Ylow m hm A u (n + 1) = 0) :
    mode (A.YM (EP m hm)) ((m : ℤ) + n) (mode (A.YM (V2mPlus m hm).conformalVector) 0 u) =
      ((m : ℂ) + n) • Ylow m hm A u n := by
  have hY1' : mode (A.YM (EP m hm)) ((m : ℤ) - 1 + (n + 1)) u = 0 := hY1
  rw [mode_translation, show (m : ℤ) + n = (m : ℤ) - 1 + (n + 1) by ring, hY1', map_zero, zero_add,
    show (m : ℤ) - 1 + (n + 1) - 1 = (m : ℤ) - 1 + n by ring]
  change _ = _ • mode (A.YM (EP m hm)) ((m : ℤ) - 1 + n) u
  congr 1
  push_cast; ring

include hL hLk in
theorem om1E (n : ℤ) (hY : ∀ ℓ : ℤ, n < ℓ → Ylow m hm A u ℓ = 0) :
    mode (A.YM ((V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-1) (EP m hm)))
      ((m : ℤ) + 1 + n) u = ((m : ℂ) + n + h) • Ylow m hm A u n := by
  rw [module_iterate0 A _ _ u (-1) _]
  rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
  · rw [Finset.sum_pair (by norm_num)]
    have h1 : mode (A.YM (EP m hm)) ((m : ℤ) + 1 + n + 0) u = 0 := by
      rw [show (m : ℤ) + 1 + n + 0 = (m : ℤ) - 1 + (n + 2) by ring]; exact hY _ (by omega)
    have h2 : mode (A.YM (EP m hm)) ((m : ℤ) + 1 + n + 1) u = 0 := by
      rw [show (m : ℤ) + 1 + n + 1 = (m : ℤ) - 1 + (n + 3) by ring]; exact hY _ (by omega)
    have hω1 : mode (A.YM (V2mPlus m hm).conformalVector) 1 u = h • u := hL
    rw [h1, h2, map_zero, map_zero, cbz_zero, cbz_one', show negOnePow 0 = 1 by simp [negOnePow],
      negOnePow_one', hω1, map_smul,
      show -1 + ((m : ℤ) + 1 + n) - 0 = (m : ℤ) + n by ring,
      show -1 + ((m : ℤ) + 1 + n) - 1 = (m : ℤ) - 1 + n by ring,
      E_Lm1 m hm A n (hY _ (by omega))]
    rw [negOnePow_neg_one']
    push_cast
    module
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hne
    apply hi
    by_cases hneg : i < 0
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
    · have hYi : mode (A.YM (EP m hm)) ((m : ℤ) - 1 + (n + 2 + i)) u = 0 := hY _ (by omega)
      rw [show (m : ℤ) + 1 + n + i = (m : ℤ) - 1 + (n + 2 + i) by ring, hYi, map_zero,
        zero_sub, show i = (i - 1) + 1 by ring, hLk (i - 1) (by omega), map_zero, smul_zero,
        neg_zero, smul_zero]

include hL hLk in
theorem om2E (n : ℤ) (hY : ∀ ℓ : ℤ, n < ℓ → Ylow m hm A u ℓ = 0) :
    mode (A.YM ((V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-2) (EP m hm)))
      ((m : ℤ) + 2 + n) u = (-((m : ℂ) + n + 2 * h)) • Ylow m hm A u n := by
  rw [module_iterate0 A _ _ u (-2) _]
  rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
  · rw [Finset.sum_pair (by norm_num)]
    have h1 : mode (A.YM (EP m hm)) ((m : ℤ) + 2 + n + 0) u = 0 := by
      rw [show (m : ℤ) + 2 + n + 0 = (m : ℤ) - 1 + (n + 3) by ring]; exact hY _ (by omega)
    have h2 : mode (A.YM (EP m hm)) ((m : ℤ) + 2 + n + 1) u = 0 := by
      rw [show (m : ℤ) + 2 + n + 1 = (m : ℤ) - 1 + (n + 4) by ring]; exact hY _ (by omega)
    have hω1 : mode (A.YM (V2mPlus m hm).conformalVector) 1 u = h • u := hL
    rw [h1, h2, map_zero, map_zero, cbz_zero, cbz_one', show negOnePow 0 = 1 by simp [negOnePow],
      negOnePow_one', hω1, map_smul,
      show -2 + ((m : ℤ) + 2 + n) - 0 = (m : ℤ) + n by ring,
      show -2 + ((m : ℤ) + 2 + n) - 1 = (m : ℤ) - 1 + n by ring,
      E_Lm1 m hm A n (hY _ (by omega))]
    rw [negOnePow_neg_two']
    push_cast
    module
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hne
    apply hi
    by_cases hneg : i < 0
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
    · have hYi : mode (A.YM (EP m hm)) ((m : ℤ) - 1 + (n + 3 + i)) u = 0 := hY _ (by omega)
      rw [show (m : ℤ) + 2 + n + i = (m : ℤ) - 1 + (n + 3 + i) by ring, hYi, map_zero,
        zero_sub, show i = (i - 1) + 1 by ring, hLk (i - 1) (by omega), map_zero, smul_zero,
        neg_zero, smul_zero]

include hL hLk in
theorem om1LE (n : ℤ) (hY : ∀ ℓ : ℤ, n < ℓ → Ylow m hm A u ℓ = 0) :
    mode (A.YM ((V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-1)
      ((V2mPlus m hm).L (-1) (EP m hm)))) ((m : ℤ) + 2 + n) u =
      (-(((m : ℂ) + n) * ((m : ℂ) + n + 1 + h))) • Ylow m hm A u n := by
  rw [module_iterate0 A _ _ u (-1) _]
  rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
  · rw [Finset.sum_pair (by norm_num)]
    simp only [T_mode]
    have h1 : mode (A.YM (EP m hm)) ((m : ℤ) + 2 + n + 0 - 1) u = 0 := by
      rw [show (m : ℤ) + 2 + n + 0 - 1 = (m : ℤ) - 1 + (n + 2) by ring]; exact hY _ (by omega)
    have h2 : mode (A.YM (EP m hm)) ((m : ℤ) + 2 + n + 1 - 1) u = 0 := by
      rw [show (m : ℤ) + 2 + n + 1 - 1 = (m : ℤ) - 1 + (n + 3) by ring]; exact hY _ (by omega)
    have hω1 : mode (A.YM (V2mPlus m hm).conformalVector) 1 u = h • u := hL
    rw [h1, h2, smul_zero, smul_zero, map_zero, map_zero, cbz_zero, cbz_one',
      show negOnePow 0 = 1 by simp [negOnePow], negOnePow_one', hω1, map_smul,
      show -1 + ((m : ℤ) + 2 + n) - 0 - 1 = (m : ℤ) + n by ring,
      show -1 + ((m : ℤ) + 2 + n) - 1 - 1 = (m : ℤ) - 1 + n by ring,
      E_Lm1 m hm A n (hY _ (by omega))]
    rw [negOnePow_neg_one']
    push_cast
    module
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hne
    apply hi
    by_cases hneg : i < 0
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
    · have hYi : mode (A.YM (EP m hm)) ((m : ℤ) - 1 + (n + 2 + i)) u = 0 := hY _ (by omega)
      rw [T_mode, T_mode, show (m : ℤ) + 2 + n + i - 1 = (m : ℤ) - 1 + (n + 2 + i) by ring,
        hYi, smul_zero, map_zero, zero_sub, show i = (i - 1) + 1 by ring,
        hLk (i - 1) (by omega), map_zero, smul_zero, smul_zero, neg_zero, smul_zero]

variable (a4 : ℂ) (hA : mode (A.YM (HP m hm 2)) 3 u = a4 • u)

include hL hLk hA in
/-- **The `E`-lowering eigenvalue.** -/
theorem oH4_Y (n : ℤ) (hY : ∀ ℓ : ℤ, n < ℓ → Ylow m hm A u ℓ = 0) :
    (2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) • mode (A.YM (HP m hm 2)) 3 (Ylow m hm A u n) =
      ((2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) * a4 -
        2 * n * (((m : ℂ) + n) ^ 2 - 4 * m * h)) • Ylow m hm A u n := by
  set p : ℤ := (m : ℤ) - 1 + n with hp
  have hc := zero_mode_comm A 3 (HP m hm 2) (EP m hm) p u
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, hA, map_smul] at hc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hc
  rw [show ((3 : ℕ) : ℤ) = 3 by rfl, H4_3_E m hm, map_zero, mode_zero, LinearMap.zero_apply,
    smul_zero, add_zero] at hc
  -- the three products
  have e2 := congrArg (fun v => mode (A.YM v) (3 + p - ((2 : ℕ) : ℤ)) u) (H4_2_E m hm)
  have e1 := congrArg (fun v => mode (A.YM v) (3 + p - ((1 : ℕ) : ℤ)) u) (H4_1_E m hm)
  have e0 := congrArg (fun v => mode (A.YM v) (3 + p - ((0 : ℕ) : ℤ)) u) (H4_0_E m hm)
  simp only [map_smul, map_sub, map_add, mode_smul, mode_sub, mode_add, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.add_apply] at e2 e1 e0
  rw [T_mode] at e2
  rw [T_mode, T_mode] at e1
  rw [T_mode, T_mode, T_mode] at e0
  have q2 : (3 : ℤ) + p - ((2 : ℕ) : ℤ) - 1 = (m : ℤ) - 1 + n := by rw [hp]; push_cast; ring
  have q1 : (3 : ℤ) + p - ((1 : ℕ) : ℤ) - 1 - 1 = (m : ℤ) - 1 + n := by rw [hp]; push_cast; ring
  have q0 : (3 : ℤ) + p - ((0 : ℕ) : ℤ) - 1 - 1 - 1 = (m : ℤ) - 1 + n := by rw [hp]; push_cast; ring
  rw [q2] at e2
  rw [q1] at e1
  rw [q0] at e0
  have r1 : (3 : ℤ) + p - ((1 : ℕ) : ℤ) = (m : ℤ) + 1 + n := by rw [hp]; push_cast; ring
  have r0 : (3 : ℤ) + p - ((0 : ℕ) : ℤ) = (m : ℤ) + 2 + n := by rw [hp]; push_cast; ring
  rw [r1, om1E m hm A hL hLk n hY] at e1
  rw [r0, om2E m hm A hL hLk n hY, om1LE m hm A hL hLk n hY] at e0
  rw [hc]
  simp only [show Nat.choose 3 0 = 1 from rfl, show Nat.choose 3 1 = 3 from rfl,
    show Nat.choose 3 2 = 3 from rfl]
  rw [show ((3 : ℕ) : ℂ) = 3 by norm_num, show ((1 : ℕ) : ℂ) = 1 by norm_num]
  have hK1 : (2 * (2 * (m : ℂ)) - 1) ≠ 0 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hK2 : (2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) =
      (2 * (2 * (m : ℂ)) - 1) * (2 * (m : ℂ) - 2) := by ring
  simp only [Ylow] at e1 e0 ⊢
  rw [hp] at e2 ⊢
  rw [show (3 : ℤ) + ((m : ℤ) - 1 + n) - ((0 : ℕ) : ℤ) = (m : ℤ) + 2 + n by push_cast; ring,
    show (3 : ℤ) + ((m : ℤ) - 1 + n) - ((1 : ℕ) : ℤ) = (m : ℤ) + 1 + n by push_cast; ring,
    show (3 : ℤ) + ((m : ℤ) - 1 + n) - ((2 : ℕ) : ℤ) = (m : ℤ) + n by push_cast; ring]
  rw [show (3 : ℤ) + ((m : ℤ) - 1 + n) - ((2 : ℕ) : ℤ) = (m : ℤ) + n by push_cast; ring] at e2
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at ⊢
  push_cast at e2 e1 e0
  linear_combination (norm := module) e0 + (3 * (2 * (m : ℂ) - 2)) • e1 +
    (2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) • e2

end ELow

end VOA.Classification.COne.PlusRat5
