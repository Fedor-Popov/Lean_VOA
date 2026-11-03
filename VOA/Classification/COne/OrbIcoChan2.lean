import VOA.Classification.COne.OrbIcoLeibniz

/-! # OrbIco: the second channel `Prim₃₆ × Prim₃₆ → Prim₁₀₀` of `V₂`

For `u, v ∈ Prim₃₆` the mode `u₍₋₂₉₎v` has weight `100 = 10²`. On the multiplet:

`second_wv_all`: `w_{6,i}₍₋₂₉₎ w_{6,j} ≡ μ τ(i,j) w_{10,i+j-2}` modulo lower Virasoro descendants,
where `τ(i,j) = (12-i)(11-i)j(j-1) - 2(12-i)i(12-j)j + i(i-1)(12-j)(11-j)` is the second
transvectant of `x^{12-i}y^i` and `x^{12-j}y^j`.

`mu2_ne_zero`: `μ ≠ 0`. The base is the lattice computation
`e^{6α}₍₋₂₉₎ f₀² e^{6α} = ε · 2(g₉g₁₁ - g₁₀²) · e^{10α}/132`, `g_k = C(k+11, 11)`,
which uses the Leibniz rule `aExpVec_mul` and `f₀² e^{6α} = (S₉S₁₁ - 2S₁₀² + S₁₁S₉) e^{4α}`.

`second_bin`: the same statement for binary forms, with an explicit bilinear map `B2`.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VertexOperatorAlgebra OrbSpan VOA.LatGen VOA.LatGen.Triplet HeisenbergN
  OrbRat6 VOA.IntegralLattice OrbC2b OrbPrim MvPolynomial Finset

/-! ## `gco 2` -/

theorem gco_two_zero : gco (2 : ℂ) 0 = 1 := gco_zero _
theorem gco_two_one : gco (2 : ℂ) 1 = -2 := by
  rw [gco_succ]; simp [gco_zero]
theorem gco_two_two : gco (2 : ℂ) 2 = 1 := by
  rw [gco_succ]; simp [Finset.sum_range_succ, gco_two_one, gco_zero]; norm_num

theorem gco_two_sum : ∀ k : ℕ, 2 ≤ k → ∑ j ∈ range (k + 1), gco (2 : ℂ) j = 0 ∧
    gco (2 : ℂ) (k + 1) = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨by simp [Finset.sum_range_succ, gco_two_one, gco_two_two, gco_zero]; norm_num, ?_⟩
    rw [gco_succ]
    simp [Finset.sum_range_succ, gco_two_one, gco_two_two, gco_zero]
    norm_num
  | succ k hk ih =>
    have hs : ∑ j ∈ range (k + 1 + 1), gco (2 : ℂ) j = 0 := by
      rw [Finset.sum_range_succ, ih.1, ih.2, add_zero]
    refine ⟨hs, ?_⟩
    rw [gco_succ, ← Finset.mul_sum]
    have hr := Finset.sum_range_reflect (fun j => gco (2 : ℂ) j) (k + 1 + 1)
    simp only [show k + 1 + 1 - 1 = k + 1 by omega] at hr
    have : ∑ m ∈ range (k + 1 + 1), gco (2 : ℂ) (k + 1 - m) = 0 := by rw [hr, hs]
    rw [this, mul_zero, mul_zero]

theorem gco_two_ge (k : ℕ) (hk : 3 ≤ k) : gco (2 : ℂ) k = 0 := by
  obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact (gco_two_sum k (by omega)).2

/-! ## `EEVec` on a Schur state with nonnegative index -/

theorem EEVec_vSchur_nonneg (α' α : (latP 1).carrier) (s w : ℕ) :
    EEVec (latP 1) α' (s : ℤ) (vSchur (latP 1) α w) =
      ∑ k ∈ range (w + 1), gco (((latP 1).form α α' : ℤ) : ℂ) k •
        (vSchur (latP 1) α' (s + k) * vSchur (latP 1) α (w - k)) := by
  rw [WpC2.EEVec_eq_weight_bounded_sum' (latP 1) α' _
    (Screen.vSchur_mem_gradingWN (latP 1) α w)]
  rw [show max (0 : ℤ) (s : ℤ) = s by omega]
  symm
  refine Finset.sum_nbij' (fun k => (s : ℤ) + k) (fun m => (m - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_range] at hk
    simp only [mem_Icc]
    omega
  · intro m hm
    simp only [mem_Icc] at hm
    simp only [mem_range]
    omega
  · intro k hk; simp
  · intro m hm
    simp only [mem_Icc] at hm
    dsimp only
    omega
  · intro k hk
    have hk' : k < w + 1 := mem_range.mp hk
    rw [show ((s : ℤ) + k).toNat = s + k by omega, show ((s : ℤ) + k - s).toNat = k by omega,
      aExpVec_vSchur (latP 1) (latP_posDef 1 le_rfl) α α' w k (by omega), mul_smul_comm]

/-! ## `f₀² e^{6α}` -/

/-- `f₀ (S₁₁ e^{5α}) = ε (S₉S₁₁ - 2S₁₀S₁₀ + S₁₁S₉) e^{4α}`. -/
def q20 : FockN (rank (latP 1)) :=
  vSchur (latP 1) (-1 : ℤ) 9 * vSchur (latP 1) (-1 : ℤ) 11 -
    (2 : ℂ) • (vSchur (latP 1) (-1 : ℤ) 10 * vSchur (latP 1) (-1 : ℤ) 10) +
    vSchur (latP 1) (-1 : ℤ) 11 * vSchur (latP 1) (-1 : ℤ) 9

theorem EEVec_q20 : EEVec (latP 1) (-1 : ℤ) ((9 : ℕ) : ℤ) (vSchur (latP 1) (-1 : ℤ) 11) = q20 := by
  rw [EEVec_vSchur_nonneg, latP_form]
  have hf : ((2 * ((1 : ℕ) : ℤ) * (-1 : ℤ) * (-1 : ℤ) : ℤ) : ℂ) = 2 := by norm_num
  rw [hf]
  rw [Finset.sum_range_succ' _ 11, Finset.sum_range_succ' _ 10, Finset.sum_range_succ' _ 9]
  rw [Finset.sum_eq_zero (fun k hk => by rw [gco_two_ge (k + 1 + 1 + 1) (by omega), zero_smul])]
  rw [gco_two_two, gco_two_one, gco_zero, q20]
  simp only [one_smul, zero_add]
  norm_num
  module

theorem fo_state5 :
    fo (latStateGen (latP 1) (vSchur (latP 1) (-1 : ℤ) 11) ((5 : ℤ))) =
      latticeCocycle (latP 1) (-1 : ℤ) (5 : ℤ) • latStateGen (latP 1) q20 ((4 : ℤ)) := by
  rw [fo_eq]
  change V2v.smul (latChargeGen (latP 1) (-1 : ℤ)) 0 _ = _
  rw [smul_chargeGen_state, latP_form]
  rw [show -(0 : ℤ) - 1 - 2 * ((1 : ℕ) : ℤ) * (-1 : ℤ) * (5 : ℤ) = ((9 : ℕ) : ℤ) by norm_num,
    EEVec_q20]
  rfl

theorem wv_two_six : wv 6 2 = ((1 / 132 : ℂ) * (latticeCocycle (latP 1) (-1 : ℤ) (6 : ℤ) *
    latticeCocycle (latP 1) (-1 : ℤ) (5 : ℤ))) • latStateGen (latP 1) q20 ((4 : ℤ)) := by
  rw [wv, cnk, vn, pow_two, Module.End.mul_apply]
  have h1 := fo_chargeGen 6 (by norm_num)
  simp only [Nat.cast_ofNat] at h1
  rw [show ((6 : ℕ) : ℤ) = (6 : ℤ) by rfl, h1, map_smul,
    show (((6 : ℤ) - 1 : ℤ)) = (5 : ℤ) by norm_num,
    show 2 * 6 - 1 = 11 by rfl, fo_state5, smul_smul, smul_smul]
  congr 1
  norm_num [Nat.factorial]
  ring

/-! ## The base value -/

/-- `g_k = C(k+11, 11)`, the coefficients of `(1-x)^{-12}`. -/
theorem gco_m12 (k : ℕ) : gco (((latP 1).form (-1 : ℤ) (6 : ℤ) : ℤ) : ℂ) k =
    (((k + 11).choose 11 : ℕ) : ℂ) := by
  rw [latP_form, ← gco_neg 11 k]
  congr 1
  norm_num

theorem aExpVec_q20 : aExpVec (latP 1) (6 : ℤ) 20 q20 =
    ((2 : ℂ) * ((167960 : ℂ) * 705432 - 352716 * 352716)) • vacuumN (rank (latP 1)) := by
  rw [q20, map_add, map_sub, map_smul,
    show (20 : ℕ) = 9 + 11 by rfl,
    aExpVec_vSchur_mul (latP 1) (latP_posDef 1 le_rfl),
    show (9 + 11 : ℕ) = 10 + 10 by rfl,
    aExpVec_vSchur_mul (latP 1) (latP_posDef 1 le_rfl),
    show (10 + 10 : ℕ) = 11 + 9 by rfl,
    aExpVec_vSchur_mul (latP 1) (latP_posDef 1 le_rfl),
    gco_m12, gco_m12, gco_m12]
  rw [smul_smul, ← sub_smul, ← add_smul]
  congr 1
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]

/-- The base coefficient `e^{6α}₍₋₂₉₎ w_{6,2} = K · e^{10α}`. -/
def kappa2 : ℂ := ((1 / 132 : ℂ) * (latticeCocycle (latP 1) (-1 : ℤ) (6 : ℤ) *
    latticeCocycle (latP 1) (-1 : ℤ) (5 : ℤ))) * (latticeCocycle (latP 1) (6 : ℤ) (4 : ℤ) *
    ((2 : ℂ) * ((167960 : ℂ) * 705432 - 352716 * 352716)))

theorem kappa2_ne_zero : kappa2 ≠ 0 := by
  unfold kappa2
  refine mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero (cocycle_ne_zero _ _)
    (cocycle_ne_zero _ _))) (mul_ne_zero (cocycle_ne_zero _ _) (by norm_num))

theorem w60_w62 : V2v.smul (wv 6 0) (-29) (wv 6 2) =
    kappa2 • latChargeGen (latP 1) ((10 : ℕ) : ℤ) := by
  rw [wv_two_six, PreVertexAlgebra.smul_smul_right, wv_zero]
  change _ • V2v.smul (latChargeGen (latP 1) ((6 : ℕ) : ℤ)) (-29)
    (latStateGen (latP 1) q20 ((4 : ℤ))) = _
  rw [smul_chargeGen_state, latP_form]
  simp only [Nat.cast_ofNat]
  have hq : q20 ∈ gradingWN (rank (latP 1)) 20 := by
    have h9 := Screen.vSchur_mem_gradingWN (latP 1) (-1 : ℤ) 9
    have h10 := Screen.vSchur_mem_gradingWN (latP 1) (-1 : ℤ) 10
    have h11 := Screen.vSchur_mem_gradingWN (latP 1) (-1 : ℤ) 11
    rw [mem_gradingWN] at h9 h10 h11
    have p1 : vSchur (latP 1) (-1 : ℤ) 9 * vSchur (latP 1) (-1 : ℤ) 11 ∈
        gradingWN (rank (latP 1)) 20 := by rw [mem_gradingWN]; exact h9.mul h11
    have p2 : vSchur (latP 1) (-1 : ℤ) 10 * vSchur (latP 1) (-1 : ℤ) 10 ∈
        gradingWN (rank (latP 1)) 20 := by rw [mem_gradingWN]; exact h10.mul h10
    have p3 : vSchur (latP 1) (-1 : ℤ) 11 * vSchur (latP 1) (-1 : ℤ) 9 ∈
        gradingWN (rank (latP 1)) 20 := by rw [mem_gradingWN]; exact h11.mul h9
    rw [q20]
    exact Submodule.add_mem _ (Submodule.sub_mem _ p1 (Submodule.smul_mem _ _ p2)) p3
  rw [show -(-29 : ℤ) - 1 - 2 * ((1 : ℕ) : ℤ) * (6 : ℤ) * (4 : ℤ) = -((20 : ℕ) : ℤ) by
    norm_num]
  rw [WpC2.EEVec_eq_weight_bounded_sum' (latP 1) _ _ hq]
  rw [show max (0 : ℤ) (-((20 : ℕ) : ℤ)) = 0 by norm_num,
    show ((20 : ℕ) : ℤ) + (-((20 : ℕ) : ℤ)) = 0 by ring, Finset.Icc_self, Finset.sum_singleton,
    show ((0 : ℤ) - (-((20 : ℕ) : ℤ))).toNat = 20 by rfl,
    show (0 : ℤ).toNat = 0 by rfl, vSchur_zero, one_mul, aExpVec_q20, latStateGen_csmul,
    smul_smul, smul_smul]
  rw [show (6 : ℤ) + (4 : ℤ) = (10 : ℤ) by norm_num]
  change _ = kappa2 • latStateGen (latP 1) (vacuumN _) (10 : ℤ)
  rw [← latStateGen_csmul, ← latStateGen_csmul]
  congr 2
  unfold kappa2
  ring


/-! ## `f₀` on the multiplet, and the vanishing products -/

theorem fo_wv (n k : ℕ) (hk : k < 2 * n) : fo (wv n k) = ((2 * n - k : ℕ) : ℂ) • wv n (k + 1) := by
  rw [wv, wv, map_smul, vn, vn, pow_succ', Module.End.mul_apply, smul_smul]
  congr 1
  unfold cnk
  have hf : ((2 * n - k).factorial : ℂ) =
      ((2 * n - k : ℕ) : ℂ) * ((2 * n - (k + 1)).factorial : ℂ) := by
    rw [show 2 * n - k = (2 * n - (k + 1)) + 1 by omega, Nat.factorial_succ]
    push_cast; ring
  rw [hf]
  ring

theorem w60_w60 : V2v.smul (wv 6 0) (-29) (wv 6 0) = 0 := by
  rw [wv_zero]
  change V2v.smul (latChargeGen (latP 1) ((6 : ℕ) : ℤ)) (-29)
    (latStateGen (latP 1) (vacuumN _) ((6 : ℕ) : ℤ)) = 0
  rw [smul_chargeGen_state, EEVec_vacuum, latP_form, if_neg (by norm_num)]
  simp [latStateGen]

theorem w60_w61 : V2v.smul (wv 6 0) (-29) (wv 6 1) = 0 := by
  rw [wv_one 6 (by norm_num), fo_chargeGen 6 (by norm_num), smul_smul,
    PreVertexAlgebra.smul_smul_right, wv_zero]
  change _ • V2v.smul (latChargeGen (latP 1) ((6 : ℕ) : ℤ)) (-29)
    (latStateGen (latP 1) (vSchur (latP 1) (-1 : ℤ) (2 * 6 - 1)) (((6 : ℕ) : ℤ) - 1 : ℤ)) = 0
  rw [smul_chargeGen_state]
  have hE := Screen.EEVec_mem_gradingZN (latP 1) ((6 : ℕ) : ℤ)
    (-(-29 : ℤ) - 1 - (latP 1).form ((6 : ℕ) : ℤ) (((6 : ℕ) : ℤ) - 1 : ℤ))
    (mem_gradingZN_of_gradingWN (Screen.vSchur_mem_gradingWN (latP 1) (-1 : ℤ) (2 * 6 - 1)))
  rw [gradingZN_of_neg (by rw [latP_form]; norm_num), Submodule.mem_bot] at hE
  rw [hE]
  simp [latStateGen]

theorem w61_w60 : V2v.smul (wv 6 1) (-29) (wv 6 0) = 0 := by
  have h := congrArg fo w60_w60
  rw [fo_smul, fo_wv0 6 (by norm_num), map_zero, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, w60_w61, smul_zero, add_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

theorem w61_w61 : V2v.smul (wv 6 1) (-29) (wv 6 1) =
    (-(11 / 12 : ℂ) * kappa2) • latChargeGen (latP 1) ((10 : ℕ) : ℤ) := by
  have h := congrArg fo w60_w61
  rw [fo_smul, fo_wv0 6 (by norm_num), fo_wv 6 1 (by norm_num), map_zero,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, w60_w62, smul_smul] at h
  have h12 : ((2 * 6 : ℕ) : ℂ) ≠ 0 := by norm_num
  have hx : V2v.smul (wv 6 1) (-29) (wv 6 1) =
      (((2 * 6 : ℕ) : ℂ))⁻¹ • ((((2 * 6 : ℕ) : ℂ)) • V2v.smul (wv 6 1) (-29) (wv 6 1)) := by
    rw [smul_smul, inv_mul_cancel₀ h12, one_smul]
  rw [hx, eq_neg_of_add_eq_zero_left h, smul_neg, smul_smul, ← neg_smul]
  congr 1
  norm_num
  ring

theorem w62_w60 : V2v.smul (wv 6 2) (-29) (wv 6 0) =
    kappa2 • latChargeGen (latP 1) ((10 : ℕ) : ℤ) := by
  have h := congrArg fo w61_w60
  rw [fo_smul, fo_wv0 6 (by norm_num), fo_wv 6 1 (by norm_num), map_zero,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, w61_w61, smul_smul] at h
  have h11 : ((2 * 6 - 1 : ℕ) : ℂ) ≠ 0 := by norm_num
  have hx : V2v.smul (wv 6 (1 + 1)) (-29) (wv 6 0) =
      (((2 * 6 - 1 : ℕ) : ℂ))⁻¹ • ((((2 * 6 - 1 : ℕ) : ℂ)) •
        V2v.smul (wv 6 (1 + 1)) (-29) (wv 6 0)) := by
    rw [smul_smul, inv_mul_cancel₀ h11, one_smul]
  rw [show (2 : ℕ) = 1 + 1 by rfl, hx, eq_neg_of_add_eq_zero_left h, smul_neg, smul_smul,
    ← neg_smul]
  congr 1
  norm_num
  ring

/-! ## The second channel on the multiplets -/

/-- The second-transvectant coefficient of `x^{12-i}y^i` and `x^{12-j}y^j`. -/
def tau2 (i j : ℕ) : ℂ :=
  (12 - (i : ℂ)) * (11 - i) * j * (j - 1) - 2 * (12 - i) * i * (12 - j) * j +
    i * (i - 1) * (12 - j) * (11 - j)

/-- `μ = K / 264`. -/
def mu2 : ℂ := kappa2 / 264

theorem mu2_ne_zero : mu2 ≠ 0 := div_ne_zero kappa2_ne_zero (by norm_num)

theorem tau2_rec (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    tau2 i j * ((i : ℂ) + j - 2) = i * tau2 (i - 1) j + j * tau2 i (j - 1) := by
  unfold tau2
  push_cast [Nat.cast_sub hi, Nat.cast_sub hj]
  ring

theorem tau2_rec_left (j : ℕ) (hj : 1 ≤ j) :
    tau2 0 j * ((j : ℂ) - 2) = j * tau2 0 (j - 1) := by
  unfold tau2
  push_cast [Nat.cast_sub hj]
  ring

theorem tau2_rec_right (i : ℕ) (hi : 1 ≤ i) :
    tau2 i 0 * ((i : ℂ) - 2) = i * tau2 (i - 1) 0 := by
  unfold tau2
  push_cast [Nat.cast_sub hi]
  ring

/-- **The second channel `Prim₃₆ × Prim₃₆ → Prim₁₀₀` is the second transvectant.** -/
theorem second_wv : ∀ t : ℕ, ∀ i j : ℕ, i + j = t → 2 ≤ t → t ≤ 22 → i ≤ 12 → j ≤ 12 →
    V2v.smul (wv 6 i) (-29) (wv 6 j) - (mu2 * tau2 i j) • wv 10 (i + j - 2) ∈
      lowerDesc V2v (((10 : ℕ) : ℤ) ^ 2) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro i j hij ht ht22 hi hj
  by_cases ht2 : t = 2
  · subst ht2
    rcases (show (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 0) by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [w60_w62, show 0 + 2 - 2 = 0 by rfl, wv_zero, mu2, tau2, ← sub_smul]
      norm_num
    · rw [w61_w61, show 1 + 1 - 2 = 0 by rfl, wv_zero, mu2, tau2, ← sub_smul]
      norm_num
      rw [show -(11 / 12 * kappa2) + kappa2 / 264 * 242 = 0 by ring, zero_smul]
      exact Submodule.zero_mem _
    · rw [w62_w60, show 2 + 0 - 2 = 0 by rfl, wv_zero, mu2, tau2, ← sub_smul]
      norm_num
  · have ht3 : 3 ≤ t := by omega
    set Φ := fun x y : ℕ => V2v.smul (wv 6 x) (-29) (wv 6 y) -
      (mu2 * tau2 x y) • wv 10 (x + y - 2) with hΦ
    change Φ i j ∈ _
    have hgr : Φ i j ∈ V2v.grading (((10 : ℕ) : ℤ) ^ 2) := by
      refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ (wv_grading _ _))
      have h := V2v.smul_mem_grading (wv_grading 6 i) (wv_grading 6 j) (-29)
      convert h using 2
    have hho : ho (Φ i j) = (((2 * 10 : ℕ) : ℂ) - 2 * ((t - 2 : ℕ) : ℂ)) • Φ i j := by
      subst hij
      simp only [hΦ]
      rw [map_sub, map_smul, ho_smul, ho_wv, ho_wv, ho_wv, PreVertexAlgebra.smul_smul_left,
        PreVertexAlgebra.smul_smul_right]
      push_cast [Nat.cast_sub (show 2 ≤ i + j by omega)]
      module
    have heo : eo (Φ i j) ∈ lowerDesc V2v (((10 : ℕ) : ℤ) ^ 2) := by
      have hsplit : eo (Φ i j) =
          (if i = 0 then 0 else (eps1 * (i : ℂ)) • Φ (i - 1) j) +
          (if j = 0 then 0 else (eps1 * (j : ℂ)) • Φ i (j - 1)) := by
        simp only [hΦ]
        rw [map_sub, map_smul, eo_smul, eo_wv' 6 i (by omega), eo_wv' 6 j (by omega),
          eo_wv' 10 (i + j - 2) (by omega), if_neg (show ¬ i + j - 2 = 0 by omega)]
        by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
        · omega
        · subst hi0
          simp only [if_true, if_neg hj0, zero_add, PreVertexAlgebra.smul_zero_left,
            PreVertexAlgebra.smul_smul_right, show j - 1 - 2 = j - 2 - 1 by omega]
          unfold tau2
          push_cast [Nat.cast_sub (show 2 ≤ j by omega), Nat.cast_sub (show 1 ≤ j by omega)]
          module
        · subst hj0
          simp only [if_true, if_neg hi0, add_zero, PreVertexAlgebra.smul_zero_right,
            PreVertexAlgebra.smul_smul_left, show i - 1 - 2 = i - 2 - 1 by omega]
          unfold tau2
          push_cast [Nat.cast_sub (show 2 ≤ i by omega), Nat.cast_sub (show 1 ≤ i by omega)]
          module
        · simp only [if_neg hi0, if_neg hj0, PreVertexAlgebra.smul_smul_left,
            PreVertexAlgebra.smul_smul_right,
            show i - 1 + j - 2 = i + j - 2 - 1 by omega,
            show i + (j - 1) - 2 = i + j - 2 - 1 by omega]
          unfold tau2
          push_cast [Nat.cast_sub (show 2 ≤ i + j by omega),
            Nat.cast_sub (show 1 ≤ i by omega), Nat.cast_sub (show 1 ≤ j by omega)]
          module
      rw [hsplit]
      refine Submodule.add_mem _ ?_ ?_
      · split_ifs with hi0
        · exact Submodule.zero_mem _
        · exact Submodule.smul_mem _ _
            (ih (i - 1 + j) (by omega) (i - 1) j rfl (by omega) (by omega) (by omega) hj)
      · split_ifs with hj0
        · exact Submodule.zero_mem _
        · exact Submodule.smul_mem _ _
            (ih (i + (j - 1)) (by omega) i (j - 1) rfl (by omega) (by omega) hi (by omega))
    exact ekernel 10 (t - 2) (by omega) hgr (by rw [hho]) heo


/-! ## The corners and the full statement -/

theorem eo_pair (i j : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 12) (hj : 1 ≤ j) (hj' : j ≤ 12) :
    eo (V2v.smul (wv 6 i) (-29) (wv 6 j)) =
      (eps1 * (i : ℂ)) • V2v.smul (wv 6 (i - 1)) (-29) (wv 6 j) +
      (eps1 * (j : ℂ)) • V2v.smul (wv 6 i) (-29) (wv 6 (j - 1)) := by
  rw [eo_smul, eo_wv' 6 i (by omega), eo_wv' 6 j (by omega), if_neg (by omega), if_neg (by omega),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]

theorem ho_pair (i j : ℕ) :
    ho (V2v.smul (wv 6 i) (-29) (wv 6 j)) =
      (((2 * 10 : ℕ) : ℂ) - 2 * ((i + j - 2 : ℤ) : ℂ)) • V2v.smul (wv 6 i) (-29) (wv 6 j) := by
  rw [ho_smul, ho_wv, ho_wv, PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  push_cast
  module

theorem grading_pair (i j : ℕ) :
    V2v.smul (wv 6 i) (-29) (wv 6 j) ∈ V2v.grading (((10 : ℕ) : ℤ) ^ 2) := by
  have h := V2v.smul_mem_grading (wv_grading 6 i) (wv_grading 6 j) (-29)
  convert h using 2

theorem second_corner_a : V2v.smul (wv 6 11) (-29) (wv 6 12) ∈
    lowerDesc V2v (((10 : ℕ) : ℤ) ^ 2) := by
  have h1 := second_wv 22 10 12 rfl (by norm_num) le_rfl (by norm_num) le_rfl
  have h2 := second_wv 22 11 11 rfl (by norm_num) le_rfl (by norm_num) (by norm_num)
  have he : eo (V2v.smul (wv 6 11) (-29) (wv 6 12)) =
      (eps1 * (11 : ℂ)) • (V2v.smul (wv 6 10) (-29) (wv 6 12) -
        (mu2 * tau2 10 12) • wv 10 (10 + 12 - 2)) +
      (eps1 * (12 : ℂ)) • (V2v.smul (wv 6 11) (-29) (wv 6 11) -
        (mu2 * tau2 11 11) • wv 10 (11 + 11 - 2)) := by
    rw [eo_pair 11 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num [tau2]
    module
  refine ekernel 10 21 (by norm_num) (grading_pair 11 12) ?_ ?_
  · rw [ho_pair]; norm_num
  · rw [he]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

theorem second_corner_b : V2v.smul (wv 6 12) (-29) (wv 6 11) ∈
    lowerDesc V2v (((10 : ℕ) : ℤ) ^ 2) := by
  have h1 := second_wv 22 11 11 rfl (by norm_num) le_rfl (by norm_num) (by norm_num)
  have h2 := second_wv 22 12 10 rfl (by norm_num) le_rfl le_rfl (by norm_num)
  have he : eo (V2v.smul (wv 6 12) (-29) (wv 6 11)) =
      (eps1 * (12 : ℂ)) • (V2v.smul (wv 6 11) (-29) (wv 6 11) -
        (mu2 * tau2 11 11) • wv 10 (11 + 11 - 2)) +
      (eps1 * (11 : ℂ)) • (V2v.smul (wv 6 12) (-29) (wv 6 10) -
        (mu2 * tau2 12 10) • wv 10 (12 + 10 - 2)) := by
    rw [eo_pair 12 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num [tau2]
    module
  refine ekernel 10 21 (by norm_num) (grading_pair 12 11) ?_ ?_
  · rw [ho_pair]; norm_num
  · rw [he]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

theorem second_corner_c : V2v.smul (wv 6 12) (-29) (wv 6 12) ∈
    lowerDesc V2v (((10 : ℕ) : ℤ) ^ 2) := by
  refine ekernel 10 22 (by norm_num) (grading_pair 12 12) ?_ ?_
  · rw [ho_pair]; norm_num
  · rw [eo_pair 12 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ second_corner_a)
      (Submodule.smul_mem _ _ second_corner_b)

theorem tau2_zero_of_le (i j : ℕ) (h : i + j ≤ 1) : tau2 i j = 0 := by
  rcases (show (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num [tau2]

theorem tau2_zero_of_ge (i j : ℕ) (hi : i ≤ 12) (hj : j ≤ 12) (h : 23 ≤ i + j) : tau2 i j = 0 := by
  rcases (show (i = 11 ∧ j = 12) ∨ (i = 12 ∧ j = 11) ∨ (i = 12 ∧ j = 12) by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num [tau2]

/-- The second channel on every pair of multiplet vectors. -/
theorem second_wv_all (i j : ℕ) (hi : i ≤ 12) (hj : j ≤ 12) :
    V2v.smul (wv 6 i) (-29) (wv 6 j) - (mu2 * tau2 i j) • wv 10 (i + j - 2) ∈
      lowerDesc V2v (((10 : ℕ) : ℤ) ^ 2) := by
  by_cases hlo : i + j ≤ 1
  · rw [tau2_zero_of_le i j hlo, mul_zero, zero_smul, sub_zero]
    rcases (show (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [w60_w60]; exact Submodule.zero_mem _
    · rw [w60_w61]; exact Submodule.zero_mem _
    · rw [w61_w60]; exact Submodule.zero_mem _
  by_cases hhi : 23 ≤ i + j
  · rw [tau2_zero_of_ge i j hi hj hhi, mul_zero, zero_smul, sub_zero]
    rcases (show (i = 11 ∧ j = 12) ∨ (i = 12 ∧ j = 11) ∨ (i = 12 ∧ j = 12) by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact second_corner_a
    · exact second_corner_b
    · exact second_corner_c
  exact second_wv (i + j) i j rfl (by omega) (by omega) hi hj

/-! ## Binary forms -/

/-- The bilinear map realizing the second channel on binary forms of degree `12`:
`x^{12-i}y^i ⊗ x^{12-j}y^j ↦ τ(i,j) x^{22-i-j} y^{i+j-2}`. -/
def B2 : P2 →ₗ[ℂ] P2 →ₗ[ℂ] P2 :=
  (basisMonomials (Fin 2) ℂ).constr ℂ fun e => (basisMonomials (Fin 2) ℂ).constr ℂ fun f =>
    tau2 (e 1) (f 1) • (X 0 ^ (22 - (e 1 + f 1)) * X 1 ^ (e 1 + f 1 - 2))

theorem B2_monomial (e f : Fin 2 →₀ ℕ) :
    B2 (monomial e 1) (monomial f 1) =
      tau2 (e 1) (f 1) • (X 0 ^ (22 - (e 1 + f 1)) * X 1 ^ (e 1 + f 1 - 2)) := by
  have he : (monomial e (1 : ℂ) : P2) = basisMonomials (Fin 2) ℂ e := by
    rw [coe_basisMonomials]
  have hf : (monomial f (1 : ℂ) : P2) = basisMonomials (Fin 2) ℂ f := by
    rw [coe_basisMonomials]
  rw [he, hf, B2, (basisMonomials (Fin 2) ℂ).constr_basis, (basisMonomials (Fin 2) ℂ).constr_basis]

theorem Tb_B2_monomial {e f : Fin 2 →₀ ℕ} (he : e 0 + e 1 = 12) (hf : f 0 + f 1 = 12) :
    Tb (B2 (monomial e 1) (monomial f 1)) = tau2 (e 1) (f 1) • wv 10 (e 1 + f 1 - 2) := by
  rw [B2_monomial, map_smul]
  by_cases h1 : e 1 + f 1 ≤ 1
  · rw [tau2_zero_of_le _ _ h1, zero_smul, zero_smul]
  by_cases h2 : 23 ≤ e 1 + f 1
  · rw [tau2_zero_of_ge _ _ (by omega) (by omega) h2, zero_smul, zero_smul]
  rw [Tb_xy _ _ 10 (by omega)]

/-- **The second channel on binary forms**: `Tb(P)₍₋₂₉₎Tb(Q) ≡ μ Tb(B2 P Q)`. -/
theorem second_bin {P Q : P2} (hP : P ∈ binDeg 12) (hQ : Q ∈ binDeg 12) :
    V2v.smul (Tb P) (-29) (Tb Q) - mu2 • Tb (B2 P Q) ∈ lowerDesc V2v (((10 : ℕ) : ℤ) ^ 2) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    induction hQ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      simp only [Set.mem_setOf_eq] at he hf
      rw [Tb_B2_monomial he hf, Tb_monomial, Tb_monomial, one_smul, one_smul,
        tbm_of_deg (n := 6) (by omega), tbm_of_deg (n := 6) (by omega), smul_smul]
      exact second_wv_all (e 1) (f 1) (by omega) (by omega)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, PreVertexAlgebra.smul_add_right, map_add, map_add, smul_add]
      convert Submodule.add_mem _ hy hz using 1; abel
    | smul c y _ hy =>
      rw [map_smul, PreVertexAlgebra.smul_smul_right, map_smul, map_smul, smul_comm, ← smul_sub]
      exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, PreVertexAlgebra.smul_add_left, map_add, LinearMap.add_apply, map_add, smul_add]
    convert Submodule.add_mem _ hx hy using 1; abel
  | smul c x _ hx =>
    rw [map_smul, PreVertexAlgebra.smul_smul_left, map_smul, LinearMap.smul_apply, map_smul,
      smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ _ hx

end VOA.Classification.COne.OrbIco
