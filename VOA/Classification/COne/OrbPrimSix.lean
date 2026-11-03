import VOA.Classification.COne.OrbPrimBinary
import VOA.Examples.TripletWpTwoMixed

/-! # OrbPrim (N): the second channel at weight `36`

For `v = T₂(I₄) ∈ Prim₁₆`, `u = T₂(I₃) ∈ Prim₉` the product `v₍₋₁₂₎u` (weight `36`) is,
modulo lower descendants, a NONZERO multiple of `T₂(I₆)`:

* `second_wv`: `w_{4,i}₍₋₁₂₎w_{3,j} ≡ λ(8j - 6i) w_{6,i+j-1}` for `i ≤ 8`, `j ≤ 6`, `i + j ≥ 1`
  (the first transvectant `P_x Q_y - P_y Q_x` of binary forms), by the same `e₀`-kernel induction
  as the top channel, with base `w_{4,0}₍₋₁₂₎w_{3,1} = 8λ e^{6α}`;
* `kappa_ne_zero`: `λ ≠ 0`, from the lattice computation
  `e^{4α}₍₋₁₂₎ f₀ e^{3α} = ε·g·e^{6α}`, `g = (1-x)^{-8}|_{x⁵} = 792` (`gco_eight_five`);
* `six_T2`: the `six` field of `T2Residual`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbPrim
open VOA VertexOperatorAlgebra OrbSpan VOA.LatGen VOA.LatGen.Triplet HeisenbergN
  OrbRat6 VOA.IntegralLattice MvPolynomial OrbC2b

/-! ## `E⁺` on Schur states -/

/-- Coefficients of `(1 - x)^{P}`: `g₀ = 1`, `(k+1) g_{k+1} = -P Σ_{m ≤ k} g_{k-m}`. -/
def gco (P : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => ((k + 1 : ℂ))⁻¹ * ∑ m : Fin (k + 1), (-P) * gco P (k - m)
decreasing_by omega

theorem gco_zero (P : ℂ) : gco P 0 = 1 := by rw [gco]

theorem gco_succ (P : ℂ) (k : ℕ) :
    gco P (k + 1) = ((k + 1 : ℂ))⁻¹ * ∑ m ∈ Finset.range (k + 1), (-P) * gco P (k - m) := by
  rw [gco, Finset.sum_range (fun m => (-P) * gco P (k - m))]

theorem aExpVec_vSchur (L : IntegralLattice) (hPos : L.PosDef) (α β : L.carrier) (N : ℕ) :
    ∀ k ≤ N, aExpVec L β k (vSchur L α N) =
      gco ((L.form α β : ℤ) : ℂ) k • vSchur L α (N - k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  rcases k with _ | k
  · simp [aExpVec_zero, gco_zero]
  · have hterm : ∀ m ∈ Finset.range (k + 1),
        ((-(chargeOsc L β ((m : ℤ) + 1))).comp (aExpVec L β (k - m))) (vSchur L α N) =
          ((-((L.form α β : ℤ) : ℂ)) * gco ((L.form α β : ℤ) : ℂ) (k - m)) •
            vSchur L α (N - (k + 1)) := by
      intro m hm
      have hm' := Finset.mem_range.mp hm
      rw [LinearMap.comp_apply, LinearMap.neg_apply, ih (k - m) (by omega) (by omega), map_smul]
      have hc := WpC2.chargeOsc_vSchur L hPos α β (m + 1) (N - (k - m)) (by omega)
      push_cast at hc
      rw [hc, if_pos (by omega), smul_smul,
        show N - (k - m) - (m + 1) = N - (k + 1) by omega, ← neg_smul]
      congr 1
      ring
    rw [aExpVec_succ, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
    rw [Finset.sum_congr rfl (fun m hm => by exact_mod_cast hterm m hm), ← Finset.sum_smul,
      smul_smul, gco_succ]
    push_cast
    rfl

theorem gco_eight_five : gco (-8) 5 = 792 := by
  simp only [gco_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [gco_zero]

/-! ## The charged products needed at weight `36` -/

theorem Y_chargeGen (a : ℤ) : V2v.Y (latChargeGen (latP 1) a) = Yeαvec (latP 1) a := by
  have hw := YfullGen_word (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) [] a
  rw [YwordLatGen_nil] at hw
  exact hw

theorem smul_chargeGen_state (a b : ℤ) (n : ℤ) (q : FockN (rank (latP 1))) :
    V2v.smul (latChargeGen (latP 1) a) n (latStateGen (latP 1) q b) =
      latticeCocycle (latP 1) a b •
        latStateGen (latP 1) (EEVec (latP 1) a (-n - 1 - (latP 1).form a b) q) (a + b) := by
  rw [PreVertexAlgebra.smul_def, Y_chargeGen, mode_apply, Yeαvec_tmul]
  rfl

theorem fo_chargeGen_three :
    fo (latChargeGen (latP 1) (3 : ℤ)) = latticeCocycle (latP 1) (-1 : ℤ) (3 : ℤ) •
      latStateGen (latP 1) (vSchur (latP 1) (-1 : ℤ) 5) (2 : ℤ) := by
  rw [fo_eq]
  change V2v.smul (latChargeGen (latP 1) (-1 : ℤ)) 0
    (latStateGen (latP 1) (vacuumN _) (3 : ℤ)) = _
  rw [smul_chargeGen_state, EEVec_vacuum, latP_form, if_pos (by norm_num)]
  norm_num
  rfl

theorem w40_w30 : V2v.smul (wv 4 0) (-12) (wv 3 0) = 0 := by
  rw [wv_zero, wv_zero]
  change V2v.smul (latChargeGen (latP 1) ((4 : ℕ) : ℤ)) (-12)
    (latStateGen (latP 1) (vacuumN _) ((3 : ℕ) : ℤ)) = 0
  rw [smul_chargeGen_state, EEVec_vacuum, latP_form, if_neg (by norm_num)]
  simp [latStateGen]

/-- The `e^{6α}`-coefficient of `w_{4,0}₍₋₁₂₎ w_{3,1}`. -/
def kappa6 : ℂ :=
  (1 / 6 : ℂ) * (latticeCocycle (latP 1) (-1 : ℤ) (3 : ℤ) *
    (latticeCocycle (latP 1) (4 : ℤ) (2 : ℤ) * 792))

theorem wv31 : wv 3 1 = (1 / 6 : ℂ) • fo (latChargeGen (latP 1) (3 : ℤ)) := by
  rw [wv, cnk, vn]
  norm_num [Nat.factorial]

theorem EEVec_four_vSchur :
    EEVec (latP 1) (4 : ℤ) (-5) (vSchur (latP 1) (-1 : ℤ) 5) =
      (792 : ℂ) • vacuumN (rank (latP 1)) := by
  rw [WpC2.EEVec_eq_weight_bounded_sum' (latP 1) (4 : ℤ) _
    (Screen.vSchur_mem_gradingWN (latP 1) (-1 : ℤ) 5)]
  rw [show max (0 : ℤ) (-5) = 0 by norm_num, show ((5 : ℕ) : ℤ) + (-5) = 0 by norm_num,
    Finset.Icc_self, Finset.sum_singleton, show ((0 : ℤ) - (-5)).toNat = 5 by rfl,
    show (0 : ℤ).toNat = 0 by rfl, vSchur_zero, one_mul,
    aExpVec_vSchur (latP 1) (latP_posDef 1 le_rfl) _ _ 5 5 le_rfl, Nat.sub_self, vSchur_zero,
    latP_form]
  have : (((2 * ((1 : ℕ) : ℤ) * (-1 : ℤ) * (4 : ℤ) : ℤ)) : ℂ) = -8 := by norm_num
  rw [this, gco_eight_five]
  rfl

theorem kappa6_ne_zero : kappa6 ≠ 0 := by
  have h1 := latticeCocycle_sq (latP 1) (-1 : ℤ) (3 : ℤ)
  have h2 := latticeCocycle_sq (latP 1) (4 : ℤ) (2 : ℤ)
  unfold kappa6
  refine mul_ne_zero (by norm_num) (mul_ne_zero ?_ (mul_ne_zero ?_ (by norm_num)))
  · intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
  · intro h; rw [h, zero_mul] at h2; exact zero_ne_one h2

theorem w40_w31 : V2v.smul (wv 4 0) (-12) (wv 3 1) =
    kappa6 • latChargeGen (latP 1) (6 : ℤ) := by
  rw [wv31, fo_chargeGen_three, smul_smul, PreVertexAlgebra.smul_smul_right, wv_zero]
  change (1 / 6 * latticeCocycle (latP 1) (-1 : ℤ) (3 : ℤ)) •
      V2v.smul (latChargeGen (latP 1) (4 : ℤ)) (-12)
        (latStateGen (latP 1) (vSchur (latP 1) (-1 : ℤ) 5) (2 : ℤ)) = _
  rw [smul_chargeGen_state, latP_form]
  rw [show -(-12 : ℤ) - 1 - 2 * ((1 : ℕ) : ℤ) * (4 : ℤ) * (2 : ℤ) = -5 by norm_num,
    EEVec_four_vSchur, smul_smul]
  rw [show latStateGen (latP 1) ((792 : ℂ) • vacuumN (rank (latP 1))) ((4 : ℤ) + (2 : ℤ)) =
      (792 : ℂ) • latChargeGen (latP 1) (6 : ℤ) from by
    rw [latChargeGen, latStateGen_csmul]; rfl]
  rw [smul_smul, kappa6]
  congr 1
  ring

/-! ## The second channel on the multiplet -/

theorem fo_smul (a : Sp) (n : ℤ) (b : Sp) :
    fo (V2v.smul a n b) = V2v.smul (fo a) n b + V2v.smul a n (fo b) := by
  rw [fo_eq, fo_eq, fo_eq]
  exact zeroMode_leibniz V2v _ a b n

theorem fo_wv0 (n : ℕ) (hn : 1 ≤ n) : fo (wv n 0) = ((2 * n : ℕ) : ℂ) • wv n 1 := by
  rw [wv_zero, wv, cnk, smul_smul]
  have hf : ((2 * n).factorial : ℂ) = ((2 * n : ℕ) : ℂ) * ((2 * n - 1).factorial : ℂ) := by
    rw [show 2 * n = (2 * n - 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [hf, mul_div_assoc', mul_div_mul_right _ _ (by exact_mod_cast Nat.factorial_ne_zero _),
    div_self (by have : (1 : ℕ) ≤ 2 * n := by omega
                 exact_mod_cast (show 2 * n ≠ 0 by omega)), one_smul]
  rfl

theorem w41_w30 : V2v.smul (wv 4 1) (-12) (wv 3 0) =
    (-(6 / 8 : ℂ) * kappa6) • latChargeGen (latP 1) (6 : ℤ) := by
  have h := congrArg fo w40_w30
  rw [fo_smul, fo_wv0 4 (by norm_num), fo_wv0 3 (by norm_num), map_zero,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, w40_w31, smul_smul] at h
  have hx : V2v.smul (wv 4 1) (-12) (wv 3 0) =
      (1 / 8 : ℂ) • ((((2 * 4 : ℕ) : ℂ)) • V2v.smul (wv 4 1) (-12) (wv 3 0)) := by
    rw [smul_smul]; norm_num
  rw [hx, eq_neg_of_add_eq_zero_left h, smul_neg, smul_smul, ← neg_smul]
  congr 1
  push_cast; ring

/-- `λ = κ/8`. -/
def lam6 : ℂ := kappa6 / 8

/-- **The second channel `Prim₁₆ × Prim₉ → Prim₃₆` is the first transvectant.** -/
theorem second_wv : ∀ t : ℕ, ∀ i j : ℕ, i + j = t → 1 ≤ t → t ≤ 13 → i ≤ 8 → j ≤ 6 →
    V2v.smul (wv 4 i) (-12) (wv 3 j) - (lam6 * (8 * (j : ℂ) - 6 * i)) • wv 6 (i + j - 1) ∈
      lowerDesc V2v (((6 : ℕ) : ℤ) ^ 2) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro i j hij ht ht13 hi hj
  by_cases ht1 : t = 1
  · subst ht1
    rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [w40_w31, show 0 + 1 - 1 = 0 by rfl, wv_zero, lam6]
      simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
      rw [← sub_smul]
      norm_num
    · rw [w41_w30, show 1 + 0 - 1 = 0 by rfl, wv_zero, lam6]
      simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
      rw [← sub_smul]
      norm_num
      rw [show -(3 / 4 * kappa6) + kappa6 / 8 * 6 = 0 by ring, zero_smul]
      exact Submodule.zero_mem _
  · have ht2 : 2 ≤ t := by omega
    set Φ := fun a b : ℕ => V2v.smul (wv 4 a) (-12) (wv 3 b) -
      (lam6 * (8 * (b : ℂ) - 6 * a)) • wv 6 (a + b - 1) with hΦ
    change Φ i j ∈ _
    have hgr : Φ i j ∈ V2v.grading (((6 : ℕ) : ℤ) ^ 2) := by
      refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ (wv_grading _ _))
      have h := V2v.smul_mem_grading (wv_grading 4 i) (wv_grading 3 j) (-12)
      convert h using 2
    have hho : ho (Φ i j) = (((2 * 6 : ℕ) : ℂ) - 2 * ((t - 1 : ℕ) : ℂ)) • Φ i j := by
      subst hij
      simp only [hΦ]
      rw [map_sub, map_smul, ho_smul, ho_wv, ho_wv, ho_wv, PreVertexAlgebra.smul_smul_left,
        PreVertexAlgebra.smul_smul_right]
      push_cast [Nat.cast_sub (show 1 ≤ i + j by omega)]
      module
    have heo : eo (Φ i j) ∈ lowerDesc V2v (((6 : ℕ) : ℤ) ^ 2) := by
      have hsplit : eo (Φ i j) =
          (if i = 0 then 0 else (eps1 * (i : ℂ)) • Φ (i - 1) j) +
          (if j = 0 then 0 else (eps1 * (j : ℂ)) • Φ i (j - 1)) := by
        simp only [hΦ]
        rw [map_sub, map_smul, eo_smul, eo_wv' 4 i (by omega), eo_wv' 3 j (by omega),
          eo_wv' 6 (i + j - 1) (by omega), if_neg (show ¬ i + j - 1 = 0 by omega)]
        by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
        · omega
        · subst hi0
          simp only [if_true, if_neg hj0, zero_add, PreVertexAlgebra.smul_zero_left,
            PreVertexAlgebra.smul_smul_right]
          push_cast [Nat.cast_sub (show 1 ≤ j by omega)]
          module
        · subst hj0
          simp only [if_true, if_neg hi0, add_zero, PreVertexAlgebra.smul_zero_right,
            PreVertexAlgebra.smul_smul_left]
          push_cast [Nat.cast_sub (show 1 ≤ i by omega)]
          module
        · simp only [if_neg hi0, if_neg hj0, PreVertexAlgebra.smul_smul_left,
            PreVertexAlgebra.smul_smul_right,
            show i - 1 + j - 1 = i + j - 1 - 1 by omega,
            show i + (j - 1) - 1 = i + j - 1 - 1 by omega]
          push_cast [Nat.cast_sub (show 1 ≤ i + j by omega), Nat.cast_sub (show 1 ≤ i by omega),
            Nat.cast_sub (show 1 ≤ j by omega)]
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
    exact ekernel 6 (t - 1) (by omega) hgr (by rw [hho]) heo

/-! ## The six field for `T2` -/

theorem Tb_xy (a b n : ℕ) (h : a + b = 2 * n) : Tb (X 0 ^ a * X 1 ^ b) = wv n b := by
  rw [binMono_eq, Tb_monomial, one_smul, tbm_of_deg (n := n) (by simp; omega)]
  simp

theorem C_eps1_sq : (MvPolynomial.C eps1 : P2) * MvPolynomial.C eps1 = 1 := by
  rw [← C_mul, eps1_sq, C_1]

theorem psi_X0 : psi (X 0) = X 0 ^ 2 - X 1 ^ 2 := by rw [psi, aeval_X]; rfl
theorem psi_X1 : psi (X 1) = MvPolynomial.C Complex.I * (X 0 ^ 2 + X 1 ^ 2) := by
  rw [psi, aeval_X]; rfl
theorem psi_X2 : psi (X 2) = MvPolynomial.C (-2 * eps1) * (X 0 * X 1) := by
  rw [psi, aeval_X]; rfl

theorem psi_I3 : psi I3 = MvPolynomial.C Complex.I * MvPolynomial.C (-2 * eps1) *
    (X 0 ^ 5 * X 1 ^ 1 - X 0 ^ 1 * X 1 ^ 5) := by
  rw [I3, map_mul, map_mul, psi_X0, psi_X1, psi_X2]
  ring

theorem C_I_pow_two : (MvPolynomial.C Complex.I : P2) ^ 2 = -1 := by
  rw [← C_pow, Complex.I_sq, map_neg, map_one]

theorem C_I_pow_four : (MvPolynomial.C Complex.I : P2) ^ 4 = 1 := by
  rw [← C_pow, Complex.I_pow_four, map_one]

theorem C_eps_pow_two : (MvPolynomial.C (-2 * eps1) : P2) ^ 2 = 4 := by
  rw [← C_pow, show (-2 * eps1) ^ 2 = 4 * (eps1 * eps1) by ring, eps1_sq, mul_one]
  exact map_ofNat _ 4

theorem C_eps_pow_four : (MvPolynomial.C (-2 * eps1) : P2) ^ 4 = 16 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, C_eps_pow_two]; norm_num

theorem psi_I4 : psi I4 = (2 : ℂ) • (X 0 ^ 8 * X 1 ^ 0) + (28 : ℂ) • (X 0 ^ 4 * X 1 ^ 4) +
    (2 : ℂ) • (X 0 ^ 0 * X 1 ^ 8) := by
  rw [I4, map_add, map_add, map_pow, map_pow, map_pow, psi_X0, psi_X1, psi_X2, mul_pow, mul_pow,
    C_I_pow_four, C_eps_pow_four, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, map_ofNat,
    map_ofNat]
  ring

theorem psi_I6 : psi I6 = (2 : ℂ) • (X 0 ^ 12 * X 1 ^ 0) + (-66 : ℂ) • (X 0 ^ 8 * X 1 ^ 4) +
    (-66 : ℂ) • (X 0 ^ 4 * X 1 ^ 8) + (2 : ℂ) • (X 0 ^ 0 * X 1 ^ 12) := by
  rw [I6, map_mul, map_mul, map_sub, map_sub, map_sub, map_pow, map_pow, map_pow, psi_X0,
    psi_X1, psi_X2, mul_pow (MvPolynomial.C Complex.I), mul_pow (MvPolynomial.C (-2 * eps1)),
    C_I_pow_two, C_eps_pow_two]
  have h1 : (MvPolynomial.C (-66 : ℂ) : P2) = -66 := by rw [map_neg, map_ofNat]
  rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, h1, map_ofNat]
  ring

theorem smul_sub_right' (a : Sp) (n : ℤ) (b c : Sp) :
    V2v.smul a n (b - c) = V2v.smul a n b - V2v.smul a n c := by
  rw [PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def, map_sub]

theorem T2_I4 : T2 I4 = (2 : ℂ) • wv 4 0 + (28 : ℂ) • wv 4 4 + (2 : ℂ) • wv 4 8 := by
  rw [T2_apply, psi_I4, map_add, map_add, map_smul, map_smul, map_smul, Tb_xy 8 0 4 rfl,
    Tb_xy 4 4 4 rfl, Tb_xy 0 8 4 rfl]

theorem T2_I3 : T2 I3 = (Complex.I * (-2 * eps1)) • (wv 3 1 - wv 3 5) := by
  rw [T2_apply, psi_I3, ← C_mul, ← smul_eq_C_mul, map_smul, map_sub, Tb_xy 5 1 3 rfl,
    Tb_xy 1 5 3 rfl]

theorem T2_I6 : T2 I6 = (2 : ℂ) • wv 6 0 + (-66 : ℂ) • wv 6 4 + (-66 : ℂ) • wv 6 8 +
    (2 : ℂ) • wv 6 12 := by
  rw [T2_apply, psi_I6, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    Tb_xy 12 0 6 rfl, Tb_xy 8 4 6 rfl, Tb_xy 4 8 6 rfl, Tb_xy 0 12 6 rfl]

/-- **(N) The second channel at weight 36 is nonzero**: `v₍₋₁₂₎u ≡ c·T₂(I₆)` with `c ≠ 0`. -/
theorem six_T2 : ∃ c d : ℂ, c ≠ 0 ∧ (V2m 1 le_rfl).smul (T2 I4) (-12) (T2 I3) - c • T2 I6 -
    d • T2 (I3 * I3) ∈ lowerDesc (V2m 1 le_rfl) 36 := by
  refine ⟨Complex.I * (-2 * eps1) * kappa6, 0, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (mul_ne_zero (by norm_num) eps1_ne_zero))
      kappa6_ne_zero
  · set Φ := fun a b : ℕ => V2v.smul (wv 4 a) (-12) (wv 3 b) -
      (lam6 * (8 * (b : ℂ) - 6 * a)) • wv 6 (a + b - 1) with hΦ
    have hmem : ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ 13 → a ≤ 8 → b ≤ 6 →
        Φ a b ∈ lowerDesc V2v 36 := fun a b h1 h2 ha hb => by
      have := second_wv (a + b) a b rfl h1 h2 ha hb
      simpa using this
    set c3 : ℂ := Complex.I * (-2 * eps1)
    have key : (V2m 1 le_rfl).smul (T2 I4) (-12) (T2 I3) - (c3 * kappa6) • T2 I6 -
        (0 : ℂ) • T2 (I3 * I3) =
        (2 * c3) • Φ 0 1 + (-(2 * c3)) • Φ 0 5 + (28 * c3) • Φ 4 1 + (-(28 * c3)) • Φ 4 5 +
          (2 * c3) • Φ 8 1 + (-(2 * c3)) • Φ 8 5 := by
      rw [T2_I4, T2_I3, T2_I6]
      change V2v.smul _ _ _ - _ - _ = _
      simp only [hΦ, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_smul_left,
        PreVertexAlgebra.smul_smul_right, smul_sub_right', zero_smul, sub_zero,
        lam6]
      norm_num
      module
    rw [key]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_ <;>
      refine Submodule.smul_mem _ _ (hmem _ _ (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))

/-- The `six` field of `T2Residual` holds. -/
theorem T2Residual.of_eqv {φ : tetra →* (P3 ≃ₐ[ℂ] P3)}
    (eqv : ∀ (g : tetra) (F : P3), (g : Aut (V2m 1 le_rfl)) (T2 F) = T2 (φ g F))
    (fix : ∀ (g : tetra) (F : P3), IsA4Inv F → φ g F = F)
    (gen1 : ∃ g : tetra, ∀ F, φ g F = s1 F) (gen2 : ∃ g : tetra, ∀ F, φ g F = s2 F)
    (gen3 : ∃ g : tetra, ∀ F, φ g F = rename cyc F)
    (hom : ∀ (g : tetra) (F : P3) (n : ℕ), F.IsHomogeneous n → (φ g F).IsHomogeneous n) :
    T2Residual φ :=
  ⟨eqv, fix, gen1, gen2, gen3, hom, six_T2⟩

end VOA.Classification.COne.OrbPrim
