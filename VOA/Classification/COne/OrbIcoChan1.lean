import VOA.Classification.COne.OrbPrimSix

/-! # OrbIco: the first non-top channel `Prim_{a²} × Prim_{b²} → Prim_{(a+b-1)²}` of `V₂`

For `a, b ≥ 1` put `n = firstIdx a b = -2ab + 2a + 2b - 2`, so that
`wt (u₍ₙ₎v) = a² + b² - n - 1 = (a + b - 1)²` for `u ∈ Prim_{a²}`, `v ∈ Prim_{b²}`.

`first_wv`: `w_{a,i}₍ₙ₎ w_{b,j} ≡ λ_{a,b} (2a j - 2b i) w_{a+b-1,i+j-1}` modulo lower Virasoro
descendants. This is the first transvectant of binary forms. The A₄ lemma `OrbPrim.second_wv`
is the case `(a, b) = (4, 3)`.

`lamF_ne_zero`: `λ_{a,b} ≠ 0`; the base value is the lattice computation
`e^{aα}₍ₙ₎ f₀ e^{bα} = ε·C(2a+2b-2, 2a-1)·e^{(a+b-1)α}` (`gco_neg`: the coefficients of
`(1-x)^{-(N+1)}` are binomial coefficients).

The icosahedral application is `(a, b) = (6, 10)`, `n = -90`, weight `225`.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VertexOperatorAlgebra OrbSpan VOA.LatGen VOA.LatGen.Triplet HeisenbergN
  OrbRat6 VOA.IntegralLattice OrbC2b OrbPrim

/-! ## Closed form of `gco` at negative integers -/

/-- `(1 - x)^{-(N+1)} = Σ C(k+N, N) xᵏ`. -/
theorem gco_neg (N : ℕ) : ∀ k : ℕ, gco (-((N : ℂ) + 1)) k = (((k + N).choose N : ℕ) : ℂ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | k
  · simp [gco_zero]
  · rw [gco_succ]
    have hs : ∑ m ∈ Finset.range (k + 1), (-(-((N : ℂ) + 1))) * gco (-((N : ℂ) + 1)) (k - m)
        = ((N : ℂ) + 1) * (((k + N + 1).choose (N + 1) : ℕ) : ℂ) := by
      rw [← Finset.mul_sum, neg_neg]
      congr 1
      rw [Finset.sum_congr rfl (fun m hm => ih (k - m) (by simp at hm; omega))]
      have hr := Finset.sum_range_reflect (fun j => (((j + N).choose N : ℕ) : ℂ)) (k + 1)
      simp only [show k + 1 - 1 = k by omega] at hr
      rw [hr]
      exact_mod_cast Nat.sum_range_add_choose k N
    rw [hs]
    have hc := Nat.choose_succ_right_eq (k + N + 1) N
    rw [show k + N + 1 - N = k + 1 by omega] at hc
    have hc' : ((N : ℂ) + 1) * (((k + N + 1).choose (N + 1) : ℕ) : ℂ) =
        ((k : ℂ) + 1) * (((k + 1 + N).choose N : ℕ) : ℂ) := by
      rw [show k + 1 + N = k + N + 1 by omega]
      have := congrArg (fun x : ℕ => (x : ℂ)) hc
      push_cast at this
      linear_combination this
    rw [hc', ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero k), one_mul]

/-! ## `f₀ e^{bα}` -/

theorem fo_chargeGen (b : ℕ) (hb : 1 ≤ b) :
    fo (latChargeGen (latP 1) (b : ℤ)) = latticeCocycle (latP 1) (-1 : ℤ) (b : ℤ) •
      latStateGen (latP 1) (vSchur (latP 1) (-1 : ℤ) (2 * b - 1)) (((b : ℤ) - 1 : ℤ)) := by
  rw [fo_eq]
  change V2v.smul (latChargeGen (latP 1) (-1 : ℤ)) 0
    (latStateGen (latP 1) (vacuumN _) (b : ℤ)) = _
  rw [smul_chargeGen_state, EEVec_vacuum, latP_form, if_pos (by push_cast; omega)]
  congr 2
  congr 1
  push_cast
  omega

theorem wv_one (b : ℕ) (hb : 1 ≤ b) :
    wv b 1 = (1 / (2 * b : ℂ)) • fo (latChargeGen (latP 1) (b : ℤ)) := by
  rw [wv, cnk, vn, pow_one]
  congr 1
  have hf : ((2 * b).factorial : ℂ) = ((2 * b : ℕ) : ℂ) * ((2 * b - 1).factorial : ℂ) := by
    rw [show 2 * b = (2 * b - 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  have h1 : ((2 * b - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (b : ℂ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  push_cast
  field_simp

/-! ## The base of the induction -/

/-- The mode index of the first channel. -/
def firstIdx (a b : ℕ) : ℤ := -2 * (a : ℤ) * b + 2 * a + 2 * b - 2

theorem wa0_wb0 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    V2v.smul (wv a 0) (firstIdx a b) (wv b 0) = 0 := by
  rw [wv_zero, wv_zero]
  change V2v.smul (latChargeGen (latP 1) (a : ℤ)) (firstIdx a b)
    (latStateGen (latP 1) (vacuumN _) (b : ℤ)) = 0
  rw [smul_chargeGen_state, EEVec_vacuum, latP_form, firstIdx, if_neg (by push_cast; nlinarith)]
  simp [latStateGen]

/-- The base coefficient `e^{aα}₍ₙ₎ f₀ e^{bα}`. -/
def kappaF (a b : ℕ) : ℂ :=
  (1 / (2 * b : ℂ)) * (latticeCocycle (latP 1) (-1 : ℤ) (b : ℤ) *
    (latticeCocycle (latP 1) (a : ℤ) (((b : ℤ) - 1 : ℤ)) *
      (((2 * b - 1 + (2 * a - 1)).choose (2 * a - 1) : ℕ) : ℂ)))

theorem cocycle_ne_zero (x y : ℤ) : latticeCocycle (latP 1) x y ≠ 0 := by
  intro h
  have := latticeCocycle_sq (latP 1) x y
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem kappaF_ne_zero (a b : ℕ) (hb : 1 ≤ b) : kappaF a b ≠ 0 := by
  unfold kappaF
  refine mul_ne_zero ?_ (mul_ne_zero (cocycle_ne_zero _ _)
    (mul_ne_zero (cocycle_ne_zero _ _) ?_))
  · have : (2 * b : ℂ) ≠ 0 := by
      have : (2 * b : ℕ) ≠ 0 := by omega
      exact_mod_cast this
    exact one_div_ne_zero this
  · exact_mod_cast (Nat.choose_pos (by omega)).ne'

theorem EEVec_vSchur_bottom (a N : ℕ) :
    EEVec (latP 1) (a : ℤ) (-(N : ℤ)) (vSchur (latP 1) (-1 : ℤ) N) =
      gco (((latP 1).form (-1 : ℤ) (a : ℤ) : ℤ) : ℂ) N • vacuumN (rank (latP 1)) := by
  rw [WpC2.EEVec_eq_weight_bounded_sum' (latP 1) (a : ℤ) _
    (Screen.vSchur_mem_gradingWN (latP 1) (-1 : ℤ) N)]
  rw [show max (0 : ℤ) (-(N : ℤ)) = 0 by omega, show ((N : ℕ) : ℤ) + (-(N : ℤ)) = 0 by ring,
    Finset.Icc_self, Finset.sum_singleton, show ((0 : ℤ) - (-(N : ℤ))).toNat = N by omega,
    show (0 : ℤ).toNat = 0 by rfl, vSchur_zero, one_mul,
    aExpVec_vSchur (latP 1) (latP_posDef 1 le_rfl) _ _ N N le_rfl, Nat.sub_self, vSchur_zero]
  rfl

theorem wa0_wb1 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    V2v.smul (wv a 0) (firstIdx a b) (wv b 1) =
      kappaF a b • latChargeGen (latP 1) (((a + b - 1 : ℕ)) : ℤ) := by
  rw [wv_one b hb, fo_chargeGen b hb, smul_smul, PreVertexAlgebra.smul_smul_right, wv_zero]
  change (1 / (2 * b : ℂ) * latticeCocycle (latP 1) (-1 : ℤ) (b : ℤ)) •
      V2v.smul (latChargeGen (latP 1) (a : ℤ)) (firstIdx a b)
        (latStateGen (latP 1) (vSchur (latP 1) (-1 : ℤ) (2 * b - 1)) (((b : ℤ) - 1 : ℤ))) = _
  rw [smul_chargeGen_state]
  have hidx : -firstIdx a b - 1 - (latP 1).form (a : ℤ) (((b : ℤ) - 1 : ℤ)) =
      -(((2 * b - 1 : ℕ)) : ℤ) := by
    rw [latP_form, firstIdx]; push_cast [show 1 ≤ 2 * b by omega]; ring
  rw [hidx, EEVec_vSchur_bottom, latP_form]
  have hg : gco (((2 * ((1 : ℕ) : ℤ) * (-1 : ℤ) * (a : ℤ) : ℤ)) : ℂ) (2 * b - 1) =
      (((2 * b - 1 + (2 * a - 1)).choose (2 * a - 1) : ℕ) : ℂ) := by
    have := gco_neg (2 * a - 1) (2 * b - 1)
    rw [← this]
    congr 1
    push_cast [show 1 ≤ 2 * a by omega]
    ring
  rw [hg, latStateGen_csmul, smul_smul, smul_smul]
  have hq : (a : ℤ) + (((b : ℤ) - 1 : ℤ)) = (((a + b - 1 : ℕ)) : ℤ) := by
    push_cast [show 1 ≤ a + b by omega]; ring
  rw [hq]
  change _ • latStateGen (latP 1) (vacuumN _) _ = _ • latStateGen (latP 1) (vacuumN _) _
  congr 1
  unfold kappaF
  ring

theorem wa1_wb0 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    V2v.smul (wv a 1) (firstIdx a b) (wv b 0) =
      (-((b : ℂ) / a) * kappaF a b) • latChargeGen (latP 1) (((a + b - 1 : ℕ)) : ℤ) := by
  have h := congrArg fo (wa0_wb0 a b ha hb)
  rw [fo_smul, fo_wv0 a ha, fo_wv0 b hb, map_zero,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, wa0_wb1 a b ha hb,
    smul_smul] at h
  have ha' : ((2 * a : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * a ≠ 0 by omega)
  have hx : V2v.smul (wv a 1) (firstIdx a b) (wv b 0) =
      (((2 * a : ℕ) : ℂ))⁻¹ • ((((2 * a : ℕ) : ℂ)) • V2v.smul (wv a 1) (firstIdx a b) (wv b 0)) := by
    rw [smul_smul, inv_mul_cancel₀ ha', one_smul]
  rw [hx, eq_neg_of_add_eq_zero_left h, smul_neg, smul_smul, ← neg_smul]
  congr 1
  have ha'' : (a : ℂ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  field_simp
  push_cast
  ring

/-! ## The first channel on the multiplets -/

/-- `λ_{a,b} = κ_{a,b} / (2a)`. -/
def lamF (a b : ℕ) : ℂ := kappaF a b / (2 * a)

theorem lamF_ne_zero (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : lamF a b ≠ 0 := by
  unfold lamF
  refine div_ne_zero (kappaF_ne_zero a b hb) ?_
  have : (2 * a : ℕ) ≠ 0 := by omega
  exact_mod_cast this

/-- The first-transvectant coefficient. -/
def coefF (a b i j : ℕ) : ℂ := 2 * (a : ℂ) * j - 2 * (b : ℂ) * i

/-- **The first channel `Prim_{a²} × Prim_{b²} → Prim_{(a+b-1)²}` is the first transvectant.** -/
theorem first_wv (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∀ t : ℕ, ∀ i j : ℕ, i + j = t → 1 ≤ t → t ≤ 2 * (a + b - 1) + 1 → i ≤ 2 * a → j ≤ 2 * b →
    V2v.smul (wv a i) (firstIdx a b) (wv b j) - (lamF a b * coefF a b i j) •
      wv (a + b - 1) (i + j - 1) ∈ lowerDesc V2v (((a + b - 1 : ℕ) : ℤ) ^ 2) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro i j hij ht htN hi hj
  by_cases ht1 : t = 1
  · subst ht1
    rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [wa0_wb1 a b ha hb, show 0 + 1 - 1 = 0 by rfl, wv_zero, lamF, coefF]
      have ha'' : (a : ℂ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
      rw [← sub_smul, show kappaF a b - kappaF a b / (2 * a) *
        (2 * (a : ℂ) * ((1 : ℕ) : ℂ) - 2 * (b : ℂ) * ((0 : ℕ) : ℂ)) = 0 by
          field_simp; push_cast; ring, zero_smul]
      exact Submodule.zero_mem _
    · rw [wa1_wb0 a b ha hb, show 1 + 0 - 1 = 0 by rfl, wv_zero, lamF, coefF]
      have ha'' : (a : ℂ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
      rw [← sub_smul, show -((b : ℂ) / a) * kappaF a b - kappaF a b / (2 * a) *
        (2 * (a : ℂ) * ((0 : ℕ) : ℂ) - 2 * (b : ℂ) * ((1 : ℕ) : ℂ)) = 0 by
          field_simp; push_cast; ring, zero_smul]
      exact Submodule.zero_mem _
  · have ht2 : 2 ≤ t := by omega
    set N := a + b - 1 with hN
    set Φ := fun x y : ℕ => V2v.smul (wv a x) (firstIdx a b) (wv b y) -
      (lamF a b * coefF a b x y) • wv N (x + y - 1) with hΦ
    change Φ i j ∈ _
    have hgr : Φ i j ∈ V2v.grading ((N : ℤ) ^ 2) := by
      refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ (wv_grading _ _))
      have h := V2v.smul_mem_grading (wv_grading a i) (wv_grading b j) (firstIdx a b)
      convert h using 2
      rw [hN, firstIdx]
      push_cast [show 1 ≤ a + b by omega]
      ring
    have hho : ho (Φ i j) = (((2 * N : ℕ) : ℂ) - 2 * ((t - 1 : ℕ) : ℂ)) • Φ i j := by
      subst hij
      simp only [hΦ]
      rw [map_sub, map_smul, ho_smul, ho_wv, ho_wv, ho_wv, PreVertexAlgebra.smul_smul_left,
        PreVertexAlgebra.smul_smul_right]
      rw [hN]
      push_cast [Nat.cast_sub (show 1 ≤ i + j by omega), Nat.cast_sub (show 1 ≤ a + b by omega)]
      module
    have heo : eo (Φ i j) ∈ lowerDesc V2v ((N : ℤ) ^ 2) := by
      have hsplit : eo (Φ i j) =
          (if i = 0 then 0 else (eps1 * (i : ℂ)) • Φ (i - 1) j) +
          (if j = 0 then 0 else (eps1 * (j : ℂ)) • Φ i (j - 1)) := by
        simp only [hΦ]
        rw [map_sub, map_smul, eo_smul, eo_wv' a i hi, eo_wv' b j hj]
        have htop : i + j - 1 ≤ 2 * N := by omega
        rw [eo_wv' N (i + j - 1) htop, if_neg (show ¬ i + j - 1 = 0 by omega)]
        by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
        · omega
        · subst hi0
          simp only [if_true, if_neg hj0, zero_add, PreVertexAlgebra.smul_zero_left,
            PreVertexAlgebra.smul_smul_right, coefF]
          push_cast [Nat.cast_sub (show 1 ≤ j by omega)]
          module
        · subst hj0
          simp only [if_true, if_neg hi0, add_zero, PreVertexAlgebra.smul_zero_right,
            PreVertexAlgebra.smul_smul_left, coefF]
          push_cast [Nat.cast_sub (show 1 ≤ i by omega)]
          module
        · simp only [if_neg hi0, if_neg hj0, PreVertexAlgebra.smul_smul_left,
            PreVertexAlgebra.smul_smul_right, coefF,
            show i - 1 + j - 1 = i + j - 1 - 1 by omega,
            show i + (j - 1) - 1 = i + j - 1 - 1 by omega]
          push_cast [Nat.cast_sub (show 1 ≤ i + j by omega),
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
    exact ekernel N (t - 1) (by omega) hgr (by rw [hho]) heo

end VOA.Classification.COne.OrbIco

namespace VOA.Classification.COne.OrbIco
open VOA VertexOperatorAlgebra OrbSpan VOA.LatGen VOA.LatGen.Triplet HeisenbergN
  OrbRat6 VOA.IntegralLattice OrbC2b OrbPrim MvPolynomial

/-! ## The corner and the full multiplet statement -/

theorem first_wv_corner (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    V2v.smul (wv a (2 * a)) (firstIdx a b) (wv b (2 * b)) ∈
      lowerDesc V2v (((a + b - 1 : ℕ) : ℤ) ^ 2) := by
  set N := a + b - 1 with hN
  have hgr : V2v.smul (wv a (2 * a)) (firstIdx a b) (wv b (2 * b)) ∈
      V2v.grading ((N : ℤ) ^ 2) := by
    have h := V2v.smul_mem_grading (wv_grading a (2 * a)) (wv_grading b (2 * b)) (firstIdx a b)
    convert h using 2
    rw [hN, firstIdx]
    push_cast [show 1 ≤ a + b by omega]
    ring
  have hho : ho (V2v.smul (wv a (2 * a)) (firstIdx a b) (wv b (2 * b))) =
      (((2 * N : ℕ) : ℂ) - 2 * ((2 * N + 1 : ℕ) : ℂ)) •
        V2v.smul (wv a (2 * a)) (firstIdx a b) (wv b (2 * b)) := by
    rw [ho_smul, ho_wv, ho_wv, PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, hN]
    push_cast [show 1 ≤ a + b by omega]
    module
  have h1 := first_wv a b ha hb (2 * a - 1 + 2 * b) (2 * a - 1) (2 * b) rfl (by omega) (by omega)
    (by omega) le_rfl
  have h2 := first_wv a b ha hb (2 * a + (2 * b - 1)) (2 * a) (2 * b - 1) rfl (by omega)
    (by omega) le_rfl (by omega)
  have heo : eo (V2v.smul (wv a (2 * a)) (firstIdx a b) (wv b (2 * b))) =
      (eps1 * ((2 * a : ℕ) : ℂ)) • (V2v.smul (wv a (2 * a - 1)) (firstIdx a b) (wv b (2 * b)) -
        (lamF a b * coefF a b (2 * a - 1) (2 * b)) • wv N (2 * a - 1 + 2 * b - 1)) +
      (eps1 * ((2 * b : ℕ) : ℂ)) • (V2v.smul (wv a (2 * a)) (firstIdx a b) (wv b (2 * b - 1)) -
        (lamF a b * coefF a b (2 * a) (2 * b - 1)) • wv N (2 * a + (2 * b - 1) - 1)) := by
    rw [eo_smul, eo_wv' a (2 * a) le_rfl, eo_wv' b (2 * b) le_rfl,
      if_neg (show ¬ 2 * a = 0 by omega), if_neg (show ¬ 2 * b = 0 by omega),
      PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
      show 2 * a + (2 * b - 1) - 1 = 2 * a - 1 + 2 * b - 1 by omega]
    have hc : (eps1 * ((2 * a : ℕ) : ℂ)) * (lamF a b * coefF a b (2 * a - 1) (2 * b)) +
        (eps1 * ((2 * b : ℕ) : ℂ)) * (lamF a b * coefF a b (2 * a) (2 * b - 1)) = 0 := by
      unfold coefF
      push_cast [Nat.cast_sub (show 1 ≤ 2 * a by omega), Nat.cast_sub (show 1 ≤ 2 * b by omega)]
      ring
    rw [smul_sub, smul_sub, smul_smul, smul_smul]
    have : ∀ (x y : Sp) (c d : ℂ) (w : Sp), c + d = 0 → x + y = x - c • w + (y - d • w) :=
      fun x y c d w h => by rw [show d = -c by linear_combination h]; module
    exact this _ _ _ _ _ hc
  have heo' : eo (V2v.smul (wv a (2 * a)) (firstIdx a b) (wv b (2 * b))) ∈
      lowerDesc V2v ((N : ℤ) ^ 2) := by
    rw [heo]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
  exact ekernel N (2 * N + 1) (by omega) hgr (by rw [hho]) heo'

/-- The first channel on every pair of multiplet vectors (the coefficient vanishes at
`i = j = 0` and at the corner `i = 2a`, `j = 2b`). -/
theorem first_wv_all (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (i j : ℕ) (hi : i ≤ 2 * a)
    (hj : j ≤ 2 * b) :
    V2v.smul (wv a i) (firstIdx a b) (wv b j) - (lamF a b * coefF a b i j) •
      wv (a + b - 1) (i + j - 1) ∈ lowerDesc V2v (((a + b - 1 : ℕ) : ℤ) ^ 2) := by
  by_cases h0 : i + j = 0
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by omega, by omega⟩
    rw [wa0_wb0 a b ha hb, show coefF a b 0 0 = 0 by simp [coefF], mul_zero, zero_smul,
      sub_zero]
    exact Submodule.zero_mem _
  by_cases hc : i = 2 * a ∧ j = 2 * b
  · obtain ⟨rfl, rfl⟩ := hc
    rw [show coefF a b (2 * a) (2 * b) = 0 by unfold coefF; push_cast; ring, mul_zero,
      zero_smul, sub_zero]
    exact first_wv_corner a b ha hb
  · exact first_wv a b ha hb (i + j) i j rfl (by omega) (by omega) hi hj

/-! ## Binary forms: the first transvectant -/

/-- The first transvectant `P_x Q_y - P_y Q_x`. -/
def tv1 (P Q : P2) : P2 := pderiv 0 P * pderiv 1 Q - pderiv 1 P * pderiv 0 Q

theorem tv1_add_left (P P' Q : P2) : tv1 (P + P') Q = tv1 P Q + tv1 P' Q := by
  simp only [tv1, map_add]; ring

theorem tv1_add_right (P Q Q' : P2) : tv1 P (Q + Q') = tv1 P Q + tv1 P Q' := by
  simp only [tv1, map_add]; ring

theorem tv1_smul_left (c : ℂ) (P Q : P2) : tv1 (c • P) Q = c • tv1 P Q := by
  simp only [tv1, Derivation.map_smul, smul_mul_assoc, smul_sub]

theorem tv1_smul_right (c : ℂ) (P Q : P2) : tv1 P (c • Q) = c • tv1 P Q := by
  simp only [tv1, Derivation.map_smul, mul_smul_comm, smul_sub]

theorem Tb_monomial_eq {g : Fin 2 →₀ ℕ} {N k : ℕ} (hg : g 0 + g 1 = 2 * N) (hk : g 1 = k)
    (c : ℂ) : Tb (monomial g c) = c • wv N k := by
  rw [Tb_monomial, tbm_of_deg hg, hk]

theorem Tb_tv1_monomial (a b : ℕ) {e f : Fin 2 →₀ ℕ} (he : e 0 + e 1 = 2 * a)
    (hf : f 0 + f 1 = 2 * b) (hab : 1 ≤ a + b) :
    Tb (tv1 (monomial e 1) (monomial f 1)) =
      coefF a b (e 1) (f 1) • wv (a + b - 1) (e 1 + f 1 - 1) := by
  rw [tv1, pderiv_monomial, pderiv_monomial, pderiv_monomial, pderiv_monomial, monomial_mul,
    monomial_mul, map_sub]
  have T1 : Tb (monomial (e - Finsupp.single 0 1 + (f - Finsupp.single 1 1))
      (1 * e 0 * (1 * f 1))) = ((e 0 * f 1 : ℕ) : ℂ) • wv (a + b - 1) (e 1 + f 1 - 1) := by
    by_cases hz : e 0 = 0 ∨ f 1 = 0
    · rcases hz with hz | hz <;> simp [hz]
    · push Not at hz
      rw [Tb_monomial_eq (N := a + b - 1) (k := e 1 + f 1 - 1)]
      · push_cast; ring_nf
      · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        simp; omega
      · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        simp; omega
  have T2 : Tb (monomial (e - Finsupp.single 1 1 + (f - Finsupp.single 0 1))
      (1 * e 1 * (1 * f 0))) = ((e 1 * f 0 : ℕ) : ℂ) • wv (a + b - 1) (e 1 + f 1 - 1) := by
    by_cases hz : e 1 = 0 ∨ f 0 = 0
    · rcases hz with hz | hz <;> simp [hz]
    · push Not at hz
      rw [Tb_monomial_eq (N := a + b - 1) (k := e 1 + f 1 - 1)]
      · push_cast; ring_nf
      · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        simp; omega
      · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        simp; omega
  rw [T1, T2, ← sub_smul]
  congr 1
  unfold coefF
  have h0 : (e 0 : ℂ) = 2 * a - e 1 := by
    have : ((e 0 + e 1 : ℕ) : ℂ) = ((2 * a : ℕ) : ℂ) := by rw [he]
    push_cast at this; linear_combination this
  have h1 : (f 0 : ℂ) = 2 * b - f 1 := by
    have : ((f 0 + f 1 : ℕ) : ℂ) = ((2 * b : ℕ) : ℂ) := by rw [hf]
    push_cast at this; linear_combination this
  push_cast
  rw [h0, h1]
  ring

/-- **The first channel on binary forms**: `Tb(P)₍ₙ₎Tb(Q) ≡ λ_{a,b} Tb((P,Q)₁)`. -/
theorem first_bin (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) {P Q : P2} (hP : P ∈ binDeg (2 * a))
    (hQ : Q ∈ binDeg (2 * b)) :
    V2v.smul (Tb P) (firstIdx a b) (Tb Q) - lamF a b • Tb (tv1 P Q) ∈
      lowerDesc V2v (((a + b - 1 : ℕ) : ℤ) ^ 2) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    induction hQ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      simp only [Set.mem_setOf_eq] at he hf
      rw [Tb_tv1_monomial a b he hf (by omega), Tb_monomial, Tb_monomial, one_smul, one_smul,
        tbm_of_deg he, tbm_of_deg hf, smul_smul]
      exact first_wv_all a b ha hb (e 1) (f 1) (by omega) (by omega)
    | zero => simp [tv1]
    | add y z _ _ hy hz =>
      rw [map_add, PreVertexAlgebra.smul_add_right, tv1_add_right, map_add, smul_add]
      convert Submodule.add_mem _ hy hz using 1; abel
    | smul c y _ hy =>
      rw [map_smul, PreVertexAlgebra.smul_smul_right, tv1_smul_right, map_smul, smul_comm,
        ← smul_sub]
      exact Submodule.smul_mem _ _ hy
  | zero => simp [tv1]
  | add x y _ _ hx hy =>
    rw [map_add, PreVertexAlgebra.smul_add_left, tv1_add_left, map_add, smul_add]
    convert Submodule.add_mem _ hx hy using 1; abel
  | smul c x _ hx =>
    rw [map_smul, PreVertexAlgebra.smul_smul_left, tv1_smul_left, map_smul, smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ _ hx

end VOA.Classification.COne.OrbIco
