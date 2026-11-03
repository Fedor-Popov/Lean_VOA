import VOA.Classification.COne.PlusRat4Gap2

/-! # Every gap-two charged/charged pair splits (all `m`)

Rows `s = r + 1 < s' = r' + 1` with `s'² = s² + 8m` (weights `h`, `h + 2`), each unique at its
weight, no row of weight `h + 1`, `4h ≠ 1`, `64h ≠ 1`.  Kernel `c_{s'}`, quotient `c_s`; `x` a
quotient-bottom lift.

1. Degree one: every degree-one mode on `x` is a multiple of `L(-1)x` (gap-one transfer, and no
   row at `h + 1`), with `H⁴₍₂₎x = L(-1)x/3`, `H⁶₍₄₎x = L(-1)x/5`, `E₍ₘ₋₂₎x = 0`.
2. Degree two: `w_t = Q_t - a_t R - b_t Q₁` are top vectors (`transfer2` with the lattice model);
   `L(1)`, `L(2)` give `(4h-1)a₂ = -1`, `(4h-1)b₂ = 4h`, `(4h-1)a₃ = -3/2`, `(4h-1)b₃ = 6h`.
3. The kernel row kills `H⁴`, `H⁶`: three relations; the certificate
   `6S(6·S r₃ - 10·S r₂) - (40h+50)·S r₁ = 8(1-64h)(S Q₂ + R - 4h Q₁)` (`S = 4h-1`)
   (`charged_Q2`) gives `S Q₂ = 4h Q₁ - R`.
4. `E₍ₘ₋₃₎x = 0` (virtual eigenvalue `4((m-2)² - 4mh) ≠ 0`, since `s ≤ m - 3`).
5. `degTwo_le`, `split_of_degTwo`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

/-! ## §1  Pure algebra -/

/-- Solving the `L(1)`, `L(2)` system. -/
theorem solve_AB {h a b α β : ℂ} (f1 : α - a * (4 * h + 2) - b * 3 = 0)
    (f2 : β - a * (6 * h) - b * (4 * h + 1 / 2) = 0) :
    (4 * h - 1) ^ 2 * a = (4 * h + 1 / 2) * α - 3 * β ∧
      (4 * h - 1) ^ 2 * b = (4 * h + 2) * β - 6 * h * α :=
  ⟨by linear_combination -(4 * h + 1 / 2) * f1 + 3 * f2,
    by linear_combination -(4 * h + 2) * f2 + 6 * h * f1⟩

/-- The charged elimination certificate. -/
theorem charged_Q2 {E : Type*} [AddCommGroup E] [Module ℂ E] {R Q1 Q2 Q3 Q4 : E}
    {h a2 b2 a3 b3 : ℂ} (h64 : 64 * h - 1 ≠ 0)
    (ha2 : (4 * h - 1) * a2 = -1) (hb2 : (4 * h - 1) * b2 = 4 * h)
    (ha3 : (4 * h - 1) * a3 = -3 / 2) (hb3 : (4 * h - 1) * b3 = 6 * h)
    (R1 : (-1 : ℂ) • Q2 + (6 : ℂ) • Q3 - a2 • ((2 : ℂ) • R + (6 : ℂ) • Q2) -
      b2 • ((2 : ℂ) • Q1 + (6 : ℂ) • Q2) = 0)
    (R2 : (3 / 2 : ℂ) • Q2 - (5 : ℂ) • Q3 + (6 : ℂ) • Q4 - a3 • ((2 : ℂ) • R + (6 : ℂ) • Q2) -
      b3 • ((2 : ℂ) • Q1 + (6 : ℂ) • Q2) = 0)
    (R3 : (-3 : ℂ) • Q2 + (10 / 3 : ℂ) • Q3 + (10 : ℂ) • Q4 -
      a2 • ((2 : ℂ) • R + (20 : ℂ) • Q3) -
      b2 • ((2 : ℂ) • Q1 + (15 : ℂ) • Q2 + (10 : ℂ) • Q3) = 0) :
    (4 * h - 1) • Q2 + R - (4 * h) • Q1 = 0 := by
  have key : (8 * (1 - 64 * h)) • ((4 * h - 1) • Q2 + R - (4 * h) • Q1) = 0 := by
    linear_combination (norm := module)
      (-(40 * h + 50) * (4 * h - 1)) • R1 + (-60 * (4 * h - 1) ^ 2) • R2 +
        (36 * (4 * h - 1) ^ 2) • R3 +
        (-(40 * h + 50)) • (ha2 • ((2 : ℂ) • R + (6 : ℂ) • Q2)) +
        (-(40 * h + 50)) • (hb2 • ((2 : ℂ) • Q1 + (6 : ℂ) • Q2)) +
        (-60 * (4 * h - 1)) • (ha3 • ((2 : ℂ) • R + (6 : ℂ) • Q2)) +
        (-60 * (4 * h - 1)) • (hb3 • ((2 : ℂ) • Q1 + (6 : ℂ) • Q2)) +
        (36 * (4 * h - 1)) • (ha2 • ((2 : ℂ) • R + (20 : ℂ) • Q3)) +
        (36 * (4 * h - 1)) • (hb2 • ((2 : ℂ) • Q1 + (15 : ℂ) • Q2 + (10 : ℂ) • Q3))
  have hc : (8 * (1 - 64 * h) : ℂ) ≠ 0 := by
    intro hc; apply h64; linear_combination -hc / 8
  exact (smul_eq_zero.mp key).resolve_left hc

/-! ## §2  The charged gap-two theorem -/

section Main
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)

@[reducible] local instance zhuRing4 : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuAlgebra4 : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

include hm2 in
/-- `4m · h_s = s²`. -/
theorem four_m_hC (r : Fin (m - 1)) : 4 * (m : ℂ) * hC m r = ((r.val + 1 : ℕ) : ℂ) ^ 2 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [hC_eq]
  push_cast
  field_simp

include hm2 in
/-- The `E`-eigenvalue does not vanish for `s ≤ m - 3`. -/
theorem E_eigen_ne (r : Fin (m - 1)) (hs : r.val + 4 ≤ m) :
    (4 * (((m : ℂ) - 2) ^ 2 - 4 * m * hC m r) : ℂ) ≠ 0 := by
  rw [four_m_hC m hm2 r]
  have h1 : ((m : ℂ) - 2) ^ 2 - ((r.val + 1 : ℕ) : ℂ) ^ 2 =
      ((m : ℂ) - 2 - ((r.val + 1 : ℕ) : ℂ)) * ((m : ℂ) - 2 + ((r.val + 1 : ℕ) : ℂ)) := by ring
  rw [h1]
  have h2 : ((m : ℂ) - 2 - ((r.val + 1 : ℕ) : ℂ)) ≠ 0 := by
    have : ((m : ℤ) - 2 - ((r.val + 1 : ℕ) : ℤ)) ≠ 0 := by omega
    exact_mod_cast this
  have h3 : ((m : ℂ) - 2 + ((r.val + 1 : ℕ) : ℂ)) ≠ 0 := by
    have : ((m : ℤ) - 2 + ((r.val + 1 : ℕ) : ℤ)) ≠ 0 := by omega
    exact_mod_cast this
  exact mul_ne_zero (by norm_num) (mul_ne_zero h2 h3)

include hm2 in
/-- **Every gap-two charged/charged pair splits** (kernel `c_{s'}`, quotient `c_s`). -/
theorem pairSplitting_charged_gap_two (r r' : Fin (m - 1))
    (hgap : weight m (.inl r') = weight m (.inl r) + 2)
    (huq : ∀ j : Label m, weight m j = weight m (.inl r) → j = .inl r)
    (huq' : ∀ j : Label m, weight m j = weight m (.inl r') → j = .inl r')
    (hno1 : ∀ j : Label m, weight m j ≠ weight m (.inl r) + 1)
    (h14 : 4 * hC m r - 1 ≠ 0) (h64 : 64 * hC m r - 1 ≠ 0) :
    PairSplitting m hm (.inl r') (.inl r) := by
  intro M _ _ A P hP hQ hb ht
  -- arithmetic
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsq : ((r'.val + 1 : ℕ) : ℤ) ^ 2 = ((r.val + 1 : ℕ) : ℤ) ^ 2 + 8 * m := by
    have h := hgap
    simp only [weight] at h
    field_simp at h
    have : (((r'.val + 1 : ℕ) : ℤ) ^ 2 : ℚ) = ((((r.val + 1 : ℕ) : ℤ) ^ 2 + 8 * m : ℤ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast this
  have hs : r.val + 4 ≤ m := by
    have hr' := r'.isLt
    by_contra hcon
    have h1 : ((r'.val + 1 : ℕ) : ℤ) ≤ (m : ℤ) - 1 := by push_cast; omega
    have h2 : (m : ℤ) - 3 ≤ ((r.val + 1 : ℕ) : ℤ) := by push_cast; omega
    have h0 : (0 : ℤ) ≤ ((r'.val + 1 : ℕ) : ℤ) := by positivity
    have h3 : ((r'.val + 1 : ℕ) : ℤ) ^ 2 ≤ ((m : ℤ) - 1) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have h5 : 0 ≤ (((r.val + 1 : ℕ) : ℤ) - ((m : ℤ) - 3)) * (((r.val + 1 : ℕ) : ℤ) + ((m : ℤ) - 3)) :=
      mul_nonneg (sub_nonneg.mpr h2) (by push_cast; omega)
    nlinarith
  have hs3 : r.val + 3 ≤ m := by omega
  have hgapC : hC m r' = hC m r + 2 := by
    simp only [hC]; rw [hgap]; push_cast; ring
  have huqC : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r → j = .inl r :=
    fun j h => huq j (Rat.cast_injective h)
  have huqC' : ∀ j : Label m, ((weight m j : ℚ) : ℂ) = hC m r + 2 → j = .inl r' :=
    fun j h => huq' j (Rat.cast_injective (h.trans hgapC.symm))
  have hno1C : ∀ j : Label m, ((weight m j : ℚ) : ℂ) ≠ hC m r + 1 := by
    intro j h
    apply hno1 j
    apply Rat.cast_injective (α := ℂ)
    rw [h]; push_cast; rfl
  change FactorBottom A ⊥ P (hC m r') at hb
  change FactorBottom A P ⊤ (hC m r) at ht
  rw [hgapC] at hb
  set h := hC m r with hhdef
  have hh : h ≠ 0 := hC_ne_zero m hm2 r
  have hre : (h + 2).re = h.re + 2 := by simp
  have hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0 := by
    intro μ hμ v hv
    have hvP : v ∈ P := by
      by_contra hc
      have hw : FactorWeight A P ⊤ μ := fun hT => hc (hT ⟨Submodule.mem_top, hv⟩)
      have := ht.2 μ hw
      linarith
    exact kernel_generalized_below_bottom_eq_zero A P _ hb hvP hv (by rw [hre]; linarith)
  obtain ⟨x, hxL, hxP⟩ := PlusRat2Dual.exists_eigen_lift (V2mPlus_c2Cofinite m hm) A P hP
    (show h + 2 ≠ h by intro hc; have := congrArg (· - h) hc; simp at this) hb ht
  have hx0 : x ≠ 0 := fun h => hxP (h ▸ P.zero_mem)
  have hxg : x ∈ (L0 A).maxGenEigenspace h :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
  have hxΩ : x ∈ Omega A := by
    intro β v hv n hn
    apply hlow _ _ _ (mode_mem_maxGenEigenspace A hv n hxg)
    have : ((β - n - 1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show β - n - 1 ≤ -1 by omega)
    rw [Complex.add_re, Complex.intCast_re]
    linarith
  -- the character of `x`
  set χ := chiT m hm hm2 (.inl r)
  have hχx := top_char_unique m hm hm2 A hxΩ hxL (.inl r) huqC
  have hzero : ∀ {k : ℤ} {a : VP m hm}, a ∈ (V2mPlus m hm).grading k →
      mode (A.YM a) (k - 1) x = χ (VOA.mk (V2mPlus m hm) a) • x := by
    intro k a ha
    have h1 := hχx (VOA.mk (V2mPlus m hm) a)
    rw [topEvaluation_mk, oLevW_homogeneous A 0 ha, add_zero] at h1
    exact h1
  have hg2 := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  have hg3 := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  have h4 : mode (A.YM (HP m hm 2)) 3 x = (0 : ℂ) • x := by
    have h1 := hzero hg2
    rw [chiT_HP_zero m hm hm2 r 2 (Or.inl rfl)] at h1
    exact h1
  have h6 : mode (A.YM (HP m hm 3)) 5 x = (0 : ℂ) • x := by
    have h1 := hzero hg3
    rw [chiT_HP_zero m hm hm2 r 3 (Or.inr rfl)] at h1
    exact h1
  have hE0 : mode (A.YM (EP m hm)) ((m : ℤ) - 1) x = 0 := by
    have h1 := hzero (EP_mem_grading m hm)
    have hv := (chiT_hasValues m hm hm2 (.inl r)).2.2
    change chiT m hm hm2 (.inl r) (VOA.mk (V2mPlus m hm) (EP m hm)) = _ at hv
    rw [hv] at h1
    simp [values] at h1
    simpa using h1
  -- degree one: the line
  have hD1 : Deg1Line A x := by
    intro j c hc
    obtain ⟨κ, hκ⟩ := transfer_Omega_gen m hm hm2 r hs3 huqC A hxΩ hxL hlow hc
    refine ⟨κ, ?_⟩
    have hL : L0 A (mode (A.YM c) (j - 2) x - κ • mode (A.YM (V2mPlus m hm).conformalVector) 0 x) =
        (h + 1) • (mode (A.YM c) (j - 2) x - κ • mode (A.YM (V2mPlus m hm).conformalVector) 0 x) := by
      rw [map_sub, map_smul, L0_mode_eigen A hxL hc, L0_mode_eigen A hxL (V2mPlus m hm).conformal_mem,
        show h + ((j - (j - 2) - 1 : ℤ) : ℂ) = h + 1 by push_cast; ring,
        show h + ((2 - 0 - 1 : ℤ) : ℂ) = h + 1 by push_cast; ring, smul_sub, smul_comm]
    have h0 := top_eval_zero_of_rows m hm hm2 A hκ hL 1 (fun j hj => absurd hj (hno1C j))
    rw [topEvaluation_one] at h0
    exact sub_eq_zero.mp h0
  have hxTD : TopData A χ h x := ⟨hxΩ, hχx, hxL, hD1⟩
  have heTD := lat_topData m hm hm2 r hs3
  have he0 := latVacuumGen_ne_zero' m hm
  have hLx0 := hxTD.Lm1_ne_zero hh hx0
  -- the degree-one constants
  have coef1 : ∀ {j : ℤ} {c : VP m hm} {κ : ℂ} {β : ℂ}, c ∈ (V2mPlus m hm).grading j →
      mode (A.YM c) (j - 2) x = κ • mode (A.YM (V2mPlus m hm).conformalVector) 0 x →
      mode (A.YM (V2mPlus m hm).conformalVector) 2 (mode (A.YM c) (j - 2) x) = β • x →
      κ * (2 * h) = β := by
    intro j c κ β _ hκ hβ
    rw [hκ, map_smul, L1_L A hxΩ hxL, smul_smul] at hβ
    have h1 : (κ * (2 * h) - β) • x = 0 := by rw [sub_smul, hβ, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hx0)
  have hp2 : mode (A.YM (HP m hm 2)) 2 x = (1 / 3 : ℂ) • mode (A.YM (HP m hm 1)) 0 x := by
    obtain ⟨κ, hκ⟩ := hD1 _ _ hg2
    rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num] at hκ
    have := coef1 hg2 (by rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num]; exact hκ)
      (by rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num]; exact L1G_p2 m hm A hxΩ hxL h4)
    have hk : κ = 1 / 3 := by
      have h2h : (2 : ℂ) * h ≠ 0 := mul_ne_zero two_ne_zero hh
      have h1 : (κ - 1 / 3) * (2 * h) = 0 := by linear_combination this
      exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right h2h)
    rw [hκ, hk]; rfl
  have hp3 : mode (A.YM (HP m hm 3)) 4 x = (1 / 5 : ℂ) • mode (A.YM (HP m hm 1)) 0 x := by
    obtain ⟨κ, hκ⟩ := hD1 _ _ hg3
    rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num] at hκ
    have := coef1 hg3 (by rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num]; exact hκ)
      (by rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num]; exact L1G_p3 m hm A hxΩ hxL h4 h6)
    have hk : κ = 1 / 5 := by
      have h2h : (2 : ℂ) * h ≠ 0 := mul_ne_zero two_ne_zero hh
      have h1 : (κ - 1 / 5) * (2 * h) = 0 := by linear_combination this
      exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right h2h)
    rw [hκ, hk]; rfl
  have hE1 : mode (A.YM (EP m hm)) ((m : ℤ) - 2) x = 0 := by
    obtain ⟨κ, hκ⟩ := hD1 _ _ (EP_mem_grading m hm)
    have := coef1 (β := 0) (EP_mem_grading m hm) hκ (by rw [L1G_v m hm A hxΩ hE0, zero_smul])
    have hk : κ = 0 := by
      rcases mul_eq_zero.mp this with h1 | h1
      · exact h1
      · exact absurd h1 (mul_ne_zero two_ne_zero hh)
    rw [hκ, hk, zero_smul]
  -- degree two: transfer
  have hTr : ∀ {k : ℤ} {t : VP m hm}, t ∈ (V2mPlus m hm).grading k →
      ∃ a b : ℂ, TopData.wv A x t k a b ∈ Omega A := by
    intro k t htk
    obtain ⟨a, b, hab⟩ := lat_deg2 m hm hm2 r hs h14 htk
    refine ⟨a, b, transfer2 A (Ns m hm r).toWeakModule χ hxTD heTD hx0 he0 hh hlow htk ?_⟩
    simp only [TopData.wv]
    rw [hab]; abel
  -- the kernel character
  have hker : ∀ w : M, w ∈ Omega A → L0 A w = (h + 2) • w →
      mode (A.YM (HP m hm 2)) 3 w = 0 ∧ mode (A.YM (HP m hm 3)) 5 w = 0 := by
    intro w hw hwL
    have hrow : ∀ t, t = 2 ∨ t = 3 → topEvaluation A w hw (VOA.mk (V2mPlus m hm) (HP m hm t)) = 0 :=
      fun t ht' => top_eval_zero_of_rows m hm hm2 A hw hwL _ (fun j hj => by
        rw [huqC' j hj]; exact chiT_HP_zero m hm hm2 r' t ht')
    have e2 := hrow 2 (Or.inl rfl)
    have e3 := hrow 3 (Or.inr rfl)
    rw [topEvaluation_mk, oLevW_homogeneous A 0 hg2] at e2
    rw [topEvaluation_mk, oLevW_homogeneous A 0 hg3] at e3
    exact ⟨e2, e3⟩
  have hL12 : ∀ w : M, w ∈ Omega A →
      mode (A.YM (V2mPlus m hm).conformalVector) 2 w = 0 ∧
        mode (A.YM (V2mPlus m hm).conformalVector) 3 w = 0 := fun w hw =>
    ⟨Omega_mode_vanish hw (V2mPlus m hm).conformal_mem (by norm_num),
      Omega_mode_vanish hw (V2mPlus m hm).conformal_mem (by norm_num)⟩
  -- the Virasoro values
  have q1L1 := L1_Q1 m hm A hxΩ hm2
  have q1L2 := L2_Q1 m hm A hxΩ hxL hm2
  have q2L1 := L1_Q2 m hm A hxΩ hp2
  have q2L2 := L2_Q2 m hm A hxΩ hxL h4
  have q3L1 := L1_Q3 m hm A hxΩ hp2 hp3
  have q3L2 := L2_Q3 m hm A hxΩ hxL h4 h6
  have rL1 := L1_R A hxΩ hxL
  have rL2 := L2_R A hxΩ hxL
  rw [HP_one] at q1L1 q1L2 q2L1 q3L1
  -- `w₂`
  obtain ⟨a2, b2, hw2⟩ := hTr hg2
  have hw2L := L0_wv A hxL hg2 a2 b2
  simp only [TopData.wv] at hw2 hw2L
  rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num] at hw2 hw2L
  obtain ⟨g1, g2⟩ := hL12 _ hw2
  rw [map_sub, map_sub, map_smul, map_smul, q2L1, rL1, q1L1] at g1
  rw [map_sub, map_sub, map_smul, map_smul, q2L2, rL2, q1L2] at g2
  have f1 : 2 - a2 * (4 * h + 2) - b2 * 3 = 0 := by
    have : (2 - a2 * (4 * h + 2) - b2 * 3) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) g1
    exact (smul_eq_zero.mp this).resolve_right hLx0
  have f2 : 4 * h - a2 * (6 * h) - b2 * (4 * h + 1 / 2) = 0 := by
    have : (4 * h - a2 * (6 * h) - b2 * (4 * h + 1 / 2)) • x = 0 := by
      linear_combination (norm := module) g2
    exact (smul_eq_zero.mp this).resolve_right hx0
  obtain ⟨sa2, sb2⟩ := solve_AB f1 f2
  have ha2 : (4 * h - 1) * a2 = -1 := by
    have h1 : (4 * h - 1) * ((4 * h - 1) * a2 + 1) = 0 := by linear_combination sa2
    linear_combination (mul_eq_zero.mp h1).resolve_left h14
  have hb2 : (4 * h - 1) * b2 = 4 * h := by
    have h1 : (4 * h - 1) * ((4 * h - 1) * b2 - 4 * h) = 0 := by linear_combination sb2
    linear_combination (mul_eq_zero.mp h1).resolve_left h14
  -- `w₃`
  obtain ⟨a3, b3, hw3⟩ := hTr hg3
  have hw3L := L0_wv A hxL hg3 a3 b3
  simp only [TopData.wv] at hw3 hw3L
  rw [show ((2 * 3 : ℕ) : ℤ) - 3 = 3 by norm_num] at hw3 hw3L
  obtain ⟨g3, g4⟩ := hL12 _ hw3
  rw [map_sub, map_sub, map_smul, map_smul, q3L1, rL1, q1L1] at g3
  rw [map_sub, map_sub, map_smul, map_smul, q3L2, rL2, q1L2] at g4
  have f3 : 3 - a3 * (4 * h + 2) - b3 * 3 = 0 := by
    have : (3 - a3 * (4 * h + 2) - b3 * 3) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) g3
    exact (smul_eq_zero.mp this).resolve_right hLx0
  have f4 : 6 * h - a3 * (6 * h) - b3 * (4 * h + 1 / 2) = 0 := by
    have : (6 * h - a3 * (6 * h) - b3 * (4 * h + 1 / 2)) • x = 0 := by
      linear_combination (norm := module) g4
    exact (smul_eq_zero.mp this).resolve_right hx0
  obtain ⟨sa3, sb3⟩ := solve_AB f3 f4
  have ha3 : (4 * h - 1) * a3 = -3 / 2 := by
    have h1 : (4 * h - 1) * ((4 * h - 1) * a3 + 3 / 2) = 0 := by linear_combination sa3
    linear_combination (mul_eq_zero.mp h1).resolve_left h14
  have hb3 : (4 * h - 1) * b3 = 6 * h := by
    have h1 : (4 * h - 1) * ((4 * h - 1) * b3 - 6 * h) = 0 := by linear_combination sb3
    linear_combination (mul_eq_zero.mp h1).resolve_left h14
  -- the three relations
  have eQ2 := oH4_Q2 m hm A h4
  have eQ3 := oH4_Q3 m hm A h4
  have eR := oH4_R m hm A h4 hp2
  have eQ1 := oH4_Q1 m hm A h4
  have fQ2 := oH6_Q2 m hm A h6
  have fR := oH6_R m hm A h6 hp3
  have fQ1 := oH6_Q1 m hm A h6
  rw [HP_one] at eR eQ1 fR fQ1
  obtain ⟨o4, o6⟩ := hker _ hw2 hw2L
  obtain ⟨o4', -⟩ := hker _ hw3 hw3L
  rw [map_sub, map_sub, map_smul, map_smul, eQ2, eR, eQ1] at o4
  rw [map_sub, map_sub, map_smul, map_smul, eQ3, eR, eQ1] at o4'
  rw [map_sub, map_sub, map_smul, map_smul, fQ2, fR, fQ1] at o6
  have hrel := charged_Q2 (R := mode (A.YM (V2mPlus m hm).conformalVector) 0
      (mode (A.YM (V2mPlus m hm).conformalVector) 0 x))
    (Q1 := mode (A.YM (V2mPlus m hm).conformalVector) (-1) x) (Q2 := mode (A.YM (HP m hm 2)) 1 x)
    (Q3 := mode (A.YM (HP m hm 3)) 3 x) (Q4 := mode (A.YM (HP m hm 4)) 5 x) h64 ha2 hb2 ha3 hb3
    (by linear_combination (norm := module) o4) (by linear_combination (norm := module) o4')
    (by linear_combination (norm := module) o6)
  have hQ2mem : mode (A.YM (HP m hm 2)) 1 x ∈ RQspan m hm A x := by
    apply Submodule.mem_span_pair.mpr
    refine ⟨-(4 * h - 1)⁻¹, (4 * h - 1)⁻¹ * (4 * h), ?_⟩
    have e : mode (A.YM (HP m hm 2)) 1 x = (4 * h - 1)⁻¹ • ((4 * h - 1) • mode (A.YM (HP m hm 2)) 1 x) := by
      rw [smul_smul, inv_mul_cancel₀ h14, one_smul]
    rw [e]
    have e2 : (4 * h - 1) • mode (A.YM (HP m hm 2)) 1 x =
        (4 * h) • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x -
          mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) := by
      linear_combination (norm := module) hrel
    rw [e2]
    module
  -- the `E`-part
  obtain ⟨aE, bE, hwE⟩ := hTr (EP_mem_grading m hm)
  have hwEL := L0_wv A hxL (EP_mem_grading m hm) aE bE
  simp only [TopData.wv] at hwE hwEL
  obtain ⟨g5, g6⟩ := hL12 _ hwE
  rw [map_sub, map_sub, map_smul, map_smul, L1_v m hm A hxΩ hE1, rL1, q1L1] at g5
  rw [map_sub, map_sub, map_smul, map_smul, L2_v m hm A hxΩ hE0, rL2, q1L2] at g6
  have f5 : aE * (4 * h + 2) + bE * 3 = 0 := by
    have : (aE * (4 * h + 2) + bE * 3) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) -g5
    exact (smul_eq_zero.mp this).resolve_right hLx0
  have f6 : aE * (6 * h) + bE * (4 * h + 1 / 2) = 0 := by
    have : (aE * (6 * h) + bE * (4 * h + 1 / 2)) • x = 0 := by
      linear_combination (norm := module) -g6
    exact (smul_eq_zero.mp this).resolve_right hx0
  obtain ⟨rfl, rfl⟩ := kac_zero h14 aE bE f5 f6
  simp only [zero_smul, sub_zero] at hwE hwEL
  have hv0 : mode (A.YM (EP m hm)) ((m : ℤ) - 3) x = 0 := by
    have o := (hker _ hwE hwEL).1
    have ev := oH4_v2 m hm A hxΩ hxL h4 hE0 hE1
    rw [o, smul_zero, mul_zero, zero_add] at ev
    exact (smul_eq_zero.mp ev.symm).resolve_left (E_eigen_ne m hm2 r hs)
  -- conclusion
  have hST : ScalarTop A x := ⟨hxΩ, fun j c hc => ⟨_, hzero hc⟩⟩
  exact split_of_degTwo m hm hm2 A P hP hQ hb ht hxΩ hxL hxP hh h14
    (degTwo_le m hm hm2 A hST hD1 hQ2mem hv0)

end Main

end VOA.Classification.COne.PlusRat4
