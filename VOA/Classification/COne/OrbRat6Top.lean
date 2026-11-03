import VOA.Classification.COne.OrbRat6V2

/-! # The `φ`-eigenspaces of `V_{ℤβ+β/2}` in weights `≤ 9/4`, and `o(aT)` on the quartet

* `phi_t0, phi_s0, phi_d0`: `φ = i` on the spin-½ doublet tops of weights `1/4, 5/4, 9/4`
  (`d₀ ∈ Fock₂ ⊗ e^{β/2}` with `E d₀ = 0` is produced by linear algebra, `Sd02_span`).
* `eigen94`: a `λ`-eigenvector of `φ` (`λ ∉ {0, i}`) of weight `9/4` is `α q₁ + γ q₃` with
  `(α, γ)` an eigenvector of the quartet block of `φ`.
* `eigen_low`: no such eigenvector exists in weight `9/4 − k`, `k ≥ 1`.
* `oa_q1 : o(aT) q₁ = 10 κ q₃`, `oa_q3 : o(aT) q₃ = −120 κ q₁`, `κ ≠ 0`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex
  MvPolynomial VOA.LatGen.Screen

/-! ## §1 Doublets in sector `0` -/

theorem phi_of_sector0 {v : Sp} {d : ℤ} (hv : v ∈ Sd 0 d) (hE : Ep v = 0)
    (hFF : Fm (Fm v) = 0) : phi v = I • v := by
  have hH : Hm v = (1 : ℂ) • v := by rw [Hm_Sd hv]; norm_num
  have hEF' : Ep (Fm v) = eps1 • v := by
    have := E_Fpow hEF hHF hE hH 0
    simpa using this
  have hfv : Fm v ∈ Sd (-1) d := by
    have := Fm_Sd hv
    simpa using this
  exact phi_doublet hv hfv hE hEF' hFF

/-- `e^{β/2}`. -/
abbrev t0 : Sp := latStateGen (latP 1) 1 (0 : ℤ)
/-- `h(−1) e^{β/2}`. -/
abbrev s0 : Sp := latStateGen (latP 1) (xo 0) (0 : ℤ)

theorem t0_Sd : t0 ∈ Sd 0 0 := latStateGen_mem_Sd one_mem_Z0
theorem s0_Sd : s0 ∈ Sd 0 1 := latStateGen_mem_Sd xo_mem_Z1

theorem phi_t0 : phi t0 = I • t0 := by
  refine phi_of_sector0 t0_Sd (Ep_Sd_zero t0_Sd (by norm_num)) ?_
  exact Fm_Sd_zero (Fm_Sd t0_Sd) (by norm_num)

theorem phi_s0 : phi s0 = I • s0 := by
  refine phi_of_sector0 s0_Sd (Ep_Sd_zero s0_Sd (by norm_num)) ?_
  exact Fm_Sd_zero (Fm_Sd s0_Sd) (by norm_num)

/-! ## §2 The vector `d₀` -/

theorem xx_mem_Z2 : xo 0 * xo 0 ∈ gradingZN (rank (latP 1)) 2 := by
  rw [gradingZN_of_nonneg (by norm_num)]
  have h := isWeightedHomogeneous_X ℂ (weightFnN (r := rank (latP 1))) ((0 : ℕ), a0 1)
  have := h.mul h
  simpa using this

theorem x1_mem_Z2 : xo 1 ∈ gradingZN (rank (latP 1)) 2 := by
  rw [gradingZN_of_nonneg (by norm_num)]
  have := isWeightedHomogeneous_X ℂ (weightFnN (r := rank (latP 1))) ((1 : ℕ), a0 1)
  simpa using this

abbrev u1 : Sp := latStateGen (latP 1) (xo 0 * xo 0) (0 : ℤ)
abbrev u2 : Sp := latStateGen (latP 1) (xo 1) (0 : ℤ)

theorem u1_Sd : u1 ∈ Sd 0 2 := latStateGen_mem_Sd xx_mem_Z2
theorem u2_Sd : u2 ∈ Sd 0 2 := latStateGen_mem_Sd x1_mem_Z2

theorem exists_Ep_u (x : Sp) (hx : x ∈ Sd 0 2) : ∃ c : ℂ, Ep x = c • q0 := by
  have h := Ep_Sd hx
  have h' : Ep x ∈ ℂ ∙ q0 := Sd_zero 1 (by simpa using h)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h'
  exact ⟨c, hc.symm⟩

def c1 : ℂ := (exists_Ep_u u1 u1_Sd).choose
def c2 : ℂ := (exists_Ep_u u2 u2_Sd).choose

theorem Ep_u1 : Ep u1 = c1 • q0 := (exists_Ep_u u1 u1_Sd).choose_spec
theorem Ep_u2 : Ep u2 = c2 • q0 := (exists_Ep_u u2 u2_Sd).choose_spec

/-- `d₀ = c₂ u₁ − c₁ u₂`, killed by `E`. -/
def d0 : Sp := c2 • u1 - c1 • u2

theorem d0_Sd : d0 ∈ Sd 0 2 :=
  Submodule.sub_mem _ (Submodule.smul_mem _ _ u1_Sd) (Submodule.smul_mem _ _ u2_Sd)

theorem Ep_d0 : Ep d0 = 0 := by
  rw [d0, map_sub, map_smul, map_smul, Ep_u1, Ep_u2, smul_smul, smul_smul, mul_comm, sub_self]

theorem Sd_m2 {x : Sp} (hx : x ∈ Sd (-2) 0) : ∃ a : ℂ, x = a • qv 3 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (Sd_zero (-2) qv_Sd3)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (Sd_zero (-2) hx)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact qv_ne 3 le_rfl hc.symm
  refine ⟨b * c⁻¹, ?_⟩
  rw [← hb, ← hc, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]

theorem FF_d0 : Fm (Fm d0) = 0 := by
  have hH : Hm d0 = (1 : ℂ) • d0 := by rw [Hm_Sd d0_Sd]; norm_num
  have hE2 := E_Fpow hEF hHF Ep_d0 hH 1
  have hw : (Fm ^ 2) d0 ∈ Sd (-2) 0 := by
    have := Fm_pow_Sd d0_Sd 2
    convert this using 2 <;> norm_num
  obtain ⟨a, ha⟩ := Sd_m2 hw
  have h2 : (Fm ^ (1 + 1)) d0 = (Fm ^ 2) d0 := rfl
  rw [h2, ha, map_smul, Ep_qv3, smul_smul] at hE2
  norm_num at hE2
  have hq2 := qv_ne 2 (by norm_num)
  have ha0 : a = 0 := by
    rcases hE2 with (h | h) | h
    · exact h
    · exact absurd h eps1_ne
    · exact absurd h hq2
  have : (Fm ^ 2) d0 = Fm (Fm d0) := by rw [pow_two, Module.End.mul_apply]
  rw [← this, ha, ha0, zero_smul]

theorem phi_d0 : phi d0 = I • d0 := phi_of_sector0 d0_Sd Ep_d0 FF_d0

theorem Sd02_span {z : Sp} (hz : z ∈ Sd 0 2) : ∃ α β : ℂ, z = α • qv 1 + β • d0 := by
  obtain ⟨x1, x2, hx⟩ := Submodule.mem_span_pair.mp (Sd_two 0 hz)
  obtain ⟨y1, y2, hy⟩ := Submodule.mem_span_pair.mp (Sd_two 0 qv_Sd1)
  have hEq : Ep (qv 1) = (y1 * c1 + y2 * c2) • q0 := by
    rw [← hy, map_add, map_smul, map_smul]
    change y1 • Ep u1 + y2 • Ep u2 = _
    rw [Ep_u1, Ep_u2, smul_smul, smul_smul, ← add_smul]
  rw [Ep_qv1, qv_zero] at hEq
  have hD : y1 * c1 + y2 * c2 = 3 * eps1 := by
    have h := sub_eq_zero.mpr hEq.symm
    rw [← sub_smul] at h
    rcases smul_eq_zero.mp h with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' (ne_zero_of_one (1 : ℤ))
  have hD0 : y1 * c1 + y2 * c2 ≠ 0 := by
    rw [hD]; exact mul_ne_zero (by norm_num) eps1_ne
  set D := y1 * c1 + y2 * c2 with hDdef
  refine ⟨D⁻¹ * (x1 * c1 + x2 * c2), D⁻¹ * (x1 * y2 - x2 * y1), ?_⟩
  have key : (D⁻¹ * (x1 * c1 + x2 * c2)) • qv 1 + (D⁻¹ * (x1 * y2 - x2 * y1)) • d0 =
      (D⁻¹ * (x1 * c1 + x2 * c2) * y1 + D⁻¹ * (x1 * y2 - x2 * y1) * c2) • u1 +
      (D⁻¹ * (x1 * c1 + x2 * c2) * y2 - D⁻¹ * (x1 * y2 - x2 * y1) * c1) • u2 := by
    rw [← hy, d0]; module
  have hA : D⁻¹ * (x1 * c1 + x2 * c2) * y1 + D⁻¹ * (x1 * y2 - x2 * y1) * c2 = x1 := by
    field_simp; rw [hDdef]; ring
  have hB : D⁻¹ * (x1 * c1 + x2 * c2) * y2 - D⁻¹ * (x1 * y2 - x2 * y1) * c1 = x2 := by
    field_simp; rw [hDdef]; ring
  rw [key, hA, hB, ← hx]

/-! ## §3 Eigenspaces -/

theorem phi_Pk (z : Sp) : Pk (phi z) = phi z := by
  change Pk (Pk (FR (Pk z))) = Pk (FR (Pk z))
  rw [Pk_Pk]

theorem Pk_of_eigen {lam : ℂ} (h0 : lam ≠ 0) {z : Sp} (hphi : phi z = lam • z) : Pk z = z := by
  have h := phi_Pk z
  rw [hphi, map_smul] at h
  exact smul_right_injective _ h0 h

/-- Weight `9/4`: the four sectors. -/
theorem weight94_le :
    Mo.weight ((9 / 4 : ℚ) : ℂ) ≤ Sd 0 2 ⊔ Sd (-1) 2 ⊔ Sd 1 0 ⊔ Sd (-2) 0 := by
  apply weight_le
  intro w n hw h
  have h1 := eq_of_weight h
  have h2 : 4 * w + (2 * n + 1) ^ 2 = 9 := by
    have : ((4 * w + (2 * n + 1) ^ 2 : ℤ) : ℚ) = ((9 : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have hb : (2 * n + 1) ^ 2 ≤ 9 := by nlinarith
  have hn1 : n ≤ 1 := by nlinarith
  have hn2 : -2 ≤ n := by nlinarith
  interval_cases n
  · have : w = 0 := by nlinarith
    subst this; exact le_sup_right
  · have : w = 2 := by nlinarith
    subst this; exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  · have : w = 2 := by nlinarith
    subst this; exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  · have : w = 0 := by nlinarith
    subst this; exact le_sup_of_le_left le_sup_right

/-- The lower weights `9/4 − k`, `k ≥ 1`. -/
theorem weight_low_le {k : ℤ} (hk : 1 ≤ k) :
    Mo.weight ((9 / 4 - k : ℚ) : ℂ) ≤ Sd 0 1 ⊔ Sd (-1) 1 ⊔ Sd 0 0 ⊔ Sd (-1) 0 := by
  apply weight_le
  intro w n hw h
  have h1 := eq_of_weight h
  have h2 : 4 * w + (2 * n + 1) ^ 2 = 9 - 4 * k := by
    have : ((4 * w + (2 * n + 1) ^ 2 : ℤ) : ℚ) = ((9 - 4 * k : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have hb : (2 * n + 1) ^ 2 ≤ 5 := by nlinarith
  have hn1 : n ≤ 0 := by nlinarith
  have hn2 : -1 ≤ n := by nlinarith
  have hk2 : k ≤ 2 := by nlinarith
  interval_cases n <;> interval_cases k
  · have : w = 1 := by nlinarith
    subst this; exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  · have : w = 0 := by nlinarith
    subst this; exact le_sup_right
  · have : w = 1 := by nlinarith
    subst this; exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  · have : w = 0 := by nlinarith
    subst this; exact le_sup_of_le_left le_sup_right

theorem Pk_sector {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) :
    Pk x = if Even n then x else 0 := by
  split_ifs with h
  · exact Pk_even hx h
  · exact Pk_odd hx (Int.not_even_iff_odd.mp h)

/-- No `φ`-eigenvector with eigenvalue `λ ∉ {0, i}` below weight `9/4`. -/
theorem eigen_low {lam : ℂ} (h0 : lam ≠ 0) (hI : lam ≠ I) {k : ℤ} (hk : 1 ≤ k) {z : Sp}
    (hz : z ∈ Mo.weight ((9 / 4 - k : ℚ) : ℂ)) (hphi : phi z = lam • z) : z = 0 := by
  have hP := Pk_of_eigen h0 hphi
  obtain ⟨z123, hz123, z4, hz4, rfl⟩ := Submodule.mem_sup.mp (weight_low_le hk hz)
  obtain ⟨z12, hz12, z3, hz3, rfl⟩ := Submodule.mem_sup.mp hz123
  obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.mp hz12
  rw [map_add, map_add, map_add, Pk_sector hz1, Pk_sector hz2, Pk_sector hz3, Pk_sector hz4]
    at hP
  simp only [show Even (0 : ℤ) by decide, show ¬ Even (-1 : ℤ) by decide, if_true, if_false,
    add_zero] at hP
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (Sd_one 0 hz1)
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp (Sd_zero 0 hz3)
  rw [← hP] at hphi ⊢
  have hphiz : phi (a • s0 + b • t0) = I • (a • s0 + b • t0) := by
    rw [map_add, map_smul, map_smul, phi_s0, phi_t0, smul_comm a I, smul_comm b I, ← smul_add]
  rw [hphiz] at hphi
  have h := sub_eq_zero.mpr hphi
  rw [← sub_smul] at h
  rcases smul_eq_zero.mp h with h' | h'
  · exact absurd (sub_eq_zero.mp h').symm hI
  · exact h'

/-- The `λ`-eigenvectors of `φ` of weight `9/4`. -/
theorem eigen94 {lam : ℂ} (h0 : lam ≠ 0) (hI : lam ≠ I) {z : Sp}
    (hz : z ∈ Mo.weight ((9 / 4 : ℚ) : ℂ)) (hphi : phi z = lam • z) :
    ∃ α γ : ℂ, z = Q 0 α 0 γ ∧ lam * α = -I / 2 * α + 3 * I * γ ∧
      lam * γ = -I / 4 * α - I / 2 * γ := by
  have hP := Pk_of_eigen h0 hphi
  obtain ⟨z123, hz123, z4, hz4, rfl⟩ := Submodule.mem_sup.mp (weight94_le hz)
  obtain ⟨z12, hz12, z3, hz3, rfl⟩ := Submodule.mem_sup.mp hz123
  obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.mp hz12
  rw [map_add, map_add, map_add, Pk_sector hz1, Pk_sector hz2, Pk_sector hz3, Pk_sector hz4]
    at hP
  simp only [show Even (0 : ℤ) by decide, show ¬ Even (-1 : ℤ) by decide,
    show ¬ Even (1 : ℤ) by decide, show Even (-2 : ℤ) by decide, if_true, if_false,
    add_zero] at hP
  obtain ⟨α, β, rfl⟩ := Sd02_span hz1
  obtain ⟨γ, rfl⟩ := Sd_m2 hz4
  rw [← hP] at hphi ⊢
  have hQ : α • qv 1 + β • d0 + γ • qv 3 = Q 0 α 0 γ + β • d0 := by simp only [Q]; module
  rw [hQ] at hphi ⊢
  rw [map_add, map_smul, phi_Q, phi_d0, smul_smul] at hphi
  -- split into the sector-0 part `X` and the sector-(−2) part `Y`
  set e1 := lam * α - (-I / 2 * α + 3 * I * γ)
  set e2 := lam * γ - (-I / 4 * α - I / 2 * γ)
  have hXY : (e1 • qv 1 + ((lam - I) * β) • d0) + e2 • qv 3 = 0 := by
    have h := sub_eq_zero.mpr hphi.symm
    rw [← h]; simp only [Q, e1, e2, smul_add]; module
  have hX : e1 • qv 1 + ((lam - I) * β) • d0 ∈ Sd 0 2 :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ qv_Sd1) (Submodule.smul_mem _ _ d0_Sd)
  have hY : e2 • qv 3 ∈ Sd (-2) 0 := Submodule.smul_mem _ _ qv_Sd3
  have hH := congrArg Hm hXY
  rw [map_add, Hm_Sd hX, Hm_Sd hY, map_zero] at hH
  have hY0 : e2 • qv 3 = 0 := by
    have h4 : (4 : ℂ) • (e2 • qv 3) = 0 := by
      have := hXY
      rw [add_eq_zero_iff_eq_neg] at this
      rw [this] at hH
      norm_num at hH
      rw [← sub_eq_zero]
      rw [show (4 : ℂ) • (e2 • qv 3) - 0 = -(((-3 : ℂ)) • (e2 • qv 3) - (e2 • qv 3)) by module]
      rw [neg_eq_zero]
      convert hH using 1
      module
    rcases smul_eq_zero.mp h4 with h | h
    · norm_num at h
    · exact h
  have he2 : e2 = 0 := by
    rcases smul_eq_zero.mp hY0 with h | h
    · exact h
    · exact absurd h (qv_ne 3 le_rfl)
  rw [hY0, add_zero] at hXY
  have hE := congrArg Ep hXY
  rw [map_add, map_smul, map_smul, Ep_qv1, Ep_d0, smul_zero, add_zero, map_zero, smul_smul]
    at hE
  have he1 : e1 = 0 := by
    rcases smul_eq_zero.mp hE with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' (mul_ne_zero (by norm_num) eps1_ne)
    · exact absurd h (qv_ne 0 (by norm_num))
  rw [he1, zero_smul, zero_add] at hXY
  have hβ : β • d0 = 0 := by
    rcases smul_eq_zero.mp hXY with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (sub_eq_zero.mp h') hI
      · rw [h', zero_smul]
    · rw [h, smul_zero]
  refine ⟨α, γ, by rw [hβ, add_zero], ?_, ?_⟩
  · exact sub_eq_zero.mp he1
  · exact sub_eq_zero.mp he2

/-! ## §4 `o(aT)` on the quartet -/

theorem mode_add_u (u v : Sp) (n : ℤ) (x : Sp) :
    mode (Mo.YM (u + v)) n x = mode (Mo.YM u) n x + mode (Mo.YM v) n x := by
  rw [map_add]; rfl

theorem mode_smul_u (c : ℂ) (u : Sp) (n : ℤ) (x : Sp) :
    mode (Mo.YM (c • u)) n x = c • mode (Mo.YM u) n x := by
  rw [map_smul]; rfl

/-- `o(v_k)` on the module (`v_k` has weight `9`). -/
abbrev Tm (k : ℕ) (x : Sp) : Sp := mode (Mo.YM (vv k)) 8 x

theorem Tm_succ (k : ℕ) (x : Sp) : Tm (k + 1) x = Fm (Tm k x) - Tm k (Fm x) := by
  have h := mode_comm (latChargeGen (latP 1) (-a1 1)) (vv k) 8 x
  rw [← fo_eq, fo_vv] at h
  exact h.symm

theorem Tm_zero (k : ℕ) : Tm k 0 = 0 := map_zero (mode (Mo.YM (vv k)) 8)

theorem Tm0_low {j : ℕ} (hj : j ≤ 2) : Tm 0 (qv j) = 0 := by
  have h := charge_Sd (3 : ℤ) 8 (qv_Sd j)
  show mode (Mo.YM (vv 0)) 8 (qv j) = 0
  rw [vv_zero]
  have hj' : (j : ℤ) ≤ 2 := by exact_mod_cast hj
  have hj0 : (0 : ℤ) ≤ j := by positivity
  rw [Sd_neg (by nlinarith), Submodule.mem_bot] at h
  exact h

theorem Tm0_qv3_exists : ∃ κ : ℂ, κ ≠ 0 ∧ Tm 0 (qv 3) = κ • qv 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (Sd_zero (-2) qv_Sd3)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact qv_ne 3 le_rfl hc.symm
  have hL : mode (Mo.YM (latChargeGen (latP 1) (3 : ℤ))) 8
      (latStateGen (latP 1) 1 (-2 : ℤ)) =
      (latCob (latP 1) (glueLat 1 1) (glueIota 1 1) (3 : ℤ) *
          latticeCocycle (glueLat 1 1) (glueIota 1 1 (3 : ℤ))
            (glueIota 1 1 (-2 : ℤ) + glueDelta 1 1)) • q0 := by
    rw [charge_latStateGen]
    congr 1
    rw [show (-8 - 1 - 2 * (3 : ℤ) * (-2) - 3) = 0 by norm_num,
      show ((3 : ℤ) + (-2 : ℤ)) = (1 : ℤ) by norm_num]
    change latStateGen (latP 1) (EEVec (latP 1) _ 0 (vacuumN _)) _ = _
    rw [EEVec_vacuum, if_pos le_rfl, show ((0 : ℤ).toNat) = 0 from rfl, vSchur_zero]
  refine ⟨c * (latCob (latP 1) (glueLat 1 1) (glueIota 1 1) (3 : ℤ) *
      latticeCocycle (glueLat 1 1) (glueIota 1 1 (3 : ℤ))
        (glueIota 1 1 (-2 : ℤ) + glueDelta 1 1)), ?_, ?_⟩
  · exact mul_ne_zero hc0 (mul_ne_zero (latCob_ne_zero _ _ _ _)
      (VOA.LatGen.latticeCocycle_ne_zero _ _ _))
  · rw [Tm, vv_zero, ← hc, map_smul, hL, smul_smul, qv_zero]

/-- The constant `κ` with `o(e^{3β}) q₃ = κ q₀`. -/
def κ : ℂ := Tm0_qv3_exists.choose

theorem κ_ne : κ ≠ 0 := Tm0_qv3_exists.choose_spec.1
theorem Tm0_qv3 : Tm 0 (qv 3) = κ • qv 0 := Tm0_qv3_exists.choose_spec.2

theorem Tm_qv4 (k : ℕ) : Tm k (qv 4) = 0 := by rw [qv_four, Tm_zero]

theorem oa_q1 : mode (Mo.YM aT) 8 (qv 1) = (10 * κ) • qv 3 := by
  have T00 := Tm0_low (j := 0) (by norm_num)
  have T01 := Tm0_low (j := 1) (by norm_num)
  have T02 := Tm0_low (j := 2) (by norm_num)
  have T03 := Tm0_qv3
  have T11 : Tm 1 (qv 1) = 0 := by rw [Tm_succ, T01, Fm_qv1, T02]; simp
  have T12 : Tm 1 (qv 2) = -(κ • qv 0) := by rw [Tm_succ, T02, Fm_qv2, T03]; simp
  have T13 : Tm 1 (qv 3) = κ • qv 1 := by
    rw [Tm_succ, T03, Fm_qv3, Tm_zero, map_smul, Fm_qv0]; simp
  have T21 : Tm 2 (qv 1) = κ • qv 0 := by rw [Tm_succ, T11, Fm_qv1, T12]; simp
  have T22 : Tm 2 (qv 2) = (-2 * κ) • qv 1 := by
    rw [Tm_succ, T12, Fm_qv2, T13, map_neg, map_smul, Fm_qv0]; module
  have T23 : Tm 2 (qv 3) = κ • qv 2 := by
    rw [Tm_succ, T13, Fm_qv3, Tm_zero, map_smul, Fm_qv1]; simp
  have T31 : Tm 3 (qv 1) = (3 * κ) • qv 1 := by
    rw [Tm_succ, T21, Fm_qv1, T22, map_smul, Fm_qv0]; module
  have T32 : Tm 3 (qv 2) = (-3 * κ) • qv 2 := by
    rw [Tm_succ, T22, Fm_qv2, T23, map_smul, Fm_qv1]; module
  have T33 : Tm 3 (qv 3) = κ • qv 3 := by
    rw [Tm_succ, T23, Fm_qv3, Tm_zero, map_smul, Fm_qv2]; simp
  have T41 : Tm 4 (qv 1) = (6 * κ) • qv 2 := by
    rw [Tm_succ, T31, Fm_qv1, T32, map_smul, Fm_qv1]; module
  have T42 : Tm 4 (qv 2) = (-4 * κ) • qv 3 := by
    rw [Tm_succ, T32, Fm_qv2, T33, map_smul, Fm_qv2]; module
  have T51 : Tm 5 (qv 1) = (10 * κ) • qv 3 := by
    rw [Tm_succ, T41, Fm_qv1, T42, map_smul, Fm_qv2]; module
  have hmode : mode (Mo.YM aT) 8 (qv 1) = (-120 : ℂ) • Tm 1 (qv 1) + Tm 5 (qv 1) := by
    simp only [aT, R7, mode_add_u, mode_smul_u, zero_smul, one_smul, zero_add, add_zero]
  rw [hmode, T11, T51, smul_zero, zero_add]

theorem oa_q3 : mode (Mo.YM aT) 8 (qv 3) = (-120 * κ) • qv 1 := by
  have T03 := Tm0_qv3
  have T13 : Tm 1 (qv 3) = κ • qv 1 := by
    rw [Tm_succ, T03, Fm_qv3, Tm_zero, map_smul, Fm_qv0]; simp
  have T23 : Tm 2 (qv 3) = κ • qv 2 := by
    rw [Tm_succ, T13, Fm_qv3, Tm_zero, map_smul, Fm_qv1]; simp
  have T33 : Tm 3 (qv 3) = κ • qv 3 := by
    rw [Tm_succ, T23, Fm_qv3, Tm_zero, map_smul, Fm_qv2]; simp
  have T43 : Tm 4 (qv 3) = 0 := by
    rw [Tm_succ, T33, Fm_qv3, Tm_zero, map_smul, Fm_qv3]; simp
  have T53 : Tm 5 (qv 3) = 0 := by
    rw [Tm_succ, T43, Fm_qv3, map_zero]; simp
  have hmode : mode (Mo.YM aT) 8 (qv 3) = (-120 : ℂ) • Tm 1 (qv 3) + Tm 5 (qv 3) := by
    simp only [aT, R7, mode_add_u, mode_smul_u, zero_smul, one_smul, zero_add, add_zero]
  rw [hmode, T13, T53, add_zero, smul_smul]

end VOA.Classification.COne.OrbRat6
