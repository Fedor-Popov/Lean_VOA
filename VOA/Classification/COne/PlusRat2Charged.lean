import VOA.Classification.COne.PlusRat2Fock
import VOA.Classification.COne.PlusRatResidual
import VOA.Moonshine.GenerationFock

/-! # The `E`-telescope on charged and half-lattice tops

On the lattice module `V_{L+λ_s}` (`1 ≤ s ≤ m`) with top exponential `e^{λ_s}` (the state
`𝟙 ⊗ e^{0}`), and `J = 2m - 2`:

* `E_n e^{λ_s} = κ₁ S_{s-1-n}(-α) e^{λ_s - α}` for `n < s`, and `0` for `n ≥ s`;
* `E_{J-n}` of that is `κ₁ κ₂ κ(-2m, s-1-n) e^{λ_s}`, where `κ(P, ·)` are the coefficients of
  `(1-x)^P` (`EEVec_neg_vSchur`);
* `∑_n (-1)^n C(J,n) κ(-2m, s-1-n) = κ(-2, s-1) = s`.

Hence the telescope is `κ₁ κ₂ s · e^{λ_s}` and every charged character takes a nonzero value on
`zetaE` (`charged_zetaE_ne_zero`).  At `s = m` the same computation on both bottom
exponentials gives the half-lattice characters the value `m` (`half_zetaE`).
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat2
open VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
open PlusUnitary PlusC2 PlusCharacterTable PlusSplitting PlusRatTelescope LatMod PlusZhuSchur
open PlusZhuNormalForms PlusResonantPairs PlusRatSign VOA.Huang.LogRemovalAdmissible
open VOA.LatExp (kZ kZ_neg kZ_nonneg kappa kappa_conv kappa_eq_wt kappa_two_term kappa_zero wt)

/-! ## §1  Binomial bookkeeping -/

theorem kappa_neg_two (k : ℕ) : kappa (-2 : ℂ) k = k + 1 := by
  induction k with
  | zero => simp [kappa_zero]
  | succ k ih =>
    have h := kappa_two_term (-2 : ℂ) k
    rw [ih] at h
    have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    apply mul_left_cancel₀ hk
    push_cast
    linear_combination h

/-- `∑_{n<s} (-1)^n C(2m-2,n) κ(-2m, s-1-n) = s`. -/
theorem telescope_kappa_sum (m : ℕ) (hm : 1 ≤ m) (s : ℕ) (hs : 1 ≤ s) :
    ∑ n ∈ Finset.range s, ((-1 : ℂ) ^ n * ((2 * m - 2).choose n : ℂ)) *
      kappa (-(2 * m : ℂ)) (s - 1 - n) = s := by
  have h := kappa_conv (((2 * m - 2 : ℕ) : ℕ) : ℂ) (-(2 * m : ℂ)) (s - 1)
  have hA : (((2 * m - 2 : ℕ) : ℕ) : ℂ) + -(2 * m : ℂ) = -2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hA, kappa_neg_two, show s - 1 + 1 = s by omega] at h
  rw [show ((s : ℕ) : ℂ) = ((s - 1 : ℕ) : ℂ) + 1 by
    rw [Nat.cast_sub hs]; push_cast; ring, ← h]
  apply Finset.sum_congr rfl
  intro n _
  rw [kappa_eq_wt, wt]

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## §2  Mode computations on the lattice modules -/

/-- The underlying state of `E`. -/
abbrev Ec : LatModuleGen (latP m) := ((EP m hm : VP m hm) : LatModuleGen (latP m))

theorem YM_Ec (j t : ℤ) (x : LatModuleGen (latP m)) :
    (latticeModule m hm j).YM (Ec m hm) t x =
      (latticeModule m hm j).YM (latChargeGen (latP m) ((1 : ℤ) : (latP m).carrier)) t x +
      (latticeModule m hm j).YM (latChargeGen (latP m) ((-1 : ℤ) : (latP m).carrier)) t x := by
  rw [Ec, EP_coe, map_add]
  rfl

/-- `E_n e^{λ_s}`. -/
theorem E_first_zero (s : ℕ) (n : ℕ) :
    (latticeModule m hm s).YM (Ec m hm) (-(n : ℤ) - 1)
        (latStateGen (latP m) (vacuumN _) ((0 : ℤ) : (latP m).carrier)) =
      if n < s then kap m s (-1) 0 •
        latStateGen (latP m) (vSchur (latP m) ((-1 : ℤ) : (latP m).carrier) (s - 1 - n))
          ((-1 : ℤ) : (latP m).carrier)
      else 0 := by
  rw [YM_Ec, latE_vac, latE_vac, if_neg (by omega), zero_add]
  by_cases hn : n < s
  · rw [if_pos (by omega), if_pos hn]
    congr 2
    congr 1; omega
  · rw [if_neg (by omega), if_neg hn]

/-- `E_n e^{λ_m - α}` at `s = m`. -/
theorem E_first_neg (n : ℕ) (hn : n < m) :
    (latticeModule m hm m).YM (Ec m hm) (-(n : ℤ) - 1)
        (latStateGen (latP m) (vacuumN _) ((-1 : ℤ) : (latP m).carrier)) =
      kap m m 1 (-1) •
        latStateGen (latP m) (vSchur (latP m) ((1 : ℤ) : (latP m).carrier) (m - 1 - n))
          ((0 : ℤ) : (latP m).carrier) := by
  rw [YM_Ec, latE_vac, latE_vac, if_pos (by omega),
    if_neg (by omega), add_zero]
  congr 2
  congr 1; omega

/-- `E_{J-n}` on the `e^{λ_s - α}` sector: only the vacuum coefficient survives. -/
theorem E_second_neg (s : ℕ) (hs : s ≤ m) (n p : ℕ) (hnp : n + 1 + p = s)
    {q : FockN (rank (latP m))} (hq : q ∈ gradingWN (rank (latP m)) p) :
    (latticeModule m hm s).YM (Ec m hm) (-(((2 * m - 2 : ℕ) : ℤ) - n) - 1)
        (latStateGen (latP m) q ((-1 : ℤ) : (latP m).carrier)) =
      kap m s 1 (-1) • latStateGen (latP m)
        (EEVec (latP m) ((1 : ℤ) : (latP m).carrier) (-(p : ℤ)) q)
          ((0 : ℤ) : (latP m).carrier) := by
  have h22 : ((2 * m - 2 : ℕ) : ℤ) = 2 * m - 2 := by omega
  rw [YM_Ec, latticeModule_latChargeGen, latticeModule_latChargeGen,
    EEVec_eq_zero_of_lt (latP m) ((-1 : ℤ) : (latP m).carrier) hq (by rw [h22]; omega)]
  rw [show latStateGen (latP m) (0 : FockN (rank (latP m))) _ = 0 by simp [latStateGen],
    smul_zero, add_zero]
  congr 2
  congr 1
  congr 1; rw [h22]; omega

/-- `E_{J-n}` on the `e^{λ_m}` sector at `s = m`. -/
theorem E_second_zero (n p : ℕ) (hnp : n + 1 + p = m)
    {q : FockN (rank (latP m))} (hq : q ∈ gradingWN (rank (latP m)) p) :
    (latticeModule m hm m).YM (Ec m hm) (-(((2 * m - 2 : ℕ) : ℤ) - n) - 1)
        (latStateGen (latP m) q ((0 : ℤ) : (latP m).carrier)) =
      kap m m (-1) 0 • latStateGen (latP m)
        (EEVec (latP m) ((-1 : ℤ) : (latP m).carrier) (-(p : ℤ)) q)
          ((-1 : ℤ) : (latP m).carrier) := by
  have h22 : ((2 * m - 2 : ℕ) : ℤ) = 2 * m - 2 := by omega
  rw [YM_Ec, latticeModule_latChargeGen, latticeModule_latChargeGen,
    EEVec_eq_zero_of_lt (latP m) ((1 : ℤ) : (latP m).carrier) hq (by rw [h22]; omega)]
  rw [show latStateGen (latP m) (0 : FockN (rank (latP m))) _ = 0 by simp [latStateGen],
    smul_zero, zero_add]
  congr 2
  congr 1
  congr 1; rw [h22]; omega


/-- The composite `E_{J-n} E_n` on `e^{λ_s}`. -/
theorem E_comp_zero (s : ℕ) (hs : s ≤ m) (n : ℕ) :
    (latticeModule m hm s).YM (Ec m hm) (-(((2 * m - 2 : ℕ) : ℤ) - n) - 1)
      ((latticeModule m hm s).YM (Ec m hm) (-(n : ℤ) - 1) (latVacuumGen (latP m))) =
      (if n < s then kap m s (-1) 0 * kap m s 1 (-1) * kappa (-(2 * m : ℂ)) (s - 1 - n)
        else 0) • latVacuumGen (latP m) := by
  rw [latVacuumGen, show (0 : (latP m).carrier) = ((0 : ℤ) : (latP m).carrier) from rfl,
    E_first_zero]
  split_ifs with hn
  · rw [map_smul, E_second_neg m hm s hs n (s - 1 - n) (by omega)
      (vSchur_mem_gradingWN (latP m) _ _), EEVec_neg_vSchur (latP m) (latP_posDef m hm),
      latStateGen_csmul, smul_smul, smul_smul, latP_form, kZ_nonneg _ (by positivity),
      Int.toNat_natCast]
    congr 1
    push_cast
    ring_nf
  · simp

/-- The composite `E_{J-n} E_n` on `e^{λ_m - α}` (at `s = m`). -/
theorem E_comp_neg (n : ℕ) (hn : n < m) :
    (latticeModule m hm m).YM (Ec m hm) (-(((2 * m - 2 : ℕ) : ℤ) - n) - 1)
      ((latticeModule m hm m).YM (Ec m hm) (-(n : ℤ) - 1)
        (latStateGen (latP m) (vacuumN _) ((-1 : ℤ) : (latP m).carrier))) =
      (kap m m (-1) 0 * kap m m 1 (-1) * kappa (-(2 * m : ℂ)) (m - 1 - n)) •
        latStateGen (latP m) (vacuumN _) ((-1 : ℤ) : (latP m).carrier) := by
  rw [E_first_neg m hm n hn, map_smul, E_second_zero m hm n (m - 1 - n) (by omega)
      (vSchur_mem_gradingWN (latP m) _ _), EEVec_neg_vSchur (latP m) (latP_posDef m hm),
      latStateGen_csmul, smul_smul, smul_smul, latP_form, kZ_nonneg _ (by positivity),
      Int.toNat_natCast]
  congr 1
  push_cast
  ring_nf

/-- The telescope coefficients. -/
abbrev tc (n : ℕ) : ℂ := (-1 : ℂ) ^ n * ((2 * m - 2).choose n : ℂ)

/-- The `E`-telescope on the top `e^{λ_s}` of `V_{L+λ_s}`, `1 ≤ s ≤ m`. -/
theorem telescope_charged (s : ℕ) (hs1 : 1 ≤ s) (hs : s ≤ m) :
    ∑ n ∈ Finset.range m, tc m n •
      mode ((resN m hm (latticeModule m hm s)).toWeakModule.YM (EP m hm))
        (((2 * m - 2 : ℕ) : ℤ) - n)
        (mode ((resN m hm (latticeModule m hm s)).toWeakModule.YM (EP m hm)) n
          (latVacuumGen (latP m))) =
      (kap m s (-1) 0 * kap m s 1 (-1) * s) • latVacuumGen (latP m) := by
  simp only [mode_apply]
  change ∑ n ∈ Finset.range m, tc m n •
      (latticeModule m hm s).YM (Ec m hm) (-(((2 * m - 2 : ℕ) : ℤ) - n) - 1)
        ((latticeModule m hm s).YM (Ec m hm) (-(n : ℤ) - 1) (latVacuumGen (latP m))) = _
  simp only [E_comp_zero m hm s hs, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hs)]
  · rw [Finset.sum_congr rfl (fun n hn => by rw [if_pos (Finset.mem_range.mp hn)])]
    rw [← telescope_kappa_sum m hm s hs1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  · intro n _ hn
    rw [if_neg (by simpa using hn), mul_zero]


/-- The `E`-telescope on the half-lattice top vectors (`s = m`): eigenvalue `m`. -/
theorem telescope_half (σ : ℂ) :
    ∑ n ∈ Finset.range m, tc m n •
      mode ((resN m hm (latticeModule m hm m)).toWeakModule.YM (EP m hm))
        (((2 * m - 2 : ℕ) : ℤ) - n)
        (mode ((resN m hm (latticeModule m hm m)).toWeakModule.YM (EP m hm)) n
          (halfVector m σ)) =
      (m : ℂ) • halfVector m σ := by
  simp only [mode_apply]
  change ∑ n ∈ Finset.range m, tc m n •
      (latticeModule m hm m).YM (Ec m hm) (-(((2 * m - 2 : ℕ) : ℤ) - n) - 1)
        ((latticeModule m hm m).YM (Ec m hm) (-(n : ℤ) - 1) (halfVector m σ)) = _
  have hterm : ∀ n ∈ Finset.range m, tc m n •
      (latticeModule m hm m).YM (Ec m hm) (-(((2 * m - 2 : ℕ) : ℤ) - n) - 1)
        ((latticeModule m hm m).YM (Ec m hm) (-(n : ℤ) - 1) (halfVector m σ)) =
      (tc m n * kappa (-(2 * m : ℂ)) (m - 1 - n)) • halfVector m σ := by
    intro n hn
    have hnm := Finset.mem_range.mp hn
    have h0 := E_comp_zero m hm m le_rfl n
    rw [if_pos hnm, half_transition_product, one_mul] at h0
    have h1 := E_comp_neg m hm n hnm
    rw [half_transition_product, one_mul] at h1
    rw [halfVector, map_add, map_add, map_smul, map_smul, h0, h1]
    module
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, telescope_kappa_sum m hm m hm]

/-! ## §3  Character values -/

theorem lowest_mem_Omega {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2mPlus m hm) M) {h : ℂ} (hlow : IsLowestWeight N h) {y : M}
    (hy : y ∈ N.weight h) : y ∈ Omega N.toWeakModule := by
  intro β v hv n hn
  exact mode_lowering_vanish N hlow hv hy hn

theorem topEvaluation_mk_eq_oMod {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2mPlus m hm) M) {y : M} (hy : y ∈ Omega N.toWeakModule) {a : VP m hm}
    {k : ℤ} (ha : a ∈ (V2mPlus m hm).grading k) :
    topEvaluation N.toWeakModule y hy (VOA.mk (V2mPlus m hm) a) = oMod N a y := by
  rw [topEvaluation_mk, oLevW_homogeneous _ 0 ha, oMod_homogeneous N ha, add_zero]

@[reducible] local instance zhuRing2 : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuAlgebra2 : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-- The value of `zetaE` at a character realized on a top eigenvector whose telescope is
known. -/
theorem zetaE_eq_of_top (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2mPlus m hm) M) {h : ℂ} (hlow : IsLowestWeight N h) {y : M}
    (hy : y ∈ N.weight h) (hy0 : y ≠ 0) (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ)
    (hg : ∀ i : Fin 3, oMod N (gP m hm i) y = χ (VOA.mk (V2mPlus m hm) (gP m hm i)) • y)
    (c : ℂ)
    (ht : ∑ n ∈ Finset.range m, tc m n •
      mode (N.toWeakModule.YM (EP m hm)) (((2 * m - 2 : ℕ) : ℤ) - n)
        (mode (N.toWeakModule.YM (EP m hm)) n y) = c • y) :
    χ (zetaE m hm) = c := by
  have hΩ := lowest_mem_Omega m hm N hlow hy
  have h1 := topEvaluation_eq_char m hm hm2 N.toWeakModule hΩ χ (fun i => by
    rw [topEvaluation_mk_eq_oMod m hm N hΩ (gP_mem_grading m hm i)]
    exact hg i) (zetaE m hm)
  rw [← telescopeE_eq m hm _ hΩ, ht] at h1
  have h2 : (χ (zetaE m hm) - c) • y = 0 := by rw [sub_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hy0

/-- Every charged character takes the value `κ₁κ₂(r+1) ≠ 0` on `zetaE`. -/
theorem charged_zetaE_ne_zero (hm2 : 2 ≤ m) (r : Fin (m - 1))
    (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ) (hχ : HasValues m hm (.inl r) χ) :
    χ (zetaE m hm) ≠ 0 := by
  have hr := r.isLt
  set s : ℕ := r.val + 1 with hs
  have hj : |(s : ℤ)| < (m : ℤ) := by
    rw [abs_of_nonneg (by positivity)]; omega
  let h : ℂ := (((((s : ℤ) : ℝ) ^ 2 / (4 * m) : ℝ)) : ℂ)
  let N := resN m hm (latticeModule m hm s)
  have hlow : IsLowestWeight N h := latticeModule_isLowestWeight m hm s hj.le
  have hx : latVacuumGen (latP m) ∈ N.weight h := latticeModule_vacuum_mem m hm s
  have hval : (((values m (twistedScale m) (.inl r)).1 : ℝ) : ℂ) = h := by
    simp [values, h, hs]
  have g0 : oMod N (gP m hm 0) (latVacuumGen (latP m)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) • latVacuumGen (latP m) := by
    rw [hχ.1, hval]
    change oMod N (V2mPlus m hm).conformalVector _ = h • _
    rw [oMod_conformalVector]; exact N.L0_weight _ _ hx
  have g1 : oMod N (gP m hm 1) (latVacuumGen (latP m)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) • latVacuumGen (latP m) := by
    rw [hχ.2.1]
    change oMod N (WP m hm) _ = _
    rw [oMod_resN m hm _ (WP_mem_grading m hm), WP_coe, oMod_W_V2m m hm _ hlow hx]
    congr 1
    simp [values, h, hs, Complex.ofReal_mul]
  have g2 : oMod N (gP m hm 2) (latVacuumGen (latP m)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) • latVacuumGen (latP m) := by
    rw [hχ.2.2]
    change oMod N (EP m hm) _ = _
    rw [oMod_resN m hm _ (EP_mem_grading m hm), oMod_E_lat_vac m hm s hj]
    simp [values]
  have hz := zetaE_eq_of_top m hm hm2 N hlow hx (latVacuumGen_ne_zero' m hm) χ (by
    intro i; fin_cases i
    exacts [g0, g1, g2]) _ (telescope_charged m hm s (by omega) (by omega))
  rw [hz]
  exact mul_ne_zero (mul_ne_zero (kap_ne_zero m s (-1) 0) (kap_ne_zero m s 1 (-1)))
    (by exact_mod_cast (show s ≠ 0 by omega))

/-- Every half-lattice character takes the value `m` on `zetaE`. -/
theorem half_zetaE (hm2 : 2 ≤ m) (σ : ℂ) (hσ : σ * σ = 1)
    (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ)
    (h0 : χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) = (m : ℂ) / 4)
    (h1 : χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) = (m : ℂ) / 2)
    (h2 : χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) = σ) :
    χ (zetaE m hm) = m := by
  let N := resN m hm (latticeModule m hm m)
  have he : ((((m : ℤ) : ℝ) ^ 2 / (4 * m) : ℝ) : ℂ) = (m : ℂ) / 4 := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    push_cast; field_simp
  have hl : IsLowestWeight N ((m : ℂ) / 4) := by
    rw [← he]; exact latticeModule_isLowestWeight m hm m (by simp)
  have hx := halfVector_mem m hm σ
  have g0 : oMod N (gP m hm 0) (halfVector m σ) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) • halfVector m σ := by
    rw [h0]
    change oMod N (V2mPlus m hm).conformalVector _ = _
    rw [oMod_conformalVector, N.L0_weight _ _ hx]
  have g1 : oMod N (gP m hm 1) (halfVector m σ) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) • halfVector m σ := by
    rw [h1]
    change oMod N (WP m hm) _ = _
    rw [oMod_resN m hm _ (WP_mem_grading m hm), WP_coe, oMod_W_V2m m hm _ hl hx]
    congr 1; ring
  have g2 : oMod N (gP m hm 2) (halfVector m σ) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) • halfVector m σ := by
    rw [h2]
    exact halfVector_E m hm σ hσ
  exact zetaE_eq_of_top m hm hm2 N hl hx (halfVector_ne_zero m σ) χ (by
    intro i; fin_cases i
    exacts [g0, g1, g2]) _ (telescope_half m hm σ)

end VOA.Classification.COne.PlusRat2
