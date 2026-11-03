import VOA.Classification.COne.OrbRat6Sep
import VOA.Classification.COne.OrbRat6Cert
import VOA.Classification.COne.PlusRat5Fock

/-! # The Heisenberg eigenvalue `heisVal j` and the twisted separation

* `vv3_eq`: `f₀³ e^{3β} = R3lit` (kernel certificates `OrbRat6Cert`), with `c = chargeCoord(−β)`.
* `A3_eq`: the `V₁₈` preimage is `evalRaw x9 R3lit`, `x9 (i+1) = μ⁻¹ h(−i−1)`, `μ` the
  oscillator matrix of `scaleMorph`.
* `word_top`: on the lowest-weight vector `e^{λ_j}` of `V_{L+λ_j}` the zero mode of a
  Heisenberg word `h(−i₁−1)⋯h(−i_k−1)𝟙` acts by `∏ (−1)^{i_r} μ₀`, `μ₀ = λ_j`
  (via the iterate formula, `heis_iter`).
* `heisVal_formula`: `heisVal j = X³(X²−1)²(X²−4)/1440`, `X = j/3`.
* `heisenbergTopSeparation` and `cubicTwistedDoubledPairs_holds`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex
  MvPolynomial VOA.LatGen.Screen OrbC2b OrbRat2 OrbRat5 VertexOperatorAlgebra ConverseUniverse
  PlusSplitting PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible PlusUnitary
  VOA.SparseRational OrbC2e PlusC2Eval PlusRat5

/-! ## §1 `v₃` as a raw polynomial -/

/-- The charge coordinate `c = chargeCoord (−β)`. -/
abbrev cm : ℂ := chargeCoord (latP 1) (-a1 1) (a0 1)

theorem cm_sq : cm * cm = ((2 : ℚ) : ℂ) := by
  have h := PlusC2.cα_sq 1 le_rfl
  have hn : cm = -PlusC2.cα 1 := OrbC2e.chargeCoord_neg (latP 1) (a1 1) (a0 1)
  rw [hn, neg_mul_neg, h]
  norm_num

theorem evRc_cert {s : ℤ} {P R : RawPoly ℕ} (h : normR (reduceR 2 (expPolyR s P)) = R) :
    evRc (a0 1) cm (expPolyR s P) = evRc (a0 1) cm R := by
  rw [← h, evRc_normR, evRc_reduceR _ _ 2 cm_sq]

theorem evRc_word_cert {s : ℤ} {w : List ℕ} {R : RawPoly ℕ}
    (h : normR (reduceR 2 (expWordR w s)) = R) :
    evRc (a0 1) cm (expWordR w s) = evRc (a0 1) cm R := by
  rw [← h, evRc_normR, evRc_reduceR _ _ 2 cm_sq]

theorem fo_evRc (γ : ℤ) (P : RawPoly ℕ) :
    fo (latStateGen (latP 1) (evRc (a0 1) cm P) γ) =
      latStateGen (latP 1) (evRc (a0 1) cm (expPolyR (-1 + 2 * γ) P)) (γ - 1 : ℤ) := by
  rw [fo_eq]
  have h := V2m_charge_smul_evRc 1 le_rfl (-a1 1) γ 0 P
  rw [PlusCharacterTable.rankOne_cocycle, one_smul] at h
  change (V2m 1 le_rfl).smul _ 0 _ = _
  rw [h]
  have e1 : (-0 - 1 - (latP 1).form (-a1 1) γ) = -1 + 2 * γ := by
    rw [latP_form]; change (-0 - 1 - 2 * ((1 : ℕ) : ℤ) * (-1) * γ : ℤ) = _; push_cast; ring
  rw [e1]
  congr 1
  change (-(1 : ℤ) + γ : ℤ) = γ - 1
  ring

theorem evRc_one : evRc (a0 1) cm [(1, [])] = 1 := by
  rw [evRc_cons, evRc_nil, evalWordC_nil]
  simp

theorem R3_sum : evRc (a0 1) cm (expPolyR 1 R2lit) = evRc (a0 1) cm R3lit := by
  rw [← cert_R3comb, evRc_normR, evRc_reduceR _ _ 2 cm_sq]
  change evRc (a0 1) cm (normR (R2lit.flatMap fun t => scaleR t.1 (expWordR t.2 1))) = _
  rw [evRc_normR]
  simp only [R2lit, R3comb, List.flatMap_cons, List.flatMap_nil, List.append_nil, evRc_append,
    evRc_scaleR, evRc_word_cert cert_W0, evRc_word_cert cert_W1, evRc_word_cert cert_W2,
    evRc_word_cert cert_W3, evRc_word_cert cert_W4, evRc_word_cert cert_W5,
    evRc_word_cert cert_W6, evRc_word_cert cert_W7, evRc_word_cert cert_W8,
    evRc_word_cert cert_W9, evRc_word_cert cert_W10, evRc_word_cert cert_W11,
    evRc_word_cert cert_W12, evRc_word_cert cert_W13, evRc_word_cert cert_W14,
    evRc_word_cert cert_W15]
  simp only [add_assoc]

/-- `f₀³ e^{3β}` explicitly. -/
theorem vv3_eq : vv 3 = latStateGen (latP 1) (evRc (a0 1) cm R3lit) (0 : ℤ) := by
  have h0 : vv 0 = latStateGen (latP 1) (evRc (a0 1) cm [(1, [])]) (3 : ℤ) := by
    rw [evRc_one, vv_zero]; rfl
  have h1 : vv 1 = latStateGen (latP 1) (evRc (a0 1) cm R1lit) (2 : ℤ) := by
    rw [← fo_vv, h0, fo_evRc, show (-1 + 2 * (3 : ℤ)) = 5 by norm_num, evRc_cert cert_R1]
    rfl
  have h2 : vv 2 = latStateGen (latP 1) (evRc (a0 1) cm R2lit) (1 : ℤ) := by
    rw [← fo_vv, h1, fo_evRc, show (-1 + 2 * (2 : ℤ)) = 3 by norm_num, evRc_cert cert_R2]
    rfl
  rw [← fo_vv, h2, fo_evRc, show (-1 + 2 * (1 : ℤ)) = 1 by norm_num, R3_sum]
  rfl

/-! ## §2 The `V₁₈` preimage of `v₃` -/

/-- The frame index of `V₁₈`. -/
abbrev a9 : Fin (rank (latP (1 * 3 ^ 2))) := a0 (1 * 3 ^ 2)

/-- The oscillator scale `μ` of `scaleMorph`. -/
abbrev muS : ℂ := oscMatrix (latP (1 * 3 ^ 2)) (latP 1) (scaleIota 1 3) (a0 1) a9

/-- The charge coordinate of `α'` in `V₁₈`. -/
abbrev c9 : ℂ := chargeCoord (latP (1 * 3 ^ 2)) ((1 : ℤ) : (latP (1 * 3 ^ 2)).carrier) a9

theorem cm_ne : cm ≠ 0 := by
  intro h; have := cm_sq; rw [h, zero_mul] at this; norm_num at this

theorem chargeCoord_three :
    chargeCoord (latP 1) ((3 : ℤ) : (latP 1).carrier) (a0 1) = -3 * cm := by
  have hneg : cm = -chargeCoord (latP 1) ((1 : ℤ) : (latP 1).carrier) (a0 1) :=
    OrbC2e.chargeCoord_neg (latP 1) (a1 1) (a0 1)
  have h2 := chargeCoord_add (latP 1) ((1 : ℤ) : (latP 1).carrier) ((1 : ℤ) : (latP 1).carrier)
    (a0 1)
  have h3 := chargeCoord_add (latP 1) ((2 : ℤ) : (latP 1).carrier) ((1 : ℤ) : (latP 1).carrier)
    (a0 1)
  change chargeCoord (latP 1) ((2 : ℤ) : (latP 1).carrier) (a0 1) = _ at h2
  change chargeCoord (latP 1) ((3 : ℤ) : (latP 1).carrier) (a0 1) = _ at h3
  rw [h3, h2, hneg]
  ring

theorem muS_c9 : muS * c9 = -3 * cm := by
  have h := congrFun (oscMatrix_chargeCoord (latP (1 * 3 ^ 2)) (latP 1)
    (latP_posDef _ (one_le_mn2 1 le_rfl 3)) (scaleIota 1 3)
    ((1 : ℤ) : (latP (1 * 3 ^ 2)).carrier)) (a0 1)
  simp only [Matrix.mulVec, dotProduct] at h
  rw [sum_rankOne (1 * 3 ^ 2), scaleIota_one, chargeCoord_three] at h
  exact h

theorem muS_ne : muS ≠ 0 := by
  intro h
  have := muS_c9
  rw [h, zero_mul] at this
  have h2 : cm = 0 := by linear_combination this / 3
  exact cm_ne h2

/-- `μ₀ = λ_j`, the shifted momentum of `e^{λ_j}`. -/
abbrev mu0 (j : ℤ) : ℂ := mu (1 * 3 ^ 2) j ((0 : ℤ) : (latP (1 * 3 ^ 2)).carrier)

theorem c9_mu0 (j : ℤ) : c9 * mu0 j = j := by
  have h := sum_chargeCoord_lamShift (latP (1 * 3 ^ 2)) (glueLat (1 * 3 ^ 2) j)
    (glueIota (1 * 3 ^ 2) j) (glueDelta (1 * 3 ^ 2) j) (latP_posDef _ (one_le_mn2 1 le_rfl 3))
    (glueLat_posDef _ (one_le_mn2 1 le_rfl 3) j) ((1 : ℤ) : (latP (1 * 3 ^ 2)).carrier)
  rw [sum_rankOne (1 * 3 ^ 2), glueIota_delta] at h
  have hz : chargeCoord (latP (1 * 3 ^ 2)) ((0 : ℤ) : (latP (1 * 3 ^ 2)).carrier)
      (a0 (1 * 3 ^ 2)) = 0 := chargeCoord_zero _ _
  rw [mu0, mu, hz, zero_add]
  rw [h]
  push_cast
  ring

/-- `ν_j = μ⁻¹ λ_j = −j/(3c)`. -/
theorem nu_eq (j : ℤ) : muS⁻¹ * mu0 j = -(j : ℂ) / 3 * cm⁻¹ := by
  have h1 := muS_c9
  have h2 := c9_mu0 j
  have hc9 : c9 ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact cm_ne (by linear_combination (1 / 3 : ℂ) * h1)
  have hmu : mu0 j = (j : ℂ) / c9 := by rw [eq_div_iff hc9, mul_comm]; exact h2
  have hmuS : muS = -3 * cm / c9 := by rw [eq_div_iff hc9]; exact h1
  rw [hmu, hmuS]
  field_simp
  try ring

/-- The raw variables of `V₁₈`: `0 ↦ c`, `i+1 ↦ μ⁻¹ h(−i−1)`. -/
noncomputable def x9 : ℕ → FockN (rank (latP (1 * 3 ^ 2)))
  | 0 => MvPolynomial.C cm
  | i + 1 => MvPolynomial.C muS⁻¹ * X (i, a9)

/-- The Fock map of `scaleMorph`. -/
abbrev fockS : FockN (rank (latP (1 * 3 ^ 2))) →ₐ[ℂ] FockN (rank (latP 1)) :=
  fockMap (oscMatrix (latP (1 * 3 ^ 2)) (latP 1) (scaleIota 1 3))

theorem fockS_x9 (v : ℕ) : fockS (x9 v) = xvc (a0 1) cm v := by
  cases v with
  | zero => simp [x9, xvc, fockS, fockMap]
  | succ i =>
    simp only [x9, xvc, map_mul]
    rw [fockMap_X, Finset.sum_eq_single (a0 1) (fun b _ hb => absurd (fin_eq_a0' b) hb)
      (fun h => absurd (Finset.mem_univ _) h)]
    have hc : fockS (MvPolynomial.C muS⁻¹) = MvPolynomial.C muS⁻¹ := by
      rw [fockS, fockMap, MvPolynomial.aeval_C]; rfl
    rw [hc, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← MvPolynomial.C_mul,
      inv_mul_cancel₀ muS_ne, MvPolynomial.C_1, one_mul]

theorem fockS_evalWord (w : List ℕ) :
    fockS (evalWord x9 w) = evalWord (xvc (a0 1) cm) w := by
  induction w with
  | nil => simp [evalWord]
  | cons v w ih =>
    rw [show evalWord x9 (v :: w) = x9 v * evalWord x9 w by simp [evalWord],
      evalWordC_cons, map_mul, fockS_x9, ih]

theorem fockS_ratAlg (q : ℚ) :
    fockS (algebraMap ℚ (FockN (rank (latP (1 * 3 ^ 2)))) q) =
      algebraMap ℚ (FockN (rank (latP 1))) q := by
  rw [IsScalarTower.algebraMap_apply ℚ ℂ (FockN _), AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply]

theorem fockS_evalRaw (R : RawPoly ℕ) :
    fockS (evalRaw x9 R) = evRc (a0 1) cm R := by
  induction R with
  | nil => simp [evalRaw]
  | cons t R ih =>
    obtain ⟨q, w⟩ := t
    rw [evRc_cons, ← ih]
    simp only [evalRaw, List.map_cons, List.sum_cons, map_add, algebraMap_rat_mul, map_smul,
      fockS_evalWord]

theorem sm_latStateGen0 (p : FockN (rank (latP (1 * 3 ^ 2)))) :
    sm (latStateGen (latP (1 * 3 ^ 2)) p (0 : ℤ)) = latStateGen (latP 1) (fockS p) (0 : ℤ) := by
  change latMorph _ _ _ _ = _
  rw [latMorph_latStateGen]
  have h0 : latCob (latP (1 * 3 ^ 2)) (latP 1) (scaleIota 1 3)
      ((0 : ℤ) : (latP (1 * 3 ^ 2)).carrier) = 1 := latCob_zero _ _ _
  have h1 : scaleIota 1 3 ((0 : ℤ) : (latP (1 * 3 ^ 2)).carrier) = ((0 : ℤ) : (latP 1).carrier) :=
    map_zero _
  rw [h0, one_smul, h1]

/-- The explicit `V₁₈` Heisenberg state `A₃`. -/
theorem A3_eq : A3 = latStateGen (latP (1 * 3 ^ 2)) (evalRaw x9 R3lit) (0 : ℤ) := by
  apply scaleMorph_injective 1 le_rfl 3
  change sm _ = sm _
  rw [sm_A3, sm_latStateGen0, fockS_evalRaw, vv3_eq]

/-! ## §3 Zero modes of Heisenberg words on `e^{λ_j}` -/

/-- The current `h(−1)𝟙` of `V₁₈`. -/
abbrev hcur : Sp9 := ls (1 * 3 ^ 2) hR

theorem hcur_grading : hcur ∈ V18.grading 1 := by
  have := h_mem_grading (1 * 3 ^ 2) (one_le_mn2 1 le_rfl 3)
  simpa using this

theorem Y_hcur : YfullGen (latP (1 * 3 ^ 2)) (latP_even _) (latP_posDef _ (one_le_mn2 1 le_rfl 3))
    hcur = alphaLatGen (latP (1 * 3 ^ 2)) a9 := by
  rw [hcur, ls_hR, curState]
  rw [show ((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) from rfl, YfullGen_rTensor_current]
  have h1 : YfullGen (latP (1 * 3 ^ 2)) (latP_even _) (latP_posDef _ (one_le_mn2 1 le_rfl 3))
      (latVacuumGen (latP (1 * 3 ^ 2))) = idField := by
    have := (latticeVOAGen (latP (1 * 3 ^ 2)) (latP_even _)
      (latP_posDef _ (one_le_mn2 1 le_rfl 3))).vacuum_Y
    change YfullGen (latP (1 * 3 ^ 2)) (latP_even _) (latP_posDef _ (one_le_mn2 1 le_rfl 3))
      (latVacuumGen (latP (1 * 3 ^ 2))) = 1 at this
    rw [this]
    funext t
    rw [idField_apply]
    rfl
  rw [nprod_congr_right _ (YfullGen_isField _ _ _ _) idField_isField h1, nprod_idField_right,
    genFieldLatGen_zero]

/-- Creation: `h₍₋ᵢ₋₁₎ (q ⊗ e⁰) = (h(−i−1) q) ⊗ e⁰` in `V₁₈`. -/
theorem creation9 (i : ℕ) (q : FockN (rank (latP (1 * 3 ^ 2)))) :
    V18.smul hcur (-((i : ℤ) + 1)) (latStateGen (latP (1 * 3 ^ 2)) q (0 : ℤ)) =
      latStateGen (latP (1 * 3 ^ 2)) (X (i, a9) * q) (0 : ℤ) := by
  rw [PreVertexAlgebra.smul_def, mode_apply]
  change YfullGen (latP (1 * 3 ^ 2)) (latP_even _) (latP_posDef _ (one_le_mn2 1 le_rfl 3))
    hcur _ _ = _
  rw [Y_hcur, alphaLatGen_latStateGen, if_neg (by omega), add_zero,
    oscN_apply_neg _ _ _ (by omega)]
  congr 3
  simp

theorem negOnePow_neg_succ (i : ℕ) : -(negOnePow (-((i : ℤ) + 1))) = (-1 : ℂ) ^ i := by
  rcases Nat.even_or_odd i with h | h
  · have h1 : ¬ _root_.Even (-((i : ℤ) + 1)) := by
      rw [even_neg, Int.even_add_one, not_not]; exact_mod_cast h
    rw [negOnePow, if_neg h1, h.neg_one_pow]; norm_num
  · have h1 : _root_.Even (-((i : ℤ) + 1)) := by
      rw [even_neg, Int.even_add_one]; exact_mod_cast Nat.not_even_iff_odd.mpr h
    rw [negOnePow, if_pos h1, h.neg_one_pow]

/-- `o(h₍₋ᵢ₋₁₎ v) e^{λ_j} = (−1)^i λ_j o(v) e^{λ_j}`. -/
theorem heis_iter {j : ℤ} (hj9 : |j| ≤ 9) {v : Sp9} {d : ℤ} (hv : v ∈ V18.grading d) (i : ℕ) :
    mode ((Nj j).YM (V18.smul hcur (-((i : ℤ) + 1)) v)) (i + d) top9 =
      ((-1 : ℂ) ^ i * mu0 j) • mode ((Nj j).YM v) (d - 1) top9 := by
  have hlow := Nj_lowest hj9
  have htop := top9_mem j
  rw [module_iterate0 (Nj j).toWeakModule hcur v top9 (-((i : ℤ) + 1)) (i + d)]
  rw [finsum_eq_single _ 0]
  · have hv0 : mode ((Nj j).YM v) ((i : ℤ) + d + 0) top9 = 0 :=
      mode_lowering_vanish (Nj j) hlow hv htop (by omega)
    have hh0 : mode ((Nj j).YM hcur) 0 top9 = mu0 j • top9 := by
      have := lat_h_mode (1 * 3 ^ 2) (one_le_mn2 1 le_rfl 3) j 0 1 ((0 : ℤ) : (latP _).carrier)
      rw [if_pos rfl, oscN_zero, LinearMap.zero_apply, zero_add, latStateGen_csmul] at this
      exact this
    rw [hv0, map_zero, zero_sub, hh0, map_smul, cbz_zero,
      show negOnePow 0 = 1 by simp [negOnePow],
      show -((i : ℤ) + 1) + ((i : ℤ) + d) - 0 = d - 1 by ring, ← negOnePow_neg_succ i]
    module
  · intro k hk
    by_cases hneg : k < 0
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
    · have hpos : 0 < k := by omega
      have hv0 : mode ((Nj j).YM v) ((i : ℤ) + d + k) top9 = 0 :=
        mode_lowering_vanish (Nj j) hlow hv htop (by omega)
      have hh0 : mode ((Nj j).YM hcur) k top9 = 0 :=
        mode_lowering_vanish (Nj j) hlow hcur_grading htop (by omega)
      rw [hv0, hh0, map_zero, map_zero, smul_zero, sub_zero, smul_zero]

/-- The weight of a raw word. -/
def wtW (w : List ℕ) : ℤ := (w.map fun v : ℕ => (v : ℤ)).sum

/-- The eigenvalue of a raw word on `e^{λ_j}`. -/
noncomputable def evW (j : ℤ) : List ℕ → ℂ
  | [] => 1
  | 0 :: w => cm * evW j w
  | (i + 1) :: w => ((-1 : ℂ) ^ i * (muS⁻¹ * mu0 j)) * evW j w

theorem wtW_cons (v : ℕ) (w : List ℕ) : wtW (v :: w) = v + wtW w := by
  simp [wtW]

theorem evalWord_x9_cons (v : ℕ) (w : List ℕ) : evalWord x9 (v :: w) = x9 v * evalWord x9 w := by
  simp [evalWord]

theorem mode_add9 (j : ℤ) (u v : Sp9) (n : ℤ) (x : Sp9) :
    mode ((Nj j).YM (u + v)) n x = mode ((Nj j).YM u) n x + mode ((Nj j).YM v) n x := by
  rw [map_add]; rfl

theorem mode_smul9 (j : ℤ) (c : ℂ) (u : Sp9) (n : ℤ) (x : Sp9) :
    mode ((Nj j).YM (c • u)) n x = c • mode ((Nj j).YM u) n x := by
  rw [map_smul]; rfl

/-- Heisenberg words on the top. -/
theorem word_top {j : ℤ} (hj9 : |j| ≤ 9) : ∀ w : List ℕ,
    latStateGen (latP (1 * 3 ^ 2)) (evalWord x9 w) (0 : ℤ) ∈ V18.grading (wtW w) ∧
    mode ((Nj j).YM (latStateGen (latP (1 * 3 ^ 2)) (evalWord x9 w) (0 : ℤ))) (wtW w - 1) top9 =
      evW j w • top9
  | [] => by
    have hvac : latStateGen (latP (1 * 3 ^ 2)) (evalWord x9 []) (0 : ℤ) = V18.vacuum := by
      simp [evalWord]; rfl
    rw [hvac]
    refine ⟨V18.vacuum_mem, ?_⟩
    rw [(Nj j).vacuum_YM]
    simp [wtW, evW, mode_apply]
  | 0 :: w => by
    obtain ⟨hg, hm⟩ := word_top hj9 w
    have hst : latStateGen (latP (1 * 3 ^ 2)) (evalWord x9 (0 :: w)) (0 : ℤ) =
        cm • latStateGen (latP (1 * 3 ^ 2)) (evalWord x9 w) (0 : ℤ) := by
      rw [evalWord_x9_cons, x9, ← MvPolynomial.smul_eq_C_mul, latStateGen_csmul]
    rw [hst, wtW_cons]
    simp only [Nat.cast_zero, zero_add]
    refine ⟨Submodule.smul_mem _ _ hg, ?_⟩
    rw [mode_smul9, hm, smul_smul]
    rfl
  | (i + 1) :: w => by
    obtain ⟨hg, hm⟩ := word_top hj9 w
    have hst : latStateGen (latP (1 * 3 ^ 2)) (evalWord x9 ((i + 1) :: w)) (0 : ℤ) =
        muS⁻¹ • V18.smul hcur (-((i : ℤ) + 1))
          (latStateGen (latP (1 * 3 ^ 2)) (evalWord x9 w) (0 : ℤ)) := by
      rw [creation9, evalWord_x9_cons, x9, mul_assoc, ← MvPolynomial.smul_eq_C_mul,
        latStateGen_csmul]
    rw [hst, wtW_cons]
    refine ⟨Submodule.smul_mem _ _ ?_, ?_⟩
    · have := V18.grading_mode hcur hcur_grading _ hg (-((i : ℤ) + 1))
      convert this using 2
      push_cast; ring
    · rw [mode_smul9, show ((i + 1 : ℕ) : ℤ) + wtW w - 1 = i + wtW w by push_cast; ring,
        heis_iter hj9 hg i, hm, smul_smul, smul_smul]
      congr 1
      simp only [evW]
      ring

theorem heis_sum {j : ℤ} (hj9 : |j| ≤ 9) : ∀ R : RawPoly ℕ, (∀ t ∈ R, wtW t.2 = 9) →
    mode ((Nj j).YM (latStateGen (latP (1 * 3 ^ 2)) (evalRaw x9 R) (0 : ℤ))) 8 top9 =
      (R.map fun t => (t.1 : ℂ) * evW j t.2).sum • top9
  | [], _ => by
    simp [evalRaw, latStateGen]
  | t :: R, hR => by
    have ht := hR t (List.mem_cons_self ..)
    have hrest := heis_sum hj9 R (fun u hu => hR u (List.mem_cons_of_mem _ hu))
    obtain ⟨_, hm⟩ := word_top hj9 t.2
    rw [ht, show (9 : ℤ) - 1 = 8 by norm_num] at hm
    have hsplit : evalRaw x9 (t :: R) = (t.1 : ℂ) • evalWord x9 t.2 + evalRaw x9 R := by
      simp only [evalRaw, List.map_cons, List.sum_cons, algebraMap_rat_mul]
    rw [hsplit, latStateGen_add_boson, latStateGen_csmul, mode_add9, mode_smul9, hm, hrest,
      List.map_cons, List.sum_cons, smul_smul, ← add_smul]

theorem R3_weights : ∀ t ∈ R3lit, wtW t.2 = 9 := by decide

theorem heisVal_eq {j : ℤ} (hj9 : |j| < 9) :
    heisVal j = (R3lit.map fun t => (t.1 : ℂ) * evW j t.2).sum := by
  have h := heisVal_spec hj9
  rw [A3_eq, heis_sum hj9.le R3lit R3_weights] at h
  have h2 := sub_eq_zero.mpr h
  rw [← sub_smul] at h2
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact (sub_eq_zero.mp h3).symm
  · exact absurd h3 top9_ne

/-- `heisVal j = X³(X²−1)²(X²−4)/1440`, `X = j/3`. -/
theorem heisVal_formula {j : ℤ} (hj9 : |j| < 9) :
    heisVal j =
      ((j : ℂ) / 3) ^ 3 * (((j : ℂ) / 3) ^ 2 - 1) ^ 2 * (((j : ℂ) / 3) ^ 2 - 4) / 1440 := by
  rw [heisVal_eq hj9]
  simp only [R3lit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, evW, nu_eq]
  set t := cm⁻¹ with ht
  have h1 : cm * t = 1 := mul_inv_cancel₀ cm_ne
  have h2 : t * t = 1 / 2 := by
    rw [ht, ← mul_inv, cm_sq]; norm_num
  have h3 : cm * t ^ 3 = 1 / 2 := by
    rw [show cm * t ^ 3 = (cm * t) * (t * t) by ring, h1, h2]; ring
  have h5 : cm * t ^ 5 = 1 / 4 := by
    rw [show cm * t ^ 5 = (cm * t) * (t * t) * (t * t) by ring, h1, h2]; ring
  have h7 : cm * t ^ 7 = 1 / 8 := by
    rw [show cm * t ^ 7 = (cm * t) * (t * t) * (t * t) * (t * t) by ring, h1, h2]; ring
  have h9 : cm * t ^ 9 = 1 / 16 := by
    rw [show cm * t ^ 9 = (cm * t) * (t * t) * (t * t) * (t * t) * (t * t) by ring, h1, h2]; ring
  push_cast
  linear_combination (1 / 180 * (-(j : ℂ) / 3) ^ 3) * h3 + (-1 / 40 * (-(j : ℂ) / 3) ^ 5) * h5 +
    (1 / 30 * (-(j : ℂ) / 3) ^ 7) * h7 + (-1 / 90 * (-(j : ℂ) / 3) ^ 9) * h9

/-- The Heisenberg separation. -/
theorem heisenbergTopSeparation : HeisenbergTopSeparation := by
  intro j hj
  have hall : ∀ x ∈ ({1, 2, 4, 5, 7, 8} : Finset ℤ), |x| < 9 := by decide
  have hj9 := hall j hj
  have hj9' : |(-j)| < 9 := by rwa [abs_neg]
  rw [heisVal_formula hj9, heisVal_formula hj9']
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- **The six twisted doubled pairs.** -/
theorem cubicTwistedDoubledPairs_holds : CubicTwistedDoubledPairs :=
  cubicTwistedDoubledPairs_of_heis heisenbergTopSeparation

/-- **The full character table of the tetrahedral model**: 21 pairwise distinct
characters of `A(W)` with the Dong–Jiang weights. -/
theorem cubicZhuCharacterTable_holds : CubicZhuCharacterTable :=
  cubicZhuCharacterTable_of_remaining cubicDoubledPair_nine_four cubicTwistedDoubledPairs_holds

end VOA.Classification.COne.OrbRat6
