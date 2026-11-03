import VOA.Classification.COne.OrbOctaRCEval
import VOA.Classification.COne.OrbOctaRProbe
import VOA.Classification.COne.OrbC2hRange

/-! Neutral measurements without constructing weight-thirty-four Fock vectors. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN MvPolynomial
  PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2g OrbC2h LatMod
local notation "ρ" => OrbOctaR.firstOscillator

theorem firstOscillator_xv (i : ℕ) :
    ρ (xv (a0 1) i) = if i = 0 then 1 else 0 := by
  simp [OrbOctaR.firstOscillator, xv]

theorem firstOscillator_xvc_zero (c : ℂ) : ρ (xvc (a0 1) c 0) = c := by
  simp [xvc, OrbOctaR.firstOscillator]

theorem firstOscillator_xvc_succ (c : ℂ) (i : ℕ) :
    ρ (xvc (a0 1) c (i + 1)) = if i = 0 then 1 else 0 := by
  simp [xvc, OrbOctaR.firstOscillator]

theorem firstOscillator_fAct_nonneg (c : ℂ) (i : ℕ) (s : ℤ) (hs : 0 ≤ s)
    (P : RawPoly ℕ) :
    ρ (evRc (a0 1) c (fActC i s P)) =
      (if i = 0 ∧ s = 0 then 1 else 0) * ρ (evRc (a0 1) c P) := by
  have hm : fMode i s < 0 := by simp only [fMode]; omega
  rw [evRc_fActC, genS_apply, if_neg (ne_of_lt hm), add_zero,
    genFieldN_coeff, LinearMap.smul_apply, map_smul]
  rw [OrbOctaR.firstOscillator_osc_neg _ _ (show -(s + (i : ℤ)) - 1 < 0 by omega)]
  have he : -(s + (i : ℤ)) - 1 = -1 ↔ i = 0 ∧ s = 0 := by omega
  simp only [he]
  by_cases h : i = 0 ∧ s = 0
  · rcases h with ⟨rfl, rfl⟩
    simp
  · simp [h]

theorem sum_zero_indicator (L : List ℤ) (c : ℂ) :
    (L.map fun m => if m = 0 then c else 0).sum = (L.count 0 : ℂ) * c := by
  induction L with
  | nil => simp
  | cons m L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.count_cons]
    by_cases hm : m = 0
    · subst m; simp; ring
    · simp [hm]

theorem wordAct_probe (c : ℂ) (is : List ℕ) (s : ℤ) (hs : 0 ≤ s)
    (w : ℕ) (P : RawPoly ℕ) :
    ρ (evRc (a0 1) c (wordActC is s w P)) =
      if s = 0 then ρ (evalWord (xv (a0 1)) is) * ρ (evRc (a0 1) c P) else 0 := by
  induction is generalizing s w P with
  | nil => by_cases h : s = 0 <;> simp [wordActC, evalWord_nil, evRc_nil, h]
  | cons i is ih =>
    let S := intRange (-((i + 1 + w : ℕ) : ℤ))
      ((max (-1) (((wWt is + w : ℕ) : ℤ) + s)) + ((i + 1 + w : ℕ) : ℤ) + 1).toNat
    have hterm (m : ℤ) :
        ρ (evRc (a0 1) c (if 0 ≤ m then fActC i m (wordActC is (s - m) w P)
          else wordActC is (s - m) ((((i + 1 + w : ℕ) : ℤ) + m).toNat)
            (fActC i m P))) =
        if m = 0 then (if i = 0 then 1 else 0) *
          ρ (evRc (a0 1) c (wordActC is s w P)) else 0 := by
      by_cases hm : 0 ≤ m
      · rw [if_pos hm, firstOscillator_fAct_nonneg _ _ _ hm]
        by_cases hz : m = 0
        · subst m; simp
        · simp [hz]
      · rw [if_neg hm, ih _ (by omega)]
        simp [show s - m ≠ 0 by omega, show m ≠ 0 by omega]
    have hcount : S.count 0 = 1 := by
      dsimp [S]
      rw [count_intRange]
      have hmax := le_max_right (-1 : ℤ) (((wWt is + w : ℕ) : ℤ) + s)
      rw [Int.toNat_of_nonneg (by omega)]
      rw [if_pos (by constructor <;> omega)]
    rw [wordActC, evRc_flatMap, map_list_sum]
    simp only [List.map_map, Function.comp_def, hterm]
    change (S.map _).sum = _
    rw [sum_zero_indicator, hcount, Nat.cast_one, one_mul, ih _ hs]
    rw [evalWord_cons, map_mul, firstOscillator_xv]
    split_ifs <;> simp_all

theorem polyAct_probe (c : ℂ) (Q : RawPoly ℕ) (s : ℤ) (hs : 0 ≤ s)
    (w : ℕ) (P : RawPoly ℕ) :
    ρ (evRc (a0 1) c (polyActC Q s w P)) =
      if s = 0 then ρ (evR (a0 1) Q) * ρ (evRc (a0 1) c P) else 0 := by
  induction Q with
  | nil => simp [polyActC, evR_nil, evRc_nil]
  | cons t Q ih =>
    rcases t with ⟨q, is⟩
    rw [polyActC, List.flatMap_cons, evRc_append, map_add, evRc_scaleR,
      map_smul, wordAct_probe _ _ _ hs]
    change _ + ρ (evRc (a0 1) c (polyActC Q s w P)) = _
    rw [ih, evR_cons, map_add, map_smul]
    by_cases h : s = 0
    · simp only [if_pos h, smul_eq_mul]
      ring
    · simp [h]

theorem polyActW_probe (c : ℂ) (Q : RawPoly ℕ) (s : ℤ) (hs : 0 ≤ s)
    (P : RawPoly ℕ) :
    ρ (evRc (a0 1) c (polyActWC Q s P)) =
      if s = 0 then ρ (evR (a0 1) Q) * ρ (evRc (a0 1) c P) else 0 := by
  induction P with
  | nil => simp [polyActWC, evRc_nil]
  | cons t P ih =>
    rw [polyActWC, List.flatMap_cons, evRc_append, map_add, polyAct_probe _ _ _ hs]
    change _ + ρ (evRc (a0 1) c (polyActWC Q s P)) = _
    rw [ih, show t :: P = [t] ++ P from rfl, evRc_append, map_add]
    split_ifs <;> ring

theorem schur_probe (c : ℂ) (n : ℕ) :
    ρ (evRc (a0 1) c (schurR n)) = c ^ n / (n.factorial : ℂ) := by
  induction n with
  | zero => simp [schurR, evRc_cons, evRc_nil, evalWordC_nil]
  | succ n ih =>
    rw [schurR, evRc_normR, evRc_scaleR, map_smul, evRc_flatMap_range, map_sum]
    simp only [evRc_prependC, map_mul, firstOscillator_xvc_zero,
      firstOscillator_xvc_succ]
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.sub_zero, ih, smul_eq_mul]
      push_cast
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        div_eq_mul_inv, mul_inv_rev, pow_succ]
      ring
    · intro i _ hi; simp [hi]
    · intro h; exact (h (Finset.mem_range.mpr (Nat.succ_pos n))).elim

def wordFirst : List ℕ → ℚ
  | [] => 1
  | i :: is => if i = 0 then wordFirst is else 0

def rawFirst (P : RawPoly ℕ) : ℚ := (P.map fun t => t.1 * wordFirst t.2).sum

theorem wordFirst_sound (is : List ℕ) :
    ρ (evalWord (xv (a0 1)) is) = (wordFirst is : ℂ) := by
  induction is with
  | nil => simp [evalWord_nil, wordFirst]
  | cons i is ih =>
    rw [evalWord_cons, map_mul, firstOscillator_xv, ih]
    by_cases hi : i = 0 <;> simp [wordFirst, hi]

theorem rawFirst_sound (P : RawPoly ℕ) :
    ρ (evR (a0 1) P) = (rawFirst P : ℂ) := by
  induction P with
  | nil => simp [evR_nil, rawFirst]
  | cons t P ih =>
    rw [evR_cons, map_add, map_smul, wordFirst_sound, ih]
    simp [rawFirst, smul_eq_mul]

theorem neutralProbe_sector (d : ℤ) (p : FockN (VOA.IntegralLattice.rank (latP 1))) :
    OrbOctaR.neutralProbe (sector d p) = if 0 = d then ρ p else 0 := by
  change ρ (coordEα (latP 1) 0 (latStateGen (latP 1) p d)) = _
  simp only [latStateGen, coordEα_apply, apply_ite, map_zero]
  by_cases h : (0 : ℤ) = d
  · simp only [if_pos h]
    exact if_pos h
  · simp only [if_neg h]
    exact if_neg h

theorem neutralProbe_NN (P Q : RawPoly ℕ) (n : ℤ) (hn : n ≤ -1) :
    OrbOctaR.neutralProbe ((V2m 1 le_rfl).smul (ls 1 P) n (ls 1 Q)) =
      if n = -1 then (rawFirst P : ℂ) * (rawFirst Q : ℂ) else 0 := by
  have h := V2m_smul_evRcW 1 le_rfl P n 0 (liftR Q)
  rw [evRc_liftR] at h
  change OrbOctaR.neutralProbe ((V2m 1 le_rfl).smul
    (latStateGen _ _ 0) n (latStateGen _ _ 0)) = _
  rw [h]
  change OrbOctaR.neutralProbe (sector 0 _) = _
  rw [neutralProbe_sector, if_pos rfl, polyActW_probe _ _ _ (by omega),
    evRc_liftR, rawFirst_sound, rawFirst_sound]
  simp only [show -n - 1 = 0 ↔ n = -1 by omega]

theorem neutralProbe_EE_zero (b d n : ℤ) (hd : 0 ≠ b + d) :
    OrbOctaR.neutralProbe ((V2m 1 le_rfl).smul (latChargeGen (latP 1) b) n
      (latChargeGen (latP 1) d)) = 0 := by
  rw [V2m_charge_smul_charge, PlusCharacterTable.rankOne_cocycle, one_smul]
  change OrbOctaR.neutralProbe (sector (b + d) _) = 0
  rw [neutralProbe_sector, if_neg hd]

theorem neutralProbe_EN_zero (b n : ℤ) (P : RawPoly ℕ) (hb : 0 ≠ b) :
    OrbOctaR.neutralProbe
      ((V2m 1 le_rfl).smul (latChargeGen (latP 1) b) n (ls 1 P)) = 0 := by
  have h := V2m_charge_smul_evRc 1 le_rfl b 0 n (liftR P)
  rw [evRc_liftR, PlusCharacterTable.rankOne_cocycle, one_smul, add_zero] at h
  rw [show ls 1 P = latStateGen (latP 1) (evR (a0 1) P) 0 from rfl, h]
  change OrbOctaR.neutralProbe (sector b _) = 0
  rw [neutralProbe_sector, if_neg hb]

theorem neutralProbe_NE_zero (b n : ℤ) (P : RawPoly ℕ) (hb : 0 ≠ b) :
    OrbOctaR.neutralProbe
      ((V2m 1 le_rfl).smul (ls 1 P) n (latChargeGen (latP 1) b)) = 0 := by
  have h := V2m_smul_evRcW 1 le_rfl P n b [(1, [])]
  simp only [evRc_cons, evRc_nil, evalWordC_nil, Rat.cast_one, one_smul, add_zero] at h
  rw [show ls 1 P = latStateGen (latP 1) (evR (a0 1) P) 0 from rfl,
    show latChargeGen (latP 1) b = latStateGen (latP 1) 1 b from rfl, h]
  change OrbOctaR.neutralProbe (sector b _) = 0
  rw [neutralProbe_sector, if_neg hb]

theorem neutralProbe_opposite (b : ℤ) (hb : b * b = 16) (j : ℕ) :
    OrbOctaR.neutralProbe
      ((V2m 1 le_rfl).smul (latChargeGen (latP 1) b) (31 - (j : ℤ))
        (latChargeGen (latP 1) (-b))) =
      ((b : ℂ) * cα 1) ^ j / (j.factorial : ℂ) := by
  have hform : (latP 1).form b (-b) = -32 := by
    rw [latP_form, Nat.cast_one, mul_one]
    nlinarith [hb]
  rw [V2m_charge_smul_charge, PlusCharacterTable.rankOne_cocycle, one_smul, hform,
    show -(31 - (j : ℤ)) - 1 - (-32) = (j : ℤ) by ring,
    if_pos (Nat.cast_nonneg j), Int.toNat_natCast]
  change OrbOctaR.neutralProbe (sector ((b : ℤ) + -b)
    (evRc (a0 1) (chargeCoord (latP 1) b (a0 1)) (schurR j))) = _
  rw [add_neg_cancel]
  change OrbOctaR.neutralProbe (sector 0 _) = _
  rw [neutralProbe_sector, if_pos rfl, schur_probe, chargeCoord_one]

theorem neutralProbe_self (P : RawPoly ℕ) (n : ℤ) :
    let x := (2 : ℂ) • latChargeGen (latP 1) (4 : ℤ) + ls 1 P +
      (2 : ℂ) • latChargeGen (latP 1) (-4 : ℤ)
    OrbOctaR.neutralProbe ((V2m 1 le_rfl).smul x n x) =
      4 * OrbOctaR.neutralProbe ((V2m 1 le_rfl).smul
        (latChargeGen (latP 1) (4 : ℤ)) n (latChargeGen (latP 1) (-4 : ℤ))) +
      4 * OrbOctaR.neutralProbe ((V2m 1 le_rfl).smul
        (latChargeGen (latP 1) (-4 : ℤ)) n (latChargeGen (latP 1) (4 : ℤ))) +
      OrbOctaR.neutralProbe ((V2m 1 le_rfl).smul (ls 1 P) n (ls 1 P)) := by
  dsimp only
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    map_add, map_smul, smul_eq_mul]
  rw [neutralProbe_EE_zero 4 4 _ (by norm_num),
    neutralProbe_EE_zero (-4) (-4) _ (by norm_num),
    neutralProbe_EN_zero 4 _ _ (by norm_num),
    neutralProbe_EN_zero (-4) _ _ (by norm_num),
    neutralProbe_NE_zero 4 _ _ (by norm_num),
    neutralProbe_NE_zero (-4) _ _ (by norm_num)]
  ring

end VOA.Classification.COne.OrbOctaRC
