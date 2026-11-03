import VOA.Classification.COne.OrbOctaRCModeTools
import VOA.Classification.COne.OrbOctaRCNeutral
import VOA.Classification.COne.OrbOctaRCVirDirect
import VOA.Classification.COne.OrbOctaRCScreen8
import VOA.Classification.COne.OrbOctaRSpan
import VOA.Classification.COne.OrbC2fTetra

/-! The explicit octahedral primary, with the multiplet normalization fixed. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN MvPolynomial
  PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g OrbC2h LatMod
  OrbPrim OrbOcta OrbOctaR OrbC2b OrbSpan

def primaryNeutralPart0 : RawPoly ℕ :=
  [(mkRat (1) 8505000, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
   (mkRat (-1) 212625, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]),
   (mkRat (1) 283500, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]),
   (mkRat (4) 118125, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]),
   (mkRat (-2) 23625, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3]),
   (mkRat (1) 30375, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2]),
   (mkRat (1) 28350, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2]),
   (mkRat (-1) 4725, [0, 0, 0, 0, 0, 0, 0, 0, 0, 6]),
   (mkRat (-1) 75600, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1]),
   (mkRat (1) 1350, [0, 0, 0, 0, 0, 0, 0, 0, 1, 5]),
   (mkRat (-1) 7875, [0, 0, 0, 0, 0, 0, 0, 0, 2, 4]),
   (mkRat (1) 2520, [0, 0, 0, 0, 0, 0, 0, 0, 3, 3]),
   (mkRat (-8) 7875, [0, 0, 0, 0, 0, 0, 0, 1, 1, 4]),
   (mkRat (-2) 1575, [0, 0, 0, 0, 0, 0, 0, 1, 2, 3]),
   (mkRat (-4) 42525, [0, 0, 0, 0, 0, 0, 0, 2, 2, 2]),
   (mkRat (1) 675, [0, 0, 0, 0, 0, 0, 1, 1, 1, 3]),
   (mkRat (1) 675, [0, 0, 0, 0, 0, 0, 1, 1, 2, 2]),
   (mkRat (4) 1575, [0, 0, 0, 0, 0, 0, 2, 6]),
   (mkRat (-2) 675, [0, 0, 0, 0, 0, 0, 3, 5]),
   (mkRat (4) 5625, [0, 0, 0, 0, 0, 0, 4, 4])]

def primaryNeutralPart1 : RawPoly ℕ :=
  [(mkRat (-1) 540, [0, 0, 0, 0, 0, 1, 1, 1, 1, 2]),
   (mkRat (-1) 525, [0, 0, 0, 0, 0, 1, 1, 6]),
   (mkRat (-2) 675, [0, 0, 0, 0, 0, 1, 2, 5]),
   (mkRat (2) 375, [0, 0, 0, 0, 0, 1, 3, 4]),
   (mkRat (-4) 1125, [0, 0, 0, 0, 0, 2, 2, 4]),
   (mkRat (1) 450, [0, 0, 0, 0, 0, 2, 3, 3]),
   (mkRat (1) 2160, [0, 0, 0, 0, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 270, [0, 0, 0, 0, 1, 1, 1, 5]),
   (mkRat (1) 225, [0, 0, 0, 0, 1, 1, 2, 4]),
   (mkRat (-1) 120, [0, 0, 0, 0, 1, 1, 3, 3]),
   (mkRat (2) 1215, [0, 0, 0, 0, 2, 2, 2, 2]),
   (mkRat (-4) 525, [0, 0, 0, 0, 4, 6]),
   (mkRat (1) 135, [0, 0, 0, 0, 5, 5]),
   (mkRat (-1) 225, [0, 0, 0, 1, 1, 1, 1, 4]),
   (mkRat (1) 135, [0, 0, 0, 1, 1, 1, 2, 3]),
   (mkRat (-2) 405, [0, 0, 0, 1, 1, 2, 2, 2]),
   (mkRat (2) 105, [0, 0, 0, 1, 3, 6]),
   (mkRat (-4) 225, [0, 0, 0, 1, 4, 5]),
   (mkRat (-2) 135, [0, 0, 0, 2, 3, 5]),
   (mkRat (16) 1125, [0, 0, 0, 2, 4, 4])]

def primaryNeutralPart2 : RawPoly ℕ :=
  [(mkRat (1) 540, [0, 0, 1, 1, 1, 1, 2, 2]),
   (mkRat (-2) 105, [0, 0, 1, 1, 2, 6]),
   (mkRat (2) 125, [0, 0, 1, 1, 4, 4]),
   (mkRat (4) 135, [0, 0, 1, 2, 2, 5]),
   (mkRat (-2) 75, [0, 0, 1, 2, 3, 4]),
   (mkRat (-8) 675, [0, 0, 2, 2, 2, 4]),
   (mkRat (1) 90, [0, 0, 2, 2, 3, 3]),
   (mkRat (-1) 1080, [0, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 140, [0, 1, 1, 1, 1, 6]),
   (mkRat (-1) 135, [0, 1, 1, 1, 2, 5]),
   (mkRat (-1) 75, [0, 1, 1, 1, 3, 4]),
   (mkRat (2) 225, [0, 1, 1, 2, 2, 4]),
   (mkRat (1) 60, [0, 1, 1, 2, 3, 3]),
   (mkRat (-2) 135, [0, 1, 2, 2, 2, 3]),
   (mkRat (4) 1215, [0, 2, 2, 2, 2, 2]),
   (mkRat (8) 525, [0, 2, 4, 6]),
   (mkRat (-2) 135, [0, 2, 5, 5]),
   (mkRat (-1) 70, [0, 3, 3, 6]),
   (mkRat (2) 75, [0, 3, 4, 5]),
   (mkRat (-8) 625, [0, 4, 4, 4])]

def primaryNeutralPart3 : RawPoly ℕ :=
  [(mkRat (1) 5760, [1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 360, [1, 1, 1, 1, 1, 5]),
   (mkRat (1) 180, [1, 1, 1, 1, 2, 4]),
   (mkRat (1) 480, [1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 135, [1, 1, 1, 2, 2, 3]),
   (mkRat (1) 405, [1, 1, 2, 2, 2, 2]),
   (mkRat (-2) 175, [1, 1, 4, 6]),
   (mkRat (1) 90, [1, 1, 5, 5]),
   (mkRat (2) 105, [1, 2, 3, 6]),
   (mkRat (-4) 225, [1, 2, 4, 5]),
   (mkRat (-1) 60, [1, 3, 3, 5]),
   (mkRat (2) 125, [1, 3, 4, 4]),
   (mkRat (-8) 945, [2, 2, 2, 6]),
   (mkRat (2) 135, [2, 2, 3, 5]),
   (mkRat (8) 1125, [2, 2, 4, 4]),
   (mkRat (-1) 50, [2, 3, 3, 4]),
   (mkRat (1) 160, [3, 3, 3, 3])]

/-- The oscillator polynomial `(2/5) s_(4,4,4,4)(sqrt(2) h(-i))`. -/
def primaryNeutral : RawPoly ℕ :=
  [primaryNeutralPart0, primaryNeutralPart1, primaryNeutralPart2, primaryNeutralPart3].flatten

set_option maxHeartbeats 2000000 in
-- Exact conversion from the certified fourth screening into neutral coordinates.
set_option maxRecDepth 4096 in
theorem primaryNeutral_screen :
    scaleR (1 / 60) screenState4 = liftR primaryNeutral := by
  decide +kernel

set_option maxHeartbeats 1000000 in
-- Check the oscillator parity of the explicit finite primary.
theorem primaryNeutral_even : ∀ t ∈ primaryNeutral, Even t.2.length := by
  decide +kernel

theorem primaryNeutral_value :
    evRc (a0 1) (cα 1) screenState4 = (60 : ℂ) • evR (a0 1) primaryNeutral := by
  have h := congrArg (evRc (a0 1) (cα 1)) primaryNeutral_screen
  rw [evRc_scaleR, evRc_liftR] at h
  have hs := congrArg (fun v => (60 : ℂ) • v) h
  norm_num [smul_smul] at hs
  exact hs

theorem wv4_four_value : wv 4 4 = (1 / 28 : ℂ) • ls 1 primaryNeutral := by
  rw [wv, cnk, vn4_4_value, primaryNeutral_value, map_smul, smul_smul]
  norm_num [Nat.factorial]
  rfl

theorem wv4_eight_value : wv 4 8 = latChargeGen (latP 1) (-4 : ℤ) := by
  rw [wv, cnk, vn4_8_value]
  simp [screenState8, evRc_cons, evRc_nil, evalWordC_nil, sector, Nat.factorial,
    latChargeGen, smul_smul, vacuumN]

/-- Equality in the actual norm-two lattice VOA, including all charge sectors. -/
theorem X_lattice_value : (OrbOctaR.X : LatModuleGen (latP 1)) =
    (2 : ℂ) • latChargeGen (latP 1) (4 : ℤ) + ls 1 primaryNeutral +
      (2 : ℂ) • latChargeGen (latP 1) (-4 : ℤ) := by
  rw [X_coe, wv_zero, wv4_four_value, wv4_eight_value, smul_smul]
  norm_num

theorem X_ambient_primary :
    (OrbOctaR.X : LatModuleGen (latP 1)) ∈ prim (V2m 1 le_rfl) 16 := by
  rw [Tav_coe ⟨isA4Inv_I4, s3_I4⟩]
  convert T2_prim I4_hom using 1

noncomputable def primaryV8 : LatModuleGen (latP 4) :=
  (2 : ℂ) • latChargeGen (latP 4) (2 : ℤ) + ls 4 primaryNeutral +
    (2 : ℂ) • latChargeGen (latP 4) (-2 : ℤ)


set_option maxHeartbeats 1000000 in
-- Check the finite oscillator grading before taking the bottom coefficient.
theorem primaryNeutral_degrees : ∀ t ∈ liftR primaryNeutral,
    wWtC t.2 = 16 ∧ ∀ i ∈ t.2, 0 < i := by
  decide +kernel

set_option maxHeartbeats 1000000 in
-- The bottom exponential coefficient is a short exact rational sum.
theorem primaryNeutral_bottom : bottomRaw 4 (liftR primaryNeutral) = (465696 / 5, 0) := by
  decide +kernel

theorem primary_bottom_mode :
    (V2m 1 le_rfl).smul (latChargeGen (latP 1) (4 : ℤ)) 15 (ls 1 primaryNeutral) =
      (465696 / 5 : ℂ) • latChargeGen (latP 1) (4 : ℤ) := by
  have h := V2m_charge_smul_evRc 1 le_rfl (4 : ℤ) (0 : ℤ) 15 (liftR primaryNeutral)
  rw [evRc_liftR, PlusCharacterTable.rankOne_cocycle, one_smul] at h
  norm_num only [latP_form, mul_zero, sub_zero, add_zero] at h
  rw [show ls 1 primaryNeutral =
    latStateGen (latP 1) (evR (a0 1) primaryNeutral) (0 : ℤ) from rfl, h]
  change latStateGen (latP 1)
    (evRc (a0 1) (chargeCoord (latP 1) (4 : ℤ) (a0 1))
      (expPolyR (-16) (liftR primaryNeutral))) (4 : ℤ) = _
  have he := expPolyR_bottom (a0 1) (chargeCoord (latP 1) (4 : ℤ) (a0 1))
    (liftR primaryNeutral) 16 primaryNeutral_degrees
  norm_num only at he
  rw [he, chargeCoord_one]
  norm_num only [Int.cast_ofNat]
  have hb := bottomRaw_sound 4 (cα 1) charge_square_two (liftR primaryNeutral)
  norm_num only [Rat.cast_ofNat] at hb
  rw [hb, primaryNeutral_bottom]
  norm_num only [pairValue, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, mul_zero, add_zero]
  exact latStateGen_csmul _ _ _ _

theorem primary_ground_coupling :
    (v2mVirUnitary 1 le_rfl).form
      ((V2m 1 le_rfl).smul (X : LatModuleGen (latP 1)) 15 X)
      (latChargeGen (latP 1) (4 : ℤ)) = (1862784 / 5 : ℂ) := by
  change ambientProbe 1 ((V2m 1 le_rfl).smul (X : LatModuleGen (latP 1)) 15 X) = _
  rw [X_lattice_value, ambientProbe_self _ _ _ ambientProbe_one_T (by norm_num [sgn]),
    primary_bottom_mode, map_smul]
  have he : ambientProbe 1 (latChargeGen (latP 1) (4 : ℤ)) = 1 := by
    change ambientProbe 1 (sector 4 1) = 1
    rw [ambientProbe_sector, if_pos rfl]
    simpa [fw] using (fockForm_monomial
      (r := VOA.IntegralLattice.rank (latP 1)) 0 0 1 1)
  rw [he]
  norm_num

theorem coe_Lneg2_pow (r : ℕ) (v : (orbifold OrbC2b.octa).carrier) :
    (((W.L (-2)) ^ r) v : LatModuleGen (latP 1)) =
      (((V2m 1 le_rfl).L (-2)) ^ r) (v : LatModuleGen (latP 1)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    change (V2m 1 le_rfl).L (-2) _ = _
    exact congrArg ((V2m 1 le_rfl).L (-2)) ih

theorem Lneg2_pow_sector (r : ℕ) (d : ℤ)
    (p : FockN (VOA.IntegralLattice.rank (latP 1))) :
    (((V2m 1 le_rfl).L (-2)) ^ r) (sector d p) =
      sector d (((fockL d (-2)) ^ r) p) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih, L_sector _ _ (by norm_num),
      pow_succ', Module.End.mul_apply]

theorem charged_vacuum_tower (q : FockN (VOA.IntegralLattice.rank (latP 1))) (r : ℕ) :
    chargedProbe (sector 4 q) (((W.L (-2)) ^ r) W.vacuum) = 0 := by
  change (v2mVirUnitary 1 le_rfl).form
    ((((W.L (-2)) ^ r) W.vacuum : (orbifold OrbC2b.octa).carrier) :
      LatModuleGen (latP 1)) (sector 4 q) = 0
  rw [coe_Lneg2_pow]
  change (v2mVirUnitary 1 le_rfl).form
    ((((V2m 1 le_rfl).L (-2)) ^ r) (sector 0 1)) (sector 4 q) = 0
  rw [Lneg2_pow_sector, sector_form, if_neg (by norm_num)]

theorem charged_X_tower (q : FockN (VOA.IntegralLattice.rank (latP 1))) (r : ℕ)
    (hq : (v2mVirUnitary 1 le_rfl).form
      ((((V2m 1 le_rfl).L (-2)) ^ r) (latChargeGen (latP 1) (4 : ℤ))) (sector 4 q) = 1) :
    chargedProbe (sector 4 q) (((W.L (-2)) ^ r) X) = 2 := by
  have hz (d : ℤ) (hd : 4 ≠ d) (p : FockN (VOA.IntegralLattice.rank (latP 1))) :
      (v2mVirUnitary 1 le_rfl).form
        ((((V2m 1 le_rfl).L (-2)) ^ r) (sector d p)) (sector 4 q) = 0 := by
    rw [Lneg2_pow_sector, sector_form, if_neg hd]
  change (v2mVirUnitary 1 le_rfl).form
    ((((W.L (-2)) ^ r) X : (orbifold OrbC2b.octa).carrier) : LatModuleGen (latP 1))
      (sector 4 q) = 2
  rw [coe_Lneg2_pow, X_lattice_value]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hq, show ls 1 primaryNeutral = sector 0 (evR (a0 1) primaryNeutral) from rfl,
    show latChargeGen (latP 1) (-4 : ℤ) = sector (-4) 1 from rfl,
    hz 0 (by norm_num), hz (-4) (by norm_num)]
  norm_num

set_option maxHeartbeats 1000000 in
-- The all-first-oscillator coefficient of the finite neutral primary.
theorem primaryNeutral_first : rawFirst primaryNeutral = 1 / 8505000 := by
  decide +kernel

theorem octaProbe_X : octaProbe X = (1 / 8505000 : ℂ) := by
  change OrbOctaR.neutralProbe (X : LatModuleGen (latP 1)) = _
  rw [X_lattice_value, map_add, map_add, map_smul, map_smul]
  change (2 : ℂ) • OrbOctaR.neutralProbe (sector 4 1) +
    OrbOctaR.neutralProbe (sector 0 (evR (a0 1) primaryNeutral)) +
    (2 : ℂ) • OrbOctaR.neutralProbe (sector (-4) 1) = _
  rw [neutralProbe_sector, neutralProbe_sector, neutralProbe_sector,
    if_neg (by norm_num), if_pos rfl, if_neg (by norm_num),
    rawFirst_sound, primaryNeutral_first]
  norm_num

theorem neutral_mode32 : octaProbe (W.smul X (-1) X) =
    (candidateA32 : ℂ) * (1 / 2) ^ 16 +
      (candidateB32 : ℂ) * (1 / 2) ^ 8 * (1 / 8505000) := by
  change OrbOctaR.neutralProbe ((V2m 1 le_rfl).smul (X : LatModuleGen (latP 1)) (-1) X) = _
  rw [X_lattice_value, neutralProbe_self]
  have hp := neutralProbe_opposite 4 (by norm_num) 32
  have hm := neutralProbe_opposite (-4) (by norm_num) 32
  norm_num only at hp hm
  rw [hp, hm, neutralProbe_NN _ _ _ (by norm_num), if_pos rfl, primaryNeutral_first]
  norm_num [mul_pow, power_two_reduce (cα 1) charge_square_two 32,
    candidateA32, candidateB32]

theorem neutral_mode34 : octaProbe (W.smul X (-3) X) =
    (candidateA34 : ℂ) * (1 / 2) ^ 17 +
      (candidateB34 : ℂ) * (1 / 2) ^ 9 * (1 / 8505000) := by
  change OrbOctaR.neutralProbe ((V2m 1 le_rfl).smul (X : LatModuleGen (latP 1)) (-3) X) = _
  rw [X_lattice_value, neutralProbe_self]
  have hp := neutralProbe_opposite 4 (by norm_num) 34
  have hm := neutralProbe_opposite (-4) (by norm_num) 34
  norm_num only at hp hm
  rw [hp, hm, neutralProbe_NN _ _ _ (by norm_num), if_neg (by norm_num)]
  norm_num [mul_pow, power_two_reduce (cα 1) charge_square_two 34,
    candidateA34, candidateB34]

end VOA.Classification.COne.OrbOctaRC
