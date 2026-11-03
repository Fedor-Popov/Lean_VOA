import VOA.Classification.COne.OrbOctaRCVir
import VOA.Examples.LatticeGenVirasoroEminus

/-! Negative Virasoro evaluation by commuting through oscillator words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice VOA.SparseRational
  HeisenbergN MvPolynomial PlusC2Eval PlusUnitary PlusC2 OrbC2e OrbC2g OrbC2h LatMod

noncomputable def fockL (d n : ℤ) : FockN (rank (latP 1)) →ₗ[ℂ] FockN (rank (latP 1)) :=
  LvirN (rank (latP 1)) 1 n + chargeOsc (latP 1) d n

theorem L_sector (n d : ℤ) (hn : n ≠ 0) (p : FockN (rank (latP 1))) :
    (V2m 1 le_rfl).L n (sector d p) = sector d (fockL d n p) := by
  rw [show (V2m 1 le_rfl).L n = LLGen (latP 1) n from
    OrbSpan.latticeVOAGen_L _ _ _ _]
  change LLGen (latP 1) n (latStateGen (latP 1) p d) = _
  rw [LLGen_tmul _ (latP_posDef 1 le_rfl), if_neg hn, add_zero]
  exact (map_add (sector d) _ _).symm

theorem sector_injective (d : ℤ) : Function.Injective (sector d) := by
  intro p q h
  have hh := congrArg (coordEα (latP 1) d) h
  simpa [sector, latStateGen, coordEα_apply] using hh

theorem fockL_neg_X (k : ℕ) (hk : 0 < k) (d : ℤ) (i : ℕ)
    (p : FockN (rank (latP 1))) :
    fockL d (-(k : ℤ)) (X (i, a0 1) * p) =
      X (i, a0 1) * fockL d (-(k : ℤ)) p +
        ((i + 1 : ℕ) : ℂ) • (X (i + k, a0 1) * p) := by
  have hh := LvirN_oscN (rank (latP 1)) 1 (by norm_num) (a0 1)
    (-(k : ℤ)) (-((i : ℤ) + 1)) p
  rw [oscN_apply_neg _ _ _ (by omega), oscN_apply_neg _ _ _ (by omega),
    oscN_apply_neg _ _ _ (by omega)] at hh
  have h1 : (-(-((i : ℤ) + 1)) - 1).toNat = i := by omega
  have h2 : (-(-(k : ℤ) + -((i : ℤ) + 1)) - 1).toNat = i + k := by omega
  rw [h1, h2] at hh
  have hq : chargeOsc (latP 1) d (-(k : ℤ)) (X (i, a0 1) * p) =
      X (i, a0 1) * chargeOsc (latP 1) d (-(k : ℤ)) p := by
    rw [show -(k : ℤ) = -(((k - 1 : ℕ) : ℤ) + 1) by omega,
      chargeOsc_neg_eq_mulLeft_vVar]
    simp only [LinearMap.mulLeft_apply]
    ring
  simp only [fockL, LinearMap.add_apply]
  rw [hh, hq, mul_add]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Nat.cast_add, Nat.cast_one, neg_neg]
  abel

def virOnWord (k : ℕ) (G : RawPoly ℕ) : List ℕ → RawPoly ℕ
  | [] => G
  | 0 :: w => prependC 0 (virOnWord k G w)
  | (i + 1) :: w => fastNormFuel (prependC (i + 1) (virOnWord k G w) ++
      scaleR (i + 1) (prependC (i + k + 1) [(1, w)]))

theorem virOnWord_sound (k : ℕ) (hk : 0 < k) (d : ℤ) (G : RawPoly ℕ)
    (hG : fockL d (-(k : ℤ)) 1 = evRc (a0 1) (cα 1) G) (w : List ℕ) :
    fockL d (-(k : ℤ)) (evalWord (xvc (a0 1) (cα 1)) w) =
      evRc (a0 1) (cα 1) (virOnWord k G w) := by
  induction w with
  | nil => simpa only [evalWordC_nil, virOnWord] using hG
  | cons i w ih =>
    cases i with
    | zero =>
      rw [evalWordC_cons, virOnWord, evRc_prependC]
      simp only [xvc, ← MvPolynomial.smul_eq_C_mul]
      rw [map_smul, ih]
    | succ i =>
      rw [evalWordC_cons, virOnWord, evRc_fastNormFuel, evRc_append, evRc_scaleR,
        evRc_prependC, evRc_prependC, evRc_cons, evRc_nil, add_zero,
        Rat.cast_one, one_smul]
      change fockL d (-(k : ℤ)) (X (i, a0 1) * _) = _
      rw [fockL_neg_X k hk, ih]
      simp only [xvc, Rat.cast_add, Rat.cast_natCast, Rat.cast_one,
        Nat.cast_add, Nat.cast_one]

def virOnPoly (k : ℕ) (G P : RawPoly ℕ) : RawPoly ℕ :=
  reduceTwo (P.flatMap fun t => scaleR t.1 (virOnWord k G t.2))

theorem virOnPoly_sound (k : ℕ) (hk : 0 < k) (d : ℤ) (G : RawPoly ℕ)
    (hG : fockL d (-(k : ℤ)) 1 = evRc (a0 1) (cα 1) G) (P : RawPoly ℕ) :
    fockL d (-(k : ℤ)) (evRc (a0 1) (cα 1) P) =
      evRc (a0 1) (cα 1) (virOnPoly k G P) := by
  rw [virOnPoly, evRc_reduceTwo_of_sq _ _ charge_square_two]
  induction P with
  | nil => simp [evRc_nil]
  | cons t P ih =>
    rcases t with ⟨q, w⟩
    rw [evRc_cons, map_add, map_smul, virOnWord_sound k hk d G hG, ih,
      List.flatMap_cons, evRc_append, evRc_scaleR]

theorem virDirect_sound (k : ℕ) (hk : 0 < k) (d : ℤ) (G : RawPoly ℕ)
    (hG : neutralQuickOne PlusC2.omR (1 - (k : ℤ)) d [(1, [])] = G)
    (P : RawPoly ℕ) :
    (V2m 1 le_rfl).L (-(k : ℤ)) (sector d (evRc (a0 1) (cα 1) P)) =
      sector d (evRc (a0 1) (cα 1) (virOnPoly k G P)) := by
  have hg := virOne_sound (-(k : ℤ)) d [(1, [])]
  rw [show -(k : ℤ) + 1 = 1 - (k : ℤ) by ring, hG] at hg
  simp only [evRc_cons, evRc_nil, evalWordC_nil, Rat.cast_one, one_smul, add_zero] at hg
  rw [L_sector _ _ (by omega)] at hg
  have hh := sector_injective d hg
  rw [L_sector _ _ (by omega), virOnPoly_sound k hk d G hh]

end VOA.Classification.COne.OrbOctaRC
