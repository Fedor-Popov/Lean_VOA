import VOA.Classification.COne.OrbC2hSingle
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e OrbC2g

/-- Substitute the sector charge when a zero mode acts, before normalizing. -/
def fActCharge (d : ℤ) (i : ℕ) (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  if fMode i s = 0 then
    if d = 0 then [] else scaleR (d:ℚ) (fActC i s P)
  else fActC i s P

theorem evRc_fActCharge {r : ℕ} (a : Fin r) (c : ℂ)
    (d : ℤ) (i : ℕ) (s : ℤ) (P : RawPoly ℕ) :
    evRc a c (fActCharge d i s P) = genS a ((d:ℂ)*c) i s (evRc a c P) := by
  have hz (h : fMode i s = 0) (z : ℂ) (q : FockN r) :
      genS a z i s q = (((fCoeff i s:ℚ):ℂ)*z) • q := by
    rw [genS_apply, genFieldN_coeff, LinearMap.smul_apply]
    have hm : -(s+(i:ℤ))-1 = fMode i s := rfl
    rw [hm, h, oscN_zero, LinearMap.zero_apply, smul_zero, if_pos rfl, zero_add]
  rw [fActCharge]
  split_ifs with h hd
  · subst d
    rw [evRc_nil, hz h]
    simp
  · rw [evRc_scaleR, evRc_fActC, hz h, hz h, smul_smul, Rat.cast_intCast]
    congr 1
    ring
  · rw [evRc_fActC, genS_apply, genS_apply, if_neg h, if_neg h]

def singleCharge (d : ℤ) (i : ℕ) (s : ℤ) (w : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  scaleR (((intRange (-((i+1+w : ℕ) : ℤ))
    ((max (-1) ((w:ℤ)+s))+((i+1+w : ℕ) : ℤ)+1).toNat).count s : ℕ):ℚ)
    (fActCharge d i s P)

theorem evRc_singleCharge {r : ℕ} (a : Fin r) (c : ℂ)
    (d : ℤ) (i : ℕ) (s : ℤ) (w : ℕ) (P Q : RawPoly ℕ)
    (h : evRc a c P = evRc a ((d:ℂ)*c) Q) :
    evRc a c (singleCharge d i s w P) =
      evRc a ((d:ℂ)*c) (wordActC [i] s w Q) := by
  rw [← evRc_singleWord, singleCharge, singleWord, evRc_scaleR, evRc_scaleR,
    evRc_fActCharge, evRc_fActC, h]

def wordCharge (d : ℤ) : List ℕ → ℤ → ℕ → RawPoly ℕ → RawPoly ℕ
  | [], s, _, P => if s = 0 then P else []
  | [i], s, w, P => fastNormFuel (singleCharge d i s w P)
  | i :: j :: is, s, w, P => if P = [] then [] else
    fastNormFuel ((intRange (-((i+1+w : ℕ) : ℤ))
      ((max (-1) (((wWt (j::is)+w : ℕ) : ℤ)+s))+((i+1+w : ℕ) : ℤ)+1).toNat).flatMap
      fun m => if 0 ≤ m then fastNormFuel (fActCharge d i m (wordCharge d (j::is) (s-m) w P))
        else wordCharge d (j::is) (s-m) ((((i+1+w : ℕ) : ℤ)+m).toNat)
          (fastNormFuel (fActCharge d i m P)))

theorem evRc_wordCharge {r : ℕ} (a : Fin r) (c : ℂ) (d : ℤ)
    (is : List ℕ) (s : ℤ) (w : ℕ) (P Q : RawPoly ℕ)
    (h : evRc a c P = evRc a ((d:ℂ)*c) Q) :
    evRc a c (wordCharge d is s w P) = evRc a ((d:ℂ)*c) (wordActC is s w Q) := by
  induction is generalizing s w P Q with
  | nil =>
    simp only [wordCharge, wordActC]
    split_ifs
    · exact h
    · rfl
  | cons i is ih =>
    cases is with
    | nil =>
      rw [wordCharge, evRc_fastNormFuel]
      exact evRc_singleCharge a c d i s w P Q h
    | cons j is =>
      rw [wordCharge]
      split_ifs with hp
      · have hz : evRc a ((d:ℂ)*c) Q = 0 := by rw [← h, hp, evRc_nil]
        rw [evRc_nil, evRc_wordActC a _ _ _ _ Q (hz ▸ Submodule.zero_mem _), hz, map_zero]
      · rw [evRc_fastNormFuel, wordActC, evRc_flatMap, evRc_flatMap]
        apply congrArg List.sum
        apply List.map_congr_left
        intro m hm
        split_ifs with hm0
        · rw [evRc_fastNormFuel, evRc_fActCharge, evRc_fActC, ih _ _ P Q h]
        · apply ih
          rw [evRc_fastNormFuel, evRc_fActCharge, evRc_fActC, h]

def polyCharge (d : ℤ) (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  fastNormFuel (P.flatMap fun t => Q.flatMap fun u =>
    scaleR u.1 (wordCharge d u.2 s (wWtC (t.2.map (·+1))) (liftR [t])))

theorem evRc_polyCharge {r : ℕ} (a : Fin r) (c : ℂ)
    (d : ℤ) (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) :
    evRc a c (polyCharge d Q s P) = evRc a ((d:ℂ)*c) (polyActWC Q s (liftR P)) := by
  rw [polyCharge, evRc_fastNormFuel, polyActWC, evRc_flatMap, evRc_flatMap]
  simp only [liftR, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply, polyActC, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  rw [evRc_scaleR, evRc_scaleR]
  apply congrArg ((u.1:ℂ) • ·)
  apply evRc_wordCharge
  change evRc a c (liftR [t]) = evRc a ((d:ℂ)*c) (liftR [t])
  rw [evRc_liftR, evRc_liftR]
end VOA.Classification.COne.OrbC2h
