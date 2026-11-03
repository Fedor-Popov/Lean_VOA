import VOA.Classification.COne.OrbC2gDiagnostic

/-! Normalizing intermediate oscillator polynomials, with the original semantics. -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e OrbC2g

def wordFast : List ℕ → ℤ → ℕ → RawPoly ℕ → RawPoly ℕ
  | [], s, _, P => if s = 0 then P else []
  | i :: is, s, w, P => if P = [] then [] else
    normR ((intRange (-((i+1+w : ℕ) : ℤ))
      ((max (-1) (((wWt is+w : ℕ) : ℤ)+s))+((i+1+w : ℕ) : ℤ)+1).toNat).flatMap
      fun m => if 0 ≤ m then normR (fActC i m (wordFast is (s-m) w P))
        else wordFast is (s-m) ((((i+1+w : ℕ) : ℤ)+m).toNat) (normR (fActC i m P)))

theorem evRc_wordFast {r : ℕ} (a : Fin r) (c : ℂ)
    (is : List ℕ) (s : ℤ) (w : ℕ) (P Q : RawPoly ℕ)
    (h : evRc a c P = evRc a c Q) :
    evRc a c (wordFast is s w P) = evRc a c (wordActC is s w Q) := by
  induction is generalizing s w P Q with
  | nil =>
    simp only [wordFast, wordActC]
    split_ifs
    · exact h
    · rfl
  | cons i is ih =>
    rw [wordFast]
    split_ifs with hp
    · have hz : evRc a c Q = 0 := by rw [← h, hp, evRc_nil]
      rw [evRc_nil, evRc_wordActC a c _ _ _ Q (hz ▸ Submodule.zero_mem _), hz, map_zero]
    · rw [evRc_normR, wordActC, evRc_flatMap, evRc_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro m hm
      split_ifs with hm0
      · rw [evRc_normR, evRc_fActC, evRc_fActC, ih _ _ P Q h]
      · apply ih
        rw [evRc_normR, evRc_fActC, evRc_fActC, h]

def polyFast (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  normR (P.flatMap fun t => Q.flatMap fun u =>
    scaleR u.1 (wordFast u.2 s (wWtC t.2) [t]))

theorem evRc_polyFast {r : ℕ} (a : Fin r) (c : ℂ)
    (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) :
    evRc a c (polyFast Q s P) = evRc a c (polyActWC Q s P) := by
  rw [polyFast, evRc_normR, polyActWC, evRc_flatMap, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [polyActC, evRc_flatMap, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  rw [evRc_scaleR, evRc_scaleR, evRc_wordFast a c _ _ _ _ _ rfl]

def neutralFast (Q : RawPoly ℕ) (n d : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  reduceR 8 (onOscillators
    (fun R => chargeScale d (polyFast Q (-n-1) (liftR R))) P)

theorem neutralFast_sound (Q P : RawPoly ℕ) (n d : ℤ) :
    evRc (LatMod.a0 4) (PlusC2.cα 4) (neutralFast Q n d P) =
      evRc (LatMod.a0 4) (PlusC2.cα 4) (neutralAction Q n d P) := by
  rw [neutralFast, neutralAction, evRc_reduce_eight, evRc_reduce_eight]
  simp only [onOscillators, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, evRc_chargePower, evRc_chargePower,
    evRc_chargeScale, evRc_chargeScale, evRc_polyFast]

end VOA.Classification.COne.OrbC2h
