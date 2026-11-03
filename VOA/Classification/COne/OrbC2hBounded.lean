import VOA.Classification.COne.OrbC2hRange
import VOA.Classification.COne.OrbC2hChargedSectors
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def singleBound (d : ℤ) (i : ℕ) (s : ℤ) (w : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  if -((i+1+w:ℕ):ℤ) ≤ s then fActCharge d i s P else []

theorem evRc_singleBound {r : ℕ} (a : Fin r) (c : ℂ)
    (d : ℤ) (i : ℕ) (s : ℤ) (w : ℕ) (P Q : RawPoly ℕ)
    (h : evRc a c P = evRc a ((d:ℂ)*c) Q) :
    evRc a c (singleBound d i s w P) =
      evRc a ((d:ℂ)*c) (wordActC [i] s w Q) := by
  rw [← evRc_singleWord, singleWord, evRc_scaleR, single_range_count, singleBound]
  split_ifs
  · simp only [Nat.cast_one, Rat.cast_one, one_smul]
    rw [evRc_fActCharge, evRc_fActC, h]
  · simp [evRc_nil]

def wordBound (d : ℤ) : List ℕ → ℤ → ℕ → RawPoly ℕ → RawPoly ℕ
  | [], s, _, P => if s = 0 then P else []
  | [i], s, w, P => fastNormFuel (singleBound d i s w P)
  | i :: j :: is, s, w, P => if P = [] then [] else
    fastNormFuel ((intRange (-((i+1+w : ℕ) : ℤ))
      ((max (-1) (((wWt (j::is)+w : ℕ) : ℤ)+s))+((i+1+w : ℕ) : ℤ)+1).toNat).flatMap
      fun m => if 0 ≤ m then fastNormFuel (fActCharge d i m (wordBound d (j::is) (s-m) w P))
        else wordBound d (j::is) (s-m) ((((i+1+w : ℕ) : ℤ)+m).toNat)
          (fastNormFuel (fActCharge d i m P)))

theorem evRc_wordBound {r : ℕ} (a : Fin r) (c : ℂ) (d : ℤ)
    (is : List ℕ) (s : ℤ) (w : ℕ) (P Q : RawPoly ℕ)
    (h : evRc a c P = evRc a ((d:ℂ)*c) Q) :
    evRc a c (wordBound d is s w P) = evRc a ((d:ℂ)*c) (wordActC is s w Q) := by
  induction is generalizing s w P Q with
  | nil =>
    simp only [wordBound, wordActC]
    split_ifs
    · exact h
    · rfl
  | cons i is ih =>
    cases is with
    | nil =>
      rw [wordBound, evRc_fastNormFuel]
      exact evRc_singleBound a c d i s w P Q h
    | cons j is =>
      rw [wordBound]
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

def polyBound (d : ℤ) (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  fastNormFuel (P.flatMap fun t => Q.flatMap fun u =>
    scaleR u.1 (wordBound d u.2 s (wWtC (t.2.map (·+1))) (liftR [t])))

theorem evRc_polyBound {r : ℕ} (a : Fin r) (c : ℂ)
    (d : ℤ) (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) :
    evRc a c (polyBound d Q s P) = evRc a ((d:ℂ)*c) (polyActWC Q s (liftR P)) := by
  rw [polyBound, evRc_fastNormFuel, polyActWC, evRc_flatMap, evRc_flatMap]
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
  apply evRc_wordBound
  change evRc a c (liftR [t]) = evRc a ((d:ℂ)*c) (liftR [t])
  rw [evRc_liftR, evRc_liftR]
def neutralBoundRaw (Q : RawPoly ℕ) (n d : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  onOscillators (polyBound d Q (-n-1)) P

theorem neutralBoundRaw_sound (Q P : RawPoly ℕ) (n d : ℤ) :
    evRc (a0 4) (cα 4) (neutralBoundRaw Q n d P) =
      evRc (a0 4) (cα 4) (neutralAction Q n d P) := by
  rw [neutralBoundRaw, neutralAction, evRc_reduce_eight]
  simp only [onOscillators, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, evRc_chargePower, evRc_chargePower,
    evRc_polyBound, evRc_chargeScale, Rat.cast_intCast]

def neutralBoundS (Q : RawPoly ℕ) (n : ℤ) (S : SectorVector) : SectorVector :=
  S.map fun t => (t.1, neutralBoundRaw Q n t.1 t.2)

theorem evaluate_neutralBoundS (Q : RawPoly ℕ) (n : ℤ) (S : SectorVector) :
    evaluate (neutralBoundS Q n S) = (V2m 4 four_ge_one).smul (ls 4 Q) n (evaluate S) := by
  rw [neutralBoundS]
  induction S with
  | nil => simp [evaluate, PreVertexAlgebra.smul_zero_right]
  | cons t S ih =>
    rcases t with ⟨d,P⟩
    simp only [List.map_cons, evaluate, neutralBoundRaw_sound, ← neutralAction_sound,
      PreVertexAlgebra.smul_add_right]
    rw [ih]

theorem neutralBound_value (Q : RawPoly ℕ) (n : ℤ) (S T : SectorVector)
    (h : VectorCertificate (neutralBoundS Q n S) T) :
    (V2m 4 four_ge_one).smul (ls 4 Q) n (evaluate S) = evaluate T := by
  rw [← evaluate_neutralBoundS]
  exact vector_eq_of_certificate _ _ h
end VOA.Classification.COne.OrbC2h
