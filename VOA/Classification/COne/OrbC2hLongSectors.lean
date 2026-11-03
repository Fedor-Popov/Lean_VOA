import VOA.Classification.COne.OrbC2hIExpLong
import VOA.Classification.COne.OrbC2hCertificates
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def expPolyLong (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => scaleR t.1 (expIntegerLong t.2 s)

theorem expPolyLong_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (s : ℤ) (P : RawPoly ℕ) :
    evRc a c (expPolyLong s P) = evRc a c (expPolyR s P) := by
  simp only [expPolyLong, expPolyR, evRc_normR, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, expIntegerLong_sound _ _ hc]

def exponentialLong (b d n : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  onOscillators
    (fun R => chargeScale b (if b*b = 1 then
      expPolyLong (-n-1-8*b*d) (liftR R) else
      expPolyFast (-n-1-8*b*d) (liftR R))) P

theorem exponentialLong_sound (b d n : ℤ) (P : RawPoly ℕ) :
    evRc (a0 4) (cα 4) (exponentialLong b d n P) =
      evRc (a0 4) (cα 4) (exponentialAction b d n P) := by
  rw [exponentialLong, exponentialAction, evRc_reduce_eight]
  simp only [onOscillators, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, evRc_chargePower, evRc_chargePower,
    evRc_chargeScale, evRc_chargeScale]
  apply congrArg ((t.1:ℂ) • ·)
  apply congrArg ((cα 4)^t.2.count 0 • ·)
  split_ifs with hb
  · apply expPolyLong_sound
    have hbC : ((b:ℚ):ℂ) * ((b:ℚ):ℂ) = 1 := by exact_mod_cast hb
    have hc : cα 4 * cα 4 = ((8:ℚ):ℂ) := by
      convert cα_sq 4 four_ge_one using 1 <;> norm_num
    calc
      _ = (((b:ℚ):ℂ) * ((b:ℚ):ℂ)) * (cα 4 * cα 4) := by ring
      _ = _ := by rw [hbC, hc, one_mul]
  · exact expPolyFast_sound _ _ _ _

def expLongS (b n : ℤ) (S : SectorVector) : SectorVector :=
  S.map fun t => (b+t.1, exponentialLong b t.1 n t.2)

theorem evaluate_expLongS (b n : ℤ) (S : SectorVector) :
    evaluate (expLongS b n S) = (V2m 4 four_ge_one).smul (latChargeGen (latP 4) b) n (evaluate S) := by
  rw [expLongS]
  induction S with
  | nil => simp [evaluate, PreVertexAlgebra.smul_zero_right]
  | cons t S ih =>
    rcases t with ⟨d,P⟩
    simp only [List.map_cons, evaluate, exponentialLong_sound, ← exponentialAction_sound,
      PreVertexAlgebra.smul_add_right]
    rw [ih]

def eLongS (n : ℤ) (S : SectorVector) : SectorVector :=
  expLongS 1 n S ++ expLongS (-1) n S

theorem evaluate_eLongS (n : ℤ) (S : SectorVector) :
    evaluate (eLongS n S) = (V2m 4 four_ge_one).smul (EP 4 four_ge_one) n (evaluate S) := by
  rw [eLongS, evaluate_append, evaluate_expLongS, evaluate_expLongS,
    EP_coe, PreVertexAlgebra.smul_add_left]


theorem eLong_value (n : ℤ) (S T : SectorVector)
    (h : VectorCertificate (eLongS n S) T) :
    (V2m 4 four_ge_one).smul (EP 4 four_ge_one) n (evaluate S) = evaluate T := by
  rw [← evaluate_eLongS]
  exact vector_eq_of_certificate _ _ h
end VOA.Classification.COne.OrbC2h
