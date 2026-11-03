import VOA.Classification.COne.OrbC2hChargedSingle
import VOA.Classification.COne.OrbC2hCertificates
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def neutralChargeRaw (Q : RawPoly ℕ) (n d : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  onOscillators (polyCharge d Q (-n-1)) P

theorem neutralChargeRaw_sound (Q P : RawPoly ℕ) (n d : ℤ) :
    evRc (a0 4) (cα 4) (neutralChargeRaw Q n d P) =
      evRc (a0 4) (cα 4) (neutralAction Q n d P) := by
  rw [neutralChargeRaw, neutralAction, evRc_reduce_eight]
  simp only [onOscillators, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, evRc_chargePower, evRc_chargePower,
    evRc_polyCharge, evRc_chargeScale, Rat.cast_intCast]

def neutralChargeS (Q : RawPoly ℕ) (n : ℤ) (S : SectorVector) : SectorVector :=
  S.map fun t => (t.1, neutralChargeRaw Q n t.1 t.2)

theorem evaluate_neutralChargeS (Q : RawPoly ℕ) (n : ℤ) (S : SectorVector) :
    evaluate (neutralChargeS Q n S) = (V2m 4 four_ge_one).smul (ls 4 Q) n (evaluate S) := by
  rw [neutralChargeS]
  induction S with
  | nil => simp [evaluate, PreVertexAlgebra.smul_zero_right]
  | cons t S ih =>
    rcases t with ⟨d,P⟩
    simp only [List.map_cons, evaluate, neutralChargeRaw_sound, ← neutralAction_sound,
      PreVertexAlgebra.smul_add_right]
    rw [ih]

theorem neutralCharge_value (Q : RawPoly ℕ) (n : ℤ) (S T : SectorVector)
    (h : VectorCertificate (neutralChargeS Q n S) T) :
    (V2m 4 four_ge_one).smul (ls 4 Q) n (evaluate S) = evaluate T := by
  rw [← evaluate_neutralChargeS]
  exact vector_eq_of_certificate _ _ h
end VOA.Classification.COne.OrbC2h
