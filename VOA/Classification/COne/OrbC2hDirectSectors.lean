import VOA.Classification.COne.OrbC2hLongSectors
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def reduceEach (S : SectorVector) : SectorVector :=
  S.map fun t => (t.1, fastReduce t.2)

theorem evaluate_reduceEach (S : SectorVector) : evaluate (reduceEach S) = evaluate S := by
  induction S with
  | nil => rfl
  | cons t S ih =>
    rcases t with ⟨d,P⟩
    simp only [reduceEach, List.map_cons, evaluate, evRc_fastReduce] at *
    rw [ih]

/-- Charge-ordered output for a single input sector, with each polynomial reduced once. -/
def eDirectS (n : ℤ) (S : SectorVector) : SectorVector :=
  reduceEach (expLongS (-1) n S ++ expLongS 1 n S)

theorem evaluate_eDirectS (n : ℤ) (S : SectorVector) :
    evaluate (eDirectS n S) = (V2m 4 four_ge_one).smul (EP 4 four_ge_one) n (evaluate S) := by
  rw [eDirectS, evaluate_reduceEach, evaluate_append, evaluate_expLongS, evaluate_expLongS,
    EP_coe, PreVertexAlgebra.smul_add_left]
  abel

theorem eDirect_value (n : ℤ) (S T : SectorVector) (h : eDirectS n S = T) :
    (V2m 4 four_ge_one).smul (EP 4 four_ge_one) n (evaluate S) = evaluate T := by
  rw [← evaluate_eDirectS, h]
end VOA.Classification.COne.OrbC2h
