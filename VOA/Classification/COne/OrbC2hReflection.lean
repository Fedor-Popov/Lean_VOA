import VOA.Classification.COne.OrbC2hCertificates
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2e OrbC2g LatMod HeisenbergN VOA.IntegralLattice

def reflectPoly (P : RawPoly ℕ) : RawPoly ℕ :=
  P.map fun t => (t.1 * (-1) ^ (oscillators t.2).length, t.2)

def reflectVector (S : SectorVector) : SectorVector :=
  S.map fun t => (-t.1, reflectPoly t.2)

theorem evRc_reflectPoly (P : RawPoly ℕ) :
    evRc (a0 4) (cα 4) (reflectPoly P) =
      sigmaN (rank (latP 4)) (evRc (a0 4) (cα 4) P) := by
  induction P with
  | nil => simp [reflectPoly, evRc_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    simp only [reflectPoly, List.map_cons, evRc_cons, map_add, map_smul]
    change _ + evRc (a0 4) (cα 4) (reflectPoly P) = _
    rw [ih, evalWord_split, map_smul, sigma_evalWord]
    push_cast
    simp only [smul_smul]
    congr 2
    ring

theorem evaluate_reflectVector (S : SectorVector) :
    evaluate (reflectVector S) = thetaLat (latP 4) (evaluate S) := by
  induction S with
  | nil => simp [reflectVector, evaluate]
  | cons t S ih =>
    rcases t with ⟨d,P⟩
    simp only [reflectVector, List.map_cons, evaluate, map_add]
    change _ + evaluate (reflectVector S) = _
    rw [ih, evRc_reflectPoly]
    congr 1
    exact (thetaLat_latStateGen _ _ _).symm

theorem evaluate_reverse (S : SectorVector) : evaluate S.reverse = evaluate S := by
  induction S with
  | nil => rfl
  | cons t S ih =>
    rw [List.reverse_cons, evaluate_append, ih]
    rcases t with ⟨d,P⟩
    simp only [evaluate, add_zero]
    exact add_comm _ _

theorem mode_of_reflection (U : VP 4 four_ge_one) (n : ℤ)
    (S T S' T' : SectorVector)
    (h : (V2m 4 four_ge_one).smul (U : LatModuleGen (latP 4)) n
      (evaluate S) = evaluate T)
    (hin : reflectVector S = S')
    (hout : (reflectVector T).reverse = T') :
    (V2m 4 four_ge_one).smul (U : LatModuleGen (latP 4)) n
      (evaluate S') = evaluate T' := by
  rw [← hin, evaluate_reflectVector]
  have hu : thetaLat (latP 4) (U : LatModuleGen (latP 4)) = U :=
    (mem_VP_iff _ _ _).mp U.property
  rw [← hu, ← theta_smul, h]
  rw [← evaluate_reflectVector, ← evaluate_reverse (reflectVector T), hout]
end VOA.Classification.COne.OrbC2h
