import VOA.Classification.COne.OrbC2hDirectSectors
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e

/-- Separate the scalar-variable block without changing the represented sum. -/
def qBuckets : RawPoly ℕ → RawPoly ℕ × RawPoly ℕ
  | [] => ([],[])
  | t::P => let p := qBuckets P
    if t.2.head? = some 0 then (t::p.1,p.2) else (p.1,t::p.2)

theorem evRc_qBuckets {r : ℕ} (a : Fin r) (c : ℂ) (P : RawPoly ℕ) :
    evRc a c (qBuckets P).1 + evRc a c (qBuckets P).2 = evRc a c P := by
  induction P with
  | nil => simp [qBuckets, evRc_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    rw [qBuckets]
    dsimp only
    split_ifs <;> simp only [evRc_cons]
    · rw [← ih]; abel
    · rw [← ih]; abel

def qMappedReduce (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => scaleR t.1 (reduceWordR 8 (sortWord t.2))

theorem evRc_qMappedReduce {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (P : RawPoly ℕ) :
    evRc a c (qMappedReduce P) = evRc a c P := by
  rw [qMappedReduce, evRc_flatMap]
  induction P with
  | nil => simp [evRc_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    rw [List.map_cons, List.sum_cons, evRc_scaleR,
      evRc_reduceWordR _ _ 8 hc, evalWord_sortWord, ih, evRc_cons]

def qBucketReduce (P : RawPoly ℕ) : RawPoly ℕ :=
  let p := qBuckets (qMappedReduce P)
  p.1 ++ p.2

theorem evRc_qBucketReduce {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (P : RawPoly ℕ) :
    evRc a c (qBucketReduce P) = evRc a c P := by
  rw [qBucketReduce, evRc_append, evRc_qBuckets, evRc_qMappedReduce _ _ hc]


open VOA VOA.LatGen VOA.LatGen.Triplet PlusC2 OrbC2c OrbC2f OrbC2g LatMod

def qReduceEach (S : SectorVector) : SectorVector :=
  S.map fun t => (t.1, qBucketReduce t.2)

theorem evaluate_qReduceEach (S : SectorVector) : evaluate (qReduceEach S) = evaluate S := by
  have hc : cα 4 * cα 4 = ((8:ℚ):ℂ) := by
    convert cα_sq 4 four_ge_one using 1 <;> norm_num
  induction S with
  | nil => rfl
  | cons t S ih =>
    rcases t with ⟨d,P⟩
    simp only [qReduceEach, List.map_cons, evaluate, evRc_qBucketReduce _ _ hc] at *
    rw [ih]

def eBucketS (n : ℤ) (S : SectorVector) : SectorVector :=
  qReduceEach (expLongS (-1) n S ++ expLongS 1 n S)

theorem evaluate_eBucketS (n : ℤ) (S : SectorVector) :
    evaluate (eBucketS n S) = (V2m 4 four_ge_one).smul (EP 4 four_ge_one) n (evaluate S) := by
  rw [eBucketS, evaluate_qReduceEach, evaluate_append, evaluate_expLongS, evaluate_expLongS,
    EP_coe, PreVertexAlgebra.smul_add_left]
  abel

theorem eBucket_value (n : ℤ) (S T : SectorVector) (h : eBucketS n S = T) :
    (V2m 4 four_ge_one).smul (EP 4 four_ge_one) n (evaluate S) = evaluate T := by
  rw [← evaluate_eBucketS, h]
end VOA.Classification.COne.OrbC2h
