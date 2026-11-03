import VOA.Classification.COne.OrbC2hInteger
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e

/-- Separate the scalar-variable block without changing the represented sum. -/
def iBuckets : IntPoly → IntPoly × IntPoly
  | [] => ([],[])
  | t::P => let p := iBuckets P
    if t.2.head? = some 0 then (t::p.1,p.2) else (p.1,t::p.2)

theorem iEval_buckets {r : ℕ} (a : Fin r) (c : ℂ) (P : IntPoly) :
    iEval a c (iBuckets P).1 + iEval a c (iBuckets P).2 = iEval a c P := by
  induction P with
  | nil => simp [iBuckets, iEval_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    rw [iBuckets]
    dsimp only
    split_ifs <;> simp only [iEval_cons]
    · rw [← ih]; abel
    · rw [← ih]; abel

def iMappedReduce (P : IntPoly) : IntPoly :=
  P.flatMap fun t => iScale t.1 (iReduceWord (sortWord t.2))

theorem iEval_mappedReduce {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (P : IntPoly) :
    iEval a c (iMappedReduce P) = iEval a c P := by
  rw [iMappedReduce, iEval_flatMap]
  induction P with
  | nil => simp [iEval_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    rw [List.map_cons, List.sum_cons, iEval_scale,
      iEval_reduceWord _ _ hc, evalWord_sortWord, ih, iEval_cons]

def iBucketReduce (P : IntPoly) : IntPoly :=
  let p := iBuckets (iMappedReduce P)
  p.1 ++ p.2

theorem iEval_bucketReduce {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (P : IntPoly) :
    iEval a c (iBucketReduce P) = iEval a c P := by
  rw [iBucketReduce, iEval_append, iEval_buckets, iEval_mappedReduce _ _ hc]

/-- Merging remains sound even when an input happens not to be sorted. -/
def iAddReduced (P Q : IntPoly) : IntPoly :=
  iMerge 100000 (iBucketReduce P) (iBucketReduce Q)

theorem iEval_addReduced {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (P Q : IntPoly) :
    iEval a c (iAddReduced P Q) = iEval a c P + iEval a c Q := by
  rw [iAddReduced, iEval_merge, iEval_bucketReduce _ _ hc, iEval_bucketReduce _ _ hc]

end VOA.Classification.COne.OrbC2h
