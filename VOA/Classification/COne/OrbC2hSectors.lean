import VOA.Classification.COne.OrbC2hIExp
import VOA.Classification.COne.OrbC2hSingle
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def expPolyReduced (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => scaleR t.1 (expInteger t.2 s)

theorem expPolyReduced_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (s : ℤ) (P : RawPoly ℕ) :
    evRc a c (expPolyReduced s P) = evRc a c (expPolyR s P) := by
  simp only [expPolyReduced, expPolyR, evRc_normR, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, expInteger_sound _ _ hc]

def exponentialFast (b d n : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  onOscillators
    (fun R => chargeScale b (if b*b = 1 then
      expPolyReduced (-n-1-8*b*d) (liftR R) else
      expPolyFast (-n-1-8*b*d) (liftR R))) P

theorem exponentialFast_sound (b d n : ℤ) (P : RawPoly ℕ) :
    evRc (a0 4) (cα 4) (exponentialFast b d n P) =
      evRc (a0 4) (cα 4) (exponentialAction b d n P) := by
  rw [exponentialFast, exponentialAction, evRc_reduce_eight]
  simp only [onOscillators, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, evRc_chargePower, evRc_chargePower,
    evRc_chargeScale, evRc_chargeScale]
  apply congrArg ((t.1:ℂ) • ·)
  apply congrArg ((cα 4)^t.2.count 0 • ·)
  split_ifs with hb
  · apply expPolyReduced_sound
    have hbC : ((b:ℚ):ℂ) * ((b:ℚ):ℂ) = 1 := by exact_mod_cast hb
    have hc : cα 4 * cα 4 = ((8:ℚ):ℂ) := by
      convert cα_sq 4 four_ge_one using 1 <;> norm_num
    calc
      _ = (((b:ℚ):ℂ) * ((b:ℚ):ℂ)) * (cα 4 * cα 4) := by ring
      _ = _ := by rw [hbC, hc, one_mul]
  · exact expPolyFast_sound _ _ _ _

def insertSector (d : ℤ) (P : RawPoly ℕ) : SectorVector → SectorVector
  | [] => [(d, fastReduce P)]
  | (e,Q) :: S => if d = e then (d, fastReduce (P ++ Q)) :: S
      else (e,Q) :: insertSector d P S

theorem evaluate_insertSector (d : ℤ) (P : RawPoly ℕ) (S : SectorVector) :
    evaluate (insertSector d P S) = sector d (evRc (a0 4) (cα 4) P) + evaluate S := by
  induction S with
  | nil => simp [insertSector, evaluate, evRc_fastReduce]
  | cons t S ih =>
    rcases t with ⟨e,Q⟩
    rw [insertSector]
    split_ifs with h
    · subst e
      simp only [evaluate, evRc_fastReduce, evRc_append, map_add]
      abel
    · rw [evaluate, ih, evaluate]
      abel

def compact : SectorVector → SectorVector
  | [] => []
  | (d,P) :: S => insertSector d P (compact S)

theorem evaluate_compact (S : SectorVector) : evaluate (compact S) = evaluate S := by
  induction S with
  | nil => rfl
  | cons t S ih => rcases t with ⟨d,P⟩; rw [compact, evaluate_insertSector, ih, evaluate]

def neutralRaw (Q : RawPoly ℕ) (n d : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  onOscillators (fun R => chargeScale d (polySingle Q (-n-1) (liftR R))) P

theorem neutralRaw_sound (Q P : RawPoly ℕ) (n d : ℤ) :
    evRc (a0 4) (cα 4) (neutralRaw Q n d P) =
      evRc (a0 4) (cα 4) (neutralAction Q n d P) := by
  rw [neutralRaw, neutralAction, evRc_reduce_eight]
  simp only [onOscillators, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [evRc_scaleR, evRc_scaleR, evRc_chargePower, evRc_chargePower,
    evRc_chargeScale, evRc_chargeScale, evRc_polySingle]

def neutralS (Q : RawPoly ℕ) (n : ℤ) (S : SectorVector) : SectorVector :=
  S.map fun t => (t.1, neutralRaw Q n t.1 t.2)

theorem evaluate_neutralS (Q : RawPoly ℕ) (n : ℤ) (S : SectorVector) :
    evaluate (neutralS Q n S) = (V2m 4 four_ge_one).smul (ls 4 Q) n (evaluate S) := by
  rw [neutralS]
  induction S with
  | nil => simp [evaluate, PreVertexAlgebra.smul_zero_right]
  | cons t S ih =>
    rcases t with ⟨d,P⟩
    simp only [List.map_cons, evaluate, neutralRaw_sound, ← neutralAction_sound,
      PreVertexAlgebra.smul_add_right]
    rw [ih]

def expS (b n : ℤ) (S : SectorVector) : SectorVector :=
  S.map fun t => (b+t.1, exponentialFast b t.1 n t.2)

theorem evaluate_expS (b n : ℤ) (S : SectorVector) :
    evaluate (expS b n S) = (V2m 4 four_ge_one).smul (latChargeGen (latP 4) b) n (evaluate S) := by
  rw [expS]
  induction S with
  | nil => simp [evaluate, PreVertexAlgebra.smul_zero_right]
  | cons t S ih =>
    rcases t with ⟨d,P⟩
    simp only [List.map_cons, evaluate, exponentialFast_sound, ← exponentialAction_sound,
      PreVertexAlgebra.smul_add_right]
    rw [ih]

def eS (n : ℤ) (S : SectorVector) : SectorVector :=
  expS 1 n S ++ expS (-1) n S

theorem evaluate_eS (n : ℤ) (S : SectorVector) :
    evaluate (eS n S) = (V2m 4 four_ge_one).smul (EP 4 four_ge_one) n (evaluate S) := by
  rw [eS, evaluate_append, evaluate_expS, evaluate_expS,
    EP_coe, PreVertexAlgebra.smul_add_left]

def nineS : SectorVector := compact
  (neutralS JR (-2) eGroundVector ++ scaleVector (-1) (eS (-2) jVector))

theorem evaluate_nineS : evaluate nineS = (weightNine : LatModuleGen (latP 4)) := by
  rw [nineS, evaluate_compact, evaluate_append, evaluate_neutralS,
    evaluate_scaleVector, evaluate_eS]
  rw [← evaluate_neutralVector, ← evaluate_eVector, ← evaluate_scaleVector,
    ← evaluate_append]
  exact evaluate_nineVector

def iterateS (n : ℤ) (i : ℕ) (S : SectorVector) : SectorVector :=
  compact (scaleVector (i+1)
    (neutralS JR (-2-i) (eS (n+i) S) ++
      scaleVector (-1) (eS (-2+n-i) (neutralS JR i S)) ++
      scaleVector (-1) (eS (-2-i) (neutralS JR (n+i) S)) ++
      neutralS JR (-2+n-i) (eS i S)))

theorem evaluate_iterateS (n : ℤ) (i : ℕ) (S : SectorVector)
    (h : evaluate S = evaluate nineVector) :
    evaluate (iterateS n i S) = evaluate (iterateVector n i nineVector) := by
  simp only [iterateS, evaluate_compact, iterateVector, evaluate_scaleVector,
    evaluate_append, evaluate_neutralS, evaluate_eS, evaluate_neutralVector,
    evaluate_eVector, h]

end VOA.Classification.COne.OrbC2h
