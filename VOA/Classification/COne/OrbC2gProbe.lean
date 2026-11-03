import VOA.Classification.COne.OrbC2gSectors

/-! # A certified neutral-sector first-oscillator probe

The probe sends h(-1) to one and every other oscillator to zero, after
extracting charge zero. On a homogeneous weight N vector it therefore reads
the coefficient of h(-1)^N. No homogeneity is needed for its soundness.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2g
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f LatMod

noncomputable def firstOscillator : FockN (rank (latP 4)) →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval fun i => if i.1 = 0 then 1 else 0

noncomputable def neutralProbe : LatModuleGen (latP 4) →ₗ[ℂ] ℂ :=
  firstOscillator.toLinearMap.comp (coordEα (latP 4) 0)

def leadWord : List ℕ → RawPoly ℕ
  | [] => [(1, [])]
  | 0 :: w => prependC 0 (leadWord w)
  | 1 :: w => leadWord w
  | (_+2) :: _ => []

def leadPoly (P : RawPoly ℕ) : RawPoly ℕ :=
  normR (P.flatMap fun t => scaleR t.1 (leadWord t.2))

theorem firstOscillator_leadWord (w : List ℕ) :
    firstOscillator (evRc (a0 4) (cα 4) (leadWord w)) =
      firstOscillator (evalWord (xvc (a0 4) (cα 4)) w) := by
  induction w with
  | nil => simp [leadWord, evRc_cons, evRc_nil, evalWordC_nil]
  | cons i w ih =>
    cases i with
    | zero =>
      rw [leadWord, evRc_prependC, evalWordC_cons, map_mul, map_mul, ih]
    | succ i =>
      cases i with
      | zero => simpa [leadWord, evalWordC_cons, xvc, firstOscillator] using ih
      | succ i => simp [leadWord, evRc_nil, evalWordC_cons, xvc, firstOscillator]

theorem firstOscillator_leadPoly (P : RawPoly ℕ) :
    firstOscillator (evRc (a0 4) (cα 4) (leadPoly P)) =
      firstOscillator (evRc (a0 4) (cα 4) P) := by
  rw [leadPoly, evRc_normR, evRc_flatMap, map_list_sum]
  induction P with
  | nil => simp [evRc_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    simp only [List.map_cons, List.sum_cons, map_add, evRc_cons, map_smul,
      evRc_scaleR, firstOscillator_leadWord]
    simp only [evRc_scaleR] at ih
    rw [ih]

/-- The charge-zero coordinate as a raw polynomial. -/
def zeroSector (S : SectorVector) : RawPoly ℕ :=
  reduceR 8 (S.flatMap fun t => if t.1 = 0 then t.2 else [])

theorem coord_evaluate (S : SectorVector) :
    coordEα (latP 4) 0 (evaluate S) = evRc (a0 4) (cα 4) (zeroSector S) := by
  classical
  rw [zeroSector, evRc_reduce_eight]
  induction S with
  | nil => simp [evaluate, evRc_nil]
  | cons s S ih =>
    rcases s with ⟨d,P⟩
    rw [evaluate, map_add, List.flatMap_cons, evRc_append, ih]
    congr 1
    change coordEα (latP 4) 0 (latStateGen (latP 4) _ d) = _
    rw [latStateGen, coordEα_apply]
    by_cases hd : d = 0
    · subst d
      split_ifs with h₁ h₂
      · rfl
      · exact (h₂ rfl).elim
      · exact (h₁ rfl).elim
      · exact (h₁ rfl).elim
    · rw [if_neg (by change ¬(0 : ℤ) = d; omega), if_neg hd, evRc_nil]

/-- A checkable rational constant certificate implies an actual VOA probe identity. -/
theorem neutralProbe_of_certificate (S : SectorVector) (q : ℚ)
    (h : leadPoly (zeroSector S) = [(q, [])]) : neutralProbe (evaluate S) = (q : ℂ) := by
  change firstOscillator (coordEα (latP 4) 0 (evaluate S)) = _
  rw [coord_evaluate, ← firstOscillator_leadPoly, h]
  simp [evRc_cons, evRc_nil, evalWordC_nil]

end VOA.Classification.COne.OrbC2g
