import VOA.DeligneAudit.D4FusionContactPolynomialGr

/-! Actual degree-preserving operators on the restricted PBW cyclic grading.
The preservation hypothesis in this generic helper is instantiated by the
proved current source invariance in the G0 and Contact companion modules. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl

noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V) (w : V)

/-- A vector in filtration length at most n has an actual cyclic symbol in degree n. -/
theorem symbol_mem_gradedCyclic {n : ℕ} {v : V} (hv : v ∈ currentPiece R w n) :
    symbol R w n v ∈ gradedCyclic R w := by
  rw [← Ple_eq_currentPiece] at hv
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      by_cases he : l.length = n
      · rw [← he]
        exact Submodule.subset_span ⟨l, rfl⟩
      · rw [symbol_zero_of_mem R w (Submodule.subset_span ⟨l, by omega, rfl⟩)]
        exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

variable (X : Module.End ℂ V)
variable (hX : ∀ n, currentPiece R w n ≤ (currentPiece R w n).comap X)

include hX in
theorem preserving_Pbelow (n : ℕ) : Pbelow R w n ≤ (Pbelow R w n).comap X := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  have hv := hX l.length (currentRadicalWord_mem R w l le_rfl)
  rw [← Ple_eq_currentPiece] at hv
  exact Pbelow_mono R w (by omega) hv

/-- The actual action keeps the PBW tag fixed. -/
def degreeZeroLift : (ℕ →₀ V) →ₗ[ℂ] (ℕ →₀ V) := Finsupp.mapRange.linearMap X

theorem degreeZeroLift_single (n : ℕ) (v : V) :
    degreeZeroLift X (Finsupp.single n v) = Finsupp.single n (X v) := by
  simp [degreeZeroLift]

include hX in
theorem degreeZeroLift_Lsub :
    Lsub R w ≤ (Lsub R w).comap (degreeZeroLift X) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, v, hv, rfl⟩
  exact Submodule.subset_span
    ⟨n, X v, preserving_Pbelow R w X hX n hv, degreeZeroLift_single X n v⟩

def ambientDegreeZeroOp : Module.End ℂ (AmbientGr R w) :=
  (Lsub R w).mapQ (Lsub R w) (degreeZeroLift X) (degreeZeroLift_Lsub R w X hX)

theorem ambientDegreeZeroOp_symbol (n : ℕ) (v : V) :
    ambientDegreeZeroOp R w X hX (symbol R w n v) = symbol R w n (X v) := by
  change (Lsub R w).mkQ (degreeZeroLift X (Finsupp.single n v)) = _
  rw [degreeZeroLift_single]
  rfl

theorem gradedCyclic_degreeZero_invariant : gradedCyclic R w ≤
    (gradedCyclic R w).comap (ambientDegreeZeroOp R w X hX) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  change ambientDegreeZeroOp R w X hX (wordSymbol R w l) ∈ gradedCyclic R w
  rw [wordSymbol, ambientDegreeZeroOp_symbol]
  exact symbol_mem_gradedCyclic R w
    (hX l.length (currentRadicalWord_mem R w l le_rfl))

/-- Restrict a genuinely filtration-preserving action to actual cyclic symbols. -/
def grPreservingOp : Module.End ℂ (Gr R w) :=
  (ambientDegreeZeroOp R w X hX).restrict
    (fun _ hv => gradedCyclic_degreeZero_invariant R w X hX hv)

theorem grPreservingOp_grWord (l : List NegLtr) :
    (grPreservingOp R w X hX (grWord R w l) : AmbientGr R w) =
      symbol R w l.length (X (nword R w l)) :=
  ambientDegreeZeroOp_symbol R w X hX l.length (nword R w l)

/-- The graded commutator on an actual word is the symbol of the actual
source commutator. Any subsequent vanishing must be proved in that degree. -/
theorem grPreservingOp_comm_word (i : Fin 9) (r : ℕ) (l : List NegLtr) :
    (((grPreservingOp R w X hX * grOp R w i r -
      grOp R w i r * grPreservingOp R w X hX) (grWord R w l)) : AmbientGr R w) =
      symbol R w (l.length + 1)
        (X (R.op (radIndex i) r (nword R w l)) -
          R.op (radIndex i) r (X (nword R w l))) := by
  change ambientDegreeZeroOp R w X hX (ambientOp R w i r (wordSymbol R w l)) -
    ambientOp R w i r (ambientDegreeZeroOp R w X hX (wordSymbol R w l)) = _
  simp only [wordSymbol, ambientOp_symbol, ambientDegreeZeroOp_symbol, map_sub]

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.grPreservingOp_comm_word
