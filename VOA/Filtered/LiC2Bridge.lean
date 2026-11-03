import VOA.Filtered.ClassicalFreeness
import VOA.Filtered.LiPoissonVertexAlgebra
import VOA.Modules.PoissonDescent

/-!
# The genuine C2 quotient at Li degree zero

The first Li filtration piece equals C2, not just contains it. The reverse
inclusion follows directly from the defining negative-mode words: a positive
total mode depth forces one mode at most minus two, and all outer minus-one
modes preserve C2.
-/

namespace VOA
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A negative-mode word with positive total depth lies in C2. -/
theorem wordAct_mem_O₂_of_level_pos (W : VertexOperatorAlgebra V)
    (l : List (Letter V)) (w : V) (hl : 1 ≤ wordLevel l) :
    wordAct (adjointWeakModule W) l w ∈ O₂ W := by
  induction l with
  | nil => simp only [wordLevel_nil] at hl; omega
  | cons a l ih =>
      change W.smul a.1 (-(a.2.2 : ℤ) - 1) (wordAct (adjointWeakModule W) l w) ∈ O₂ W
      by_cases ha : a.2.2 = 0
      · have ht : 1 ≤ wordLevel l := by simpa only [wordLevel_cons, ha, zero_add] using hl
        simpa only [ha, Nat.cast_zero, neg_zero, zero_sub] using
          poissonMul_mem_O₂_right W a.1 (ih ht)
      · exact smul_le_neg_two_mem_O₂ W _ _ (by omega)

/-- The first Li filtration piece is contained in the genuine C2 subspace. -/
theorem liFiltration_one_le_O₂ (W : VertexOperatorAlgebra V) :
    liFiltration W 1 ≤ O₂ W := by
  change Submodule.span ℂ (Gset (adjointWeakModule W) ({W.vacuum} : Set V) 1) ≤ O₂ W
  apply Submodule.span_le.mpr
  rintro x ⟨l, w, _, _, hl, rfl⟩
  exact wordAct_mem_O₂_of_level_pos W l w hl

/-- Equality of the first Li filtration piece and C2, for every VOA. -/
theorem liFiltration_one_eq_O₂ (W : VertexOperatorAlgebra V) :
    liFiltration W 1 = O₂ W :=
  le_antisymm (liFiltration_one_le_O₂ W) (O₂_le_liFiltration_one W)

/-- A homogeneous degree-zero class vanishes precisely on C2. -/
theorem liDegreeZeroClass_eq_zero_iff_mem_O₂ (W : VertexOperatorAlgebra V) (N : ℕ)
    (x : W.grading (N : ℤ)) : liDegreeZeroClass W N x = 0 ↔ x.1 ∈ O₂ W := by
  constructor
  · intro h
    have hi := DirectSum.of_injective (β := fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (0, N)
    unfold liDegreeZeroClass at h
    have hq := hi (h.trans (map_zero _).symm)
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hq
    change x.1 ∈ liWeightPiece W 1 N at hm
    rw [← liFiltration_one_eq_O₂]
    exact hm.1
  · exact liDegreeZeroClass_eq_zero_of_mem_O₂ W N x

/-- The intrinsic zeroth Li quotient is exactly the genuine C2 quotient. -/
noncomputable def liZerothQuotientEquivC2 (W : VertexOperatorAlgebra V) :
    (V ⧸ liFiltration W 1) ≃ₗ[ℂ] A₂ W :=
  Submodule.quotEquivOfEq _ _ (liFiltration_one_eq_O₂ W)

/-- Every positive mode vanishes between degree-zero Li classes. -/
theorem liDegreeZeroClass_mode_succ (W : VertexOperatorAlgebra V) (N M n : ℕ)
    (x : W.grading (N : ℤ)) (y : W.grading (M : ℤ)) :
    liAssociatedGradedMode W (n + 1) (liDegreeZeroClass W N x) (liDegreeZeroClass W M y) = 0 := by
  change liAssociatedGradedMode W (n + 1)
    (liGradedClass W 0 N x.1 _) (liGradedClass W 0 M y.1 _) = 0
  exact liGradedClass_mode_eq_zero W 0 0 N M (n + 1) (Or.inl (by omega)) _ _ _ _

/-- The zeroth Li mode is represented by the genuine C2 Poisson bracket. -/
theorem liDegreeZeroClass_mode_zero (W : VertexOperatorAlgebra V) (N M : ℕ)
    (hNM : 1 ≤ N + M) (x : W.grading (N : ℤ)) (y : W.grading (M : ℤ)) :
    liAssociatedGradedMode W 0 (liDegreeZeroClass W N x) (liDegreeZeroClass W M y) =
      liDegreeZeroClass W (N + M - 1)
        ⟨poissonBracket W x.1 y.1, by
          have h := W.smul_mem_grading x.2 y.2 (0 : ℤ)
          have heq : ((N + M - 1 : ℕ) : ℤ) = (N : ℤ) + M - 0 - 1 := by
            rw [Nat.cast_sub hNM, Nat.cast_add, Nat.cast_one]
            ring
          simpa only [heq, poissonBracket_def] using h⟩ := by
  change liAssociatedGradedMode W 0
    (liGradedClass W 0 N x.1 _) (liGradedClass W 0 M y.1 _) = _
  rw [liGradedClass_mode W 0 0 N M 0 (by omega) (by omega)]
  rfl

end VOA
