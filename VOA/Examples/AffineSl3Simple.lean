import VOA.Examples.AffineSl3Virasoro
import VOA.Examples.AffineSl3VacuumWeightOne
import VOA.Examples.AffineSimpleQuotient

/-!
# The actual simple affine sl3 quotient

The nonzero universal vacuum VOA has its canonical simple quotient at
all noncritical levels. Its current fields descend with the same level,
and at nonzero level no weight-one matrix state is lost: the positive
mode reads the nondegenerate trace form against the surviving vacuum.
No admissible singular-vector or determinant assertion is used here.
-/
namespace VOA.AffineSl3
open VOA.AffineLie Module
open scoped BigOperators
noncomputable section

/-- A basis current state is the corresponding minus-one creation mode. -/
theorem currentState_generator (k : ℂ) (a : Fin 8) :
    currentState k (generator a)=J k a (-1) (vacuumA k) := rfl

/-- The reconstructed field of any matrix current state has exactly the
original affine current modes, not merely the same vacuum coefficient. -/
theorem mode_YA_currentState (k : ℂ) (hk : k+3≠0) (x : Sl3) (n : ℤ) :
    mode (YA k hk (currentState k x)) n =
      vacuumRho form form_invariant k (current x n) := by
  let ev : FormalDist (End ℂ (Vacuum k)) →ₗ[ℂ] End ℂ (Vacuum k) :=
    { toFun := fun f => mode f n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev (YA k hk (currentState k x)) = _
  rw [basis_decomp x]
  simp only [map_sum,map_smul,currentState_generator,YA_current_state]
  have hev (a : Fin 8) : ev (Jfield k a)=J k a n := Jfield_mode k a n
  simp only [hev]
  unfold current
  simp only [← ofLoopₗ_apply,map_sum,map_smul]
  rfl

/-- The maximal proper ideal of the actual universal sl3 vacuum VOA. -/
def maxIdeal (k : ℂ) (hk : k+3≠0) : Submodule ℂ (Vacuum k) :=
  QuotVOA.maxGradedIdeal (affineSl3VOA k hk)

/-- The carrier of the actual simple affine sl3 VOA. -/
abbrev SimpleSpace (k : ℂ) (hk : k+3≠0) := Vacuum k ⧸ maxIdeal k hk

/-- The canonical projection to the simple affine carrier. -/
def simpleProjection (k : ℂ) (hk : k+3≠0) : Vacuum k →ₗ[ℂ] SimpleSpace k hk :=
  (maxIdeal k hk).mkQ

/-- The actual simple affine sl3 VOA, formed by the maximal proper ideal. -/
def simpleVOA (k : ℂ) (hk : k+3≠0) : VertexOperatorAlgebra (SimpleSpace k hk) :=
  QuotVOA.maxQuotientVOA (affineSl3VOA k hk)

/-- The quotient is simple among all ideals, not only graded ideals. -/
theorem simpleVOA_isSimple (k : ℂ) (hk : k+3≠0) : (simpleVOA k hk).IsSimple :=
  QuotVOA.isSimple_maxQuotientVOA' (affineSl3VOA k hk) (vacuumA_ne_zero k)

/-- The quotient vacuum survives; simplicity is not a zero-algebra statement. -/
theorem simple_vacuum_ne_zero (k : ℂ) (hk : k+3≠0) :
    (simpleVOA k hk).vacuum≠0 :=
  SimpleQuot.maxQuotientVOA_vacuum_ne_zero (affineSl3VOA k hk) (vacuumA_ne_zero k)

/-- The simple affine quotient has the same Sugawara central charge. -/
theorem simple_centralCharge (k : ℂ) (hk : k+3≠0) :
    (simpleVOA k hk).centralCharge=8*k/(k+3) := rfl

/-- Every product descends through the actual quotient projection. -/
theorem simpleProjection_product (k : ℂ) (hk : k+3≠0) (u v : Vacuum k) (n : ℤ) :
    (simpleVOA k hk).smul (simpleProjection k hk u) n (simpleProjection k hk v)=
      simpleProjection k hk ((affineSl3VOA k hk).smul u n v) :=
  SimpleQuot.maxQuotientVOA_mkQ_smul (affineSl3VOA k hk) u n v

/-- A matrix current in the simple quotient, linear in the matrix. -/
def simpleCurrentState (k : ℂ) (hk : k+3≠0) : Sl3 →ₗ[ℂ] SimpleSpace k hk :=
  (simpleProjection k hk).comp (currentState k)

/-- The actual simple weight-one space is spanned by matrix current states. -/
theorem simple_grading_one_eq_range (k : ℂ) (hk : k+3≠0) :
    (simpleVOA k hk).grading 1=LinearMap.range (simpleCurrentState k hk) := by
  change (gradingZA k 1).map (simpleProjection k hk)=_
  rw [grading_one_eq_range, simpleCurrentState, LinearMap.range_comp]

/-- The simple current's first product is level times the trace pairing
against the surviving quotient vacuum. -/
theorem simpleCurrentState_first_product (k : ℂ) (hk : k+3≠0) (x y : Sl3) :
    (simpleVOA k hk).smul (simpleCurrentState k hk y) 1 (simpleCurrentState k hk x)=
      (k*form y x) • (simpleVOA k hk).vacuum := by
  change (simpleVOA k hk).smul (simpleProjection k hk (currentState k y)) 1
    (simpleProjection k hk (currentState k x))=_
  rw [simpleProjection_product]
  change simpleProjection k hk (mode (YA k hk (currentState k y)) 1 (currentState k x))=_
  rw [mode_YA_currentState,positive_current_currentState,map_smul]
  rfl

/-- Nonzero level prevents any matrix current from vanishing in the simple
quotient, by the actual first-product trace pairing. -/
theorem simpleCurrentState_injective (k : ℂ) (hk : k+3≠0) (hk0 : k≠0) :
    Function.Injective (simpleCurrentState k hk) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply form_right_nondegenerate x
  intro y
  have h := simpleCurrentState_first_product k hk x y
  rw [hx,PreVertexAlgebra.smul_zero_right] at h
  have hs : k*form y x=0 := (smul_eq_zero.mp h.symm).resolve_right (simple_vacuum_ne_zero k hk)
  exact (mul_eq_zero.mp hs).resolve_left hk0

/-- Weight one of the actual simple affine sl3 VOA is exactly sl3 whenever
level is nonzero and noncritical. -/
def simpleWeightOneEquiv (k : ℂ) (hk : k+3≠0) (hk0 : k≠0) :
    Sl3 ≃ₗ[ℂ] (simpleVOA k hk).grading 1 :=
  (LinearEquiv.ofInjective (simpleCurrentState k hk) (simpleCurrentState_injective k hk hk0)).trans
    (LinearEquiv.ofEq _ _ (simple_grading_one_eq_range k hk).symm)

/-- The eight actual Chevalley current states form a basis of simple weight one. -/
def simpleWeightOneBasis (k : ℂ) (hk : k+3≠0) (hk0 : k≠0) :
    Module.Basis (Fin 8) ℂ ((simpleVOA k hk).grading 1) :=
  chevalleyBasis.map (simpleWeightOneEquiv k hk hk0)

/-- The simple affine weight-one space has dimension eight at nonzero,
noncritical level; no additional singular-vector input is required. -/
theorem simple_weightOne_finrank (k : ℂ) (hk : k+3≠0) (hk0 : k≠0) :
    Module.finrank ℂ ((simpleVOA k hk).grading 1)=8 := by
  simpa using Module.finrank_eq_card_basis (simpleWeightOneBasis k hk hk0)

end
end VOA.AffineSl3
