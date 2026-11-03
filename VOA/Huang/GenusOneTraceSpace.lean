import VOA.Huang.GenusOneSClosure

/-!
# The finite-dimensional space of one-point intertwiner traces

The trace space is the range of a linear map from the finite direct product of
self-intertwiner spaces. Its finite dimensionality does not imply S-invariance.
-/
namespace VOA.Huang.GenusOne
open VOA
open scoped BigOperators
universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Convergence makes evaluation linear in the intertwiner. -/
noncomputable def traceFunctionLinear (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    {h : ℂ} (hcw : HasConformalWeight N h) :
    IntertwiningOperator A N N →ₗ[ℂ] (M₁ → UpperHalfPlane → ℂ) where
  toFun Y := traceFunction Y h
  map_add' Y Z := by
    funext w τ
    change traceFunction (Y + Z) h w τ = traceFunction Y h w τ + traceFunction Z h w τ
    rw [← traceFunctionC_coe, ← traceFunctionC_coe, ← traceFunctionC_coe]
    change qEvalC (traceLinear (Y + Z) w) _ _ = _
    rw [map_add, LinearMap.add_apply]
    exact qEvalC_add _ _ _
      (summable_qTerm _ _ (traceSubexponential_of_irreducible hC2 hA Y hcw w) τ.im_pos)
      (summable_qTerm _ _ (traceSubexponential_of_irreducible hC2 hA Z hcw w) τ.im_pos)
  map_smul' c Y := by
    funext w τ
    change traceFunction (c • Y) h w τ = c * traceFunction Y h w τ
    unfold traceFunction
    change qEvalAt (traceLinear (c • Y) w) _ _ = _
    rw [map_smul, LinearMap.smul_apply, qEvalAt_smul]
    rfl

/-- Self-intertwiner spaces are finite dimensional, with no new fusion-rule input. -/
theorem finiteDimensional_selfIntertwiners (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (P : IrrModule W) :
    FiniteDimensional ℂ (IntertwiningOperator A P.isMod P.isMod) := by
  obtain ⟨a, ha, hne⟩ := A.exists_isLowestWeight_of_irreducible hA
  let Q : LWModule W := ⟨M₁, A, a, ha, hne⟩
  exact FusionC2.finiteDimensional_intertwiningSpace_of_C2 (P₁ := Q)
    (P₂ := P.toIrrLWModule.val) (P₃ := P.toIrrLWModule.val)
    (moduleC2_of_irreducible hC2 hA) P.irreducible P.irreducible

variable {ι : Type u} [Fintype ι]

/-- Sum of trace functions on a finite family of irreducible traced modules. -/
noncomputable def traceFamilyLinear (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) :
    (∀ i, IntertwiningOperator A (Mfam i).isMod (Mfam i).isMod) →ₗ[ℂ]
      (M₁ → UpperHalfPlane → ℂ) where
  toFun Z w τ := ∑ i, traceFunction (Z i) (h i) w τ
  map_add' Z Z' := by
    funext w τ
    change (∑ i, traceFunction (Z i + Z' i) (h i) w τ) =
      (∑ i, traceFunction (Z i) (h i) w τ) + ∑ i, traceFunction (Z' i) (h i) w τ
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      congrFun (congrFun ((traceFunctionLinear hC2 hA (hcw i)).map_add (Z i) (Z' i)) w) τ
  map_smul' c Z := by
    funext w τ
    change (∑ i, traceFunction (c • Z i) (h i) w τ) = c * ∑ i, traceFunction (Z i) (h i) w τ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      congrFun (congrFun ((traceFunctionLinear hC2 hA (hcw i)).map_smul c (Z i)) w) τ

/-- Finite dimensionality of the simultaneous trace space in both w and τ.
Completeness of the finite family is not needed for this dimension statement. -/
theorem finiteDimensional_traceFamily_range (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) :
    FiniteDimensional ℂ (LinearMap.range (traceFamilyLinear hC2 hA Mfam h hcw)) := by
  letI : ∀ i, FiniteDimensional ℂ (IntertwiningOperator A (Mfam i).isMod (Mfam i).isMod) :=
    fun i => finiteDimensional_selfIntertwiners hC2 hA (Mfam i)
  exact Module.Finite.range (traceFamilyLinear hC2 hA Mfam h hcw)

end VOA.Huang.GenusOne
