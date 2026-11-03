import VOA.Huang.GenusOneSquareGrading

/-!
# The simultaneous S-slash on insertion vectors

All square weights are handled by one linear map. Holomorphy and the prescribed
values on eigenspaces are proved here. Preserving the block relations is a separate
algebraic issue; no trace realization is assumed.
-/
namespace VOA.Huang.GenusOne
open VOA
open scoped BigOperators MatrixGroups
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {F : M → ℂ → ℂ}

noncomputable def IsInsertionAnalyticBlock.linear (hF : IsInsertionAnalyticBlock A F) :
    M →ₗ[ℂ] (ℂ → ℂ) where
  toFun := F
  map_add' x y := funext (hF.addv x y)
  map_smul' c x := funext (hF.smulv c x)

/-- Induction on the proved square-weight decomposition. -/
theorem insertionSqWeight_induction (D : DirectSum.IsInternal (insertionSqWeight A))
    {P : M → Prop} (hhom : ∀ (α : ℂ) (x : M), sqL A 0 x = α • x → P x)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (x : M) : P x := by
  have hx : x ∈ ⨆ α, insertionSqWeight A α := by
    rw [D.submodule_iSup_eq_top]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := P) hx
    (fun α x hx => hhom α x ((mem_insertionSqWeight A α x).mp hx)) h0 hadd

/-- The endomorphism z^(-L[0]); no infinite sum of endomorphisms is used. -/
noncomputable def insertionScale (D : DirectSum.IsInternal (insertionSqWeight A)) (z : ℂ) :
    M →ₗ[ℂ] M :=
  letI := DirectSum.IsInternal.chooseDecomposition (insertionSqWeight A) D
  (DFinsupp.lsum ℂ (fun α => z ^ (-α) • (insertionSqWeight A α).subtype)).comp
    (DirectSum.decomposeLinearEquiv (insertionSqWeight A)).toLinearMap

theorem insertionScale_of_weight (D : DirectSum.IsInternal (insertionSqWeight A))
    {α : ℂ} {w : M} (hw : sqL A 0 w = α • w) (z : ℂ) :
    insertionScale D z w = z ^ (-α) • w := by
  letI := DirectSum.IsInternal.chooseDecomposition (insertionSqWeight A) D
  change (DFinsupp.lsum ℂ (fun α => z ^ (-α) • (insertionSqWeight A α).subtype))
    (DirectSum.decompose (insertionSqWeight A) w) = _
  rw [DirectSum.decompose_of_mem (insertionSqWeight A)
    ((mem_insertionSqWeight A α w).mpr hw)]
  exact DFinsupp.lsum_single ℂ (fun α => z ^ (-α) • (insertionSqWeight A α).subtype)
    α ⟨w, (mem_insertionSqWeight A α w).mpr hw⟩

/-- Canonical linear S-slash, extended by zero outside the upper half-plane. -/
noncomputable def insertionSlash (D : DirectSum.IsInternal (insertionSqWeight A))
    (hF : IsInsertionAnalyticBlock A F) : M →ₗ[ℂ] (ℂ → ℂ) where
  toFun w := (imGT 0).indicator (fun z => F (insertionScale D z w) (mobiusC ModularGroup.S z))
  map_add' x y := by
    funext z
    by_cases hz : z ∈ imGT 0
    · simp only [Set.indicator_of_mem hz, map_add, hF.addv, Pi.add_apply]
    · simp only [Set.indicator_of_notMem hz, Pi.add_apply, add_zero]
  map_smul' c x := by
    funext z
    by_cases hz : z ∈ imGT 0
    · simp only [Set.indicator_of_mem hz, map_smul, hF.smulv,
        Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    · simp only [Set.indicator_of_notMem hz, Pi.smul_apply, smul_zero]

theorem insertionSlash_apply (D : DirectSum.IsInternal (insertionSqWeight A))
    (hF : IsInsertionAnalyticBlock A F) (w : M) {z : ℂ} (hz : z ∈ imGT 0) :
    insertionSlash D hF w z = F (insertionScale D z w) (mobiusC ModularGroup.S z) := by
  exact Set.indicator_of_mem hz
    (fun z => F (insertionScale D z w) (mobiusC ModularGroup.S z))

theorem insertionSlash_of_weight (D : DirectSum.IsInternal (insertionSqWeight A))
    (hF : IsInsertionAnalyticBlock A F) {α : ℂ} {w : M}
    (hw : sqL A 0 w = α • w) {z : ℂ} (hz : z ∈ imGT 0) :
    insertionSlash D hF w z = sSlash α (F w) z := by
  rw [insertionSlash_apply D hF w hz, insertionScale_of_weight D hw, hF.smulv]
  rfl

/-- Holomorphy holds simultaneously for all vectors, including inhomogeneous ones. -/
theorem differentiableOn_insertionSlash (D : DirectSum.IsInternal (insertionSqWeight A))
    (hF : IsInsertionAnalyticBlock A F) (w : M) :
    DifferentiableOn ℂ (insertionSlash D hF w) (imGT 0) := by
  refine insertionSqWeight_induction D (P := fun w =>
    DifferentiableOn ℂ (insertionSlash D hF w) (imGT 0)) ?_ ?_ ?_ w
  · intro α x hx
    exact (differentiableOn_sSlash α (hF.holo x)).congr
      (fun z hz => insertionSlash_of_weight D hF hx hz)
  · dsimp only
    rw [map_zero]; exact differentiableOn_const 0
  · intro x y hx hy
    rw [map_add]; exact hx.add hy

/-- The eigenvector prescription determines the linear slash on the whole module. -/
theorem insertionSlash_unique (D : DirectSum.IsInternal (insertionSqWeight A))
    (hF : IsInsertionAnalyticBlock A F) (G : M →ₗ[ℂ] (ℂ → ℂ))
    (hG : ∀ (α : ℂ) (w : M), sqL A 0 w = α • w → ∀ z ∈ imGT 0, G w z = sSlash α (F w) z) :
    ∀ w z, z ∈ imGT 0 → G w z = insertionSlash D hF w z := by
  intro w
  refine insertionSqWeight_induction D (P := fun w =>
    ∀ z ∈ imGT 0, G w z = insertionSlash D hF w z) ?_ ?_ ?_ w
  · intro α x hx z hz
    rw [hG α x hx z hz, insertionSlash_of_weight D hF hx hz]
  · intro z _; simp
  · intro x y hx hy z hz
    simp only [map_add, Pi.add_apply, hx z hz, hy z hz]

end VOA.Huang.GenusOne
