import VOA.Huang.GenusOneSpanningReduction

/-!
# Algebraic coordinate-change obligations for insertion blocks

The remaining covariance conditions are on actual module vectors, not functions
or traces: covariance of the relation subspace and of the Eisenstein connection.
The latter identity includes the G₂ anomaly. Together they imply full analytic
block covariance; holomorphy and simultaneous linear extension are already proved.
Source: Miyamoto, math/0010180, Theorem 5.1 (especially condition C4).
-/
namespace VOA.Huang.GenusOne
open VOA Complex
open scoped BigOperators MatrixGroups
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {F : M → ℂ → ℂ}

theorem insertion_connection_support (A : OrdVModule W M) (z : ℂ) (w : M) :
    (Function.support fun m : ℕ =>
      zhuGC (m + 1) z • sqL A (2 * (m + 1) - 2 : ℤ) w).Finite := by
  obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A w
  refine (Set.finite_Iio K).subset fun m hm => ?_
  simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
  by_contra hn
  exact hm (by rw [hK m (by omega), smul_zero])

/-- The Eisenstein connection is a pointwise finite operator on the insertion module. -/
noncomputable def insertionConnection (A : OrdVModule W M) (z : ℂ) : M →ₗ[ℂ] M where
  toFun w := sqL A (-2) w - ∑ᶠ m : ℕ,
    zhuGC (m + 1) z • sqL A (2 * (m + 1) - 2 : ℤ) w
  map_add' x y := by
    simp only [map_add, smul_add]
    rw [finsum_add_distrib (insertion_connection_support A z x)
      (insertion_connection_support A z y)]
    abel
  map_smul' c x := by
    simp only [map_smul, smul_comm (zhuGC _ z) c]
    rw [RingHom.id_apply, smul_sub,
      smul_finsum' c (insertion_connection_support A z x)]

noncomputable def insertionNegTwoVector (A : OrdVModule W M) (a : V) (k : ℕ)
    (z : ℂ) (w : M) : M :=
  sqAct A a k (-2) w + ∑ᶠ m : ℕ,
    (((2 * (m + 1) - 1 : ℕ) : ℂ) * zhuGC (m + 1) z) •
      sqAct A a k (2 * (m + 1) - 2 : ℤ) w

theorem insertion_negTwo_support (A : OrdVModule W M) (a : V) (k : ℕ) (z : ℂ) (w : M) :
    (Function.support fun m : ℕ =>
      (((2 * (m + 1) - 1 : ℕ) : ℂ) * zhuGC (m + 1) z) •
        sqAct A a k (2 * (m + 1) - 2 : ℤ) w).Finite := by
  obtain ⟨K, hK⟩ := sqAct_tail_eventually_zero A a k w
  refine (Set.finite_Iio K).subset fun m hm => ?_
  simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
  by_contra hn
  exact hm (by rw [hK m (by omega), smul_zero])

/-- The actual two algebraic block relations at the point z. -/
noncomputable def insertionRelationSpace (A : OrdVModule W M) (z : ℂ) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ (k : ℕ), 1 ≤ k ∧ ∃ a ∈ W.grading (k : ℤ), ∃ w : M,
    x = sqAct A a k 0 w ∨ x = insertionNegTwoVector A a k z w}

noncomputable def IsInsertionAnalyticBlock.eval (hF : IsInsertionAnalyticBlock A F)
    (z : ℂ) : M →ₗ[ℂ] ℂ := (LinearMap.proj z).comp hF.linear

theorem IsInsertionAnalyticBlock.eval_connection (hF : IsInsertionAnalyticBlock A F)
    {z : ℂ} (hz : z ∈ imGT 0) (w : M) :
    hF.eval z (insertionConnection A z w) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * _root_.deriv (F w) z := by
  change hF.eval z (sqL A (-2) w - ∑ᶠ m : ℕ,
    zhuGC (m + 1) z • sqL A (2 * (m + 1) - 2 : ℤ) w) = _
  rw [map_sub, map_finsum _ (insertion_connection_support A z w)]
  simp only [map_smul, smul_eq_mul]
  change F (sqL A (-2) w) z - _ = _
  change F (sqL A (-2) w) z - (∑ᶠ m : ℕ, zhuGC (m + 1) z *
    F (sqL A (2 * (m + 1) - 2 : ℤ) w) z) = _
  rw [hF.omega w z hz, add_sub_cancel_right]

theorem IsInsertionAnalyticBlock.eval_relation (hF : IsInsertionAnalyticBlock A F)
    {z : ℂ} (hz : z ∈ imGT 0) : insertionRelationSpace A z ≤ LinearMap.ker (hF.eval z) := by
  apply Submodule.span_le.mpr
  rintro x ⟨k, hk, a, ha, w, rfl | rfl⟩
  · exact hF.vanish_apply k hk ha w z
  · change hF.eval z (sqAct A a k (-2) w + ∑ᶠ m : ℕ,
      (((2 * (m + 1) - 1 : ℕ) : ℂ) * zhuGC (m + 1) z) •
        sqAct A a k (2 * (m + 1) - 2 : ℤ) w) = 0
    rw [map_add, map_finsum _ (insertion_negTwo_support A a k z w)]
    simp only [map_smul, smul_eq_mul, mul_assoc]
    exact hF.negTwo k hk a ha w z hz

/-- Pure module-coordinate targets. These are true for the square coordinate;
neither field assumes block covariance, trace spanning, or any modular law for traces.
The second field records the quasimodular correction explicitly. -/
structure InsertionCoordinateCovariance (A : OrdVModule W M)
    (D : DirectSum.IsInternal (insertionSqWeight A)) : Prop where
  relations : ∀ z ∈ imGT 0, ∀ w ∈ insertionRelationSpace A z,
    insertionScale D z w ∈ insertionRelationSpace A (mobiusC ModularGroup.S z)
  connection : ∀ z ∈ imGT 0, ∀ w : M,
    insertionConnection A (mobiusC ModularGroup.S z) (insertionScale D z w) =
      z ^ (2 : ℕ) • insertionScale D z (insertionConnection A z w) +
        (z / (2 * (Real.pi : ℂ) * I)) • insertionScale D z (sqL A 0 w)

theorem insertionSlash_deriv_of_coordinateCovariance
    (D : DirectSum.IsInternal (insertionSqWeight A))
    (hcoord : InsertionCoordinateCovariance A D) (hF : IsInsertionAnalyticBlock A F)
    (w : M) {z : ℂ} (hz : z ∈ imGT 0) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * _root_.deriv (insertionSlash D hF w) z =
      insertionSlash D hF (insertionConnection A z w) z := by
  have hz0 : z ≠ 0 := by rintro rfl; exact (lt_irrefl (0 : ℝ)) hz
  have hsz := mobiusC_mem_imGT ModularGroup.S hz
  refine insertionSqWeight_induction D (P := fun w =>
    (2 * (Real.pi : ℂ) * I)⁻¹ * _root_.deriv (insertionSlash D hF w) z =
      insertionSlash D hF (insertionConnection A z w) z) ?_ ?_ ?_ w
  · intro α x hx
    have he : insertionSlash D hF x =ᶠ[nhds z] sSlash α (F x) := by
      filter_upwards [(isOpen_imGT 0).mem_nhds hz] with t ht
      exact insertionSlash_of_weight D hF hx ht
    have hc := congrArg (hF.eval (mobiusC ModularGroup.S z)) (hcoord.connection z hz x)
    rw [insertionScale_of_weight D hx, map_smul, map_smul, hF.eval_connection hsz,
      map_add, map_smul, hx, map_smul, map_smul, insertionScale_of_weight D hx,
      map_smul] at hc
    simp only [map_smul, smul_eq_mul] at hc
    change z ^ (-α) * ((2 * (Real.pi : ℂ) * I)⁻¹ * _root_.deriv (F x)
        (mobiusC ModularGroup.S z)) =
      z ^ (2 : ℕ) * F (insertionScale D z (insertionConnection A z x))
        (mobiusC ModularGroup.S z) +
        (z / (2 * (Real.pi : ℂ) * I)) * (α * (z ^ (-α) * F x (mobiusC ModularGroup.S z))) at hc
    rw [he.deriv_eq, deriv_sSlash α (hF.holo x) hz, insertionSlash_apply D hF _ hz]
    field_simp
    field_simp at hc
    linear_combination hc
  · dsimp only
    simp only [map_zero, Pi.zero_apply, deriv_zero, mul_zero]
  · intro x y hx hy
    dsimp only at hx hy ⊢
    rw [map_add, deriv_add
      ((differentiableOn_insertionSlash D hF x).differentiableAt ((isOpen_imGT 0).mem_nhds hz))
      ((differentiableOn_insertionSlash D hF y).differentiableAt ((isOpen_imGT 0).mem_nhds hz)),
      map_add, map_add, Pi.add_apply, mul_add, hx, hy]

/-- All analytic block conditions follow from the two module-coordinate identities. -/
theorem isInsertionAnalyticBlock_insertionSlash
    (D : DirectSum.IsInternal (insertionSqWeight A))
    (hcoord : InsertionCoordinateCovariance A D) (hF : IsInsertionAnalyticBlock A F) :
    IsInsertionAnalyticBlock A (insertionSlash D hF) := by
  let G := insertionSlash D hF
  have hrel : ∀ z ∈ imGT 0, ∀ x ∈ insertionRelationSpace A z, G x z = 0 := by
    intro z hz x hx
    rw [insertionSlash_apply D hF x hz]
    exact hF.eval_relation (mobiusC_mem_imGT ModularGroup.S hz) (hcoord.relations z hz x hx)
  refine ⟨differentiableOn_insertionSlash D hF,
    fun x y z => congrFun (G.map_add x y) z,
    fun c x z => congrFun (G.map_smul c x) z, ?_, ?_, ?_⟩
  · intro k hk a ha w
    funext z
    by_cases hz : z ∈ imGT 0
    · exact hrel z hz _ (Submodule.subset_span ⟨k, hk, a, ha, w, Or.inl rfl⟩)
    · exact Set.indicator_of_notMem hz
        (fun t => F (insertionScale D t (sqAct A a k 0 w)) (mobiusC ModularGroup.S t))
  · intro k hk a ha w z hz
    let E : M →ₗ[ℂ] ℂ := (LinearMap.proj z).comp G
    have hr := hrel z hz _ (Submodule.subset_span ⟨k, hk, a, ha, w, Or.inr rfl⟩)
    change E (insertionNegTwoVector A a k z w) = 0 at hr
    change E (sqAct A a k (-2) w) + ∑ᶠ m : ℕ,
      ((2 * (m + 1) - 1 : ℕ) : ℂ) *
        (zhuGC (m + 1) z * E (sqAct A a k (2 * (m + 1) - 2 : ℤ) w)) = 0
    rw [insertionNegTwoVector, map_add,
      map_finsum _ (insertion_negTwo_support A a k z w)] at hr
    simpa only [map_smul, smul_eq_mul, mul_assoc] using hr
  · intro w z hz
    let E : M →ₗ[ℂ] ℂ := (LinearMap.proj z).comp G
    have hd := insertionSlash_deriv_of_coordinateCovariance D hcoord hF w hz
    change (2 * (Real.pi : ℂ) * I)⁻¹ * _root_.deriv (G w) z =
      E (sqL A (-2) w - ∑ᶠ m : ℕ,
        zhuGC (m + 1) z • sqL A (2 * (m + 1) - 2 : ℤ) w) at hd
    rw [map_sub, map_finsum _ (insertion_connection_support A z w)] at hd
    simp only [map_smul, smul_eq_mul] at hd
    change E (sqL A (-2) w) = (2 * (Real.pi : ℂ) * I)⁻¹ * _root_.deriv (G w) z +
      ∑ᶠ m : ℕ, zhuGC (m + 1) z * E (sqL A (2 * (m + 1) - 2 : ℤ) w)
    linear_combination -hd

/-- The full simultaneous covariance target reduces to pure module-coordinate algebra. -/
theorem insertionSBlockCovariance_of_coordinateCovariance
    (D : DirectSum.IsInternal (insertionSqWeight A))
    (hcoord : InsertionCoordinateCovariance A D) : InsertionSBlockCovariance A := by
  intro F hF
  exact ⟨insertionSlash D hF, isInsertionAnalyticBlock_insertionSlash D hcoord hF,
    fun _ _ hw _ hz => insertionSlash_of_weight D hF hw hz⟩

/-- Assembly with only the algebraic coordinate and finite interpolation residuals. -/
theorem insertionSClosure_of_coordinates_interpolation
    {ι : Type u} [Fintype ι] (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (D : DirectSum.IsInternal (insertionSqWeight A))
    (hcoord : InsertionCoordinateCovariance A D)
    {U : Finset M} (hU : InsertionDetermining A U) (τ₀ : UpperHalfPlane)
    (hint : InsertionTraceInterpolation A Mfam h U τ₀) : InsertionSClosure A Mfam h :=
  insertionSClosure_of_covariance_spanning hC2 hA Mfam h hcw
    (insertionSBlockCovariance_of_coordinateCovariance D hcoord)
    (insertionTraceSpanning_of_interpolation hC2 hA Mfam h hcw hU τ₀ hint)

end VOA.Huang.GenusOne
