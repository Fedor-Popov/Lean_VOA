import VOA.Huang.GenusOneConnectionCovariance

/-! # S-covariance of the module relation space

Extend both state slots linearly before using square weights. The G₂ term is
removed by the zero-mode relation, exactly as in Miyamoto Theorem 5.1, C3.
-/
namespace VOA.Huang.GenusOne.SquareModule
open VOA Complex
open scoped BigOperators MatrixGroups
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

theorem sqMode_eventually_zero (A : OrdVModule W M) (a : V) (w : M) :
    ∃ K : ℤ, ∀ j : ℤ, K ≤ j → sqMode A j a w = 0 := by
  refine ordinaryGrading_induction W (P := fun a =>
    ∃ K : ℤ, ∀ j : ℤ, K ≤ j → sqMode A j a w = 0) ?_ ?_ ?_ a
  · intro k a ha
    obtain ⟨K, hK⟩ := sqAct_eventually_zero A a k.toNat w
    exact ⟨K, fun j hj => by rw [sqMode_of_mem_grading A ha]; exact hK j hj⟩
  · exact ⟨0, fun j _ => by simp⟩
  · rintro a b ⟨Ka, ha⟩ ⟨Kb, hb⟩
    exact ⟨max Ka Kb, fun j hj => by
      rw [map_add, LinearMap.add_apply, ha j (le_trans (le_max_left _ _) hj),
        hb j (le_trans (le_max_right _ _) hj), add_zero]⟩

theorem sqMode_tail_support (A : OrdVModule W M) (a : V) (w : M) (c : ℕ → ℂ) :
    (Function.support fun m : ℕ => c m • sqMode A (2 * (m + 2) - 2 : ℤ) a w).Finite := by
  obtain ⟨K, hK⟩ := sqMode_eventually_zero A a w
  refine (Set.finite_Iio (K.toNat + 1)).subset fun m hm => ?_
  simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
  by_contra hn
  exact hm (by rw [hK _ (by omega), smul_zero])

/-- The minus-two relation after removing its zero-mode G₂ term. -/
noncomputable def negVector (A : OrdVModule W M) (z : ℂ) (w : M) : V →ₗ[ℂ] M where
  toFun a := sqMode A (-2) a w + ∑ᶠ m : ℕ,
    (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) z) •
      sqMode A (2 * (m + 2) - 2 : ℤ) a w
  map_add' a b := by
    simp only [map_add, LinearMap.add_apply, smul_add]
    rw [finsum_add_distrib (sqMode_tail_support A a w _) (sqMode_tail_support A b w _)]
    abel
  map_smul' c a := by
    simp only [map_smul, LinearMap.smul_apply, smul_comm _ c, RingHom.id_apply]
    rw [smul_add, smul_finsum' c (sqMode_tail_support A a w _)]

theorem insertionNegTwoVector_eq {a : V} {k : ℕ} (ha : a ∈ W.grading (k : ℤ))
    (z : ℂ) (w : M) :
    insertionNegTwoVector A a k z w =
      negVector A z w a + zhuGC 1 z • sqAct A a k 0 w := by
  obtain ⟨K, hK⟩ := sqAct_tail_eventually_zero A a k w
  have hp := finsum_nat_peel_module (K := K) (f := fun m : ℕ =>
    (((2 * (m + 1) - 1 : ℕ) : ℂ) * zhuGC (m + 1) z) •
      sqAct A a k (2 * (m + 1) - 2 : ℤ) w)
    (fun m hm => by dsimp only; rw [hK m hm, smul_zero])
  rw [insertionNegTwoVector, hp]
  change _ = sqMode A (-2) a w + _ + _
  simp only [sqMode_of_mem_grading A ha, Int.toNat_natCast]
  norm_num only [Nat.zero_add, Nat.cast_zero, zero_add, Nat.reduceMul, Nat.reduceSub,
    Nat.cast_one, one_mul, mul_one, sub_self]
  have ht : (∑ᶠ m : ℕ,
      (((2 * (m + 1 + 1) - 1 : ℕ) : ℂ) * zhuGC (m + 1 + 1) z) •
        sqAct A a k (2 * ((m + 1 : ℕ) + 1) - 2 : ℤ) w) =
      ∑ᶠ m : ℕ, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) z) •
        sqAct A a k (2 * (m + 2) - 2 : ℤ) w := by
    apply finsum_congr
    intro m
    congr 2
  rw [ht]
  abel

theorem sqMode_zero_mem_relation (A : OrdVModule W M) (z : ℂ) (a : V) (w : M) :
    sqMode A 0 a w ∈ insertionRelationSpace A z := by
  refine ordinaryGrading_induction W (P := fun a =>
    sqMode A 0 a w ∈ insertionRelationSpace A z) ?_ ?_ ?_ a
  · intro k x hx
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · rw [W.positivity k hk, Submodule.mem_bot] at hx
      simp [hx]
    · rw [W.vacuum_grade, Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_smul, LinearMap.smul_apply,
        sqMode_of_mem_grading A W.vacuum_mem_grading_zero]
      simp [sqAct_vacuum]
    · have hx' : x ∈ W.grading (k.toNat : ℤ) := by
        simpa [Int.toNat_of_nonneg (le_of_lt hk)] using hx
      rw [sqMode_of_mem_grading A hx]
      exact Submodule.subset_span ⟨k.toNat, by omega, x, hx', w, Or.inl rfl⟩
  · simp
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy

theorem negVector_mem_relation (A : OrdVModule W M) (z : ℂ) (a : V) (w : M) :
    negVector A z w a ∈ insertionRelationSpace A z := by
  refine ordinaryGrading_induction W (P := fun a =>
    negVector A z w a ∈ insertionRelationSpace A z) ?_ ?_ ?_ a
  · intro k x hx
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · rw [W.positivity k hk, Submodule.mem_bot] at hx
      simp [hx]
    · rw [W.vacuum_grade, Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_smul]
      apply Submodule.smul_mem
      change sqMode A (-2) W.vacuum w + _ ∈ _
      simp only [sqMode_of_mem_grading A W.vacuum_mem_grading_zero, Int.toNat_zero]
      have hzero (j : ℤ) (hj : j ≠ -1) : sqAct A W.vacuum 0 j w = 0 := by
        rw [sqAct_vacuum, if_neg hj, zero_smul, LinearMap.zero_apply]
      rw [hzero (-2) (by norm_num)]
      have ht (m : ℕ) : sqAct A W.vacuum 0 (2 * (m + 2) - 2 : ℤ) w = 0 :=
        hzero _ (by omega)
      simp only [ht, smul_zero, finsum_zero, add_zero]
      exact Submodule.zero_mem _
    · have hx' : x ∈ W.grading (k.toNat : ℤ) := by
        simpa [Int.toNat_of_nonneg (le_of_lt hk)] using hx
      have hneg : insertionNegTwoVector A x k.toNat z w ∈ insertionRelationSpace A z :=
        Submodule.subset_span ⟨k.toNat, by omega, x, hx', w, Or.inr rfl⟩
      have h0 := sqMode_zero_mem_relation A z x w
      rw [sqMode_of_mem_grading A hx] at h0
      rw [insertionNegTwoVector_eq hx'] at hneg
      exact (Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ h0)).mp hneg
  · simp
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Covariance of an individual square-homogeneous minus-two relation. -/
theorem insertionScale_negVector (D : DirectSum.IsInternal (insertionSqWeight A))
    {a : V} {β : ℂ} (ha : Lsq W 0 a = β • a) {z : ℂ} (hz : z ∈ imGT 0) (w : M) :
    insertionScale D z (negVector A z w a) =
      z ^ (-(β + 1)) • negVector A (mobiusC ModularGroup.S z) (insertionScale D z w) a := by
  have hz0 : z ≠ 0 := by rintro rfl; exact (lt_irrefl (0 : ℝ)) hz
  change insertionScale D z (sqMode A (-2) a w + _) = _ • (sqMode A (-2) a _ + _)
  rw [map_add, map_finsum _ (sqMode_tail_support A a w _), smul_add,
    smul_finsum' _ (sqMode_tail_support A a (insertionScale D z w) _)]
  congr 1
  · rw [insertionScale_sqMode D ha _ hz0]
    congr 2
    push_cast
    ring
  · apply finsum_congr
    intro m
    rw [map_smul, insertionScale_sqMode D ha _ hz0, zhuGC_S (by omega) hz]
    simp only [smul_smul]
    have hp : z ^ (-(β - ((2 * (m + 2) - 2 : ℤ) : ℂ) - 1)) =
        z ^ (-(β + 1)) * z ^ (2 * (m + 2) : ℕ) := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hz0]
      congr 1
      push_cast
      ring
    rw [hp]
    congr 1
    ring

theorem insertionScale_zero_mem_relation (D : DirectSum.IsInternal (insertionSqWeight A))
    {z : ℂ} (hz : z ∈ imGT 0) (a : V) (w : M) :
    insertionScale D z (sqMode A 0 a w) ∈ insertionRelationSpace A (mobiusC ModularGroup.S z) := by
  have hz0 : z ≠ 0 := by rintro rfl; exact (lt_irrefl (0 : ℝ)) hz
  refine sqWeightNat_induction W (P := fun a =>
    insertionScale D z (sqMode A 0 a w) ∈ insertionRelationSpace A (mobiusC ModularGroup.S z))
    ?_ ?_ ?_ a
  · intro k x hx
    rw [insertionScale_sqMode D ((mem_sqWeightSpace_iff W _ x).mp hx) _ hz0]
    exact Submodule.smul_mem _ _ (sqMode_zero_mem_relation A _ _ _)
  · simp
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply, map_add]
    exact Submodule.add_mem _ hx hy

theorem insertionScale_neg_mem_relation (D : DirectSum.IsInternal (insertionSqWeight A))
    {z : ℂ} (hz : z ∈ imGT 0) (a : V) (w : M) :
    insertionScale D z (negVector A z w a) ∈
      insertionRelationSpace A (mobiusC ModularGroup.S z) := by
  refine sqWeightNat_induction W (P := fun a =>
    insertionScale D z (negVector A z w a) ∈ insertionRelationSpace A (mobiusC ModularGroup.S z))
    ?_ ?_ ?_ a
  · intro k x hx
    rw [insertionScale_negVector D ((mem_sqWeightSpace_iff W _ x).mp hx) hz]
    exact Submodule.smul_mem _ _ (negVector_mem_relation A _ _ _)
  · simp
  · intro x y hx hy
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

end VOA.Huang.GenusOne.SquareModule

namespace VOA.Huang.GenusOne
open VOA Complex SquareModule
open scoped MatrixGroups
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

/-- The relation field of `InsertionCoordinateCovariance`. -/
theorem insertionRelationSpace_S (D : DirectSum.IsInternal (insertionSqWeight A))
    {z : ℂ} (hz : z ∈ imGT 0) {w : M} (hw : w ∈ insertionRelationSpace A z) :
    insertionScale D z w ∈ insertionRelationSpace A (mobiusC ModularGroup.S z) := by
  change w ∈ Submodule.span ℂ _ at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, a, ha, w, rfl | rfl⟩ := hx
    · have he : sqAct A a k 0 = SquareModule.sqMode A 0 a := by
        rw [SquareModule.sqMode_of_mem_grading A ha, Int.toNat_natCast]
      rw [he]
      exact insertionScale_zero_mem_relation D hz a w
    · rw [insertionNegTwoVector_eq ha, map_add, map_smul]
      apply Submodule.add_mem _ (insertionScale_neg_mem_relation D hz a w)
      apply Submodule.smul_mem
      have he : sqAct A a k 0 = SquareModule.sqMode A 0 a := by
        rw [SquareModule.sqMode_of_mem_grading A ha, Int.toNat_natCast]
      rw [he]
      exact insertionScale_zero_mem_relation D hz a w
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

/-- Both coordinate fields hold for every supplied internal square-weight decomposition. -/
theorem insertionCoordinateCovariance_holds (D : DirectSum.IsInternal (insertionSqWeight A)) :
    InsertionCoordinateCovariance A D :=
  ⟨fun _ hz _ hw => insertionRelationSpace_S D hz hw,
    fun _ hz w => insertionConnection_S D hz w⟩

/-- Simultaneous analytic block covariance for every irreducible ordinary insertion. -/
theorem insertionSBlockCovariance_of_irreducible (hA : A.IsIrreducible) :
    InsertionSBlockCovariance A :=
  insertionSBlockCovariance_of_coordinateCovariance
    (insertionSqWeight_isInternal_of_irreducible A hA)
    (insertionCoordinateCovariance_holds _)

end VOA.Huang.GenusOne
