import VOA.Huang.GenusTwoPointSepQTransport
import VOA.Huang.GenusOneQEquationSepEquations

/-!
# Collected Ward identities and the exact trace-descent interface

A complex-bilinear trace has a canonical scalar extension to Huang's tensor
module. It is enough to collect each minus-two identity at one valid cutoff;
the relation tensors are independent of the cutoff. Both orientations are
retained. The collected identities for the actual geometric trace remain
explicit hypotheses, not consequences of the raw q-transport theorem.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA QEquation
open scoped BigOperators TensorProduct
universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}
  {R : Type*} [CommRing R] [Algebra ℂ R]

private theorem sum_range_eq_of_tails {F : Type*} [AddCommGroup F]
    (f : ℕ → F) {K L : ℕ} (hK : ∀ m, K ≤ m → f m = 0)
    (hL : ∀ m, L ≤ m → f m = 0) :
    ∑ m ∈ Finset.range K, f m = ∑ m ∈ Finset.range L, f m := by
  have h (J : ℕ) (hJ : ∀ m, J ≤ m → f m = 0) :
      ∑ᶠ m, f m = ∑ m ∈ Finset.range J, f m := by
    apply finsum_eq_sum_of_support_subset
    intro m hm
    simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at *
    by_contra hn
    exact hm (hJ m (by omega))
  exact (h K hK).symm.trans (h L hL)

/-- The actual relation tensor is independent of any valid tail cutoff. -/
theorem relationLeft_cutoff (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) (a : V) (x : M₁) (y : M₂) {K L : ℕ}
    (hK : TailBound A B a x y K) (hL : TailBound A B a x y L) :
    relationLeft A B c a x y K = relationLeft A B c a x y L := by
  unfold relationLeft
  congr 1
  · congr 1
    apply sum_range_eq_of_tails
    · intro m hm
      rw [(hK (2 * (m + 1)) (by omega)).1]
      simp
    · intro m hm
      rw [(hL (2 * (m + 1)) (by omega)).1]
      simp
  · apply sum_range_eq_of_tails
    · intro m hm
      rw [(hK m (by omega)).2]
      simp
    · intro m hm
      rw [(hL m (by omega)).2]
      simp

theorem relationRight_cutoff (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) (a : V) (x : M₁) (y : M₂) {K L : ℕ}
    (hK : TailBound A B a x y K) (hL : TailBound A B a x y L) :
    relationRight A B c a x y K = relationRight A B c a x y L := by
  unfold relationRight
  congr 1
  · congr 1
    apply sum_range_eq_of_tails
    · intro m hm
      rw [(hK (2 * (m + 1)) (by omega)).2]
      simp
    · intro m hm
      rw [(hL (2 * (m + 1)) (by omega)).2]
      simp
  · apply sum_range_eq_of_tails
    · intro m hm
      rw [(hK m (by omega)).1]
      simp
    · intro m hm
      rw [(hL m (by omega)).1]
      simp

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [Module R F]
  [IsScalarTower ℂ R F]

/-- Canonical R-linear extension of a bilinear trace. This construction alone
does not say that the trace annihilates the relation module. -/
def tensorTrace (S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] F) : Tensor R M₁ M₂ →ₗ[R] F :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton R _ (TensorProduct.lift S))

@[simp] theorem tensorTrace_pair (S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] F) (x : M₁) (y : M₂) :
    tensorTrace (R := R) S (pair (R := R) x y) = S x y := by
  simp [tensorTrace, pair]

/-- The left collected minus-two Ward identity, at one valid cutoff per
insertion triple. For the geometric trace the coefficients must be the actual
Eisenstein and oriented Weierstrass kernels. -/
def CollectedLeftWard (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) (S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] F) : Prop :=
  ∀ a x y, ∃ K, TailBound A B a x y K ∧
    S (mode (A.YM a) (-2) x) y +
      (∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : R) * c.G k) •
        S (mode (A.YM a) (2 * (k + 1)) x) y) +
      (∑ m ∈ Finset.range K, ((-1 : R) ^ m * (m + 1) * c.Pleft m) •
        S x (mode (B.YM a) m y)) = 0

/-- The opposite orientation is a separate obligation. -/
def CollectedRightWard (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) (S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] F) : Prop :=
  ∀ a x y, ∃ K, TailBound A B a x y K ∧
    S x (mode (B.YM a) (-2) y) +
      (∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : R) * c.G k) •
        S x (mode (B.YM a) (2 * (k + 1)) y)) +
      (∑ m ∈ Finset.range K, ((-1 : R) ^ m * (m + 1) * c.Pright m) •
        S (mode (A.YM a) m x) y) = 0

/-- The two collected identities imply exactly the pre-existing TraceDescent,
including every generator and every allowed cutoff of the relation submodule. -/
theorem traceDescent_of_collected (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) (S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] F)
    (hL : CollectedLeftWard A B c S) (hR : CollectedRightWard A B c S) :
    TraceDescent A B c (tensorTrace S) := by
  apply Submodule.span_le.mpr
  rintro t ⟨a, x, y, K, hK, ht | ht⟩
  · obtain ⟨L, htail, h⟩ := hL a x y
    change tensorTrace S t = 0
    rw [ht, relationLeft_cutoff A B c a x y hK htail]
    simpa only [relationLeft, map_add, map_sum, map_smul, tensorTrace_pair] using h
  · obtain ⟨L, htail, h⟩ := hR a x y
    change tensorTrace S t = 0
    rw [ht, relationRight_cutoff A B c a x y hK htail]
    simpa only [relationRight, map_add, map_sum, map_smul, tensorTrace_pair] using h

/-- No relation was lost in the collected formulation. -/
theorem traceDescent_iff_collected (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) (S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] F) :
    TraceDescent A B c (tensorTrace S) ↔
      CollectedLeftWard A B c S ∧ CollectedRightWard A B c S := by
  constructor
  · intro h
    constructor
    · intro a x y
      obtain ⟨K, hK⟩ := exists_tailBound A B a x y
      refine ⟨K, hK, ?_⟩
      have he := h (Submodule.subset_span ⟨a, x, y, K, hK, Or.inl rfl⟩)
      simpa only [LinearMap.mem_ker, relationLeft, map_add, map_sum, map_smul,
        tensorTrace_pair] using he
    · intro a x y
      obtain ⟨K, hK⟩ := exists_tailBound A B a x y
      refine ⟨K, hK, ?_⟩
      have he := h (Submodule.subset_span ⟨a, x, y, K, hK, Or.inr rfl⟩)
      simpa only [LinearMap.mem_ker, relationRight, map_add, map_sum, map_smul,
        tensorTrace_pair] using he
  · rintro ⟨hL, hR⟩
    exact traceDescent_of_collected A B c S hL hR

/-- Direct consumer with the original uniform q-equation quantifiers. The
actual collected Ward laws and orbit compatibility have not been discharged. -/
theorem exists_uniform_qEquation_of_collected [IsNoetherianRing R]
    (A : AdmissibleModule W M₁) (B : AdmissibleModule W M₂)
    (hA : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hB : FusionC2.ModuleC2Cofinite B.toWeakModule)
    (c : Kernels R) (t : ℕ → Tensor R M₁ M₂) :
    ∃ (m : ℕ) (a : ℕ → R), 0 < m ∧
      ∀ S : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] F,
        CollectedLeftWard A.toWeakModule B.toWeakModule c S →
        CollectedRightWard A.toWeakModule B.toWeakModule c S →
        ∀ D : ℕ → F → F, QOrbitCompatibility (tensorTrace S) t D →
          qIterate D (tensorTrace S (t 0)) m =
            ∑ k ∈ Finset.range m, a k • qIterate D (tensorTrace S (t 0)) k := by
  obtain ⟨m, a, hm, h⟩ := exists_uniform_qEquation A B hA hB c t
  exact ⟨m, a, hm, fun S hL hR D hD =>
    h (tensorTrace S) (traceDescent_of_collected _ _ c S hL hR) D hD⟩

end VOA.Huang.GenusTwoPoint.Separate
