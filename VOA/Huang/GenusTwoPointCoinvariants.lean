import VOA.Huang.GenusTwoPointC2Reduction
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The two-insertion genus-one relation quotient

This is the algebraic quotient in Huang, math/0303049, Section 3, with its
Eisenstein and Weierstrass coefficients left as parameters in a complex
algebra R. The two full minus-two relations are imposed on the actual tensor
product of insertion modules. C₂-cofiniteness proves finite generation.
Identifying the parameters with elliptic functions and proving that actual
geometrically modified traces kill these relations remain separate steps.
-/
namespace VOA.Huang.GenusTwoPoint.QEquation
open VOA VOA.Huang.FusionC2
open scoped BigOperators TensorProduct
universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}
  {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Scalar extension of the two insertion modules. -/
abbrev Tensor (R : Type*) [CommRing R] [Algebra ℂ R]
    (M₁ M₂ : Type u) [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] := R ⊗[ℂ] (M₁ ⊗[ℂ] M₂)

/-- The canonical bilinear insertion map. -/
noncomputable def pair : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] Tensor R M₁ M₂ :=
  (TensorProduct.mk ℂ M₁ M₂).compr₂ (TensorProduct.mk ℂ R (M₁ ⊗[ℂ] M₂) 1)

/-- G(k) stands for G_(2k+4); Pleft(m), Pright(m) for the two orientations
of wp_(m+2). No analytic or elliptic identity is assumed by this data type. -/
structure Kernels (R : Type*) where
  G : ℕ → R
  Pleft : ℕ → R
  Pright : ℕ → R

/-- A common finite cutoff for the two module-mode tails. -/
def TailBound (A : WeakModule W M₁) (B : WeakModule W M₂)
    (a : V) (x : M₁) (y : M₂) (K : ℕ) : Prop :=
  ∀ m : ℤ, K ≤ m → mode (A.YM a) m x = 0 ∧ mode (B.YM a) m y = 0

theorem exists_tailBound (A : WeakModule W M₁) (B : WeakModule W M₂)
    (a : V) (x : M₁) (y : M₂) : ∃ K, TailBound A B a x y K := by
  obtain ⟨i, hi⟩ := A.truncation a x
  obtain ⟨j, hj⟩ := B.truncation a y
  exact ⟨(max i j).toNat, fun m hm => ⟨hi m (by omega), hj m (by omega)⟩⟩

noncomputable def relationLeft (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) (a : V) (x : M₁) (y : M₂) (K : ℕ) : Tensor R M₁ M₂ :=
  pair (R := R) (mode (A.YM a) (-2) x) y +
    (∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : R) * c.G k) •
      pair (R := R) (mode (A.YM a) (2 * (k + 1)) x) y) +
    (∑ m ∈ Finset.range K, ((-1 : R) ^ m * (m + 1) * c.Pleft m) •
      pair (R := R) x (mode (B.YM a) m y))

noncomputable def relationRight (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) (a : V) (x : M₁) (y : M₂) (K : ℕ) : Tensor R M₁ M₂ :=
  pair (R := R) x (mode (B.YM a) (-2) y) +
    (∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : R) * c.G k) •
      pair (R := R) x (mode (B.YM a) (2 * (k + 1)) y)) +
    (∑ m ∈ Finset.range K, ((-1 : R) ^ m * (m + 1) * c.Pright m) •
      pair (R := R) (mode (A.YM a) m x) y)

/-- Both insertion relations, using only cutoffs beyond the actual tails. -/
noncomputable def relations (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) : Submodule R (Tensor R M₁ M₂) :=
  Submodule.span R {t | ∃ a x y K, TailBound A B a x y K ∧
    (t = relationLeft A B c a x y K ∨ t = relationRight A B c a x y K)}

/-- Universal two-insertion values in the relation quotient. -/
noncomputable def quotientPair (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] (Tensor R M₁ M₂ ⧸ relations A B c) :=
  (pair (R := R)).compr₂ ((relations A B c).mkQ.restrictScalars ℂ)

private theorem rearrange {F : Type*} [AddCommGroup F] {a b c : F}
    (h : a + b + c = 0) : a = -b - c := by
  apply eq_sub_iff_add_eq.mpr
  apply eq_neg_of_add_eq_zero_left
  rwa [add_right_comm]

/-- The concrete relation quotient satisfies the two-slot reduction. -/
theorem quotientPair_C2Reduction (A : WeakModule W M₁) (B : WeakModule W M₂)
    (c : Kernels R) : C2Reduction (R := R) A B (quotientPair A B c) := by
  classical
  let J := relations A B c
  let S := quotientPair A B c
  constructor
  · intro a x y
    obtain ⟨K, hK⟩ := exists_tailBound A B a x y
    have hj : relationLeft A B c a x y K ∈ J :=
      Submodule.subset_span ⟨a, x, y, K, hK, Or.inl rfl⟩
    have he := (Submodule.Quotient.mk_eq_zero J).mpr hj
    change J.mkQ (relationLeft A B c a x y K) = 0 at he
    simp only [relationLeft, map_add, map_sum, map_smul] at he
    have heq : S (mode (A.YM a) (-2) x) y =
        -(∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : R) * c.G k) •
          S (mode (A.YM a) (2 * (k + 1)) x) y) -
        ∑ m ∈ Finset.range K, ((-1 : R)^m * (m + 1) * c.Pleft m) •
          S x (mode (B.YM a) m y) := by
      exact rearrange he
    change S _ _ ∈ lowerSpan (R := R) A B S a x y
    rw [heq]
    unfold lowerSpan
    apply Submodule.sub_mem
    · apply Submodule.neg_mem
      apply Submodule.sum_mem
      intro k hk
      apply Submodule.smul_mem
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨2 * (k + 1), by push_cast; rfl⟩)
    · apply Submodule.sum_mem
      intro m hm
      apply Submodule.smul_mem
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨m, rfl⟩)
  · intro a x y
    obtain ⟨K, hK⟩ := exists_tailBound A B a x y
    have hj : relationRight A B c a x y K ∈ J :=
      Submodule.subset_span ⟨a, x, y, K, hK, Or.inr rfl⟩
    have he := (Submodule.Quotient.mk_eq_zero J).mpr hj
    change J.mkQ (relationRight A B c a x y K) = 0 at he
    simp only [relationRight, map_add, map_sum, map_smul] at he
    have heq : S x (mode (B.YM a) (-2) y) =
        -(∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : R) * c.G k) •
          S x (mode (B.YM a) (2 * (k + 1)) y)) -
        ∑ m ∈ Finset.range K, ((-1 : R)^m * (m + 1) * c.Pright m) •
          S (mode (A.YM a) m x) y := by
      exact rearrange he
    change S _ _ ∈ lowerSpan (R := R) A B S a x y
    rw [heq]
    unfold lowerSpan
    apply Submodule.sub_mem
    · apply Submodule.neg_mem
      apply Submodule.sum_mem
      intro k hk
      apply Submodule.smul_mem
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨2 * (k + 1), by push_cast; rfl⟩)
    · apply Submodule.sum_mem
      intro m hm
      apply Submodule.smul_mem
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨m, rfl⟩)

/-- The C₂-cofinite two-insertion quotient is finite over its coefficient ring.
Neither a trace identity nor a differential equation is assumed here. -/
theorem finite_coinvariants (A : AdmissibleModule W M₁) (B : AdmissibleModule W M₂)
    (hA : ModuleC2Cofinite A.toWeakModule) (hB : ModuleC2Cofinite B.toWeakModule)
    (c : Kernels R) : Module.Finite R
      (Tensor R M₁ M₂ ⧸ relations A.toWeakModule B.toWeakModule c) := by
  classical
  let J := relations A.toWeakModule B.toWeakModule c
  let S := quotientPair A.toWeakModule B.toWeakModule c
  obtain ⟨U, Z, hUZ⟩ := exists_generators_of_C2 (R := R)
    (E := Tensor R M₁ M₂ ⧸ J) A B hA hB
  let f : U × Z → Tensor R M₁ M₂ ⧸ J := fun k => S k.1.val k.2.val
  let T := Submodule.span R (Set.range f)
  have hpair : ∀ x y, S x y ∈ T := by
    intro x y
    obtain ⟨r, hr⟩ := hUZ S (quotientPair_C2Reduction _ _ c) x y
    rw [hr]
    exact T.sum_mem fun k _ => T.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  have htop : T = ⊤ := by
    apply top_unique
    intro z hz
    clear hz
    obtain ⟨t, rfl⟩ := J.mkQ_surjective z
    induction t using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using T.zero_mem
    | add x y hx hy => simpa only [map_add] using T.add_mem hx hy
    | tmul r v =>
      induction v using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]; exact T.zero_mem
      | add x y hx hy =>
        simpa only [TensorProduct.tmul_add, map_add] using T.add_mem hx hy
      | tmul x y =>
        have he : J.mkQ (r ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y)) = r • S x y := by
          change J.mkQ (r ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y)) =
            r • J.mkQ (1 ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y))
          rw [← J.mkQ.map_smul]
          simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [he]
        exact T.smul_mem r (hpair x y)
  exact ⟨htop ▸ Submodule.fg_span (Set.finite_range f)⟩

end VOA.Huang.GenusTwoPoint.QEquation
