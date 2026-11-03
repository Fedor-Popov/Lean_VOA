import VOA.Huang.AssocConverseModeAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Formal independence of nonisomorphic intermediate channels

The simultaneous coefficient span is stable under all modes. Its isotypic
projections therefore remain in the span, even for coincident weight classes.
-/

namespace VOA.Huang.AssocConverse
open VOA VOA.Huang.AssocTarget
open scoped BigOperators TensorProduct
universe u v w
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {ι : Type v}
  {P₁ P₂ P₃ P₄ : LWModule W}

def familyCoefficientVector (R : ι → LWModule W) {κ : ι → Type w}
    (B : ∀ j, κ j → IntertwiningOperator P₂.isMod P₃.isMod (R j).isMod)
    (n : ℂ) (x : P₂.carrier) (y : P₃.carrier) : ∀ j, κ j → (R j).carrier :=
  fun j k => (B j k).val n x y

noncomputable def familyCoefficientSpan (R : ι → LWModule W) {κ : ι → Type w}
    (B : ∀ j, κ j → IntertwiningOperator P₂.isMod P₃.isMod (R j).isMod) :
    Submodule ℂ (∀ j, κ j → (R j).carrier) :=
  Submodule.span ℂ {z | ∃ n x y, z = familyCoefficientVector R B n x y}

theorem familyCoefficientVector_mem (R : ι → LWModule W) {κ : ι → Type w}
    (B : ∀ j, κ j → IntertwiningOperator P₂.isMod P₃.isMod (R j).isMod)
    (n : ℂ) (x : P₂.carrier) (y : P₃.carrier) :
    familyCoefficientVector R B n x y ∈ familyCoefficientSpan R B :=
  Submodule.subset_span ⟨n, x, y, rfl⟩

theorem familyCoefficientSpan_mode_stable (R : ι → LWModule W) {κ : ι → Type w}
    (B : ∀ j, κ j → IntertwiningOperator P₂.isMod P₃.isMod (R j).isMod)
    (a : 𝒱) (m : ℤ) {z : ∀ j, κ j → (R j).carrier}
    (hz : z ∈ familyCoefficientSpan R B) :
    (fun j k => mode ((R j).isMod.YM a) m (z j k)) ∈ familyCoefficientSpan R B := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, x, y, rfl⟩ := hz
    have he : (fun j k => mode ((R j).isMod.YM a) m (familyCoefficientVector R B n x y j k)) =
        familyCoefficientVector R B n x (mode (P₃.isMod.YM a) m y) +
          ∑ᶠ k : ℤ, cbz m k •
            familyCoefficientVector R B (m + n - k) (mode (P₂.isMod.YM a) k x) y := by
      obtain ⟨N, hN⟩ := P₂.isMod.truncation a x
      have hs : (Function.support fun k : ℤ => cbz m k •
          familyCoefficientVector R B (m + n - k) (mode (P₂.isMod.YM a) k x) y).Finite := by
        apply (Set.finite_Ico 0 N).subset
        intro k hk
        by_contra h
        apply hk
        change cbz m k • familyCoefficientVector R B (m + n - k)
          (mode (P₂.isMod.YM a) k x) y = 0
        by_cases hk0 : k < 0
        · simp [cbz_apply_neg m hk0]
        · have hkN : N ≤ k := by simp only [Set.mem_Ico] at h; omega
          rw [hN k hkN]
          have hz : familyCoefficientVector R B (m + n - k) 0 y = 0 := by
            funext j b
            exact congrArg (fun g : P₃.carrier →ₗ[ℂ] (R j).carrier => g y)
              ((B j b).val (m + n - k)).map_zero
          rw [hz, smul_zero]
      funext j b
      have hj := (B j b).property.commutator a x y m n
      have hm := map_finsum
        ((LinearMap.proj b : (κ j → (R j).carrier) →ₗ[ℂ] (R j).carrier).comp
          (LinearMap.proj j)) hs
      simp only [Pi.add_apply]
      rw [show (∑ᶠ k : ℤ, cbz m k •
          familyCoefficientVector R B (m + n - k) (mode (P₂.isMod.YM a) k x) y) j b =
          ∑ᶠ k : ℤ, cbz m k • (B j b).val (m + n - k)
            (mode (P₂.isMod.YM a) k x) y from hm]
      exact (sub_eq_iff_eq_add.mp hj).trans (add_comm _ _)
    rw [he]
    exact (familyCoefficientSpan R B).add_mem (familyCoefficientVector_mem R B _ _ _)
      (VOA.Huang.BottomRecovery.finsum_mem_submodule _ _ fun k =>
        (familyCoefficientSpan R B).smul_mem _ (familyCoefficientVector_mem R B _ _ _))
  | zero => simpa only [Pi.zero_apply, map_zero] using (familyCoefficientSpan R B).zero_mem
  | add x y _ _ hx hy => simpa using (familyCoefficientSpan R B).add_mem hx hy
  | smul c x _ hx => simpa using (familyCoefficientSpan R B).smul_mem c hx

/-- A finite relation among formal products separates by the isomorphism class
of the intermediate module, independently of all conformal weights. -/
theorem coefficient_products_separate [Fintype ι]
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW)
    (hne : ∀ i j, LWModule.Iso W (R i) (R j) → i = j)
    (κ : ι → Type w) [∀ j, Fintype (κ j)]
    (A : ∀ j, κ j → IntertwiningOperator P₁.isMod (R j).isMod P₄.isMod)
    (B : ∀ j, κ j → IntertwiningOperator P₂.isMod P₃.isMod (R j).isMod)
    (hzero : ∀ p n x y z, ∑ j, ∑ k, (A j k).val p x ((B j k).val n y z) = 0) :
    ∀ j p n x y z, ∑ k, (A j k).val p x ((B j k).val n y z) = 0 := by
  classical
  intro j p n x y z
  let L : (∀ j, κ j → (R j).carrier) →ₗ[ℂ] P₄.carrier :=
    ∑ j, ∑ k, ((A j k).val p x).comp
      ((LinearMap.proj k : (κ j → (R j).carrier) →ₗ[ℂ] (R j).carrier).comp
      (LinearMap.proj j : (∀ j, κ j → (R j).carrier) →ₗ[ℂ] 
        (κ j → (R j).carrier)))
  have hL : familyCoefficientSpan R B ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, y, w, rfl⟩
    change L (familyCoefficientVector R B n y w) = 0
    simpa [L, familyCoefficientVector] using hzero p n x y w
  have hmem := single_mem_of_mode_stable R iR hne κ (familyCoefficientSpan R B)
    (fun a m _ hz => familyCoefficientSpan_mode_stable R B a m hz)
    (familyCoefficientVector_mem R B n y z) j
  have he := hL hmem
  change L (Pi.single j (familyCoefficientVector R B n y z j)) = 0 at he
  simp only [L, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply] at he
  change (∑ i, ∑ k, (A i k).val p x
    ((Pi.single j (familyCoefficientVector R B n y z j) :
      ∀ i, κ i → (R i).carrier) i k)) = 0 at he
  rw [Finset.sum_eq_single j] at he
  · simpa only [Pi.single_eq_same, familyCoefficientVector] using he
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi]
    simp
  · simp

/-- The original formal residual is discharged for every finite irredundant
family of irreducibles. Completeness and strong rationality are unnecessary. -/
theorem formalChannelSeparation_of_irredundant [Fintype ι]
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW)
    (hne : ∀ i j, LWModule.Iso W (R i) (R j) → i = j) : FormalChannelSeparation R := by
  classical
  intro P₁ P₂ P₃ P₄ _ _ _ _ t ht
  have hrep (j : ι) := TensorProduct.exists_sum_tmul_eq (t j)
  choose n A B hrep using hrep
  have he (j : ι) : formalProductTensorMap P₁ P₂ P₃ P₄ (R j) (t j) =
      ∑ k, formalProductTensorMap P₁ P₂ P₃ P₄ (R j) (A j k ⊗ₜ[ℂ] B j k) := by
    rw [hrep j, map_sum]
  have hz : ∀ p q x y z, ∑ j, ∑ k, (A j k).val p x ((B j k).val q y z) = 0 := by
    intro p q x y z
    have hh := congrFun ht (p, q, x, y, z)
    change (∑ j, formalProductTensorMap P₁ P₂ P₃ P₄ (R j) (t j)) (p, q, x, y, z) = 0 at hh
    simpa only [he, Finset.sum_apply, formalProductTensorMap_tmul] using hh
  have hs := coefficient_products_separate R iR hne (fun j => Fin (n j)) A B hz
  intro j
  funext d
  rw [he, Finset.sum_apply]
  exact hs j d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2

/-- After algebraic separation, analytic coefficient uniqueness is the only
remaining faithfulness input. -/
theorem productChannelFaithful_of_coefficient_uniqueness [Fintype ι]
    (hV : StronglyRational W) (R : ι → LWModule W)
    (iR : ∀ j, (R j).IsIrreducibleLW)
    (hne : ∀ i j, LWModule.Iso W (R i) (R j) → i = j)
    (hcoeff : ProductCoefficientUniqueness hV R) : ProductChannelFaithful hV R :=
  productChannelFaithful_of_coefficient_separation hV R iR hcoeff
    (formalChannelSeparation_of_irredundant R iR hne)

theorem associativityBoth_of_coefficient_uniqueness [Fintype ι]
    (hV : StronglyRational W) (R : ι → LWModule W)
    (hR : CompleteIrredundantFamily R) (hcoeff : ProductCoefficientUniqueness hV R) :
    AssociativityBoth W :=
  associativityBoth_of_coefficient_separation hV R hR hcoeff
    (formalChannelSeparation_of_irredundant R hR.1 hR.2.2)

end VOA.Huang.AssocConverse
