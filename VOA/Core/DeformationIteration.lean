/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationReconstruction

/-!
# Iteration and product closure in the first-order extension

The iterate slice of Jacobi expresses the mode of a product state in terms of
compositions of the two original fields. We establish this identity on V × V,
including the correction in the acting state. It makes the states whose modes
preserve a subspace closed under their own products. This is the step that lets
current-mode closure propagate to states obtained by repeated current actions.
-/
noncomputable section
namespace VOA.Deform.Reconstruction
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V} (D : FirstOrderDeformation W)

/-- The nth first-order product is additive in its acting state. -/
theorem product_add_left (a b x : V × V) (n : ℤ) :
    product D (a + b) n x = product D a n x + product D b n x := by
  apply Prod.ext <;> simp [product] <;> abel

/-- A scalar in the acting state factors out of its first-order product. -/
theorem product_smul_left (c : ℂ) (a x : V × V) (n : ℤ) :
    product D (c • a) n x = c • product D a n x := by
  apply Prod.ext <;> simp [product, smul_add]

/-- The zero state acts by zero in the extension. -/
theorem product_zero_left (x : V × V) (n : ℤ) : product D 0 n x = 0 := by
  simp [product]

/-- First-order products are additive in the state on which they act. -/
theorem product_add_right (a x y : V × V) (n : ℤ) :
    product D a n (x + y) = product D a n x + product D a n y := by
  apply Prod.ext <;> simp [product] <;> abel

/-- Scaling the target scales the first-order product. -/
theorem product_smul_right (c : ℂ) (a x : V × V) (n : ℤ) :
    product D a n (c • x) = c • product D a n x := by
  apply Prod.ext <;> simp [product, smul_add]

/-- Every first-order mode sends the zero target to zero. -/
theorem product_zero_right (a : V × V) (n : ℤ) : product D a n 0 = 0 := by
  simp [product]

/-- The pure vacuum acts as the identity in mode −1 and by zero in all other modes. -/
theorem product_vacuum (x : V × V) (n : ℤ) :
    product D (W.vacuum, 0) n x = if n = -1 then x else 0 := by
  by_cases h : n = -1 <;> apply Prod.ext <;>
    simp [product, PreVertexAlgebra.smul_vacuum_left, h]

/-- Truncation of ordinary and correction fields gives truncation of the full
first-order product, even when both inputs have nonzero tangent coordinates. -/
theorem product_eventually_zero (a x : V × V) :
    ∃ N : ℤ, ∀ n, N ≤ n → product D a n x = 0 := by
  obtain ⟨N0, h0⟩ := W.toPreVertexAlgebra.smul_eventually_zero a.1 x.1
  obtain ⟨N1, h1⟩ := W.toPreVertexAlgebra.smul_eventually_zero a.1 x.2
  obtain ⟨N2, h2⟩ := W.toPreVertexAlgebra.smul_eventually_zero a.2 x.1
  obtain ⟨N3, h3⟩ := D.smul₁_eventually_zero a.1 x.1
  refine ⟨max (max N0 N1) (max N2 N3), fun n hn => ?_⟩
  simp [product, h0 n (by omega), h1 n (by omega), h2 n (by omega), h3 n (by omega)]

/-- One summand in the integer-index iterate formula for the original VOA. -/
private def ordinaryTerm (a b x : V) (ℓ n i : ℤ) : V :=
  (negOnePow i * cbz ℓ i) • (W.smul a (ℓ - i) (W.smul b (n + i) x) -
    negOnePow ℓ • W.smul b (ℓ + n - i) (W.smul a i x))

/-- The ordinary iterate sum has genuinely finite support: negative indices have
zero binomial coefficient and sufficiently positive modes annihilate the target. -/
private theorem ordinaryTerm_finite (a b x : V) (ℓ n : ℤ) :
    Function.HasFiniteSupport (ordinaryTerm (W := W) a b x ℓ n) := by
  obtain ⟨N0, h0⟩ := W.toPreVertexAlgebra.smul_eventually_zero b x
  obtain ⟨N1, h1⟩ := W.toPreVertexAlgebra.smul_eventually_zero a x
  refine (Set.finite_Icc 0 (max (N0 - n) N1)).subset ?_
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp [ordinaryTerm, cbz_apply_neg ℓ h]
  · simp [ordinaryTerm, h0 (n + i) (by omega), h1 i (by omega)]

/-- The ordinary iterate identity is the m=0 slice of Jacobi. -/
private theorem ordinaryTerm_sum (a b x : V) (ℓ n : ℤ) :
    (∑ᶠ i, ordinaryTerm (W := W) a b x ℓ n i) = W.smul (W.smul a ℓ b) n x := by
  have h := W.jacobi a b x ℓ 0 n
  conv_rhs at h =>
    rw [finsum_eq_single _ (0 : ℤ)
      (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
  simpa [ordinaryTerm, cbz_zero_left] using h

/-- One summand in the correction to the iterate formula, with exactly one
correction field in each composition. -/
private def correctionTerm (a b x : V) (ℓ n i : ℤ) : V :=
  (negOnePow i * cbz ℓ i) •
    (D.smul₁ a (ℓ - i) (W.smul b (n + i) x) +
      W.smul a (ℓ - i) (D.smul₁ b (n + i) x) - negOnePow ℓ •
      (D.smul₁ b (ℓ + n - i) (W.smul a i x) +
        W.smul b (ℓ + n - i) (D.smul₁ a i x)))

/-- The correction iterate sum is finite by the previously verified Jacobi bounds. -/
private theorem correctionTerm_finite (a b x : V) (ℓ n : ℤ) :
    Function.HasFiniteSupport (correctionTerm D a b x ℓ n) := by
  unfold correctionTerm
  simpa only [add_zero, zero_add] using D.jacobiLHS_support_finite a b x ℓ 0 n

/-- Differentiating the iterate identity corrects both the acting product state
and the field attached to its ordinary value. Both terms are essential. -/
private theorem correctionTerm_sum (a b x : V) (ℓ n : ℤ) :
    (∑ᶠ i, correctionTerm D a b x ℓ n i) =
      W.smul (D.smul₁ a ℓ b) n x + D.smul₁ (W.smul a ℓ b) n x := by
  have h := D.borcherds₁ a b x ℓ 0 n
  conv_rhs at h =>
    rw [finsum_eq_single _ (0 : ℤ)
      (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
  simpa [correctionTerm, cbz_zero_left] using h

/-- A summand in the full first-order iterate identity on pairs. -/
def iterateTerm (a b x : V × V) (ℓ n i : ℤ) : V × V :=
  (negOnePow i * cbz ℓ i) • (product D a (ℓ - i) (product D b (n + i) x) -
    negOnePow ℓ • product D b (ℓ + n - i) (product D a i x))

/-- The pair-valued iterate sum is finite by truncation of the pair products. -/
theorem iterateTerm_finite (a b x : V × V) (ℓ n : ℤ) :
    Function.HasFiniteSupport (iterateTerm D a b x ℓ n) := by
  obtain ⟨N0, h0⟩ := product_eventually_zero D b x
  obtain ⟨N1, h1⟩ := product_eventually_zero D a x
  refine (Set.finite_Icc 0 (max (N0 - n) N1)).subset ?_
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp [iterateTerm, cbz_apply_neg ℓ h]
  · simp [iterateTerm, h0 (n + i) (by omega), h1 i (by omega), product_zero_right]

/-- Modes of product states are sums of compositions of the original modes,
with all constant and first-order contributions retained. -/
theorem product_iterate (a b x : V × V) (ℓ n : ℤ) :
    product D (product D a ℓ b) n x = ∑ᶠ i, iterateTerm D a b x ℓ n i := by
  have hf := iterateTerm_finite D a b x ℓ n
  apply Prod.ext
  · change _ = (LinearMap.fst ℂ V V).toAddMonoidHom _
    rw [(LinearMap.fst ℂ V V).toAddMonoidHom.map_finsum hf]
    exact (ordinaryTerm_sum a.1 b.1 x.1 ℓ n).symm
  · change _ = (LinearMap.snd ℂ V V).toAddMonoidHom _
    rw [(LinearMap.snd ℂ V V).toAddMonoidHom.map_finsum hf]
    have hexp : (fun i => (iterateTerm D a b x ℓ n i).2) =
        (fun i => ordinaryTerm (W := W) a.1 b.1 x.2 ℓ n i +
          ordinaryTerm (W := W) a.1 b.2 x.1 ℓ n i +
          ordinaryTerm (W := W) a.2 b.1 x.1 ℓ n i + correctionTerm D a.1 b.1 x.1 ℓ n i) := by
      funext i
      dsimp [iterateTerm, product, ordinaryTerm, correctionTerm]
      simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right]
      module
    change (product D (product D a ℓ b) n x).2 = ∑ᶠ i, (iterateTerm D a b x ℓ n i).2
    rw [hexp, finsum_add_distrib (f := fun i =>
      ordinaryTerm (W := W) a.1 b.1 x.2 ℓ n i +
      ordinaryTerm (W := W) a.1 b.2 x.1 ℓ n i + ordinaryTerm (W := W) a.2 b.1 x.1 ℓ n i)
      (((ordinaryTerm_finite a.1 b.1 x.2 ℓ n).add (ordinaryTerm_finite a.1 b.2 x.1 ℓ n)).add
        (ordinaryTerm_finite a.2 b.1 x.1 ℓ n)) (correctionTerm_finite D a.1 b.1 x.1 ℓ n),
      finsum_add_distrib (f := fun i => ordinaryTerm (W := W) a.1 b.1 x.2 ℓ n i +
        ordinaryTerm (W := W) a.1 b.2 x.1 ℓ n i)
        ((ordinaryTerm_finite a.1 b.1 x.2 ℓ n).add (ordinaryTerm_finite a.1 b.2 x.1 ℓ n))
        (ordinaryTerm_finite a.2 b.1 x.1 ℓ n),
      finsum_add_distrib (ordinaryTerm_finite a.1 b.1 x.2 ℓ n)
        (ordinaryTerm_finite a.1 b.2 x.1 ℓ n),
      ordinaryTerm_sum, ordinaryTerm_sum, ordinaryTerm_sum, correctionTerm_sum]
    simp only [product, PreVertexAlgebra.smul_add_left]
    abel

/-- States all of whose first-order modes preserve a chosen subspace. Linearity
of the field assignment makes this set a linear subspace itself. -/
def modePreservers (S : Submodule ℂ (V × V)) : Submodule ℂ (V × V) where
  carrier := {a | ∀ x ∈ S, ∀ n, product D a n x ∈ S}
  zero_mem' := by intro x hx n; rw [product_zero_left]; exact S.zero_mem
  add_mem' := by
    intro a b ha hb x hx n
    rw [product_add_left]
    exact S.add_mem (ha x hx n) (hb x hx n)
  smul_mem' := by
    intro c a ha x hx n
    rw [product_smul_left]
    exact S.smul_mem c (ha x hx n)

/-- The iterate formula closes mode-preserving states under all products.
Each summand is a composition of operators already known to preserve the subspace. -/
theorem modePreservers_product (S : Submodule ℂ (V × V)) {a b : V × V}
    (ha : a ∈ modePreservers D S) (hb : b ∈ modePreservers D S) (ℓ : ℤ) :
    product D a ℓ b ∈ modePreservers D S := by
  intro x hx n
  rw [product_iterate]
  classical
  rw [finsum_eq_sum _ (iterateTerm_finite D a b x ℓ n)]
  apply S.sum_mem
  intro i _
  exact S.smul_mem _ (S.sub_mem (ha _ (hb x hx _) _) (S.smul_mem _ (hb _ (ha x hx _) _)))

/-- The pure vacuum preserves every linear subspace. -/
theorem vacuum_mem_modePreservers (S : Submodule ℂ (V × V)) :
    (W.vacuum, 0) ∈ modePreservers D S := by
  intro x hx n
  rw [product_vacuum]
  split_ifs
  · exact hx
  · exact S.zero_mem

end VOA.Deform.Reconstruction
