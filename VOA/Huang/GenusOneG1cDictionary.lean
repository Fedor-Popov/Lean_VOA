import VOA.Huang.VerlindeTransportGenusZero
import VOA.Huang.TensorCatTransport
import VOA.Huang.GenusOneG1cOverlap
import VOA.Huang.GenusTwoPointVacuum

/-!
# The dictionary: categorical vacuum channel ↔ intertwining operators ↔ genus-one functions

Step (0) of the proof of (G1). `VerlindeTransport.TransferChoice` gives morphisms in the proved
category of ordinary modules: `ε : M_a ⊠ M_b → V`, `inc_j`, `proj_j` and the vacuum channel in
product form `ψ_x = α⁻¹ ≫ (ε ▷ M_x) ≫ λ` (`vacuumProduct`). By the universal property of the
chosen fusion products, every morphism out of `X ⊠ Y` IS an intertwining operator (postcompose with
the universal intertwiner). This file makes the correspondence explicit and proves the identities
that turn Huang's vacuum-channel function into a concrete genus-one function:

* `epsInt c` — Huang's `Y^e_{a a'}` (`= ε ∘ 𝒴_{ab}`), an intertwiner of type `(V / M_a M_b)`;
  `muInt c x j` — `μ_j = ((M_a ◁ inc_j) ≫ ψ_x) ∘ 𝒴`, type `(M_x / M_a M_{lab j})`;
  `nuInt c x j` — `ν_j = proj_j ∘ 𝒴`, type `(M_{lab j} / M_b M_x)`.
* `iterate_dictionary`: the iterate channel of the associator-transported vacuum channel
  `α ≫ ψ_x` is the represented iterate `Y_{M_x}(Y^e(·, z₀)·, z₂)` (module vertex operator of
  `M_x` after `Y^e`).
* `product_dictionary`: the product channel of `ψ_x` is `Σ_j μ_j(·, z₁) ν_j(·, z₂)`, by the split
  presentation `Σ_j proj_j ≫ inc_j = 𝟙`.
* `vacuum_fourPoint`: genus-zero associativity for THESE channels, from the defining four-point
  identity of the evaluation associator (`evalAssoc_fourPoint`):
  `⟨f, Y_{M_x}(Y^e(w_a, x) w_b, 1) w⟩ = Σ_j ⟨f, μ_j(w_a, 1 + x) ν_j(w_b, 1) w⟩`, `0 < x < 1`.
* `vacuum_coeff`: the same for every fixed-weight trace coefficient.
* `vacuumChannel_eq_product`: the genus-one vacuum-channel function
  `Ψ_x(z₀) = Tr_{M_x} Y_{M_x}(Y^e(w_a, z₀) w_b, 1) q^{L₀ − c/24}` (`iterF`) equals
  `Σ_j Tr_{M_x} μ_j(w_a, 1 + z₀) ν_j(w_b, 1) q^{L₀ − c/24}` (`prodF`) on the complex half-disc,
  both sides absolutely convergent.

So `Ψ_x` is a concrete genus-one function built from intertwiners, and its product decomposition
uses exactly the `inc_j`, `proj_j` of the `TransferChoice` that enter `bTransfer`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1c

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.FusionProduct VOA.Huang.FusionUnit
  VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion VOA.Huang.AssocTarget CategoryTheory
open VOA.Huang.GenusTwoPoint (IterateSewingSummable ProductSewingSummable productTerm
  iterateTerm productCoeff iterateCoeff qFactor vacuumLW weightFunctional
  supportedAt_weightFunctional iterateCoeff_eq_sum_iterValue productCoeff_eq_sum_prodValue)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- A morphism out of a fusion product is recovered from its intertwiner. -/
theorem lift_postcompose {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂]
    [Module ℂ M₂] {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} (P : Product A₁ A₂)
    {N : Type u} [AddCommGroup N] [Module ℂ N] (AN : OrdVModule W N) (f : homSpace P.isMod AN) :
    P.lift AN (postcompose P.intertwiner AN f) = f :=
  (P.universal N AN).1 (P.lift_spec AN _)

/-- Finite sums of intertwiners are evaluated modewise. -/
theorem intertwiner_sum_apply {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃] {A₁ : OrdVModule W M₁}
    {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {κ : Type*} (s : Finset κ)
    (I : κ → IntertwiningOperator A₁ A₂ A₃) (n : ℂ) (u : M₁) (v : M₂) :
    (∑ j ∈ s, I j).val n u v = ∑ j ∈ s, (I j).val n u v := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, ← ih]
    rfl

variable (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

/-! ## §1 The intertwiners of a `TransferChoice` -/

/-- **Huang's `Y^e_{a a'}`**: `ε` composed with the universal intertwiner of `M_a ⊠ M_b`. -/
def epsInt (c : TransferChoice F D a b) :
    IntertwiningOperator (lwOf D a).isMod (lwOf D b).isMod (adjointModule W) :=
  postcompose (F (famObj D a) (famObj D b)).intertwiner (adjointModule W) c.ε

/-- The morphism `μ_j = (M_a ◁ inc_j) ≫ ψ_x : M_a ⊠ M_{lab j} → M_x`. -/
def muHom (c : TransferChoice F D a b) (x : ι) (j : Fin (c.r x)) :
    tensorObj F (famObj D a) (famObj D (c.lab x j)) ⟶ famObj D x :=
  tensorHom F (𝟙 (famObj D a)) (c.inc x j) ≫ vacuumProduct F H c x

/-- The intertwiner `μ_j` of type `(M_x / M_a M_{lab j})`. -/
def muInt (c : TransferChoice F D a b) (x : ι) (j : Fin (c.r x)) :
    IntertwiningOperator (lwOf D a).isMod (lwOf D (c.lab x j)).isMod (lwOf D x).isMod :=
  postcompose (F (famObj D a) (famObj D (c.lab x j))).intertwiner (lwOf D x).isMod
    (muHom F H c x j)

/-- The intertwiner `ν_j = proj_j ∘ 𝒴` of type `(M_{lab j} / M_b M_x)`. -/
def nuInt (c : TransferChoice F D a b) (x : ι) (j : Fin (c.r x)) :
    IntertwiningOperator (lwOf D b).isMod (lwOf D x).isMod (lwOf D (c.lab x j)).isMod :=
  postcompose (F (famObj D b) (famObj D x)).intertwiner (lwOf D (c.lab x j)).isMod
    (c.proj x j)

theorem epsInt_apply (c : TransferChoice F D a b) (n : ℂ) (u : (lwOf D a).carrier)
    (v : (lwOf D b).carrier) :
    (epsInt F c).val n u v = c.ε.val ((F (famObj D a) (famObj D b)).intertwiner.val n u v) := rfl

theorem muInt_apply (c : TransferChoice F D a b) (x : ι) (j : Fin (c.r x)) (n : ℂ)
    (u : (lwOf D a).carrier) (v : (lwOf D (c.lab x j)).carrier) :
    (muInt F H c x j).val n u v = (vacuumProduct F H c x).val
      ((F (famObj D a) (tensorObj F (famObj D b) (famObj D x))).intertwiner.val n u
        ((c.inc x j).val v)) := by
  change (tensorHom F (𝟙 (famObj D a)) (c.inc x j) ≫ vacuumProduct F H c x).val _ = _
  rw [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply]

theorem nuInt_apply (c : TransferChoice F D a b) (x : ι) (j : Fin (c.r x)) (n : ℂ)
    (u : (lwOf D b).carrier) (v : (lwOf D x).carrier) :
    (nuInt F c x j).val n u v =
      (c.proj x j).val ((F (famObj D b) (famObj D x)).intertwiner.val n u v) :=
  rfl

/-! ## §2 Iterate and product channels -/

/-- The associator-transported vacuum channel is `α ≫ ψ_x = (ε ▷ M_x) ≫ λ`. -/
theorem assoc_vacuumProduct (c : TransferChoice F D a b) (x : ι) :
    (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ vacuumProduct F H c x =
      tensorHom F c.ε (𝟙 (famObj D x)) ≫ (leftUnitor F (famObj D x)).hom := by
  unfold vacuumProduct
  exact Iso.hom_inv_id_assoc _ _

/-- **Iterate dictionary.** The iterate channel of `α ≫ ψ_x` is the represented iterate
`Y_{M_x}(Y^e(·, z₀)·, z₂)`. -/
theorem iterate_dictionary (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b) (x : ι) :
    postcompose (F (tensorObj F (famObj D a) (famObj D b)) (famObj D x)).intertwiner
        (famObj D x).isMod
        ((evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ vacuumProduct F H c x) =
      representedIterate F (P₁ := lwOf D a) (P₂ := lwOf D b) (P₃ := lwOf D x)
        (P₄ := lwOf D x) (Q := vacuumLW W hv) (moduleIntertwiner (lwOf D x).isMod)
        (epsInt F c) := by
  rw [assoc_vacuumProduct]
  have hl : (F (famObj D a) (famObj D b)).lift (vacuumLW W hv).isMod (epsInt F c) = c.ε :=
    lift_postcompose (F (famObj D a) (famObj D b)) (adjointModule W) c.ε
  apply Subtype.ext
  funext n
  refine LinearMap.ext fun u => LinearMap.ext fun m => ?_
  change (tensorHom F c.ε (𝟙 (famObj D x)) ≫ (leftUnitor F (famObj D x)).hom).val
      ((F (tensorObj F (famObj D a) (famObj D b)) (famObj D x)).intertwiner.val n u m) =
    (moduleIntertwiner (lwOf D x).isMod).val n
      (((F (famObj D a) (famObj D b)).lift (vacuumLW W hv).isMod (epsInt F c)).val u) m
  rw [hl, Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply, leftUnitor_intertwiner]
  rfl

/-- **Product dictionary.** The product channel of `ψ_x` is `Σ_j μ_j(·, z₁) ν_j(·, z₂)`. -/
theorem product_dictionary (c : TransferChoice F D a b) (x : ι) :
    postcompose (F (famObj D a) (tensorObj F (famObj D b) (famObj D x))).intertwiner
        (famObj D x).isMod (vacuumProduct F H c x) =
      ∑ j, representedProduct F (P₁ := lwOf D a) (P₂ := lwOf D b) (P₃ := lwOf D x)
        (P₄ := lwOf D x) (Q := lwOf D (c.lab x j)) (muInt F H c x j) (nuInt F c x j) := by
  have hl : ∀ j, (F (famObj D b) (famObj D x)).lift (lwOf D (c.lab x j)).isMod
      (nuInt F c x j) = c.proj x j := fun j =>
    lift_postcompose (F (famObj D b) (famObj D x)) (lwOf D (c.lab x j)).isMod (c.proj x j)
  apply Subtype.ext
  funext n
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  change _ = (∑ j, representedProduct F (P₁ := lwOf D a) (P₂ := lwOf D b) (P₃ := lwOf D x)
        (P₄ := lwOf D x) (Q := lwOf D (c.lab x j)) (muInt F H c x j) (nuInt F c x j)).val n u v
  rw [intertwiner_sum_apply]
  have hterm : ∀ j, (representedProduct F (P₁ := lwOf D a) (P₂ := lwOf D b) (P₃ := lwOf D x)
      (P₄ := lwOf D x) (Q := lwOf D (c.lab x j)) (muInt F H c x j) (nuInt F c x j)).val n u v =
      (vacuumProduct F H c x).val
        ((F (famObj D a) (tensorObj F (famObj D b) (famObj D x))).intertwiner.val n u
          ((c.inc x j).val ((c.proj x j).val v))) := by
    intro j
    change (muInt F H c x j).val n u
      (((F (famObj D b) (famObj D x)).lift (lwOf D (c.lab x j)).isMod (nuInt F c x j)).val v) = _
    rw [hl j, muInt_apply]
    rfl
  simp only [hterm]
  have hsum : ∑ j, (c.inc x j).val ((c.proj x j).val v) = v := by
    have htot := congrArg (fun f => f.val v) (c.total x)
    simpa only [Ordinary.sum_val_apply, Ordinary.comp_apply, Ordinary.id_apply] using htot
  set Y := (F (famObj D a) (tensorObj F (famObj D b) (famObj D x))).intertwiner with hY
  calc _ = (vacuumProduct F H c x).val (Y.val n u v) := rfl
    _ = (vacuumProduct F H c x).val (Y.val n u (∑ j, (c.inc x j).val ((c.proj x j).val v))) := by
        rw [hsum]
    _ = _ := by rw [map_sum]; exact map_sum (vacuumProduct F H c x).val _ _

/-! ## §3 Genus-zero associativity for the categorical channels -/

/-- The iterate value is the library `iterValue` at `z₂ = 1`. -/
theorem iterateValue_eq_iterValue {P₁ P₂ P₃ P₄ Q : LWModule W}
    (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) (d : AssocConverse.TestData P₁ P₂ P₃ P₄) :
    AssocConverse.iterateValue A B d = iterValue A.val B.val d.f d.w₁ d.w₂ d.w₃
      (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2) (d.α₁ + d.α₂ - 1 - Q.h) (d.x : ℂ) 1 := rfl

/-- The product value is the library `prodValue` at `z₁ = 1 + x`, `z₂ = 1`. -/
theorem productValue_eq_prodValue {P₁ P₂ P₃ P₄ Q : LWModule W}
    (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod) (d : AssocConverse.TestData P₁ P₂ P₃ P₄) :
    AssocConverse.productValue A B d = prodValue A.val B.val d.f d.w₁ d.w₂ d.w₃
      (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2) (d.α₂ + d.α₃ - 1 - Q.h) (1 + (d.x : ℂ)) 1 := rfl

/-- **Genus-zero associativity of the vacuum channel**, read off the evaluation associator:
`⟨f, Y_{M_x}(Y^e(w_a, x) w_b, 1) w⟩ = Σ_j ⟨f, μ_j(w_a, 1 + x) ν_j(w_b, 1) w⟩`. -/
theorem vacuum_fourPoint (hV : StronglyRational W) (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b) (x : ι)
    (d : AssocConverse.TestData (lwOf D a) (lwOf D b) (lwOf D x) (lwOf D x)) :
    AssocConverse.iterateValue (Q := vacuumLW W hv) (moduleIntertwiner (lwOf D x).isMod)
        (epsInt F c) d =
      ∑ j, AssocConverse.productValue (Q := lwOf D (c.lab x j)) (muInt F H c x j)
        (nuInt F c x j) d := by
  have h4 := evalAssoc_fourPoint F H (famObj D a) (famObj D b) (famObj D x) (famObj D x)
    (vacuumProduct F H c x)
  have h := congrFun h4 (TensorCat.ordinaryTest d)
  rw [iterate_dictionary F H hv c x, product_dictionary F H c x] at h
  refine (representedIterate_evaluation F (Q := vacuumLW W hv) _ _ d).symm.trans (h.trans ?_)
  refine (productEvaluation_sum F (fun j => representedProduct F (P₁ := lwOf D a)
    (P₂ := lwOf D b) (P₃ := lwOf D x) (P₄ := lwOf D x) (Q := lwOf D (c.lab x j))
    (muInt F H c x j) (nuInt F c x j)) (TensorCat.ordinaryTest d)
    (fun j => representedProduct_summable F hV (lwOf_irreducible D a) (lwOf_irreducible D b)
      (lwOf_irreducible D x) (lwOf_irreducible D x) _ _ d)).trans ?_
  exact Finset.sum_congr rfl fun j _ => representedProduct_evaluation F _ _ d

/-- **Every fixed-weight trace coefficient of the vacuum channel decomposes** into the
categorical product channels, on the real segment `0 < s < 1`. -/
theorem vacuum_coeff (hV : StronglyRational W) (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b) (x : ι) {α₁ α₂ : ℂ} {wa : (lwOf D a).carrier}
    {wb : (lwOf D b).carrier} (hwa : wa ∈ (lwOf D a).isMod.weight α₁)
    (hwb : wb ∈ (lwOf D b).isMod.weight α₂) (β : ℂ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    iterateCoeff (Q := vacuumLW W hv) (N := lwOf D x) (moduleIntertwiner (lwOf D x).isMod)
        (epsInt F c) wa wb α₁ α₂ β (s : ℂ) 1 =
      ∑ j, productCoeff (Q := lwOf D (c.lab x j)) (muInt F H c x j) (nuInt F c x j)
        wa wb α₁ α₂ β ((1 + s : ℝ) : ℂ) 1 := by
  classical
  letI := (lwOf D x).isMod.finrank β
  let bs := Module.finBasis ℂ ((lwOf D x).isMod.weight β)
  have hs0' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsn : ‖(s : ℂ)‖ < ‖(1 : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs0.le, norm_one]; exact hs1
  have hpn : ‖(1 : ℂ)‖ < ‖((1 + s : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_one]; linarith
  rw [iterateCoeff_eq_sum_iterValue hV (lwOf_irreducible D a) (lwOf_irreducible D b)
    (lwOf_irreducible D x) _ _ hwa hwb β bs hs0' hsn]
  simp_rw [productCoeff_eq_sum_prodValue hV (lwOf_irreducible D a) (lwOf_irreducible D b)
    (lwOf_irreducible D x) _ _ hwa hwb β bs one_ne_zero hpn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let d : AssocConverse.TestData (lwOf D a) (lwOf D b) (lwOf D x) (lwOf D x) :=
    ⟨α₁, α₂, β, β, wa, wb, bs i, weightFunctional (lwOf D x).isMod β bs i, hwa, hwb,
      (bs i).property, supportedAt_weightFunctional (lwOf D x).isMod β bs i, s, hs0, hs1⟩
  have h := vacuum_fourPoint F H hV hv c x d
  rw [iterateValue_eq_iterValue] at h
  simp only [productValue_eq_prodValue] at h
  have hσ : α₁ + α₂ + β - β - 2 = α₁ + α₂ - 2 := by ring
  have hcast : ((1 + s : ℝ) : ℂ) = 1 + (s : ℂ) := by push_cast; ring
  rw [hcast]
  simpa only [d, hσ] using h

/-! ## §4 The genus-one vacuum-channel function -/

/-- **The vacuum-channel function is a concrete genus-one function built from intertwiners**,
and it equals the sum of the categorical product channels on the complex half-disc:
`Tr_{M_x} Y_{M_x}(Y^e(w_a, z₀) w_b, 1) q^{L₀−c/24} =
 Σ_j Tr_{M_x} μ_j(w_a, 1 + z₀) ν_j(w_b, 1) q^{L₀−c/24}`, both absolutely convergent. -/
theorem vacuumChannel_eq_product (hV : StronglyRational W) (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b) (x : ι) {α₁ α₂ : ℂ} {wa : (lwOf D a).carrier}
    {wb : (lwOf D b).carrier} (hwa : wa ∈ (lwOf D a).isMod.weight α₁)
    (hwb : wb ∈ (lwOf D b).isMod.weight α₂) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ : ℂ, 0 < z₀.re → ‖z₀‖ < δ →
      IterateSewingSummable (Q := vacuumLW W hv) (N := lwOf D x)
        (moduleIntertwiner (lwOf D x).isMod) (epsInt F c) wa wb α₁ α₂ z₀ 1 τ ∧
      (∀ j, ProductSewingSummable (Q := lwOf D (c.lab x j)) (muInt F H c x j) (nuInt F c x j)
        wa wb α₁ α₂ (1 + z₀) 1 τ) ∧
      iterF (Q := vacuumLW W hv) (N := lwOf D x) (moduleIntertwiner (lwOf D x).isMod)
          (epsInt F c) wa wb α₁ α₂ τ z₀ =
        ∑ j, prodF (Q := lwOf D (c.lab x j)) (muInt F H c x j) (nuInt F c x j) wa wb α₁ α₂ τ
          (1 + z₀) := by
  have iQ : (vacuumLW W hv).IsIrreducibleLW :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hV.simple
  exact complex_overlap_of_coeff hV (lwOf_irreducible D a) (lwOf_irreducible D b)
    (lwOf_irreducible D x) iQ (R := fun j => lwOf D (c.lab x j))
    (moduleIntertwiner (lwOf D x).isMod) (epsInt F c) (muInt F H c x) (nuInt F c x) hwa hwb τ
    ⟨1, one_pos, fun s hs0 hs1 n => vacuum_coeff F H hV hv c x hwa hwb _ s hs0 hs1⟩

end VOA.Huang.GenusOneG1c
