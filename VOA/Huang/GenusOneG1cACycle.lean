import VOA.Huang.GenusOneG1cGeneral

/-!
# The A-cycle of the vacuum channel (Huang Lemma 4.2 (4.10), Cor. 4.4 (4.23))

`GenusOneWard.prodLift_acycle_right` multiplies the `j`-th product channel `μ_j ν_j` of `Ψ_x` by
the phase `aPhase γ x j = e^{2πi(h_{lab j} − h_x − γ)}` (`γ` the weight of `w_b`). Categorically
the A-transported product is the product channel of `aHom = (M_a ◁ T_x) ≫ ψ_x`,
`T_x = Σ_j aPhase_j • (proj_j ≫ inc_j)` (`aProduct_dictionary`). Through the evaluation
associator and a section `η'` of `ε` (`η' ≫ ε = 𝟙`, exists: `exists_vacuumSection`):

* `assoc_aHom_decomp`: `α ≫ aHom = Ω_x • (α ≫ ψ_x) + ((𝟙 − ε ≫ η') ▷ –) ≫ α ≫ aHom`, where
  `Ω_x • 𝟙 = λ⁻¹ ≫ (η' ▷ M_x) ≫ α ≫ aHom` (Schur, `IsACycleScalar`, `exists_aCycleScalar`);
  the remainder vanishes on the vacuum summand (`eta_aNonVac`);
* `acycle_fourPoint`: `Σ_j aPhase_j ⟨f, μ_j(w_a, 1 + t) ν_j(w_b, 1) w⟩ =
  Ω_x ⟨f, Y_{M_x}(Y^e(w_a, t) w_b, 1) w⟩ + Σ_k ⟨f, A_k(B_k(w_a, t) w_b, 1) w⟩`;
* `acycle_vacuumChannel_complex` (genus one, half-disc): the A-cycle `ℓ₂ ↦ ℓ₂ + 2πi` of the
  product expansion of `Ψ_x` at `(log(1 + z₀), 0)` equals `Ω_x · Ψ_x(z₀) + Σ_k R_k(z₀)`, with
  `Ψ_x = iterF Y_{M_x} (epsInt c)` itself — Huang's (4.10): the A-cycle acts on the vacuum
  channel by the scalar `Ω_x` modulo channels orthogonal to the vacuum summand of `M_a ⊠ M_b`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1c

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.FusionProduct VOA.Huang.FusionUnit
  VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion VOA.Huang.AssocTarget CategoryTheory
  Complex
open VOA.Huang.GenusTwoPoint (IterateSewingSummable ProductSewingSummable vacuumLW)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]
variable (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

/-! ## §1 The A-transported morphism -/

/-- The A-cycle phase of the summand `j` of `M_b ⊠ M_x` (`γ`: weight of the `M_b` insertion). -/
def aPhase (c : TransferChoice F D a b) (γ : ℂ) (x : ι) (j : Fin (c.r x)) : ℂ :=
  exp (2 * (Real.pi : ℂ) * I * (D.h (c.lab x j) - D.h x - γ))

/-- `T_x = Σ_j aPhase_j • (proj_j ≫ inc_j)`. -/
def aTwist (c : TransferChoice F D a b) (γ : ℂ) (x : ι) :
    tensorObj F (famObj D b) (famObj D x) ⟶ tensorObj F (famObj D b) (famObj D x) :=
  ∑ j, aPhase F c γ x j • (c.proj x j ≫ c.inc x j)

/-- The A-transported vacuum channel `(M_a ◁ T_x) ≫ ψ_x`. -/
def aHom (c : TransferChoice F D a b) (γ : ℂ) (x : ι) :
    tensorObj F (famObj D a) (tensorObj F (famObj D b) (famObj D x)) ⟶ famObj D x :=
  tensorHom F (𝟙 (famObj D a)) (aTwist F c γ x) ≫ vacuumProduct F H c x

/-- The product channel of `aHom` is `Σ_j aPhase_j • μ_j(·, z₁) ν_j(·, z₂)`. -/
theorem aProduct_dictionary (c : TransferChoice F D a b) (γ : ℂ) (x : ι) :
    postcompose (F (famObj D a) (tensorObj F (famObj D b) (famObj D x))).intertwiner
        (famObj D x).isMod (aHom F H c γ x) =
      ∑ j, aPhase F c γ x j • representedProduct F (P₁ := lwOf D a) (P₂ := lwOf D b)
        (P₃ := lwOf D x) (P₄ := lwOf D x) (Q := lwOf D (c.lab x j)) (muInt F H c x j)
        (nuInt F c x j) := by
  have hl : ∀ j, (F (famObj D b) (famObj D x)).lift (lwOf D (c.lab x j)).isMod
      (nuInt F c x j) = c.proj x j := fun j =>
    lift_postcompose (F (famObj D b) (famObj D x)) (lwOf D (c.lab x j)).isMod (c.proj x j)
  apply Subtype.ext
  funext n
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  change _ = (∑ j, aPhase F c γ x j • representedProduct F (P₁ := lwOf D a) (P₂ := lwOf D b)
        (P₃ := lwOf D x) (P₄ := lwOf D x) (Q := lwOf D (c.lab x j)) (muInt F H c x j)
        (nuInt F c x j)).val n u v
  rw [intertwiner_sum_apply]
  have hterm : ∀ j, (aPhase F c γ x j • representedProduct F (P₁ := lwOf D a)
      (P₂ := lwOf D b) (P₃ := lwOf D x) (P₄ := lwOf D x) (Q := lwOf D (c.lab x j))
      (muInt F H c x j) (nuInt F c x j)).val n u v =
      aPhase F c γ x j • (vacuumProduct F H c x).val
        ((F (famObj D a) (tensorObj F (famObj D b) (famObj D x))).intertwiner.val n u
          ((c.inc x j).val ((c.proj x j).val v))) := by
    intro j
    change aPhase F c γ x j • (muInt F H c x j).val n u
      (((F (famObj D b) (famObj D x)).lift (lwOf D (c.lab x j)).isMod (nuInt F c x j)).val v) = _
    rw [hl j, muInt_apply]
    rfl
  simp only [hterm]
  have hT : (aTwist F c γ x).val v =
      ∑ j, aPhase F c γ x j • (c.inc x j).val ((c.proj x j).val v) := by
    unfold aTwist
    rw [Ordinary.sum_val_apply]
    rfl
  set Y := (F (famObj D a) (tensorObj F (famObj D b) (famObj D x))).intertwiner with hY
  calc _ = (vacuumProduct F H c x).val (Y.val n u ((aTwist F c γ x).val v)) := by
        change (tensorHom F (𝟙 (famObj D a)) (aTwist F c γ x) ≫ vacuumProduct F H c x).val
          (Y.val n u v) = _
        rw [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply]
    _ = _ := by
        rw [hT, map_sum]
        simp only [LinearMap.map_smul]
        exact (map_sum (vacuumProduct F H c x).val _ _).trans
          (Finset.sum_congr rfl fun j _ => (vacuumProduct F H c x).val.map_smul _ _)

/-- `Ω` lists the Schur scalars of the A-transported vacuum coefficients. -/
def IsACycleScalar (c : TransferChoice F D a b)
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)) (γ : ℂ)
    (Ω : ι → ℂ) : Prop :=
  ∀ x, (leftUnitor F (famObj D x)).inv ≫ tensorHom F η' (𝟙 (famObj D x)) ≫
    (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ aHom F H c γ x =
      Ω x • 𝟙 (famObj D x)

theorem exists_aCycleScalar (c : TransferChoice F D a b)
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)) (γ : ℂ) :
    ∃ Ω : ι → ℂ, IsACycleScalar F H c η' γ Ω :=
  ⟨fun x => (endo_scalar D x _).choose, fun x => (endo_scalar D x _).choose_spec⟩

/-- The complement `𝟙 − ε ≫ η'` of the vacuum summand of `M_a ⊠ M_b`. -/
def aNonVac (c : TransferChoice F D a b)
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)) :
    tensorObj F (famObj D a) (famObj D b) ⟶ tensorObj F (famObj D a) (famObj D b) :=
  𝟙 _ - c.ε ≫ η'

theorem eta_aNonVac (c : TransferChoice F D a b)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (hη' : η' ≫ c.ε = 𝟙 _) : η' ≫ aNonVac F c η' = 0 := by
  unfold aNonVac
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hη', Category.id_comp, sub_self]

theorem aNonVac_eps (c : TransferChoice F D a b)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (hη' : η' ≫ c.ε = 𝟙 _) : aNonVac F c η' ≫ c.ε = 0 := by
  unfold aNonVac
  rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hη', Category.comp_id, sub_self]

/-- **The A-cycle acts on the vacuum channel by a scalar, modulo the non-vacuum summands.** -/
theorem assoc_aHom_decomp (c : TransferChoice F D a b)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)} {γ : ℂ}
    {Ω : ι → ℂ} (hΩ : IsACycleScalar F H c η' γ Ω) (x : ι) :
    (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ aHom F H c γ x =
      Ω x • ((evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫
        vacuumProduct F H c x) +
      tensorHom F (aNonVac F c η') (𝟙 (famObj D x)) ≫
        (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ aHom F H c γ x := by
  have hb := hΩ x
  have hX : tensorHom F η' (𝟙 (famObj D x)) ≫
      (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ aHom F H c γ x =
        Ω x • (leftUnitor F (famObj D x)).hom := by
    have h2 := congrArg (fun f => (leftUnitor F (famObj D x)).hom ≫ f) hb
    simp only at h2
    rw [Iso.hom_inv_id_assoc] at h2
    rw [h2, Linear.comp_smul, Category.comp_id]
  have h1 : 𝟙 (tensorObj F (famObj D a) (famObj D b)) = c.ε ≫ η' + aNonVac F c η' := by
    unfold aNonVac; abel
  have h3 : tensorHom F (c.ε ≫ η') (𝟙 (famObj D x)) =
      tensorHom F c.ε (𝟙 (famObj D x)) ≫ tensorHom F η' (𝟙 (famObj D x)) := by
    rw [← TensorCat.tensorHom_comp, Category.id_comp]
  have e1 : (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ aHom F H c γ x =
      tensorHom F (𝟙 (tensorObj F (famObj D a) (famObj D b))) (𝟙 (famObj D x)) ≫
        (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ aHom F H c γ x := by
    rw [TensorCat.tensorHom_id, Category.id_comp]
  conv_lhs => rw [e1, h1, TensorCat.tensorHom_add_left, Preadditive.add_comp, h3,
    Category.assoc, hX, Linear.comp_smul]
  rw [assoc_vacuumProduct]

/-- The remainder vanishes on the vacuum summand. -/
theorem eta_aRem (c : TransferChoice F D a b)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (hη' : η' ≫ c.ε = 𝟙 _) (γ : ℂ) (x : ι) :
    tensorHom F η' (𝟙 (famObj D x)) ≫ tensorHom F (aNonVac F c η') (𝟙 (famObj D x)) ≫
      (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ aHom F H c γ x = 0 := by
  rw [← Category.assoc, ← TensorCat.tensorHom_comp, Category.id_comp, eta_aNonVac F c hη',
    tensorHom_zero_left', Limits.zero_comp]

/-- Splitting a left whiskering through a split presentation. -/
theorem tensorHom_split_left {X Y Z T : Ordinary W} {r : ℕ} (Ms : Fin r → Ordinary W)
    (i : ∀ k, Ms k ⟶ tensorObj F X Y) (p : ∀ k, tensorObj F X Y ⟶ Ms k)
    (htot : ∑ k, p k ≫ i k = 𝟙 _) (κ : tensorObj F X Y ⟶ tensorObj F X Y)
    (G : tensorObj F (tensorObj F X Y) Z ⟶ T) :
    tensorHom F κ (𝟙 Z) ≫ G = ∑ k, tensorHom F (κ ≫ p k) (𝟙 Z) ≫ (tensorHom F (i k) (𝟙 Z) ≫ G) := by
  have hsplit : κ = ∑ k, (κ ≫ p k) ≫ i k := by
    conv_lhs => rw [← Category.comp_id κ, ← htot]
    rw [Preadditive.comp_sum]
    exact Finset.sum_congr rfl fun k _ => (Category.assoc _ _ _).symm
  have hT : ∀ (s : Finset (Fin r)), tensorHom F (∑ k ∈ s, (κ ≫ p k) ≫ i k) (𝟙 Z) =
      ∑ k ∈ s, tensorHom F ((κ ≫ p k) ≫ i k) (𝟙 Z) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simpa using tensorHom_zero_left' F
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, TensorCat.tensorHom_add_left, ih]
  nth_rewrite 1 [hsplit]
  rw [hT, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Category.id_comp (𝟙 Z), TensorCat.tensorHom_comp, Category.id_comp, Category.assoc]

/-- The `k`-th inner channel of the A-cycle remainder, `((𝟙 − ε ≫ η') ≫ p_k) ∘ 𝒴_{ab}`. -/
def aRemInner (c : TransferChoice F D a b)
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)) {r : ℕ}
    (lab' : Fin r → ι) (p : ∀ k, tensorObj F (famObj D a) (famObj D b) ⟶ famObj D (lab' k))
    (k : Fin r) :
    IntertwiningOperator (lwOf D a).isMod (lwOf D b).isMod (lwOf D (lab' k)).isMod :=
  postcompose (F (famObj D a) (famObj D b)).intertwiner (lwOf D (lab' k)).isMod
    (aNonVac F c η' ≫ p k)

/-- The `k`-th outer channel of the A-cycle remainder. -/
def aRemOuter (c : TransferChoice F D a b) (γ : ℂ) (x : ι) {r : ℕ} (lab' : Fin r → ι)
    (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D a) (famObj D b)) (k : Fin r) :
    IntertwiningOperator (lwOf D (lab' k)).isMod (lwOf D x).isMod (lwOf D x).isMod :=
  postcompose (F (famObj D (lab' k)) (famObj D x)).intertwiner (lwOf D x).isMod
    (tensorHom F (i k) (𝟙 _) ≫
      (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ aHom F H c γ x)

theorem eta_aRemInner (c : TransferChoice F D a b)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (hη' : η' ≫ c.ε = 𝟙 _) {r : ℕ} (lab' : Fin r → ι)
    (p : ∀ k, tensorObj F (famObj D a) (famObj D b) ⟶ famObj D (lab' k)) (k : Fin r) :
    η' ≫ aNonVac F c η' ≫ p k = 0 := by
  rw [← Category.assoc, eta_aNonVac F c hη', Limits.zero_comp]

theorem productEvaluation_sum_smul (hs : OrdinaryFourPointSummability F) {X Y Z T : Ordinary W}
    {r : ℕ} (t : Fin r → ℂ) (I : Fin r → ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    productEvaluation F (∑ j, t j • I j) d = ∑ j, t j * productEvaluation F (I j) d := by
  have h := congrFun (map_sum (productEvaluationLinear F hs X Y Z T) (fun j => t j • I j)
    Finset.univ) d
  rw [Finset.sum_apply] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  exact congrFun (map_smul (productEvaluationLinear F hs X Y Z T) (t j) (I j)) d

/-- **The A-cycle four-point identity.** -/
theorem acycle_fourPoint (hV : StronglyRational W) (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)} {γ : ℂ}
    {Ω : ι → ℂ} (hΩ : IsACycleScalar F H c η' γ Ω) (x : ι) {r : ℕ} (lab' : Fin r → ι)
    (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D a) (famObj D b))
    (p : ∀ k, tensorObj F (famObj D a) (famObj D b) ⟶ famObj D (lab' k))
    (htot : ∑ k, p k ≫ i k = 𝟙 _)
    (d : AssocConverse.TestData (lwOf D a) (lwOf D b) (lwOf D x) (lwOf D x)) :
    ∑ j, aPhase F c γ x j * AssocConverse.productValue (Q := lwOf D (c.lab x j))
        (muInt F H c x j) (nuInt F c x j) d =
      Ω x * AssocConverse.iterateValue (Q := vacuumLW W hv) (moduleIntertwiner (lwOf D x).isMod)
        (epsInt F c) d +
      ∑ k, AssocConverse.iterateValue (Q := lwOf D (lab' k)) (aRemOuter F H c γ x lab' i k)
        (aRemInner F c η' lab' p k) d := by
  have hs := ordinaryFourPointSummability_pbw F hV
  have h4 := congrFun (evalAssoc_fourPoint F H (famObj D a) (famObj D b) (famObj D x)
    (famObj D x) (aHom F H c γ x)) (TensorCat.ordinaryTest d)
  have hP : productEvaluation F
      (postcompose (F (famObj D a) (tensorObj F (famObj D b) (famObj D x))).intertwiner
        (famObj D x).isMod (aHom F H c γ x)) (TensorCat.ordinaryTest d) =
      ∑ j, aPhase F c γ x j * AssocConverse.productValue (Q := lwOf D (c.lab x j))
        (muInt F H c x j) (nuInt F c x j) d := by
    rw [aProduct_dictionary]
    refine (productEvaluation_sum_smul F hs _ _ _).trans ?_
    exact Finset.sum_congr rfl fun j _ => congrArg _ (representedProduct_evaluation F _ _ d)
  obtain ⟨A, hA⟩ : ∃ A : IterateSpace F (famObj D a) (famObj D b) (famObj D x) (famObj D x),
      A = postcompose (F (tensorObj F (famObj D a) (famObj D b)) (famObj D x)).intertwiner
        (famObj D x).isMod
        ((evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ vacuumProduct F H c x) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin r → IterateSpace F (famObj D a) (famObj D b) (famObj D x)
      (famObj D x), B = fun k => postcompose
        (F (tensorObj F (famObj D a) (famObj D b)) (famObj D x)).intertwiner
        (famObj D x).isMod
        (tensorHom F (aNonVac F c η' ≫ p k) (𝟙 (famObj D x)) ≫ (tensorHom F (i k) (𝟙 _) ≫
          (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ aHom F H c γ x)) :=
    ⟨_, rfl⟩
  have hdec : postcompose (F (tensorObj F (famObj D a) (famObj D b)) (famObj D x)).intertwiner
      (famObj D x).isMod
      ((evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫ aHom F H c γ x) =
      Ω x • A + ∑ k, B k := by
    rw [hA, hB]
    conv_lhs => rw [assoc_aHom_decomp F H c hΩ x,
      tensorHom_split_left F (fun k => famObj D (lab' k)) i p htot]
    exact (postcompose_cat_add F _ _).trans
      (congrArg₂ (· + ·) (postcompose_cat_smul F _ _) (postcompose_cat_sum F _ _))
  have hI0 : iterateEvaluation F A (TensorCat.ordinaryTest d) =
      AssocConverse.iterateValue (Q := vacuumLW W hv) (moduleIntertwiner (lwOf D x).isMod)
        (epsInt F c) d := by
    rw [hA, iterate_dictionary F H hv c x]
    exact representedIterate_evaluation F _ _ d
  have hIk : ∀ k, iterateEvaluation F (B k) (TensorCat.ordinaryTest d) =
      AssocConverse.iterateValue (Q := lwOf D (lab' k)) (aRemOuter F H c γ x lab' i k)
        (aRemInner F c η' lab' p k) d := by
    intro k
    rw [hB]
    exact (congrArg (fun I => iterateEvaluation F I (TensorCat.ordinaryTest d))
      (iterate_tensorHom_dictionary F (P₁ := lwOf D a) (P₂ := lwOf D b)
        (P₃ := lwOf D x) (P₄ := lwOf D x) (lwOf D (lab' k))
        (aNonVac F c η' ≫ p k) (tensorHom F (i k) (𝟙 _) ≫
          (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).hom ≫
            aHom F H c γ x))).trans
      (representedIterate_evaluation F _ _ d)
  rw [hdec, iterateEvaluation_add F hs, iterateEvaluation_smul F hs,
    iterateEvaluation_sum F _ _ (fun k => (hs _ _ _ _ _).1 _), hP, hI0] at h4
  rw [← h4]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => hIk k)

end VOA.Huang.GenusOneG1c
