import VOA.Huang.GenusOneG1cDictionary

/-!
# The B-cycle transfer as the vacuum coefficient of the reversed product (genus zero)

Step (c), genus-zero half: Huang's Lemma 4.2 (4.11) reads the B-cycle matrix off the
vacuum channel of the REVERSED product `ν_j(w_b, z₁) μ_j(w_a, z₂)` (traced, at genus one, over
`M_{lab j}`; `prodLift_bcycle` produces exactly this reversed product from the vacuum channel
`Ψ_x`).
Here that reading is made exact in the category and then on four-point functions:

* `assoc_revHom_decomp` (category): for any `π : M_b ⊠ M_a → V` with `η ≫ π = 𝟙`,
  `α ≫ (ν_j ∘ (M_b ◁ μ_j)) = β_{xj} • ((π ▷ M_{lab j}) ≫ λ) + remHom`, where the remainder
  `remHom = ((𝟙 − π ≫ η) ▷ –) ≫ α ≫ …` has ZERO vacuum coefficient: `(η ▷ –) ≫ remHom = 0`
  (`eta_remHom`), `(𝟙 − π ≫ η) ≫ π = 0`, `η ≫ (𝟙 − π ≫ η) = 0`. The scalar `β_{xj}` is the
  `bTransfer` scalar (`IsTransferScalar`).
* `revProduct_dictionary`: the product channel of `ν_j ∘ (M_b ◁ μ_j)` is the represented product
  `ν_j(·, z₁) μ_j(·, z₂)` of the intertwiners of `GenusOneG1cDictionary`.
* `iterate_tensorHom_dictionary`: an iterate morphism `(g ▷ Z) ≫ h` with `g : X ⊠ Y → Q` is the
  represented iterate `h̃(g̃(·, z₀)·, z₂)`.
* `reversed_fourPoint`: with a split presentation `Σ_k p_k ≫ i_k = 𝟙` of `M_b ⊠ M_a`,
  `⟨f, ν_j(w_b, 1 + x) μ_j(w_a, 1) w⟩ = β_{xj} ⟨f, Y_{M_{lab j}}(Y^π(w_b, x) w_a, 1) w⟩
     + Σ_k ⟨f, A_k(B_k(w_b, x) w_a, 1) w⟩`, where every inner channel `B_k` is orthogonal to the
  vacuum summand (`η ≫ (𝟙 − π ≫ η) ≫ p_k = 0`).
-/

noncomputable section

namespace VOA.Huang.GenusOneG1c

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.FusionProduct VOA.Huang.FusionUnit
  VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion VOA.Huang.AssocTarget CategoryTheory
open VOA.Huang.GenusTwoPoint (vacuumLW)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]
variable (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

/-! ## §1 The categorical decomposition -/

/-- The reversed product morphism `ν_j ∘ (M_b ◁ μ_j) : M_b ⊠ (M_a ⊠ M_{lab j}) → M_{lab j}`. -/
def revHom (c : TransferChoice F D a b) (x : ι) (j : Fin (c.r x)) :
    tensorObj F (famObj D b) (tensorObj F (famObj D a) (famObj D (c.lab x j))) ⟶
      famObj D (c.lab x j) :=
  tensorHom F (𝟙 (famObj D b)) (muHom F H c x j) ≫ c.proj x j

theorem bTransfer_eq_revHom (c : TransferChoice F D a b) (x : ι) (j : Fin (c.r x)) :
    bTransfer F H c x j = (leftUnitor F (famObj D (c.lab x j))).inv ≫
      tensorHom F c.η (𝟙 (famObj D (c.lab x j))) ≫
      (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫
      revHom F H c x j := rfl

/-- The complement of the vacuum summand of `M_b ⊠ M_a`: `𝟙 − π ≫ η`. -/
def nonVac (c : TransferChoice F D a b)
    (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) :
    tensorObj F (famObj D b) (famObj D a) ⟶ tensorObj F (famObj D b) (famObj D a) :=
  𝟙 _ - π ≫ c.η

theorem eta_nonVac (c : TransferChoice F D a b)
    {π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject} (hπ : c.η ≫ π = 𝟙 _) :
    c.η ≫ nonVac F c π = 0 := by
  unfold nonVac
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hπ, Category.id_comp, sub_self]

theorem nonVac_pi (c : TransferChoice F D a b)
    {π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject} (hπ : c.η ≫ π = 𝟙 _) :
    nonVac F c π ≫ π = 0 := by
  unfold nonVac
  rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hπ, Category.comp_id, sub_self]

/-- The remainder of the reversed iterate: the part through the non-vacuum complement. -/
def remHom (c : TransferChoice F D a b)
    (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) (x : ι) (j : Fin (c.r x)) :
    tensorObj F (tensorObj F (famObj D b) (famObj D a)) (famObj D (c.lab x j)) ⟶
      famObj D (c.lab x j) :=
  tensorHom F (nonVac F c π) (𝟙 _) ≫
    (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫ revHom F H c x j

theorem tensorHom_zero_left' {X X' Y : Ordinary W} :
    tensorHom F (0 : X ⟶ X') (𝟙 Y) = 0 := by
  have h := TensorCat.tensorHom_smul_left F (0 : ℂ) (0 : X ⟶ X') (𝟙 Y)
  rwa [zero_smul, zero_smul] at h

/-- The remainder has zero vacuum coefficient. -/
theorem eta_remHom (c : TransferChoice F D a b)
    {π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject} (hπ : c.η ≫ π = 𝟙 _)
    (x : ι) (j : Fin (c.r x)) :
    tensorHom F c.η (𝟙 (famObj D (c.lab x j))) ≫ remHom F H c π x j = 0 := by
  unfold remHom
  rw [← Category.assoc, ← TensorCat.tensorHom_comp, Category.id_comp, eta_nonVac F c hπ,
    tensorHom_zero_left', Limits.zero_comp]

/-- **The B-cycle scalar is the vacuum coefficient of the reversed product** (category). -/
theorem assoc_revHom_decomp (c : TransferChoice F D a b) {β : ∀ x, Fin (c.r x) → ℂ}
    (hβ : IsTransferScalar F H c β)
    (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject)
    (x : ι) (j : Fin (c.r x)) :
    (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫ revHom F H c x j =
      β x j • (tensorHom F π (𝟙 (famObj D (c.lab x j))) ≫
        (leftUnitor F (famObj D (c.lab x j))).hom) + remHom F H c π x j := by
  have hb := hβ x j
  rw [bTransfer_eq_revHom] at hb
  have hX : tensorHom F c.η (𝟙 (famObj D (c.lab x j))) ≫
      (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫
        revHom F H c x j = β x j • (leftUnitor F (famObj D (c.lab x j))).hom := by
    have h2 := congrArg (fun f => (leftUnitor F (famObj D (c.lab x j))).hom ≫ f) hb
    simp only at h2
    rw [Iso.hom_inv_id_assoc] at h2
    rw [h2, Linear.comp_smul, Category.comp_id]
  have h1 : 𝟙 (tensorObj F (famObj D b) (famObj D a)) = π ≫ c.η + nonVac F c π := by
    unfold nonVac; abel
  have h3 : tensorHom F (π ≫ c.η) (𝟙 (famObj D (c.lab x j))) =
      tensorHom F π (𝟙 (famObj D (c.lab x j))) ≫ tensorHom F c.η (𝟙 (famObj D (c.lab x j))) := by
    rw [← TensorCat.tensorHom_comp, Category.id_comp]
  have e1 : (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫
      revHom F H c x j = tensorHom F (𝟙 (tensorObj F (famObj D b) (famObj D a)))
        (𝟙 (famObj D (c.lab x j))) ≫
        (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫
          revHom F H c x j := by
    rw [TensorCat.tensorHom_id, Category.id_comp]
  rw [e1, h1, TensorCat.tensorHom_add_left, Preadditive.add_comp, h3, Category.assoc, hX,
    Linear.comp_smul]
  rfl

/-! ## §2 Intertwiner dictionary for the reversed product and its iterate channels -/

/-- An iterate morphism `(g ▷ Z) ≫ h` through an LW object `Q` is the represented iterate. -/
theorem iterate_tensorHom_dictionary {P₁ P₂ P₃ P₄ : LWModule W} (Q : LWModule W)
    (g : tensorObj F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod) ⟶ Ordinary.of Q.isMod)
    (h : tensorObj F (Ordinary.of Q.isMod) (Ordinary.of P₃.isMod) ⟶ Ordinary.of P₄.isMod) :
    postcompose (F (tensorObj F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod))
        (Ordinary.of P₃.isMod)).intertwiner P₄.isMod
        (tensorHom F g (𝟙 (Ordinary.of P₃.isMod)) ≫ h) =
      representedIterate F (Q := Q)
        (postcompose (F (Ordinary.of Q.isMod) (Ordinary.of P₃.isMod)).intertwiner P₄.isMod h)
        (postcompose (F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).intertwiner Q.isMod g) := by
  have hl : (F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).lift Q.isMod
      (postcompose (F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).intertwiner Q.isMod g) = g :=
    lift_postcompose _ _ g
  apply Subtype.ext
  funext n
  refine LinearMap.ext fun u => LinearMap.ext fun m => ?_
  change (tensorHom F g (𝟙 (Ordinary.of P₃.isMod)) ≫ h).val
      ((F (tensorObj F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod))
        (Ordinary.of P₃.isMod)).intertwiner.val n u m) =
    h.val ((F (Ordinary.of Q.isMod) (Ordinary.of P₃.isMod)).intertwiner.val n
      (((F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).lift Q.isMod
        (postcompose _ Q.isMod g)).val u) m)
  erw [hl]
  rw [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply]
  rfl

/-- The vacuum pairing `π` as an intertwiner (Huang's `Y^e_{a' a}` for the reversed pair). -/
def piInt (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) :
    IntertwiningOperator (lwOf D b).isMod (lwOf D a).isMod (adjointModule W) :=
  postcompose (F (famObj D b) (famObj D a)).intertwiner (adjointModule W) π

/-- The vacuum part of the reversed iterate is `Y_{M_{lab j}}(Y^π(·, z₀)·, z₂)`. -/
theorem vacuumPart_dictionary (hv : W.vacuum ≠ 0)
    (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) (y : ι) :
    postcompose (F (tensorObj F (famObj D b) (famObj D a)) (famObj D y)).intertwiner
        (famObj D y).isMod (tensorHom F π (𝟙 (famObj D y)) ≫ (leftUnitor F (famObj D y)).hom) =
      representedIterate F (P₁ := lwOf D b) (P₂ := lwOf D a) (P₃ := lwOf D y)
        (P₄ := lwOf D y) (Q := vacuumLW W hv) (moduleIntertwiner (lwOf D y).isMod)
        (piInt F π) := by
  have hl : (F (famObj D b) (famObj D a)).lift (vacuumLW W hv).isMod (piInt F π) = π :=
    lift_postcompose (F (famObj D b) (famObj D a)) (adjointModule W) π
  apply Subtype.ext
  funext n
  refine LinearMap.ext fun u => LinearMap.ext fun m => ?_
  change (tensorHom F π (𝟙 (famObj D y)) ≫ (leftUnitor F (famObj D y)).hom).val
      ((F (tensorObj F (famObj D b) (famObj D a)) (famObj D y)).intertwiner.val n u m) =
    (moduleIntertwiner (lwOf D y).isMod).val n
      (((F (famObj D b) (famObj D a)).lift (vacuumLW W hv).isMod (piInt F π)).val u) m
  rw [hl, Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply, leftUnitor_intertwiner]
  rfl

/-- The product channel of `ν_j ∘ (M_b ◁ μ_j)` is the represented product
`ν_j(·, z₁) μ_j(·, z₂)`. -/
theorem revProduct_dictionary (c : TransferChoice F D a b) (x : ι) (j : Fin (c.r x)) :
    postcompose (F (famObj D b) (tensorObj F (famObj D a) (famObj D (c.lab x j)))).intertwiner
        (famObj D (c.lab x j)).isMod (revHom F H c x j) =
      representedProduct F (P₁ := lwOf D b) (P₂ := lwOf D a) (P₃ := lwOf D (c.lab x j))
        (P₄ := lwOf D (c.lab x j)) (Q := lwOf D x) (nuInt F c x j) (muInt F H c x j) := by
  have hl : (F (famObj D a) (famObj D (c.lab x j))).lift (lwOf D x).isMod (muInt F H c x j) =
      muHom F H c x j :=
    lift_postcompose (F (famObj D a) (famObj D (c.lab x j))) (lwOf D x).isMod (muHom F H c x j)
  apply Subtype.ext
  funext n
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  change (tensorHom F (𝟙 (famObj D b)) (muHom F H c x j) ≫ c.proj x j).val
      ((F (famObj D b) (tensorObj F (famObj D a) (famObj D (c.lab x j)))).intertwiner.val n u v) =
    (nuInt F c x j).val n u
      (((F (famObj D a) (famObj D (c.lab x j))).lift (lwOf D x).isMod (muInt F H c x j)).val v)
  rw [hl, Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply]
  rfl

/-! ## §3 The reversed four-point identity -/

/-- The remainder's `k`-th inner channel `B_k = ((𝟙 − π ≫ η) ≫ p_k) ∘ 𝒴_{ba}`. -/
def remInner (c : TransferChoice F D a b)
    (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) {r : ℕ} (lab' : Fin r → ι)
    (p : ∀ k, tensorObj F (famObj D b) (famObj D a) ⟶ famObj D (lab' k)) (k : Fin r) :
    IntertwiningOperator (lwOf D b).isMod (lwOf D a).isMod (lwOf D (lab' k)).isMod :=
  postcompose (F (famObj D b) (famObj D a)).intertwiner (lwOf D (lab' k)).isMod
    (nonVac F c π ≫ p k)

/-- The remainder's `k`-th outer channel `A_k = ((i_k ▷ –) ≫ α ≫ revHom) ∘ 𝒴`. -/
def remOuter (c : TransferChoice F D a b) (x : ι) (j : Fin (c.r x)) {r : ℕ} (lab' : Fin r → ι)
    (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D b) (famObj D a)) (k : Fin r) :
    IntertwiningOperator (lwOf D (lab' k)).isMod (lwOf D (c.lab x j)).isMod
      (lwOf D (c.lab x j)).isMod :=
  postcompose (F (famObj D (lab' k)) (famObj D (c.lab x j))).intertwiner
    (lwOf D (c.lab x j)).isMod
    (tensorHom F (i k) (𝟙 _) ≫
      (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫ revHom F H c x j)

/-- Every remainder inner channel is orthogonal to the vacuum summand. -/
theorem eta_remInner (c : TransferChoice F D a b)
    {π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject} (hπ : c.η ≫ π = 𝟙 _)
    {r : ℕ} (lab' : Fin r → ι)
    (p : ∀ k, tensorObj F (famObj D b) (famObj D a) ⟶ famObj D (lab' k)) (k : Fin r) :
    c.η ≫ nonVac F c π ≫ p k = 0 := by
  rw [← Category.assoc, eta_nonVac F c hπ, Limits.zero_comp]

/-- The remainder splits into iterate channels through the summands of a split presentation. -/
theorem remHom_split (c : TransferChoice F D a b)
    (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) (x : ι) (j : Fin (c.r x))
    {r : ℕ} (lab' : Fin r → ι)
    (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D b) (famObj D a))
    (p : ∀ k, tensorObj F (famObj D b) (famObj D a) ⟶ famObj D (lab' k))
    (htot : ∑ k, p k ≫ i k = 𝟙 _) :
    remHom F H c π x j = ∑ k, tensorHom F (nonVac F c π ≫ p k) (𝟙 (famObj D (c.lab x j))) ≫
      (tensorHom F (i k) (𝟙 _) ≫
        (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫
          revHom F H c x j) := by
  have hsplit : nonVac F c π = ∑ k, (nonVac F c π ≫ p k) ≫ i k := by
    conv_lhs => rw [← Category.comp_id (nonVac F c π), ← htot]
    rw [Preadditive.comp_sum]
    exact Finset.sum_congr rfl fun k _ => (Category.assoc _ _ _).symm
  have hT : ∀ (s : Finset (Fin r)), tensorHom F (∑ k ∈ s, (nonVac F c π ≫ p k) ≫ i k)
      (𝟙 (famObj D (c.lab x j))) =
      ∑ k ∈ s, tensorHom F ((nonVac F c π ≫ p k) ≫ i k) (𝟙 (famObj D (c.lab x j))) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simpa using tensorHom_zero_left' F
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, TensorCat.tensorHom_add_left, ih]
  unfold remHom
  nth_rewrite 1 [hsplit]
  rw [hT, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Category.id_comp (𝟙 (famObj D (c.lab x j))), TensorCat.tensorHom_comp, Category.id_comp,
    Category.assoc]

theorem postcompose_cat_add {X Y T : Ordinary W} (f g : tensorObj F X Y ⟶ T) :
    postcompose (F X Y).intertwiner T.isMod (f + g) =
      postcompose (F X Y).intertwiner T.isMod f + postcompose (F X Y).intertwiner T.isMod g :=
  map_add (postcompose (F X Y).intertwiner T.isMod) f g

theorem postcompose_cat_smul {X Y T : Ordinary W} (t : ℂ) (f : tensorObj F X Y ⟶ T) :
    postcompose (F X Y).intertwiner T.isMod (t • f) =
      t • postcompose (F X Y).intertwiner T.isMod f :=
  map_smul (postcompose (F X Y).intertwiner T.isMod) t f

theorem postcompose_cat_sum {X Y T : Ordinary W} {κ : Type*} (s : Finset κ)
    (f : κ → (tensorObj F X Y ⟶ T)) :
    postcompose (F X Y).intertwiner T.isMod (∑ k ∈ s, f k) =
      ∑ k ∈ s, postcompose (F X Y).intertwiner T.isMod (f k) :=
  map_sum (postcompose (F X Y).intertwiner T.isMod) f s

theorem iterateEvaluation_add (hs : OrdinaryFourPointSummability F) {X Y Z T : Ordinary W}
    (I J : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    iterateEvaluation F (I + J) d = iterateEvaluation F I d + iterateEvaluation F J d :=
  congrFun (map_add (iterateEvaluationLinear F hs X Y Z T) I J) d

theorem iterateEvaluation_smul (hs : OrdinaryFourPointSummability F) {X Y Z T : Ordinary W}
    (t : ℂ) (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    iterateEvaluation F (t • I) d = t * iterateEvaluation F I d :=
  congrFun (map_smul (iterateEvaluationLinear F hs X Y Z T) t I) d

/-- **The reversed four-point identity** (genus-zero half of Huang's Lemma 4.2 (4.11)): the
reversed product `⟨f, ν_j(w_b, 1 + x) μ_j(w_a, 1) w⟩` is `β_{xj}` times the vacuum channel
`⟨f, Y_{M_{lab j}}(Y^π(w_b, x) w_a, 1) w⟩` plus iterate channels through the summands of
`M_b ⊠ M_a` whose inner channels are orthogonal to the vacuum summand (`eta_remInner`). -/
theorem reversed_fourPoint (hV : StronglyRational W) (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b) {β : ∀ x, Fin (c.r x) → ℂ} (hβ : IsTransferScalar F H c β)
    (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) (x : ι) (j : Fin (c.r x))
    {r : ℕ} (lab' : Fin r → ι)
    (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D b) (famObj D a))
    (p : ∀ k, tensorObj F (famObj D b) (famObj D a) ⟶ famObj D (lab' k))
    (htot : ∑ k, p k ≫ i k = 𝟙 _)
    (d : AssocConverse.TestData (lwOf D b) (lwOf D a) (lwOf D (c.lab x j))
      (lwOf D (c.lab x j))) :
    AssocConverse.productValue (Q := lwOf D x) (nuInt F c x j) (muInt F H c x j) d =
      β x j * AssocConverse.iterateValue (Q := vacuumLW W hv)
        (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π) d +
      ∑ k, AssocConverse.iterateValue (Q := lwOf D (lab' k)) (remOuter F H c x j lab' i k)
        (remInner F c π lab' p k) d := by
  have hs := ordinaryFourPointSummability_pbw F hV
  have h4 := congrFun (evalAssoc_fourPoint F H (famObj D b) (famObj D a) (famObj D (c.lab x j))
    (famObj D (c.lab x j))
    (revHom F H c x j)) (TensorCat.ordinaryTest d)
  have hP : productEvaluation F
      (postcompose (F (famObj D b) (tensorObj F (famObj D a) (famObj D (c.lab x j)))).intertwiner
      (famObj D (c.lab x j)).isMod (revHom F H c x j)) (TensorCat.ordinaryTest d) =
      AssocConverse.productValue (Q := lwOf D x) (nuInt F c x j) (muInt F H c x j) d := by
    rw [revProduct_dictionary]
    exact representedProduct_evaluation F _ _ d
  have hI0 : iterateEvaluation F
      (postcompose (F (tensorObj F (famObj D b) (famObj D a)) (famObj D (c.lab x j))).intertwiner
      (famObj D (c.lab x j)).isMod (tensorHom F π (𝟙 (famObj D (c.lab x j))) ≫
        (leftUnitor F (famObj D (c.lab x j))).hom)) (TensorCat.ordinaryTest d) =
      AssocConverse.iterateValue (Q := vacuumLW W hv)
        (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π) d := by
    rw [vacuumPart_dictionary F hv π]
    exact representedIterate_evaluation F _ _ d
  have hIk : ∀ k, iterateEvaluation F
      (postcompose (F (tensorObj F (famObj D b) (famObj D a)) (famObj D (c.lab x j))).intertwiner
        (famObj D (c.lab x j)).isMod
        (tensorHom F (nonVac F c π ≫ p k) (𝟙 (famObj D (c.lab x j))) ≫ (tensorHom F (i k) (𝟙 _) ≫
          (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫ revHom F H c x j)))
      (TensorCat.ordinaryTest d) =
      AssocConverse.iterateValue (Q := lwOf D (lab' k)) (remOuter F H c x j lab' i k)
        (remInner F c π lab' p k) d := by
    intro k
    exact (congrArg (fun I => iterateEvaluation F I (TensorCat.ordinaryTest d))
      (iterate_tensorHom_dictionary F (P₁ := lwOf D b) (P₂ := lwOf D a)
        (P₃ := lwOf D (c.lab x j)) (P₄ := lwOf D (c.lab x j)) (lwOf D (lab' k))
        (nonVac F c π ≫ p k) (tensorHom F (i k) (𝟙 _) ≫
          (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫
            revHom F H c x j))).trans
      (representedIterate_evaluation F _ _ d)
  obtain ⟨A, hA⟩ : ∃ A : IterateSpace F (famObj D b) (famObj D a) (famObj D (c.lab x j))
      (famObj D (c.lab x j)), A = postcompose
        (F (tensorObj F (famObj D b) (famObj D a)) (famObj D (c.lab x j))).intertwiner
        (famObj D (c.lab x j)).isMod
        (tensorHom F π (𝟙 (famObj D (c.lab x j))) ≫ (leftUnitor F (famObj D (c.lab x j))).hom) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin r → IterateSpace F (famObj D b) (famObj D a) (famObj D (c.lab x j))
      (famObj D (c.lab x j)), B = fun k => postcompose
        (F (tensorObj F (famObj D b) (famObj D a)) (famObj D (c.lab x j))).intertwiner
        (famObj D (c.lab x j)).isMod
        (tensorHom F (nonVac F c π ≫ p k) (𝟙 (famObj D (c.lab x j))) ≫ (tensorHom F (i k) (𝟙 _) ≫
          (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫
            revHom F H c x j)) :=
    ⟨_, rfl⟩
  have hdec : postcompose
      (F (tensorObj F (famObj D b) (famObj D a)) (famObj D (c.lab x j))).intertwiner
      (famObj D (c.lab x j)).isMod
      ((evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫ revHom F H c x j) =
      β x j • A + ∑ k, B k := by
    rw [hA, hB]
    conv_lhs => rw [assoc_revHom_decomp F H c hβ π x j, remHom_split F H c π x j lab' i p htot]
    exact (postcompose_cat_add F _ _).trans
      (congrArg₂ (· + ·) (postcompose_cat_smul F _ _) (postcompose_cat_sum F _ _))
  rw [hdec, iterateEvaluation_add F hs, iterateEvaluation_smul F hs,
    iterateEvaluation_sum F _ _ (fun k => (hs _ _ _ _ _).1 _), hP] at h4
  rw [← h4, hA, hI0, hB]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => hIk k)

end VOA.Huang.GenusOneG1c
