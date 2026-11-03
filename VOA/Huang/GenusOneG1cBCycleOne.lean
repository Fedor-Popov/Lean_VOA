import VOA.Huang.GenusOneG1cBCycle
import VOA.Huang.GenusOneG1Cycles

/-!
# The B-cycle of the vacuum channel at genus one (Huang Lemma 4.2 (4.11), real segment)

Genus-one half of step (c). Combining

* the categorical dictionary (`GenusOneG1cDictionary`: `Ψ_x = Σ_j Tr_{M_x} μ_j ν_j`),
* the B-cycle of the product channel (`GenusOneWard.prodLift_bcycle`: `q^{L₀}` conjugation and
  trace cyclicity turn `Tr_{M_x} μ_j(w_a, ·) ν_j(w_b, ·)` into
  `Tr_{M_{lab j}} ν_j(w_b, ·) μ_j(w_a, ·)`),
* the reversed four-point identity (`GenusOneG1cBCycle.reversed_fourPoint`),

we prove (`bcycle_vacuumChannel`): for every traced label `x`, on a real segment `0 < s < δ`,

  `e^{−2πiτα_a} Σ_j prodLift μ_j ν_j (ℓ₁ = −2πiτ, ℓ₂ = log(1+s))
     = Σ_z transferMatrix c β x z · Φ_z(s) + Σ_{j,k} R_{jk}(s)`,

where the left side is the product expansion of the vacuum channel `Ψ_x` (the same expansion that
equals the iterate `Ψ_x` near the collision, `vacuumChannel_eq_product`) at the B-translate
`ℓ₁ ↦ ℓ₁ − 2πiτ` of the near-collision point `(ℓ₁, ℓ₂) = (0, log(1+s))`;
`Φ_z(s) = Tr_{M_z} Y_{M_z}(Y^π(w_b, s) w_a, 1) q^{L₀ − c/24}` is the vacuum channel of the
REVERSED pair `(b, a)` traced over `M_z`; and every `R_{jk}` is an iterate channel through a summand
of `M_b ⊠ M_a` whose inner channel is orthogonal to the vacuum summand (`eta_remInner`).
The matrix that appears is exactly `transferMatrix c β`, i.e. the genus-zero B-transfer of
`VerlindeTransport` — this is the identification of the B-cycle matrix demanded by
`VacuumChannelTransportInput`, on a real segment, with the reversed-pair vacuum channels
`Φ_z` in place of `Ψ_z`.

Also `exists_vacuumRetraction`: a retraction `π` with `η ≫ π = 𝟙` exists (nice `W`).
-/

noncomputable section

namespace VOA.Huang.GenusOneG1c

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.FusionProduct VOA.Huang.FusionUnit
  VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion VOA.Huang.AssocTarget CategoryTheory
  Complex
open VOA.Huang.GenusTwoPoint (IterateSewingSummable ProductSewingSummable productTerm
  iterateTerm productCoeff iterateCoeff qFactor vacuumLW weightFunctional
  supportedAt_weightFunctional iterateCoeff_eq_sum_iterValue productCoeff_eq_sum_prodValue
  summable_iterate_q_of_sewing productQSummable_of_sewing)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]
variable (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

/-! ## §1 Existence of the vacuum retraction -/

/-- For nice `W` and a complete family, every nonzero `η : V → M_b ⊠ M_a` has a retraction. -/
theorem exists_vacuumRetraction (hNice : VOA.Classification.COne.Nice W) (hcomp : Complete D.Mfam)
    (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)) (hη : η ≠ 0) :
    ∃ π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject, η ≫ π = 𝟙 _ := by
  obtain ⟨r, lab, inc, proj, htot⟩ :=
    exists_split hNice.1 D hcomp (tensorObj F (famObj D b) (famObj D a))
  have hex : ∃ k, η ≫ proj k ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hη
    rw [← Category.comp_id η, ← htot, Preadditive.comp_sum]
    exact Finset.sum_eq_zero (fun k _ => by rw [← Category.assoc, hall k, Limits.zero_comp])
  obtain ⟨k, hk⟩ := hex
  obtain ⟨e0⟩ := hv0
  let I0 : famObj D v0 ≅ vacuumObject := Ordinary.isoOfModuleEquiv e0
  let φ : famObj D v0 ⟶ famObj D (lab k) := I0.hom ≫ η ≫ proj k
  have hφ : φ ≠ 0 := by
    intro h0
    apply hk
    have : I0.inv ≫ φ = η ≫ proj k := by simp only [φ, Iso.inv_hom_id_assoc]
    rw [← this, h0, Limits.comp_zero]
  have hφ' : φ.val ≠ 0 := fun h0 =>
    hφ (Ordinary.hom_ext _ _ (fun v => LinearMap.congr_fun h0 v))
  have hb := bijective_of_hom (D.Mfam v0).irreducible (D.Mfam (lab k)).irreducible
    φ.property hφ'
  let I := isoOfBijective φ hb
  refine ⟨proj k ≫ I.inv ≫ I0.hom, ?_⟩
  have hI : I.hom = φ := isoOfBijective_hom φ hb
  have h1 : η ≫ proj k = I0.inv ≫ I.hom := by
    rw [hI]; simp only [φ, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h1, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]

/-! ## §2 Coefficient and genus-one forms of the reversed identity -/

section Reversed

variable (hV : StronglyRational W) (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
  {β : ∀ x, Fin (c.r x) → ℂ} (hβ : IsTransferScalar F H c β)
  (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject)
  {r : ℕ} (lab' : Fin r → ι)
  (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D b) (famObj D a))
  (p : ∀ k, tensorObj F (famObj D b) (famObj D a) ⟶ famObj D (lab' k))
  (htot : ∑ k, p k ≫ i k = 𝟙 _)

include hV hβ htot in
/-- The reversed identity for every fixed-weight trace coefficient (real segment `0 < s < 1`). -/
theorem reversed_coeff (x : ι) (j : Fin (c.r x)) {αb αa : ℂ} {wb : (lwOf D b).carrier}
    {wa : (lwOf D a).carrier} (hwb : wb ∈ (lwOf D b).isMod.weight αb)
    (hwa : wa ∈ (lwOf D a).isMod.weight αa) (β₀ : ℂ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    productCoeff (Q := lwOf D x) (N := lwOf D (c.lab x j)) (nuInt F c x j) (muInt F H c x j)
        wb wa αb αa β₀ ((1 + s : ℝ) : ℂ) 1 =
      β x j * iterateCoeff (Q := vacuumLW W hv) (N := lwOf D (c.lab x j))
        (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π) wb wa αb αa β₀ (s : ℂ) 1 +
      ∑ k, iterateCoeff (Q := lwOf D (lab' k)) (N := lwOf D (c.lab x j))
        (remOuter F H c x j lab' i k) (remInner F c π lab' p k) wb wa αb αa β₀ (s : ℂ) 1 := by
  classical
  letI := (lwOf D (c.lab x j)).isMod.finrank β₀
  let bs := Module.finBasis ℂ ((lwOf D (c.lab x j)).isMod.weight β₀)
  have hs0' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsn : ‖(s : ℂ)‖ < ‖(1 : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs0.le, norm_one]; exact hs1
  have hpn : ‖(1 : ℂ)‖ < ‖((1 + s : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_one]; linarith
  have iL := lwOf_irreducible D (c.lab x j)
  rw [productCoeff_eq_sum_prodValue hV (lwOf_irreducible D b) (lwOf_irreducible D a) iL _ _
    hwb hwa β₀ bs one_ne_zero hpn,
    iterateCoeff_eq_sum_iterValue hV (lwOf_irreducible D b) (lwOf_irreducible D a) iL _ _
      hwb hwa β₀ bs hs0' hsn]
  simp_rw [iterateCoeff_eq_sum_iterValue hV (lwOf_irreducible D b) (lwOf_irreducible D a) iL _ _
      hwb hwa β₀ bs hs0' hsn]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ), Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  let d : AssocConverse.TestData (lwOf D b) (lwOf D a) (lwOf D (c.lab x j))
      (lwOf D (c.lab x j)) :=
    ⟨αb, αa, β₀, β₀, wb, wa, bs t, weightFunctional (lwOf D (c.lab x j)).isMod β₀ bs t, hwb, hwa,
      (bs t).property, supportedAt_weightFunctional (lwOf D (c.lab x j)).isMod β₀ bs t, s, hs0,
      hs1⟩
  have h := reversed_fourPoint F H hV hv c hβ π x j lab' i p htot d
  simp only [iterateValue_eq_iterValue, productValue_eq_prodValue] at h
  have hσ : αb + αa + β₀ - β₀ - 2 = αb + αa - 2 := by ring
  have hcast : ((1 + s : ℝ) : ℂ) = 1 + (s : ℂ) := by push_cast; ring
  rw [hcast]
  simpa only [d, hσ] using h

/-- A positive real below finitely many positive reals. -/
theorem exists_pos_le_fin {r : ℕ} (f : Fin r → ℝ) (hf : ∀ k, 0 < f k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k, δ ≤ f k := by
  refine ⟨1 / (1 + ∑ k, 1 / f k), ?_, fun k => ?_⟩
  · have : 0 ≤ ∑ k, 1 / f k := Finset.sum_nonneg fun k _ => (one_div_pos.mpr (hf k)).le
    positivity
  · have hS : 1 / f k ≤ ∑ k, 1 / f k :=
      Finset.single_le_sum (f := fun k => 1 / f k) (fun k _ => (one_div_pos.mpr (hf k)).le)
        (Finset.mem_univ k)
    have h1 : 0 < 1 + ∑ k, 1 / f k := by linarith [(one_div_pos.mpr (hf k)).le]
    rw [div_le_iff₀ h1]
    have := hf k
    calc 1 = f k * (1 / f k) := by field_simp
      _ ≤ f k * (1 + ∑ k, 1 / f k) := mul_le_mul_of_nonneg_left (by linarith) this.le

include hV hβ htot in
/-- **The reversed identity at genus one** (real segment): the reversed product channel
`Tr_{M_{lab j}} ν_j(w_b, 1 + s) μ_j(w_a, 1) q^{L₀−c/24}` equals `β_{xj}` times the reversed-pair
vacuum channel plus the non-vacuum iterate channels, all absolutely convergent. -/
theorem reversed_genusOne (x : ι) (j : Fin (c.r x)) {αb αa : ℂ} {wb : (lwOf D b).carrier}
    {wa : (lwOf D a).carrier} (hwb : wb ∈ (lwOf D b).isMod.weight αb)
    (hwa : wa ∈ (lwOf D a).isMod.weight αa) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      prodF (Q := lwOf D x) (N := lwOf D (c.lab x j)) (nuInt F c x j) (muInt F H c x j)
          wb wa αb αa τ ((1 + s : ℝ) : ℂ) =
        β x j * iterF (Q := vacuumLW W hv) (N := lwOf D (c.lab x j))
          (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π) wb wa αb αa τ (s : ℂ) +
        ∑ k, iterF (Q := lwOf D (lab' k)) (N := lwOf D (c.lab x j))
          (remOuter F H c x j lab' i k) (remInner F c π lab' p k) wb wa αb αa τ (s : ℂ) := by
  have iQ0 : (vacuumLW W hv).IsIrreducibleLW :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hV.simple
  have iL := lwOf_irreducible D (c.lab x j)
  obtain ⟨δ0, hδ0, -, h0⟩ := GenusOneG1b.exists_iterateSewingRadius_holds hV
    (lwOf_irreducible D b) (lwOf_irreducible D a) iL iQ0
    (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π) hwb hwa τ
  have hk := fun k => GenusOneG1b.exists_iterateSewingRadius_holds hV
    (lwOf_irreducible D b) (lwOf_irreducible D a) iL (lwOf_irreducible D (lab' k))
    (remOuter F H c x j lab' i k) (remInner F c π lab' p k) hwb hwa τ
  choose δk hδk _ hks using hk
  obtain ⟨δK, hδK, hδKle⟩ := exists_pos_le_fin δk hδk
  have hq1 : ‖qParam τ‖ < 1 := norm_qParam_lt_one τ
  have hq0 : 0 ≤ ‖qParam τ‖ := norm_nonneg _
  set δq : ℝ := (1 - ‖qParam τ‖) / 2 with hδq
  have hδq0 : 0 < δq := by rw [hδq]; linarith
  refine ⟨min (min δ0 δK) (min δq (1 / 2)), lt_min (lt_min hδ0 hδK) (lt_min hδq0 (by norm_num)),
    fun s hs0 hs => ?_⟩
  have hsδ0 : s < δ0 := lt_of_lt_of_le hs ((min_le_left _ _).trans (min_le_left _ _))
  have hsδK : s < δK := lt_of_lt_of_le hs ((min_le_left _ _).trans (min_le_right _ _))
  have hsδq : s < δq := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _))
  have hs1 : s < 1 := by
    have := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_right _ _)); linarith
  have hs0' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsn : ‖(s : ℂ) / 1‖ = s := by
    rw [div_one, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  -- summabilities
  have hI0 : IterateSewingSummable (Q := vacuumLW W hv) (N := lwOf D (c.lab x j))
      (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π) wb wa αb αa (s : ℂ) 1 τ :=
    h0 _ 1 hs0' one_ne_zero (by rw [hsn]; exact hsδ0)
  have hIk : ∀ k, IterateSewingSummable (Q := lwOf D (lab' k)) (N := lwOf D (c.lab x j))
      (remOuter F H c x j lab' i k) (remInner F c π lab' p k) wb wa αb αa (s : ℂ) 1 τ :=
    fun k => hks k _ 1 hs0' one_ne_zero (by rw [hsn]; exact lt_of_lt_of_le hsδK (hδKle k))
  have hnorm1 : ‖((1 + s : ℝ) : ℂ)‖ = 1 + s := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hP : ProductSewingSummable (Q := lwOf D x) (N := lwOf D (c.lab x j)) (nuInt F c x j)
      (muInt F H c x j) wb wa αb αa ((1 + s : ℝ) : ℂ) 1 τ := by
    refine GenusOneWard.productSewingSummable_holds _ _ hV (lwOf_irreducible D b)
      (lwOf_irreducible D a) iL hwb hwa one_ne_zero ?_ τ ?_
    · rw [norm_one, hnorm1]; linarith
    · rw [norm_one, hnorm1]
      have h1 : ‖qParam τ‖ * (1 + s) ≤ ‖qParam τ‖ * (1 + δq) :=
        mul_le_mul_of_nonneg_left (by linarith) hq0
      have h2 : ‖qParam τ‖ * (1 + δq) < 1 := by rw [hδq]; nlinarith
      linarith
  -- reduce to q-series of coefficients
  unfold prodF iterF
  rw [GenusOneG1b.tsum_pair_eq (f := fun n k => productTerm (Q := lwOf D x)
      (N := lwOf D (c.lab x j)) (nuInt F c x j) (muInt F H c x j) wb wa αb αa
      ((lwOf D (c.lab x j)).h + n) ((1 + s : ℝ) : ℂ) 1 k)
    (g := qFactor (lwOf D (c.lab x j)) τ) hP,
    GenusOneG1b.tsum_pair_eq (f := fun n k => iterateTerm (Q := vacuumLW W hv)
      (N := lwOf D (c.lab x j)) (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π)
      wb wa αb αa ((lwOf D (c.lab x j)).h + n) (s : ℂ) 1 k)
    (g := qFactor (lwOf D (c.lab x j)) τ) hI0]
  have hR : ∀ k, ∑' e : ℕ × ℕ, iterateTerm (Q := lwOf D (lab' k)) (N := lwOf D (c.lab x j))
      (remOuter F H c x j lab' i k) (remInner F c π lab' p k) wb wa αb αa
      ((lwOf D (c.lab x j)).h + e.1) (s : ℂ) 1 e.2 * qFactor (lwOf D (c.lab x j)) τ e.1 =
      ∑' n : ℕ, iterateCoeff (Q := lwOf D (lab' k)) (N := lwOf D (c.lab x j))
        (remOuter F H c x j lab' i k) (remInner F c π lab' p k) wb wa αb αa
        ((lwOf D (c.lab x j)).h + n) (s : ℂ) 1 * qFactor (lwOf D (c.lab x j)) τ n := fun k =>
    GenusOneG1b.tsum_pair_eq (f := fun n m => iterateTerm (Q := lwOf D (lab' k))
      (N := lwOf D (c.lab x j)) (remOuter F H c x j lab' i k) (remInner F c π lab' p k)
      wb wa αb αa ((lwOf D (c.lab x j)).h + n) (s : ℂ) 1 m)
      (g := qFactor (lwOf D (c.lab x j)) τ) (hIk k)
  simp only [hR]
  change ∑' n : ℕ, productCoeff (Q := lwOf D x) (N := lwOf D (c.lab x j)) (nuInt F c x j)
      (muInt F H c x j) wb wa αb αa ((lwOf D (c.lab x j)).h + n) ((1 + s : ℝ) : ℂ) 1 *
        qFactor (lwOf D (c.lab x j)) τ n = _
  simp only [reversed_coeff F H hV hv c hβ π lab' i p htot x j hwb hwa _ s hs0 hs1, add_mul,
    Finset.sum_mul, mul_assoc]
  have hS0 := summable_iterate_q_of_sewing _ _ _ _ _ _ _ _ τ hI0
  have hSk := fun k => summable_iterate_q_of_sewing _ _ _ _ _ _ _ _ τ (hIk k)
  rw [Summable.tsum_add (hS0.mul_left (β x j))
      (summable_sum fun k _ => hSk k), tsum_mul_left,
    Summable.tsum_finsetSum fun k _ => hSk k]
  rfl

/-- The product channel on the universal cover at `(log z₁, log 1)` is `prodF` at `z₁`. -/
theorem prodLift_log_one {P₁ P₂ N Q : LWModule W}
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod) (x : P₁.carrier) (y : P₂.carrier)
    (α₁ α₂ : ℂ) (τ : UpperHalfPlane) {z₁ : ℂ} (hz₁ : z₁ ≠ 0) :
    GenusOneWard.prodLift Y₁ Y₂ x y α₁ α₂ (log z₁) 0 τ = prodF Y₁ Y₂ x y α₁ α₂ τ z₁ := by
  unfold GenusOneWard.prodLift prodF
  rw [← Complex.log_one]
  exact tsum_congr fun e => GenusOneWard.liftTerm_log_eq Y₁ Y₂ hz₁ one_ne_zero x y α₁ α₂ τ e

/-- Grouping the vacuum terms by label produces `transferMatrix`. -/
theorem sum_group_transfer (c : TransferChoice F D a b) (β : ∀ x, Fin (c.r x) → ℂ) (x : ι)
    (Φ : ι → ℂ) :
    ∑ j, β x j * Φ (c.lab x j) = ∑ z, transferMatrix c β x z * Φ z := by
  unfold transferMatrix
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq]
  simp

include hV hβ htot in
/-- **The B-cycle of the vacuum channel (Huang Lemma 4.2 (4.11), genus one, real segment).**
The product expansion of `Ψ_x = Σ_j Tr_{M_x} μ_j(w_a, ·) ν_j(w_b, ·)` (absolutely convergent at the
point below), taken at the B-translate `ℓ₁ = −2πiτ` of the near-collision point
`(ℓ₁, ℓ₂) = (0, log(1+s))` and multiplied by `e^{−2πiτα_a}`, equals
`Σ_z transferMatrix c β x z · Φ_z(s)` — `Φ_z` the vacuum channel of the reversed pair `(b, a)`
traced over `M_z` — plus iterate channels `R_{jk}` whose inner channels are orthogonal to the
vacuum summand of `M_b ⊠ M_a` (`eta_remInner`). -/
theorem bcycle_vacuumChannel (x : ι) {αa αb : ℂ} {wa : (lwOf D a).carrier}
    {wb : (lwOf D b).carrier} (hwa : wa ∈ (lwOf D a).isMod.weight αa)
    (hwb : wb ∈ (lwOf D b).isMod.weight αb) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      (∀ j, Summable (GenusOneWard.liftTerm (Q := lwOf D (c.lab x j)) (N := lwOf D x)
        (muInt F H c x j) (nuInt F c x j) wa wb αa αb (-(2 * (Real.pi : ℂ) * I * τ))
        (log ((1 + s : ℝ) : ℂ)) τ)) ∧
      exp (-(2 * (Real.pi : ℂ) * I * τ * αa)) *
          ∑ j, GenusOneWard.prodLift (Q := lwOf D (c.lab x j)) (N := lwOf D x)
            (muInt F H c x j) (nuInt F c x j) wa wb αa αb (-(2 * (Real.pi : ℂ) * I * τ))
            (log ((1 + s : ℝ) : ℂ)) τ =
        ∑ z, transferMatrix c β x z * iterF (Q := vacuumLW W hv) (N := lwOf D z)
          (moduleIntertwiner (lwOf D z).isMod) (piInt F π) wb wa αb αa τ (s : ℂ) +
        ∑ j, ∑ k, iterF (Q := lwOf D (lab' k)) (N := lwOf D (c.lab x j))
          (remOuter F H c x j lab' i k) (remInner F c π lab' p k) wb wa αb αa τ (s : ℂ) := by
  have hj := fun j => reversed_genusOne F H hV hv c hβ π lab' i p htot x j hwb hwa τ
  choose δj hδj hrev using hj
  obtain ⟨δJ, hδJ, hδJle⟩ := exists_pos_le_fin δj hδj
  have him : 0 < (τ : ℂ).im := τ.im_pos
  set E : ℝ := Real.exp (2 * Real.pi * (τ : ℂ).im) - 1 with hE
  have hE0 : 0 < E := by
    rw [hE]; have : 1 < Real.exp (2 * Real.pi * (τ : ℂ).im) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  refine ⟨min δJ E, lt_min hδJ hE0, fun s hs0 hs => ⟨fun j => ?_, ?_⟩⟩
  · have hsE : s < E := lt_of_lt_of_le hs (min_le_right _ _)
    have hre1 : (-(2 * (Real.pi : ℂ) * I * τ)).re = 2 * Real.pi * (τ : ℂ).im := by
      simp [Complex.mul_re, Complex.mul_im]
    have hre2 : (log ((1 + s : ℝ) : ℂ)).re = Real.log (1 + s) := by
      rw [Complex.log_re, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have h1s : 0 < 1 + s := by linarith
    refine GenusOneWard.summable_liftTerm _ _ hV (lwOf_irreducible D a) (lwOf_irreducible D b)
      (lwOf_irreducible D x) hwa hwb _ _ τ ?_ ?_
    · rw [hre1, hre2]
      have : 1 + s < Real.exp (2 * Real.pi * (τ : ℂ).im) := by rw [hE] at hsE; linarith
      have := Real.log_lt_log h1s this
      rwa [Real.log_exp] at this
    · rw [hre1, hre2, Real.exp_log h1s]
      have hq : ‖qParam τ‖ = Real.exp (-(2 * Real.pi * (τ : ℂ).im)) := by
        rw [qParam, Complex.norm_exp]
        congr 1
        simp [Complex.mul_re, Complex.mul_im]
      rw [hq, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
      linarith
  · have hsJ : ∀ j, s < δj j := fun j => lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_left _ _))
      (hδJle j)
    have h1s : ((1 + s : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 1 + s := by linarith
      exact_mod_cast this.ne'
    have hB : ∀ j, exp (-(2 * (Real.pi : ℂ) * I * τ * αa)) *
        GenusOneWard.prodLift (Q := lwOf D (c.lab x j)) (N := lwOf D x)
          (muInt F H c x j) (nuInt F c x j) wa wb αa αb (-(2 * (Real.pi : ℂ) * I * τ))
          (log ((1 + s : ℝ) : ℂ)) τ =
        prodF (Q := lwOf D x) (N := lwOf D (c.lab x j)) (nuInt F c x j) (muInt F H c x j)
          wb wa αb αa τ ((1 + s : ℝ) : ℂ) := by
      intro j
      rw [← GenusOneWard.prodLift_bcycle (muInt F H c x j) (nuInt F c x j) hwa hwb, neg_add_cancel,
        prodLift_log_one _ _ _ _ _ _ τ h1s]
    rw [Finset.mul_sum]
    simp only [hB]
    simp only [fun j => hrev j s hs0 (hsJ j)]
    rw [Finset.sum_add_distrib]
    congr 1
    exact sum_group_transfer F c β x (fun z => iterF (Q := vacuumLW W hv) (N := lwOf D z)
      (moduleIntertwiner (lwOf D z).isMod) (piInt F π) wb wa αb αa τ (s : ℂ))

end Reversed

end VOA.Huang.GenusOneG1c
