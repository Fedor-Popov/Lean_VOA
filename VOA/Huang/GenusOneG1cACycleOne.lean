import VOA.Huang.GenusOneG1cACycle

/-!
# The A-cycle of the vacuum channel at genus one, and `Ω_{v0} ≠ 0`

* `exists_vacuumSection`: a section `η'` of `ε` (`η' ≫ ε = 𝟙`) exists (nice `W`, complete family).
* `acycle_nonvacuum_genusOne`: `Σ_j (aPhase_j − Ω_x) Tr_{M_x} μ_j(w_a, 1+z₀) ν_j(w_b, 1)
  = Σ_k R_k(z₀)` on the complex half-disc (from `acycle_fourPoint` minus `Ω_x · vacuum_fourPoint`,
  through `coeff_of_fourPoint` and `genusOne_of_coeff`).
* `acycle_vacuumChannel_complex` (Huang Lemma 4.2 (4.10)): the A-cycle `ℓ₂ ↦ ℓ₂ + 2πi` of the
  product expansion of `Ψ_x` at `(log(1 + z₀), 0)` equals `Ω_x · Ψ_x(z₀) + Σ_k R_k(z₀)`, where
  `Ψ_x = iterF Y_{M_x} (epsInt c)` is the vacuum channel itself and every `R_k` is an iterate
  channel whose inner channel is orthogonal to the vacuum summand of `M_a ⊠ M_b`
  (`eta_aRemInner`).
* `aCycleScalar_vacuum_ne_zero`: for the vacuum label, `Ω_{v0} = e^{2πi(h_b − h_{v0} − γ)} ≠ 0`
  (every summand of `M_b ⊠ M_{v0}` is labelled `b`, so `T_{v0}` is a scalar).
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

/-- A section of a nonzero `ε : M_a ⊠ M_b → V` exists. -/
theorem exists_vacuumSection (hNice : VOA.Classification.COne.Nice W) (hcomp : Complete D.Mfam)
    (v0 : ι) (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (ε : tensorObj F (famObj D a) (famObj D b) ⟶ vacuumObject) (hε : ε ≠ 0) :
    ∃ η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b), η' ≫ ε = 𝟙 _ := by
  obtain ⟨r, lab, inc, proj, htot⟩ :=
    exists_split hNice.1 D hcomp (tensorObj F (famObj D a) (famObj D b))
  have hex : ∃ j, inc j ≫ ε ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hε
    rw [← Category.id_comp ε, ← htot, Preadditive.sum_comp]
    exact Finset.sum_eq_zero (fun j _ => by rw [Category.assoc, hall j, Limits.comp_zero])
  obtain ⟨j, hj⟩ := hex
  obtain ⟨e0⟩ := hv0
  let I0 : famObj D v0 ≅ vacuumObject := Ordinary.isoOfModuleEquiv e0
  let φ : famObj D (lab j) ⟶ famObj D v0 := inc j ≫ ε ≫ I0.inv
  have hφ : φ ≠ 0 := by
    intro h0
    apply hj
    have hφI : φ ≫ I0.hom = inc j ≫ ε := by
      simp only [φ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hφI, h0, Limits.zero_comp]
  have hφ' : φ.val ≠ 0 := fun h0 =>
    hφ (Ordinary.hom_ext _ _ (fun v => LinearMap.congr_fun h0 v))
  have hb := bijective_of_hom (D.Mfam (lab j)).irreducible (D.Mfam v0).irreducible
    φ.property hφ'
  let I := isoOfBijective φ hb
  have hI : I.inv ≫ φ = 𝟙 _ := by
    rw [← isoOfBijective_hom φ hb]
    exact I.inv_hom_id
  refine ⟨I0.inv ≫ I.inv ≫ inc j, ?_⟩
  have : I0.inv ≫ (I.inv ≫ φ) ≫ I0.hom = 𝟙 _ := by
    rw [hI, Category.id_comp, Iso.inv_hom_id]
  rw [← this]
  simp only [φ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

section ACycle

variable (hV : StronglyRational W) (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
  {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)} {γ : ℂ}
  {Ω : ι → ℂ} (hΩ : IsACycleScalar F H c η' γ Ω)
  {r : ℕ} (lab' : Fin r → ι)
  (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D a) (famObj D b))
  (p : ∀ k, tensorObj F (famObj D a) (famObj D b) ⟶ famObj D (lab' k))
  (htot : ∑ k, p k ≫ i k = 𝟙 _)

include hV hv hΩ htot in
/-- The A-transported vacuum channel minus `Ω_x` times the vacuum channel, in product form, is
a sum of non-vacuum iterate channels (genus one, complex half-disc). -/
theorem acycle_nonvacuum_genusOne (x : ι) {αa αb : ℂ} {wa : (lwOf D a).carrier}
    {wb : (lwOf D b).carrier} (hwa : wa ∈ (lwOf D a).isMod.weight αa)
    (hwb : wb ∈ (lwOf D b).isMod.weight αb) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ : ℂ, 0 < z₀.re → ‖z₀‖ < δ →
      ∑ j, (aPhase F c γ x j - Ω x) * prodF (Q := lwOf D (c.lab x j)) (N := lwOf D x)
          (muInt F H c x j) (nuInt F c x j) wa wb αa αb τ (1 + z₀) =
        ∑ k, 1 * iterF (Q := lwOf D (lab' k)) (N := lwOf D x) (aRemOuter F H c γ x lab' i k)
          (aRemInner F c η' lab' p k) wa wb αa αb τ z₀ := by
  have h4 : ∀ d : AssocConverse.TestData (lwOf D a) (lwOf D b) (lwOf D x) (lwOf D x),
      ∑ j, (aPhase F c γ x j - Ω x) * AssocConverse.productValue (Q := lwOf D (c.lab x j))
        (muInt F H c x j) (nuInt F c x j) d =
      ∑ k, 1 * AssocConverse.iterateValue (Q := lwOf D (lab' k)) (aRemOuter F H c γ x lab' i k)
        (aRemInner F c η' lab' p k) d := by
    intro d
    have hA := acycle_fourPoint F H hV hv c hΩ x lab' i p htot d
    have hvac := vacuum_fourPoint F H hV hv c x d
    simp only [sub_mul, Finset.sum_sub_distrib, one_mul, hA, ← Finset.mul_sum, hvac]
    ring
  obtain ⟨δ, hδ, hres⟩ := genusOne_of_coeff (fun j => muInt F H c x j) (fun j => nuInt F c x j)
    (fun k => aRemOuter F H c γ x lab' i k) (fun k => aRemInner F c η' lab' p k)
    (fun j => aPhase F c γ x j - Ω x) (fun _ => 1) hV (lwOf_irreducible D a)
    (lwOf_irreducible D b) (lwOf_irreducible D x) (fun k => lwOf_irreducible D (lab' k))
    hwa hwb τ ⟨1, one_pos, fun s hs0 hs1 n => coeff_of_fourPoint _ _ _ _ _ _ hV
      (lwOf_irreducible D a) (lwOf_irreducible D b) (lwOf_irreducible D x) h4 hwa hwb _ s hs0
      hs1⟩
  exact ⟨δ, hδ, fun z₀ hre hn => (hres z₀ hre hn).2.2⟩

include hV hΩ htot in
/-- **The A-cycle of the vacuum channel (Huang Lemma 4.2 (4.10)), genus one, half-disc.**
With `γ = α_b`: `Σ_j prodLift μ_j ν_j (log(1+z₀), 2πi) = Ω_x · Ψ_x(z₀) + Σ_k R_k(z₀)`. -/
theorem acycle_vacuumChannel_complex (x : ι) {αa : ℂ} {wa : (lwOf D a).carrier}
    {wb : (lwOf D b).carrier} (hwa : wa ∈ (lwOf D a).isMod.weight αa)
    (hwb : wb ∈ (lwOf D b).isMod.weight γ) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ : ℂ, 0 < z₀.re → ‖z₀‖ < δ →
      ∑ j, GenusOneWard.prodLift (Q := lwOf D (c.lab x j)) (N := lwOf D x)
          (muInt F H c x j) (nuInt F c x j) wa wb αa γ (log (1 + z₀))
          (2 * (Real.pi : ℂ) * I) τ =
        Ω x * iterF (Q := vacuumLW W hv) (N := lwOf D x) (moduleIntertwiner (lwOf D x).isMod)
          (epsInt F c) wa wb αa γ τ z₀ +
        ∑ k, iterF (Q := lwOf D (lab' k)) (N := lwOf D x) (aRemOuter F H c γ x lab' i k)
          (aRemInner F c η' lab' p k) wa wb αa γ τ z₀ := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := acycle_nonvacuum_genusOne F H hV hv c hΩ lab' i p htot x hwa hwb τ
  obtain ⟨δ₂, hδ₂, h₂⟩ := vacuumChannel_eq_product F H hV hv c x hwa hwb τ
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun z₀ hre hn => ?_⟩
  have e1 := h₁ z₀ hre (lt_of_lt_of_le hn (min_le_left _ _))
  have e2 := (h₂ z₀ hre (lt_of_lt_of_le hn (min_le_right _ _))).2.2
  have h1z : (1 + z₀) ≠ 0 := by
    intro h; have := one_lt_norm_one_add hre; rw [h, norm_zero] at this; linarith
  have hA : ∀ j, GenusOneWard.prodLift (Q := lwOf D (c.lab x j)) (N := lwOf D x)
      (muInt F H c x j) (nuInt F c x j) wa wb αa γ (log (1 + z₀)) (2 * (Real.pi : ℂ) * I) τ =
      aPhase F c γ x j * prodF (Q := lwOf D (c.lab x j)) (N := lwOf D x)
        (muInt F H c x j) (nuInt F c x j) wa wb αa γ τ (1 + z₀) := by
    intro j
    have h := GenusOneWard.prodLift_acycle_right (muInt F H c x j) (nuInt F c x j) wa wb αa γ
      (log (1 + z₀)) 0 τ
    rw [zero_add, prodLift_log_one _ _ _ _ _ _ τ h1z] at h
    rw [h]
    rfl
  simp only [hA]
  simp only [one_mul] at e1
  rw [e2, ← e1, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

end ACycle

/-! ## `Ω_{v0} ≠ 0` -/

/-- Every nonzero summand of `M_b ⊠ M_{v0}` is labelled `b`. -/
theorem lab_eq_of_vacuum (hirr : Irredundant D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (c : TransferChoice F D a b) (j : Fin (c.r v0)) (hj : c.inc v0 j ≠ 0) :
    c.lab v0 j = b := by
  obtain ⟨e0⟩ := hv0
  let I0 : famObj D v0 ≅ vacuumObject := Ordinary.isoOfModuleEquiv e0
  let J : tensorObj F (famObj D b) (famObj D v0) ⟶ famObj D b :=
    tensorHom F (𝟙 _) I0.hom ≫ (rightUnitor F (famObj D b)).hom
  let J' : famObj D b ⟶ tensorObj F (famObj D b) (famObj D v0) :=
    (rightUnitor F (famObj D b)).inv ≫ tensorHom F (𝟙 _) I0.inv
  have hJ : J ≫ J' = 𝟙 _ := by
    simp only [J, J', Category.assoc, Iso.hom_inv_id_assoc]
    rw [← TensorCat.tensorHom_comp, Category.id_comp, Iso.hom_inv_id, TensorCat.tensorHom_id]
  let φ : famObj D (c.lab v0 j) ⟶ famObj D b := c.inc v0 j ≫ J
  have hφ : φ ≠ 0 := by
    intro h0
    apply hj
    have : φ ≫ J' = c.inc v0 j := by simp only [φ, Category.assoc, hJ, Category.comp_id]
    rw [← this, h0, Limits.zero_comp]
  have hφ' : φ.val ≠ 0 := fun h0 =>
    hφ (Ordinary.hom_ext _ _ (fun v => LinearMap.congr_fun h0 v))
  have hb := bijective_of_hom (D.Mfam (c.lab v0 j)).irreducible (D.Mfam b).irreducible
    φ.property hφ'
  exact hirr _ _ ⟨moduleEquivOfBijective φ hb⟩

/-- **`Ω_{v0} ≠ 0`**: for the vacuum label the A-cycle scalar is the phase
`e^{2πi(h_b − h_{v0} − γ)}`. -/
theorem aCycleScalar_vacuum (hirr : Irredundant D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (c : TransferChoice F D a b)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (hη' : η' ≫ c.ε = 𝟙 _) {γ : ℂ} {Ω : ι → ℂ} (hΩ : IsACycleScalar F H c η' γ Ω) :
    Ω v0 = exp (2 * (Real.pi : ℂ) * I * (D.h b - D.h v0 - γ)) := by
  set t := exp (2 * (Real.pi : ℂ) * I * (D.h b - D.h v0 - γ)) with ht
  have hT : aTwist F c γ v0 = t • 𝟙 _ := by
    unfold aTwist
    rw [← c.total v0, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : c.inc v0 j = 0
    · rw [hj, Limits.comp_zero, smul_zero, smul_zero]
    · rw [show aPhase F c γ v0 j = t by
        unfold aPhase; rw [lab_eq_of_vacuum F hirr v0 hv0 c j hj]]
  have hΩv := hΩ v0
  unfold aHom at hΩv
  rw [hT, TensorCat.tensorHom_smul_right, TensorCat.tensorHom_id, Linear.smul_comp,
    Category.id_comp, Linear.comp_smul, Linear.comp_smul, Linear.comp_smul,
    assoc_vacuumProduct, ← Category.assoc (tensorHom F η' _), ← TensorCat.tensorHom_comp,
    Category.id_comp, hη', TensorCat.tensorHom_id, Category.id_comp, Iso.inv_hom_id] at hΩv
  exact (smul_id_cancel D v0 hΩv).symm

theorem aCycleScalar_vacuum_ne_zero (hirr : Irredundant D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (c : TransferChoice F D a b)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (hη' : η' ≫ c.ε = 𝟙 _) {γ : ℂ} {Ω : ι → ℂ} (hΩ : IsACycleScalar F H c η' γ Ω) :
    Ω v0 ≠ 0 := by
  rw [aCycleScalar_vacuum F H hirr v0 hv0 c hη' hΩ]
  exact exp_ne_zero _

end VOA.Huang.GenusOneG1c
