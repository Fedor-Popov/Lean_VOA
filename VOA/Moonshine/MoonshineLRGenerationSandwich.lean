import VOA.Moonshine.MoonshineLRGenerationQuotientData

/-!
# The character identity in KNZ form, and the dimension sandwich

For Borcherds data `D` with a normalised real pair:
* `finrank_positiveGenWeight`: `dim U_(a,b) = dim 𝔤_(1, a+b−1)` on the cone, `0` off it;
* **`coneProd_neg_mul_knzSeries`**:
  `Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{−dim 𝔤_(m,n)} · (1 − Σ dim 𝔤_(1,a+b−1) pᵃ q^b) = 1`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open Module

/-- The product depends only on the exponents with `m, n ≥ 1`. -/
theorem coneProd_congr {e₁ e₂ : ℕ → ℕ → ℂ} (h : ∀ m n, 0 < m → 0 < n → e₁ m n = e₂ m n) :
    coneProd e₁ = coneProd e₂ := by
  have hL : coneLog e₁ = coneLog e₂ := by
    refine PowerSeries.ext fun a => ?_
    simp only [coneLog, PowerSeries.coeff_mk, coneLogCoeff]
    congr 2
    refine PowerSeries.ext fun b => ?_
    simp only [PowerSeries.coeff_mk]
    refine Finset.sum_congr rfl fun m hm => ?_
    split_ifs with hc
    · have hmpos := Nat.pos_of_mem_divisors hm
      have hq : 0 < a / m := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (fun ha => by
        simp [ha] at hm)) (Nat.dvd_of_mem_divisors hm)) hmpos
      rw [h m (b / (a / m)) hmpos (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hc.2) hc.1) hq)]
    · rfl
  rw [coneProd, coneProd, hL]

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

theorem weightSpace_le_positivePart {γ : ℤ × ℤ} (hγ : borcherdsPositiveCone γ) :
    D.weightSpace γ ≤ D.positivePart.toSubmodule :=
  (le_iSup₂_of_le γ hγ le_rfl : D.weightSpace γ ≤ D.weightSpan borcherdsPositiveCone)

theorem natWeight_cone {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    borcherdsPositiveCone (natWeight (m, n)) := by
  simp only [borcherdsPositiveCone, natWeight]
  omega

theorem finrank_positiveWeight {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    finrank ℂ (positiveWeight D (m, n)) = finrank ℂ (D.weightSpace (natWeight (m, n))) :=
  (Submodule.comapSubtypeEquivOfLe
    (weightSpace_le_positivePart D (natWeight_cone hm hn))).finrank_eq

theorem positiveWeight_eq_bot {γ : ℕ × ℕ} (hγ : ¬ (1 ≤ γ.1 ∧ 1 ≤ γ.2)) :
    positiveWeight D γ = ⊥ := by
  by_contra h
  exact hγ (positiveWeight_cone D γ h)

/-- The image of `U_γ` in `g` is `genSpace e ⊓ g_γ`. -/
theorem map_positiveGenWeight (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot) (γ : ℕ × ℕ) :
    (positiveGenWeight D e γ).map (D.positivePart.toSubmodule.subtype ∘ₗ
        (D.positiveGeneratorSpace e).subtype) =
      D.genSpace e ⊓ D.weightSpace (natWeight γ) := by
  ext v
  simp only [Submodule.mem_map, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hU, hw⟩
    exact ⟨⟨⟨v, D.genSpace_le_positive e he hU⟩, hU⟩, hw, rfl⟩

theorem finrank_positiveGenWeight_eq (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    (γ : ℕ × ℕ) :
    finrank ℂ (positiveGenWeight D e γ) =
      finrank ℂ (D.genSpace e ⊓ D.weightSpace (natWeight γ) : Submodule ℂ g) := by
  rw [← map_positiveGenWeight D e he γ]
  refine (Submodule.equivMapOfInjective _ ?_ _).finrank_eq
  intro x y h
  exact Subtype.ext (Subtype.ext h)

/-- **`dim U_(a,b) = dim 𝔤_(1, a+b−1)`** on the cone, `0` off it. -/
theorem finrank_positiveGenWeight (e f : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) (a b : ℕ) :
    finrank ℂ (positiveGenWeight D e (a, b)) =
      if 1 ≤ a ∧ 1 ≤ b then finrank ℂ (D.weightSpace (1, ((a + b - 1 : ℕ) : ℤ))) else 0 := by
  split_ifs with hab
  · obtain ⟨ha, hb⟩ := hab
    let i : borcherdsStringIndex := ⟨(((a + b - 1 : ℕ) : ℤ), a - 1), by
      constructor <;> push_cast [Nat.cast_sub (show 1 ≤ a + b by omega),
        Nat.cast_sub ha] <;> omega⟩
    have hdeg : borcherdsStringDegree i = natWeight (a, b) := by
      simp only [borcherdsStringDegree, natWeight, i]
      ext <;> push_cast [Nat.cast_sub (show 1 ≤ a + b by omega), Nat.cast_sub ha] <;> ring
    rw [finrank_positiveGenWeight_eq D e he, ← hdeg, D.genSpace_weight_intersection e he i,
      D.generatorString_finrank e f he hf hef _ i.property.1 _ i.property.2]
    rfl
  · rw [show positiveGenWeight D e (a, b) = ⊥ from by
      rw [positiveGenWeight, positiveWeight_eq_bot D hab, Submodule.comap_bot,
        Submodule.ker_subtype], finrank_bot]

/-- `1 − ch U` is the KNZ series of the simple imaginary root dimensions. -/
theorem one_sub_finrankSeries_positiveGenWeight (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) :
    1 - finrankSeries (positiveGenWeight D e) =
      knzSeries fun j => (finrank ℂ (D.weightSpace (1, (j : ℤ))) : ℂ) := by
  refine PowerSeries.ext fun a => ?_
  rw [map_sub, PowerSeries.coeff_one, finrankSeries, knzSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk, knzCoeff]
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl, if_pos rfl]
    have h0 : (PowerSeries.mk fun b => (finrank ℂ (positiveGenWeight D e (0, b)) : ℂ)) = 0 := by
      refine PowerSeries.ext fun b => ?_
      rw [PowerSeries.coeff_mk, finrank_positiveGenWeight D e f he hf hef, if_neg (by omega)]
      simp
    rw [h0, map_zero, sub_zero]
  · rw [if_neg ha, if_neg ha, zero_sub]
    congr 2
    refine PowerSeries.ext fun b => ?_
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, finrank_positiveGenWeight D e f he hf hef]
    by_cases hb : b = 0
    · rw [if_neg (by omega), if_pos hb]
      simp
    · rw [if_pos ⟨by omega, by omega⟩, if_neg hb]

/-- **The character identity in KNZ form** for Borcherds data:
`Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{−dim 𝔤_(m,n)} · knzSeries (dim 𝔤_(1,·)) = 1`. -/
theorem coneProd_neg_mul_knzSeries (e f : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) :
    coneProd (fun m n => -(finrank ℂ (D.weightSpace ((m : ℤ), (n : ℤ))) : ℂ)) *
      knzSeries (fun j => (finrank ℂ (D.weightSpace (1, (j : ℤ))) : ℂ)) = 1 := by
  rw [← one_sub_finrankSeries_positiveGenWeight D e f he hf hef]
  refine Eq.trans ?_ (positivePart_coneProd_mul_one_sub D e f he hf hef)
  congr 1
  refine coneProd_congr fun m n hm hn => ?_
  rw [finrank_positiveWeight D hm hn]
  rfl

/-- The KNZ series depends only on the coefficients `c j` with `j ≥ 1`. -/
theorem knzSeries_congr {c c' : ℕ → ℂ} (h : ∀ j, 1 ≤ j → c j = c' j) :
    knzSeries c = knzSeries c' := by
  refine PowerSeries.ext fun a => ?_
  simp only [knzSeries, PowerSeries.coeff_mk, knzCoeff]
  split_ifs with ha
  · rfl
  · congr 2
    refine PowerSeries.ext fun b => ?_
    simp only [PowerSeries.coeff_mk]
    split_ifs with hb
    · rfl
    · exact h _ (by omega)

/-! ### The sandwich for pre-data -/

namespace BorcherdsPreData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (P : BorcherdsPreData g)

/-- `dim g_γ = dim g_{−γ}`, from the nondegenerate pairing. -/
theorem finrank_weightSpace_le_neg (γ : ℤ × ℤ) :
    finrank ℂ (P.weightSpace γ) ≤ finrank ℂ (P.weightSpace (-γ)) := by
  haveI := P.weight_finite γ
  haveI := P.weight_finite (-γ)
  let φ : P.weightSpace γ →ₗ[ℂ] Module.Dual ℂ (P.weightSpace (-γ)) :=
    P.form.compl₁₂ (P.weightSpace γ).subtype (P.weightSpace (-γ)).subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (P.form_nondegenerate γ x x.2 fun y hy =>
      LinearMap.congr_fun hx ⟨y, hy⟩)
  calc finrank ℂ (P.weightSpace γ) ≤ finrank ℂ (Module.Dual ℂ (P.weightSpace (-γ))) :=
        LinearMap.finrank_le_finrank_of_injective hφ
    _ = finrank ℂ (P.weightSpace (-γ)) := Subspace.dual_finrank_eq

theorem finrank_weightSpace_neg (γ : ℤ × ℤ) :
    finrank ℂ (P.weightSpace (-γ)) = finrank ℂ (P.weightSpace γ) := by
  refine le_antisymm ?_ (P.finrank_weightSpace_le_neg γ)
  have h := P.finrank_weightSpace_le_neg (-γ)
  rwa [neg_neg] at h

/-- The KNZ hypothesis for pre-data: `Π (1 − pᵐ qⁿ)^{dim g_(m,n)} = knzSeries (dim g_(1,·))`. -/
def KNZ : Prop :=
  coneProd (fun m n => (finrank ℂ (P.weightSpace ((m : ℤ), (n : ℤ))) : ℂ)) =
    knzSeries fun j => (finrank ℂ (P.weightSpace (1, (j : ℤ))) : ℂ)

theorem simpleImaginary (j : ℕ) (hj : 1 ≤ j) : borcherdsSimpleRoot (1, (j : ℤ)) :=
  Or.inr ⟨j, by exact_mod_cast hj, rfl⟩

/-- **The sandwich, dimension half:** under KNZ, `dim 𝔤_γ = dim g_γ` on the cone. -/
theorem finrank_quotientWeight_of_KNZ (hK : P.KNZ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    finrank ℂ (P.quotientWeight ((m : ℤ), (n : ℤ))) =
      finrank ℂ (P.weightSpace ((m : ℤ), (n : ℤ))) := by
  obtain ⟨e, f, he, hf, hef⟩ := P.quotientData.exists_normalized_real_pair
  have h₁ := coneProd_neg_mul_knzSeries P.quotientData e f he hf hef
  have hknz : knzSeries (fun j => (finrank ℂ (P.quotientData.weightSpace (1, (j : ℤ))) : ℂ)) =
      knzSeries fun j => (finrank ℂ (P.weightSpace (1, (j : ℤ))) : ℂ) := by
    refine knzSeries_congr fun j hj => ?_
    have hα := simpleImaginary j hj
    change ((finrank ℂ (P.quotientWeight (1, (j : ℤ))) : ℕ) : ℂ) = _
    rw [P.finrank_quotientWeight (P.weightSpace_le_simpleSpan hα)
      (P.weightSpace_neg_le_simpleSpan hα)]
  rw [hknz] at h₁
  have h₂ : coneProd (fun m n => (finrank ℂ (P.weightSpace ((m : ℤ), (n : ℤ))) : ℂ)) =
      1 - (1 - knzSeries fun j => (finrank ℂ (P.weightSpace (1, (j : ℤ))) : ℂ)) := by
    rw [sub_sub_cancel]
    exact hK
  rw [← sub_sub_cancel 1 (knzSeries fun j => (finrank ℂ (P.weightSpace (1, (j : ℤ))) : ℂ))]
    at h₁
  have := eq_of_coneProd_neg_mul_eq_one h₁ h₂ m n hm hn
  exact_mod_cast this.symm

/-- **The sandwich, inclusion half:** under KNZ, `g_γ ⊆ G` on the positive cone. -/
theorem weightSpace_le_simpleSpan_of_KNZ (hK : P.KNZ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    P.weightSpace ((m : ℤ), (n : ℤ)) ≤ P.simpleSpan.toSubmodule := by
  set γ : ℤ × ℤ := ((m : ℤ), (n : ℤ))
  haveI := P.weight_finite γ
  have h1 : finrank ℂ (P.quotientWeight γ) ≤ finrank ℂ (P.simpleSpanWeight γ) :=
    Submodule.finrank_map_le _ _
  have h2 : finrank ℂ (P.simpleSpanWeight γ) =
      finrank ℂ (P.simpleSpan.toSubmodule ⊓ P.weightSpace γ : Submodule ℂ g) := by
    rw [← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective _ P.simpleSpan.toSubmodule.injective_subtype _).finrank_eq
  have h3 : (P.simpleSpan.toSubmodule ⊓ P.weightSpace γ : Submodule ℂ g) = P.weightSpace γ := by
    apply Submodule.eq_of_le_of_finrank_eq inf_le_right
    apply le_antisymm (Submodule.finrank_mono inf_le_right)
    rw [← h2, ← P.finrank_quotientWeight_of_KNZ hK m n hm hn]
    exact h1
  rw [← h3]
  exact inf_le_left

/-! ### Opposite pre-data -/

theorem cartanPairing_neg (ξ : ℂ × ℂ) (γ : ℤ × ℤ) :
    borcherdsCartanPairing ξ (borcherdsWeightVector (-γ)) =
      -borcherdsCartanPairing ξ (borcherdsWeightVector γ) := by
  simp only [borcherdsCartanPairing, borcherdsWeightVector, Prod.fst_neg, Prod.snd_neg,
    Int.cast_neg]
  ring

/-- The opposite pre-data: `g_γ ↦ g_{−γ}`, Cartan `ξ ↦ h(−ξ)`. -/
def opposite : BorcherdsPreData g where
  weightSpace γ := P.weightSpace (-γ)
  weight_internal := by
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨P.weight_internal.submodule_iSupIndep.comp neg_injective, ?_⟩
    rw [← P.weight_internal.submodule_iSup_eq_top]
    exact (Equiv.neg (ℤ × ℤ)).iSup_comp (g := P.weightSpace)
  weight_finite γ := P.weight_finite (-γ)
  bracket_weight {γ δ} {x y} hx hy := by
    rw [neg_add]
    exact P.bracket_weight hx hy
  cartanMap := -P.cartanMap
  cartan_injective := fun ξ μ h => P.cartan_injective (neg_injective h)
  cartan_range := by
    rw [LinearMap.range_neg, P.cartan_range, neg_zero]
  cartan_action ξ γ x hx := by
    rw [LinearMap.neg_apply, neg_lie, P.cartan_action ξ (-γ) x hx, cartanPairing_neg, neg_smul,
      neg_neg]
  form := P.form
  form_symmetric := P.form_symmetric
  form_invariant := P.form_invariant
  form_orthogonal γ δ h x hx y hy :=
    P.form_orthogonal (-γ) (-δ) (by rw [← neg_add]; exact neg_ne_zero.mpr h) x hx y hy
  form_cartan ξ μ := by
    change P.form (-(P.cartanMap ξ)) (-(P.cartanMap μ)) = _
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
    exact P.form_cartan ξ μ
  form_nondegenerate γ x hx h := P.form_nondegenerate (-γ) x hx h
  root_support γ h := (borcherdsRootSupport_neg γ).mp (P.root_support (-γ) h)
  real_dimension := ⟨P.real_dimension.2, by rw [neg_neg]; exact P.real_dimension.1⟩

theorem opposite_simpleGenerators :
    borcherdsSimpleGenerators P.opposite.weightSpace =
      borcherdsSimpleGenerators P.weightSpace := by
  ext x
  simp only [borcherdsSimpleGenerators, opposite, neg_zero, neg_neg, Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨α, hα, h | h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨α, hα, Or.inr h⟩
    · exact Or.inr ⟨α, hα, Or.inl h⟩
  · rintro (h | ⟨α, hα, h | h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨α, hα, Or.inr h⟩
    · exact Or.inr ⟨α, hα, Or.inl h⟩

theorem opposite_simpleSpan : P.opposite.simpleSpan = P.simpleSpan := by
  rw [simpleSpan, simpleSpan, opposite_simpleGenerators]

theorem opposite_KNZ (hK : P.KNZ) : P.opposite.KNZ := by
  have h1 : (fun m n : ℕ => (finrank ℂ (P.opposite.weightSpace ((m : ℤ), (n : ℤ))) : ℂ)) =
      fun m n : ℕ => (finrank ℂ (P.weightSpace ((m : ℤ), (n : ℤ))) : ℂ) := by
    funext m n
    change ((finrank ℂ (P.weightSpace (-((m : ℤ), (n : ℤ)))) : ℕ) : ℂ) = _
    rw [P.finrank_weightSpace_neg]
  have h2 : (fun j : ℕ => (finrank ℂ (P.opposite.weightSpace (1, (j : ℤ))) : ℂ)) =
      fun j : ℕ => (finrank ℂ (P.weightSpace (1, (j : ℤ))) : ℂ) := by
    funext j
    change ((finrank ℂ (P.weightSpace (-(1, (j : ℤ)))) : ℕ) : ℂ) = _
    rw [P.finrank_weightSpace_neg]
  rw [KNZ, h1, h2]
  exact hK

/-! ### Generation -/

/-- **Generation from KNZ:** pre-data satisfying KNZ is generated by its simple root spaces. -/
theorem simpleSpan_eq_top_of_KNZ (hK : P.KNZ) : P.simpleSpan = ⊤ := by
  have hall : ∀ γ, P.weightSpace γ ≤ P.simpleSpan.toSubmodule := by
    intro γ
    by_cases h0 : P.weightSpace γ = ⊥
    · rw [h0]
      exact bot_le
    have hs := P.root_support γ h0
    have hcone : ∀ (Q : BorcherdsPreData g) (hQ : Q.KNZ) (δ : ℤ × ℤ),
        borcherdsPositiveCone δ → Q.weightSpace δ ≤ Q.simpleSpan.toSubmodule := by
      intro Q hQ δ hδ
      obtain ⟨h1, h2⟩ := hδ
      have := Q.weightSpace_le_simpleSpan_of_KNZ hQ δ.1.toNat δ.2.toNat (by omega) (by omega)
      rwa [show (((δ.1.toNat : ℕ) : ℤ), ((δ.2.toNat : ℕ) : ℤ)) = δ by
        ext <;> simp <;> omega] at this
    rcases hs with rfl | (rfl | hγ) | (hγ | hγ)
    · exact fun x hx => P.mem_simpleSpan_of_mem_zero hx
    · exact P.weightSpace_le_simpleSpan (Or.inl rfl)
    · exact hcone P hK γ hγ
    · rw [show γ = -borcherdsRealRoot by rw [← hγ, neg_neg]]
      exact P.weightSpace_neg_le_simpleSpan (Or.inl rfl)
    · have := hcone P.opposite (P.opposite_KNZ hK) (-γ) hγ
      rw [opposite_simpleSpan] at this
      change P.weightSpace (-(-γ)) ≤ _ at this
      rwa [neg_neg] at this
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ ⨆ γ, P.weightSpace γ := by
    rw [P.weight_internal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  exact (iSup_le hall) hx

/-- **Simple-root generation for pre-data:** under KNZ, `lieSpan (simple generators) = ⊤`. -/
theorem lieSpan_eq_top_of_KNZ (hK : P.KNZ) :
    LieSubalgebra.lieSpan ℂ g (borcherdsSimpleGenerators P.weightSpace) = ⊤ :=
  P.simpleSpan_eq_top_of_KNZ hK

end BorcherdsPreData

end VOA.Moonshine.ConwayNorton.M8
