import VOA.Moonshine.MoonshineCNBorcherdsVermaWeights
import VOA.Moonshine.MoonshineCNInducedVectorMap
import VOA.Moonshine.MoonshineCNBorcherdsCasimirInduction

/-! The length-one resolution of the trivial module by generalized Verma modules.

For abstract Borcherds data with a normalized real pair `(e, f)`, the map
`N(U) → N(ℂ)`, `[a ⊗ u] ↦ [a u ⊗ 1]`, is injective, and its image is the kernel of the
augmentation `N(ℂ) → ℂ`.  Equivalently, right multiplication `U(𝔲⁺) ⊗ U → U(𝔲⁺)` is injective
with image the augmentation ideal.

The injectivity proof is the lowest-vector argument: the Casimir operator vanishes on `N(U)`,
a nonzero kernel would contain a nonzero vector killed by all lowering operators, the Casimir
scalar `-2n(m-1)` then forces first coordinate one, and in first coordinate one `N(U)` is its
bottom, where the map is injective. -/

noncomputable section
open scoped TensorProduct
open Module
namespace VOA.Moonshine.ConwayNorton

variable {g M : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup M] [Module ℂ M]

namespace BorcherdsAdmissible
variable {D : BorcherdsData g} {ρ : g →ₗ⁅ℂ⁆ End ℂ M} (A : BorcherdsAdmissible D ρ)

/-- A submodule which is spanned by weight vectors, on a module with weights in the positive cone
and vanishing Casimir operator, is zero once it meets the first-coordinate-one line trivially. -/
theorem submodule_eq_bot_of_casimir_zero
    (hcone : ∀ μ, ¬ borcherdsPositiveCone μ → A.weightSpace μ = ⊥)
    (hΩ : ∀ v, A.casimirOperator v = 0)
    (K : Submodule ℂ M) (hK : ∀ (x : g), ∀ v ∈ K, ρ x v ∈ K)
    (hgr : K ≤ ⨆ μ, K ⊓ A.weightSpace μ)
    (hline : ∀ n : ℤ, K ⊓ A.weightSpace (1, n) = ⊥) : K = ⊥ := by
  classical
  have hconeK : ∀ μ, K ⊓ A.weightSpace μ ≠ ⊥ → borcherdsPositiveCone μ := by
    intro μ hμ
    by_contra hc
    exact hμ (by rw [hcone μ hc, inf_bot_eq])
  by_contra hne
  have hex : ∃ μ, K ⊓ A.weightSpace μ ≠ ⊥ := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (le_bot_iff.mp (hgr.trans (iSup_le fun μ => (h μ).le)))
  have hP : ∃ h : ℕ, ∃ μ : ℤ × ℤ,
      borcherdsRootHeight μ = (h : ℤ) ∧ K ⊓ A.weightSpace μ ≠ ⊥ := by
    obtain ⟨μ, hμ⟩ := hex
    have hc := hconeK μ hμ
    refine ⟨(borcherdsRootHeight μ).toNat, μ, ?_, hμ⟩
    simp only [borcherdsRootHeight, borcherdsPositiveCone] at hc ⊢
    omega
  obtain ⟨μ₀, hμ₀h, hμ₀⟩ := Nat.find_spec hP
  have hmin : ∀ ν, borcherdsRootHeight ν < (Nat.find hP : ℤ) → K ⊓ A.weightSpace ν = ⊥ := by
    intro ν hν
    by_contra hne'
    have hc := hconeK ν hne'
    have h0 : 0 ≤ borcherdsRootHeight ν := by
      simp only [borcherdsRootHeight, borcherdsPositiveCone] at hc ⊢
      omega
    exact Nat.find_min hP (show (borcherdsRootHeight ν).toNat < Nat.find hP by omega)
      ⟨ν, by omega, hne'⟩
  obtain ⟨k, hkK, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ₀
  obtain ⟨_, f, _, hf, hef⟩ := D.exists_normalized_real_pair
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hef
  have hiter : ∀ i : ℕ, (ρ f ^ i) k ∈
      K ⊓ A.weightSpace (μ₀.1 - (i : ℤ), μ₀.2 + (i : ℤ)) := by
    intro i
    induction i with
    | zero => simpa using hkK
    | succ i ih =>
        rw [pow_succ', Module.End.mul_apply]
        refine ⟨hK f _ ih.1, ?_⟩
        have h := A.action_weight hf ih.2
        have hw : (μ₀.1 - (i : ℤ), μ₀.2 + (i : ℤ)) + -borcherdsRealRoot =
            (μ₀.1 - ((i + 1 : ℕ) : ℤ), μ₀.2 + ((i + 1 : ℕ) : ℤ)) := by
          simp only [borcherdsRealRoot, Prod.ext_iff, Prod.fst_add, Prod.snd_add,
            Prod.fst_neg, Prod.snd_neg]
          push_cast
          constructor <;> ring
        rwa [hw] at h
  have hc₀ := hconeK μ₀ hμ₀
  have hQ : ∃ i : ℕ, (ρ f ^ (i + 1)) k = 0 := by
    refine ⟨μ₀.1.toNat - 1, ?_⟩
    have hmem := (hiter (μ₀.1.toNat - 1 + 1)).2
    rw [hcone] at hmem
    · exact (Submodule.mem_bot ℂ).mp hmem
    · simp only [borcherdsPositiveCone] at hc₀ ⊢
      omega
  have hnz : ∀ i : ℕ, (∀ j < i, ¬ (ρ f ^ (j + 1)) k = 0) → (ρ f ^ i) k ≠ 0 := by
    intro i hi
    cases i with
    | zero => simpa using hk0
    | succ j => exact hi j (Nat.lt_succ_self j)
  have hk'0 := hnz (Nat.find hQ) (fun j hj => Nat.find_min hQ hj)
  have hk' := hiter (Nat.find hQ)
  have hfk' : ρ f ((ρ f ^ Nat.find hQ) k) = 0 := by
    have h := Nat.find_spec hQ
    rwa [pow_succ', Module.End.mul_apply] at h
  set μ' : ℤ × ℤ := (μ₀.1 - (Nat.find hQ : ℤ), μ₀.2 + (Nat.find hQ : ℤ)) with hμ'
  have hμ'h : borcherdsRootHeight μ' = (Nat.find hP : ℤ) := by
    rw [← hμ₀h]
    simp only [hμ', borcherdsRootHeight]
    ring
  have hlow : ∀ β, borcherdsPositiveRoot β → ∀ x ∈ D.weightSpace (-β),
      ρ x ((ρ f ^ Nat.find hQ) k) = 0 := by
    intro β hβ x hx
    rcases hβ with rfl | hβ
    · obtain ⟨c, rfl⟩ := D.realRoot_vector_eq_smul _ (Or.inr rfl) f hf hf0 x hx
      rw [map_smul, LinearMap.smul_apply, hfk', smul_zero]
    · have hmem : ρ x ((ρ f ^ Nat.find hQ) k) ∈ K ⊓ A.weightSpace (μ' + -β) :=
        ⟨hK x _ hk'.1, A.action_weight hx hk'.2⟩
      have hlt : borcherdsRootHeight (μ' + -β) < (Nat.find hP : ℤ) := by
        rw [← hμ'h]
        simp only [borcherdsRootHeight, borcherdsPositiveCone, Prod.fst_add, Prod.snd_add,
          Prod.fst_neg, Prod.snd_neg] at hβ ⊢
        omega
      rw [hmin _ hlt] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
  have hcone' : borcherdsPositiveCone μ' :=
    hconeK μ' ((Submodule.ne_bot_iff _).mpr ⟨_, hk', hk'0⟩)
  have h1 := A.lowest_casimir_zero_first_coordinate hk'.2 hk'0 hcone' hlow (hΩ _)
  have hk'' : (ρ f ^ Nat.find hQ) k ∈ K ⊓ A.weightSpace (1, μ'.2) := by
    have h : μ' = (1, μ'.2) := Prod.ext h1 rfl
    rw [← h]
    exact hk'
  rw [hline] at hk''
  exact hk'0 ((Submodule.mem_bot ℂ).mp hk'')

end BorcherdsAdmissible

namespace BorcherdsData
variable (D : BorcherdsData g) (e f : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
  (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)

/-- The parabolic action on U agrees with the adjoint action modulo the parabolic. -/
theorem genSpaceParabolicRep_sub_mem (x : D.parabolicPart) (u : D.genSpace e) :
    ⁅(x : g), (u : g)⁆ - (D.genSpaceParabolicRep e f he hf hef x u : g) ∈ D.parabolicPart := by
  have hπ : (D.genSpaceParabolicRep e f he hf hef x u : g) =
      ⁅((D.parabolicLeviProjectionLinear x : D.leviPart) : g), (u : g)⁆ := rfl
  rw [hπ, ← sub_lie]
  exact D.negative_bracket_genSpace e he (D.parabolicLeviProjection_residual x) u.property

/-- The resolution map `N(U) → N(ℂ)`, `[a ⊗ u] ↦ [a u ⊗ 1]`. -/
def generatorVermaResolution :
    relativeInducedSpace D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) →ₗ[ℂ]
      relativeInducedSpace D.parabolicPart D.parabolicTrivialRep :=
  inducedVectorMap D.parabolicPart (D.genSpace e) (D.genSpaceParabolicRep e f he hf hef)
    (D.genSpaceParabolicRep_sub_mem e f he hf hef)

theorem generatorVermaResolution_equivariant (z : g)
    (q : relativeInducedSpace D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)) :
    D.generatorVermaResolution e f he hf hef
        (relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) z q) =
      relativeInducedRep D.parabolicPart D.parabolicTrivialRep z
        (D.generatorVermaResolution e f he hf hef q) :=
  inducedVectorMap_equivariant _ _ _ _ z q

/-- The raising operator on U is the raising operator on the bottom of `N(U)`. -/
theorem generatorBottom_raising (u : g) (hu : u ∈ D.genSpace e) :
    PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)
        ⟨⁅e, u⁆, D.genSpace_raising_stable e he hu⟩ =
      relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) e
        (PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) ⟨u, hu⟩) := by
  have heL : e ∈ D.leviPart := D.weightSpace_le_weightSpan (Or.inr (Or.inl rfl)) he
  have h := relativeInducedRep_bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)
    ⟨e, D.leviPart_le_parabolic heL⟩ ⟨u, hu⟩
  refine Eq.trans ?_ h.symm
  congr 1
  apply Subtype.ext
  exact (D.genSpaceParabolicRep_levi e f he hf hef ⟨e, heL⟩ ⟨u, hu⟩).symm

include he in
theorem genSpace_raising_pow_mem (u : g) (hu : u ∈ D.genSpace e) (k : ℕ) :
    (LieModule.toEnd ℂ g g e ^ k) u ∈ D.genSpace e := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply]
      exact D.genSpace_raising_stable e he ih

theorem generatorBottom_raising_pow (u : g) (hu : u ∈ D.genSpace e) (k : ℕ) :
    PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)
        ⟨(LieModule.toEnd ℂ g g e ^ k) u, D.genSpace_raising_pow_mem e he u hu k⟩ =
      (relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) e ^ k)
        (PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) ⟨u, hu⟩) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := D.generatorBottom_raising e f he hf hef _ (D.genSpace_raising_pow_mem e he u hu k)
      rw [ih] at h
      have hsub : (⟨(LieModule.toEnd ℂ g g e ^ (k + 1)) u,
          D.genSpace_raising_pow_mem e he u hu (k + 1)⟩ : D.genSpace e) =
          ⟨⁅e, (LieModule.toEnd ℂ g g e ^ k) u⁆,
            D.genSpace_raising_stable e he (D.genSpace_raising_pow_mem e he u hu k)⟩ :=
        Subtype.ext (show (LieModule.toEnd ℂ g g e ^ (k + 1)) u =
            ⁅e, (LieModule.toEnd ℂ g g e ^ k) u⁆ by
          rw [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply])
      rw [hsub, h, pow_succ' (relativeInducedRep D.parabolicPart
        (D.genSpaceParabolicRep e f he hf hef) e), Module.End.mul_apply]

/-- The Casimir operator vanishes on the bottom of `N(U)`. -/
theorem generatorVerma_casimir_bottom (w : D.genSpace e) :
    (D.generatorVermaAdmissible e f he hf hef).casimirOperator
      (PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) w) = 0 := by
  apply D.generatorBottom_mem_of_strings e f he hf hef
    (LinearMap.ker (D.generatorVermaAdmissible e f he hf hef).casimirOperator)
  intro i u hu hs
  obtain ⟨v, hv, rfl⟩ := hs
  obtain ⟨hj, hk⟩ := i.property
  have hvU : v ∈ D.genSpace e :=
    D.generatorString_le_genSpace e i.val.1 hj 0 (by omega) ⟨v, hv, by simp⟩
  rw [LinearMap.mem_ker]
  have hb := D.generatorBottom_raising_pow e f he hf hef v hvU i.val.2
  have hb' : PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)
      ⟨(LieModule.toEnd ℂ g g e ^ i.val.2) v, hu⟩ =
        UniversalEnvelopingAlgebra.lift ℂ
          (relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef))
          (UniversalEnvelopingAlgebra.ι ℂ e ^ i.val.2)
          (PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)
            ⟨v, hvU⟩) := by
    rw [map_pow, UniversalEnvelopingAlgebra.lift_ι_apply]
    exact hb
  rw [hb']
  apply (D.generatorVermaAdmissible e f he hf hef).casimirOperator_simple_lowest_enveloping
    (α := borcherdsImaginaryRoot i.val.1)
  · exact D.generatorBottom_mem_cartanEigenspace e f he hf hef _ v hvU hv
  · exact Or.inr ⟨i.val.1, hj, rfl⟩
  · intro β hβ x hx
    have hxp : x ∈ D.parabolicPart := by
      apply D.weightSpace_le_weightSpan (P := fun γ => ¬ borcherdsPositiveCone γ) _ hx
      rcases hβ with rfl | hβ
      · simp [borcherdsPositiveCone, borcherdsRealRoot]
      · simp only [borcherdsPositiveCone, Prod.fst_neg, Prod.snd_neg] at hβ ⊢
        omega
    rw [show x = ((⟨x, hxp⟩ : D.parabolicPart) : g) from rfl,
      relativeInducedRep_bottom]
    rcases hβ with rfl | hβ
    · have hxL : x ∈ D.leviPart := D.weightSpace_le_weightSpan (Or.inr (Or.inr rfl)) hx
      have hσ : D.genSpaceParabolicRep e f he hf hef ⟨x, hxp⟩ ⟨v, hvU⟩ = 0 := by
        apply Subtype.ext
        refine (D.genSpaceParabolicRep_levi e f he hf hef ⟨x, hxL⟩ ⟨v, hvU⟩).trans ?_
        exact D.simple_lowering_vanishes i.val.1 hj x v hx hv
      rw [hσ, map_zero]
    · have hxN : x ∈ D.negativePart := D.weightSpace_le_weightSpan (P := borcherdsNegativeCone)
        (by simpa [borcherdsNegativeCone] using hβ) hx
      rw [D.genSpaceParabolicRep_negative e f he hf hef ⟨x, hxp⟩ hxN, LinearMap.zero_apply,
        map_zero]

/-- The Casimir operator vanishes on the whole of `N(U)`. -/
theorem generatorVerma_casimir_eq_zero
    (v : relativeInducedSpace D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)) :
    (D.generatorVermaAdmissible e f he hf hef).casimirOperator v = 0 := by
  have h := inducedCasimir_scalar_of_bottom D.parabolicPart
    (D.genSpaceParabolicRep e f he hf hef) D (D.generatorVermaAdmissible e f he hf hef) 0
    (fun w => by rw [D.generatorVerma_casimir_bottom e f he hf hef w, zero_smul])
  rw [h, zero_smul, LinearMap.zero_apply]

/-- In first coordinate one, `N(U)` consists of bottom vectors of the same weight. -/
theorem generatorVerma_firstLine_bottom (n : ℤ)
    {v : relativeInducedSpace D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)}
    (hv : v ∈ D.cartanEigenspace
      (relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)) (1, n)) :
    ∃ (u : g) (hu : u ∈ D.genSpace e), u ∈ D.weightSpace (1, n) ∧
      v = PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) ⟨u, hu⟩ := by
  let ρU := relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)
  let B := ((D.weightSpace (1, n)).comap (D.genSpace e).subtype).map
    (PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef))
  let R := ⨆ μ, ⨆ (_ : μ ≠ (1, n) ∧ 1 ≤ μ.1), D.cartanEigenspace ρU μ
  have hB : B ≤ D.cartanEigenspace ρU (1, n) := by
    rintro _ ⟨⟨u, hu⟩, hw, rfl⟩
    exact D.generatorBottom_mem_cartanEigenspace e f he hf hef _ u hu hw
  have hBR : B ⊔ R = ⊤ := by
    apply D.inducedSpace_eq_top_of_bottom
    · apply D.generatorBottom_mem_of_strings e f he hf hef
      intro i u hu hs
      have hwt := D.generatorString_le_weight e he _ _ hs
      by_cases hi : borcherdsStringDegree i = (1, n)
      · apply Submodule.mem_sup_left
        refine ⟨⟨u, hu⟩, ?_, rfl⟩
        change u ∈ D.weightSpace (1, n)
        rw [← hi]
        exact hwt
      · apply Submodule.mem_sup_right
        exact Submodule.mem_iSup_of_mem (borcherdsStringDegree i)
          (Submodule.mem_iSup_of_mem ⟨hi, by simp [borcherdsStringDegree]⟩
            (D.generatorBottom_mem_cartanEigenspace e f he hf hef _ u hu hwt))
    · intro x hx w hw
      obtain ⟨b, hb, r, hr, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add]
      apply Submodule.mem_sup_right
      have hmaps : ∀ μ α, (μ = (1, n) ∨ (μ ≠ (1, n) ∧ 1 ≤ μ.1)) → borcherdsPositiveCone α →
          (μ + α ≠ (1, n) ∧ 1 ≤ (μ + α).1) := by
        intro μ α hμ hα
        simp only [borcherdsPositiveCone] at hα
        rcases hμ with rfl | ⟨_, hμ⟩
        · constructor
          · intro h
            have := congrArg Prod.fst h
            simp only [Prod.fst_add] at this
            omega
          · simp only [Prod.fst_add]
            omega
        · constructor
          · intro h
            have := congrArg Prod.fst h
            simp only [Prod.fst_add] at this
            omega
          · simp only [Prod.fst_add]
            omega
      have hb' : b ∈ ⨆ μ, ⨆ (_ : μ = (1, n) ∨ (μ ≠ (1, n) ∧ 1 ≤ μ.1)),
          D.cartanEigenspace ρU μ :=
        Submodule.mem_iSup_of_mem (1, n) (Submodule.mem_iSup_of_mem (Or.inl rfl) (hB hb))
      have hr' : r ∈ ⨆ μ, ⨆ (_ : μ = (1, n) ∨ (μ ≠ (1, n) ∧ 1 ≤ μ.1)),
          D.cartanEigenspace ρU μ :=
        (show R ≤ ⨆ μ, ⨆ (_ : μ = (1, n) ∨ (μ ≠ (1, n) ∧ 1 ≤ μ.1)),
            D.cartanEigenspace ρU μ from
          iSup_mono fun μ => iSup_le fun h => le_iSup_of_le (Or.inr h) le_rfl) hr
      exact Submodule.add_mem _
        (D.cartanEigenspace_span_maps ρU _ _ borcherdsPositiveCone hmaps hx hb')
        (D.cartanEigenspace_span_maps ρU _ _ borcherdsPositiveCone hmaps hx hr')
  have hvBR : v ∈ B ⊔ R := by rw [hBR]; trivial
  obtain ⟨b, hb, r, hr, hsum⟩ := Submodule.mem_sup.mp hvBR
  have hr0 : r = 0 := by
    have hrv : r ∈ D.cartanEigenspace ρU (1, n) := by
      have : r = v - b := by rw [← hsum]; abel
      rw [this]
      exact Submodule.sub_mem _ hv (hB hb)
    apply (Submodule.disjoint_def.mp
      (iSupIndep_def.mp (D.cartanEigenspace_iSupIndep ρU) (1, n))) r hrv
    exact (show R ≤ ⨆ μ, ⨆ (_ : μ ≠ (1, n)), D.cartanEigenspace ρU μ from
      iSup_mono fun μ => iSup_le fun h => le_iSup_of_le h.1 le_rfl) hr
  obtain ⟨⟨u, hu⟩, hw, rfl⟩ := hb
  exact ⟨u, hu, hw, by rw [← hsum, hr0, add_zero]⟩

/-- The resolution map is injective on the first-coordinate-one line. -/
theorem generatorVermaResolution_firstLine (n : ℤ) :
    LinearMap.ker (D.generatorVermaResolution e f he hf hef) ⊓
      D.cartanEigenspace
        (relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)) (1, n) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hker, hv⟩
  obtain ⟨u, hu, -, rfl⟩ := D.generatorVerma_firstLine_bottom e f he hf hef n hv
  have hker' : D.generatorVermaResolution e f he hf hef
      (PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) ⟨u, hu⟩) = 0 :=
    hker
  rw [generatorVermaResolution, inducedVectorMap_bottom] at hker'
  have hu0 : u = 0 := trivialInduced_action_bottom_injective D.parabolicPart D.positivePart
    (D.parabolicVermaMultiplication_bijective D.parabolicTrivialRep).1
    (D.genSpace_le_positive e he hu) hker'
  subst hu0
  exact (Submodule.mem_bot ℂ).mpr (by
    rw [show (⟨0, hu⟩ : D.genSpace e) = 0 from rfl, map_zero])

/-- The generalized Verma map `N(U) → N(ℂ)` is injective. -/
theorem generatorVermaResolution_injective :
    Function.Injective (D.generatorVermaResolution e f he hf hef) := by
  let A := D.generatorVermaAdmissible e f he hf hef
  let ρU := relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)
  rw [← LinearMap.ker_eq_bot]
  apply A.submodule_eq_bot_of_casimir_zero
  · exact fun μ hμ => D.generatorVerma_weight_eq_bot e f he hf hef hμ
  · exact D.generatorVerma_casimir_eq_zero e f he hf hef
  · intro x v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [D.generatorVermaResolution_equivariant, hv, map_zero]
  · apply D.cartanEigenspace_kernel_graded ρU
      (relativeInducedRep D.parabolicPart D.parabolicTrivialRep)
    · intro ξ v
      exact D.generatorVermaResolution_equivariant e f he hf hef _ v
    · apply top_unique
      rw [← D.generatorVerma_cartanEigenspace_span e f he hf hef]
      exact iSup_mono fun μ => iSup_le fun _ => le_rfl
  · exact D.generatorVermaResolution_firstLine e f he hf hef

include he hf hef in
/-- Right multiplication `U(𝔲⁺) ⊗ U → U(𝔲⁺)` is injective. -/
theorem positiveGeneratorMultiplication_injective :
    Function.Injective (envelopingGeneratorMultiplication (D.positiveGeneratorSpace e)) :=
  generatorMultiplication_injective_of_inducedVectorMap D.parabolicPart (D.genSpace e)
    (D.genSpaceParabolicRep e f he hf hef) (D.genSpaceParabolicRep_sub_mem e f he hf hef)
    D.positivePart (D.genSpace_le_positive e he)
    (D.generatorVermaResolution_injective e f he hf hef)
    (D.parabolicVermaMultiplication_bijective _).1

include he hf hef in
/-- The short exact sequence `0 → U(𝔲⁺) ⊗ U → U(𝔲⁺) → ℂ → 0`. -/
theorem positiveGeneratorMultiplication_shortExact :
    Function.Injective (envelopingGeneratorMultiplication (D.positiveGeneratorSpace e)) ∧
      Function.Exact (envelopingGeneratorMultiplication (D.positiveGeneratorSpace e))
        (envelopingAugmentation (g := D.positivePart)).toLinearMap ∧
      Function.Surjective (envelopingAugmentation (g := D.positivePart)) :=
  ⟨D.positiveGeneratorMultiplication_injective e f he hf hef,
    D.positiveGeneratorMultiplication_exact e f he hf hef, envelopingAugmentation_surjective⟩

/-- The augmentation of `N(ℂ)`, read off in PBW coordinates. -/
def trivialVermaAugmentation :
    relativeInducedSpace D.parabolicPart D.parabolicTrivialRep →ₗ[ℂ] ℂ :=
  (envelopingAugmentation (g := D.positivePart)).toLinearMap ∘ₗ
    (TensorProduct.rid ℂ (UniversalEnvelopingAlgebra ℂ D.positivePart)).toLinearMap ∘ₗ
      (D.parabolicVermaEquiv D.parabolicTrivialRep).symm.toLinearMap

theorem trivialVermaAugmentation_verma (a : UniversalEnvelopingAlgebra ℂ D.positivePart) :
    D.trivialVermaAugmentation
        (D.parabolicVermaMultiplication D.parabolicTrivialRep (a ⊗ₜ[ℂ] (1 : ℂ))) =
      envelopingAugmentation a := by
  have h : (D.parabolicVermaEquiv D.parabolicTrivialRep).symm
      (D.parabolicVermaMultiplication D.parabolicTrivialRep (a ⊗ₜ[ℂ] (1 : ℂ))) =
        a ⊗ₜ[ℂ] (1 : ℂ) :=
    (D.parabolicVermaEquiv D.parabolicTrivialRep).symm_apply_apply _
  simp only [trivialVermaAugmentation, LinearMap.comp_apply, LinearEquiv.coe_coe, h,
    TensorProduct.rid_tmul, one_smul, AlgHom.toLinearMap_apply]

theorem trivialVermaAugmentation_surjective :
    Function.Surjective D.trivialVermaAugmentation := fun c =>
  ⟨D.parabolicVermaMultiplication D.parabolicTrivialRep
    (algebraMap ℂ _ c ⊗ₜ[ℂ] (1 : ℂ)), by rw [trivialVermaAugmentation_verma, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply]⟩

/-- The length-one resolution `0 → N(U) → N(ℂ) → ℂ → 0` of the trivial module by generalized
Verma modules: injectivity, exactness in the middle, and surjectivity. -/
theorem generatorVermaResolution_shortExact :
    Function.Injective (D.generatorVermaResolution e f he hf hef) ∧
      Function.Exact (D.generatorVermaResolution e f he hf hef) D.trivialVermaAugmentation ∧
      Function.Surjective D.trivialVermaAugmentation := by
  refine ⟨D.generatorVermaResolution_injective e f he hf hef, ?_,
    D.trivialVermaAugmentation_surjective⟩
  have hkey := inducedVectorMap_verma_generator D.parabolicPart (D.genSpace e)
    (D.genSpaceParabolicRep e f he hf hef) (D.genSpaceParabolicRep_sub_mem e f he hf hef)
    D.positivePart (D.genSpace_le_positive e he)
  have hμ := D.positiveGeneratorMultiplication_exact e f he hf hef
  intro y
  obtain ⟨t, rfl⟩ := (D.parabolicVermaMultiplication_bijective D.parabolicTrivialRep).2 y
  let a := TensorProduct.rid ℂ (UniversalEnvelopingAlgebra ℂ D.positivePart) t
  have ht : t = a ⊗ₜ[ℂ] (1 : ℂ) := by
    simp only [a]
    exact ((TensorProduct.rid ℂ _).symm_apply_apply t).symm.trans rfl
  rw [ht, trivialVermaAugmentation_verma]
  constructor
  · intro ha
    obtain ⟨s, hs⟩ := (hμ a).mp ha
    refine ⟨D.parabolicVermaMultiplication (D.genSpaceParabolicRep e f he hf hef)
      ((Submodule.comapSubtypeEquivOfLe (D.genSpace_le_positive e he)).toLinearMap.lTensor _ s),
      ?_⟩
    exact (hkey s).trans (congrArg (fun b => relativeVermaMultiplication D.parabolicPart
      D.positivePart (0 : D.parabolicPart →ₗ⁅ℂ⁆ End ℂ ℂ) (b ⊗ₜ[ℂ] (1 : ℂ))) hs)
  · rintro ⟨z, hz⟩
    obtain ⟨t', rfl⟩ := (D.parabolicVermaMultiplication_bijective _).2 z
    obtain ⟨s, rfl⟩ := (LinearEquiv.lTensor (UniversalEnvelopingAlgebra ℂ D.positivePart)
      (Submodule.comapSubtypeEquivOfLe (D.genSpace_le_positive e he))).surjective t'
    have h := hkey s
    change D.generatorVermaResolution e f he hf hef
      (D.parabolicVermaMultiplication _ _) = _ at hz
    have h' : D.parabolicVermaMultiplication D.parabolicTrivialRep
        (envelopingGeneratorMultiplication (D.positiveGeneratorSpace e) s ⊗ₜ[ℂ] (1 : ℂ)) =
      D.parabolicVermaMultiplication D.parabolicTrivialRep (a ⊗ₜ[ℂ] (1 : ℂ)) :=
      h.symm.trans hz
    have h'' := (D.parabolicVermaMultiplication_bijective _).1 h'
    have h3 := congrArg (TensorProduct.rid ℂ (UniversalEnvelopingAlgebra ℂ D.positivePart)) h''
    simp only [TensorProduct.rid_tmul, one_smul] at h3
    rw [← h3]
    exact (hμ _).mpr ⟨s, rfl⟩

end BorcherdsData
end VOA.Moonshine.ConwayNorton
