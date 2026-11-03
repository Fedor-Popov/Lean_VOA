import VOA.DeligneAudit.SL4TFinitePointFunctions
import Mathlib.RepresentationTheory.Invariants

/-! Exactness of finite-group invariants and dimension along invariant filtrations. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Averaging in a complex representation of a finite group. -/
def finiteRepresentationAverage (ρ : Representation ℂ G V) : V →ₗ[ℂ] V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g

/-- Every averaged vector is invariant. -/
theorem finiteRepresentationAverage_fixed (ρ : Representation ℂ G V) (v : V) :
    finiteRepresentationAverage ρ v ∈ ρ.invariants := by
  intro g
  simp only [finiteRepresentationAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum]
  congr 1
  have he (h : G) : ρ g (ρ h v) = ρ (g * h) v := by rw [map_mul]; rfl
  simp only [he]
  exact Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h => ρ h v)

/-- Averaging is the identity on invariant vectors. -/
theorem finiteRepresentationAverage_id (ρ : Representation ℂ G V) (v : V)
    (hv : v ∈ ρ.invariants) : finiteRepresentationAverage ρ v = v := by
  change ∀ g, ρ g v = v at hv
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteRepresentationAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    hv, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Equivariant linear maps commute with averaging. -/
theorem finiteRepresentationAverage_map (ρ : Representation ℂ G V)
    (τ : Representation ℂ G W) (f : V →ₗ[ℂ] W)
    (hf : ∀ g v, f (ρ g v) = τ g (f v)) (v : V) :
    f (finiteRepresentationAverage ρ v) = finiteRepresentationAverage τ (f v) := by
  simp only [finiteRepresentationAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, hf]

/-- Restriction of an equivariant linear map to invariant vectors. -/
def representationFixedMap (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (ρ g v) = τ g (f v)) :
    ρ.invariants →ₗ[ℂ] τ.invariants where
  toFun v := ⟨f v.val, fun g => by rw [← hf, v.property g]⟩
  map_add' v w := Subtype.ext (map_add f v.val w.val)
  map_smul' c v := Subtype.ext (map_smul f c v.val)

/-- An equivariant linear equivalence restricts to an equivalence of fixed spaces. -/
def representationFixedEquiv (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (e : V ≃ₗ[ℂ] W) (he : ∀ g v, e (ρ g v) = τ g (e v)) :
    ρ.invariants ≃ₗ[ℂ] τ.invariants :=
  LinearEquiv.ofBijective (representationFixedMap ρ τ e.toLinearMap he) (by
    constructor
    · intro v w h
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val h)
    · intro w
      refine ⟨⟨e.symm w.val, fun g => ?_⟩, ?_⟩
      · apply e.injective
        rw [he, e.apply_symm_apply, w.property g]
      · exact Subtype.ext (e.apply_symm_apply w.val))

/-- Surjective equivariant linear maps are surjective on invariant vectors. -/
theorem representationFixedMap_surjective (ρ : Representation ℂ G V)
    (τ : Representation ℂ G W) (f : V →ₗ[ℂ] W)
    (hf : ∀ g v, f (ρ g v) = τ g (f v)) (hs : Function.Surjective f) :
    Function.Surjective (representationFixedMap ρ τ f hf) := by
  intro w
  obtain ⟨v, hv⟩ := hs w.val
  refine ⟨⟨finiteRepresentationAverage ρ v, finiteRepresentationAverage_fixed ρ v⟩, ?_⟩
  apply Subtype.ext
  change f (finiteRepresentationAverage ρ v) = w.val
  rw [finiteRepresentationAverage_map ρ τ f hf, hv,
    finiteRepresentationAverage_id τ w.val w.property]

/-- Fixed vectors in a stable subspace are the intersection with the ambient fixed space. -/
def stableSubspaceFixedEquiv (ρ : Representation ℂ G V) (S : Submodule ℂ V)
    (hS : ∀ g, S ≤ S.comap (ρ g)) :
    (ρ.subrepresentation S hS).invariants ≃ₗ[ℂ] ↥(S ⊓ ρ.invariants) where
  toFun v := ⟨v.val.val, v.val.property, fun g => congrArg Subtype.val (v.property g)⟩
  invFun v := ⟨⟨v.val, v.property.1⟩, fun g => Subtype.ext (v.property.2 g)⟩
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' c v := rfl

/-- Invariants are exact across a stable quotient, including the dimension identity. -/
theorem stableQuotient_fixed_finrank [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (S : Submodule ℂ V)
    (hS : ∀ g, S ≤ S.comap (ρ g)) :
    Module.finrank ℂ (ρ.quotient S hS).invariants +
      Module.finrank ℂ ↥(S ⊓ ρ.invariants) = Module.finrank ℂ ρ.invariants := by
  let f := representationFixedMap ρ (ρ.quotient S hS) S.mkQ (fun _ _ => rfl)
  have hs : Function.Surjective f :=
    representationFixedMap_surjective _ _ _ _ S.mkQ_surjective
  have hk : LinearMap.ker f = S.comap ρ.invariants.subtype := by
    ext v
    change (⟨S.mkQ v.val, _⟩ : (ρ.quotient S hS).invariants) = 0 ↔ v.val ∈ S
    rw [Subtype.ext_iff]
    exact Submodule.Quotient.mk_eq_zero S
  have hd := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, hk] at hd
  have he : Module.finrank ℂ (S.comap ρ.invariants.subtype) =
      Module.finrank ℂ ↥(S ⊓ ρ.invariants) := by
    rw [← Submodule.finrank_map_subtype_eq ρ.invariants,
      Submodule.map_comap_subtype, inf_comm]
  rwa [he] at hd

/-- A stable quotient has the expected difference of invariant dimensions. -/
theorem stableQuotient_fixed_finrank_sub [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (S : Submodule ℂ V)
    (hS : ∀ g, S ≤ S.comap (ρ g)) :
    Module.finrank ℂ (ρ.quotient S hS).invariants =
      Module.finrank ℂ ρ.invariants - Module.finrank ℂ ↥(S ⊓ ρ.invariants) := by
  have h := stableQuotient_fixed_finrank ρ S hS
  omega

/-- The representation on one successive quotient of a stable filtration. -/
def stableFiltrationLayer (ρ : Representation ℂ G V) (F : ℕ → Submodule ℂ V)
    (hF : ∀ n g, F n ≤ (F n).comap (ρ g)) (n : ℕ) :
    Representation ℂ G (F (n + 1) ⧸ (F n).comap (F (n + 1)).subtype) :=
  (ρ.subrepresentation (F (n + 1)) (hF (n + 1))).quotient
    ((F n).comap (F (n + 1)).subtype) (fun g v hv => hF n g hv)

/-- Fixed dimensions add across each successive quotient of a stable filtration. -/
theorem stableFiltrationLayer_fixed_finrank [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (F : ℕ → Submodule ℂ V)
    (hF : ∀ n g, F n ≤ (F n).comap (ρ g)) (hmono : Monotone F) (n : ℕ) :
    Module.finrank ℂ (stableFiltrationLayer ρ F hF n).invariants +
      Module.finrank ℂ ↥(F n ⊓ ρ.invariants) =
        Module.finrank ℂ ↥(F (n + 1) ⊓ ρ.invariants) := by
  let τ := ρ.subrepresentation (F (n + 1)) (hF (n + 1))
  let S := (F n).comap (F (n + 1)).subtype
  have hs : ∀ g, S ≤ S.comap (τ g) := fun g v hv => hF n g hv
  have h := stableQuotient_fixed_finrank τ S hs
  let e : ↥(S ⊓ τ.invariants) ≃ₗ[ℂ] ↥(F n ⊓ ρ.invariants) :=
    { toFun := fun v =>
        ⟨v.val.val, v.property.1, fun g => congrArg Subtype.val (v.property.2 g)⟩
      invFun := fun v => ⟨⟨v.val, hmono (Nat.le_succ n) v.property.1⟩,
        v.property.1, fun g => Subtype.ext (v.property.2 g)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [e.finrank_eq, (stableSubspaceFixedEquiv ρ (F (n + 1))
    (hF (n + 1))).finrank_eq] at h
  exact h

/-- Passing to the associated graded of a finite stable filtration preserves fixed dimension. -/
theorem stableFiltration_fixed_finrank [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (F : ℕ → Submodule ℂ V)
    (hF : ∀ n g, F n ≤ (F n).comap (ρ g)) (hmono : Monotone F)
    (hzero : F 0 = ⊥) (d : ℕ) (htop : F d = ⊤) :
    (∑ n ∈ Finset.range d,
      Module.finrank ℂ (stableFiltrationLayer ρ F hF n).invariants) =
        Module.finrank ℂ ρ.invariants := by
  have hsum : ∀ m, (∑ n ∈ Finset.range m,
      Module.finrank ℂ (stableFiltrationLayer ρ F hF n).invariants) =
        Module.finrank ℂ ↥(F m ⊓ ρ.invariants) := by
    intro m
    induction m with
    | zero => rw [hzero, bot_inf_eq]; simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih, add_comm]
        exact stableFiltrationLayer_fixed_finrank ρ F hF hmono m
  have h := hsum d
  rw [htop, top_inf_eq] at h
  exact h

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.finiteRepresentationAverage_fixed
#print axioms VOA.DeligneAudit.SL4T.finiteRepresentationAverage_id
#print axioms VOA.DeligneAudit.SL4T.finiteRepresentationAverage_map
#print axioms VOA.DeligneAudit.SL4T.representationFixedMap_surjective
#print axioms VOA.DeligneAudit.SL4T.stableQuotient_fixed_finrank
#print axioms VOA.DeligneAudit.SL4T.stableQuotient_fixed_finrank_sub
#print axioms VOA.DeligneAudit.SL4T.stableFiltrationLayer_fixed_finrank
#print axioms VOA.DeligneAudit.SL4T.stableFiltration_fixed_finrank
