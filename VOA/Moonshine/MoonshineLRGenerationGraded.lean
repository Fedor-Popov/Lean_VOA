import VOA.Moonshine.MoonshineCNRelativePBW
import VOA.Moonshine.MoonshineLRGenerationSeries

/-!
# Graded PBW for `U(L)`

Let `L` be a complex Lie algebra with a grading `wt : G → Submodule ℂ L` (a direct sum
decomposition with `⁅L_γ, L_δ⁆ ⊆ L_{γ+δ}`), and `b` a homogeneous basis, `b a ∈ L_{deg a}`.

* `envPBWBasis b`: the ordered monomials `ι(b a₁) ⋯ ι(b a_k)` (`a₁ ≤ ⋯ ≤ a_k`) form a basis of
  `U(L)`, indexed by `Multiset A`. This is `relativePBWEquiv`, induced from the zero
  subalgebra.
* `envCoaction`: the algebra map `U(L) → U(L)[G]` with `ι x ↦ single γ (ι x)` for `x ∈ L_γ`.
  It exists by the universal property, and `envGraded Γ := {a | Δ a = single Γ a}` is the
  grading of `U(L)`.
* **`finrank_envGraded_eq_expCount`**: for degrees in the open cone `ℕ × ℕ`,
  `dim U(L)_Γ = expCount deg low Γ`, the number of exponent vectors of weight `Γ`.

With `expSeries_eq_coneProd`, this gives the PBW character `Σ_Γ dim U(L)_Γ e^Γ =
Π (1 − e^γ)^{−dim L_γ}`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open UniversalEnvelopingAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-! ### The PBW basis of `U(L)` -/

section PBW

variable {A : Type*} (b : Basis A ℂ L)

/-- The word `ι(b a₁) ⋯ ι(b a_k)` in `U(L)`. -/
def envPBWWord (l : List A) : UniversalEnvelopingAlgebra ℂ L :=
  (l.map fun a => ι ℂ (b a)).prod

theorem envPBWWord_nil : envPBWWord b [] = 1 := by simp [envPBWWord]

theorem envPBWWord_cons (a : A) (l : List A) :
    envPBWWord b (a :: l) = ι ℂ (b a) * envPBWWord b l := by simp [envPBWWord]

/-- The complement `⊤` of the zero subalgebra. -/
theorem isCompl_bot_top_lie :
    IsCompl (⊥ : LieSubalgebra ℂ L).toSubmodule (⊤ : Submodule ℂ L) := by
  rw [LieSubalgebra.bot_toSubmodule]
  exact isCompl_bot_top

/-- The basis `b`, viewed on the complement `⊤`. -/
def envTopBasis : Basis A ℂ (⊤ : Submodule ℂ L) := b.map Submodule.topEquiv.symm

theorem coe_envTopBasis (a : A) : ((envTopBasis b a : (⊤ : Submodule ℂ L)) : L) = b a := by
  simp [envTopBasis, Basis.map_apply]

/-- The trivial bottom representation `⊥ → End ℂ`. -/
abbrev envBottomRep : (⊥ : LieSubalgebra ℂ L) →ₗ⁅ℂ⁆ Module.End ℂ ℂ := 0

theorem relativeInducedWord_bot (l : List A) (u : ℂ) :
    relativeInducedWord (⊥ : LieSubalgebra ℂ L) envBottomRep (envTopBasis b) l u =
      Submodule.Quotient.mk (envPBWWord b l ⊗ₜ[ℂ] u) := by
  induction l with
  | nil => rw [relativeInducedWord_nil, envPBWWord_nil]; rfl
  | cons a l ih =>
      rw [relativeInducedWord_cons, ih, envPBWWord_cons, ← coe_envTopBasis b a]
      rfl

variable [LinearOrder A]

/-- PBW coordinates on `U(L)`: `a ↦ [a ⊗ 1]` followed by relative PBW coordinates. -/
def envPBWCoordinates : UniversalEnvelopingAlgebra ℂ L →ₗ[ℂ] (Multiset A →₀ ℂ) :=
  relativePBWCoordinates (⊥ : LieSubalgebra ℂ L) envBottomRep isCompl_bot_top_lie
      (envTopBasis b) ∘ₗ
    (PBWTheorem.balancing (⊥ : LieSubalgebra ℂ L) envBottomRep).mkQ ∘ₗ
      (TensorProduct.mk ℂ (UniversalEnvelopingAlgebra ℂ L) ℂ).flip 1

/-- **Sorted words have coordinates `single m 1`.** -/
theorem envPBWCoordinates_word (l : List A) (hl : l.Pairwise (· ≤ ·)) :
    envPBWCoordinates b (envPBWWord b l) = Finsupp.single (l : Multiset A) 1 := by
  change relativePBWCoordinates _ _ _ _ (Submodule.Quotient.mk (envPBWWord b l ⊗ₜ[ℂ] 1)) = _
  rw [← relativeInducedWord_bot, relativePBWCoordinates_word _ _ _ _ l hl]

theorem balancing_bot_eq_bot :
    PBWTheorem.balancing (⊥ : LieSubalgebra ℂ L) envBottomRep = ⊥ := by
  rw [PBWTheorem.balancing, Submodule.span_eq_bot]
  rintro _ ⟨y, x, u, rfl⟩
  have hx : (x : L) = 0 := (LieSubalgebra.mem_bot (x : L)).mp x.2
  simp [hx]

theorem envPBWCoordinates_injective : Function.Injective (envPBWCoordinates b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h := relativeInducedWordMap_coordinates (⊥ : LieSubalgebra ℂ L) envBottomRep
    isCompl_bot_top_lie (envTopBasis b)
    (Submodule.Quotient.mk (a ⊗ₜ[ℂ] (1 : ℂ)))
  change relativeInducedWordMap _ _ _ (envPBWCoordinates b a) = _ at h
  rw [ha, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero, balancing_bot_eq_bot,
    Submodule.mem_bot] at h
  have h2 := congrArg (TensorProduct.rid ℂ (UniversalEnvelopingAlgebra ℂ L)) h
  simpa using h2

theorem envPBWCoordinates_surjective : Function.Surjective (envPBWCoordinates b) := by
  intro v
  refine ⟨v.sum fun m c => c • envPBWWord b (m.sort (· ≤ ·)), ?_⟩
  rw [map_finsuppSum]
  conv_rhs => rw [← Finsupp.sum_single v]
  refine Finsupp.sum_congr fun m _ => ?_
  rw [map_smul, envPBWCoordinates_word b _ (Multiset.pairwise_sort m (· ≤ ·)), Multiset.sort_eq,
    Finsupp.smul_single_one]

/-- PBW: `U(L) ≃ (Multiset A →₀ ℂ)`. -/
def envPBWEquiv : UniversalEnvelopingAlgebra ℂ L ≃ₗ[ℂ] (Multiset A →₀ ℂ) :=
  LinearEquiv.ofBijective (envPBWCoordinates b)
    ⟨envPBWCoordinates_injective b, envPBWCoordinates_surjective b⟩

/-- **The PBW basis of `U(L)`**: ordered monomials in the basis `b`. -/
def envPBWBasis : Basis (Multiset A) ℂ (UniversalEnvelopingAlgebra ℂ L) :=
  Basis.ofRepr (envPBWEquiv b)

theorem envPBWBasis_apply (m : Multiset A) :
    envPBWBasis b m = envPBWWord b (m.sort (· ≤ ·)) := by
  rw [envPBWBasis, Basis.coe_ofRepr, LinearEquiv.symm_apply_eq]
  change _ = envPBWCoordinates b _
  rw [envPBWCoordinates_word b _ (Multiset.pairwise_sort m (· ≤ ·)), Multiset.sort_eq]

end PBW

/-! ### The grading of `U(L)` -/

section Graded

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]
variable (wt : G → Submodule ℂ L) [DirectSum.Decomposition wt]
variable (hbr : ∀ {γ δ : G} {x y : L}, x ∈ wt γ → y ∈ wt δ → ⁅x, y⁆ ∈ wt (γ + δ))

/-- `x ↦ Σ_γ single γ (ι x_γ)`. -/
def envGradedComp : L →ₗ[ℂ] AddMonoidAlgebra (UniversalEnvelopingAlgebra ℂ L) G :=
  DirectSum.toModule ℂ G _ (fun γ => AddMonoidAlgebra.lsingle (R := ℂ) γ ∘ₗ
      (ι ℂ : L →ₗ⁅ℂ⁆ UniversalEnvelopingAlgebra ℂ L).toLinearMap ∘ₗ (wt γ).subtype) ∘ₗ
    (DirectSum.decomposeLinearEquiv wt).toLinearMap

omit [AddCommMonoid G] in
theorem envGradedComp_of_mem {γ : G} {x : L} (hx : x ∈ wt γ) :
    envGradedComp wt x = AddMonoidAlgebra.single γ (ι ℂ x) := by
  simp only [envGradedComp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem wt hx,
    ← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof]
  rfl

include hbr in
theorem envGradedComp_lie (x y : L) :
    envGradedComp wt ⁅x, y⁆ = ⁅envGradedComp wt x, envGradedComp wt y⁆ := by
  have htop := (DirectSum.Decomposition.isInternal wt).submodule_iSup_eq_top
  have hx : x ∈ ⨆ γ, wt γ := htop ▸ Submodule.mem_top
  induction hx using Submodule.iSup_induction' generalizing y with
  | mem γ x hx =>
      have hy : y ∈ ⨆ γ, wt γ := htop ▸ Submodule.mem_top
      induction hy using Submodule.iSup_induction' with
      | mem δ y hy =>
          rw [envGradedComp_of_mem wt (hbr hx hy), envGradedComp_of_mem wt hx,
            envGradedComp_of_mem wt hy, LieHom.map_lie, Ring.lie_def, Ring.lie_def,
            AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, add_comm δ γ]
          exact Finsupp.single_sub (γ + δ) (ι ℂ x * ι ℂ y) (ι ℂ y * ι ℂ x)
      | zero => simp
      | add y₁ y₂ _ _ h₁ h₂ => rw [lie_add, map_add, h₁, h₂, map_add, lie_add]
  | zero => simp
  | add x₁ x₂ _ _ h₁ h₂ => rw [add_lie, map_add, h₁, h₂, map_add, add_lie]

/-- The Lie map `L → U(L)[G]`. -/
def envGradedLie : L →ₗ⁅ℂ⁆ AddMonoidAlgebra (UniversalEnvelopingAlgebra ℂ L) G :=
  { envGradedComp wt with map_lie' := fun {x y} => envGradedComp_lie wt hbr x y }

/-- **The coaction** `Δ : U(L) → U(L)[G]`, `ι x ↦ single γ (ι x)` for `x ∈ L_γ`. -/
def envCoaction : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ]
    AddMonoidAlgebra (UniversalEnvelopingAlgebra ℂ L) G :=
  lift ℂ (envGradedLie wt hbr)

theorem envCoaction_ι_of_mem {γ : G} {x : L} (hx : x ∈ wt γ) :
    envCoaction wt hbr (ι ℂ x) = AddMonoidAlgebra.single γ (ι ℂ x) := by
  rw [envCoaction, lift_ι_apply]
  exact envGradedComp_of_mem wt hx

/-- The degree-`Γ` part of `U(L)`: `{a | Δ a = single Γ a}`. -/
def envGraded (Γ : G) : Submodule ℂ (UniversalEnvelopingAlgebra ℂ L) :=
  LinearMap.ker ((envCoaction wt hbr).toLinearMap - AddMonoidAlgebra.lsingle (R := ℂ) Γ)

theorem mem_envGraded {Γ : G} {a : UniversalEnvelopingAlgebra ℂ L} :
    a ∈ envGraded wt hbr Γ ↔ envCoaction wt hbr a = AddMonoidAlgebra.single Γ a := by
  rw [envGraded, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

theorem ι_mem_envGraded {γ : G} {x : L} (hx : x ∈ wt γ) : ι ℂ x ∈ envGraded wt hbr γ :=
  (mem_envGraded wt hbr).mpr (envCoaction_ι_of_mem wt hbr hx)

theorem one_mem_envGraded : (1 : UniversalEnvelopingAlgebra ℂ L) ∈ envGraded wt hbr 0 := by
  rw [mem_envGraded, map_one, AddMonoidAlgebra.one_def]

theorem mul_mem_envGraded {Γ Δ : G} {a c : UniversalEnvelopingAlgebra ℂ L}
    (ha : a ∈ envGraded wt hbr Γ) (hc : c ∈ envGraded wt hbr Δ) :
    a * c ∈ envGraded wt hbr (Γ + Δ) := by
  rw [mem_envGraded] at ha hc ⊢
  rw [map_mul, ha, hc, AddMonoidAlgebra.single_mul_single]

variable {A : Type*} [LinearOrder A] (b : Basis A ℂ L) (deg : A → G)
  (hb : ∀ a, b a ∈ wt (deg a))

omit [LinearOrder A] in
include hb in
theorem envPBWWord_mem (l : List A) : envPBWWord b l ∈ envGraded wt hbr (l.map deg).sum := by
  induction l with
  | nil => rw [envPBWWord_nil, List.map_nil, List.sum_nil]; exact one_mem_envGraded wt hbr
  | cons a l ih =>
      rw [envPBWWord_cons, List.map_cons, List.sum_cons]
      exact mul_mem_envGraded wt hbr (ι_mem_envGraded wt hbr (hb a)) ih

include hb in
theorem envPBWBasis_mem (m : Multiset A) :
    envPBWBasis b m ∈ envGraded wt hbr (m.map deg).sum := by
  rw [envPBWBasis_apply]
  have h := envPBWWord_mem wt hbr b deg hb (m.sort (· ≤ ·))
  rwa [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq] at h

/-- The projection `a ↦ (Δ a)_Γ`. -/
def envGradedProj (Γ : G) : UniversalEnvelopingAlgebra ℂ L →ₗ[ℂ] UniversalEnvelopingAlgebra ℂ L :=
  Finsupp.lapply Γ ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap ∘ₗ
    (envCoaction wt hbr).toLinearMap

theorem envGradedProj_basis {κ : Type*} (B : Basis κ ℂ (UniversalEnvelopingAlgebra ℂ L))
    (w : κ → G) (hB : ∀ k, B k ∈ envGraded wt hbr (w k)) (Γ : G) (k : κ) :
    envGradedProj wt hbr Γ (B k) = if w k = Γ then B k else 0 := by
  have h := (mem_envGraded wt hbr).mp (hB k)
  simp only [envGradedProj, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h,
    LinearEquiv.coe_coe, Finsupp.lapply_apply]
  change (Finsupp.single _ _ : G →₀ _) Γ = _
  rw [Finsupp.single_apply]

theorem repr_envGradedProj {κ : Type*} (B : Basis κ ℂ (UniversalEnvelopingAlgebra ℂ L))
    (w : κ → G) (hB : ∀ k, B k ∈ envGraded wt hbr (w k)) (Γ : G)
    (a : UniversalEnvelopingAlgebra ℂ L) (k : κ) :
    B.repr (envGradedProj wt hbr Γ a) k = if w k = Γ then B.repr a k else 0 := by
  have h : (Finsupp.lapply k ∘ₗ B.repr.toLinearMap ∘ₗ envGradedProj wt hbr Γ) =
      if w k = Γ then Finsupp.lapply k ∘ₗ B.repr.toLinearMap else 0 := by
    refine B.ext fun k' => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      envGradedProj_basis wt hbr B w hB]
    by_cases hk : k' = k
    · subst hk
      split_ifs <;> simp
    · split_ifs <;> simp [hk]
  have h2 := LinearMap.congr_fun h a
  split_ifs at h2 ⊢ <;> simpa using h2

/-- The coordinates of a degree-`Γ` element in a homogeneous basis are supported on weight `Γ`. -/
theorem repr_eq_zero_of_mem_envGraded {κ : Type*}
    (B : Basis κ ℂ (UniversalEnvelopingAlgebra ℂ L)) (w : κ → G)
    (hB : ∀ k, B k ∈ envGraded wt hbr (w k)) {Γ : G} {a : UniversalEnvelopingAlgebra ℂ L}
    (ha : a ∈ envGraded wt hbr Γ) {k : κ} (hk : w k ≠ Γ) : B.repr a k = 0 := by
  have h := repr_envGradedProj wt hbr B w hB (w k) a k
  rw [if_pos rfl] at h
  rw [← h]
  have hp : envGradedProj wt hbr (w k) a = 0 := by
    simp only [envGradedProj, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      (mem_envGraded wt hbr).mp ha, LinearEquiv.coe_coe, Finsupp.lapply_apply]
    change (Finsupp.single _ _ : G →₀ _) _ = 0
    rw [Finsupp.single_apply, if_neg (Ne.symm hk)]
  rw [hp, map_zero, Finsupp.zero_apply]

/-- **Dimension of a graded piece from any homogeneous basis of `U(L)`:** if `S` is the finite set
of basis indices of weight `Γ`, then `dim U(L)_Γ = #S`. -/
theorem finrank_envGraded_of_basis {κ : Type*}
    (B : Basis κ ℂ (UniversalEnvelopingAlgebra ℂ L)) (w : κ → G)
    (hB : ∀ k, B k ∈ envGraded wt hbr (w k)) (Γ : G) (S : Finset κ)
    (hS : ∀ k, k ∈ S ↔ w k = Γ) :
    finrank ℂ (envGraded wt hbr Γ) = S.card := by
  have hspan : envGraded wt hbr Γ = Submodule.span ℂ (Set.range fun k : S => B (k : κ)) := by
    apply le_antisymm
    · intro a ha
      refine Submodule.span_mono ?_ (B.mem_span_repr_support a)
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨⟨k, (hS k).mpr ?_⟩, rfl⟩
      by_contra hne
      exact (Finsupp.mem_support_iff.mp hk) (repr_eq_zero_of_mem_envGraded wt hbr B w hB ha hne)
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := hB (k : κ)
      rwa [(hS k).mp k.2] at this
  rw [hspan]
  exact (finrank_span_eq_card (B.linearIndependent.comp _ Subtype.val_injective)).trans
    (Fintype.card_coe S)

include hb in
/-- **Graded PBW.** If `S` is the finite set of multisets of weight `Γ`, the degree-`Γ` part of
`U(L)` has dimension `#S`. -/
theorem finrank_envGraded (Γ : G) (S : Finset (Multiset A))
    (hS : ∀ m, m ∈ S ↔ (m.map deg).sum = Γ) :
    finrank ℂ (envGraded wt hbr Γ) = S.card :=
  finrank_envGraded_of_basis wt hbr (envPBWBasis b) (fun m => (m.map deg).sum)
    (envPBWBasis_mem wt hbr b deg hb) Γ S hS

end Graded

/-! ### The cone count -/

section Cone

theorem expWeight_toFinsupp {A : Type*} [DecidableEq A] (deg : A → ℕ × ℕ) (m : Multiset A) :
    expWeight deg (Multiset.toFinsupp m) = (m.map deg).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [expWeight]
  | cons a m ih =>
      rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
        expWeight_add, expWeight_single, ih, one_smul, Multiset.map_add, Multiset.sum_add,
        Multiset.map_singleton, Multiset.sum_singleton]

variable (wt : ℕ × ℕ → Submodule ℂ L) [DirectSum.Decomposition wt]
variable (hbr : ∀ {γ δ : ℕ × ℕ} {x y : L}, x ∈ wt γ → y ∈ wt δ → ⁅x, y⁆ ∈ wt (γ + δ))
variable {A : Type*} [LinearOrder A] (b : Basis A ℂ L) (deg : A → ℕ × ℕ)
  (hb : ∀ a, b a ∈ wt (deg a))
  (hdeg : ∀ a, 1 ≤ (deg a).1 ∧ 1 ≤ (deg a).2)
  (low : (ℕ × ℕ) → Finset A) (hlow : ∀ Γ a, a ∈ low Γ ↔ deg a ≤ Γ)

include hb hdeg hlow in
/-- **Graded PBW in the cone:** `dim U(L)_Γ = expCount deg low Γ`. -/
theorem finrank_envGraded_eq_expCount (Γ : ℕ × ℕ) :
    finrank ℂ (envGraded wt hbr Γ) = expCount deg low Γ := by
  classical
  rw [finrank_envGraded wt hbr b deg hb Γ
    ((expVectors deg low Γ).map Multiset.toFinsupp.symm.toEquiv.toEmbedding), Finset.card_map,
    expCount]
  intro m
  rw [Finset.mem_map_equiv, mem_expVectors deg hdeg low hlow]
  change expWeight deg (Multiset.toFinsupp m) = _ ↔ _
  rw [expWeight_toFinsupp]

end Cone

end VOA.Moonshine.ConwayNorton.M8
