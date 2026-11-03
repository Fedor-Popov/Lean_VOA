import VOA.Classification.COne.McRaeM2FinLen

/-!
# McRae's route: the contragredient is a contravariant functor (transposes)

For graded weak modules `N₁, N₂` (`C2Rigid.GWModule`) and a weak-module homomorphism
`f : N₁ → N₂` preserving the gradings (automatic for generalized-eigenspace gradings,
`gradedHom_of_isGenGraded`):

* `transpose f hf : contra N₂ → contra N₁`, a weak-module homomorphism, characterized by
  `⟨transpose f g, x⟩ = ⟨g, f x⟩` (`pairing_transpose`);
* `transpose_injective_of_surjective` — `f` onto ⟹ `f'` one-to-one;
* `transpose_surjective_of_injective` — `f` one-to-one ⟹ `f'` onto.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Huang.LogRemovalAdmissible

universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂] {W : VertexOperatorAlgebra V}

section Transpose
variable (N₁ : GWModule W M₁) (N₂ : GWModule W M₂)
  (f : N₁.toWeakModule.Hom N₂.toWeakModule)
  (hf : ∀ α : ℂ, ∀ x ∈ N₁.weight α, f.toLinearMap x ∈ N₂.weight α)

/-- Weak-module homomorphisms between generalized-eigenspace-graded modules preserve gradings. -/
theorem gradedHom_of_isGenGraded (h₁ : IsGenGraded N₁) (h₂ : IsGenGraded N₂) :
    ∀ α : ℂ, ∀ x ∈ N₁.weight α, f.toLinearMap x ∈ N₂.weight α := by
  intro α x hx
  rw [weight_eq_maxGen N₂ h₂]
  have hx' := h₁ α hx
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx'
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨k, ?_⟩
  have hp : ∀ (j : ℕ) (y : M₁), ((L0 N₂.toWeakModule - α • 1) ^ j) (f.toLinearMap y) =
      f.toLinearMap (((L0 N₁.toWeakModule - α • 1) ^ j) y) := by
    intro j
    induction j with
    | zero => intro y; rfl
    | succ j ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply,
        LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        Module.End.one_apply, Module.End.one_apply, map_sub, map_smul]
      congr 1
      exact (f.map_act W.conformalVector 1 _).symm
  rw [hp, hk, map_zero]

include hf in
/-- The restriction of `f` to a graded piece. -/
def wRes (α : ℂ) : N₁.weight α →ₗ[ℂ] N₂.weight α :=
  f.toLinearMap.restrict (hf α)

/-- The transpose, as a linear map of restricted duals. -/
def transposeL : RestrictedDual N₂ →ₗ[ℂ] RestrictedDual N₁ :=
  DirectSum.toModule ℂ ℂ (RestrictedDual N₁)
    (fun α => (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N₁.weight β)) α) ∘ₗ
      (wRes N₁ N₂ f hf α).dualMap)

theorem transposeL_lof (α : ℂ) (g : Module.Dual ℂ (N₂.weight α)) :
    transposeL N₁ N₂ f hf (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N₂.weight β)) α g) =
      DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N₁.weight β)) α (g ∘ₗ wRes N₁ N₂ f hf α) := by
  unfold transposeL
  exact DirectSum.toModule_lof ℂ (φ := fun α =>
    (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N₁.weight β)) α) ∘ₗ
      (wRes N₁ N₂ f hf α).dualMap) α g

theorem component_transposeL (α : ℂ) (g : RestrictedDual N₂) :
    DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₁.weight β)) α (transposeL N₁ N₂ f hf g) =
      (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₂.weight β)) α g) ∘ₗ
        wRes N₁ N₂ f hf α := by
  classical
  refine DirectSum.induction_on (β := fun β => Module.Dual ℂ (N₂.weight β)) g ?_ ?_ ?_
  · have h0 : transposeL N₁ N₂ f hf (0 : RestrictedDual N₂) = 0 := LinearMap.map_zero _
    have h1 : DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₂.weight β)) α
        (0 : RestrictedDual N₂) = 0 := LinearMap.map_zero _
    have h2 : DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₁.weight β)) α
        (0 : RestrictedDual N₁) = 0 := LinearMap.map_zero _
    change DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₁.weight β)) α
      (transposeL N₁ N₂ f hf (0 : RestrictedDual N₂)) =
      (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₂.weight β)) α
        (0 : RestrictedDual N₂)) ∘ₗ wRes N₁ N₂ f hf α
    rw [h0, h1, h2, LinearMap.zero_comp]
  · intro β h
    have hof : (DirectSum.of (fun β => Module.Dual ℂ (N₂.weight β)) β h)
        = DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N₂.weight β)) β h := rfl
    rw [hof, transposeL_lof]
    by_cases hβ : β = α
    · subst hβ
      rw [DirectSum.component.lof_self, DirectSum.component.lof_self]
    · rw [DirectSum.component.of, DirectSum.component.of, dif_neg hβ, dif_neg hβ]
      rfl
  · intro a b ha hb
    have h0 : transposeL N₁ N₂ f hf ((a + b : RestrictedDual N₂)) =
        transposeL N₁ N₂ f hf a + transposeL N₁ N₂ f hf b := LinearMap.map_add _ _ _
    have h1 : DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₂.weight β)) α
        ((a + b : RestrictedDual N₂)) =
        DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₂.weight β)) α a +
        DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₂.weight β)) α b :=
      LinearMap.map_add _ _ _
    have h2 : ∀ c d : RestrictedDual N₁, DirectSum.component ℂ ℂ
        (fun β => Module.Dual ℂ (N₁.weight β)) α (c + d) =
        DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₁.weight β)) α c +
        DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₁.weight β)) α d :=
      fun c d => LinearMap.map_add _ _ _
    change DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₁.weight β)) α
      (transposeL N₁ N₂ f hf ((a + b : RestrictedDual N₂))) =
      (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N₂.weight β)) α
        ((a + b : RestrictedDual N₂))) ∘ₗ wRes N₁ N₂ f hf α
    rw [h0, h1, h2, ha, hb, LinearMap.add_comp]

/-- The transpose is the adjoint of `f` for the canonical pairing. -/
theorem pairing_transposeL {α : ℂ} {x : M₁} (hx : x ∈ N₁.weight α) (g : RestrictedDual N₂) :
    dualPairing N₁ x (transposeL N₁ N₂ f hf g) = dualPairing N₂ (f.toLinearMap x) g := by
  rw [dualPairing_component N₁ _ hx, dualPairing_component N₂ _ (hf α x hx),
    component_transposeL]
  rfl

include hf in
/-- `f` commutes with the `Y`-side adjoint operators. -/
theorem map_dualAdj {wt : ℤ} {u : V} (hu : u ∈ W.grading wt) (k : ℤ) {α : ℂ} {x : M₁}
    (hx : x ∈ N₁.weight α) :
    f.toLinearMap (dualAdj N₁ wt u k α x) = dualAdj N₂ wt u k α (f.toLinearMap x) := by
  rw [dualAdj_clean N₁ hu k hx, dualAdj_clean N₂ hu k (hf α x hx), map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  congr 1
  exact f.map_act _ _ x

/-- The transpose intertwines the contragredient modes. -/
theorem transposeL_mode (u : V) (n : ℤ) (g : RestrictedDual N₂) :
    transposeL N₁ N₂ f hf (mode (YMdual N₂ u) n g) =
      mode (YMdual N₁ u) n (transposeL N₁ N₂ f hf g) := by
  apply restrictedDual_ext_of_pairing N₁
  intro α x hx
  have hu : u ∈ ⨆ w, W.grading w := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction W.grading
    (motive := fun u => dualPairing N₁ x (transposeL N₁ N₂ f hf (mode (YMdual N₂ u) n g)) =
      dualPairing N₁ x (mode (YMdual N₁ u) n (transposeL N₁ N₂ f hf g))) hu ?_ ?_ ?_
  · intro w a ha
    rw [pairing_transposeL N₁ N₂ f hf hx, dualPairing_mode_dualAdj N₂ ha n g (hf α x hx),
      dualPairing_mode_dualAdj N₁ ha n _ hx,
      pairing_transposeL N₁ N₂ f hf (dualAdj_mem N₁ w a n α x), map_dualAdj N₁ N₂ f hf ha n hx]
  · show dualPairing N₁ x (transposeL N₁ N₂ f hf (mode (YMdual N₂ 0) n g)) =
      dualPairing N₁ x (mode (YMdual N₁ 0) n (transposeL N₁ N₂ f hf g))
    have h2 : mode (YMdual N₂ (0 : V)) n = 0 := by rw [map_zero]; rfl
    have h1 : mode (YMdual N₁ (0 : V)) n = 0 := by rw [map_zero]; rfl
    rw [h1, h2, LinearMap.zero_apply, LinearMap.zero_apply,
      show transposeL N₁ N₂ f hf (0 : RestrictedDual N₂) = 0 from LinearMap.map_zero _]
  · intro a b ha hb
    show dualPairing N₁ x (transposeL N₁ N₂ f hf (mode (YMdual N₂ (a + b)) n g)) =
      dualPairing N₁ x (mode (YMdual N₁ (a + b)) n (transposeL N₁ N₂ f hf g))
    have e₂ : mode (YMdual N₂ (a + b)) n g = mode (YMdual N₂ a) n g + mode (YMdual N₂ b) n g := by
      rw [map_add]; rfl
    have e₁ : mode (YMdual N₁ (a + b)) n (transposeL N₁ N₂ f hf g) =
        mode (YMdual N₁ a) n (transposeL N₁ N₂ f hf g) +
          mode (YMdual N₁ b) n (transposeL N₁ N₂ f hf g) := by
      rw [map_add]; rfl
    rw [e₂, e₁, LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, ha, hb]

/-- **The transpose** `f' : N₂' → N₁'`, a homomorphism of contragredient weak modules. -/
def transpose : (contra N₂).toWeakModule.Hom (contra N₁).toWeakModule where
  toLinearMap := transposeL N₁ N₂ f hf
  map_act u n g := transposeL_mode N₁ N₂ f hf u n g

@[simp] theorem transpose_apply (g : RestrictedDual N₂) :
    (transpose N₁ N₂ f hf).toLinearMap g = transposeL N₁ N₂ f hf g := rfl

include hf in
/-- If `f` maps onto, it maps each graded piece onto. -/
theorem exists_preimage_weight (hsurj : Function.Surjective f.toLinearMap) {α : ℂ} {y : M₂}
    (hy : y ∈ N₂.weight α) : ∃ x ∈ N₁.weight α, f.toLinearMap x = y := by
  classical
  obtain ⟨x, rfl⟩ := hsurj y
  refine ⟨cmp N₁ α x, cmp_mem N₁ α x, ?_⟩
  obtain ⟨s, hs0, hsum⟩ := exists_sum_cmp N₁ x
  have hfx : f.toLinearMap x = ∑ β ∈ s, f.toLinearMap (cmp N₁ β x) := by
    rw [← map_sum, hsum]
  -- compare `α`-components of `f x`
  have hc : cmp N₂ α (f.toLinearMap x) = f.toLinearMap x := cmp_of_mem N₂ hy
  have hc2 : cmp N₂ α (f.toLinearMap x) = f.toLinearMap (cmp N₁ α x) := by
    rw [hfx]
    have hlin : ∀ (t : Finset ℂ) (c : ℂ → M₂),
        cmp N₂ α (∑ β ∈ t, c β) = ∑ β ∈ t, cmp N₂ α (c β) := by
      intro t c
      induction t using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        have h := cmp_smul N₂ α 0 (0 : M₂)
        rwa [zero_smul, zero_smul] at h
      | insert a t hat ih => rw [Finset.sum_insert hat, Finset.sum_insert hat, cmp_add, ih]
    rw [hlin]
    by_cases hα : α ∈ s
    · rw [Finset.sum_eq_single_of_mem α hα]
      · exact cmp_of_mem N₂ (hf α _ (cmp_mem N₁ α x))
      · intro β _ hne
        exact cmp_of_mem_ne N₂ (hf β _ (cmp_mem N₁ β x)) hne
    · rw [hs0 α hα, map_zero, Finset.sum_eq_zero]
      intro β hβ
      exact cmp_of_mem_ne N₂ (hf β _ (cmp_mem N₁ β x)) (fun h => hα (h ▸ hβ))
  rw [← hc2, hc]

/-- `f` onto ⟹ `f'` one-to-one. -/
theorem transpose_injective_of_surjective (hsurj : Function.Surjective f.toLinearMap) :
    Function.Injective (transpose N₁ N₂ f hf).toLinearMap := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro g hg
  have hg0 : transposeL N₁ N₂ f hf g = 0 := hg
  have : g = 0 := by
    apply restrictedDual_ext_of_pairing N₂
    intro α y hy
    obtain ⟨x, hx, rfl⟩ := exists_preimage_weight N₁ N₂ f hf hsurj hy
    rw [← pairing_transposeL N₁ N₂ f hf hx, hg0, LinearMap.map_zero, LinearMap.map_zero]
  rw [this]; exact Submodule.zero_mem _

/-- `f` one-to-one ⟹ `f'` onto. -/
theorem transpose_surjective_of_injective (hinj : Function.Injective f.toLinearMap) :
    Function.Surjective (transpose N₁ N₂ f hf).toLinearMap := by
  classical
  have hres : ∀ α, Function.Surjective (wRes N₁ N₂ f hf α).dualMap := by
    intro α
    apply LinearMap.dualMap_surjective_of_injective
    intro a b h
    apply Subtype.ext
    exact hinj (congrArg Subtype.val h)
  intro φ
  refine DirectSum.induction_on (β := fun β => Module.Dual ℂ (N₁.weight β)) φ ?_ ?_ ?_
  · exact ⟨0, LinearMap.map_zero _⟩
  · intro α h
    obtain ⟨g, hg⟩ := hres α h
    refine ⟨DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N₂.weight β)) α g, ?_⟩
    rw [transpose_apply, transposeL_lof]
    rw [← hg]
    rfl
  · rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, by rw [LinearMap.map_add, hx, hy]; rfl⟩

end Transpose

end VOA.C2Rigid
