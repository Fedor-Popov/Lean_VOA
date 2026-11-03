/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.FusionTop
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The unit axiom of the fusion rules: `N^{P₃}_{V P₂} = [P₂ ≅ P₃]`

For intertwining operators of type `(M₃ / V M₂)` (first slot the adjoint module):

* `vac_mode_eq_zero` — `𝒴(𝟙, z)` has only the mode `𝒴(𝟙)₍₋₁₎` (from `L₋₁𝟙 = 0` and the
  `L₋₁`-derivative property);
* `isHom_vacMode` — `𝒴(𝟙)₍₋₁₎ : M₂ → M₃` commutes with every mode (commutator formula and
  `u₍ᵢ₎𝟙 = 0`, `i ≥ 0`);
* `eq_zero_of_vacMode` — `𝒴(𝟙)₍₋₁₎ = 0 ⟹ 𝒴 = 0` (the left annihilator is closed under modes by
  the Jacobi identity at `m = 0`, and `u = u₍₋₁₎𝟙`), for **any** modules `M₂, M₃`;

so `𝒴 ↦ 𝒴(𝟙)₍₋₁₎` embeds the intertwiner space into `Hom_V(M₂, M₃)` (`vacModeMap`).  With Schur's
lemma for irreducible lowest-weight modules (`exists_smul_eq_of_hom`, via an eigenvalue of the
finite-dimensional bottom) this gives

* `fusionRule_adjoint_le_one` and `finiteDimensional_intertwiningSpace_adjoint`;
* `fusionRule_adjoint_self` : `N^{P}_{V P} = 1`;
* `fusionRule_adjoint_eq_zero` : `N^{P₃}_{V P₂} = 0` when `P₂ ≇ P₃`.

This is the unit row `N_{0b}^c = δ_{bc}` of the fusion matrices in `HuangVerlindeFusionInput`.

## Status
No `sorry`, no new axioms; unconditional (irreducible lowest-weight `P₂, P₃`).
-/

namespace VOA.Huang.FusionUnit

open VOA VOA.Huang.FusionTop

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## §1  Module homomorphisms -/

section Hom

variable {M₂ M₃ : Type u} [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]

/-- The space of `V`-module homomorphisms `M₂ → M₃` (linear maps commuting with every mode). -/
def homSpace (A₂ : OrdVModule W M₂) (A₃ : OrdVModule W M₃) : Submodule ℂ (M₂ →ₗ[ℂ] M₃) where
  carrier := {f | ∀ (u : 𝒱) (n : ℤ) (x : M₂), f (mode (A₂.YM u) n x) = mode (A₃.YM u) n (f x)}
  zero_mem' := by intro u n x; simp
  add_mem' := by
    intro f g hf hg u n x
    simp only [LinearMap.add_apply, hf u n x, hg u n x, map_add]
  smul_mem' := by
    intro c f hf u n x
    simp only [LinearMap.smul_apply, hf u n x, map_smul]

variable {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}

/-- The kernel of a homomorphism, as a weak submodule. -/
def kerSub {f : M₂ →ₗ[ℂ] M₃} (hf : f ∈ homSpace A₂ A₃) :
    WeakModule.Submodule' A₂.toWeakModule where
  carrier := LinearMap.ker f
  act_mem u n x hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [WeakModule.act_def, hf u n x, hx, map_zero]

/-- The range of a homomorphism, as a weak submodule. -/
def rangeSub {f : M₂ →ₗ[ℂ] M₃} (hf : f ∈ homSpace A₂ A₃) :
    WeakModule.Submodule' A₃.toWeakModule where
  carrier := LinearMap.range f
  act_mem u n y hy := by
    obtain ⟨x, rfl⟩ := hy
    exact ⟨mode (A₂.YM u) n x, hf u n x⟩

/-- A nonzero homomorphism between irreducible modules is bijective. -/
theorem bijective_of_hom (h₂ : A₂.IsIrreducible) (h₃ : A₃.IsIrreducible) {f : M₂ →ₗ[ℂ] M₃}
    (hf : f ∈ homSpace A₂ A₃) (hf0 : f ≠ 0) : Function.Bijective f := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    rcases h₂.2 (kerSub hf) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hf0
  · rw [← LinearMap.range_eq_top]
    rcases h₃.2 (rangeSub hf) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hf0
    · exact h

/-- A module homomorphism preserves weight spaces. -/
theorem hom_mem_weight {f : M₂ →ₗ[ℂ] M₃} (hf : f ∈ homSpace A₂ A₃) {α : ℂ} {x : M₂}
    (hx : x ∈ A₂.weight α) : f x ∈ A₃.weight α := by
  apply eigenvector_mem_weight A₃
  rw [← hf, A₂.L0_weight α x hx, map_smul]

/-- **Schur's lemma** for irreducible lowest-weight modules: two homomorphisms `f, g : P₂ → P₃`
with `g ≠ 0` are proportional (`f = c • g`). -/
theorem exists_smul_eq_of_hom {P₂ P₃ : LWModule W} (h₂ : P₂.IsIrreducibleLW)
    (h₃ : P₃.IsIrreducibleLW) {f g : P₂.carrier →ₗ[ℂ] P₃.carrier}
    (hf : f ∈ homSpace P₂.isMod P₃.isMod) (hg : g ∈ homSpace P₂.isMod P₃.isMod) (hg0 : g ≠ 0) :
    ∃ c : ℂ, c • g = f := by
  let e := LinearEquiv.ofBijective g (bijective_of_hom h₂ h₃ hg hg0)
  have he : ∀ y, e.symm (g y) = y := fun y => e.symm_apply_apply y
  -- `h = g⁻¹ ∘ f` is an endomorphism of `P₂`
  set h : P₂.carrier →ₗ[ℂ] P₂.carrier := e.symm.toLinearMap ∘ₗ f with hh
  have hhom : h ∈ homSpace P₂.isMod P₂.isMod := by
    intro u n x
    simp only [hh, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [hf u n x]
    have : mode (P₃.isMod.YM u) n (f x) = g (mode (P₂.isMod.YM u) n (e.symm (f x))) := by
      rw [hg u n, show g (e.symm (f x)) = f x from e.apply_symm_apply (f x)]
    rw [this, he]
  -- restrict to the finite-dimensional, nonzero bottom and take an eigenvalue
  have hmaps : ∀ x ∈ P₂.isMod.weight P₂.h, h x ∈ P₂.isMod.weight P₂.h :=
    fun x hx => hom_mem_weight hhom hx
  let hb : Module.End ℂ (P₂.isMod.weight P₂.h) := h.restrict hmaps
  haveI : FiniteDimensional ℂ (P₂.isMod.weight P₂.h) := P₂.isMod.finrank P₂.h
  haveI : Nontrivial (P₂.isMod.weight P₂.h) := Submodule.nontrivial_iff_ne_bot.mpr P₂.realized
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue hb
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hv' : h (v : P₂.carrier) = c • (v : P₂.carrier) := by
    have := congrArg Subtype.val hv.apply_eq_smul
    simpa [hb] using this
  have hv0 : (v : P₂.carrier) ≠ 0 := fun h0 => hv.2 (Subtype.ext h0)
  -- the kernel of `h - c` is a nonzero submodule, hence everything
  have hsub : (h - c • LinearMap.id) ∈ homSpace P₂.isMod P₂.isMod := by
    intro u n x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul,
      hhom u n x]
  rcases h₂.2 (kerSub hsub) with hk | hk
  · exfalso
    have : (v : P₂.carrier) ∈ (kerSub hsub).carrier := by
      change _ ∈ LinearMap.ker _
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hv']; simp
    rw [hk, Submodule.mem_bot] at this
    exact hv0 this
  · refine ⟨c, LinearMap.ext fun x => ?_⟩
    have hx : x ∈ (kerSub hsub).carrier := by rw [hk]; trivial
    change x ∈ LinearMap.ker _ at hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
    have := congrArg g hx
    simp only [hh, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_smul] at this
    rw [show g (e.symm (f x)) = f x from e.apply_symm_apply (f x)] at this
    rw [LinearMap.smul_apply, ← this]

/-- `Hom_V(P₂, P₃)` is finite-dimensional of dimension `≤ 1`. -/
theorem finite_and_finrank_homSpace_le_one {P₂ P₃ : LWModule W} (h₂ : P₂.IsIrreducibleLW)
    (h₃ : P₃.IsIrreducibleLW) :
    FiniteDimensional ℂ (homSpace P₂.isMod P₃.isMod) ∧
      Module.finrank ℂ (homSpace P₂.isMod P₃.isMod) ≤ 1 := by
  by_cases hall : ∀ g ∈ homSpace P₂.isMod P₃.isMod, g = 0
  · have : Subsingleton (homSpace P₂.isMod P₃.isMod) :=
      ⟨fun a b => Subtype.ext (by rw [hall a a.2, hall b b.2])⟩
    exact ⟨inferInstance, by rw [Module.finrank_zero_of_subsingleton]; exact zero_le_one⟩
  · push Not at hall
    obtain ⟨g, hg, hg0⟩ := hall
    have hspan : ∀ f : homSpace P₂.isMod P₃.isMod, ∃ c : ℂ, c • (⟨g, hg⟩ : homSpace _ _) = f := by
      intro f
      obtain ⟨c, hc⟩ := exists_smul_eq_of_hom h₂ h₃ f.2 hg hg0
      exact ⟨c, Subtype.ext hc⟩
    refine ⟨?_, finrank_le_one _ hspan⟩
    refine Module.Finite.of_surjective (LinearMap.toSpanSingleton ℂ _ (⟨g, hg⟩ : homSpace _ _))
      (fun f => ?_)
    obtain ⟨c, hc⟩ := hspan f
    exact ⟨c, by simpa using hc⟩

/-- Post-composing an intertwining operator with a module homomorphism gives an intertwining
operator. -/
theorem isIntertwiningOperator_compHom {M₁ M₄ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₄] [Module ℂ M₄] {A₁ : OrdVModule W M₁} {A₄ : OrdVModule W M₄}
    {Y : IntertwiningModes M₁ M₂ M₃} (hY : IsIntertwiningOperator A₁ A₂ A₃ Y)
    {f : M₃ →ₗ[ℂ] M₄} (hf : f ∈ homSpace A₃ A₄) :
    IsIntertwiningOperator A₁ A₂ A₄ (fun n => (Y n).compr₂ f) := by
  refine ⟨fun w₁ w₂ n => ?_, fun w₁ n => ?_, fun u w₁ w₂ ℓ m n => ?_⟩
  · obtain ⟨N, hN⟩ := hY.truncation w₁ w₂ n
    exact ⟨N, fun k hk => by simp [hN k hk]⟩
  · ext x
    simp only [LinearMap.compr₂_apply, LinearMap.smul_apply]
    rw [hY.L_neg_one w₁ n, LinearMap.smul_apply, map_smul]
  · have hj := congrArg f (hY.jacobi u w₁ w₂ ℓ m n)
    change f (∑ᶠ i, IsIntertwiningOperator.jacL A₂ A₃ Y u w₁ w₂ ℓ m n i)
      = f (∑ᶠ i, IsIntertwiningOperator.jacR A₁ Y u w₁ w₂ ℓ m n i) at hj
    rw [map_finsum f (IsIntertwiningOperator.jacL_support_finite hY.truncation u w₁ w₂ ℓ m n),
      map_finsum f (IsIntertwiningOperator.jacR_support_finite Y u w₁ w₂ ℓ m n)] at hj
    convert hj using 2
    · funext i
      simp only [IsIntertwiningOperator.jacL, LinearMap.compr₂_apply, map_smul, map_sub,
        hf u _ _]
    · funext i
      simp only [IsIntertwiningOperator.jacR, LinearMap.compr₂_apply, map_smul]

/-- Precomposing the first slot of an intertwining operator with a module homomorphism gives an
intertwining operator. -/
theorem isIntertwiningOperator_precomp {M₀ M₁ : Type u} [AddCommGroup M₀] [Module ℂ M₀]
    [AddCommGroup M₁] [Module ℂ M₁] {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
    {Y : IntertwiningModes M₁ M₂ M₃} (hY : IsIntertwiningOperator A₁ A₂ A₃ Y)
    {g : M₀ →ₗ[ℂ] M₁} (hg : g ∈ homSpace A₀ A₁) :
    IsIntertwiningOperator A₀ A₂ A₃ (fun n => (Y n).comp g) := by
  refine ⟨fun w₀ w₂ n => hY.truncation (g w₀) w₂ n, fun w₀ n => ?_, fun u w₀ w₂ ℓ m n => ?_⟩
  · simp only [LinearMap.comp_apply]
    rw [show g (A₀.Lm1 w₀) = A₁.Lm1 (g w₀) from hg W.conformalVector 0 w₀, hY.L_neg_one]
  · simp only [LinearMap.comp_apply, hg u]
    exact hY.jacobi u (g w₀) w₂ ℓ m n

/-- A module isomorphism in the first slot identifies the intertwiner spaces. -/
noncomputable def intertwiningEquivLeft {M₀ M₁ : Type u} [AddCommGroup M₀] [Module ℂ M₀]
    [AddCommGroup M₁] [Module ℂ M₁] {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
    (e : ModuleEquiv W A₀ A₁) :
    intertwiningSpace A₁ A₂ A₃ ≃ₗ[ℂ] intertwiningSpace A₀ A₂ A₃ where
  toFun Y := ⟨fun n => ((Y : IntertwiningModes M₁ M₂ M₃) n).comp (e.toLinearEquiv : M₀ →ₗ[ℂ] M₁),
    isIntertwiningOperator_precomp Y.2 (fun u n x => e.map_act u n x)⟩
  invFun Y := ⟨fun n => ((Y : IntertwiningModes M₀ M₂ M₃) n).comp
      (e.symm.toLinearEquiv : M₁ →ₗ[ℂ] M₀),
    isIntertwiningOperator_precomp Y.2 (fun u n x => e.symm.map_act u n x)⟩
  map_add' Y Y' := Subtype.ext (by funext n; ext; simp)
  map_smul' c Y := Subtype.ext (by funext n; ext; simp)
  left_inv Y := Subtype.ext (by
    funext n; ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact congrArg (fun z => (Y : IntertwiningModes M₁ M₂ M₃) n z _)
      (e.toLinearEquiv.apply_symm_apply x))
  right_inv Y := Subtype.ext (by
    funext n; ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact congrArg (fun z => (Y : IntertwiningModes M₀ M₂ M₃) n z _)
      (e.toLinearEquiv.symm_apply_apply x))

/-- Fusion rules only depend on the first module up to isomorphism. -/
theorem fusionRule_congr_left {M₀ M₁ : Type u} [AddCommGroup M₀] [Module ℂ M₀]
    [AddCommGroup M₁] [Module ℂ M₁] {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
    (e : ModuleEquiv W A₀ A₁) : fusionRule A₀ A₂ A₃ = fusionRule A₁ A₂ A₃ :=
  (intertwiningEquivLeft (A₂ := A₂) (A₃ := A₃) e).finrank_eq.symm

end Hom

/-! ## §2  The vacuum mode of an intertwiner of type `(M₃ / V M₂)` -/

section Vac

variable {M₂ M₃ : Type u} [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
variable {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {Y : IntertwiningModes 𝒱 M₂ M₃}

theorem adjoint_mode (u : 𝒱) (n : ℤ) (v : 𝒱) :
    mode ((adjointModule W).YM u) n v = W.smul u n v := rfl

theorem adjoint_Lm1_vacuum : (adjointModule W).Lm1 W.vacuum = 0 := by
  change W.smul W.conformalVector 0 W.vacuum = 0
  exact W.toPreVertexAlgebra.smul_vacuum_zero _

/-- `𝒴(𝟙, z) = 𝒴(𝟙)₍₋₁₎`: every other mode of the vacuum vanishes. -/
theorem vac_mode_eq_zero (hY : IsIntertwiningOperator (adjointModule W) A₂ A₃ Y) {n : ℂ}
    (hn : n ≠ -1) : Y n W.vacuum = 0 := by
  have h := hY.L_neg_one W.vacuum (n + 1)
  rw [adjoint_Lm1_vacuum, map_zero, add_sub_cancel_right] at h
  have hne : -(n + 1) ≠ 0 := by
    intro h0; apply hn; linear_combination -h0
  exact (smul_eq_zero.mp h.symm).resolve_left hne

/-- `𝒴(𝟙)₍₋₁₎` is a module homomorphism `M₂ → M₃`. -/
theorem isHom_vacMode (hY : IsIntertwiningOperator (adjointModule W) A₂ A₃ Y) :
    Y (-1) W.vacuum ∈ homSpace A₂ A₃ := by
  intro u m x
  have h := hY.commutator u W.vacuum x m (-1)
  rw [LatFus.finsum_eq_zero_of_forall (fun i => ?_), sub_eq_zero] at h
  · exact h.symm
  · rcases lt_or_ge i 0 with hi | hi
    · rw [cbz_apply_neg m hi, zero_smul]
    · rw [adjoint_mode, W.toPreVertexAlgebra.smul_vacuum_nonneg u hi, map_zero,
        LinearMap.zero_apply, smul_zero]

/-- **An intertwiner of type `(M₃ / V M₂)` is determined by `𝒴(𝟙)₍₋₁₎`** (any `M₂, M₃`). -/
theorem eq_zero_of_vacMode (hY : IsIntertwiningOperator (adjointModule W) A₂ A₃ Y)
    (h0 : Y (-1) W.vacuum = 0) : Y = 0 := by
  have hvac : ∀ (n : ℂ) (x : M₂), Y n W.vacuum x = 0 := by
    intro n x
    by_cases hn : n = -1
    · rw [hn, h0, LinearMap.zero_apply]
    · rw [vac_mode_eq_zero hY hn, LinearMap.zero_apply]
  -- the left annihilator `K` is closed under all modes
  have hK : ∀ (w₁ : 𝒱), (∀ (n : ℂ) (x : M₂), Y n w₁ x = 0) →
      ∀ (u : 𝒱) (ℓ : ℤ) (n : ℂ) (x : M₂), Y n (W.smul u ℓ w₁) x = 0 := by
    intro w₁ hw u ℓ n x
    exact LatFus.assoc_vanish hY u w₁ x (fun p => hw p x) (fun i _ p => hw p _) ℓ n
  funext n
  ext w₁ x
  have := hK W.vacuum hvac w₁ (-1) n x
  rw [W.toPreVertexAlgebra.smul_vacuum_neg_one] at this
  simpa using this

variable (A₂ A₃)

/-- The **vacuum-mode map** `𝒴 ↦ 𝒴(𝟙)₍₋₁₎ : Int(V M₂ → M₃) → Hom_V(M₂, M₃)`, injective. -/
noncomputable def vacModeMap :
    intertwiningSpace (adjointModule W) A₂ A₃ →ₗ[ℂ] homSpace A₂ A₃ where
  toFun Y := ⟨(Y : IntertwiningModes 𝒱 M₂ M₃) (-1) W.vacuum, isHom_vacMode Y.2⟩
  map_add' Y Y' := Subtype.ext (by simp)
  map_smul' c Y := Subtype.ext (by simp)

variable {A₂ A₃}

theorem vacModeMap_injective : Function.Injective (vacModeMap A₂ A₃) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  apply Subtype.ext
  exact eq_zero_of_vacMode Y.2 (congrArg Subtype.val hY)

end Vac

/-! ## §3  The unit axiom -/

section Unit

variable {P₂ P₃ : LWModule W}

/-- Intertwiner spaces of type `(P₃ / V P₂)` are finite-dimensional. -/
theorem finiteDimensional_intertwiningSpace_adjoint (h₂ : P₂.IsIrreducibleLW)
    (h₃ : P₃.IsIrreducibleLW) :
    FiniteDimensional ℂ (intertwiningSpace (adjointModule W) P₂.isMod P₃.isMod) :=
  haveI := (finite_and_finrank_homSpace_le_one h₂ h₃).1
  Module.Finite.of_injective _ vacModeMap_injective

/-- `N^{P₃}_{V P₂} ≤ 1`. -/
theorem fusionRule_adjoint_le_one (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW) :
    fusionRule (adjointModule W) P₂.isMod P₃.isMod ≤ 1 := by
  haveI := (finite_and_finrank_homSpace_le_one h₂ h₃).1
  exact (LinearMap.finrank_le_finrank_of_injective vacModeMap_injective).trans
    (finite_and_finrank_homSpace_le_one h₂ h₃).2

/-- `N^{P}_{V P} = 1` for an irreducible lowest-weight module. -/
theorem fusionRule_adjoint_self (P : LWModule W) (hP : P.IsIrreducibleLW) :
    fusionRule (adjointModule W) P.isMod P.isMod = 1 := by
  haveI : Nontrivial P.carrier := hP.1
  haveI := finiteDimensional_intertwiningSpace_adjoint hP hP
  exact le_antisymm (fusionRule_adjoint_le_one hP hP) (one_le_fusionRule_adjoint P.isMod)

/-- A nonzero intertwiner of type `(P₃ / V P₂)` gives a module isomorphism `P₂ ≅ P₃`. -/
theorem nonempty_moduleEquiv_of_ne_zero (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW)
    (Y : intertwiningSpace (adjointModule W) P₂.isMod P₃.isMod) (hY : Y ≠ 0) :
    Nonempty (ModuleEquiv W P₂.isMod P₃.isMod) := by
  have hf := isHom_vacMode Y.2
  have hf0 : (Y : IntertwiningModes 𝒱 P₂.carrier P₃.carrier) (-1) W.vacuum ≠ 0 := fun h0 =>
    hY (Subtype.ext (eq_zero_of_vacMode Y.2 h0))
  let e := LinearEquiv.ofBijective _ (bijective_of_hom h₂ h₃ hf hf0)
  exact ⟨⟨e, fun u n x => hf u n x⟩⟩

/-- `N^{P₃}_{V P₂} = 0` when `P₂ ≇ P₃`. -/
theorem fusionRule_adjoint_eq_zero (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW)
    (hne : ¬ Nonempty (ModuleEquiv W P₂.isMod P₃.isMod)) :
    fusionRule (adjointModule W) P₂.isMod P₃.isMod = 0 := by
  have : Subsingleton (intertwiningSpace (adjointModule W) P₂.isMod P₃.isMod) := by
    refine ⟨fun a b => ?_⟩
    by_contra hab
    have : a - b ≠ 0 := sub_ne_zero.mpr hab
    exact hne (nonempty_moduleEquiv_of_ne_zero h₂ h₃ _ this)
  exact Module.finrank_zero_of_subsingleton

open Classical in
/-- **The unit axiom**: `N^{P₃}_{V P₂} = 1` if `P₂ ≅ P₃` and `0` otherwise. -/
theorem fusionRule_adjoint_eq (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW) :
    fusionRule (adjointModule W) P₂.isMod P₃.isMod
      = if Nonempty (ModuleEquiv W P₂.isMod P₃.isMod) then 1 else 0 := by
  split_ifs with h
  · haveI := finiteDimensional_intertwiningSpace_adjoint h₂ h₃
    obtain ⟨e⟩ := h
    refine le_antisymm (fusionRule_adjoint_le_one h₂ h₃) ?_
    -- `e ∘ Y_{P₂}` is a nonzero intertwiner of type `(P₃ / V P₂)`
    haveI : Nontrivial P₂.carrier := h₂.1
    have hhom : (e.toLinearEquiv : P₂.carrier →ₗ[ℂ] P₃.carrier) ∈ homSpace P₂.isMod P₃.isMod :=
      fun u n x => e.map_act u n x
    let Y' : intertwiningSpace (adjointModule W) P₂.isMod P₃.isMod :=
      ⟨fun n => (moduleModes P₂.isMod n).compr₂ (e.toLinearEquiv : P₂.carrier →ₗ[ℂ] P₃.carrier),
        isIntertwiningOperator_compHom (isIntertwiningOperator_moduleModes P₂.isMod) hhom⟩
    have hne : Nontrivial (intertwiningSpace (adjointModule W) P₂.isMod P₃.isMod) := by
      refine ⟨⟨Y', 0, fun h0 => ?_⟩⟩
      obtain ⟨x, hx⟩ := exists_ne (0 : P₂.carrier)
      have h1 := congrArg (fun Z : intertwiningSpace (adjointModule W) P₂.isMod P₃.isMod =>
        (Z : IntertwiningModes 𝒱 P₂.carrier P₃.carrier) ((-1 : ℤ) : ℂ) W.vacuum x) h0
      change e.toLinearEquiv (moduleModes P₂.isMod ((-1 : ℤ) : ℂ) W.vacuum x) = 0 at h1
      rw [moduleModes_apply_intCast, ← WeakModule.act_def, WeakModule.act_vacuum, if_pos rfl,
        LinearEquiv.map_eq_zero_iff] at h1
      exact hx h1
    exact (Module.finrank_pos_iff_of_free ℂ _).mpr hne
  · exact fusionRule_adjoint_eq_zero h₂ h₃ h

end Unit

end VOA.Huang.FusionUnit
