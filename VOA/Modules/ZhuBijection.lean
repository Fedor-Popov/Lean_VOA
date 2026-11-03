/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuModule
import VOA.Modules.Rationality

/-!
# Theorem 5.3.4 — the bijection `Φ(𝒱) ↔ Irr A(𝒱)`, the forward direction

The Zhu correspondence `M ↦ M_h` as a genuine, well-defined map on iso-classes (the *easy* half
of Theorem 5.3.4, Gannon §5.3.2), built on `ZhuModule.actA`:

* `ModuleEquiv.maps_weight` / `ModuleEquiv.intertwine_oMod` — a `𝒱`-module isomorphism preserves
  every weight space and intertwines the module zero mode `o(u)`;
* `ModuleEquiv.toAModEquiv` — hence it restricts to a genuine `A(𝒱)`-module isomorphism of the
  lowest-weight spaces (functoriality / well-definedness of `M ↦ M_h`);
* `AMod`/`LWModule` (bundled `A(𝒱)`-modules and lowest-weight `𝒱`-modules with their iso-class
  setoids) and **`forwardMap : LWModuleIsoClass W → AModIsoClass W`** — the forward map as a
  `Quotient.lift`.

## Status
Axiom-clean for the forward map and its functoriality/well-definedness (built on `actA`).

The **hard direction** `U ↦ M(U)` is **not** obtained here.  `Modules.ZhuInduced` packages it as
`InducedAssignment`, but that structure is uninhabited for every `𝒱`
(`not_nonempty_inducedAssignment`, `Modules/ZhuVermaAnArchZhu534.lean`), so the round-trip
theorems built on it are vacuous.  The library's bijection on irreducibles is `zhuBijective`
(`Modules/ZhuVermaAnArchLUBijection.lean`, conditional on `Pr : BottomProjection …`), and it proves
only the uniqueness half: its codomain is image-defined, so existence is not proved.
No carrier is asserted here.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu [574]; Frenkel–Zhu; Dong–Li–Mason.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open Classical
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Functoriality of the easy direction `M ↦ M_h`

A `𝒱`-module isomorphism `e : N ≃ₘ N'` preserves the conformal grading (it commutes with
`L₀ = ω₍₁₎`) and intertwines every mode, in particular the module zero mode `o(u)`. Hence it
restricts to an isomorphism of the lowest-weight spaces *as `A(𝒱)`-modules*. This is the
well-definedness of the forward map `[M] ↦ [M_h]` on iso-classes. -/

section Functoriality

variable {M N : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
variable {W : VertexOperatorAlgebra 𝒱} {A : OrdVModule W M} {B : OrdVModule W N}

/-- A module isomorphism intertwines the mode operator viewed as an `End`: for the bundled
`mode (YM u) n`, `e (u₍ₙ₎ x) = u₍ₙ₎ (e x)`. (Restatement of `ModuleEquiv.map_act`.) -/
theorem ModuleEquiv.intertwine_mode (e : ModuleEquiv W A B) (u : 𝒱) (n : ℤ) (x : M) :
    e.toLinearEquiv (mode (A.YM u) n x) = mode (B.YM u) n (e.toLinearEquiv x) := by
  have := e.map_act u n x
  simpa only [WeakModule.act_def] using this

/-- **A module isomorphism preserves weight spaces.** If `x ∈ M_α` then `e x ∈ N'_α`: `e`
commutes with `L₀ = ω₍₁₎`, so it carries `α`-eigenvectors to `α`-eigenvectors. -/
theorem ModuleEquiv.maps_weight (e : ModuleEquiv W A B) {α : ℂ} {x : M}
    (hx : x ∈ A.weight α) : e.toLinearEquiv x ∈ B.weight α := by
  apply eigenvector_mem_weight B
  -- `L₀ (e x) = e (L₀ x) = e (α • x) = α • e x`.
  rw [← e.intertwine_mode W.conformalVector 1 x, A.L0_weight α x hx, map_smul]

/-- **A module isomorphism reflects nontriviality of weight spaces.** If `A.weight α ≠ ⊥`
then `B.weight α ≠ ⊥` (the iso carries a nonzero `α`-vector to a nonzero `α`-vector). -/
theorem ModuleEquiv.weight_ne_bot (e : ModuleEquiv W A B) {α : ℂ}
    (hα : A.weight α ≠ ⊥) : B.weight α ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hα ⊢
  obtain ⟨x, hx, hx0⟩ := hα
  refine ⟨e.toLinearEquiv x, e.maps_weight hx, ?_⟩
  intro h0
  exact hx0 (by simpa using congrArg e.toLinearEquiv.symm h0)

/-- **`IsLowestWeight` transports across a module isomorphism.** If `A` has lowest weight `h`
and `e : A ≃ₘ B`, then `B` also has lowest weight `h`. (Same nonzero weights, by
`weight_ne_bot` applied to `e.symm`.) -/
theorem ModuleEquiv.isLowestWeight_transport (e : ModuleEquiv W A B) {h : ℂ}
    (hA : IsLowestWeight A h) : IsLowestWeight B h := by
  intro α hα
  exact hA α (e.symm.weight_ne_bot hα)

/-- **The realized lowest weight is unique.** If `h₁` and `h₂` are both lowest weights of the
*same* module `A`, and the bottom layer `M_{h₁}` is nonzero, then `h₁ = h₂`. (`h₁ = h₂ + n` and
`h₂ = h₁ + m` force `n = m = 0`.) Stated for a `B`-realization via an iso below. -/
theorem isLowestWeight_unique (A : OrdVModule W M) {h₁ h₂ : ℂ}
    (hne : A.weight h₁ ≠ ⊥) (h1 : IsLowestWeight A h₁) (h2 : IsLowestWeight A h₂)
    (hne2 : A.weight h₂ ≠ ⊥) : h₁ = h₂ := by
  obtain ⟨n, hn⟩ := h2 h₁ hne   -- h₁ = h₂ + n
  obtain ⟨m, hm⟩ := h1 h₂ hne2  -- h₂ = h₁ + m
  have hsum : (n : ℂ) + (m : ℂ) = 0 := by linear_combination -hn - hm
  have hnm : (n : ℤ) + (m : ℤ) = 0 := by exact_mod_cast hsum
  have hn0 : n = 0 := by omega
  rw [hn, hn0]; simp

/-- **A module isomorphism intertwines the module zero mode** `o(u)` on homogeneous states:
for `u ∈ 𝒱ₖ`, `e (o(u) x) = o(u) (e x)`. (`o(u) = u₍ₖ₋₁₎` there, and `e` intertwines modes.) -/
theorem ModuleEquiv.intertwine_oMod_homog (e : ModuleEquiv W A B) {k : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading k) (x : M) :
    e.toLinearEquiv (oMod A u x) = oMod B u (e.toLinearEquiv x) := by
  rw [oMod_homogeneous A hu, oMod_homogeneous B hu, e.intertwine_mode]

/-- **A module isomorphism intertwines the module zero mode** `o(u)` for *all* states `u`
(extend by linearity over the grade decomposition). -/
theorem ModuleEquiv.intertwine_oMod (e : ModuleEquiv W A B) (u : 𝒱) (x : M) :
    e.toLinearEquiv (oMod A u x) = oMod B u (e.toLinearEquiv x) := by
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => e.toLinearEquiv (oMod A u x) = oMod B u (e.toLinearEquiv x)) hutop
    ?_ ?_ ?_
  · intro i y hy; exact e.intertwine_oMod_homog hy x
  · simp
  · intro y z hy hz
    rw [map_add, LinearMap.add_apply, map_add, hy, hz, map_add, LinearMap.add_apply]

end Functoriality

/-! ## The bundled `A(𝒱)`-module produced by `M ↦ M_h`, and its functoriality

We package the project's descended action `actA : A(𝒱) →ₗ End ℂ M_h` (Theorem 5.3.4, easy
direction — `Modules.ZhuModule.actA`, unital `actA_one` and multiplicative `actA_mk_mul` on
*all* representable products) as a bundled `AMod`, and show the easy direction is functorial:
a `𝒱`-module isomorphism with a common lowest weight `h` induces an `AMod`-isomorphism. -/

section AMod

variable (W : VertexOperatorAlgebra 𝒱)

/-- A **bundled (left) `A(𝒱)`-module**, modeled on exactly the data the descended action
`actA` produces: a `ℂ`-space with a ℂ-linear `A(𝒱) → End` that is *unital* (`[𝟙]` acts as
`1`) and *multiplicative on every representable Zhu product* (`ρ[u*v] = ρ[u]·ρ[v]`). Once
Zhu's ideal theorem gives `A(𝒱)` its ring structure this is a genuine `A(𝒱)`-module. -/
structure AMod where
  /-- The underlying carrier. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  /-- The ℂ-linear action of `A(𝒱)`. -/
  ρ : A W →ₗ[ℂ] End ℂ carrier
  /-- The unit `[𝟙]` acts as the identity. -/
  ρ_one : ρ (one W) = 1
  /-- Multiplicativity on representable Zhu products (holds for all `u, v` via `actA_mk_mul`). -/
  ρ_mul : ∀ u v : 𝒱, ρ (mk W (zhuMul W u v)) = ρ (mk W u) * ρ (mk W v)

attribute [instance] AMod.addCommGroup AMod.module

/-- **An isomorphism of bundled `A(𝒱)`-modules**: a ℂ-linear equivalence intertwining the
`A(𝒱)`-action. -/
structure AModEquiv (P Q : AMod W) where
  /-- The underlying linear equivalence. -/
  toLinearEquiv : P.carrier ≃ₗ[ℂ] Q.carrier
  /-- Intertwining of the `A(𝒱)`-action. -/
  map_ρ : ∀ (a : A W) (x : P.carrier), toLinearEquiv (P.ρ a x) = Q.ρ a (toLinearEquiv x)

namespace AModEquiv

/-- The identity `A(𝒱)`-module isomorphism. -/
def refl (P : AMod W) : AModEquiv W P P where
  toLinearEquiv := LinearEquiv.refl ℂ P.carrier
  map_ρ _ _ := rfl

/-- The inverse `A(𝒱)`-module isomorphism. -/
def symm {P Q : AMod W} (e : AModEquiv W P Q) : AModEquiv W Q P where
  toLinearEquiv := e.toLinearEquiv.symm
  map_ρ a y := by
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, e.map_ρ, LinearEquiv.apply_symm_apply]

/-- Composition of `A(𝒱)`-module isomorphisms. -/
def trans {P Q R : AMod W} (e : AModEquiv W P Q) (f : AModEquiv W Q R) :
    AModEquiv W P R where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  map_ρ a x := by simp only [LinearEquiv.trans_apply, e.map_ρ, f.map_ρ]

end AModEquiv

/-- `A(𝒱)`-module isomorphism is an equivalence relation (a genuine `Setoid`). -/
def AMod.setoid : Setoid (AMod W) where
  r P Q := Nonempty (AModEquiv W P Q)
  iseqv :=
    { refl := fun P => ⟨AModEquiv.refl W P⟩
      symm := fun ⟨e⟩ => ⟨AModEquiv.symm W e⟩
      trans := fun ⟨e⟩ ⟨f⟩ => ⟨AModEquiv.trans W e f⟩ }

/-- Iso-classes of bundled `A(𝒱)`-modules — the `A(𝒱)`-side index set (a model for the
classes of irreducible `A(𝒱)`-modules; the target of the forward map `[M] ↦ [M_h]`). -/
def AModIsoClass : Type (u + 1) := Quotient (AMod.setoid W)

end AMod

/-! ## The easy direction packaged into `AMod`, functorially -/

section EasyAMod

variable {M N : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
variable {W : VertexOperatorAlgebra 𝒱} {P : OrdVModule W M} {Q : OrdVModule W N}

/-- **The easy direction `M ↦ M_h` as a bundled `A(𝒱)`-module.** A `𝒱`-module `P` with
lowest weight `h` yields the `A(𝒱)`-module on its lowest-weight space `M_h = P.weight h`,
with action the project's descended `actA`. Its laws are `actA_one`/`actA_mk_mul`. -/
noncomputable def lowestAMod {P : OrdVModule W M} {h : ℂ} (hcw : IsLowestWeight P h) : AMod W where
  carrier := P.weight h
  ρ := actA P hcw
  ρ_one := actA_one P hcw
  ρ_mul u v := actA_mk_mul P hcw u v

/-- The restricted linear equivalence `P.weight h ≃ₗ Q.weight h` induced by a `𝒱`-module
isomorphism `e` (using that `e` preserves weight spaces, both ways). -/
noncomputable def ModuleEquiv.restrictWeight (e : ModuleEquiv W P Q) (h : ℂ) :
    (P.weight h) ≃ₗ[ℂ] (Q.weight h) where
  toFun x := ⟨e.toLinearEquiv (x : M), e.maps_weight x.2⟩
  invFun y := ⟨e.toLinearEquiv.symm (y : N), e.symm.maps_weight y.2⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

@[simp] theorem ModuleEquiv.restrictWeight_coe (e : ModuleEquiv W P Q) (h : ℂ)
    (x : P.weight h) : ((e.restrictWeight h x : Q.weight h) : N) = e.toLinearEquiv (x : M) := rfl

/-- **Functoriality of the easy direction.** A `𝒱`-module isomorphism `e : P ≃ₘ Q` with a
common lowest weight `h` induces an `A(𝒱)`-module isomorphism of the lowest-weight spaces:
`(M_h, actA) ≅ (N_h, actA)`. The intertwining is exactly `e (o(u) x) = o(u) (e x)`
(`intertwine_oMod`), descended through `A(𝒱)`. This is the well-definedness of `[M] ↦ [M_h]`. -/
noncomputable def ModuleEquiv.toAModEquiv (e : ModuleEquiv W P Q)
    {h : ℂ} (hP : IsLowestWeight P h) (hQ : IsLowestWeight Q h) :
    AModEquiv W (lowestAMod hP) (lowestAMod hQ) where
  toLinearEquiv := e.restrictWeight h
  map_ρ a x := by
    -- `x` lives in `(lowestAMod hP).carrier = P.weight h`; name the underlying weight vector.
    let x' : P.weight h := x
    -- Reduce to representatives `a = [u]` of `A(𝒱) = 𝒱/O(𝒱)`.
    refine Submodule.Quotient.induction_on (O W) a (fun u => ?_)
    -- Both sides land in `Q.weight h`; compare their `N`-coercions.
    apply Subtype.ext
    -- Unfold `lowestAMod.ρ = actA`, then compute both coercions to `N` via the bridge
    -- `actA_mk_apply_coe` (`[u]·y = o(u) y`) and the intertwining `e (o(u) z) = o(u) (e z)`.
    show e.toLinearEquiv (((actA P hP (VOA.mk W u) x' : P.weight h)) : M)
        = ((actA Q hQ (VOA.mk W u) (e.restrictWeight h x') : Q.weight h) : N)
    rw [actA_mk_apply_coe P hP u x', actA_mk_apply_coe Q hQ u (e.restrictWeight h x'),
      ModuleEquiv.restrictWeight_coe]
    exact e.intertwine_oMod u (x' : M)

end EasyAMod

/-! ## The forward map of the bijection `[M] ↦ [M_h]`, on iso-classes

We bundle a `𝒱`-module together with its *realized* lowest weight `h` (`M_h ≠ ⊥`), form the
`Setoid` of such bundles under `𝒱`-module isomorphism, and define the forward map of
Theorem 5.3.4 — `[M] ↦ [M_h]` — as a genuine function on iso-classes into `AModIsoClass`,
*well-defined* by the functoriality `ModuleEquiv.toAModEquiv` together with the uniqueness of
the realized lowest weight (`isLowestWeight_unique`). This is the easy half of the bijection
realized at the level of iso-classes; only the hard inverse `U ↦ M(U)` remains. -/

section ForwardMap

variable (W : VertexOperatorAlgebra 𝒱)

/-- A **bundled lowest-weight `𝒱`-module**: a `𝒱`-module with a *realized* lowest weight `h`
(the bottom layer `M_h` is nonzero, so `h` is genuinely the minimal weight). -/
structure LWModule where
  /-- The carrier. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  /-- The graded `𝒱`-module structure. -/
  isMod : OrdVModule W carrier
  /-- The realized lowest weight. -/
  h : ℂ
  /-- `h` is a lowest weight. -/
  isLow : IsLowestWeight isMod h
  /-- It is *realized*: the bottom layer is nonzero. -/
  realized : isMod.weight h ≠ ⊥

attribute [instance] LWModule.addCommGroup LWModule.module

/-- Isomorphism of bundled lowest-weight modules (a `𝒱`-module isomorphism of the carriers). -/
def LWModule.Iso (P Q : LWModule W) : Prop :=
  Nonempty (ModuleEquiv W P.isMod Q.isMod)

/-- `LWModule`-isomorphism is an equivalence relation. -/
def LWModule.setoid : Setoid (LWModule W) where
  r := LWModule.Iso W
  iseqv :=
    { refl := fun P => ⟨ModuleEquiv.refl P.isMod⟩
      symm := fun ⟨e⟩ => ⟨e.symm⟩
      trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

/-- Iso-classes of bundled lowest-weight `𝒱`-modules. -/
def LWModuleIsoClass : Type (u + 1) := Quotient (LWModule.setoid W)

/-- **Isomorphic lowest-weight modules realize the same lowest weight.** -/
theorem LWModule.h_eq_of_iso {P Q : LWModule W} (e : ModuleEquiv W P.isMod Q.isMod) :
    P.h = Q.h := by
  -- `Q.h` and (the transported) `P.h` are both lowest weights of `Q`, both realized.
  have hPh_on_Q : IsLowestWeight Q.isMod P.h := e.isLowestWeight_transport P.isLow
  have hQh_real : Q.isMod.weight Q.h ≠ ⊥ := Q.realized
  have hPh_real : Q.isMod.weight P.h ≠ ⊥ := e.weight_ne_bot P.realized
  exact isLowestWeight_unique Q.isMod hPh_real hPh_on_Q Q.isLow hQh_real

/-- `lowestAMod` depends on its weight only up to equality of the weight value (the proof of
`IsLowestWeight` is irrelevant): if `h₁ = h₂` then `lowestAMod hcw₁ = lowestAMod hcw₂`. -/
theorem lowestAMod_congr {M : Type u} [AddCommGroup M] [Module ℂ M] {P : OrdVModule W M}
    {h₁ h₂ : ℂ} (hh : h₁ = h₂) (hcw₁ : IsLowestWeight P h₁) (hcw₂ : IsLowestWeight P h₂) :
    lowestAMod hcw₁ = lowestAMod hcw₂ := by
  subst hh
  rw [Subsingleton.elim hcw₁ hcw₂]

/-- The bundled `A(𝒱)`-module `M_h` of a lowest-weight module. -/
noncomputable def LWModule.toAMod (P : LWModule W) : AMod W :=
  lowestAMod P.isLow

/-- **The easy-direction iso for isomorphic lowest-weight modules.** Given `e : P ≃ₘ Q`, the
lowest-weight `A(𝒱)`-modules `P.toAMod` and `Q.toAMod` are isomorphic. Combines the lowest-
weight uniqueness (`h_eq_of_iso`) with the functoriality `ModuleEquiv.toAModEquiv`. -/
noncomputable def LWModule.isoToAModEquiv {P Q : LWModule W}
    (e : ModuleEquiv W P.isMod Q.isMod) : AModEquiv W P.toAMod Q.toAMod := by
  -- The realized lowest weights agree.
  have hh : P.h = Q.h := LWModule.h_eq_of_iso W e
  -- Transport `Q`'s lowest-weight proof to `P.h`; the resulting `lowestAMod` is `Q.toAMod`
  -- (proof-irrelevant equality of the `IsLowestWeight` arguments, both at `P.h = Q.h`).
  have hQ' : IsLowestWeight Q.isMod P.h := e.isLowestWeight_transport P.isLow
  have hAModEq : lowestAMod hQ' = Q.toAMod :=
    lowestAMod_congr W hh hQ' Q.isLow
  -- `toAModEquiv` at the common weight `P.h`, then rewrite the target via `hAModEq`.
  exact hAModEq ▸ e.toAModEquiv P.isLow hQ'

/-- **The forward map `[M] ↦ [M_h]`** of Theorem 5.3.4, as a genuine function on iso-classes
into `AModIsoClass`. Well-defined: an isomorphism `e : P ≃ₘ Q` forces `P.h = Q.h`
(`h_eq_of_iso`) and then `toAModEquiv` gives `M_{P.h} ≅ M_{Q.h}` as `A(𝒱)`-modules
(`LWModule.isoToAModEquiv`). -/
noncomputable def forwardMap : LWModuleIsoClass W → AModIsoClass W :=
  Quotient.lift (fun P => (Quotient.mk (AMod.setoid W) P.toAMod : AModIsoClass W))
    (fun _ _ ⟨e⟩ => Quotient.sound ⟨LWModule.isoToAModEquiv W e⟩)

/-- On a representative, the forward map is `[lowestAMod]`. -/
@[simp] theorem forwardMap_mk (P : LWModule W) :
    forwardMap W (Quotient.mk (LWModule.setoid W) P)
      = Quotient.mk (AMod.setoid W) P.toAMod := rfl

end ForwardMap

end VOA
