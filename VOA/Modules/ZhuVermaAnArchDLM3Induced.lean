/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3Deg
import VOA.Modules.ZhuVermaAnArchMUModuleDataBuild

/-!
# DLM3 §4 (4.1)–(4.2) — the induced module `M_n(U) = Ind_{P_n}^{V̂} U` and its `V̂`-action

Dong–Li–Mason, *Vertex operator algebras and associative algebras*, J. Algebra **206** (1998)
67–96 (arXiv `q-alg/9612010v2`), Theorem 4.1, is the only known proof of Dong–Jiang Proposition 4.6
(`A_n(𝒱) = A_{n,n}(𝒱)`), which in turn gates the whole Zhu bijection construction.  Its construction is *not*
built from `A_{n,m}` bimodules — it is pure affinization plus Lie induction:

> "Fix an `A_n(V)`-module `U` … By Proposition 3.1 we can lift `U` to a module for the Lie algebra
> `V̂(0)`, and then to one for `P_n = ⨁_{p>n} V̂(−p) ⊕ V̂(0)` by letting `V̂(−p)` act trivially.
> Define `M_n(U) = Ind_{P_n}^{V̂}(U) = U(V̂) ⊗_{U(P_n)} U`."  (DLM3 (4.1))
>
> "We define for `v ∈ V`, `Y_{M_n(U)}(v,z) = ∑_m v(m) z^{−m−1}`."  (DLM3 (4.2))

**This file is exactly (4.1)–(4.2).**  It builds the carrier, its `V̂`-representation, and the two
*module-field* properties that DLM3 uses without comment throughout §4:

* `VHat.DLM3.IndMod P` — the carrier `U(V̂) ⊗_{U(P_n)} U`.  Mathlib has no tensor product over a
  noncommutative ring, so — following the repo's own `DJPiece`/`djBalancing` pattern
  (`ZhuVermaAnArchDJCarrier`) — it is realized as the `ℂ`-tensor product `U(V̂) ⊗_ℂ U` modulo the
  `U(P_n)`-balancing relations `y·g ⊗ u − y ⊗ g·u`, imposed for the **Lie generators** `g ∈ P_n`.
  (`U(P_n)` itself is never constructed here, and the classical telescoping argument identifying
  this span with the full `U(P_n)`-balancing is *not* formalized — nothing below uses it.)
* `VHat.DLM3.indRho P : VHatRep W (IndMod P)` — the `V̂`-representation of (4.2), namely **left
  multiplication by `U(V̂)`**.  Its Lie-morphism property is free (it is `uι` followed by the left
  regular representation), so the repo's `assembleModeData` obligations `hderiv`/`hbracket` do not
  even arise here: `(L₋₁a)(m) = −m·a(m−1)` is already a relation *in* `V̂` (`gen_Lneg1`) and the
  Borcherds commutator is `uι`'s `map_lie` (`umode_commutator`).
* `VHat.DLM3.ind_actModeTruncated` — **`ActModeTruncated (indRho P)`**, the lower-truncation
  (module-field) property.  This is the first genuinely non-formal theorem of the file: the deep
  part `⨁_{p>n} V̂(−p)` annihilates `U` (DLM3 (4.1)), and `gen_eventually_deep` plus the Borcherds
  commutator `actMode_bracket` propagate that up the whole of `U(V̂)` by an induction on words.
* `VHat.DLM3.ind_vacuumCreation` — **`VacuumCreation (indRho P)`**, i.e. `𝟙₍ₘ₎ = δ_{m,−1}·id`.
  This uses all three vacuum facts of `ZhuVermaAnArchDLM3Deg`: `𝟙(m) = 0` for `m ≠ −1`, `𝟙(−1)`
  is central in `V̂`, and `𝟙(−1) ∈ P_n` acts on `U` as the identity of `A_n(𝒱)`.

The workhorse for both is `VHat.uenv_induction`, the word-length induction principle on `U(V̂)`
obtained from Mathlib's universal property (`UniversalEnvelopingAlgebra.lift`/`hom_ext`) exactly as
`TensorAlgebra.induction` is obtained from `TensorAlgebra.lift`.

**What is NOT attempted here** (per the build plan): the module Jacobi 5.3.1b, equivalently the
residual `ModuleIterate` (`ZhuVermaAnArchMUjacobi`), equivalently DLM3's defect quotient (4.3)–(4.4)
`M̄_n(U) = M_n(U)/U(V̂)W`.  It is *false* on `M_n(U)` itself — that is precisely why DLM3 quotient
by the associativity defect — so no claim about it is made.

Everything here is `sorry`-free, `pbw`-free and `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 (`q-alg/9612010v2`) §3 (3.1)–(3.3), §4 (4.1)–(4.2), Thm 4.1; H. Li `hep-th/9406211` §2;
`ZhuVermaAnArchDLM3Deg` (`Pn`, `deepPart`, `gen_eventually_deep`, the vacuum package),
`ZhuVermaAnArchMUVhat` (`UEnv`, `uι`, `VHatRep`, `actMode`, `actMode_bracket`),
`ZhuVermaAnArchMUjacobi` (`ActModeTruncated`), `ZhuVermaAnArchMUModuleDataBuild`
(`VacuumCreation`), `ZhuVermaAnArchDJCarrier` (the balancing-quotient pattern).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## Word induction on `U(V̂)`

Mathlib's `UniversalEnvelopingAlgebra` API is thin (`ι`, `lift`, `hom_ext`).  The following two
results extract from it the only structural facts we need: a subalgebra containing the image of
`uι` is everything, and hence the induction principle "`algebraMap`, `uι`-generators, `+`, `*`". -/

/-- A subalgebra of `U(V̂)` containing all the loop modes `uι x` is the whole of `U(V̂)`.  Proof:
the corestriction `V̂ →ₗ⁅ℂ⁆ s` lifts to `U(V̂) →ₐ[ℂ] s` whose composite with the inclusion
agrees with the identity on the generators, hence *is* the identity (`hom_ext`). -/
theorem uenv_subalgebra_eq_top {W : VertexOperatorAlgebra 𝒱} (s : Subalgebra ℂ (UEnv W))
    (h : ∀ x : VHatCarrier W, uι W x ∈ s) : s = ⊤ := by
  classical
  set of : VHatCarrier W →ₗ⁅ℂ⁆ s :=
    { toFun := fun x => ⟨uι W x, h x⟩
      map_add' := fun x y => by
        refine Subtype.ext ?_
        change uι W (x + y) = uι W x + uι W y
        rw [map_add]
      map_smul' := fun c x => by
        refine Subtype.ext ?_
        change uι W (c • x) = c • uι W x
        rw [map_smul]
      map_lie' := fun {x y} => by
        refine Subtype.ext ?_
        change uι W ⁅x, y⁆
          = ((⁅(⟨uι W x, h x⟩ : s), (⟨uι W y, h y⟩ : s)⁆ : s) : UEnv W)
        rw [Ring.lie_def]
        change uι W ⁅x, y⁆ = uι W x * uι W y - uι W y * uι W x
        rw [(uι W).map_lie x y, Ring.lie_def] } with hof
  have key : (Subalgebra.val s).comp (UniversalEnvelopingAlgebra.lift ℂ of)
      = AlgHom.id ℂ (UEnv W) := by
    refine UniversalEnvelopingAlgebra.hom_ext (R := ℂ) (LieHom.ext fun x => ?_)
    change (Subalgebra.val s) (UniversalEnvelopingAlgebra.lift ℂ of (uι W x)) = uι W x
    rw [show uι W x = UniversalEnvelopingAlgebra.ι ℂ x from rfl,
      UniversalEnvelopingAlgebra.lift_ι_apply ℂ of x]
    rfl
  refine eq_top_iff.mpr fun a _ => ?_
  have ha : a = (Subalgebra.val s) (UniversalEnvelopingAlgebra.lift ℂ of a) := by
    conv_lhs => rw [show a = AlgHom.id ℂ (UEnv W) a from rfl]
    rw [← key]
    rfl
  rw [ha]
  exact (UniversalEnvelopingAlgebra.lift ℂ of a).2

/-- **Word induction on `U(V̂)`.**  A predicate holding on the scalars and the loop modes `uι x`,
and stable under sums and products, holds on all of `U(V̂)`.  (Companion of
`TensorAlgebra.induction`; the engine behind every "spanned by monomials in `a(m)`" argument.) -/
theorem uenv_induction {W : VertexOperatorAlgebra 𝒱} {C : UEnv W → Prop}
    (h_alg : ∀ c : ℂ, C (algebraMap ℂ (UEnv W) c))
    (h_gen : ∀ x : VHatCarrier W, C (uι W x))
    (h_mul : ∀ a b : UEnv W, C a → C b → C (a * b))
    (h_add : ∀ a b : UEnv W, C a → C b → C (a + b)) (a : UEnv W) : C a := by
  classical
  set s : Subalgebra ℂ (UEnv W) :=
    { carrier := {a | C a}
      mul_mem' := @h_mul
      add_mem' := @h_add
      algebraMap_mem' := h_alg } with hs
  have htop : s = ⊤ := uenv_subalgebra_eq_top s h_gen
  have hmem : a ∈ s := by rw [htop]; trivial
  exact hmem

namespace DLM3

/-! ## The `P_n`-module datum (DLM3 (4.1), first half) -/

/-- **DLM3 (4.1), the input datum.**  An `A_n(𝒱)`-module `U`, *pulled back along DLM3 Proposition
3.1* (`V̂(0) ↠ A_n(𝒱)`) and extended to the parabolic `P_n` by letting the deep part act trivially,
is precisely a Lie-algebra representation of `P_n` on `U` with the two DLM3 normalizations:

* `deep_zero` — "… and then to one for `P_n` … by letting `V̂(−p)` act trivially" (DLM3 (4.1));
* `vacuum_one` — the vacuum loop mode `𝟙(−1) ∈ V̂(0)` maps to the identity of `A_n(𝒱)` under
  Proposition 3.1, hence acts on `U` as `id`.

Carrying the datum in this form keeps the construction *faithful* and independent of the (not yet
built) Proposition 3.1 surjection `V̂(0) ↠ A_n(𝒱)`: any genuine `A_n(𝒱)`-module produces one. -/
structure ParabolicRep (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (U : Type u)
    [AddCommGroup U] [Module ℂ U] where
  /-- The `P_n`-action on `U`. -/
  act : Pn W n →ₗ⁅ℂ⁆ End ℂ U
  /-- The deep part `⨁_{p>n} V̂(−p)` acts trivially (DLM3 (4.1)). -/
  deep_zero : ∀ g : Pn W n, (g : VHatCarrier W) ∈ deepPart W n → act g = 0
  /-- The vacuum loop mode `𝟙(−1)` acts as the identity (the unit of `A_n(𝒱)`). -/
  vacuum_one : act ⟨gen W W.vacuum (-1), vacuumGen_mem_parabolic W n⟩ = 1

variable {W : VertexOperatorAlgebra 𝒱} {n : ℕ} {U : Type u} [AddCommGroup U] [Module ℂ U]

/-! ## The carrier `M_n(U) = U(V̂) ⊗_{U(P_n)} U` (DLM3 (4.1), second half) -/

/-- The `ℂ`-linear cover `U(V̂) ⊗_ℂ U` of DLM3's induced module. -/
abbrev IndCover (W : VertexOperatorAlgebra 𝒱) (U : Type u) [AddCommGroup U] [Module ℂ U] :
    Type u := UEnv W ⊗[ℂ] U

/-- Left multiplication of `U(V̂)` on the cover `U(V̂) ⊗_ℂ U`. -/
noncomputable def coverAct (W : VertexOperatorAlgebra 𝒱) (U : Type u) [AddCommGroup U]
    [Module ℂ U] (x : UEnv W) : End ℂ (IndCover W U) :=
  LinearMap.rTensor U (LinearMap.mulLeft ℂ x)

@[simp] theorem coverAct_tmul (x y : UEnv W) (u : U) :
    coverAct W U x (y ⊗ₜ[ℂ] u) = (x * y) ⊗ₜ[ℂ] u := rfl

/-- **The `U(P_n)`-balancing relations** `y·g ⊗ u − y ⊗ g·u` (`g ∈ P_n`, `y ∈ U(V̂)`) whose span is
divided out to form `U(V̂) ⊗_{U(P_n)} U` (DLM3 (4.1)).  Cf. `djBalancingSet`. -/
def balancingSet (P : ParabolicRep W n U) : Set (IndCover W U) :=
  {t | ∃ (y : UEnv W) (g : Pn W n) (u : U),
    t = (y * uι W (g : VHatCarrier W)) ⊗ₜ[ℂ] u - y ⊗ₜ[ℂ] (P.act g u)}

/-- The balancing submodule (the span of `balancingSet`). -/
noncomputable def balancing (P : ParabolicRep W n U) : Submodule ℂ (IndCover W U) :=
  Submodule.span ℂ (balancingSet P)

/-- **DLM3 (4.1): `M_n(U) = Ind_{P_n}^{V̂}(U) = U(V̂) ⊗_{U(P_n)} U`.** -/
abbrev IndMod (P : ParabolicRep W n U) : Type u := IndCover W U ⧸ balancing P

/-- The quotient map `U(V̂) ⊗_ℂ U ↠ M_n(U)`. -/
noncomputable def indMk (P : ParabolicRep W n U) : IndCover W U →ₗ[ℂ] IndMod P :=
  (balancing P).mkQ

/-- `y ↦ [y ⊗ u]`, as a `ℂ`-linear map `U(V̂) → M_n(U)`; the workhorse of every computation
below (it turns tensor bookkeeping into `map_add`/`map_smul`). -/
noncomputable def indTmul (P : ParabolicRep W n U) (u : U) : UEnv W →ₗ[ℂ] IndMod P :=
  (indMk P).comp ((TensorProduct.mk ℂ (UEnv W) U).flip u)

@[simp] theorem indTmul_apply (P : ParabolicRep W n U) (u : U) (y : UEnv W) :
    indTmul P u y = indMk P (y ⊗ₜ[ℂ] u) := rfl

/-- **The defining relation of `M_n(U)`**: `y·g ⊗ u = y ⊗ g·u` for `g ∈ P_n`. -/
theorem indMk_balance (P : ParabolicRep W n U) (y : UEnv W) (g : Pn W n) (u : U) :
    indMk P ((y * uι W (g : VHatCarrier W)) ⊗ₜ[ℂ] u) = indMk P (y ⊗ₜ[ℂ] (P.act g u)) := by
  rw [← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨y, g, u, rfl⟩)

/-- Extensionality on `M_n(U)`: two linear maps agree as soon as they agree on the images of the
pure tensors `y ⊗ u`. -/
theorem indMod_ext {P : ParabolicRep W n U} {N : Type u} [AddCommGroup N] [Module ℂ N]
    {f g : IndMod P →ₗ[ℂ] N}
    (h : ∀ (y : UEnv W) (u : U), f (indMk P (y ⊗ₜ[ℂ] u)) = g (indMk P (y ⊗ₜ[ℂ] u))) : f = g := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨t, rfl⟩ := (balancing P).mkQ_surjective z
  change f (indMk P t) = g (indMk P t)
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul y u => exact h y u
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]

/-! ## The `V̂`-action (DLM3 (4.2)) -/

/-- The balancing submodule is stable under left multiplication (its generating set is). -/
theorem balancing_stable (P : ParabolicRep W n U) (x : UEnv W) :
    ∀ t ∈ balancing P, coverAct W U x t ∈ balancing P := by
  intro t ht
  refine Submodule.span_induction
    (p := fun t _ => coverAct W U x t ∈ balancing P) ?_ ?_ ?_ ?_ ht
  · rintro t ⟨y, g, u, rfl⟩
    change coverAct W U x
      ((y * uι W (g : VHatCarrier W)) ⊗ₜ[ℂ] u - y ⊗ₜ[ℂ] (P.act g u)) ∈ balancing P
    rw [map_sub, coverAct_tmul, coverAct_tmul, ← mul_assoc]
    exact Submodule.subset_span ⟨x * y, g, u, rfl⟩
  · change coverAct W U x (0 : IndCover W U) ∈ balancing P
    rw [map_zero]; exact Submodule.zero_mem _
  · intro t₁ t₂ _ _ h₁ h₂
    change coverAct W U x (t₁ + t₂) ∈ balancing P
    rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  · intro c t₁ _ h₁
    change coverAct W U x (c • t₁) ∈ balancing P
    rw [map_smul]; exact Submodule.smul_mem _ _ h₁

/-- **DLM3 (4.2)**: the loop mode `x ∈ V̂` acts on `M_n(U)` by left multiplication by `uι x`. -/
noncomputable def indActEnd (P : ParabolicRep W n U) (x : VHatCarrier W) : End ℂ (IndMod P) :=
  Submodule.mapQ _ _ (coverAct W U (uι W x))
    (fun t ht => balancing_stable P (uι W x) t ht)

@[simp] theorem indActEnd_mk (P : ParabolicRep W n U) (x : VHatCarrier W) (y : UEnv W) (u : U) :
    indActEnd P x (indMk P (y ⊗ₜ[ℂ] u)) = indMk P ((uι W x * y) ⊗ₜ[ℂ] u) := rfl

/-- **The `V̂`-representation of DLM3 (4.2)** on `M_n(U)`: the left regular action of `U(V̂)`,
restricted along `uι`.  The Lie-morphism property is *free* (`uι` is a Lie morphism and left
multiplication is an algebra map), so no `hderiv`/`hbracket` obligations arise. -/
noncomputable def indRho (P : ParabolicRep W n U) : VHatRep W (IndMod P) where
  toFun := indActEnd P
  map_add' x y := by
    refine indMod_ext fun z u => ?_
    change indTmul P u (uι W (x + y) * z)
      = indTmul P u (uι W x * z) + indTmul P u (uι W y * z)
    rw [map_add, add_mul, map_add]
  map_smul' c x := by
    refine indMod_ext fun z u => ?_
    change indTmul P u (uι W (c • x) * z) = c • indTmul P u (uι W x * z)
    rw [map_smul, smul_mul_assoc, map_smul]
  map_lie' {x y} := by
    refine indMod_ext fun z u => ?_
    change indTmul P u (uι W ⁅x, y⁆ * z)
      = indTmul P u (uι W x * (uι W y * z)) - indTmul P u (uι W y * (uι W x * z))
    rw [(uι W).map_lie x y, Ring.lie_def, sub_mul, mul_assoc, mul_assoc, map_sub]

@[simp] theorem indRho_apply (P : ParabolicRep W n U) (x : VHatCarrier W) :
    indRho P x = indActEnd P x := rfl

@[simp] theorem indRho_actMode_mk (P : ParabolicRep W n U) (a : 𝒱) (m : ℤ) (y : UEnv W) (u : U) :
    (indRho P).actMode a m (indMk P (y ⊗ₜ[ℂ] u)) = indMk P ((uι W (gen W a m) * y) ⊗ₜ[ℂ] u) := rfl

/-! ## `M_n(U)` is generated from `1 ⊗ U` -/

/-- **The generation principle for `M_n(U)`** (PBW-free): a submodule containing `1 ⊗ U` and stable
under all loop modes is everything.  This is what makes every property of `M_n(U)` provable by an
induction on words in `U(V̂)` (`uenv_induction`). -/
theorem ind_generation (P : ParabolicRep W n U) (S : Submodule ℂ (IndMod P))
    (hone : ∀ u : U, indMk P ((1 : UEnv W) ⊗ₜ[ℂ] u) ∈ S)
    (hact : ∀ (x : VHatCarrier W) (z : IndMod P), z ∈ S → indRho P x z ∈ S) : S = ⊤ := by
  have key : ∀ (u : U) (y : UEnv W), indMk P (y ⊗ₜ[ℂ] u) ∈ S := by
    intro u
    have hmul : ∀ b : UEnv W, ∀ y : UEnv W, indTmul P u y ∈ S → indTmul P u (b * y) ∈ S := by
      intro b
      refine uenv_induction
        (C := fun b => ∀ y : UEnv W, indTmul P u y ∈ S → indTmul P u (b * y) ∈ S)
        ?_ ?_ ?_ ?_ b
      · intro c y hy
        rw [← Algebra.smul_def, map_smul]
        exact Submodule.smul_mem _ _ hy
      · intro x y hy
        have := hact x _ hy
        rwa [indRho_apply, indTmul_apply, indActEnd_mk, ← indTmul_apply] at this
      · intro b₁ b₂ h₁ h₂ y hy
        rw [mul_assoc]
        exact h₁ (b₂ * y) (h₂ y hy)
      · intro b₁ b₂ h₁ h₂ y hy
        rw [add_mul, map_add]
        exact Submodule.add_mem _ (h₁ y hy) (h₂ y hy)
    intro y
    have h1 : indTmul P u (1 : UEnv W) ∈ S := hone u
    have := hmul y 1 h1
    rwa [mul_one, indTmul_apply] at this
  have key2 : ∀ t : IndCover W U, indMk P t ∈ S := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul y u => exact key u y
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨t, rfl⟩ := (balancing P).mkQ_surjective z
  exact key2 t

/-! ## Lower truncation: `ActModeTruncated (indRho P)` -/

/-- The subspace of vectors on which the loop modes are lower truncated. -/
noncomputable def truncSub (P : ParabolicRep W n U) : Submodule ℂ (IndMod P) where
  carrier := {z | ∀ c : 𝒱, ∃ N : ℤ, ∀ m : ℤ, N ≤ m → (indRho P).actMode c m z = 0}
  add_mem' := by
    rintro z z' hz hz' c
    obtain ⟨N, hN⟩ := hz c
    obtain ⟨N', hN'⟩ := hz' c
    refine ⟨max N N', fun m hm => ?_⟩
    rw [map_add, hN m (le_trans (le_max_left _ _) hm), hN' m (le_trans (le_max_right _ _) hm),
      add_zero]
  zero_mem' := fun c => ⟨0, fun m _ => map_zero _⟩
  smul_mem' := by
    rintro a z hz c
    obtain ⟨N, hN⟩ := hz c
    exact ⟨N, fun m hm => by rw [map_smul, hN m hm, smul_zero]⟩

theorem mem_truncSub {P : ParabolicRep W n U} {z : IndMod P} :
    z ∈ truncSub P ↔ ∀ c : 𝒱, ∃ N : ℤ, ∀ m : ℤ, N ≤ m → (indRho P).actMode c m z = 0 := Iff.rfl

/-- `1 ⊗ u` is lower truncated: for `m` large, `c(m)` is deep, hence acts by `0` on `U`. -/
theorem one_tmul_mem_truncSub (P : ParabolicRep W n U) (u : U) :
    indMk P ((1 : UEnv W) ⊗ₜ[ℂ] u) ∈ truncSub P := by
  intro c
  obtain ⟨N, hN⟩ := gen_eventually_deep W n c
  refine ⟨N, fun m hm => ?_⟩
  have hdeep : gen W c m ∈ deepPart W n := hN m hm
  have hg : gen W c m ∈ parabolic W n := deepPart_le_parabolic W n hdeep
  have hbal := indMk_balance P 1 (⟨gen W c m, hg⟩ : Pn W n) u
  rw [P.deep_zero (⟨gen W c m, hg⟩ : Pn W n) hdeep] at hbal
  change indMk P ((uι W (gen W c m) * 1) ⊗ₜ[ℂ] u) = 0
  rw [mul_one, ← one_mul (uι W (gen W c m))]
  change indMk P (((1 : UEnv W) * uι W ((⟨gen W c m, hg⟩ : Pn W n) : VHatCarrier W)) ⊗ₜ[ℂ] u) = 0
  rw [hbal]
  rw [LinearMap.zero_apply, TensorProduct.tmul_zero, map_zero]

/-- The stability of `truncSub` under a *single* loop mode: the Borcherds commutator
`actMode_bracket` exchanges `c(m)` past `b(k)` at the cost of finitely many iterate modes, each of
which is again eventually truncated. -/
theorem truncSub_actMode (P : ParabolicRep W n U) (b : 𝒱) (k : ℤ) (z : IndMod P)
    (hz : z ∈ truncSub P) : (indRho P).actMode b k z ∈ truncSub P := by
  classical
  intro c
  obtain ⟨N₀, hN₀⟩ := hz c
  obtain ⟨Ncb, hNcb⟩ := W.smul_eventually_zero c b
  choose Nf hNf using fun i : ℕ => hz (W.smul c (i : ℤ) b)
  set K : ℕ := Ncb.toNat with hK
  set Nmax : ℕ := (Finset.range K).sup (fun i => (Nf i + (i : ℤ) - k).toNat) with hNmax
  refine ⟨max N₀ (Nmax : ℤ), fun m hm => ?_⟩
  have hm0 : N₀ ≤ m := le_trans (le_max_left _ _) hm
  have hmM : (Nmax : ℤ) ≤ m := le_trans (le_max_right _ _) hm
  set ev : End ℂ (IndMod P) →ₗ[ℂ] IndMod P :=
    { toFun := fun T => T z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hev
  have hbr : ⁅(indRho P).actMode c m, (indRho P).actMode b k⁆ ∈ LinearMap.ker ev := by
    rw [(indRho P).actMode_bracket c b m k]
    refine finsum_mem_submodule _ fun i => Submodule.smul_mem _ _ ?_
    rw [LinearMap.mem_ker]
    change (indRho P).actMode (W.smul c (i : ℤ) b) (m + k - (i : ℤ)) z = 0
    by_cases hi : (i : ℤ) < Ncb
    · have hiK : i ∈ Finset.range K := Finset.mem_range.mpr (by omega)
      have hsup : (Nf i + (i : ℤ) - k).toNat ≤ Nmax :=
        Finset.le_sup (f := fun j : ℕ => (Nf j + (j : ℤ) - k).toNat) hiK
      have h1 : Nf i + (i : ℤ) - k ≤ ((Nf i + (i : ℤ) - k).toNat : ℤ) := Int.self_le_toNat _
      have h2 : (((Nf i + (i : ℤ) - k).toNat : ℕ) : ℤ) ≤ (Nmax : ℤ) := by exact_mod_cast hsup
      exact hNf i (m + k - (i : ℤ)) (by omega)
    · rw [hNcb (i : ℤ) (by omega), VHatRep.actMode_zero_left]
      rfl
  rw [LinearMap.mem_ker] at hbr
  have hbrz : (⁅(indRho P).actMode c m, (indRho P).actMode b k⁆ : End ℂ (IndMod P)) z = 0 := hbr
  have hcomm : (indRho P).actMode c m ((indRho P).actMode b k z)
      = (indRho P).actMode b k ((indRho P).actMode c m z)
        + (⁅(indRho P).actMode c m, (indRho P).actMode b k⁆ : End ℂ (IndMod P)) z := by
    rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
    abel
  rw [hcomm, hN₀ m hm0, map_zero, hbrz, add_zero]

/-- **`ActModeTruncated (indRho P)` — the module-field property of `M_n(U)`.**  DLM3 uses it
silently from (4.2) on; it is a genuine theorem: the deep part annihilates `U` (`deep_zero`), and
`gen_eventually_deep` together with the Borcherds commutator propagate that through all of
`U(V̂)`. -/
theorem ind_actModeTruncated (P : ParabolicRep W n U) :
    VHatRep.ActModeTruncated (indRho P) := by
  have htop : truncSub P = ⊤ := by
    refine ind_generation P (truncSub P) (one_tmul_mem_truncSub P) ?_
    intro x z hz
    have hx : x ∈ Submodule.span ℂ (Set.range (fun p : 𝒱 × ℤ => gen W p.1 p.2)) := by
      rw [gen_span_top]; exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun x _ => indRho P x z ∈ truncSub P) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨⟨b, k⟩, rfl⟩
      exact truncSub_actMode P b k z hz
    · change indRho P (0 : VHatCarrier W) z ∈ truncSub P
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro x₁ x₂ _ _ h₁ h₂
      change indRho P (x₁ + x₂) z ∈ truncSub P
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ h₁ h₂
    · intro c x₁ _ h₁
      change indRho P (c • x₁) z ∈ truncSub P
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ h₁
  intro a z
  have hz : z ∈ truncSub P := by rw [htop]; trivial
  exact hz a

/-! ## Vacuum creation: `VacuumCreation (indRho P)` -/

/-- `uι 𝟙(−1)` is central in `U(V̂)` (`𝟙(−1)` is central in `V̂` and the loop modes generate). -/
theorem uι_vacuum_central (W : VertexOperatorAlgebra 𝒱) (y : UEnv W) :
    Commute (uι W (gen W W.vacuum (-1))) y := by
  refine uenv_induction (C := fun y => Commute (uι W (gen W W.vacuum (-1))) y) ?_ ?_ ?_ ?_ y
  · intro c
    exact (Algebra.commutes c (uι W (gen W W.vacuum (-1)))).symm
  · intro x
    have h : ⁅uι W (gen W W.vacuum (-1)), uι W x⁆ = 0 := by
      rw [← (uι W).map_lie (gen W W.vacuum (-1)) x, gen_vacuum_central W x, map_zero]
    rw [Ring.lie_def, sub_eq_zero] at h
    exact h
  · intro a b ha hb; exact ha.mul_right hb
  · intro a b ha hb; exact ha.add_right hb

/-- **`VacuumCreation (indRho P)`** — the module form of VA2, `𝟙₍ₘ₎ = δ_{m,−1}·id`.  For `m ≠ −1`
the loop generator `𝟙(m)` is already `0` in `V̂`; for `m = −1` it is central and acts on `U` as the
identity of `A_n(𝒱)`. -/
theorem ind_vacuumCreation (P : ParabolicRep W n U) :
    VHatRep.VacuumCreation (indRho P) := by
  intro m
  by_cases hm : m = -1
  · subst hm
    rw [if_pos rfl]
    refine indMod_ext fun y u => ?_
    change indMk P ((uι W (gen W W.vacuum (-1)) * y) ⊗ₜ[ℂ] u) = indMk P (y ⊗ₜ[ℂ] u)
    rw [(uι_vacuum_central W y)]
    have hbal := indMk_balance P y (⟨gen W W.vacuum (-1), vacuumGen_mem_parabolic W n⟩ : Pn W n) u
    rw [P.vacuum_one] at hbal
    change indMk P ((y * uι W ((⟨gen W W.vacuum (-1), vacuumGen_mem_parabolic W n⟩ :
      Pn W n) : VHatCarrier W)) ⊗ₜ[ℂ] u) = indMk P (y ⊗ₜ[ℂ] u)
    rw [hbal]
    rfl
  · rw [if_neg hm, VHatRep.actMode_def, gen_vacuum_eq_zero W hm, map_zero]

/-! ## The defect quotient of `M_n(U)` is a weak `𝒱`-module

DLM3 (4.3)–(4.4) divide `M_n(U)` by the `U(V̂)`-submodule generated by the associativity defect and
call the result `M̄_n(U)`.  In the repo the corresponding object is `defectSubmodule` — the smallest
`V̂`-invariant submodule containing every *iterate* defect (`ZhuVermaAnArchMUjacobiClose`) — and
`isModuleJacobi_quotientRep` proves the module Jacobi 5.3.1b for that quotient unconditionally,
given only the truncation of the ambient representation.  Combining it with the two theorems above
gives the module-hood half of DLM3 Theorem 4.1 outright.

⚠ **Two honest caveats, recorded rather than papered over.**
1. The repo's `defectSubmodule` imposes the defect relation for *every* vector of `M_n(U)`, while
   DLM3 (4.3) imposes it only for `u ∈ U` (level `n`) and then *proves* (Props 4.3, 4.6, 4.7) that
   it propagates.  Our quotient is therefore a priori a quotient of DLM3's `M̄_n(U)`.  Module-hood
   is thereby free; the level-`n` identification is not.
2. Consequently **nothing here claims `M̄_n(U)(n) = U`, `M̄_n(U)(0) ≠ 0`, or admissibility** — those
   are DLM3's `U*`/length-filtration/`J` package (Thm 4.1, endgame after Prop 4.7), untouched. -/

/-- **DLM3 (4.4)** in the repo's form: the defect quotient `M̄_n(U)` of `M_n(U)`. -/
abbrev IndBar (P : ParabolicRep W n U) : Type u :=
  IndMod P ⧸ VHatRep.defectSubmodule (indRho P)

/-- The `V̂`-representation on `M̄_n(U)`. -/
noncomputable def indBarRho (P : ParabolicRep W n U) : VHatRep W (IndBar P) :=
  VHatRep.quotientRep (indRho P) (VHatRep.defectSubmodule (indRho P))
    (VHatRep.defectSubmodule_invariant (indRho P))

@[simp] theorem indBarRho_actMode_mk (P : ParabolicRep W n U) (a : 𝒱) (p : ℤ) (x : IndMod P) :
    (indBarRho P).actMode a p (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk ((indRho P).actMode a p x) :=
  VHatRep.actMode_quotientRep _ _ _ a p x

/-- Truncation descends to the defect quotient. -/
theorem indBar_actModeTruncated (P : ParabolicRep W n U) :
    VHatRep.ActModeTruncated (indBarRho P) :=
  VHatRep.actMode_quotientRep_truncated (indRho P) (VHatRep.defectSubmodule (indRho P))
    (VHatRep.defectSubmodule_invariant (indRho P)) (ind_actModeTruncated P)

/-- Vacuum creation descends to the defect quotient. -/
theorem indBar_vacuumCreation (P : ParabolicRep W n U) :
    VHatRep.VacuumCreation (indBarRho P) := by
  intro m
  refine LinearMap.ext fun y => ?_
  refine Submodule.Quotient.induction_on _ y fun x => ?_
  rw [indBarRho_actMode_mk, ind_vacuumCreation P m]
  by_cases hm : m = -1
  · rw [if_pos hm, if_pos hm]
    rfl
  · rw [if_neg hm, if_neg hm, LinearMap.zero_apply, LinearMap.zero_apply,
      Submodule.Quotient.mk_zero]

/-- **The module-hood half of DLM3 Theorem 4.1**: the defect quotient `M̄_n(U)` of the induced
module is a genuine weak `𝒱`-module (Gannon Def. 5.3.1a–b).  Its three fields are supplied by
`indBar_vacuumCreation` (5.3.1a), `indBar_actModeTruncated` (the field property) and
`isModuleJacobi_quotientRep` (5.3.1b, unconditional on the defect quotient).

Read the two caveats above before using this: it is *weak*-module-hood for the repo's defect
quotient; the grading, `M̄_n(U)(0) ≠ 0` and `M̄_n(U)(n) = U` are **not** claimed. -/
noncomputable def indBarWeakModule (P : ParabolicRep W n U) : WeakModule W (IndBar P) :=
  VHatRep.weakModuleOfRep (indBarRho P) (indBar_actModeTruncated P) (indBar_vacuumCreation P)
    (VHatRep.isModuleJacobi_quotientRep (indRho P) (ind_actModeTruncated P))

@[simp] theorem indBarWeakModule_act (P : ParabolicRep W n U) (a : 𝒱) (p : ℤ) (y : IndBar P) :
    (indBarWeakModule P).act a p y = (indBarRho P).actMode a p y :=
  VHatRep.weakModuleOfRep_act _ _ _ _ a p y

end DLM3

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
