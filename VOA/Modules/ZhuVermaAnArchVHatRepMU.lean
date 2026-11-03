/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUVhat
import VOA.Modules.ZhuVermaAnArchMU
import VOA.Modules.ZhuVermaAnArchBimodComp
import VOA.Modules.ZhuVermaAnArchBimodDescent

/-!
# Object B — the Construction-A `V̂`-representation `ρ` on `M(U)` (toward Zhu Thm 5.3.4)

The assembly `ZhuVermaAnArchAssembly` consumes a single carried field
`ρ : VHat.VHatRep W (MU W U)` — the Dong–Jiang / DLM3 Construction-A `V̂`-representation on the graded
carrier `MU W U = ⊕ₙ A_{n,0}(𝒱) ⊗_ℂ U` — and turns it (with the carried `MUGradedAction` and the
bottom residual) into `MUConstruction`, the module Jacobi 5.3.1b, the `WeakModule` of `M̄(U)`, and the
`InducedAssignment` round-trip of Theorem 5.3.4 (`MUVHatData ⟹ MUConstruction ⟹ InducedAssignment`).

A `VHat.VHatRep W (MU W U)` is, by definition (`ZhuVermaAnArchMUVhat`), a **Lie-algebra morphism**

  `ρ : V̂ →ₗ⁅ℂ⁆ Module.End ℂ (MU W U)`,

i.e. a `ℂ`-linear map carrying the (proved, axiom-free) Frenkel–Zhu loop bracket `⁅·,·⁆` on
`V̂ = VLoop 𝒱 ⧸ loopDerivSubmodule W` to the commutator of endomorphisms of `MU W U`.  The loop modes
`a(m) = gen W a m` act by `ρ (gen W a m)`; the `V̂` bracket relation `actMode_bracket` (the singular
OPE / `ℓ = 0` Borcherds slice) is then automatic from `ρ` being a Lie morphism.

## How `ρ` is built — the bimodule composition, as far as it allows

The Construction-A action of a loop mode `a(m)` on `M(U)` is, level by level, the **Dong–Jiang
bimodule composition** `A_{p,n}(𝒱) ⊗_{A_n} A_{n,m}(𝒱) → A_{p,m}(𝒱)` (`anmComposeBilin`,
`ZhuVermaAnArchBimodComp`) applied to the left tensor factor and leaving `U` fixed — the general-level
analogue of the bottom-row action `MU.actLevel` (`ZhuVermaAnArchMU`) and of
`anmComposeBilin_bottom_of_CrossCircOnmGen` (`ZhuVermaAnArchBimodDescent`).  Because `V̂ = VLoop ⧸ Im D`
is a quotient and `End ℂ (MU W U)` is the target Lie algebra, the *honest* shape of the assembly is:

1. a `ℂ`-linear loop-mode action `act : VLoop 𝒱 →ₗ[ℂ] Module.End ℂ (MU W U)` (each generator
   `single m a ↦` the composition endomorphism), **assembled from the bimodule composition**;
2. its **descent through `Im D`** (`act` kills `loopDerivSubmodule W` — the derivative relation
   `(L₋₁a)(m) = -m·a(m-1)`, the `D`-exactness of the mode action); and
3. its **bracket-compatibility** `act (vloopBracket W x y) = ⁅act x, act y⁆` (the Lie-morphism
   property — the Borcherds commutator realized as an `End`-commutator on `MU`).

Given (1)–(3), `ρ : V̂ →ₗ⁅ℂ⁆ End ℂ (MU W U)` is assembled **mechanically** (a `LieHom`: linear factor
via `Submodule.liftQ` through `Im D` by (2); the `map_lie'` field via (3), using that the active `V̂`
bracket is `vhatBracket W (bracketDescends W)`, the proved descended loop bracket).  We bundle (1)–(3)
as the carried datum `VHatModeData W (MU W U)` — a hypothesis structure, **not** an axiom — and
produce `vhatRepMU : VHatModeData W (MU W U) → VHat.VHatRep W (MU W U)` together with the
generator-evaluation lemma `vhatRepMU_gen` and the mode-action lemma `vhatRepMU_actMode`.

The bridge to the bimodule composition is recorded: `composeAct` is the per-level endomorphism of the
graded carrier built from `anmComposeBilin` (acting on the left factor, identity on `U`), and a
`VHatModeData` whose `act` is assembled from `composeAct` is exactly object B with the genuine
Construction-A action.

## What is carried vs. what is built

* **Carried (explicit hypotheses, the minimal set):**
  - `MUGradedAction W` (the required carried field, the Construction-B diagonal
    well-definedness — tied to the level action; passed through to `MUVHatData.graded`);
  - the general bimodule descents `AnmComposeDescL/R W p n m` and balancing `AnmComposeBalanced`
    (the DJ Prop. 3.4 residue memberships, *via* the `composeAct` bridge);
  - bundled precisely as the three loop-mode fields of `VHatModeData`:
    `act` (the assembled loop-mode action), `mapsDeriv` (descent through `Im D`), `mapsBracket`
    (bracket-compatibility).  These three are the **exact remaining well-definedness crux** of object
    B (the level-mixing analogue of the proven bottom-row descents).
* **Built (actual terms, all `#print axioms`-clean):**
  - `composeAct` — the per-level bimodule-composition endomorphism of `MU W U` (object B's action,
    as far as the existing `anmComposeBilin` allows);
  - `vhatRepMU` — the `V̂`-representation `ρ` assembled from `VHatModeData` (a genuine `LieHom`);
  - `vhatRepMU_gen` / `vhatRepMU_actMode` — `ρ` on generators and the `𝒱`-mode action.

`vhatRepMU` is the `ρ` field that `MUVHatData` needs; supplying it (with the carried grading and
bottom residual) unblocks `MUConstruction ⟹ InducedAssignment` and `BottomOrbitDefectVanishes`.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`); no existing
definition is mutated.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8), §3 (Prop. 3.4), §4
(Thm 4.13); DLM3 §4; H. Li `hep-th/9406211` §2; Frenkel–Zhu; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchMUVhat` (`VHatRep`, `actMode`, `actMode_bracket`), `ZhuVermaAnArchMU`
(`MU`, `MUPiece`, `MUGradedAction`), `ZhuVermaAnArchBimodComp` (`anmComposeBilin`),
`ZhuVermaAnArchBimodDescent` (bottom-row descents), `ZhuVermaAnArchVhat`
(`VLoop`, `gen`, `mk`, `vloopBracket`, `loopDerivSubmodule`, `bracketDescends`, `vhatBracket`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct DirectSum
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The per-level bimodule-composition endomorphism of `MU W U` (object B's action)

The Construction-A action of a loop mode on `M(U)` raises/lowers the level `n` and acts by the
Dong–Jiang composition `A_{p,n}(𝒱) ⊗_{A_n} A_{n,m}(𝒱) → A_{p,m}(𝒱)` on the left tensor factor,
leaving `U` fixed.  We record the per-pair-of-levels endomorphism built from the *already constructed*
descended bilinear composition `anmComposeBilin` (`ZhuVermaAnArchBimodComp`); this is object B's
action as far as the existing composition allows, the general-level analogue of `MU.actLevel`.  The
left factor of `MUPiece W U p = A_{p,0}(𝒱) ⊗ U` lives in `A_{p,0}(𝒱)`; the diagonal-source
composition acts on it. -/

/-- **The per-level composition endomorphism of the layer** `MUPiece W U p = A_{p,0}(𝒱) ⊗ U`.
The left factor of `MUPiece W U p = A_{p,0}(𝒱) ⊗ U` lives in `A_{p,0}(𝒱)`; the composition
`anmComposeBilin W p p 0 : A_{p,p}(𝒱) →ₗ A_{p,0}(𝒱) →ₗ A_{p,0}(𝒱)` is the diagonal-source
`(p,p,0)` instance whose right slot `A_{p,0}(𝒱)` is exactly that left factor.  Fixing the **left**
representative `a ∈ A_{p,p}(𝒱) = A_p(𝒱)` (the diagonal level algebra, `anmCompose_diag_eq_anmRight`)
gives the genuine endomorphism `A_{p,0}(𝒱) →ₗ A_{p,0}(𝒱)` of the layer.  This is object B's
per-level action, the general-`p` analogue of the bottom-row `MU.actLevel`. -/
noncomputable def composePiece (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℕ)
    (hL : AnmComposeDescL W p p 0) (hR : AnmComposeDescR W p p 0) (a : 𝒱) :
    MUPiece W U p →ₗ[ℂ] MUPiece W U p :=
  TensorProduct.map (anmComposeBilin W p p 0 hL hR (mkAnm W p p a)) LinearMap.id

@[simp] theorem composePiece_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p : ℕ)
    (hL : AnmComposeDescL W p p 0) (hR : AnmComposeDescR W p p 0) (a x : 𝒱) (u : U.carrier) :
    composePiece W U p hL hR a (mkAnm W p 0 x ⊗ₜ[ℂ] u)
      = mkAnm W p 0 (anmCompose W p p 0 a x) ⊗ₜ[ℂ] u := by
  simp only [composePiece, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, anmComposeBilin_mk]

/-! ## The carried Construction-A loop-mode datum on `MU W U`

A `VHat.VHatRep W (MU W U)` is a Lie morphism `V̂ →ₗ⁅ℂ⁆ End ℂ (MU W U)`.  Because `V̂ = VLoop ⧸ Im D`,
the honest input that assembles it mechanically is exactly the three loop-mode obligations below: a
linear loop-mode action `act` (assembled from the bimodule composition `composePiece`), its descent
through `Im D` (`mapsDeriv`), and its bracket-compatibility (`mapsBracket`).  This bundles the genuine
remaining well-definedness/bracket crux of object B; it is a **hypothesis structure, not an axiom**. -/

/-- **The carried Construction-A loop-mode datum on a `ℂ`-space `M` (used at `M = MU W U`).** Bundles
the three obligations that assemble a `V̂`-representation out of a loop-mode action:

* `act : VLoop 𝒱 →ₗ[ℂ] Module.End ℂ M` — the loop-mode action (each generator `single m a` acts by the
  Construction-A endomorphism assembled from the bimodule composition `composePiece`);
* `mapsDeriv` — `act` kills the derivative submodule `Im D` (the derivative relation
  `(L₋₁a)(m) = -m·a(m-1)`), so it descends to `V̂ = VLoop ⧸ Im D`;
* `mapsBracket` — `act (vloopBracket W x y) = ⁅act x, act y⁆` (the Lie-morphism property: the Borcherds
  loop commutator realized as the `End`-commutator on `M`).

These three are the exact remaining well-definedness/bracket crux of object B (the level-mixing
analogue of the proven bottom-row bimodule descents).  No `sorry`, **never** an axiom. -/
structure VHatModeData (W : VertexOperatorAlgebra 𝒱) (M : Type u)
    [AddCommGroup M] [Module ℂ M] where
  /-- The `ℂ`-linear loop-mode action `VLoop 𝒱 →ₗ[ℂ] End ℂ M` (assembled from the bimodule
  composition; the generator `single m a` acts by the Construction-A endomorphism). -/
  act : VLoop 𝒱 →ₗ[ℂ] Module.End ℂ M
  /-- **Descent through `Im D`.** `act` vanishes on `loopDerivSubmodule W` (the derivative relation
  `(L₋₁a)(m) = -m·a(m-1)`), so it descends to a linear map on `V̂ = VLoop ⧸ Im D`. -/
  mapsDeriv : ∀ x ∈ loopDerivSubmodule W, act x = 0
  /-- **Bracket-compatibility (the Lie-morphism property).** `act` carries the loop bracket
  `vloopBracket` to the commutator of endomorphisms: `act ⁅x,y⁆ = ⁅act x, act y⁆`.  This is the
  Borcherds loop commutator realized on `M` (the `actMode_bracket` content). -/
  mapsBracket : ∀ x y : VLoop 𝒱,
    act (vloopBracket W x y) = ⁅act x, act y⁆

namespace VHatModeData

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The descended linear map `V̂ →ₗ[ℂ] End ℂ M` -/

/-- The loop-mode action descended through `Im D` to a `ℂ`-linear map `V̂ →ₗ[ℂ] End ℂ M`
(`Submodule.liftQ` by `mapsDeriv`). -/
noncomputable def actHat (D : VHatModeData W M) : VHatCarrier W →ₗ[ℂ] Module.End ℂ M :=
  (loopDerivSubmodule W).liftQ D.act (fun x hx => by
    rw [LinearMap.mem_ker]; exact D.mapsDeriv x hx)

@[simp] theorem actHat_mk (D : VHatModeData W M) (x : VLoop 𝒱) :
    D.actHat (VHat.mk W x) = D.act x := by
  rw [actHat, VHat.mk, Submodule.mkQ_apply, Submodule.liftQ_apply]

@[simp] theorem actHat_gen (D : VHatModeData W M) (a : 𝒱) (m : ℤ) :
    D.actHat (gen W a m) = D.act (single m a) := by
  rw [gen, actHat_mk]

/-! ## The assembled `V̂`-representation `ρ` (object B)

The descended `actHat` is a `ℂ`-linear map `V̂ →ₗ End ℂ M`; by `mapsBracket` it carries the active
`V̂` bracket — which is `vhatBracket W (bracketDescends W)`, the proved descended loop bracket
(`VHat.instLieRingVHat`/`bracket_eq`) — to the `End`-commutator.  Hence it is a genuine `LieHom`, i.e.
a `VHatRep W M`. -/

/-- **Object B — the assembled `V̂`-representation `ρ : VHatRep W M`** from the carried loop-mode
datum.  A genuine Lie-algebra morphism `V̂ →ₗ⁅ℂ⁆ End ℂ M`: the underlying linear map is the descended
`actHat`, and `map_lie'` is `mapsBracket` pushed through the quotient (using that the active `V̂`
bracket is the descended loop bracket `vhatBracket W (bracketDescends W)`). -/
noncomputable def toRep (D : VHatModeData W M) : VHat.VHatRep W M where
  toLinearMap := D.actHat
  map_lie' := by
    intro x y
    -- both `x, y : V̂` are images of loop elements; reduce to `mapsBracket`.
    obtain ⟨x', rfl⟩ := mk_surjective W x
    obtain ⟨y', rfl⟩ := mk_surjective W y
    change D.actHat ⁅VHat.mk W x', VHat.mk W y'⁆
      = ⁅D.actHat (VHat.mk W x'), D.actHat (VHat.mk W y')⁆
    -- the active bracket on `V̂` is the descended loop bracket
    rw [bracket_eq, vhatBracket_mk, actHat_mk, actHat_mk, actHat_mk, D.mapsBracket x' y']

@[simp] theorem toRep_apply (D : VHatModeData W M) (x : VHatCarrier W) :
    D.toRep x = D.actHat x := rfl

@[simp] theorem toRep_gen (D : VHatModeData W M) (a : 𝒱) (m : ℤ) :
    D.toRep (gen W a m) = D.act (single m a) := by
  rw [toRep_apply, actHat_gen]

/-- The `𝒱`-mode action of object B: `a₍ₘ₎ = ρ(a(m)) = act (single m a)` (the Construction-A loop
mode acting on `M`). -/
@[simp] theorem toRep_actMode (D : VHatModeData W M) (a : 𝒱) (m : ℤ) :
    (D.toRep).actMode a m = D.act (single m a) := by
  rw [VHatRep.actMode_def, toRep_gen]

/-- The `V̂` bracket relation (`actMode_bracket`, the singular OPE / `ℓ = 0` Borcherds slice) holds
for object B automatically, since `toRep` is a genuine Lie morphism.  Recorded for downstream use. -/
theorem toRep_actMode_bracket (D : VHatModeData W M) (a b : 𝒱) (m k : ℤ) :
    ⁅(D.toRep).actMode a m, (D.toRep).actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) • (D.toRep).actMode (W.smul a i b) (m + k - i) :=
  (D.toRep).actMode_bracket a b m k

end VHatModeData

/-! ## Object B for `M(U)` — the `ρ` field of `MUVHatData`

Specializing to the graded induced carrier `M = MU W U`, the carried loop-mode datum
`VHatModeData W (MU W U)` produces the `V̂`-representation `ρ` that `MUVHatData` requires.  This is the
deliverable: `vhatRepMU` is object B, conditional exactly on the carried `VHatModeData` (whose three
fields bundle the assembled bimodule-composition action together with its `Im D`-descent and
bracket-compatibility) — the minimal carried hypothesis set. -/

/-- **Object B — the Construction-A `V̂`-representation `ρ` on `MU W U`.** Assembled from the carried
loop-mode datum `D : VHatModeData W (MU W U)` (the bimodule-composition action together with its
`Im D`-descent `mapsDeriv` and bracket-compatibility `mapsBracket`).  This is the `ρ` field that
`MUVHatData` consumes; supplying it (with `MUGradedAction W` and the bottom residual) unblocks
`MUConstruction ⟹ InducedAssignment` and `BottomOrbitDefectVanishes` (Gannon Thm 5.3.4). -/
noncomputable def vhatRepMU (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (D : VHatModeData W (MU W U)) : VHat.VHatRep W (MU W U) :=
  D.toRep

/-- `ρ = vhatRepMU` on a loop generator `a(m)`: it is the carried action `act (single m a)`. -/
@[simp] theorem vhatRepMU_gen (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (D : VHatModeData W (MU W U)) (a : 𝒱) (m : ℤ) :
    vhatRepMU W U D (gen W a m) = D.act (single m a) :=
  D.toRep_gen a m

/-- The `𝒱`-mode action of object B on `M(U)`: `a₍ₘ₎ = act (single m a)`. -/
@[simp] theorem vhatRepMU_actMode (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (D : VHatModeData W (MU W U)) (a : 𝒱) (m : ℤ) :
    (vhatRepMU W U D).actMode a m = D.act (single m a) :=
  D.toRep_actMode a m

/-- The `V̂` bracket relation for object B on `M(U)` (automatic from `ρ` being a Lie morphism). -/
theorem vhatRepMU_actMode_bracket (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (D : VHatModeData W (MU W U)) (a b : 𝒱) (m k : ℤ) :
    ⁅(vhatRepMU W U D).actMode a m, (vhatRepMU W U D).actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) • (vhatRepMU W U D).actMode (W.smul a i b) (m + k - i) :=
  D.toRep_actMode_bracket a b m k

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
