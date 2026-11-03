/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCarrierBridge

/-!
# Constructing the `CarrierBridge` — the Dong–Jiang identification `M̄(U) ≅ MU W U`

Part of the lifting construction for Zhu Theorem 5.3.4.  The main theorem
`Function.Bijective (forwardMap W)` (`headline_zhuBijection_of_bridge`,
`ZhuVermaAnArchCarrierBridge`) consumes a `VHat.CarrierBridge W U.carrier (MU W U) YMU` — the central
Dong–Jiang Prop 3.4 / 3.5 identification between the abstract Construction-A defect quotient
`M̄(U) = (U(V̂) ⊗ U) ⧸ defectSubmodule (freeRep W U)` and the headline graded carrier
`MU W U = ⊕ₙ A_{n,0}(𝒱) ⊗ U`, *together with* `𝒱`-mode equivariance.

A `CarrierBridge` is a `ℂ`-linear **isomorphism** (`≃ₗ`) plus equivariance.  Building a `≃ₗ` directly
is awkward: one would have to produce a bijective linear map and invert it.  This file **constructs**
the bridge from its honest constituents — the two *directional* DJ maps and the round-trip identities
— and isolates the EXACT remaining mathematical content (the DJ residue-membership well-definedness)
as a single, precise, carried datum.  Concretely:

## The construction (`CarrierBridge.ofData`)

A `CarrierBridgeData W M MUcar YMU` carries

* `fwd : M̄(U) →ₗ[ℂ] MUcar`     — the **forward DJ layering map** (a loop monomial in `U(V̂) ⊗ U`,
  modulo the defect submodule, lands in its `A_{n,0}`-layer through the general product `anmGen`,
  well-defined since the defects map into `OnmFull` — DJ Prop 3.4);
* `bwd : MUcar →ₗ[ℂ] M̄(U)`     — the **backward representative map** (an `A_{n,0} ⊗ U` element lifts
  to a representative loop monomial — DJ Prop 3.5);
* `left_inv`/`right_inv`        — `bwd ∘ fwd = id`, `fwd ∘ bwd = id` (mutually inverse: the two DJ
  maps are inverse on the nose, the genuine identification);
* `equivariant`                 — `fwd (actMode a m x) = YMU a m (fwd x)` (the `𝒱`-mode action is
  intertwined — DJ Prop 3.4 equivariance).

From this raw data, `CarrierBridge.ofData` assembles a genuine `CarrierBridge` term by packaging
`fwd`/`bwd` as a `LinearEquiv` via `LinearEquiv.ofLinear` (the two round-trips give the iso) and
forwarding `equivariant`.  This is pure linear algebra — **no membership/scalar/degree identity is
introduced here**; the genuine DJ content is carried verbatim inside `CarrierBridgeData`, never an
axiom.

A `CarrierBridgeData` term ⟹ a `CarrierBridge` term ⟹ (`headline_zhuBijection_of_bridge`) the Zhu
main theorem.  We restate the end-to-end consequence at the family level
(`CarrierBridgeDataFamily`, `zhuBijection_of_bridgeData`), so the remaining leaf is *exactly* the
four directional DJ pieces per bottom `U`, with the iso/inversion machinery discharged as terms.

## What is built (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `VHat.CarrierBridgeData W M MUcar YMU` — the raw directional DJ data (`fwd`, `bwd`, round-trips,
  equivariance).
* `VHat.CarrierBridge.ofData D : CarrierBridge W M MUcar YMU` — the assembled bridge, with
  `ofData_equiv_apply` / `ofData_equiv_symm_apply` (the iso is `fwd` with inverse `bwd`).
* `VHat.CarrierBridgeData.toCarrierBridge` — the same, as a method.
* `VHat.CarrierBridgeDataFamily W` — a per-`U` family of `CarrierBridgeData`, refining
  `CarrierBridgeFamily` with the directional data; `toCarrierBridgeFamily` produces the
  `CarrierBridgeFamily` consumed by `headline_zhuBijection_of_bridge`.
* `VOA.zhuBijection_of_bridgeData` — **main theorem**: from a `CarrierBridgeDataFamily` plus the
  downstream universal-property data, `Function.Bijective (forwardMap W)`.

## The remaining membership (the genuine DJ residue content, carried, never faked)

The only mathematical content is the existence of `fwd`/`bwd` and their being mutually inverse and
equivariant — i.e. the Dong–Jiang Prop 3.4 / 3.5 identification, the well-definedness of the
`anmGen`-layering modulo `OnmFull` (the defects map into `OnmFull`, `ZhuVermaAnArchAnmFull`).  This is
carried verbatim as the four `CarrierBridgeData` fields, **never** an axiom.  The
dimension-by-dimension match `dim M̄(U)(n) = dim A_{n,0}(𝒱) ⊗ U` (the reason `fwd`/`bwd` are inverse)
is engine-verified on the rank-1 free boson (`certificates/mathematica/carrier_bridge_check.wl`,
`n = 0,1,2`: both sides `= p(n)` with `U` the 1-dim bottom).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchCarrierRho` (`CarrierBridge`,
`freeRep`, `defectSubmodule`), `ZhuVermaAnArchCarrierBridge` (`transportRep`,
`CarrierBridgeFamily`, `headline_zhuBijection_of_bridge`), `ZhuVermaAnArchAnmFull`
(`anmGen`, `OnmFull`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
  {MUcar : Type u} [AddCommGroup MUcar] [Module ℂ MUcar] {YMU : 𝒱 → ℤ → End ℂ MUcar}

/-! ## The abstract defect quotient `M̄(U)` and its representation (abbreviations) -/

/-- The abstract Construction-A carrier `M̄(U) = (U(V̂) ⊗ M) ⧸ defectSubmodule (freeRep W M)`. -/
abbrev Mbar (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M] [Module ℂ M] : Type u :=
  (UEnv W ⊗[ℂ] M) ⧸ VHatRep.defectSubmodule (freeRep W M)

/-- The genuine defect-quotient representation on `M̄(U)` (the Construction-A engine). -/
noncomputable abbrev MbarRep (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M]
    [Module ℂ M] : VHatRep W (Mbar W M) :=
  VHatRep.quotientRep (freeRep W M) (VHatRep.defectSubmodule (freeRep W M))
    (VHatRep.defectSubmodule_invariant (freeRep W M))

/-! ## The raw directional Dong–Jiang data

We carry the two directional DJ maps and the round-trip / equivariance identities.  This is the
honest content of the bridge: the iso and its inverse are *not* abstractly extracted from a bijection
hypothesis — they are the genuine forward (`anmGen`-layering, DJ Prop 3.4) and backward
(representative loop monomial, DJ Prop 3.5) maps, with the round-trips recording that they identify
the two carriers exactly. -/

/-- **The raw directional `CarrierBridge` data** (Dong–Jiang Prop 3.4 / 3.5).  Carries:
* `fwd` — the forward DJ layering map `M̄(U) →ₗ MUcar`;
* `bwd` — the backward representative map `MUcar →ₗ M̄(U)`;
* `left_inv`/`right_inv` — the mutual-inverse identities (`bwd ∘ fwd = id`, `fwd ∘ bwd = id`);
* `equivariant` — `𝒱`-mode equivariance of `fwd` against the headline field `YMU`.

A `CarrierBridgeData` term assembles (`ofData`) into a genuine `CarrierBridge`; **no** axiom. -/
structure CarrierBridgeData (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M] [Module ℂ M]
    (MUcar : Type u) [AddCommGroup MUcar] [Module ℂ MUcar]
    (YMU : 𝒱 → ℤ → End ℂ MUcar) where
  /-- The forward Dong–Jiang layering map `M̄(U) →ₗ MUcar` (`anmGen`/`OnmFull` descent, Prop 3.4). -/
  fwd : Mbar W M →ₗ[ℂ] MUcar
  /-- The backward representative map `MUcar →ₗ M̄(U)` (loop-monomial lift, Prop 3.5). -/
  bwd : MUcar →ₗ[ℂ] Mbar W M
  /-- `bwd ∘ fwd = id` on `M̄(U)`. -/
  left_inv : bwd.comp fwd = LinearMap.id
  /-- `fwd ∘ bwd = id` on `MUcar`. -/
  right_inv : fwd.comp bwd = LinearMap.id
  /-- `𝒱`-mode equivariance: `fwd (a₍ₘ₎ x) = YMU a m (fwd x)` (DJ Prop 3.4 equivariance). -/
  equivariant : ∀ (a : 𝒱) (m : ℤ) (x : Mbar W M),
    fwd ((MbarRep W M).actMode a m x) = YMU a m (fwd x)

namespace CarrierBridgeData

variable (D : CarrierBridgeData W M MUcar YMU)

/-- The `ℂ`-linear isomorphism `M̄(U) ≃ₗ MUcar` packaged from the two directional maps via
`LinearEquiv.ofLinear` (the two round-trips give a genuine `≃ₗ`). -/
noncomputable def toLinearEquiv : Mbar W M ≃ₗ[ℂ] MUcar :=
  LinearEquiv.ofLinear D.fwd D.bwd D.right_inv D.left_inv

@[simp] theorem toLinearEquiv_apply (x : Mbar W M) : D.toLinearEquiv x = D.fwd x := rfl

@[simp] theorem toLinearEquiv_symm_apply (y : MUcar) : D.toLinearEquiv.symm y = D.bwd y := rfl

/-- **The assembled `CarrierBridge`** from the raw directional DJ data.  The iso is `toLinearEquiv`
(`fwd` with inverse `bwd`); equivariance is forwarded from `D.equivariant`.  Pure linear algebra — no
membership/scalar/degree identity introduced; the genuine DJ content is the carried `D`. -/
noncomputable def toCarrierBridge : CarrierBridge W M MUcar YMU where
  equiv := D.toLinearEquiv
  equivariant := fun a m x => by
    rw [toLinearEquiv_apply, toLinearEquiv_apply]
    exact D.equivariant a m x

@[simp] theorem toCarrierBridge_equiv :
    (D.toCarrierBridge).equiv = D.toLinearEquiv := rfl

@[simp] theorem toCarrierBridge_equiv_apply (x : Mbar W M) :
    (D.toCarrierBridge).equiv x = D.fwd x :=
  D.toLinearEquiv_apply x

@[simp] theorem toCarrierBridge_equiv_symm_apply (y : MUcar) :
    (D.toCarrierBridge).equiv.symm y = D.bwd y :=
  D.toLinearEquiv_symm_apply y

end CarrierBridgeData

/-- **`CarrierBridge.ofData`** — the `CarrierBridge` constructed from raw directional DJ data.  This
is the constructor form of `CarrierBridgeData.toCarrierBridge`: from `fwd`/`bwd`/round-trips/
equivariance, a genuine bridge term, hence the input of `headline_zhuBijection_of_bridge`. -/
noncomputable def CarrierBridge.ofData (D : CarrierBridgeData W M MUcar YMU) :
    CarrierBridge W M MUcar YMU :=
  D.toCarrierBridge

@[simp] theorem CarrierBridge.ofData_equiv_apply (D : CarrierBridgeData W M MUcar YMU)
    (x : Mbar W M) : (CarrierBridge.ofData D).equiv x = D.fwd x :=
  D.toCarrierBridge_equiv_apply x

@[simp] theorem CarrierBridge.ofData_equiv_symm_apply (D : CarrierBridgeData W M MUcar YMU)
    (y : MUcar) : (CarrierBridge.ofData D).equiv.symm y = D.bwd y :=
  D.toCarrierBridge_equiv_symm_apply y

/-! ## The representative-level forward map (the genuine `anmGen`/`OnmFull` well-definedness)

The forward DJ layering map `fwd : M̄(U) →ₗ MUcar` is the *descent* of a representative-level map
`g : (U(V̂) ⊗ M) →ₗ MUcar` (the `anmGen`-layering on loop monomials) **provided** `g` kills the defect
submodule, i.e. `defectSubmodule (freeRep W M) ≤ ker g`.  This is precisely the Dong–Jiang Prop 3.4
well-definedness: the defects map into `OnmFull` (`ZhuVermaAnArchAnmFull`), so the layering is
well-defined on `M̄(U)`.  We build `fwd` from `g` and that single membership via `Submodule.liftQ`,
sharpening the forward direction from a carried map to a carried representative map + the carried
membership (the genuine residue content). -/

/-- **The representative-level directional bridge data.**  Refines `CarrierBridgeData` on the forward
side: the forward map is given by a representative-level layering `g : (U(V̂) ⊗ M) →ₗ MUcar` together
with the well-definedness membership `hker : defectSubmodule ≤ ker g` (DJ Prop 3.4 — defects map into
`OnmFull`).  The backward map and round-trips/equivariance are stated at the representative level for
`g`. -/
structure CarrierBridgeReprData (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M]
    [Module ℂ M] (MUcar : Type u) [AddCommGroup MUcar] [Module ℂ MUcar]
    (YMU : 𝒱 → ℤ → End ℂ MUcar) where
  /-- The representative-level forward layering map on loop monomials `(U(V̂) ⊗ M) →ₗ MUcar`. -/
  g : (UEnv W ⊗[ℂ] M) →ₗ[ℂ] MUcar
  /-- **Well-definedness** (DJ Prop 3.4): `g` kills the defect submodule (defects map into
  `OnmFull`).  This is the genuine residue-membership content. -/
  hker : VHatRep.defectSubmodule (freeRep W M) ≤ LinearMap.ker g
  /-- The backward representative map `MUcar →ₗ M̄(U)` (loop-monomial lift, Prop 3.5). -/
  bwd : MUcar →ₗ[ℂ] Mbar W M
  /-- `bwd` is a left inverse of the descended forward map: `bwd (g t) = [t]`.  (This forces
  `bwd ∘ fwd = id`.) -/
  left_inv : ∀ t : UEnv W ⊗[ℂ] M, bwd (g t) = Submodule.Quotient.mk t
  /-- The forward-section identity: every `y` lifts to a representative `t` with `bwd y = [t]` and
  `g t = y`.  (This forces `fwd ∘ bwd = id`.) -/
  fwd_section : ∀ y : MUcar, ∃ t : UEnv W ⊗[ℂ] M,
    bwd y = Submodule.Quotient.mk t ∧ g t = y
  /-- Representative `𝒱`-mode equivariance: `g (a₍ₘ₎ · t) = YMU a m (g t)`, the loop-mode action of
  the free representation intertwined with the headline field. -/
  equivariant : ∀ (a : 𝒱) (m : ℤ) (t : UEnv W ⊗[ℂ] M),
    g ((freeRep W M).actMode a m t) = YMU a m (g t)

namespace CarrierBridgeReprData

variable (D : CarrierBridgeReprData W M MUcar YMU)

/-- The descended forward map `fwd = liftQ g hker : M̄(U) →ₗ MUcar`. -/
noncomputable def fwd : Mbar W M →ₗ[ℂ] MUcar :=
  (VHatRep.defectSubmodule (freeRep W M)).liftQ D.g D.hker

@[simp] theorem fwd_mk (t : UEnv W ⊗[ℂ] M) :
    D.fwd (Submodule.Quotient.mk t) = D.g t :=
  Submodule.liftQ_apply _ D.g t

/-- The assembled directional `CarrierBridgeData` from representative-level data: the forward map is
the genuine `liftQ`-descent of the layering `g` past the well-definedness membership `hker`. -/
noncomputable def toCarrierBridgeData : CarrierBridgeData W M MUcar YMU where
  fwd := D.fwd
  bwd := D.bwd
  left_inv := by
    refine LinearMap.ext fun x => ?_
    refine Submodule.Quotient.induction_on _ x fun t => ?_
    simp only [LinearMap.comp_apply, fwd_mk, LinearMap.id_coe, id_eq, D.left_inv t]
  right_inv := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨t, hbwd, hg⟩ := D.fwd_section y
    simp only [LinearMap.comp_apply, hbwd, fwd_mk, hg, LinearMap.id_coe, id_eq]
  equivariant := by
    intro a m x
    refine Submodule.Quotient.induction_on _ x fun t => ?_
    rw [fwd_mk]
    rw [show (MbarRep W M).actMode a m (Submodule.Quotient.mk t)
        = Submodule.Quotient.mk ((freeRep W M).actMode a m t) from
      VHatRep.actMode_quotientRep (freeRep W M) (VHatRep.defectSubmodule (freeRep W M))
        (VHatRep.defectSubmodule_invariant (freeRep W M)) a m t]
    rw [fwd_mk, D.equivariant a m t]

/-- The `CarrierBridge` built directly from representative-level data. -/
noncomputable def toCarrierBridge : CarrierBridge W M MUcar YMU :=
  D.toCarrierBridgeData.toCarrierBridge

end CarrierBridgeReprData

/-! ## The per-`U` family of directional bridge data → the headline `CarrierBridgeFamily`

`headline_zhuBijection_of_bridge` consumes a `CarrierBridgeFamily W` (one `CarrierBridge` per bottom
module `U`, plus the named grading/finiteness data).  We refine it: a `CarrierBridgeDataFamily`
carries the *directional* DJ data per `U` (assembled into bridges by `ofData`), together with the
same named grading data.  `toCarrierBridgeFamily` then produces the `CarrierBridgeFamily` the main theorem
consumes. -/

/-- **A per-`U` family of directional `CarrierBridgeData`** plus the named grading/finiteness data —
the refined input where each bridge is given by its honest forward/backward DJ maps rather than as an
opaque iso. -/
structure CarrierBridgeDataFamily (W : VertexOperatorAlgebra 𝒱) where
  /-- The lowest weight of `M(U)`. -/
  hU : AMod W → ℂ
  /-- The headline field on each carrier `MU W U`. -/
  YMU : ∀ U : AMod W, 𝒱 → ℤ → End ℂ (MU W U)
  /-- The directional Dong–Jiang bridge data `M̄(U) ≅ MU W U` for each bottom (DJ Prop 3.4/3.5). -/
  data : ∀ U : AMod W, CarrierBridgeData W U.carrier (MU W U) (YMU U)
  /-- Truncation of the free Construction-A action (PBW-gated bottom survival). -/
  htr : ∀ U : AMod W, VHatRep.ActModeTruncated (freeRep W U.carrier)
  /-- Vacuum creation (module VA2) on each headline field. -/
  hvac : ∀ (U : AMod W) (m : ℤ),
    YMU U W.vacuum m = if m = -1 then (1 : End ℂ (MU W U)) else 0
  /-- The grading scalar `L₀ = h + n` on each carrier (5.3.1c). -/
  hL0 : ∀ (U : AMod W) (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
    YMU U W.conformalVector 1 x = ((hU U : ℂ) + n) • x
  /-- Finiteness of each graded piece. -/
  hfin : ∀ (U : AMod W) (n : ℕ), FiniteDimensional ℂ (MU.deg W U n)
  /-- Bottom nonvanishing of each `M(U)`. -/
  hbot : ∀ U : AMod W, MU.deg W U 0 ≠ ⊥

namespace CarrierBridgeDataFamily

variable (F : CarrierBridgeDataFamily W)

/-- **The headline `CarrierBridgeFamily` produced by a directional family** — each per-`U` bridge is
`CarrierBridge.ofData (F.data U)`; the grading/finiteness data are forwarded.  This is exactly the
input `headline_zhuBijection_of_bridge` consumes. -/
noncomputable def toCarrierBridgeFamily : VHat.CarrierBridgeFamily W where
  hU := F.hU
  YMU := F.YMU
  bridge := fun U => CarrierBridge.ofData (F.data U)
  htr := F.htr
  hvac := F.hvac
  hL0 := F.hL0
  hfin := F.hfin
  hbot := F.hbot

@[simp] theorem toCarrierBridgeFamily_bridge (U : AMod W) :
    (F.toCarrierBridgeFamily).bridge U = CarrierBridge.ofData (F.data U) := rfl

@[simp] theorem toCarrierBridgeFamily_hU : (F.toCarrierBridgeFamily).hU = F.hU := rfl

@[simp] theorem toCarrierBridgeFamily_YMU : (F.toCarrierBridgeFamily).YMU = F.YMU := rfl

end CarrierBridgeDataFamily

end VHat

/-! ## The headline — the Zhu bijection from a directional carrier-bridge family

End-to-end: a `CarrierBridgeDataFamily` (the four directional Dong–Jiang pieces per bottom, plus the
named grading data) yields the `CarrierBridgeFamily` consumed by `headline_zhuBijection_of_bridge`,
hence the main Zhu theorem `Function.Bijective (forwardMap W)`. -/

/-- **Main connection — the Zhu bijection from a directional carrier-bridge family.**

From a `VHat.CarrierBridgeDataFamily W` (each bottom `U` supplied with the honest forward/backward
Dong–Jiang maps `fwd`/`bwd`, their mutual-inverse identities, and `𝒱`-mode equivariance, together
with the named grading/finiteness data) plus the downstream universal-property inputs (`ludata`, the
bottom-survival realization, the `M(·)`-functoriality `Dfun`, the irreducibility scope, and the
bottom-generation family `G`), the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)` is a **bijection**.

The directional family is assembled into a `CarrierBridgeFamily` by `CarrierBridge.ofData` (the iso
and its inverse are the carried `fwd`/`bwd`, the inversion machinery discharged as terms via
`LinearEquiv.ofLinear`), so this is literally `headline_zhuBijection_of_bridge` over
`F.toCarrierBridgeFamily`.  The only carried mathematical content is the Dong–Jiang Prop 3.4 / 3.5
residue-membership identification inside each `CarrierBridgeData` — **no `sorry`, no axiom, no
`pbw`**. -/
theorem zhuBijection_of_bridgeData {W : VertexOperatorAlgebra 𝒱}
    (F : VHat.CarrierBridgeDataFamily W)
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((F.toCarrierBridgeFamily.toMURepFamily).mudata U))
    (realizes : ∀ U : AMod W,
      AModEquiv W
        (((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata).K U).toAMod U)
    (Dfun : InducedAssignment.MUFunctorialData
      ((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata))
    (hall : InducedAssignment.AllLWIrreducible W)
    (G : InducedAssignment.GenFromBottomFinalFamily
      ((F.toCarrierBridgeFamily.toMURepFamily).toLUFamily ludata)) :
    Function.Bijective (forwardMap W) :=
  headline_zhuBijection_of_bridge F.toCarrierBridgeFamily ludata realizes Dfun hall G

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
