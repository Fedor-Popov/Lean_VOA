/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCarrierRho
import VOA.Modules.ZhuVermaAnArchMU
import VOA.Modules.ZhuVermaAnArchMUModuleDataBuild

/-!
# The `CarrierBridge` linchpin — transporting Construction A onto the headline carrier `MU W U`

This file is the linchpin of the lifting construction for Zhu Thm 5.3.4: it turns the
abstract Dong–Jiang identification `M̄(U) ≅ MU W U` (the `CarrierBridge` of
`ZhuVermaAnArchCarrierRho`, DJ Prop 3.4 / 3.5) into the *headline* inputs that
`MUModuleData.buildMUModuleData` consumes on the carrier `MU W U = ⊕ₙ A_{n,0}(𝒱) ⊗ U`.

## The transport (pure linear algebra — no membership/scalar/degree identity introduced here)

Given a `CarrierBridge W M MUcar YMU` (a `ℂ`-linear iso `e : M̄(U) ≃ₗ MUcar` intertwining the
`𝒱`-mode action with the headline field `YMU`), we **conjugate** the genuine defect-quotient
representation `ρ̄ = quotientRep (freeRep W M) …` (the axiom-free Construction-A engine built in
`ZhuVermaAnArchCarrierRho`) along `e`:

  `transportRep B  :=  e.conj ∘ ρ̄`    (`LinearEquiv.conj` of each loop mode).

`LinearEquiv.conj` is a *ring* iso `End M̄ ≃ End MUcar` (`conj_comp`, `conj_id`), so it carries the
`V̂`-bracket to the `V̂`-bracket: `transportRep B` is a **genuine `VHatRep W MUcar`**, no axiom and no
new hypothesis at the operator level.  Its `𝒱`-mode action is *exactly* the headline field:
`(transportRep B).actMode a m = YMU a m` (`transportRep_actMode`), by the bridge's equivariance.

Everything proved here is structural conjugation algebra — the *only* mathematical content is carried,
verbatim and never as an axiom, inside the `CarrierBridge` (the DJ Prop 3.4/3.5 iso + equivariance)
and the named truncation/vacuum/grading hypotheses.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `VHat.VHatRep.transport e ρ̄ : VHatRep W MUcar` — transport of any `VHatRep` along a `ℂ`-linear
  iso `e`, with `transport_actMode` (`a₍ₘ₎ = e ∘ ρ̄ a m ∘ e⁻¹`), `transport_truncated`,
  `transport_isModuleJacobi` (all transports are structural; no carried content).
* `VHat.transportRep B : VHatRep W MUcar` — the Construction-A representation **on the headline
  carrier `MU W U`**, obtained by conjugating the genuine defect-quotient engine along the bridge.
* `VHat.transportRep_actMode` — `(transportRep B).actMode a m = YMU a m`: the transported `𝒱`-mode
  action **is** the headline field (so all downstream `actMode` properties are properties of `YMU`).
* `VHat.transportRep_truncated` — `ActModeTruncated (transportRep B)`, transported from the carried
  bottom-survival truncation on `freeRep`.
* `VHat.transportRep_isModuleJacobi` — `(transportRep B).IsModuleJacobi`: the module Jacobi 5.3.1b on
  the headline carrier, transported from `freeRep_defectQuotient_isModuleJacobi`.
* `VHat.transportRep_vacuum` / `VHat.transportRep_L0` — vacuum-creation (module VA2) and the grading
  scalar (`L₀ = h + n`) on the headline carrier, given the corresponding carried datum *on `YMU`*
  (the DJ grading; these are the precise remaining `MUModuleData` inputs the bridge does NOT supply
  by itself).
* `VHat.headline_buildMUModuleData` / `VHat.headline_MURepFamily_data` — the headline reduction:
  from a `CarrierBridge` (per `U`) plus the named grading/vacuum/finiteness/bottom data, the
  `MURepFamily`-style data on `MU W U` is produced, hence `MUModuleData.buildMUModuleData` and the
  main Zhu theorem `Function.Bijective (forwardMap W)` (`headline_zhuBijection_of_bridge`).

## The remaining membership (the genuine DJ residue content, carried, never faked)

The *existence* of the `CarrierBridge` (the iso `M̄(U) ≅ ⊕ₙ A_{n,0} ⊗ U` and its equivariance) is the
Dong–Jiang Prop 3.4 / 3.5 identification: the loop monomial `1 ⊗ (a₁₍m₁₎⋯aₖ₍mₖ₎) ⊗ u` modulo the
defect submodule lands in the `A_{n,0}` layer through the general product `anmGen`, well-defined since
the defects map into `OnmFull` (`ZhuVermaAnArchAnmFull`).  This is the residue-membership descent —
carried as the explicit `CarrierBridge` hypothesis here, NOT proved (and NOT an axiom).  The
dimension-by-dimension match `dim M̄(U)(n) = dim A_{n,0}(𝒱) ⊗ U` is engine-verified on the rank-1 free
boson (`certificates/mathematica/carrier_bridge_check.wl`, `n = 0,1,2`: both sides `= p(n)` with `U` the
1-dim bottom).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchCarrierRho` (`freeRep`,
`CarrierBridge`, `headline_isModuleJacobi_transported`), `ZhuVermaAnArchMU` (`MU`, `MU.deg`),
`ZhuVermaAnArchMUModuleDataBuild` (`buildMUModuleData`, `MURepFamily`, `zhuBijection_of_repFamily`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M N : Type u}
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-! ## Transport of a `V̂`-representation along a `ℂ`-linear isomorphism

`LinearEquiv.conj e : End ℂ M ≃ₗ End ℂ N` is multiplicative (`conj_comp`) and unital (`conj_id`), so
it is a ring iso of endomorphism algebras.  Therefore conjugating a `V̂`-representation `ρ : VHatRep
W M` along an iso `e : M ≃ₗ[ℂ] N` again carries the `V̂`-bracket to the commutator, i.e. yields a
genuine `VHatRep W N`.  This is the engine of the carrier bridge. -/

/-- **Transport of a `V̂`-representation along a `ℂ`-linear iso** `e : M ≃ₗ[ℂ] N`: conjugate each loop
mode, `(transport e ρ) x = e.conj (ρ x)`.  A genuine Lie morphism `V̂ →ₗ⁅ℂ⁆ End ℂ N` because
`LinearEquiv.conj` respects composition and identity (it is a ring iso of `End`). -/
noncomputable def transport (e : M ≃ₗ[ℂ] N) (ρ : VHatRep W M) : VHatRep W N where
  toFun x := e.conj (ρ x)
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [map_smul, RingHom.id_apply]
  map_lie' {x y} := by
    -- `e.conj` is multiplicative and unital, hence carries the commutator to the commutator.
    -- `End` mul is composition, so `conj_comp` gives `e.conj (a*b) = e.conj a * e.conj b`.
    have hmul : ∀ a b : End ℂ M, e.conj (a * b) = e.conj a * e.conj b := by
      intro a b
      rw [Module.End.mul_eq_comp, LinearEquiv.conj_comp, Module.End.mul_eq_comp]
    rw [ρ.map_lie x y, Ring.lie_def, Ring.lie_def, map_sub, hmul, hmul]

@[simp] theorem transport_apply (e : M ≃ₗ[ℂ] N) (ρ : VHatRep W M) (x : VHatCarrier W) :
    transport e ρ x = e.conj (ρ x) := rfl

/-- The transported mode acts by conjugation:
`(transport e ρ).actMode a m y = e (ρ.actMode a m (e⁻¹ y))`. -/
@[simp] theorem transport_actMode_apply (e : M ≃ₗ[ℂ] N) (ρ : VHatRep W M) (a : 𝒱) (m : ℤ) (y : N) :
    (transport e ρ).actMode a m y = e (ρ.actMode a m (e.symm y)) := by
  rw [actMode_def, actMode_def, transport_apply, LinearEquiv.conj_apply_apply]

/-- **The transported representation is `ActModeTruncated`** whenever the source is: truncation is a
property of `e⁻¹ y`, and `e 0 = 0`. -/
theorem transport_truncated (e : M ≃ₗ[ℂ] N) (ρ : VHatRep W M) (htr : ActModeTruncated ρ) :
    ActModeTruncated (transport e ρ) := by
  intro a y
  obtain ⟨Nn, hN⟩ := htr a (e.symm y)
  refine ⟨Nn, fun p hp => ?_⟩
  rw [transport_actMode_apply, hN p hp, map_zero]

/-- **The transported representation satisfies the module Jacobi 5.3.1b** whenever the source does.
Both sides of the Jacobi identity are pushed through the `ℂ`-linear `e`, and the supports of the two
families (controlled by truncation) are finite, so `map_finsum` applies. -/
theorem transport_isModuleJacobi (e : M ≃ₗ[ℂ] N) (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (hjac : ρ.IsModuleJacobi) : (transport e ρ).IsModuleJacobi := by
  intro u v y ℓ m n
  -- pull `y` back along `e`, apply the source Jacobi at `e⁻¹ y`, push forward by `e`.
  set x₀ := e.symm y with hx₀
  have hab := hjac u v x₀ ℓ m n
  -- rewrite both sides of the goal as `e` of the source sides
  have hLHS : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        ((transport e ρ).actMode u (ℓ + m - i) ((transport e ρ).actMode v (n + i) y)
          - negOnePow ℓ • (transport e ρ).actMode v (ℓ + n - i)
              ((transport e ρ).actMode u (m + i) y)))
      = e (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (ρ.actMode u (ℓ + m - i) (ρ.actMode v (n + i) x₀)
            - negOnePow ℓ • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + i) x₀))) := by
    rw [show (e : _ → N) = e.toLinearMap from rfl,
      map_finsum e.toLinearMap (hLHS_fin ρ htr u v x₀ ℓ m n)]
    refine finsum_congr fun i => ?_
    simp only [transport_actMode_apply, LinearEquiv.symm_apply_apply, LinearEquiv.coe_coe,
      map_smul, map_sub, hx₀]
  have hRHS : (∑ᶠ i : ℤ, cbz m i •
        (transport e ρ).actMode (W.smul u (ℓ + i) v) (m + n - i) y)
      = e (∑ᶠ i : ℤ, cbz m i • ρ.actMode (W.smul u (ℓ + i) v) (m + n - i) x₀) := by
    rw [show (e : _ → N) = e.toLinearMap from rfl,
      map_finsum e.toLinearMap (hRHS_fin ρ htr u v x₀ ℓ m n)]
    refine finsum_congr fun i => ?_
    simp only [transport_actMode_apply, LinearEquiv.coe_coe, map_smul, hx₀]
  rw [hLHS, hRHS]
  exact congrArg e hab

end VHatRep

/-! ## The carrier bridge transport — Construction A on the headline carrier `MU W U`

Given a `CarrierBridge W M MUcar YMU` (the DJ Prop 3.4 / 3.5 iso `M̄(U) ≅ MUcar` intertwining the
abstract `actMode` with the headline field `YMU`), we conjugate the genuine defect-quotient engine
`ρ̄ = quotientRep (freeRep W M) …` along `B.equiv`.  This lands the Construction-A representation
**on the headline carrier**, with mode action *exactly* `YMU`. -/

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
  {MUcar : Type u} [AddCommGroup MUcar] [Module ℂ MUcar] {YMU : 𝒱 → ℤ → End ℂ MUcar}

/-- The genuine defect-quotient representation `ρ̄` of the free Construction-A action (abbreviation). -/
noncomputable abbrev defectRep (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M]
    [Module ℂ M] : VHatRep W ((UEnv W ⊗[ℂ] M) ⧸ VHatRep.defectSubmodule (freeRep W M)) :=
  VHatRep.quotientRep (freeRep W M) (VHatRep.defectSubmodule (freeRep W M))
    (VHatRep.defectSubmodule_invariant (freeRep W M))

/-- **The Construction-A representation on the headline carrier `MUcar = MU W U`** — conjugate the
genuine defect-quotient engine `defectRep` along the carrier-bridge iso `B.equiv`.  A genuine
`VHatRep W MUcar`, axiom-free; the only carried content is the bridge `B` itself. -/
noncomputable def transportRep (B : CarrierBridge W M MUcar YMU) : VHatRep W MUcar :=
  VHatRep.transport B.equiv (defectRep W M)

/-- **The transported `𝒱`-mode action is the headline field**:
`(transportRep B).actMode a m = YMU a m`.  This is the bridge's equivariance, read through the
transport (`transport_actMode_apply` + `B.equivariant`). -/
theorem transportRep_actMode (B : CarrierBridge W M MUcar YMU) (a : 𝒱) (m : ℤ) (y : MUcar) :
    (transportRep B).actMode a m y = YMU a m y := by
  rw [transportRep, VHatRep.transport_actMode_apply]
  -- `B.equivariant` (at `e⁻¹ y`) carries `actMode` to `YMU` (`defectRep = quotientRep`).
  have h := B.equivariant a m (B.equiv.symm y)
  rw [B.equiv.apply_symm_apply] at h
  exact h

@[simp] theorem transportRep_actMode_eq (B : CarrierBridge W M MUcar YMU) (a : 𝒱) (m : ℤ) :
    (transportRep B).actMode a m = YMU a m :=
  LinearMap.ext (transportRep_actMode B a m)

/-- **The transported representation is `ActModeTruncated`**, given the carried truncation of the free
representation (the PBW-gated bottom survival).  Transported through `transport_truncated` and
`actMode_quotientRep_truncated`. -/
theorem transportRep_truncated (B : CarrierBridge W M MUcar YMU)
    (htr : VHatRep.ActModeTruncated (freeRep W M)) :
    VHatRep.ActModeTruncated (transportRep B) :=
  VHatRep.transport_truncated B.equiv (defectRep W M)
    (VHatRep.actMode_quotientRep_truncated (freeRep W M) (VHatRep.defectSubmodule (freeRep W M))
      (VHatRep.defectSubmodule_invariant (freeRep W M)) htr)

/-- **The module Jacobi 5.3.1b holds for the transported representation on `MU W U`**, given the
truncation crux.  It is `freeRep_defectQuotient_isModuleJacobi` transported through
`transport_isModuleJacobi`.  No axiom; the only hypotheses are the bridge `B` and truncation. -/
theorem transportRep_isModuleJacobi (B : CarrierBridge W M MUcar YMU)
    (htr : VHatRep.ActModeTruncated (freeRep W M)) :
    (transportRep B).IsModuleJacobi :=
  VHatRep.transport_isModuleJacobi B.equiv (defectRep W M)
    (VHatRep.actMode_quotientRep_truncated (freeRep W M) (VHatRep.defectSubmodule (freeRep W M))
      (VHatRep.defectSubmodule_invariant (freeRep W M)) htr)
    (freeRep_defectQuotient_isModuleJacobi W M htr)

/-- **Vacuum creation (module VA2) for the transported representation**, given the corresponding
datum *on the headline field* `YMU` (the DJ grading datum the bridge does not itself supply).
Since `(transportRep B).actMode = YMU`, the two `VacuumCreation` statements are literally the same. -/
theorem transportRep_vacuum (B : CarrierBridge W M MUcar YMU)
    (hvac : ∀ m : ℤ, YMU W.vacuum m = if m = -1 then (1 : End ℂ MUcar) else 0) :
    VHatRep.VacuumCreation (transportRep B) := by
  intro m
  rw [transportRep_actMode_eq]
  exact hvac m

/-- **The grading scalar `L₀ = h + n` for the transported representation**, given the datum on the
headline field `YMU`.  Since `(transportRep B).actMode = YMU`, the statements coincide. -/
theorem transportRep_L0 {U : AMod W} {h : ℂ} {YMU' : 𝒱 → ℤ → End ℂ (MU W U)}
    (B : CarrierBridge W U.carrier (MU W U) YMU')
    (hL0 : ∀ (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
      YMU' W.conformalVector 1 x = ((h : ℂ) + n) • x)
    (n : ℕ) (x : MU W U) (hx : x ∈ MU.deg W U n) :
    (transportRep B).actMode W.conformalVector 1 x = ((h : ℂ) + n) • x := by
  rw [transportRep_actMode]
  exact hL0 n x hx

end VHat

/-! ## The headline reduction — `CarrierBridge ⟹ buildMUModuleData ⟹ the Zhu bijection`

We now assemble, per bottom `A(𝒱)`-module `U`, the full `MUModuleData W U h` term on the headline
carrier `MU W U`, **through `buildMUModuleData`**, using only:

* the carrier bridge `B` (the DJ Prop 3.4 / 3.5 iso, carried);
* truncation of `freeRep` (the PBW-gated bottom survival, carried);
* vacuum / grading data **on the headline field** `YMU` (the DJ grading data);
* finiteness and bottom-nonvanishing of `MU W U` (siblings).

Everything else — the `V̂`-action, its Lie-morphism property, the module Jacobi — is supplied by the
transported Construction-A engine. -/

namespace VHat

open VHat.VHatRep

-- The transported representation `transportRep` unfolds to the conjugation of the heavy
-- defect-quotient engine; the structural defeq checks below (matching `transportRep`-typed fields)
-- need a larger heartbeat budget.  No `sorry`/axiom/`pbw` — pure elaboration cost.
set_option maxHeartbeats 4000000

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The headline `MUModuleData W U h` term, built from a carrier bridge.**  The `V̂`-representation
on `MU W U` is the transported Construction-A engine `transportRep B`; its mode action is the
headline field `YMU`.  All of `weak` (vacuum/truncation/module-Jacobi 5.3.1b) is supplied by the
transport; the grading scalar, finiteness and bottom-nonvanishing are the named carried data.  No
`sorry`, no axiom, no `pbw`. -/
noncomputable def headline_buildMUModuleData {U : AMod W} {h : ℂ} {YMU : 𝒱 → ℤ → End ℂ (MU W U)}
    (B : CarrierBridge W U.carrier (MU W U) YMU)
    (htr : VHatRep.ActModeTruncated (freeRep W U.carrier))
    (hvac : ∀ m : ℤ, YMU W.vacuum m = if m = -1 then (1 : End ℂ (MU W U)) else 0)
    (hL0 : ∀ (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
      YMU W.conformalVector 1 x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MU.deg W U n))
    (hbot : MU.deg W U 0 ≠ ⊥) :
    MUModuleData W U h :=
  MUModuleData.buildMUModuleData (transportRep B) (transportRep_truncated B htr)
    (transportRep_vacuum B hvac) (transportRep_isModuleJacobi B htr)
    (fun n x hx => transportRep_L0 B hL0 n x hx) hfin hbot

/-- The mode action of the headline-built module data is the headline field `YMU`. -/
@[simp] theorem headline_buildMUModuleData_act {U : AMod W} {h : ℂ}
    {YMU : 𝒱 → ℤ → End ℂ (MU W U)}
    (B : CarrierBridge W U.carrier (MU W U) YMU)
    (htr : VHatRep.ActModeTruncated (freeRep W U.carrier))
    (hvac : ∀ m : ℤ, YMU W.vacuum m = if m = -1 then (1 : End ℂ (MU W U)) else 0)
    (hL0 : ∀ (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
      YMU W.conformalVector 1 x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MU.deg W U n))
    (hbot : MU.deg W U 0 ≠ ⊥) (a : 𝒱) (m : ℤ) (x : MU W U) :
    (headline_buildMUModuleData B htr hvac hL0 hfin hbot).weak.act a m x = YMU a m x := by
  rw [headline_buildMUModuleData, MUModuleData.buildMUModuleData_act, transportRep_actMode]

/-! ### The per-`U` family input to `MURepFamily` from a family of carrier bridges -/

/-- **A per-`U` family of carrier-bridge data** — the carried Dong–Jiang identification for every
bottom module, together with the named grading/finiteness data.  This is exactly the input the
headline `MURepFamily` consumes, packaged through the bridge transport. -/
structure CarrierBridgeFamily (W : VertexOperatorAlgebra 𝒱) where
  /-- The lowest weight of `M(U)`. -/
  hU : AMod W → ℂ
  /-- The headline field on each carrier `MU W U`. -/
  YMU : ∀ U : AMod W, 𝒱 → ℤ → End ℂ (MU W U)
  /-- The Dong–Jiang carrier bridge `M̄(U) ≅ MU W U` for each bottom (DJ Prop 3.4/3.5). -/
  bridge : ∀ U : AMod W, CarrierBridge W U.carrier (MU W U) (YMU U)
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

namespace CarrierBridgeFamily

variable (F : CarrierBridgeFamily W)

/-- **The headline `MURepFamily` produced by a family of carrier bridges.**  Each per-`U`
`VHatRep W (MU W U)` is the transported Construction-A engine; the module data fields are the
transported truncation / vacuum / module-Jacobi plus the carried grading data.  This is the genuine
`V̂`-representation family on the headline carriers `MU W U` — the linchpin output. -/
noncomputable def toMURepFamily : InducedAssignment.MURepFamily W where
  hU := F.hU
  rho := fun U => transportRep (F.bridge U)
  htr := fun U => transportRep_truncated (F.bridge U) (F.htr U)
  hvac := fun U => transportRep_vacuum (F.bridge U) (F.hvac U)
  hjac := fun U => transportRep_isModuleJacobi (F.bridge U) (F.htr U)
  hL0 := fun U n x hx => transportRep_L0 (F.bridge U) (F.hL0 U) n x hx
  hfin := F.hfin
  hbot := F.hbot

@[simp] theorem toMURepFamily_rho (U : AMod W) :
    F.toMURepFamily.rho U = transportRep (F.bridge U) := rfl

@[simp] theorem toMURepFamily_hU : F.toMURepFamily.hU = F.hU := rfl

end CarrierBridgeFamily

end VHat

/-- **Main connection — the Zhu bijection from a family of carrier bridges.**

The linchpin assembled end-to-end: from a `CarrierBridgeFamily W` (the Dong–Jiang Prop 3.4/3.5
identifications `M̄(U) ≅ MU W U` for every bottom, plus the named grading data), the transported
Construction-A engine gives the headline `MURepFamily W` on the carriers `MU W U`; together with the
per-`U` maximal-`J` data, the realization isos, `M(·)`-functoriality, the irreducibility scope, and
the bottom-generation family, the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)` is a **bijection**.

The headline `MUModuleData` is produced entirely by `buildMUModuleData` over the transported engine,
so the carrier-bridge iso discharges the carrier identification (the `anmGen`/`OnmFull` descent) that
the bijection's `MUModuleData.weak` Jacobi requires — **no `sorry`, no axiom, no `pbw`**. -/
theorem headline_zhuBijection_of_bridge {W : VertexOperatorAlgebra 𝒱}
    (F : VHat.CarrierBridgeFamily W)
    (ludata : ∀ U : AMod W, MUModuleData.LUData (F.toMURepFamily.mudata U))
    (realizes : ∀ U : AMod W,
      AModEquiv W ((F.toMURepFamily.toLUFamily ludata).K U).toAMod U)
    (Dfun : InducedAssignment.MUFunctorialData (F.toMURepFamily.toLUFamily ludata))
    (hall : InducedAssignment.AllLWIrreducible W)
    (G : InducedAssignment.GenFromBottomFinalFamily (F.toMURepFamily.toLUFamily ludata)) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_repFamily F.toMURepFamily ludata realizes Dfun hall G

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
