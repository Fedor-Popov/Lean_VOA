/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUjacobiClose
import VOA.Modules.ZhuVermaAnArchAnmFull
import Mathlib.Algebra.Algebra.Bilinear

/-!
# A GENUINE `V̂`-representation on the induced carrier — the `ρ` input of Construction A

This file proves the **carrier-action engine** of the lifting half of Zhu Theorem 5.3.4: a genuine
`V̂`-representation (`VHat.VHatRep`) on the *free / induced* carrier, whose defect quotient
(`VHat.VHatRep.isModuleJacobi_quotientRep`) is `M̄(U)`.  This is the `ρ` field that
`VHatModeData`/`MUModuleData` consume; it is built **axiom-free, with no carried hypothesis at the
operator level** (the genuine well-definedness of the `V̂`-action), reducing the remaining content of
`M(U)` to precisely (i) the truncation/field property `ActModeTruncated` (the PBW-gated bottom
survival, route-independent) and (ii) the `anmGen`/`OnmFull` carrier identification.

## The strategy — path (a): the left-regular / free `V̂`-module

`ZhuVermaAnArchVhat` proves `V̂ = VLoop 𝒱 ⧸ Im D` is a complete `ℂ`-Lie algebra
(`VHat.lieRing`/`VHat.lieAlgebra`, the three Frenkel–Zhu obligations are theorems), and
`ZhuVermaAnArchMUVhat` forms its universal enveloping algebra `UEnv W = U(V̂)` with the canonical Lie
morphism `uι W : V̂ →ₗ⁅ℂ⁆ U(V̂)`.  The cleanest **genuine** `V̂`-representation is then the
**left-regular representation** of `V̂` on its own enveloping algebra `U(V̂)`:

  `leftReg W := (Algebra.lmul ℂ (U(V̂)) : U(V̂) →ₗ⁅ℂ⁆ End ℂ (U(V̂))).comp (uι W)`,

a genuine Lie morphism `V̂ →ₗ⁅ℂ⁆ End ℂ (U(V̂))` — `Algebra.lmul` is a `ℂ`-algebra morphism (so its
underlying `LieHom` carries commutators to commutators: `L_{xy} = L_x ∘ L_y`), and `uι` is a Lie
morphism, so the composite is a Lie morphism.  No carried hypothesis, no axiom: the genuine
`V̂`-action exists.  Its `𝒱`-mode action is `a₍ₘ₎ = L_{a(m)}` (left multiplication by the loop mode),
which obeys the free `ℓ = 0` Borcherds commutator `VHat.VHatRep.actMode_bracket` automatically.

The **induced module** `M(U) = U(V̂) ⊗_{U(P)} U` is realized inside this engine: for an
`A₀(𝒱) = A(𝒱)`-module (more generally any `ℂ`-space) `U`, the **free** `V̂`-action on `U(V̂) ⊗ U`
acts through `leftReg` on the first factor and the identity on `U` (`freeRep`).  Both are genuine
`VHatRep`s, axiom-clean.  The genuine module `M̄(U)` is the **defect quotient** of `freeRep` (Frenkel–
Zhu / Dong–Jiang generalized Verma construction), on which `IsModuleJacobi` 5.3.1b holds **by
construction** via the already-proven `isModuleJacobi_quotientRep` — provided the truncation property
`ActModeTruncated` (which we carry, since it is exactly the PBW-gated bottom survival, the one genuine
route-independent crux).

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `VHat.leftReg W : VHatRep W (UEnv W)` — the left-regular `V̂`-representation on `U(V̂)`, a genuine
  Lie morphism (`leftReg_apply`, `leftReg_actMode`: `a₍ₘ₎ = L_{a(m)}`; `leftReg_actMode_bracket`).
* `VHat.freeRep W M : VHatRep W (UEnv W ⊗[ℂ] M)` for any `ℂ`-space `M` — the free / induced
  `V̂`-action (left-regular on `U(V̂)`, identity on `M`), a genuine Lie morphism
  (`freeRep_actMode_tmul`: `a₍ₘ₎ (e ⊗ x) = (a(m)·e) ⊗ x`; `freeRep_actMode_bracket`).
* `VHat.freeRep_defectQuotient_isModuleJacobi` — `IsModuleJacobi` 5.3.1b holds on the defect quotient
  `M̄(U)` of `freeRep`, **given** the carried truncation `ActModeTruncated (freeRep W M)` (the genuine
  bottom-survival crux).  This discharges the headline `MUModuleData.weak`'s Jacobi field on the
  genuine induced carrier.
* `VHat.CarrierBridge` — the precise (and *only*) carried identification connecting this engine's
  defect quotient to the headline carrier `MU W U = ⊕ₙ A_{n,0}(𝒱) ⊗ U`: a `𝒱`-mode-equivariant
  `ℂ`-linear isomorphism (the `anmGen`/`OnmFull` descent, DJ Prop 3.4 / 3.5).  This is the residue
  membership content, carried as an explicit hypothesis, never an axiom.

The OPERATOR core (the existence of the genuine `V̂`-action) is a **theorem with no hypothesis**.
The two remaining inputs are isolated and named: truncation (PBW / bottom survival) and the carrier
bridge (`anmGen`/`OnmFull`).

## References
DLM3 §4; H. Li `hep-th/9406211` §2; Frenkel–Zhu; Dong–Jiang `math/0601626` §2–3; Gannon §5.3.2,
Thm 5.3.4; `ZhuVermaAnArchMUVhat` (`UEnv`, `uι`, `umode`, `VHatRep`, `actMode`, `actMode_bracket`),
`ZhuVermaAnArchMUjacobiClose` (`quotientRep`, `defectSubmodule`, `isModuleJacobi_quotientRep`,
`ActModeTruncated`), `ZhuVermaAnArchAnmFull` (`anmGen`, `OnmFull`, `AnmFull`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The left-regular `V̂`-representation on `U(V̂)`

`Algebra.lmul ℂ (UEnv W)` is the `ℂ`-algebra morphism `U(V̂) →ₐ[ℂ] End ℂ (U(V̂))` of left
multiplication (`L_a b = a * b`).  As an `AlgHom` it is, in particular, a `LieHom`
(`LieAlgebra.ofAssociativeAlgebraHom`-style coercion: `L_{xy} = L_x ∘ L_y` carries commutators to
commutators).  Composing with the canonical Lie morphism `uι W : V̂ →ₗ⁅ℂ⁆ U(V̂)` gives the genuine
left-regular `V̂`-representation. -/

/-- **The left-regular `V̂`-representation on `U(V̂)`** — a genuine Lie morphism
`V̂ →ₗ⁅ℂ⁆ End ℂ (U(V̂))`: the loop mode `a(m)` acts by left multiplication by `uι (a(m))` in the
enveloping algebra.  Axiom-free, no carried hypothesis: the genuine `V̂`-action exists. -/
noncomputable def leftReg (W : VertexOperatorAlgebra 𝒱) : VHat.VHatRep W (UEnv W) :=
  (Algebra.lmul ℂ (UEnv W) : UEnv W →ₗ⁅ℂ⁆ End ℂ (UEnv W)).comp (uι W)

@[simp] theorem leftReg_apply (W : VertexOperatorAlgebra 𝒱) (x : VHatCarrier W) (e : UEnv W) :
    leftReg W x e = (uι W x) * e := rfl

/-- The `𝒱`-mode action of the left-regular representation: `a₍ₘ₎ = L_{a(m)}` (left multiplication
by the loop mode `umode W a m = uι (gen W a m)`). -/
@[simp] theorem leftReg_actMode (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) (e : UEnv W) :
    (leftReg W).actMode a m e = (umode W a m) * e := by
  rw [VHatRep.actMode_def, leftReg_apply, umode_def]

/-- **The free `ℓ = 0` Borcherds commutator law** for the left-regular representation (automatic,
since `leftReg` is a genuine Lie morphism):
`⁅a₍ₘ₎, b₍ₖ₎⁆ = ∑ᶠ i, gBinom m i • (a₍ᵢ₎b)₍ₘ₊ₖ₋ᵢ₎`. -/
theorem leftReg_actMode_bracket (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (m k : ℤ) :
    ⁅(leftReg W).actMode a m, (leftReg W).actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) • (leftReg W).actMode (W.smul a i b) (m + k - i) :=
  (leftReg W).actMode_bracket a b m k

/-! ## The free / induced `V̂`-representation on `U(V̂) ⊗ M`

For any `ℂ`-space `M`, `V̂` acts on `U(V̂) ⊗[ℂ] M` through the left-regular representation on the first
factor and the identity on the second.  `TensorProduct.map (leftReg W x) LinearMap.id` is the
endomorphism; `x ↦ that` is a Lie morphism because `TensorProduct.map (· ) id` is an algebra
morphism `End ℂ (U(V̂)) →ₐ End ℂ (U(V̂) ⊗ M)` (it respects composition and identity), so it carries
commutators to commutators and `leftReg` already carries the `V̂` bracket to the commutator. -/

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The endomorphism `e ↦ e ⊗ id` on `End ℂ (U(V̂))`, packaged as the underlying linear map of the
free action of a fixed `x : V̂`. -/
noncomputable def freeEnd (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M] [Module ℂ M]
    (x : VHatCarrier W) : End ℂ (UEnv W ⊗[ℂ] M) :=
  TensorProduct.map (leftReg W x) LinearMap.id

@[simp] theorem freeEnd_tmul (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M]
    [Module ℂ M] (x : VHatCarrier W) (e : UEnv W) (y : M) :
    freeEnd W M x (e ⊗ₜ[ℂ] y) = (leftReg W x e) ⊗ₜ[ℂ] y := by
  rw [freeEnd, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

/-- **The free / induced `V̂`-representation on `U(V̂) ⊗ M`** — a genuine Lie morphism
`V̂ →ₗ⁅ℂ⁆ End ℂ (U(V̂) ⊗ M)`.  `V̂` acts through `leftReg` on the first tensor factor, identity on
`M`.  For `M = U` an `A(𝒱)`-module, this is the free cover of the generalized Verma module `M(U)`;
its defect quotient is `M̄(U)`.  Axiom-free, no carried hypothesis at the operator level. -/
noncomputable def freeRep (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M] [Module ℂ M] :
    VHat.VHatRep W (UEnv W ⊗[ℂ] M) where
  toFun := freeEnd W M
  map_add' x y := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul e z =>
      simp only [freeEnd_tmul, LinearMap.add_apply, map_add, TensorProduct.add_tmul]
    | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply, h₁, h₂]
  map_smul' c x := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul e z =>
      simp only [freeEnd_tmul, LinearMap.smul_apply, map_smul, RingHom.id_apply,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, LinearMap.smul_apply, h₁, h₂]
  map_lie' {x y} := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul e z =>
      -- `freeEnd` of a bracket = bracket of `freeEnd`s, since `leftReg` is a Lie morphism and
      -- `· ⊗ id` respects composition.
      rw [freeEnd_tmul, (leftReg W).map_lie x y]
      rw [Ring.lie_def, Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
        Module.End.mul_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        freeEnd_tmul, freeEnd_tmul, freeEnd_tmul, freeEnd_tmul, ← TensorProduct.sub_tmul]
    | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂]

@[simp] theorem freeRep_apply (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M]
    [Module ℂ M] (x : VHatCarrier W) :
    freeRep W M x = freeEnd W M x := rfl

/-- The free `𝒱`-mode action on a pure tensor: `a₍ₘ₎ (e ⊗ x) = (a(m)·e) ⊗ x`. -/
@[simp] theorem freeRep_actMode_tmul (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M]
    [Module ℂ M] (a : 𝒱) (m : ℤ) (e : UEnv W) (y : M) :
    (freeRep W M).actMode a m (e ⊗ₜ[ℂ] y) = ((umode W a m) * e) ⊗ₜ[ℂ] y := by
  rw [VHatRep.actMode_def, freeRep_apply, freeEnd_tmul, leftReg_apply, umode_def]

/-- **The free `ℓ = 0` Borcherds commutator law** for the free representation (automatic). -/
theorem freeRep_actMode_bracket (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M]
    [Module ℂ M] (a b : 𝒱) (m k : ℤ) :
    ⁅(freeRep W M).actMode a m, (freeRep W M).actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) • (freeRep W M).actMode (W.smul a i b) (m + k - i) :=
  (freeRep W M).actMode_bracket a b m k

/-! ## The defect quotient `M̄(U)` and the module Jacobi 5.3.1b

The genuine module is the defect quotient `M̄(U) = (U(V̂) ⊗ U) ⧸ defectSubmodule (freeRep W U)`,
the Frenkel–Zhu / Dong–Jiang generalized Verma module.  `isModuleJacobi_quotientRep` (already
proven, `ZhuVermaAnArchMUjacobiClose`) gives `IsModuleJacobi` 5.3.1b on it, **given** the truncation
`ActModeTruncated (freeRep W U)`.  Truncation is precisely the PBW-gated bottom-survival property, the
single genuine route-independent crux; we carry it as an explicit hypothesis. -/

/-- **`IsModuleJacobi` 5.3.1b holds on the defect quotient `M̄(U)` of the free representation**, given
the truncation/field property of `freeRep W M` (the PBW-gated bottom survival, carried).  This is the
headline `WeakModule.jacobi` content of `MUModuleData.weak`, realized on the genuine induced carrier
via the already-proven `isModuleJacobi_quotientRep`.  No axiom; the only hypothesis is truncation. -/
theorem freeRep_defectQuotient_isModuleJacobi (W : VertexOperatorAlgebra 𝒱) (M : Type u)
    [AddCommGroup M] [Module ℂ M] (htr : VHatRep.ActModeTruncated (freeRep W M)) :
    (VHatRep.quotientRep (freeRep W M) (VHatRep.defectSubmodule (freeRep W M))
        (VHatRep.defectSubmodule_invariant (freeRep W M))).IsModuleJacobi :=
  VHatRep.isModuleJacobi_quotientRep (freeRep W M) htr

/-! ## The carrier bridge — the only remaining identification (`anmGen`/`OnmFull` descent)

The genuine module data `MUModuleData W U h` lives on the carrier `MU W U = ⊕ₙ A_{n,0}(𝒱) ⊗ U`.  The
defect quotient `M̄(U)` constructed above is the *same* `𝒱`-module abstractly (Dong–Jiang Prop 3.4 /
3.5: the bimodule composition through `anmGen`/`OnmFull` identifies the layers).  The connection is a
`𝒱`-mode-equivariant `ℂ`-linear isomorphism between the two carriers.  We record it as the precise
carried datum — the genuine residue-membership content (`anmGen`, `OnmFull`), carried as a hypothesis,
never an axiom. -/

/-- **The carrier bridge** between the abstract defect quotient `M̄(U)` (built here from `freeRep`) and
the headline carrier `MU W U = ⊕ₙ A_{n,0}(𝒱) ⊗ U`.  A `ℂ`-linear isomorphism that intertwines the
`𝒱`-mode actions (`actMode` on the defect quotient `↦ Y_{M(U)}` on `MU W U`).  This is exactly the
Dong–Jiang Prop 3.4 / 3.5 identification through the general product `anmGen` and the full ideal
`OnmFull` — the residue-membership descent — carried as an explicit hypothesis. -/
structure CarrierBridge (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M] [Module ℂ M]
    (MUcar : Type u) [AddCommGroup MUcar] [Module ℂ MUcar]
    (YMU : 𝒱 → ℤ → End ℂ MUcar) where
  /-- The `ℂ`-linear isomorphism of carriers. -/
  equiv :
    ((UEnv W ⊗[ℂ] M) ⧸ VHatRep.defectSubmodule (freeRep W M)) ≃ₗ[ℂ] MUcar
  /-- `𝒱`-mode equivariance: the abstract `actMode` on `M̄(U)` is carried to the headline field
  `Y_{M(U)}(a, ·) = a₍ₘ₎` on `MU W U` (`anmGen`/`OnmFull` descent, DJ Prop 3.4/3.5). -/
  equivariant : ∀ (a : 𝒱) (m : ℤ) (x : (UEnv W ⊗[ℂ] M) ⧸ VHatRep.defectSubmodule (freeRep W M)),
    equiv ((VHatRep.quotientRep (freeRep W M) (VHatRep.defectSubmodule (freeRep W M))
        (VHatRep.defectSubmodule_invariant (freeRep W M))).actMode a m x)
      = YMU a m (equiv x)

/-- Finiteness of the combined LHS family of the abstract module Jacobi (given truncation): its
support sits inside the union of the `MPuv`/`MPvu` supports. -/
theorem hLHS_fin {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
    (ρ : VHat.VHatRep W M) (htr : VHatRep.ActModeTruncated ρ) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
        (ρ.actMode u (ℓ + m - i) (ρ.actMode v (n + i) x)
          - negOnePow ℓ • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + i) x))).Finite := by
  refine ((VHatRep.MPuv_fin ρ htr u v x ℓ m n).union
    (VHatRep.MPvu_fin ρ htr u v x ℓ m n)).subset ?_
  intro i hi
  rw [Function.mem_support] at hi
  by_contra hc
  rw [Set.mem_union, not_or, Function.mem_support, not_not, Function.mem_support, not_not] at hc
  apply hi
  rw [smul_sub, hc.1, smul_comm, hc.2, smul_zero, sub_zero]

/-- Finiteness of the abstract module-Jacobi RHS family (`MBR`). -/
theorem hRHS_fin {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
    (ρ : VHat.VHatRep W M) (_htr : VHatRep.ActModeTruncated ρ) (u v : 𝒱) (x : M) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ =>
      cbz m i • ρ.actMode (W.smul u (ℓ + i) v) (m + n - i) x).Finite :=
  VHatRep.MBR_fin ρ u v x ℓ m n

/-- **The headline reduction.**  Given the truncation crux and the carrier bridge, the genuine
module Jacobi 5.3.1b holds for the headline field `YMU` on the headline carrier `MU W U`: it is the
defect-quotient Jacobi `freeRep_defectQuotient_isModuleJacobi` transported along the bridge.  The
abstract `IsModuleJacobi` is the verbatim `WeakModule.jacobi` shape, so this is exactly the
`MUModuleData.weak` Jacobi content, modulo the two named carried inputs (truncation; `anmGen`/
`OnmFull` bridge) — **no axiom, no `sorry`, no `pbw`**. -/
theorem headline_isModuleJacobi_transported (W : VertexOperatorAlgebra 𝒱) (M : Type u)
    [AddCommGroup M] [Module ℂ M]
    {MUcar : Type u} [AddCommGroup MUcar] [Module ℂ MUcar] {YMU : 𝒱 → ℤ → End ℂ MUcar}
    (htr : VHatRep.ActModeTruncated (freeRep W M))
    (B : CarrierBridge W M MUcar YMU) :
    ∀ (u v : 𝒱) (x : MUcar) (ℓ m n : ℤ),
      (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (YMU u (ℓ + m - i) (YMU v (n + i) x)
            - negOnePow ℓ • YMU v (ℓ + n - i) (YMU u (m + i) x)))
        = ∑ᶠ i : ℤ, cbz m i • YMU (W.smul u (ℓ + i) v) (m + n - i) x := by
  -- abbreviations for the defect quotient and its representation
  let rho := VHatRep.quotientRep (freeRep W M) (VHatRep.defectSubmodule (freeRep W M))
      (VHatRep.defectSubmodule_invariant (freeRep W M))
  have hjac : rho.IsModuleJacobi := freeRep_defectQuotient_isModuleJacobi W M htr
  have htr_rho : rho.ActModeTruncated :=
    VHatRep.actMode_quotientRep_truncated (freeRep W M) (VHatRep.defectSubmodule (freeRep W M))
      (VHatRep.defectSubmodule_invariant (freeRep W M)) htr
  intro u v x ℓ m n
  -- pull `x` back along the equiv, apply abstract Jacobi, push forward by equivariance
  obtain ⟨x₀, rfl⟩ := B.equiv.surjective x
  -- the abstract identity at `x₀`
  have hab := hjac u v x₀ ℓ m n
  -- transport: `YMU a p (equiv y) = equiv (rho.actMode a p y)` (equivariance, reversed)
  have hev : ∀ (a : 𝒱) (p : ℤ)
      (y : (UEnv W ⊗[ℂ] M) ⧸ VHatRep.defectSubmodule (freeRep W M)),
      YMU a p (B.equiv y) = B.equiv (rho.actMode a p y) := fun a p y => (B.equivariant a p y).symm
  -- rewrite both sides of the goal into `equiv` of the abstract sides
  -- LHS
  have hLHS : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (YMU u (ℓ + m - i) (YMU v (n + i) (B.equiv x₀))
          - negOnePow ℓ • YMU v (ℓ + n - i) (YMU u (m + i) (B.equiv x₀))))
      = B.equiv (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (rho.actMode u (ℓ + m - i) (rho.actMode v (n + i) x₀)
            - negOnePow ℓ • rho.actMode v (ℓ + n - i) (rho.actMode u (m + i) x₀))) := by
    rw [show (B.equiv : _ → MUcar) = B.equiv.toLinearMap from rfl,
      map_finsum B.equiv.toLinearMap (hLHS_fin rho htr_rho u v x₀ ℓ m n)]
    refine finsum_congr fun i => ?_
    simp only [hev, LinearEquiv.coe_coe, map_smul, map_sub]
  -- RHS
  have hRHS : (∑ᶠ i : ℤ, cbz m i • YMU (W.smul u (ℓ + i) v) (m + n - i) (B.equiv x₀))
      = B.equiv (∑ᶠ i : ℤ, cbz m i • rho.actMode (W.smul u (ℓ + i) v) (m + n - i) x₀) := by
    rw [show (B.equiv : _ → MUcar) = B.equiv.toLinearMap from rfl,
      map_finsum B.equiv.toLinearMap (hRHS_fin rho htr_rho u v x₀ ℓ m n)]
    refine finsum_congr fun i => ?_
    simp only [hev, LinearEquiv.coe_coe, map_smul]
  rw [hLHS, hRHS]
  exact congrArg B.equiv hab

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
