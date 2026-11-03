/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import VOA.Modules.ZhuVermaAnArchVhatJac3
import VOA.Modules.ZhuBijection

/-!
# Construction A for `M(U)` — the universal enveloping algebra `U(V̂)` route

The hard direction `U ↦ M(U)` of Zhu's Theorem 5.3.4 (Gannon §5.3.2; Frenkel–Zhu; Dong–Li–Mason
*Twisted representations of VOAs* §4) builds the lowest-weight `𝒱`-module realizing an
`A(𝒱)`-module `U` as a **generalized Verma module** for the loop Lie algebra `V̂`:

`M(U) = U(V̂) ⊗_{U(P)} U`,

where `V̂ = (𝒱 ⊗ ℂ[t,t⁻¹]) / Im D` is the (centreless) Frenkel–Zhu loop Lie algebra, `P ⊆ V̂` the
parabolic of non-negative degrees, `U(·)` the universal enveloping algebra, and `U` is pulled back
along the surjection `P → A₀(𝒱)`.

Crucially **`V̂` is already a complete `ℂ`-Lie algebra in this project** (`VHat.lieRing` /
`VHat.lieAlgebra`, file `ZhuVermaAnArchVhatJac3`; the three Frenkel–Zhu obligations
`bracketDescends`/`vhatAntisymm`/`vhatLeibniz_holds` are all proved theorems). So Mathlib's
`UniversalEnvelopingAlgebra` applies *directly* to `VHat.lieRing W`, and the whole associative
machinery of `U(V̂)` becomes available axiom-free.

This file proves the **foundation of Construction A on top of that Lie algebra**:

* **`UEnv W := UniversalEnvelopingAlgebra ℂ (VHatCarrier W)`** — the associative enveloping algebra
  of `V̂`, a genuine `ℂ`-algebra (Mathlib instance, no axiom).
* **`uι W : V̂ →ₗ⁅ℂ⁆ U(V̂)`** — the canonical Lie morphism; **`umode W a m := uι (gen a m)`** — the
  loop mode `a(m)` realized as an element of the associative algebra `U(V̂)`.
* **`umode_bracket`** — the Borcherds commutator relation *inside* `U(V̂)`:
  `⁅a(m), b(k)⁆ = uι ⁅gen a m, gen b k⁆ = Σᶠ i, gBinom m i • (a₍ᵢ₎b)(m+k-i)` (the singular OPE, now
  an honest commutator of associative-algebra elements — `umode_commutator`).
* **`VHatRep W M`** — a `V̂`-representation on a `ℂ`-space `M` (a Lie morphism `V̂ →ₗ⁅ℂ⁆ End ℂ M`),
  and **`VHatRep.toAlgHom : U(V̂) →ₐ[ℂ] End ℂ M`** — the universal property of `U(V̂)` turning a
  `V̂`-module into a genuine `U(V̂)`-module (this is *exactly* the engine that builds the action of
  `M(U)`: the modes `a₍ₙ₎` act through `umode`).
* **`VHatRep.actMode`** / **`VHatRep.actMode_bracket`** — the `𝒱`-mode action `a₍ₘ₎ := ρ(a(m))` of a
  representation, and its honest commutator law (the `ℓ = 0` Borcherds slice — locality), pushed
  through `ρ` from `umode_commutator`.

What remains for a full `M(U)` (the `U(P)`-relative tensor product carrier, the field
`Y_{M(U)}(u,z) = Σ u₍ₙ₎ z^{-n-1}` packaged as a `WeakModule.YM`, the bounded-below `ℂ`-grading, and
the **module Jacobi 5.3.1b**) is recorded at the end as the single precise crux
`VHatRep.IsModuleJacobi` — the genuine remaining theorem (it is *not* a free consequence of `V̂`
being a Lie algebra: the `ℓ ≠ 0` Borcherds terms — the iterate `(a₍ᵢ₎b)` products — are extra
content). Everything proved here is `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 §4; H. Li hep-th/9406211 §2; Frenkel–Zhu; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The universal enveloping algebra `U(V̂)`

`V̂` already carries `VHat.lieRing`/`VHat.lieAlgebra` (the three Frenkel–Zhu obligations are proved
theorems). We attach those instances locally and form Mathlib's `UniversalEnvelopingAlgebra`. -/

/-- The active `LieRing` instance on `V̂` (the proved Frenkel–Zhu Lie ring). -/
noncomputable scoped instance instLieRingVHat (W : VertexOperatorAlgebra 𝒱) :
    LieRing (VHatCarrier W) :=
  VHat.lieRing W

/-- The active `LieAlgebra ℂ` instance on `V̂`. -/
noncomputable scoped instance instLieAlgebraVHat (W : VertexOperatorAlgebra 𝒱) :
    LieAlgebra ℂ (VHatCarrier W) :=
  VHat.lieAlgebra W

/-- The bracket on `V̂` is the descended Borcherds loop bracket. -/
theorem bracket_eq (W : VertexOperatorAlgebra 𝒱) (x y : VHatCarrier W) :
    ⁅x, y⁆ = vhatBracket W (bracketDescends W) x y := rfl

/-- **The universal enveloping algebra `U(V̂)`** of the Frenkel–Zhu loop Lie algebra `V̂` — a
genuine associative `ℂ`-algebra (Mathlib `UniversalEnvelopingAlgebra`, axiom-free). This is the
ambient algebra of Construction A: `M(U)` will be a `U(V̂)`-module. -/
abbrev UEnv (W : VertexOperatorAlgebra 𝒱) : Type u :=
  UniversalEnvelopingAlgebra ℂ (VHatCarrier W)

/-- The canonical Lie morphism `V̂ →ₗ⁅ℂ⁆ U(V̂)` (Mathlib `UniversalEnvelopingAlgebra.ι`). -/
noncomputable def uι (W : VertexOperatorAlgebra 𝒱) :
    VHatCarrier W →ₗ⁅ℂ⁆ UEnv W :=
  UniversalEnvelopingAlgebra.ι ℂ

/-- **The loop mode `a(m)` as an element of `U(V̂)`** — `umode W a m = uι (gen a m)`. These are the
generators of the associative algebra of Construction A; the `𝒱`-modes `a₍ₘ₎` of any module act by
the image of these under the module structure map. -/
noncomputable def umode (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) : UEnv W :=
  uι W (gen W a m)

@[simp] theorem umode_def (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) :
    umode W a m = uι W (gen W a m) := rfl

theorem umode_add_left (W : VertexOperatorAlgebra 𝒱) (a a' : 𝒱) (m : ℤ) :
    umode W (a + a') m = umode W a m + umode W a' m := by
  simp only [umode, gen_add_left, map_add]

theorem umode_smul_left (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (a : 𝒱) (m : ℤ) :
    umode W (c • a) m = c • umode W a m := by
  simp only [umode, gen_smul_left, map_smul]

theorem umode_zero_left (W : VertexOperatorAlgebra 𝒱) (m : ℤ) :
    umode W (0 : 𝒱) m = 0 := by
  simp only [umode, gen_zero_left, map_zero]

/-- **The Borcherds commutator inside `U(V̂)`** (DLM3 §4): the Lie morphism `uι` carries the loop
bracket to the algebra commutator, so the loop modes obey the singular OPE as a genuine commutator
of associative-algebra elements:
`⁅a(m), b(k)⁆ = uι ⁅gen a m, gen b k⁆`. -/
theorem umode_bracket (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (m k : ℤ) :
    ⁅umode W a m, umode W b k⁆ = uι W ⁅gen W a m, gen W b k⁆ := by
  simp only [umode]
  exact ((uι W).map_lie (gen W a m) (gen W b k)).symm

/-- **The Borcherds commutator formula in `U(V̂)`** in fully expanded OPE form: the commutator of
loop modes is the (finite) singular OPE sum
`⁅a(m), b(k)⁆ = Σᶠ i, gBinom m i • (a₍ᵢ₎b)(m+k-i)`. This is the Frenkel–Zhu commutator 5.1.7c at the
associative level — the engine of all the mode commutation relations the module action must satisfy
(the `ℓ = 0` Borcherds slice). -/
theorem umode_commutator (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (m k : ℤ) :
    ⁅umode W a m, umode W b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) • umode W (W.smul a i b) (m + k - i) := by
  rw [umode_bracket, bracket_eq, vhatBracket_gen W (bracketDescends W) a b m k]
  -- push the linear map underlying `uι` through the finsum (finite support by VOA regularity)
  have hfin : (Function.support fun i : ℕ =>
      (gBinom m i) • gen W (W.smul a i b) (m + k - i)).Finite := by
    obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
    refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    refine hi ?_
    rw [hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), gen_zero_left, smul_zero]
  have hcoe : ∀ x : VHatCarrier W, uι W x = (uι W).toLinearMap x := fun _ => rfl
  rw [hcoe, map_finsum _ hfin]
  refine finsum_congr fun i => ?_
  rw [map_smul]
  rfl

/-! ## `V̂`-representations and the `U(V̂)`-module bridge (the engine of `M(U)`)

A `V̂`-module is a Lie morphism `ρ : V̂ →ₗ⁅ℂ⁆ End ℂ M`. By the universal property of `U(V̂)`
(`UniversalEnvelopingAlgebra.lift`) it extends *uniquely* to an associative algebra morphism
`U(V̂) →ₐ[ℂ] End ℂ M`, i.e. a genuine `U(V̂)`-module structure. The `𝒱`-modes act by
`a₍ₘ₎ := ρ(a(m))`, and the Borcherds commutator `umode_commutator` is pushed through `ρ` to give the
mode-commutation (locality / `ℓ = 0` Borcherds) law on `M`. This is precisely the action machinery
the induced module `M(U)` runs on. -/

/-- A **`V̂`-representation on `M`**: a Lie-algebra morphism `V̂ →ₗ⁅ℂ⁆ End ℂ M` (DLM3 §4). Equivalently
a `U(V̂)`-module; the `𝒱`-modes act through `actMode`. -/
abbrev VHatRep (W : VertexOperatorAlgebra 𝒱) (M : Type u) [AddCommGroup M] [Module ℂ M] : Type u :=
  VHatCarrier W →ₗ⁅ℂ⁆ Module.End ℂ M

namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The `U(V̂)`-module structure of a representation** — the universal property of `U(V̂)`:
`ρ : V̂ →ₗ⁅ℂ⁆ End ℂ M` lifts to a *unique* algebra morphism `U(V̂) →ₐ[ℂ] End ℂ M`
(`UniversalEnvelopingAlgebra.lift`). This is the bridge that turns a `V̂`-module into a genuine
`U(V̂)`-module, the carrier-action engine of `M(U)`. -/
noncomputable def toAlgHom (ρ : VHatRep W M) : UEnv W →ₐ[ℂ] Module.End ℂ M :=
  UniversalEnvelopingAlgebra.lift ℂ ρ

/-- The lifted algebra morphism agrees with `ρ` on the canonical generators `uι x`. -/
@[simp] theorem toAlgHom_uι (ρ : VHatRep W M) (x : VHatCarrier W) :
    ρ.toAlgHom (uι W x) = ρ x := by
  simp only [toAlgHom, uι]
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℂ ρ x

/-- **The `𝒱`-mode action** of a `V̂`-representation: `a₍ₘ₎ := ρ(a(m))`, an endomorphism of `M`. -/
noncomputable def actMode (ρ : VHatRep W M) (a : 𝒱) (m : ℤ) : Module.End ℂ M :=
  ρ (gen W a m)

@[simp] theorem actMode_def (ρ : VHatRep W M) (a : 𝒱) (m : ℤ) :
    ρ.actMode a m = ρ (gen W a m) := rfl

/-- `actMode` is the lift applied to the algebra generator `umode`. -/
theorem actMode_eq_toAlgHom_umode (ρ : VHatRep W M) (a : 𝒱) (m : ℤ) :
    ρ.actMode a m = ρ.toAlgHom (umode W a m) := by
  rw [actMode_def, umode_def, toAlgHom_uι]

theorem actMode_add_left (ρ : VHatRep W M) (a a' : 𝒱) (m : ℤ) :
    ρ.actMode (a + a') m = ρ.actMode a m + ρ.actMode a' m := by
  simp only [actMode_def, gen_add_left, map_add]

theorem actMode_smul_left (ρ : VHatRep W M) (c : ℂ) (a : 𝒱) (m : ℤ) :
    ρ.actMode (c • a) m = c • ρ.actMode a m := by
  simp only [actMode_def, gen_smul_left, map_smul]

/-- **The mode-commutation law on `M`** (locality, the `ℓ = 0` Borcherds slice 5.1.7c): pushing the
`U(V̂)` Borcherds commutator `umode_commutator` through the representation `ρ` gives
`[a₍ₘ₎, b₍ₖ₎] = Σᶠ i, gBinom m i • (a₍ᵢ₎b)₍ₘ₊ₖ₋ᵢ₎` as a genuine commutator of endomorphisms of `M`.
This is the heart of the module-action consistency. -/
theorem actMode_bracket (ρ : VHatRep W M) (a b : 𝒱) (m k : ℤ) :
    ⁅ρ.actMode a m, ρ.actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) • ρ.actMode (W.smul a i b) (m + k - i) := by
  -- `actMode a m = ρ (gen a m)`, and `ρ` is a Lie morphism, so it carries the V̂-bracket to the
  -- End-commutator; then expand via `vhatBracket_gen` and push `ρ` through the finite OPE sum.
  rw [actMode_def, actMode_def, ← ρ.map_lie (gen W a m) (gen W b k),
    bracket_eq, vhatBracket_gen W (bracketDescends W) a b m k]
  -- finite support of the OPE family (VOA regularity)
  have hfin : (Function.support fun i : ℕ =>
      (gBinom m i) • gen W (W.smul a i b) (m + k - i)).Finite := by
    obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
    refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    refine hi ?_
    rw [hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), gen_zero_left, smul_zero]
  have hcoe : ∀ x : VHatCarrier W, ρ x = ρ.toLinearMap x := fun _ => rfl
  rw [hcoe, map_finsum _ hfin]
  refine finsum_congr fun i => ?_
  rw [map_smul]
  rfl

/-! ## The remaining crux for `M(U)`: the module Jacobi 5.3.1b

The action engine above (`toAlgHom`, `actMode`, `actMode_bracket`) gives a `V̂`-module on any space,
hence on the induced carrier `M(U) = U(V̂) ⊗_{U(P)} U`. To upgrade it to a *`𝒱`-module* — a
`OrdVModule W M(U)` realizing `U` — three further pieces are needed, and exactly one of them is genuine
mathematical content beyond `V̂` being a Lie algebra:

1. the carrier `M(U)` as the relative tensor product `U(V̂) ⊗_{U(P)} U` (pure algebra:
   `U(P)`-module + base change), with its `ℂ`-grading bounded below (PBW degree count) — *engineering*;
2. the field `Y_{M(U)}(u,z) = Σₙ actMode u n · z^{-n-1}` packaged as a `WeakModule.YM`, vacuum
   `Y_M(𝟙,z)=id` (`umode` of the vacuum), and the field/truncation property — *engineering*;
3. **the module Jacobi 5.3.1b** — the genuine theorem `IsModuleJacobi` below. Its `ℓ = 0` slice
   (locality / mode commutation) is *already proved* as `VHatRep.actMode_bracket`; the `ℓ ≠ 0`
   terms — the iterate products `(u₍ℓ₊ᵢ₎v)` — are the Borcherds content not implied by the Lie
   bracket alone. This is the precise remaining core.

`IsModuleJacobi ρ` is stated verbatim as the `WeakModule.jacobi` field (Def 5.3.1b) in terms of the
representation's mode action `actMode`, so that a proof of it (together with 1–2) yields a genuine
`WeakModule`/`OrdVModule` on `M(U)` mechanically. -/

/-- **The module Jacobi identity 5.3.1b for a `V̂`-representation**, stated exactly as the
`WeakModule.jacobi` field but with the mode action `a₍ₙ₎ := actMode a n`. This is the single genuine
remaining theorem of Construction A: its `ℓ = 0` slice is `actMode_bracket` (locality), and the full
identity (the `ℓ ≠ 0` iterate terms) is the Borcherds module identity DLM3 must verify on
`M(U) = U(V̂) ⊗_{U(P)} U`. A `Prop`-valued target, **not** an axiom. -/
def IsModuleJacobi (ρ : VHatRep W M) : Prop :=
  ∀ (u v : 𝒱) (x : M) (ℓ m n : ℤ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (ρ.actMode u (ℓ + m - i) (ρ.actMode v (n + i) x)
          - negOnePow ℓ • ρ.actMode v (ℓ + n - i) (ρ.actMode u (m + i) x)))
      = ∑ᶠ i : ℤ, cbz m i • ρ.actMode (W.smul u (ℓ + i) v) (m + n - i) x

end VHatRep

end VHat

end VOA
