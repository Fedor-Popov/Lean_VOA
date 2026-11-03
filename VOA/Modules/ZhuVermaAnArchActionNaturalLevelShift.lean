/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMuEquivClose
import VOA.Modules.ZhuVermaAnArchLevelShiftRho
import VOA.Modules.ZhuVermaAnArchHinge

/-!
# DJ Prop 3.4 (`MUActionNatural`) proved for the concrete level-shift construction

`Modules.ZhuVermaAnArchMuEquivClose` reduced the functoriality clause `hiso`/`muEquiv` of Zhu
Theorem 5.3.4 (the injective half) to the single Construction-A datum `MUFirstFactorData F`, whose
three fields are

* `firstAct`  — a **bottom-independent** first-factor `𝒱`-action on `Â(𝒱) = ⊕ₙ A_{n,0}(𝒱)`;
* `act_eq`    — the DJ §4 `uₚ` formula `(F.mudata U).weak.act u n = firstAct u n ⊗ id_U`;
* `J_natural` — DJ Prop 3.5 (canonicity of `J`: `M(φ)` carries `J₁` onto `J₂`).

From that datum `MUFirstFactorData.actionNatural` proves DJ Prop 3.4 (`MUActionNatural F`) by the
two-disjoint-factors `TensorProduct.map` commutation.  But `firstAct`/`act_eq` are still **carried**
there — the abstract `MUModuleData.weak` field is opaque.

This file **discharges `firstAct`/`act_eq` as terms** for the *genuine* Dong–Jiang Construction-A
loop action `levelShiftAct` (`ZhuVermaAnArchLevelShiftRho`), the action every actual `M(U)` in the
build carries (`BimodGenuineConstructionA.mudata_act`).  Concretely, the level-shift loop mode
`a₍ₘ₎` acts on the layer `n` by

  `a₍ₘ₎([x] ⊗ u) = [a *^{σ m n, n, 0} x] ⊗ u`     (`levelShiftActGen_incl_tmul`),

i.e. by the bimodule composition `anmComposeBilin` on the **first** tensor factor `A_{n,0}(𝒱)`,
identity on the bottom `U`.  So it **is** `firstAct ⊗ id_U` for the bottom-independent first-factor
map `firstActLevelShiftDeg` (assembled from the same `anmComposeBilin` pieces over `Â(𝒱)`).  The
key identity is the one genuinely new theorem here:

  `levelShiftAct_eq_liftFirst : levelShiftAct W U σ m hL hR a`
  `  = MU.liftFirst U (firstActLevelShiftDeg …)`.

Everything else reuses the *already-proven* map-level commutation
`MU.functorEquiv_comp_liftFirst` (`ZhuVermaAnArchMuEquivClose`).

## The one structural requirement — `σ` bottom-independent

`firstAct` must be one first-factor map for **every** bottom `U` (that is the content of
Construction A).  The level-shift assignment `σ` and its descents `hL`/`hR` therefore enter as
**bottom-independent** data (they depend only on the VOA grading, not on `U`), which is physically
exactly the Frenkel–Zhu grade shift.  The theorem `MUActionNatural_of_levelShift` consumes precisely
the hypothesis that the carried action of every `M(U)` is the *same-σ* level-shift action `hact`,
and returns DJ Prop 3.4 (`MUActionNatural F`) — a **proved** theorem, not a carried hypothesis.

## What is built (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`MU.firstActLevelShiftDeg`** — the bottom-independent first-factor level-shift map on
  `Â(𝒱) = ⊕ₙ A_{n,0}(𝒱)`, `lof n [x] ↦ lof (σ m n) [a *^{σ m n, n, 0} x]`, assembled by
  `DirectSum.toModule` from the `anmComposeBilin` pieces.
* **`VHat.levelShiftPiece_apply_tmul`** — the abstract-representative evaluation of
  `levelShiftPiece` (on `y ⊗ u`, `y : A_{n,0}(𝒱)` not restricted to a `mkAnm`), needed for the
  tensor-factor calc.
* **`VHat.levelShiftAct_eq_liftFirst`** — **the genuinely new identity**: the level-shift action
  *is* `liftFirst` of the concrete bottom-independent first-factor map (DJ §4 `uₚ`).
* **`InducedAssignment.MUActionNatural_of_levelShift`** — **DJ Prop 3.4 proved**:
  `MUActionNatural F` for any family whose per-`U` action is the (bottom-independent-σ) level-shift
  action.
* **`InducedAssignment.isoInvariant_of_levelShift`** — `isoInvariant` (functoriality of `L(·)` on
  bottoms) from the level-shift action form (`hact`) plus the *single* remaining carried DJ residual
  `MUJNatural F` (canonicity of `J`).  So `hiso` rests on `[hact (a TERM for the genuine
  construction) + MUJNatural]`; DJ Prop 3.4 is a proved `TensorProduct.map` commutation.
* **`zhuBijection_assembled_levelShiftNatural`** — the headline `Φ(𝒱) ↔ Irr A(𝒱)` bijection with
  `hiso` sourced this way.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13 (§4 `uₚ`, first-factor
action); Frenkel–Zhu; Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchLevelShiftRho` (`levelShiftAct`,
`levelShiftPiece`), `ZhuVermaAnArchMuEquivClose` (`MU.firstSum`, `MU.liftFirst`,
`MU.functorEquiv_comp_liftFirst`, `MUActionNatural`, `MUFirstFactorData`), `ZhuVermaAnArchBimodComp`
(`anmComposeBilin`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The abstract-representative evaluation of `levelShiftPiece` -/

namespace VHat

variable {W : VertexOperatorAlgebra 𝒱}

/-- **Abstract-representative evaluation of `levelShiftPiece`.**  On a decomposable tensor
`y ⊗ u` with `y : A_{n,0}(𝒱)` an *arbitrary* class (not restricted to a `mkAnm` representative), the
level-shift piece is the bimodule composition `anmComposeBilin` applied to `y` in the **first**
tensor factor, `u` untouched, then included into the shifted layer `σ m n`.  (The existing
`levelShiftPiece_tmul` is the `y = mkAnm x` special case; this abstract form is what the
tensor-factor commutation calc needs.) -/
@[simp] theorem levelShiftPiece_apply_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ) (m : ℤ) (n : ℕ)
    (hL : AnmComposeDescL W (σ m n) n 0) (hR : AnmComposeDescR W (σ m n) n 0) (a : 𝒱)
    (y : Anm W n 0) (u : U.carrier) :
    levelShiftPiece W U σ m n hL hR a (y ⊗ₜ[ℂ] u)
      = MU.incl W U (σ m n)
          (anmComposeBilin W (σ m n) n 0 hL hR (mkAnm W (σ m n) n a) y ⊗ₜ[ℂ] u) := by
  simp only [levelShiftPiece, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

end VHat

/-! ## The concrete bottom-independent first-factor level-shift map -/

namespace MU

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The bottom-independent first-factor level-shift map** on `Â(𝒱) = ⊕ₙ A_{n,0}(𝒱)` for a
degree-`m` loop vector `a`.  On the layer `n` it sends `lof n [x]` to
`lof (σ m n) [a *^{σ m n, n, 0} x]` (the
`anmComposeBilin` composition into the shifted layer `σ m n`), assembled by `DirectSum.toModule`.
This is the first-factor `firstAct u m` of DJ §4 `uₚ`, depending only on the VOA data `σ`/`hL`/`hR`,
**not** on any bottom `U`. -/
noncomputable def firstActLevelShiftDeg (W : VertexOperatorAlgebra 𝒱)
    (σ : ℤ → ℕ → ℕ) (m : ℤ)
    (hL : ∀ n : ℕ, AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ n : ℕ, AnmComposeDescR W (σ m n) n 0) (a : 𝒱) :
    MU.firstSum W →ₗ[ℂ] MU.firstSum W :=
  DirectSum.toModule ℂ ℕ (MU.firstSum W)
    (fun n => (DirectSum.lof ℂ ℕ (fun k => Anm W k 0) (σ m n)).comp
      (anmComposeBilin W (σ m n) n 0 (hL n) (hR n) (mkAnm W (σ m n) n a)))

@[simp] theorem firstActLevelShiftDeg_lof (W : VertexOperatorAlgebra 𝒱)
    (σ : ℤ → ℕ → ℕ) (m : ℤ)
    (hL : ∀ n : ℕ, AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ n : ℕ, AnmComposeDescR W (σ m n) n 0) (a : 𝒱) (n : ℕ) (y : Anm W n 0) :
    firstActLevelShiftDeg W σ m hL hR a (DirectSum.lof ℂ ℕ (fun k => Anm W k 0) n y)
      = DirectSum.lof ℂ ℕ (fun k => Anm W k 0) (σ m n)
          (anmComposeBilin W (σ m n) n 0 (hL n) (hR n) (mkAnm W (σ m n) n a) y) := by
  rw [firstActLevelShiftDeg, DirectSum.toModule_lof]
  rfl

end MU

/-! ## The genuinely new identity — `levelShiftAct = liftFirst (firstAct)` (DJ §4 `uₚ`) -/

namespace VHat

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The level-shift loop action IS `liftFirst` of the concrete bottom-independent first-factor
map** — the DJ §4 `uₚ = firstAct ⊗ id_U` formula, *proved* for the genuine Construction-A action.

On a layer-`n` generator `[x] ⊗ u`:
* `levelShiftAct` gives `incl (σ m n) ([a *^{σ m n, n, 0} x] ⊗ u)` (`levelShiftAct_incl` +
  `levelShiftPiece_apply_tmul`);
* `liftFirst U (firstActLevelShiftDeg …)` gives `distrib (lof (σ m n) [a *^{σ m n, n, 0} x] ⊗ u)
  = incl (σ m n) ([a *^{σ m n, n, 0} x] ⊗ u)` (`liftFirst_incl` + `firstActLevelShiftDeg_lof` +
  `distrib_lof_tmul`).
They agree — the action touches only the first tensor factor, exactly `firstAct ⊗ id_U`. -/
theorem levelShiftAct_eq_liftFirst (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (σ : ℤ → ℕ → ℕ) (m : ℤ)
    (hL : ∀ n : ℕ, AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ n : ℕ, AnmComposeDescR W (σ m n) n 0) (a : 𝒱) :
    levelShiftAct W U σ m hL hR a
      = MU.liftFirst U (MU.firstActLevelShiftDeg W σ m hL hR a) := by
  -- Both sides are ℂ-linear out of `MU W U = ⊕ₙ (A_{n,0} ⊗ U)`; check on `incl n (y ⊗ u)`.
  apply DirectSum.linearMap_ext
  intro n
  apply TensorProduct.ext'
  intro y u
  change levelShiftAct W U σ m hL hR a (MU.incl W U n (y ⊗ₜ[ℂ] u))
    = MU.liftFirst U (MU.firstActLevelShiftDeg W σ m hL hR a) (MU.incl W U n (y ⊗ₜ[ℂ] u))
  rw [levelShiftAct_incl, levelShiftPiece_apply_tmul, MU.liftFirst_incl,
    MU.firstActLevelShiftDeg_lof, MU.distrib_lof_tmul]

end VHat

/-! ## DJ Prop 3.4 (`MUActionNatural`) proved for the level-shift construction -/

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **DJ Prop 3.4 (`MUActionNatural F`) proved for the genuine level-shift construction.**

Suppose the carried `𝒱`-action of every `M(U)` in the family `F` is the *bottom-independent-σ*
level-shift action `levelShiftAct W U σ n hL hR u` (this is a **term** for the genuine
Construction-A family via `BimodGenuineConstructionA.mudata_act`, once `σ`/`hL`/`hR` are supplied
bottom-independent).  Then the genuine Dong–Jiang map `M(φ) = 1 ⊗ φ` intertwines the two actions:

`M(φ)((F.mudata U₁).act u n x) = (F.mudata U₂).act u n (M(φ) x)`.

Proof: rewrite each action by `hact` and `levelShiftAct_eq_liftFirst` to `liftFirst U (firstAct …)`,
then apply the *already-proven* map-level commutation `MU.functorEquiv_comp_liftFirst` (the two
`TensorProduct.map`s on disjoint factors commute).  DJ Prop 3.4 is thus a proved theorem, not a
carried hypothesis. -/
theorem MUActionNatural_of_levelShift (F : LUFamily W) (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hact : ∀ (U : AMod W) (u : 𝒱) (n : ℤ),
      (F.mudata U).weak.act u n
        = VHat.levelShiftAct W U σ n (fun k => hL n k) (fun k => hR n k) u) :
    MUActionNatural F := by
  intro U₁ U₂ φ u n x
  rw [hact U₁ u n, hact U₂ u n,
    VHat.levelShiftAct_eq_liftFirst, VHat.levelShiftAct_eq_liftFirst]
  -- The map-level commutation applied to `x`.
  have key := congrArg (fun (f : MU W U₁ →ₗ[ℂ] MU W U₂) => f x)
    (MU.functorEquiv_comp_liftFirst φ (MU.firstActLevelShiftDeg W σ n (fun k => hL n k)
      (fun k => hR n k) u))
  simpa [LinearMap.comp_apply] using key

/-- **`isoInvariant` (functoriality of `L(·)` on bottoms) from the level-shift action form.**

`hiso` rests on exactly `[hact + MUJNatural F]`: the DJ Prop 3.4 naturality is the *proved*
`MUActionNatural_of_levelShift`, and only DJ Prop 3.5 (`MUJNatural`, canonicity of `J`) is carried.
Assembled via `MUFunctorialData.ofNaturality` and the unconditional quotient-functor descent. -/
theorem isoInvariant_of_levelShift (F : LUFamily W) (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hact : ∀ (U : AMod W) (u : 𝒱) (n : ℤ),
      (F.mudata U).weak.act u n
        = VHat.levelShiftAct W U σ n (fun k => hL n k) (fun k => hR n k) u)
    (hJ : MUJNatural F) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂) :=
  (MUFunctorialData.ofNaturality (MUActionNatural_of_levelShift F σ hL hR hact) hJ).isoInvariant

end InducedAssignment

/-! ## The headline — the Zhu bijection with `hiso` on the level-shift-action naturality -/

/-- **`zhuBijection_assembled_levelShiftNatural` — the `Φ(𝒱) ↔ Irr A(𝒱)` bijection of Zhu Theorem
5.3.4, with `hiso` resting on the proved DJ Prop 3.4 naturality of the level-shift action.**

Identical to `zhuBijection_assembled_muNatural`/`_firstFactor`, except the functoriality clause
`hiso` is sourced from `isoInvariant_of_levelShift`: DJ Prop 3.4 (`MUActionNatural`) is a proved
`TensorProduct.map` commutation for the genuine Construction-A level-shift action (`hact`), and only
DJ Prop 3.5 (`MUJNatural`, canonicity of `J`) remains carried on the `hiso` side. -/
theorem zhuBijection_assembled_levelShiftNatural {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hact : ∀ (U : AMod W) (u : 𝒱) (n : ℤ),
      (F.mudata U).weak.act u n
        = VHat.levelShiftAct W U σ n (fun k => hL n k) (fun k => hR n k) u)
    (hJ : InducedAssignment.MUJNatural F)
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_final_scorecard A hall hirr F
    (InducedAssignment.isoInvariant_of_levelShift F σ hL hR hact hJ) G

/-! ## The faithful (`hall`-free) hinge, with `hiso`'s DJ Prop 3.4 half discharged -/

/-- **`phase4_of_dj28_levelShiftNatural` — the faithful, `hall`-free Zhu Theorem 5.3.4 bijection
`Φ(𝒱) ↔ Irr A(𝒱)` (`forwardMapIrr`) with the functoriality `hiso`'s DJ Prop 3.4 half proved for the
genuine level-shift construction.**

This threads the reduced `hiso` (`isoInvariant_of_levelShift`) into the faithful hinge
`phase4_of_dj28_neededSlice` (`ZhuVermaAnArchHinge`).  Compared with that hinge, the opaque carried
functoriality clause `hiso` is sourced from `[hact + MUJNatural]`, where DJ Prop
3.4 (`MUActionNatural`) is a **proved** `TensorProduct.map` commutation for the level-shift action
(`hact`), and only DJ Prop 3.5 (`MUJNatural`, canonicity of `J`) remains carried on the `hiso` side.

The full injective-side surface is thus: `[hslice` (the keystone `NeededSliceMems`), `A`/`hirr`,
`F`, `hact` (the level-shift action form of `M(U)`), `MUJNatural` (canonicity of `J`), `G`]`.  The
DJ Prop 3.4 naturality inside `hiso` is discharged. -/
theorem phase4_of_dj28_levelShiftNatural {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (F : InducedAssignment.LUFamily W)
    (σ : ℤ → ℕ → ℕ)
    (hL : ∀ (m : ℤ) (n : ℕ), AnmComposeDescL W (σ m n) n 0)
    (hR : ∀ (m : ℤ) (n : ℕ), AnmComposeDescR W (σ m n) n 0)
    (hact : ∀ (U : AMod W) (u : 𝒱) (n : ℤ),
      (F.mudata U).weak.act u n
        = VHat.levelShiftAct W U σ n (fun k => hL n k) (fun k => hR n k) u)
    (hJ : InducedAssignment.MUJNatural F)
    (G : InducedAssignment.GenFromBottomGFamily F) :
    Function.Bijective (forwardMapIrr W) :=
  phase4_of_dj28_neededSlice hslice A hirr F
    (InducedAssignment.isoInvariant_of_levelShift F σ hL hR hact hJ) G

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
