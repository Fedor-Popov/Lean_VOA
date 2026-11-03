/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSdRealizes

/-!
# Track-B constructor — the bottom-survival iso `surv : L(U)_h ≅ M(U)_h` as a TERM off the
maximal-`J` construction

`Modules.ZhuVermaAnArchSdRealizes` reduced the bijection's `realizes` leaf to the `AModEquiv.trans`
of two honest pieces `surv`/`r0`, with `surv U : L(U).toAMod ≅ M(U).toAMod` (the **bottom survival**)
carried as a hypothesis and `r0 U : M(U).toAMod ≅ U` (R0 balanced bottom) the proven
`MUConstruct.bottomBalancedEquiv`.

This file **proves `surv` as a genuine TERM** off the `lumaxOfRegen` maximal-`J` construction.  The
key observation, made precise here, is that `surv` needs no new deep content:

* `L(U) = M(U)/J` with `J := supBotTrivialGraded` the maximal bottom-trivial graded submodule
  (`lumaxOfRegen`, from `bregen`);
* `J ⊓ M(U)_h = ⊥` is proved (`MUModuleData.supBotTrivialGraded_bottom_disjoint`, the
  `bottom_disjoint` field of `MaxJData.ofRegen`), so the quotient map `mkQ` restricted to the bottom
  weight space `M(U)_h` is **injective**;
* the projection `mkQ : M(U) → M(U)/J` is a `𝒱`-module homomorphism (`OrdVModule.quotientMk`), so it
  intertwines every mode, hence the module zero mode `o(u)`, hence the descended `A(𝒱)`-action `actA`
  on the bottoms.

Together these say: `mkQ` carries the bottom `M(U)_h` **isomorphically** onto the quotient bottom
`L(U)_h = (M(U)_h).map mkQ` as `A(𝒱)`-modules.  That isomorphism is `M(U)_h ≅ L(U)_h`; its inverse
is exactly `surv U : L(U)_h ≅ M(U)_h`.

So the single carried bottom-survival leaf of `sdRealizes` **folds into the maximal-`J`
construction** — a function of `G` (via `mudata`) and `bregen` (via `lumaxOfRegen`), with **no**
residual hypothesis.  Feeding it into `sdRealizes`/`bijection_of_sdRealizes` drops `surv` from the
bijection's leaf list; `realizes = surv.trans r0` is then a term of `G`/`bregen` alone.

## What is a TERM here

* **`InducedAssignment.oModHomIntertwine`** — a `𝒱`-module homomorphism `φ : A → B` (`WeakModule.Hom`
  between the underlying weak modules of two `OrdVModule`s) intertwines the module zero mode:
  `φ (o(u) x) = o(u) (φ x)`.  (The Hom analogue of `ModuleEquiv.intertwine_oMod`.)
* **`InducedAssignment.bottomSurvEquiv`** — the generic bottom-survival `A(𝒱)`-iso
  `M_h ≅ (M/J)_h` from a graded submodule `J` with `J ⊓ M_h = ⊥`.
* **`InducedAssignment.survOfRegen`** — `surv` for the Track-B maximal-`J` construction, the TERM
  `(bottomSurvEquiv …).symm` with `J := supBotTrivialGraded` and `J ⊓ M(U)_h = ⊥` the proved
  `supBotTrivialGraded_bottom_disjoint`.
* **`bijection_of_sdSurv`** — the faithful Zhu-5.3.4 bijection with `surv` discharged to
  `survOfRegen` (so `realizes` folds entirely into `bregen`; the leaf list drops from five to four:
  `[hslice, G, bregen, G']`).

## What is CARRIED

Nothing new.  The bijection's remaining inputs (`hslice` — carrying `MUGradedAction`; `G`; `bregen`;
`r0` — the proven R0 balanced bottom; `Dfun`; `G'`) are threaded unchanged.  `surv` is not a
leaf.

## References
Dong–Li–Mason J. Algebra 206 (1998), Prop 3.2.9; Dong–Jiang Math. Z. 259 (2008); Frenkel–Zhu;
Gannon §5.3.2, Thm 5.3.4; `ZhuBijection` (`AMod`, `AModEquiv`, `lowestAMod`, `actA_mk_apply_coe`,
`intertwine_oMod`); `ZhuAlgebra` (`oMod_homogeneous`); `ZhuVermaAnArchVModQuotGraded`
(`OrdVModule.quotient`, `quotient_weight`, `quotientMk`); `ZhuVermaAnArchLumaxSupDisjoint`
(`supBotTrivialGraded_bottom_disjoint`); `ZhuVermaAnArchStructuralClose` (`lumaxOfRegen`,
`BottomRegenData`); `ZhuVermaAnArchSdRealizes` (`sdRealizes`, `bijection_of_sdRealizes`).
-/

set_option linter.style.longLine false

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra
open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## A `𝒱`-module homomorphism intertwines the module zero mode `o(u)` -/

section OModHom

variable {M N : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
variable {A : OrdVModule W M} {B : OrdVModule W N}

/-- **A weak-module homomorphism intertwines the mode operator** `u₍ₙ₎`:
`φ(u₍ₙ₎ x) = u₍ₙ₎ φ(x)`.  (Restatement of `WeakModule.Hom.map_act` through `WeakModule.act_def`.) -/
theorem homIntertwineMode (φ : A.toWeakModule.Hom B.toWeakModule)
    (u : 𝒱) (n : ℤ) (x : M) :
    φ.toLinearMap (mode (A.YM u) n x) = mode (B.YM u) n (φ.toLinearMap x) := by
  have := φ.map_act u n x
  simpa only [WeakModule.act_def] using this

/-- **A `𝒱`-module homomorphism intertwines the module zero mode** `o(u)` on homogeneous states:
for `u ∈ 𝒱ₖ`, `φ(o(u) x) = o(u) (φ x)`.  (`o(u) = u₍ₖ₋₁₎` there.) -/
theorem oModHomIntertwine_homog (φ : A.toWeakModule.Hom B.toWeakModule)
    {k : ℤ} {u : 𝒱} (hu : u ∈ W.grading k) (x : M) :
    φ.toLinearMap (oMod A u x) = oMod B u (φ.toLinearMap x) := by
  rw [oMod_homogeneous A hu, oMod_homogeneous B hu, homIntertwineMode]

/-- **A `𝒱`-module homomorphism intertwines the module zero mode** `o(u)` for *all* states `u`
(extend by linearity over the grade decomposition).  The Hom analogue of
`ModuleEquiv.intertwine_oMod`. -/
theorem oModHomIntertwine (φ : A.toWeakModule.Hom B.toWeakModule) (u : 𝒱) (x : M) :
    φ.toLinearMap (oMod A u x) = oMod B u (φ.toLinearMap x) := by
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => φ.toLinearMap (oMod A u x) = oMod B u (φ.toLinearMap x)) hutop
    ?_ ?_ ?_
  · intro i y hy; exact oModHomIntertwine_homog φ hy x
  · simp
  · intro y z hy hz
    rw [map_add, LinearMap.add_apply, map_add, hy, hz, map_add, LinearMap.add_apply]

end OModHom

/-! ## The generic bottom-survival `A(𝒱)`-iso `M_h ≅ (M/J)_h` -/

section BottomSurv

variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {N : OrdVModule W M} {h : ℂ}
variable {P : WeakModule.Submodule' N.toWeakModule}

/-- The forward linear map `M_h → M/P`, the quotient projection restricted to the bottom weight
space: `x ↦ mkQ x`. -/
noncomputable def survFwdMap (P : WeakModule.Submodule' N.toWeakModule) (h : ℂ) :
    (N.weight h) →ₗ[ℂ] (M ⧸ P.carrier) :=
  P.carrier.mkQ.comp (N.weight h).subtype

@[simp] theorem survFwdMap_apply (P : WeakModule.Submodule' N.toWeakModule) (h : ℂ)
    (x : N.weight h) :
    survFwdMap P h x = Submodule.Quotient.mk (x : M) := rfl

/-- **The forward map is injective** when `J ⊓ M_h = ⊥`.  Its kernel is the set of bottom vectors in
`J`, which is `J ⊓ M_h = ⊥`. -/
theorem survFwdMap_injective (hdisj : P.carrier ⊓ N.weight h = ⊥) :
    Function.Injective (survFwdMap P h) := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro x hx
  -- `hx : mkQ (x : M) = 0`, i.e. `(x : M) ∈ P.carrier`.
  rw [LinearMap.mem_ker, survFwdMap_apply, Submodule.Quotient.mk_eq_zero] at hx
  -- `(x : M) ∈ P.carrier ⊓ N.weight h = ⊥`.
  have hmem : (x : M) ∈ P.carrier ⊓ N.weight h := ⟨hx, x.2⟩
  rw [hdisj, Submodule.mem_bot] at hmem
  exact Subtype.ext hmem

/-- The range of the forward map is `(M_h).map mkQ`, the quotient bottom `(M/P)_h`. -/
theorem survFwdMap_range :
    LinearMap.range (survFwdMap P h) = (N.weight h).map P.carrier.mkQ := by
  rw [survFwdMap, LinearMap.range_comp, Submodule.range_subtype]

/-- The linear equivalence `M_h ≃ₗ (M/P)_h` from injectivity of the restricted projection, with the
target reindexed as the quotient bottom `(N.weight h).map mkQ`. -/
noncomputable def survLinEquiv (hdisj : P.carrier ⊓ N.weight h = ⊥) :
    (N.weight h) ≃ₗ[ℂ] ((N.weight h).map P.carrier.mkQ) :=
  (LinearEquiv.ofInjective (survFwdMap P h) (survFwdMap_injective hdisj)).trans
    (LinearEquiv.ofEq _ _ survFwdMap_range)

/-- On a bottom vector `x`, the survival linear equivalence coerces to `mkQ (x : M)` in `M/P`. -/
@[simp] theorem survLinEquiv_coe (hdisj : P.carrier ⊓ N.weight h = ⊥) (x : N.weight h) :
    ((survLinEquiv hdisj x : (N.weight h).map P.carrier.mkQ) : M ⧸ P.carrier)
      = Submodule.Quotient.mk (x : M) := by
  rfl

end BottomSurv

/-! ## Assembling the survival `AModEquiv` (forward: `M_h ≅ (M/J)_h`) -/

section BottomSurvAMod

variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {N : OrdVModule W M} {h : ℂ}
variable {P : WeakModule.Submodule' N.toWeakModule}

/-- **The forward bottom-survival `A(𝒱)`-iso** `M_h ≅ (M/J)_h`.

The linear part is `survLinEquiv` (the quotient projection restricted to the bottom, injective by
`J ⊓ M_h = ⊥`).  The `A(𝒱)`-intertwining is: on a representative `[u] ∈ A(𝒱)`, both sides coerce to
`M/P`, where the projection `mkQ = quotientMk` intertwines the module zero mode `o(u)`
(`oModHomIntertwine`), so `mkQ (o(u) x) = o(u) (mkQ x)`. -/
noncomputable def bottomSurvEquiv (hgr : OrdVModule.IsGradedSubmodule N P)
    (hcw : IsLowestWeight N h) (hLQ : IsLowestWeight (OrdVModule.quotient N P hgr) h)
    (hdisj : P.carrier ⊓ N.weight h = ⊥) :
    AModEquiv W (lowestAMod hcw) (lowestAMod hLQ) where
  toLinearEquiv := survLinEquiv hdisj
  map_ρ a x := by
    -- Reduce `a = [u]`.
    refine Submodule.Quotient.induction_on (O W) a (fun u => ?_)
    -- Name the underlying bottom weight vector (`x : (lowestAMod hcw).carrier = N.weight h`).
    let x' : N.weight h := x
    -- Both sides live in `(quotient N P hgr).weight h = (N.weight h).map mkQ ⊆ M/P`; compare
    -- coercions to `M/P`.
    apply Subtype.ext
    -- Unfold `lowestAMod.ρ = actA`, coerce through the two bottom weight spaces.
    show ((survLinEquiv hdisj (actA N hcw (VOA.mk W u) x')
            : (N.weight h).map P.carrier.mkQ) : M ⧸ P.carrier)
        = ((actA (OrdVModule.quotient N P hgr) hLQ (VOA.mk W u)
              (survLinEquiv hdisj x') : (OrdVModule.quotient N P hgr).weight h) : M ⧸ P.carrier)
    -- LHS: `mkQ (o(u) (x : M))`.
    rw [survLinEquiv_coe hdisj, actA_mk_apply_coe N hcw u x']
    -- RHS: `o(u) (mkQ (x : M))` — coerce through `actA_mk_apply_coe` for the quotient module.
    rw [actA_mk_apply_coe (OrdVModule.quotient N P hgr) hLQ u (survLinEquiv hdisj x'),
      survLinEquiv_coe hdisj]
    -- Now `mkQ (o(u) (x:M)) = o(u) (mkQ (x:M))` via the projection Hom intertwining `o(u)`.
    -- `quotientMk.toLinearMap = mkQ` (by `quotientMk_apply`, rfl), so this is the Hom intertwining.
    have hint := oModHomIntertwine (OrdVModule.quotientMk N P hgr) u (x' : M)
    rw [OrdVModule.quotientMk_apply, OrdVModule.quotientMk_apply] at hint
    exact hint

end BottomSurvAMod

/-! ## `surv` for the Track-B maximal-`J` construction — a TERM of `G` and `bregen` -/

/-- **`survOfRegen` — the bottom-survival iso `L(U)_h ≅ M(U)_h` as a TERM off the maximal-`J`
construction.**

`L(U) = M(U)/J` with `J := supBotTrivialGraded` (`lumaxOfRegen G bregen`, from `bregen`), and
`J ⊓ M(U)_h = ⊥` is the **proved** `supBotTrivialGraded_bottom_disjoint`.  The forward
`bottomSurvEquiv` is the `A(𝒱)`-iso `M(U)_h ≅ L(U)_h`; `survOfRegen` is its `symm`, matching the
`surv` argument of `sdRealizes`.  No `sorry`, **never** an axiom. -/
noncomputable def survOfRegen (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G) :
    ∀ U : AMod W,
      AModEquiv W (((G.toBimodGenuineConstructionA).toLUFamily (sdLudata G bregen)).K U).toAMod
        ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toLWModule.toAMod :=
  fun U =>
    -- Notation for the genuine `M(U)` and its maximal-`J` datum.
    let R := (G.toBimodGenuineConstructionA).toMURepFamily
    let D := R.mudata U
    let L := sdLudata G bregen U
    -- `(K U).toAMod = lowestAMod (L.LU_isLowestWeight)`; `(mudata U).toLWModule.toAMod =
    -- lowestAMod D.isLowestWeight`.  The forward survival iso is `M(U)_h ≅ L(U)_h`; take `symm`.
    -- `L.J = D.supBotTrivialGraded` definitionally (through `toLUData`/`toLUMaxData`/`ofRegen`),
    -- so the disjointness is the proved `supBotTrivialGraded_bottom_disjoint`.
    (bottomSurvEquiv (M := MU W U) (N := D.toOrdVModule) (h := R.hU U) (P := L.J)
        L.J_graded D.isLowestWeight L.LU_isLowestWeight
        D.supBotTrivialGraded_bottom_disjoint).symm

end InducedAssignment

/-! ## The bijection with `surv` discharged to the maximal-`J` construction -/

/-- **`bijection_of_sdSurv` — the faithful Zhu-5.3.4 bijection with `surv` reduced to the maximal-`J`
construction (so `realizes` folds entirely into `bregen`).**

`Function.Bijective (forwardMapIrr W)` from the keystone `hslice`, the genuine construction datum `G`
(carrying `MUGradedAction`), the maximal-`J` residue `bregen`, the R0 balanced-bottom piece `r0` (the
proven `MUConstruct.bottomBalancedEquiv`), the functoriality datum `Dfun`, and the
generation-from-bottom family `G'`.  The bottom-survival piece `surv` is the TERM
`InducedAssignment.survOfRegen G bregen`, so the bijection's leaf list drops from five to four:
`[hslice, G, bregen, G']` (`r0`, `Dfun` being proven/threaded).  Feeds
`InducedAssignment.sdRealizes G bregen (survOfRegen G bregen) r0` into `bijection_of_sdRealizes`.
No `sorry`, **never** an axiom. -/
theorem bijection_of_sdSurv {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W)
    (G : InducedAssignment.BimodGenuineConstructionAUniform W)
    (bregen : InducedAssignment.BottomRegenData G)
    (r0 : ∀ U : AMod W,
      AModEquiv W ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).toLWModule.toAMod U)
    (Dfun : InducedAssignment.MUFunctorialData
      ((G.toBimodGenuineConstructionA).toLUFamily (InducedAssignment.sdLudata G bregen)))
    (G' : InducedAssignment.GenFromBottomGFamily
      (G.toLUFamily (fun U => (InducedAssignment.lumaxOfRegen G bregen U).toLUData))) :
    Function.Bijective (forwardMapIrr W) :=
  bijection_of_sdRealizes hslice G bregen (InducedAssignment.survOfRegen G bregen) r0 Dfun G'

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
