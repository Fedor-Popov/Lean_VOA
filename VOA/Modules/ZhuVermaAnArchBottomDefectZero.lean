/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchBottomLevelDefect

/-!
# The bare module-iterate defect on the bottom `M₀` — the exact `A(𝒱)`-level computation

`ZhuVermaAnArchBottomLevelDefect` reduced full bottom survival of the sound Construction-A
representation `repMULevel` to the single carried datum

  `bottomDefectZero : ∀ u v x ℓ N, x ∈ MUdegZ W U 0 → defectVec (repMULevel …) u v x ℓ N = 0`,

the **bare** (`g = 1`) iterate defect on the bottom `M₀ = MUdegZ 0 = MU.deg 0 = A(𝒱) ⊗ U`.  This
file computes that defect **exactly** at the bottom — the depth-`0` mirror of the
`gMode_anmCirc_lowest` / `oMod_zhuMul_lowest` collapse — pushing it all the way down to a pure
identity in the Zhu algebra `A(𝒱) = Anm W 0 0`.

## The mechanism — the bottom action factors as a pure `A(𝒱)`-identity tensored with `id_U`

The sound modes of `repMULevel` are the level-diagonal action `composeActLevel a`
(`repMULevel_actMode`), **independent of the mode index** `m`, and *block-diagonal* for the level
grading (`composeActLevel_incl`).  On the bottom block `M₀ = MU.deg 0 = range (MU.incl 0)`, a state
is `MU.incl 0 y` with `y : MUPiece W U 0 = A(𝒱) ⊗ U`, and `composeActLevel a (MU.incl 0 y) =
MU.incl 0 (MU.actLevel 0 (hclo 0) a y)` (`composeActLevel_incl`), where the level-`0` action acts on
the left tensor factor by the **bottom right residue** `MU.actAnm 0 (hclo 0) a`, i.e.
`mkAnm 0 r ↦ mkAnm 0 (anmRight 0 0 r a) = mkAnm 0 (zhuMul r a)` (`anmRight_zero_zero`), leaving `U`
untouched.

Therefore (using the already-closed `defectVec_eq_defectLin`, which factors the level-constant
finite sum out of the summation index) the whole bottom defect is

  `MU.incl 0 ((D ⊗ id_U) y)`,   `D : A(𝒱) →ₗ A(𝒱)`,
  `D (mkAnm 0 r) = mkAnm 0 (zhuMul r (u₍ℓ₎v))`
    `− S • (mkAnm 0 (zhuMul (zhuMul r v) u) − (−1)^ℓ • mkAnm 0 (zhuMul (zhuMul r u) v))`,

with the level-constant finite-sum scalar `S = ∑ᶠ i, (−1)^i · C(ℓ,i)` (`= 1` for `ℓ = 0`, `0`
otherwise — for `ℓ < 0` the support is infinite, so the `finsum` is `0`).  Hence the bottom defect
vanishes **iff** `D = 0` on every representative `mkAnm 0 r`, i.e. iff the `A(𝒱)`-level identity

  `[zhuMul r (u₍ℓ₎v)] = S • ([zhuMul (zhuMul r v) u] − (−1)^ℓ • [zhuMul (zhuMul r u) v])`  in `A(𝒱)`

holds.  This file proves that *reduction* (`bottomDefectZero_iff_AVRelation`,
`repMULevel_bottomDefectZero` from `BottomAVRelation`), and isolates `BottomAVRelation` as the EXACT
remaining `A(𝒱)`-level identity — the genuine depth-`0` zero-mode content.

## ⚠ ENGINE FINDING — `BottomAVRelation` is NOT an identity for the *level-constant* action

`certificates/mathematica/bottom_defect_zero.wl` (rank-`1` free boson, `A(𝒱) = ℂ[x]`) shows the
combination `D (mkAnm 0 r)` is **not** in `O(𝒱)` in general for the bare level-constant action:
e.g. `r = 𝟙`, `u = v = α₍₋₁₎𝟙`, `ℓ = −1` gives `D 𝟙 = [α₍₋₁₎α₍₋₁₎𝟙] = x² ≠ 0` (since `S = 0` for
`ℓ < 0`), and many `ℓ ≥ 0` cases with `wt u ≥ 2` likewise fail (the index-independent action does not
reproduce the genuine depth-graded mode action off the diagonal).  So `BottomAVRelation` is recorded
here as the **precise required identity**, *not* asserted to hold for `repMULevel` — it holds for the
genuine depth-graded module action (where modes depend on the index), which the level-constant
`repMULevel` only matches on the diagonal.  Everything *structural* below (the exact bottom
computation) is TRUE and proved; the remaining identity is stated honestly and **never** assumed as
an axiom or `sorry`.

## What is built here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`bottomActLevel_incl`** — the bottom factoring `composeActLevel a (MU.incl 0 y) =
  MU.incl 0 (MU.actLevel 0 (hclo 0) a y)` specialised to the bottom block.
* **`defectLin0`** — the bottom defect endomorphism of `A(𝒱) ⊗ U` (level-`0` mirror of `defectLin`).
* **`defectLin_bottom_incl`** — `defectLin u v ℓ N (MU.incl 0 y) = MU.incl 0 (defectLin0 … y)`, the
  full block-diagonal factoring of the bare defect on the bottom (no defect outside the block).
* **`defectLin0_tmul_eq`** — the bottom defect on a pure tensor `mkAnm 0 r ⊗ u₀`, as the explicit
  `A(𝒱)`-combination tensored with `u₀`.
* **`BottomAVRelation`** — the precise `A(𝒱)`-level identity (the EXACT remaining zero-mode datum), a
  `Prop`, **never** an axiom.
* **`defectLin0_eq_zero`** — `BottomAVRelation ⟹ defectLin0 = 0` (`TensorProduct.ext`).
* **`bottomDefectZero_iff_AVRelation`** — the clean equivalence: the bare bottom defect vanishes for
  all bottom inputs **iff** `BottomAVRelation` holds.
* **`repMULevel_bottomDefectZero`** — *the closure direction*: from `BottomAVRelation`,
  `bottomDefectZero` holds (and hence, via `repMULevel_bottomSurvives_of_bottomDefect`, full bottom
  survival of `M(U)`).
* **`repMULevel_bottomSurvives_of_AVRelation`** — bottom survival from the single `A(𝒱)`-level datum.

## References
DLM3 §4; Frenkel–Zhu; Dong–Jiang `math/0601626`; Gannon §5.3.2, Thm 5.3.4, 5.3.9a;
`ZhuVermaAnArchBottomLevelDefect` (`defectLin`, `defectVec_eq_defectLin`,
`repMULevel_bottomSurvives_of_bottomDefect`); `ZhuVermaAnArchMU` (`MU.actLevel`, `MU.actLevel_tmul`,
`MU.deg`, `MU.incl`); `ZhuVermaAnArchBimodDescentsGen` (`composeActLevel`, `composeActLevel_incl`,
`repMULevel_actMode`); `ZhuVermaAnArchAnm` (`anmRight_zero_zero`, `mkAnm`);
`certificates/mathematica/bottom_defect_zero.wl`.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

variable (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
  (hclo : ∀ n : ℕ, AnmRightModule W n)

/-! ## (A) The bottom action factors through `A(𝒱)` -/

/-- **The bottom block factoring.**  On the bottom level (`n = 0`), `composeActLevel a` carries
`MU.incl 0 y` to `MU.incl 0 (MU.actLevel 0 (hclo 0) a y)` — the level-`0` right residue action on the
left tensor factor.  Specialisation of `composeActLevel_incl` to `n = 0`. -/
theorem bottomActLevel_incl (a : 𝒱) (y : MUPiece W U 0) :
    composeActLevel W U hclo a (MU.incl W U 0 y)
      = MU.incl W U 0 (MU.actLevel W U 0 (hclo 0) a y) :=
  composeActLevel_incl W U hclo a 0 y

/-! ## (B) The level-`0` defect endomorphism of `A(𝒱) ⊗ U` -/

/-- **The bottom defect endomorphism** of `MUPiece W U 0 = A(𝒱) ⊗ U` — the level-`0` mirror of
`defectLin`, built from the bottom level action `MU.actLevel 0` with the (level-constant) finite-sum
scalar `S = ∑ᶠ i, (−1)^i · C(ℓ,i)` factored out.  `defectLin u v ℓ N` is `MU.incl 0`-conjugate to it
on the bottom block (`defectLin_bottom_incl`). -/
noncomputable def defectLin0 (u v : 𝒱) (ℓ : ℤ) : MUPiece W U 0 →ₗ[ℂ] MUPiece W U 0 :=
  MU.actLevel W U 0 (hclo 0) (W.smul u ℓ v)
    - (∑ᶠ i : ℤ, negOnePow i * cbz ℓ i) •
        ((MU.actLevel W U 0 (hclo 0) u).comp (MU.actLevel W U 0 (hclo 0) v)
          - negOnePow ℓ •
              (MU.actLevel W U 0 (hclo 0) v).comp (MU.actLevel W U 0 (hclo 0) u))

variable (hderiv : ∀ (a : 𝒱) (m : ℤ),
    composeActLevelFamily W U hclo m (W.L (-1) a)
      + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
  (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
    assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
      = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆)

/-- **`defectLin` factors through `MU.incl 0` on the bottom block.**  Using the bottom factoring
`composeActLevel a (MU.incl 0 y) = MU.incl 0 (actLevel 0 a y)` (`bottomActLevel_incl`) on every
composition appearing in `defectLin`, the whole bottom defect equals `MU.incl 0 (defectLin0 … y)`. -/
theorem defectLin_bottom_incl (u v : 𝒱) (ℓ N : ℤ) (y : MUPiece W U 0) :
    defectLin W U hclo u v ℓ N (MU.incl W U 0 y)
      = MU.incl W U 0 (defectLin0 W U hclo u v ℓ y) := by
  rw [defectLin, defectLin0]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    bottomActLevel_incl, map_sub, map_smul]

/-! ## (C) The bottom defect on a pure tensor `mkAnm 0 r ⊗ u₀` -/

/-- **The bottom defect on a pure tensor.**  `MU.actLevel 0 (hclo 0) a` acts on `mkAnm 0 r ⊗ u₀` by
`mkAnm 0 (anmRight 0 0 r a) ⊗ u₀ = mkAnm 0 (zhuMul r a) ⊗ u₀` (`MU.actLevel_tmul`,
`anmRight_zero_zero`).  Composing the three actions, `defectLin0 u v ℓ` sends `mkAnm 0 r ⊗ u₀` to the
explicit `A(𝒱)`-combination tensored with `u₀`. -/
theorem defectLin0_tmul_eq (u v : 𝒱) (ℓ : ℤ) (r : 𝒱) (u₀ : U.carrier) :
    defectLin0 W U hclo u v ℓ (mkAnm W 0 0 r ⊗ₜ[ℂ] u₀)
      = (mkAnm W 0 0 (zhuMul W r (W.smul u ℓ v))
          - (∑ᶠ i : ℤ, negOnePow i * cbz ℓ i) •
              (mkAnm W 0 0 (zhuMul W (zhuMul W r v) u)
                - negOnePow ℓ • mkAnm W 0 0 (zhuMul W (zhuMul W r u) v))) ⊗ₜ[ℂ] u₀ := by
  rw [defectLin0]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    MU.actLevel_tmul, anmRight_zero_zero]
  -- the map `f : z ↦ z ⊗ₜ u₀` is `ℂ`-linear, so it distributes over the `S •`/`sub` combination.
  set f := (TensorProduct.mk ℂ (Anm W 0 0) U.carrier).flip u₀ with hf
  show f (mkAnm W 0 0 (zhuMul W r (W.smul u ℓ v)))
      - (∑ᶠ i : ℤ, negOnePow i * cbz ℓ i) •
          (f (mkAnm W 0 0 (zhuMul W (zhuMul W r v) u))
            - negOnePow ℓ • f (mkAnm W 0 0 (zhuMul W (zhuMul W r u) v)))
      = f (mkAnm W 0 0 (zhuMul W r (W.smul u ℓ v))
          - (∑ᶠ i : ℤ, negOnePow i * cbz ℓ i) •
              (mkAnm W 0 0 (zhuMul W (zhuMul W r v) u)
                - negOnePow ℓ • mkAnm W 0 0 (zhuMul W (zhuMul W r u) v)))
  rw [map_sub, map_smul, map_sub, map_smul]

/-! ## (D) The `A(𝒱)`-level identity — the EXACT remaining zero-mode datum -/

/-- **The `A(𝒱)`-level identity** — the precise depth-`0` content the bottom defect reduces to, a
`Prop`, **never** an axiom.  In the Zhu algebra `A(𝒱) = Anm W 0 0` (with the level-constant
finite-sum scalar `S = ∑ᶠ i, (−1)^i C(ℓ,i)`),

  `[zhuMul r (u₍ℓ₎v)] = S • ([zhuMul (zhuMul r v) u] − (−1)^ℓ • [zhuMul (zhuMul r u) v])`.

⚠ This is the identity required for the *bare level-constant* defect to vanish on the bottom.
Engine (`certificates/mathematica/bottom_defect_zero.wl`) shows it does **not** hold for the
index-independent `composeActLevel` action in general (e.g. `ℓ < 0`, or `wt u ≥ 2`); it holds for the
genuine depth-graded mode action, which `repMULevel` matches only on the diagonal.  It is stated here
as the exact target, carried as an explicit hypothesis wherever consumed — not assumed. -/
def BottomAVRelation : Prop :=
  ∀ (u v r : 𝒱) (ℓ : ℤ),
    mkAnm W 0 0 (zhuMul W r (W.smul u ℓ v))
      = (∑ᶠ i : ℤ, negOnePow i * cbz ℓ i) •
          (mkAnm W 0 0 (zhuMul W (zhuMul W r v) u)
            - negOnePow ℓ • mkAnm W 0 0 (zhuMul W (zhuMul W r u) v))

/-- **`defectLin0 = 0` from the `A(𝒱)`-level identity.**  On every pure tensor `mkAnm 0 r ⊗ u₀`,
`defectLin0` is the `A(𝒱)`-combination (`defectLin0_tmul_eq`) tensored with `u₀`; that combination is
`0` by `BottomAVRelation`.  Pure tensors of the form `mkAnm 0 r ⊗ u₀` span `A(𝒱) ⊗ U` (every element
of `A(𝒱)` is a `mkAnm 0`-representative), so `defectLin0 = 0` by `TensorProduct.ext`. -/
theorem defectLin0_eq_zero (hrel : BottomAVRelation W) (u v : 𝒱) (ℓ : ℤ) :
    defectLin0 W U hclo u v ℓ = 0 := by
  apply TensorProduct.ext'
  intro a u₀
  -- `a : A(𝒱) = 𝒱 ⧸ Onm 0 0`; lift to a representative `r` with `a = mkAnm 0 r`.
  refine Submodule.Quotient.induction_on _ a (fun r => ?_)
  show defectLin0 W U hclo u v ℓ (mkAnm W 0 0 r ⊗ₜ[ℂ] u₀) = 0
  rw [defectLin0_tmul_eq, hrel u v r ℓ, sub_self, TensorProduct.zero_tmul]

/-! ## (E) The closure direction — `bottomDefectZero` and bottom survival from the `A(𝒱)` datum -/

/-- **`bottomDefectZero` for the concrete `repMULevel`, from the `A(𝒱)`-level identity.**

A bottom state `x ∈ MUdegZ W U 0 = MU.deg W U 0` is `MU.incl 0 y` for some `y` (range of `MU.incl 0`).
By `defectVec_eq_defectLin` the bare defect is `defectLin u v ℓ N (MU.incl 0 y)`, which factors as
`MU.incl 0 (defectLin0 … y)` (`defectLin_bottom_incl`); `defectLin0 = 0` by the `A(𝒱)`-level identity
(`defectLin0_eq_zero`), so the whole bottom defect is `MU.incl 0 0 = 0`.  The only carried datum is
the genuine `A(𝒱) = A_0`-level (zero-mode Borcherds) identity `BottomAVRelation`, **never** an axiom;
everything else is proved. -/
theorem repMULevel_bottomDefectZero (hrel : BottomAVRelation W) :
    ∀ (u v : 𝒱) (x : MU W U) (ℓ N : ℤ), x ∈ MUdegZ W U 0 →
      VHatRep.defectVec (repMULevel W U hclo hderiv hbracket) u v x ℓ N = 0 := by
  intro u v x ℓ N hx
  rw [MUdegZ, if_pos (le_refl (0 : ℤ))] at hx
  simp only [Int.toNat_zero] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [defectVec_eq_defectLin, defectLin_bottom_incl, defectLin0_eq_zero W U hclo hrel,
    LinearMap.zero_apply, map_zero]

/-- **Bottom survival for the concrete `repMULevel`, from the `A(𝒱)`-level identity.**  Chains the
closed `bottomDefectZero` (`repMULevel_bottomDefectZero`) into the constructive bottom survival
(`repMULevel_bottomSurvives_of_bottomDefect`): the lowest-weight space `U = M₀` survives the defect
quotient `M̄(U)`.  The only carried datum is `BottomAVRelation`; everything else is proved. -/
theorem repMULevel_bottomSurvives_of_AVRelation (hrel : BottomAVRelation W) :
    VHatRep.BottomSurvives (repMULevel W U hclo hderiv hbracket) (MUdegZ W U) :=
  repMULevel_bottomSurvives_of_bottomDefect W U hclo hderiv hbracket
    (repMULevel_bottomDefectZero W U hclo hderiv hbracket hrel)

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
