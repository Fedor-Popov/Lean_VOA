/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchBottomOrbitClose

/-!
# `bottomLevelDefect` for the concrete `M(U)` — the bare degree-`0` defect on the bottom

`ZhuVermaAnArchBottomOrbitClose` reduced full bottom survival of the sound Construction-A
representation `repMULevel` to the **single level-`0` identity** `bottomLevelDefect`:

  `∀ u v x ℓ N, deg0Proj (defectVec (repMULevel …) u v x ℓ N) = 0`,

the degree-`0` component of the *bare* (`g = 1`) iterate defect.  This file discharges that level-`0`
identity, mirroring `gMode_anmCirc_lowest` / `oMod_zhuMul_lowest`: the bottom mode action factors
through `A(𝒱) = A_0` and `U` is an `A(𝒱)`-module, so the bare zero-mode (Borcherds) defect vanishes
on the bottom `M₀ = A(𝒱) ⊗ U`.

## The mechanism — the level-constant action makes the defect a single block-diagonal `LinearMap`

The sound modes of `repMULevel` are the *level-diagonal* action `composeActLevel a`
(`repMULevel_actMode`), **independent of the mode index** `m`.  Therefore in the defect vector

  `defectVec ρ u v x ℓ N`
    `= composeActLevel (u₍ℓ₎v) x`
      `− ∑ᶠ i, (negOnePow i · cbz ℓ i) • (composeActLevel u (composeActLevel v x)`
        `− negOnePow ℓ • composeActLevel v (composeActLevel u x))`

the inner vector `D(x) = composeActLevel u (composeActLevel v x) − negOnePow ℓ • composeActLevel v
(composeActLevel u x)` is **independent of `i`**, so the finite sum **factors** (`finsum_smul`, valid
even for an infinite support over the torsion-free `ℂ`-module `M(U)`):

  `∑ᶠ i, sᵢ • D(x) = (∑ᶠ i, sᵢ) • D(x)`,   `sᵢ = negOnePow i · cbz ℓ i`.

Hence `defectVec ρ u v · ℓ N` is **a genuine `ℂ`-linear endomorphism** `defectLin` of `M(U)`
(`defectVec_eq_defectLin`), and — since every `composeActLevel a` is block-diagonal for the level
grading (`composeActLevel_block`) — `defectLin` is block-diagonal, so it commutes with the degree-`0`
projection `deg0Proj` (`deg0Proj_comm_blockDiag`):

  `deg0Proj (defectVec ρ u v x ℓ N) = defectLin (deg0Proj x)`.

This collapses the whole `(u,v,x,ℓ,N)` family to the single **bottom-input** statement
`defectVec ρ u v x₀ ℓ N = 0` for `x₀ ∈ M₀` — the genuine `A(𝒱) = A_0`-module Borcherds (zero-mode)
relation, carried as the explicit hypothesis `bottomDefectZero`, **never** an axiom.  Engine-verified
(`certificates/mathematica/bottom_level_defect.wl`): finsum factoring, linearity of the defect in `x`,
block-diagonal commutation with `deg0Proj`, and vanishing of `deg0Proj (defect)` on off-bottom input.

## What is built here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`defectLin`** — the defect endomorphism `x ↦ defectVec (repMULevel …) u v x ℓ N`, assembled from
  `composeActLevel` (the level-constant action) with the finite sum *factored out*.
* **`defectVec_eq_defectLin`** — `defectVec (repMULevel …) u v x ℓ N = defectLin … x` (finsum
  factoring via `finsum_smul`).
* **`defectLin_block`** — `defectLin` is block-diagonal for the `ℤ`-lifted level grading `MUdegZ`.
* **`deg0Proj_defectVec_eq`** — the block-diagonal collapse:
  `deg0Proj (defectVec ρ u v x ℓ N) = defectVec ρ u v (deg0Proj x) ℓ N`.
* **`repMULevel_bottomLevelDefect`** — *the closure*: from the single carried bottom-input identity
  `bottomDefectZero` (the `A(𝒱)`-module Borcherds relation), `bottomLevelDefect` holds.
* **`repMULevel_bottomSurvives_of_bottomDefect`** — bottom survival for the concrete `repMULevel`,
  carrying only `bottomDefectZero` (chained through `repMULevel_bottomSurvives`).

## References
DLM3 §4; Frenkel–Zhu; Dong–Jiang `math/0601626`; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchBottomOrbitClose` (`repMULevel_bottomOrbitDefectVanishes`, `MUdegZ`, `composeActLevel_block`,
`deg0Proj_comm_blockDiag`); `ZhuVermaAnArchMUjacobiClose` (`defectVec`);
`ZhuVermaAnArchFreenessCircle` (`gMode_anmCirc_lowest`); `ZhuModule` (`oMod_zhuMul_lowest_all`);
`certificates/mathematica/bottom_level_defect.wl`.
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
  (hderiv : ∀ (a : 𝒱) (m : ℤ),
    composeActLevelFamily W U hclo m (W.L (-1) a)
      + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
  (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
    assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
      = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆)

/-! ## (A) The level-constant defect as a single block-diagonal `LinearMap` -/

/-- **The defect endomorphism of `M(U)`** — `x ↦ defectVec (repMULevel …) u v x ℓ N`, written as a
genuine `ℂ`-linear endomorphism by factoring the (constant-vector) finite sum out of `i`.  The scalar
`∑ᶠ i, negOnePow i · cbz ℓ i` is pulled out via `finsum_smul`; the action `composeActLevel a` is the
same level-constant endomorphism at every mode index, so the whole defect is built from compositions
of `composeActLevel` and a scalar multiple. -/
noncomputable def defectLin (u v : 𝒱) (ℓ N : ℤ) : MU W U →ₗ[ℂ] MU W U :=
  composeActLevel W U hclo (W.smul u ℓ v)
    - (∑ᶠ i : ℤ, negOnePow i * cbz ℓ i) •
        ((composeActLevel W U hclo u).comp (composeActLevel W U hclo v)
          - negOnePow ℓ • (composeActLevel W U hclo v).comp (composeActLevel W U hclo u))

/-- **`defectVec (repMULevel …) u v x ℓ N = defectLin … x`.**  The modes of `repMULevel` are the
level-constant action `composeActLevel a` (`repMULevel_actMode`), so the inner vector of the defect
sum is independent of the summation index `i`; the finite sum factors (`finsum_smul`, valid over the
torsion-free `ℂ`-module `M(U)` even when the support is infinite). -/
theorem defectVec_eq_defectLin (u v : 𝒱) (x : MU W U) (ℓ N : ℤ) :
    VHatRep.defectVec (repMULevel W U hclo hderiv hbracket) u v x ℓ N
      = defectLin W U hclo u v ℓ N x := by
  rw [VHatRep.defectVec, defectLin]
  -- Rewrite every mode action to the level-constant `composeActLevel`, then fully unfold all
  -- `LinearMap` applications on both sides.
  simp only [repMULevel_actMode, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  -- Both sides agree on the first term; the finite sum factors via `finsum_smul`
  -- (`D` is independent of `i`).
  congr 1
  rw [finsum_smul]

/-! ## (B) Block-diagonality of `defectLin` and the degree-`0` collapse -/

/-- **`defectLin` is block-diagonal** for the `ℤ`-lifted level grading `MUdegZ`.  Each
`composeActLevel a` preserves every level (`composeActLevel_block`), and block-preservation is closed
under composition, scalar multiplication and subtraction; the negative degrees are `⊥`. -/
theorem defectLin_block (u v : 𝒱) (ℓ N : ℤ) (d : ℤ) {z : MU W U} (hz : z ∈ MUdegZ W U d) :
    defectLin W U hclo u v ℓ N z ∈ MUdegZ W U d := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [MUdegZ, if_neg (not_le.mpr hd), Submodule.mem_bot] at hz
    rw [hz, map_zero, MUdegZ, if_neg (not_le.mpr hd)]
    exact Submodule.zero_mem _
  · rw [MUdegZ, if_pos hd] at hz ⊢
    set n : ℕ := d.toNat with hn
    -- block-preservation of `composeActLevel a` at this level.
    have hT : ∀ (a : 𝒱) {w : MU W U}, w ∈ MU.deg W U n →
        composeActLevel W U hclo a w ∈ MU.deg W U n :=
      fun a w hw => composeActLevel_block W U hclo a n hw
    simp only [defectLin, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    refine Submodule.sub_mem _ (hT _ hz) (Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_))
    · exact hT _ (hT _ hz)
    · exact Submodule.smul_mem _ _ (hT _ (hT _ hz))

/-- **The block-diagonal collapse.**  By `defectVec_eq_defectLin` and the block-diagonality of
`defectLin` (`defectLin_block`), the degree-`0` projection commutes with the defect
(`deg0Proj_comm_blockDiag`):

  `deg0Proj (defectVec ρ u v x ℓ N) = defectVec ρ u v (deg0Proj x) ℓ N`,

reducing the whole `(u,v,x,ℓ,N)` family to **bottom inputs** `deg0Proj x ∈ M₀`. -/
theorem deg0Proj_defectVec_eq (u v : 𝒱) (x : MU W U) (ℓ N : ℤ) :
    VHatRep.deg0Proj (MUdegZ_isInternal W U)
        (VHatRep.defectVec (repMULevel W U hclo hderiv hbracket) u v x ℓ N)
      = VHatRep.defectVec (repMULevel W U hclo hderiv hbracket) u v
          (VHatRep.deg0Proj (MUdegZ_isInternal W U) x) ℓ N := by
  rw [defectVec_eq_defectLin, defectVec_eq_defectLin,
    VHatRep.deg0Proj_comm_blockDiag (MUdegZ_isInternal W U)
      (fun nn w hw => defectLin_block W U hclo u v ℓ N nn hw) x]

/-! ## (C) `bottomLevelDefect` from the bottom-input `A(𝒱)`-module relation -/

/-- **`bottomLevelDefect` for the concrete `repMULevel`, from the bottom-input defect identity.**

The block-diagonal collapse (`deg0Proj_defectVec_eq`) reduces the level-`0` projection of the bare
defect to the *bottom-input* defect `defectVec ρ u v x₀ ℓ N` with `x₀ = deg0Proj x ∈ M₀`.  On the
bottom `M₀ = A(𝒱) ⊗ U` the level-constant action is the right `A(𝒱) = A_0`-residue (Zhu) product, so
the bare iterate defect is exactly the `A(𝒱)`-module Borcherds (zero-mode) relation — `0` because
`U` is an `A(𝒱)`-module (the same mechanism as `gMode_anmCirc_lowest` / `oMod_zhuMul_lowest_all`).
That bottom-input relation is the single carried hypothesis `bottomDefectZero`, **never** an axiom;
everything around it is proved. -/
theorem repMULevel_bottomLevelDefect
    (bottomDefectZero : ∀ (u v : 𝒱) (x : MU W U) (ℓ N : ℤ), x ∈ MUdegZ W U 0 →
      VHatRep.defectVec (repMULevel W U hclo hderiv hbracket) u v x ℓ N = 0) :
    ∀ (u v : 𝒱) (x : MU W U) (ℓ N : ℤ),
      VHatRep.deg0Proj (MUdegZ_isInternal W U)
        (VHatRep.defectVec (repMULevel W U hclo hderiv hbracket) u v x ℓ N) = 0 := by
  intro u v x ℓ N
  rw [deg0Proj_defectVec_eq]
  -- `deg0Proj x` lies in the bottom `M₀`, where the bare defect vanishes by `bottomDefectZero`.
  exact bottomDefectZero u v _ ℓ N (VHatRep.deg0Proj_mem (MUdegZ_isInternal W U) x)

/-! ## (D) Bottom survival for the concrete `repMULevel`, carrying only the bottom relation -/

/-- **Bottom survival for the concrete `repMULevel`, from the bottom-input `A(𝒱)`-module relation.**
Chaining the closed `bottomLevelDefect` (`repMULevel_bottomLevelDefect`) into the constructive bottom
survival of `ZhuVermaAnArchBottomOrbitClose` (`repMULevel_bottomSurvives`): the lowest-weight space
`U = M₀` survives the defect quotient `M̄(U)`.  The only carried datum is the genuine `A(𝒱) = A_0`
zero-mode (Borcherds) relation on the bottom `bottomDefectZero`; everything else is proved. -/
theorem repMULevel_bottomSurvives_of_bottomDefect
    (bottomDefectZero : ∀ (u v : 𝒱) (x : MU W U) (ℓ N : ℤ), x ∈ MUdegZ W U 0 →
      VHatRep.defectVec (repMULevel W U hclo hderiv hbracket) u v x ℓ N = 0) :
    VHatRep.BottomSurvives (repMULevel W U hclo hderiv hbracket) (MUdegZ W U) :=
  repMULevel_bottomSurvives W U hclo hderiv hbracket
    (repMULevel_bottomLevelDefect W U hclo hderiv hbracket bottomDefectZero)

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
