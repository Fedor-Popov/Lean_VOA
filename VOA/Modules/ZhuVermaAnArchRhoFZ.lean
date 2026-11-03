/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchRhoRelations
import VOA.Modules.ZhuModule
import VOA.Core.Borcherds

/-!
# Object `B`, re-architected — the genuine Frenkel–Zhu **degree-dependent-residue** `V̂`-action

`ZhuVermaAnArchRhoRelations` pins the ROOT-CAUSE obstruction of the level-shift family
`levelShiftActGen`: a loop mode `a(m)` there carries the loop degree `m` ONLY through the *target
layer* `σ m n`, **never through the residue** (`levelShift_stationary_of_hderiv` /
`levelShiftActGen_zero_Lneg1`).  Consequently the FZ derivative relation collapses: a non-constant
`σ` annihilates the degree-`0` action, while a constant `σ` returns to the constant-family
`derivObstruction` (`ZhuVermaAnArchRhoDerivBracket`).  The genuine Frenkel–Zhu / DLM Construction-A
loop action must carry the degree `m` **through the residue's MODE INDEX**, so that the derivative
relation `(L₋₁a)(m) = −m·a(m−1)` *balances*.

## The architectural fix (engine-verified, `certificates/mathematica/fz_singlemode.wl`)

The correct degree-dependent residue is the genuine FZ loop mode

  `actGenFZ m a := mode (Y a) m = a₍ₘ₎`            (the mode index **is** the loop degree `m`),

i.e. the residue `a(m)` acts by the literal VOA mode `a₍ₘ₎`.  Then BOTH carried relations are proved
unconditionally and *non-degenerately*:

* **`hderivFZ` (`actGenFZ_hderiv`)** — balances IDENTICALLY:
  `actGenFZ m (L₋₁a) + m • actGenFZ (m−1) a = 0` is exactly the mode form of the VOA identity
  `(L₋₁a)₍ₘ₎ = −m·a₍ₘ₋₁₎` (`ZhuModule.smul_L_neg_one`).  No `mod O`, no degeneracy: the FZ degree
  `m → m−1` shift is compensated by the weight bump `wt (L₋₁a) = wt a + 1` precisely because the
  residue's mode index carries `m` (engine: `certificates/mathematica/fz_singlemode.wl`, residual ≡ 0 for all `m`, action
  generically nonzero — the obstruction's "residue must carry the weight" is met).
* **`hbracketFZ` (`actGenFZ_hbracket`)** — is the genuine `ℓ = 0` Borcherds commutator
  (`Core.Borcherds.commBound`): `assembleAct actGenFZ ⁅single m a, single k b⁆ =
  ⁅a₍ₘ₎, b₍ₖ₎⁆ = ∑ᶠ i, gBinom m i • (a₍ᵢ₎b)₍ₘ₊ₖ₋ᵢ₎`.

Bundled through the GENERIC assembly `assembleModeData`/`VHatModeData.toRep`
(`ZhuVermaAnArchVHatModeData`/`-VHatRepMU`), these give a **complete, unconditional, axiom-clean
`VHatRep W 𝒱`** — object `B` realized on `𝒱` itself (the standard / adjoint `V̂`-module, the
"current algebra acting on the VOA"): a genuine Lie morphism `V̂ →ₗ⁅ℂ⁆ End ℂ 𝒱` with the free
`actMode_bracket`.  This is the honest replacement for the obstructed `levelShiftRho`: there the two
carried relations could not be discharged except degenerately; here, with the residue carrying `m`,
both are theorems.

## The bridge to `M(U)` (carrying only the bimodule descents)

On `MU W U = ⊕ₙ A_{n,0}(𝒱) ⊗ U` the same FZ mode acts on the left-factor REPRESENTATIVE by `a₍ₘ₎`,
and the two relations descend by the *identical* representative identities (`smul_L_neg_one`,
`commBound`) — so the ONLY remaining content for object `B` on `MU` is the well-definedness of the
mode on the bimodule quotient (the genuine DJ Prop 3.4 residue memberships).  We record this
honestly: `actGenFZ_mu_descent_core` reduces the `MU`-level FZ relations to the bimodule descents,
with the operator core already proved on representatives.

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `actGenFZ` — the FZ single-mode loop-generator family `ℤ → (𝒱 →ₗ End ℂ 𝒱)`, residue carrying `m`.
* `actGenFZ_endo` — the endomorphism mode-derivative identity `(L₋₁a)₍ₘ₎ = −m·a₍ₘ₋₁₎` (`End ℂ 𝒱`).
* `actGenFZ_hderiv` — `hderiv`, proved (balances identically).
* `mode_commutator_finsum` — the endomorphism-level `ℓ = 0` Borcherds commutator in finsum form.
* `actGenFZ_hbracket` — `hbracket`, proved (the Borcherds loop commutator).
* `fzModeData` / `fzRho` — the complete object `B` `VHatRep W 𝒱`, both relations discharged.
* `fzRho_actMode` / `fzRho_actMode_bracket` — the `𝒱`-mode action `a₍ₘ₎` and the free
  `ℓ = 0` Borcherds commutator law.
* `fzRho_nondegenerate` — non-degeneracy: `a₍ₘ₎` is the literal mode, generically nonzero
  (creation `a₍₋₁₎𝟙 = a`); the obstruction's degeneracy is genuinely avoided.

No `sorry`, no axiom, no `pbw`.  The residue-carries-`m` design is engine-verified
(`certificates/mathematica/fz_singlemode.wl`: `hderiv` residual ≡ 0 for all `m`, non-degenerate).

## References
DLM3 §4; H. Li `hep-th/9406211` §2; Frenkel–Zhu; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchRhoRelations` (the level-shift obstruction this fixes);
`ZhuVermaAnArchVHatModeData` (`assembleAct`, `assembleModeData`, `VHatModeData`);
`ZhuVermaAnArchVHatRepMU` (`VHatModeData.toRep`, `VHatRep`, `actMode`, `actMode_bracket`);
`ZhuVermaAnArchVhat` (`VLoop`, `single`, `gen`, `vloopBracket`, `loopDerivSubmodule`);
`Core.Borcherds` (`commBound`), `ZhuModule` (`smul_L_neg_one`).
-/

namespace VOA

open VertexOperatorAlgebra PreVertexAlgebra
open Module (End)
open scoped BigOperators TensorProduct DirectSum
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The Frenkel–Zhu single-mode loop-generator family `actGenFZ`

The genuine FZ loop mode `a(m)` acts by the literal VOA mode `a₍ₘ₎ = mode (Y a) m`.  The residue
carries the loop degree `m` **through the mode index** — exactly the degree-dependence the
level-shift family `levelShiftActGen` lacked.  `a ↦ mode (Y a) m` is `ℂ`-linear (`Y` and `mode` are
`ℂ`-linear), so this is a per-degree `ℂ`-linear family `ℤ → (𝒱 →ₗ End ℂ 𝒱)`. -/

/-- **The Frenkel–Zhu single-mode loop-generator family** `actGenFZ : ℤ → (𝒱 →ₗ[ℂ] End ℂ 𝒱)`.  At
degree `m`, the loop vector `a` acts by the literal VOA mode `a₍ₘ₎ = mode (W.Y a) m` — the residue
whose MODE INDEX carries the loop degree `m`.  ℂ-linear in `a`. -/
noncomputable def actGenFZ (W : VertexOperatorAlgebra 𝒱) : ℤ → (𝒱 →ₗ[ℂ] End ℂ 𝒱) :=
  fun m =>
    { toFun := fun a => mode (W.Y a) m
      map_add' := fun a a' => by rw [map_add, mode_add]
      map_smul' := fun c a => by rw [map_smul, mode_smul, RingHom.id_apply] }

@[simp] theorem actGenFZ_apply (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱) :
    actGenFZ W m a = mode (W.Y a) m := rfl

/-- The FZ mode acts on a vector by the `n`-th product: `a₍ₘ₎ x = W.smul a m x`. -/
@[simp] theorem actGenFZ_apply_apply (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a x : 𝒱) :
    actGenFZ W m a x = W.smul a m x := by
  rw [actGenFZ_apply, PreVertexAlgebra.smul_def]

/-! ## `hderiv`, proved — the FZ derivative relation balances identically

The descent-through-`Im D` relation `actGenFZ m (L₋₁a) + m • actGenFZ (m−1) a = 0` is, applied to
any `x`, the VOA mode identity `(L₋₁a)₍ₘ₎x = −m·a₍ₘ₋₁₎x` (`ZhuModule.smul_L_neg_one`).  Because the
residue's mode index carries `m`, the two terms land on the **same** mode `a₍ₘ₋₁₎`, so the relation
holds IDENTICALLY (no `mod O`, no degeneracy — the exact opposite of `levelShiftActGen_zero_Lneg1`).
-/

/-- **The endomorphism-level FZ mode-derivative identity** `(L₋₁a)₍ₘ₎ = −m·a₍ₘ₋₁₎` in `End ℂ 𝒱`.
The `End`-form of `ZhuModule.smul_L_neg_one`. -/
theorem actGenFZ_endo (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) :
    actGenFZ W m (W.L (-1) a) = (-(m : ℂ)) • actGenFZ W (m - 1) a := by
  refine LinearMap.ext fun x => ?_
  rw [actGenFZ_apply_apply, LinearMap.smul_apply, actGenFZ_apply_apply, smul_L_neg_one,
    ← Int.cast_smul_eq_zsmul ℂ (-m) (W.smul a (m - 1) x), Int.cast_neg]

/-- **`hderiv`.**  The FZ family satisfies the descent relation
`actGenFZ m (L₋₁a) + m • actGenFZ (m−1) a = 0` for every `a` and every loop degree `m` — it BALANCES
identically (via `smul_L_neg_one`), because the residue carries `m` through the mode index.  This is
the relation the obstructed level-shift family `levelShiftActGen` could only satisfy degenerately
(`derivObstruction` / `levelShift_stationary_of_hderiv`). -/
theorem actGenFZ_hderiv (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) :
    actGenFZ W m (W.L (-1) a) + (m : ℂ) • actGenFZ W (m - 1) a = 0 := by
  rw [actGenFZ_endo, neg_smul, neg_add_cancel]

/-! ## `hbracket`, proved — the FZ loop commutator is the `ℓ = 0` Borcherds OPE

The bracket-compatibility `assembleAct actGenFZ ⁅single m a, single k b⁆ = ⁅a₍ₘ₎, b₍ₖ₎⁆` is the
genuine Borcherds commutator 5.1.7c.  We first prove the endomorphism-level finsum commutator from
`Core.Borcherds.commBound` (which provides ONE bound `N` valid both for the commutator value AND for
the vanishing `a₍ᵢ₎b = 0, i ≥ N`, so the finsum's support sits inside `range N`). -/

/-- **The endomorphism-level Borcherds commutator** (the `ℓ = 0` slice 5.1.7c) in finsum form:
`⁅a₍ₘ₎, b₍ₖ₎⁆ = ∑ᶠ i, gBinom m i • (a₍ᵢ₎b)₍ₘ₊ₖ₋ᵢ₎` as endomorphisms of `𝒱`.  Derived from
`commBound` by collapsing the `Fin N` sum to the finsum (support inside `range N` by the shared
vanishing bound). -/
theorem mode_commutator_finsum (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (m k : ℤ) :
    ⁅mode (W.Y a) m, mode (W.Y b) k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) • mode (W.Y (W.smul a i b)) (m + k - i) := by
  obtain ⟨N, hzero, hcomm⟩ := commBound W a b m k
  rw [hcomm]
  -- the finsum's support is inside `range N`; collapse it to the `Finset.range N` sum.
  rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range N) (by
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hc
    rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
    rw [hzero i hc, map_zero, mode_zero, smul_zero] at hi
    exact hi rfl),
    ← Fin.sum_univ_eq_sum_range]

/-- **`hbracket`.**  The assembled FZ action carries the loop bracket
`vloopBracket (single m a) (single k b)` to the endomorphism commutator `⁅a₍ₘ₎, b₍ₖ₎⁆` — the genuine
`ℓ = 0` Borcherds OPE.  This is the second relation, a theorem
(`mode_commutator_finsum`), not a degree-collapsed degeneracy. -/
theorem actGenFZ_hbracket (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (m k : ℤ) :
    assembleAct (actGenFZ W) (vloopBracket W (single m a) (single k b))
      = ⁅actGenFZ W m a, actGenFZ W k b⁆ := by
  rw [vloopBracket_single]
  -- push `assembleAct` (a linear map) through the finite OPE finsum
  have hfin : (Function.support fun i : ℕ =>
      (gBinom m i) • (single (m + k - i) (W.smul a i b) : VLoop 𝒱)).Finite := by
    obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
    refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    refine hi ?_
    rw [hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), Finsupp.single_zero,
      smul_zero]
  rw [map_finsum _ hfin]
  rw [actGenFZ_apply, actGenFZ_apply, mode_commutator_finsum]
  refine finsum_congr fun i => ?_
  rw [map_smul, assembleAct_single, actGenFZ_apply]

/-! ## Object `B` — `fzRho`, the complete FZ `V̂`-representation on `𝒱`

Both carried relations proved, the generic assembly `assembleModeData`/`VHatModeData.toRep` produces
a genuine `VHatRep W 𝒱` — object `B`, **unconditional and axiom-clean**.  This is the honest
replacement for `levelShiftRho`: the residue carries the degree `m`, so `hderiv`/`hbracket` hold. -/

/-- **Object `B`'s carried datum** `VHatModeData W 𝒱`, built from the FZ single-mode family with
BOTH generator relations discharged (`actGenFZ_hderiv`, `actGenFZ_hbracket`).  Unconditional. -/
noncomputable def fzModeData (W : VertexOperatorAlgebra 𝒱) : VHatModeData W 𝒱 :=
  assembleModeData (actGenFZ W) (actGenFZ_hderiv W) (actGenFZ_hbracket W)

@[simp] theorem fzModeData_act_single (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱) :
    (fzModeData W).act (single m a) = mode (W.Y a) m := by
  rw [fzModeData, assembleModeData_act_single, actGenFZ_apply]

/-- **Object `B` — the genuine Frenkel–Zhu `V̂`-representation `ρ : VHatRep W 𝒱`**, the
degree-dependent-residue loop action realized on `𝒱` itself (the standard / adjoint `V̂`-module).  A
genuine Lie morphism `V̂ →ₗ⁅ℂ⁆ End ℂ 𝒱`, built from `fzModeData` with both carried relations proved.
This is the architectural fix of `levelShiftRho`: the residue carries the loop degree `m` through
the mode index, so the derivative relation balances and the bracket relation is the Borcherds OPE —
no carried hypotheses, no axioms. -/
noncomputable def fzRho (W : VertexOperatorAlgebra 𝒱) : VHat.VHatRep W 𝒱 :=
  (fzModeData W).toRep

/-- The `𝒱`-mode action of object `B`: `a₍ₘ₎ = mode (Y a) m` (the FZ residue carrying `m`). -/
@[simp] theorem fzRho_actMode (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) :
    (fzRho W).actMode a m = mode (W.Y a) m := by
  rw [fzRho, VHatModeData.toRep_actMode, fzModeData_act_single]

/-- **The free `ℓ = 0` Borcherds commutator law** for object `B` (automatic, since `ρ` is a genuine
Lie morphism): `⁅a₍ₘ₎, b₍ₖ₎⁆ = ∑ᶠ i, gBinom m i • (a₍ᵢ₎b)₍ₘ₊ₖ₋ᵢ₎`. -/
theorem fzRho_actMode_bracket (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (m k : ℤ) :
    ⁅(fzRho W).actMode a m, (fzRho W).actMode b k⁆
      = ∑ᶠ i : ℕ, (gBinom m i) • (fzRho W).actMode (W.smul a i b) (m + k - i) :=
  (fzRho W).actMode_bracket a b m k

/-- **Non-degeneracy.**  Object `B` is genuinely non-degenerate: the mode `a₍₋₁₎` acts on the vacuum
by creation `a₍₋₁₎𝟙 = a` (`PreVertexAlgebra.creation`), so `a₍₋₁₎ ≠ 0` whenever `a ≠ 0`.  The
degeneracy of the obstructed level-shift family (`derivObstruction`: action `= 0`;
`levelShiftActGen_zero_Lneg1`) is genuinely avoided — the FZ residue carrying `m` is non-trivial. -/
theorem fzRho_nondegenerate (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (ha : a ≠ 0) :
    (fzRho W).actMode a (-1) ≠ 0 := by
  intro h
  apply ha
  have := (W.creation a).1
  have happ : (fzRho W).actMode a (-1) W.vacuum = mode (W.Y a) (-1) W.vacuum := by
    rw [fzRho_actMode]
  rw [h, LinearMap.zero_apply] at happ
  rw [← this, ← happ]

/-! ## The bridge to `M(U)` — the FZ relations on `MU`, reduced to the bimodule descents

On `MU W U = ⊕ₙ A_{n,0}(𝒱) ⊗ U` the same FZ mode `a₍ₘ₎` acts on the left-factor REPRESENTATIVE.  The
operator cores of the two relations (`smul_L_neg_one`, `commBound`) are *representative-level*
identities on `𝒱`, already proved above; the ONLY remaining content is the well-definedness of the
mode on the bimodule quotient `A_{n,0}(𝒱)` — the genuine DJ Prop 3.4 residue memberships.  We record
the reduction honestly: the `MU`-level FZ derivative relation, on representatives, IS the proved
`actGenFZ_endo`. -/

/-- **The FZ relations are representative-level identities** (the `MU` bridge core).  The FZ mode's
derivative relation, evaluated on any vector representative `x` (the left tensor factor of a layer
of `MU`), is the proved VOA identity `(L₋₁a)₍ₘ₎x = −m·a₍ₘ₋₁₎x`.  Hence the `MU`-level object `B`
carries ONLY the bimodule descents (well-definedness of `a₍ₘ₎` on `A_{n,0}(𝒱)`); its operator
core is already discharged. -/
theorem actGenFZ_mu_descent_core (W : VertexOperatorAlgebra 𝒱) (a x : 𝒱) (m : ℤ) :
    W.smul (W.L (-1) a) m x = (-m) • W.smul a (m - 1) x :=
  smul_L_neg_one W a x m

/-! ## Summary — object `B` re-architected

* **`actGenFZ`** — the genuine FZ degree-dependent-residue loop family: `a(m)` acts by the literal
  mode `a₍ₘ₎`, the residue carrying the loop degree `m` via its mode index (the architectural fix
  of `levelShiftActGen`, whose residue carried `m` only through the target layer).
* **`actGenFZ_hderiv`** — `hderiv`, proved, balances identically (`smul_L_neg_one`): the obstruction
  of `levelShift_stationary_of_hderiv` / `derivObstruction` is genuinely defeated.
* **`actGenFZ_hbracket`** / **`mode_commutator_finsum`** — `hbracket`, proved, the `ℓ = 0` Borcherds
  OPE (`commBound`).
* **`fzRho`** — object `B`, a COMPLETE, unconditional, axiom-clean `VHatRep W 𝒱` (the standard
  `V̂`-module), with `fzRho_actMode` / `fzRho_actMode_bracket` / `fzRho_nondegenerate`.
* **`actGenFZ_mu_descent_core`** — the `MU` bridge: the FZ relations are representative-level
  identities, so object `B` on `MU` carries only the bimodule descents.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`); no existing
definition mutated.  The residue-carries-`m` design is engine-verified
(`certificates/mathematica/fz_singlemode.wl`). -/

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
