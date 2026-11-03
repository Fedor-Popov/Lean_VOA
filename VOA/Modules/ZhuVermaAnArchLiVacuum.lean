/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLiRegRep
import VOA.Modules.ZhuVermaAnArchLiReduce
import VOA.Core.BilinearForm
import VOA.Modules.ZhuVermaAnArchDJ28PoleShift

/-!
# Li's regular representation — brick 2: the level-`(0,n)` vacuum space `Ω_{0,n}(D^{(-1)}(𝒱))`.

Brick 1 (`ZhuVermaAnArchLiRegRep`) built the full-dual FHL adjoint `Yadj`/`adjOp`.  This file builds the
**level-`(0,n)` DAGGER vacuum space** `VacuumSpace W n ⊆ 𝒱^*` as the concrete pole-order condition on
`Yadj` (Li arXiv 2205.05481, Def 3.4 / Prop 3.5, `m = 0`), and proves the sound inclusion
`AdjPoleSpace W n ⊆ Onm W n 0`.

Li's dagger Prop 3.5: `f ∈ (A^†_{n,0}(𝒱))^* = (O†_{n,0})^⊥` iff, for every homogeneous `v` of weight
`wt`, `x^{wt+n}(x+1)^{wt} Y^*(v,x) f ∈ 𝒱^*[[x]]`.  Reading off the coefficient of `x^{-1-s}` (mode
convention `Y^*(v,x)f = ∑_N (Yadj W wt v N f) x^{-N-1}`, `(x+1)^{wt} = ∑_j C(wt,j) x^j`) turns the pole
condition into the concrete mode identity

  `∑_{j=0}^{wt} C(wt,j) · (Yadj W wt v (wt+n+j+s) f) = 0`   for every `s ≥ 0`   (†)

— this is `vacMap`/`VacuumSpace` below.

⚠ **Scope correction (adversarially verified against Li §3–4).**  `VacuumSpace` encodes ONLY the pole
condition, so it annihilates the DAGGER ideal `O†_{n,0}` (circle span), which for `n ≥ 1` is STRICTLY
SMALLER than the repo's DIAMOND ideal `Onm W n 0 = O'_{n,0}` (circles ⊔ grading generators).  Li's full
diamond Prop 3.5 also imposes the grading eigen-clause `(L*(1)+L*(0))f = n·f` (Prop 4.1), which
`VacuumSpace` omits.  Consequently the P1/vacuum-route main theorems once stated here (`mUGradedAction_of_-
liVacuum`, `mUGradedAction_of_liPrimal`) were UNSOUND (their `LiProp35`/`AdjPoleSpace = Onm` hypotheses
are false for `n ≥ 1`) and have been REMOVED.  The SOUND route to `MUGradedAction` is
`ZhuVermaAnArchLiReduce.mUGradedAction_of_liDualStable` ⟸ `∀n, LiDualStable W n`, diamond-native and
(by `liDualStable_of_closure`) equal to the cross-level closure `CrossCircCore` — the genuine open
theorem the Li machinery adapters back onto, not a shortcut past it.

SOUND contributions of this file: the FHL adjoint `adjOp` (verified = the repo's proven `dualCompMap`),
the dagger vacuum space, and the PROVEN inclusion `adjPoleSpace_le_Onm` (via the FHL `x↔z⁻¹`
re-summation `adjPoleMap_eq_resHomSum` + `resHom_offdiag_mem_Onm`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
H. Li arXiv 2205.05481, Def 3.4 / Prop 3.5 / Prop 4.1 / Thm 3.2 / Lemma 3.14; FHL; Dong–Jiang
math/0601626.
-/

namespace VOA

open VertexOperatorAlgebra Submodule LinearMap
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The vacuum functional `vacMap` — the coefficient of `x^{-1-s}` in `x^{wt+n}(x+1)^{wt}Y^*(v,x)`. -/

/-- **Vacuum functional** at homogeneous weight `wt`, level `n`, mode `s`: the linear map on `𝒱^*`
sending `f` to the coefficient of `x^{-1-s}` in `x^{wt+n}(x+1)^{wt} Y^*(v,x) f`, i.e.
`∑_{j=0}^{wt} C(wt,j) · Yadj W wt v (wt+n+j+s) f`.  `f` lies in the level-`(0,n)` vacuum space iff this
vanishes for every homogeneous `v` and every `s ≥ 0` (`VacuumSpace`). -/
noncomputable def vacMap (W : VertexOperatorAlgebra 𝒱) (n wt : ℕ) (v : 𝒱) (s : ℕ) :
    Module.Dual ℂ 𝒱 →ₗ[ℂ] Module.Dual ℂ 𝒱 :=
  ∑ j ∈ Finset.range (wt + 1),
    (Nat.choose wt j : ℂ) • Yadj W (wt : ℤ) v ((wt : ℤ) + (n : ℤ) + (j : ℤ) + (s : ℤ))

/-- **The level-`(0,n)` vacuum space** `Ω_{0,n}(D^{(-1)}(𝒱)) ⊆ 𝒱^*` (Li Def 3.4, `m = 0`): the
functionals `f` whose FHL adjoint `Y^*(v,x) f` has pole order bounded by the `(x^{wt+n}(x+1)^{wt})`
clearing for every homogeneous `v` — the mode condition `vacMap W n wt v s f = 0` (∀ homog `v`, ∀ `s`).
A subspace of the full dual (closure is immediate: each `vacMap` is `ℂ`-linear in `f`). -/
def VacuumSpace (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Submodule ℂ (Module.Dual ℂ 𝒱) where
  carrier := {f | ∀ (wt : ℕ) (v : 𝒱), v ∈ W.grading (wt : ℤ) → ∀ s : ℕ, vacMap W n wt v s f = 0}
  zero_mem' := by intro wt v _ s; rw [map_zero]
  add_mem' := by
    intro f g hf hg wt v hv s; rw [map_add, hf wt v hv s, hg wt v hv s, add_zero]
  smul_mem' := by
    intro c f hf wt v hv s; rw [map_smul, hf wt v hv s, smul_zero]

/-- Membership in the vacuum space is exactly the pole/mode condition (†). -/
theorem mem_vacuumSpace (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (f : Module.Dual ℂ 𝒱) :
    f ∈ VacuumSpace W n ↔
      ∀ (wt : ℕ) (v : 𝒱), v ∈ W.grading (wt : ℤ) → ∀ s : ℕ, vacMap W n wt v s f = 0 :=
  Iff.rfl

/-! ## The two Li inputs, and the structural reduction of `LiDualStable`. -/

/-- **Li Proposition 3.5** (level `(k,0)`), the **DAGGER** identification `(Onm W k 0)^⊥ = VacuumSpace`.
⚠ This is TRUE only at `k = 0`.  For `k ≥ 1` `VacuumSpace W k` encodes the pole condition ONLY, so it is
the annihilator of the DAGGER ideal `O†_{k,0}` (circle span) — which is STRICTLY SMALLER than the DIAMOND
ideal `Onm W k 0 = O'_{k,0}` (circles ⊔ grading generators `anmLgen`).  Hence
`(Onm W k 0).dualAnnihilator ⊊ VacuumSpace W k` and `LiProp35 W k` is FALSE for `k ≥ 1` (Li's full
diamond Prop 3.5 additionally imposes the grading eigen-clause `(L*(1)+L*(0))f = k·f`, Prop 4.1, which
`VacuumSpace` omits).  Retained only to state the dagger relationship; the TRUE, unconditional content
is the one inclusion `adjPoleSpace_le_Onm` (`AdjPoleSpace W n ⊆ Onm W n 0`). -/
def LiProp35 (W : VertexOperatorAlgebra 𝒱) (k : ℕ) : Prop :=
  (Onm W k 0).dualAnnihilator = VacuumSpace W k

/-- **Li regular-representation stability** (Thm 3.2 / Lemma 3.14), DAGGER form: the transpose of the
right action carries the DAGGER vacuum space `VacuumSpace W n` into `VacuumSpace W 0`. -/
def VacuumStable (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ a : 𝒱, ∀ f ∈ VacuumSpace W n, (anmRightR W n 0 a).dualMap f ∈ VacuumSpace W 0

/-! ## ⚠ CORRECTION (dagger vs diamond) — the SOUND route to `MUGradedAction`.

An earlier framing in this file claimed `MUGradedAction W` reduces (via a `mUGradedAction_of_liVacuum` /
`mUGradedAction_of_liPrimal` main theorem) to `∀k, LiProp35 W k` (equivalently `AdjPoleSpace W k = Onm W k 0`)
plus a vacuum-stability.  That reduction is UNSOUND: its hypothesis is FALSE for `k ≥ 1`, because
`VacuumSpace` encodes only the pole condition (the DAGGER ideal `O†`), not Li's grading eigen-clause
(Prop 4.1) that `Onm = O'` (DIAMOND) requires — an adversarially-verified reading of Li §3–4.  Those two
dead main theorems have been REMOVED.

The SOUND, already-wired route is `ZhuVermaAnArchLiReduce.mUGradedAction_of_liDualStable` ⟸
`∀n, LiDualStable W n`, which is DIAMOND-native and (by `liDualStable_of_closure`) equivalent to the
cross-level closure `CrossCircCore` — the genuine remaining open theorem.  Li's regular representation
adapters back onto `CrossCircCore`; it does not shortcut it.

What this file contributes SOUNDLY: the full-dual FHL adjoint (`adjOp`, verified equal to the repo's
proven `dualCompMap`), the (dagger) vacuum space, and the PROVEN inclusion `adjPoleSpace_le_Onm`. -/

/-! ## Prop 3.5 in PRIMAL form — `LiProp35 W n ⟺ AdjPoleSpace W n = Onm W n 0` (dagger).

`vacMap` is precompose-by-a-fixed-vector-operator: `vacMap W n wt v s f x = f (adjPoleMap W n wt v s x)`
where `adjPoleMap W n wt v s = ∑_j C(wt,j) · adjOp W wt v (wt+n+j+s)` is the **FHL-adjoint pole
operator** on `𝒱`.  Hence the (dual) vacuum space is the annihilator of the (primal) span of the pole
vectors, `VacuumSpace W n = (AdjPoleSpace W n).dualAnnihilator`, and — over the field `ℂ`, via the
double annihilator — `LiProp35` becomes the primal identity `AdjPoleSpace W n = Onm W n 0`.  ⚠ Per the
dagger/diamond correction above, that primal equality is FALSE for `n ≥ 1` (`AdjPoleSpace = O†_{n,0} ⊊
Onm = O'_{n,0}`); the TRUE, unconditional half is the ⊆ inclusion `adjPoleSpace_le_Onm`, proved below via
the FHL `x ↔ z⁻¹` re-summation. -/

/-- **The FHL-adjoint pole operator** on `𝒱`: `adjPoleMap W n wt v s = ∑_j C(wt,j) · adjOp W wt v
(wt+n+j+s)`.  Its image (over homogeneous `v`, all `s`) spans the primal counterpart of the vacuum
space, and `vacMap` is precomposition by it. -/
noncomputable def adjPoleMap (W : VertexOperatorAlgebra 𝒱) (n wt : ℕ) (v : 𝒱) (s : ℕ) :
    𝒱 →ₗ[ℂ] 𝒱 :=
  ∑ j ∈ Finset.range (wt + 1),
    (Nat.choose wt j : ℂ) • adjOp W (wt : ℤ) v ((wt : ℤ) + (n : ℤ) + (j : ℤ) + (s : ℤ))

/-- `vacMap` is precomposition by the pole operator: `vacMap W n wt v s f x = f (adjPoleMap … x)`. -/
theorem vacMap_apply (W : VertexOperatorAlgebra 𝒱) (n wt : ℕ) (v : 𝒱) (s : ℕ)
    (f : Module.Dual ℂ 𝒱) (x : 𝒱) :
    vacMap W n wt v s f x = f (adjPoleMap W n wt v s x) := by
  simp only [vacMap, adjPoleMap, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    Yadj_apply, map_sum, map_smul]

/-- The set of **FHL-adjoint pole vectors** at level `n`. -/
def adjPoleSet (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Set 𝒱 :=
  {x | ∃ (wt : ℕ) (v : 𝒱), v ∈ W.grading (wt : ℤ) ∧ ∃ (s : ℕ) (y : 𝒱), x = adjPoleMap W n wt v s y}

/-- **The primal pole space** `AdjPoleSpace W n = span{ adjPoleMap W n wt v s y }` — the primal
counterpart of the level-`(0,n)` vacuum space. -/
def AdjPoleSpace (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ (adjPoleSet W n)

/-- **The vacuum space is the annihilator of the pole space.**  `VacuumSpace W n =
(AdjPoleSpace W n).dualAnnihilator`: a functional lies in the level-`(0,n)` vacuum space iff it
annihilates every FHL-adjoint pole vector. -/
theorem vacuumSpace_eq_dualAnnihilator (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    VacuumSpace W n = (AdjPoleSpace W n).dualAnnihilator := by
  apply SetLike.ext'
  rw [AdjPoleSpace, coe_dualAnnihilator_span]
  ext f
  constructor
  · rintro hf x ⟨wt, v, hv, s, y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← vacMap_apply, hf wt v hv s, LinearMap.zero_apply]
  · intro hf wt v hv s
    ext x
    rw [vacMap_apply, LinearMap.zero_apply]
    have hx : adjPoleMap W n wt v s x ∈ LinearMap.ker f := hf ⟨wt, v, hv, s, x, rfl⟩
    rwa [LinearMap.mem_ker] at hx

/-- **The primal form of `LiProp35`** (a true formal equivalence).  Over `ℂ`, via the double
annihilator, `(Onm W n 0).dualAnnihilator = VacuumSpace W n` iff `AdjPoleSpace W n = Onm W n 0`.  ⚠ Both
sides are FALSE for `n ≥ 1` (dagger `⊊` diamond); the iff itself is a true tautology.  The one true,
unconditional inclusion is `adjPoleSpace_le_Onm` (`AdjPoleSpace W n ⊆ Onm W n 0`). -/
theorem liProp35_iff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    LiProp35 W n ↔ AdjPoleSpace W n = Onm W n 0 := by
  rw [LiProp35, vacuumSpace_eq_dualAnnihilator]
  constructor
  · intro h
    have h2 := congrArg Submodule.dualCoannihilator h
    rw [Subspace.dualAnnihilator_dualCoannihilator_eq,
      Subspace.dualAnnihilator_dualCoannihilator_eq] at h2
    exact h2.symm
  · intro h; rw [h]

/-! ## `VacuumStable` in PRIMAL (dagger) form.

The dagger stability `VacuumStable W n` descends to the pole space: since `VacuumSpace W k =
(AdjPoleSpace W k).dualAnnihilator`, and the transpose of `anmRightR W n 0 a` is precomposition,
`VacuumStable` follows from the PRIMAL containment `anmRight W n 0 a (AdjPoleSpace W 0) ⊆ AdjPoleSpace W n`
(the right action carries level-`0` DAGGER pole vectors into level-`n` ones).  ⚠ Note this concerns the
DAGGER vacuum spaces; it does NOT by itself discharge the DIAMOND `LiDualStable` (which annihilates `Onm`,
not `O†`).  Kept as reusable pole-arithmetic infrastructure. -/

/-- **Primal (dagger) pole-stability**: the right action by `a` carries the level-`(0,0)` pole space
into the level-`(0,n)` pole space. -/
def AdjPoleStable (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ a : 𝒱, ∀ w ∈ AdjPoleSpace W 0, anmRight W n 0 a w ∈ AdjPoleSpace W n

/-- **`VacuumStable W n` (dagger) from primal pole-stability.**  If `anmRight W n 0 a` carries the
level-`0` dagger pole space into the level-`n` one, then the transpose carries `VacuumSpace W n` into
`VacuumSpace W 0`. -/
theorem vacuumStable_of_adjPoleStable (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (h : AdjPoleStable W n) : VacuumStable W n := by
  intro a f hf
  rw [vacuumSpace_eq_dualAnnihilator W n, Submodule.mem_dualAnnihilator] at hf
  rw [vacuumSpace_eq_dualAnnihilator W 0, Submodule.mem_dualAnnihilator]
  intro w hw
  rw [LinearMap.dualMap_apply, anmRightR_apply]
  exact hf _ (h a w hw)

/-! ## The circle ⊆ inclusion `AdjPoleSpace W n ⊆ Onm W n 0` (Li Prop 3.5, forward/circle half).

⚠ **Dagger vs diamond.**  `AdjPoleSpace W n` is the span of the FHL-adjoint pole vectors — Li's DAGGER
ideal `O†_{n,0}` (what the pole condition of `VacuumSpace` alone annihilates).  For `n ≥ 1` this is
STRICTLY SMALLER than the DIAMOND ideal `Onm W n 0 = O'_{n,0}` (`= span{anmCirc} ⊔ OnmL`), which also
carries the grading generators `anmLgen`.  So `AdjPoleSpace W n = Onm W n 0` (`liProp35_iff`'s RHS) is
FALSE for `n ≥ 1` — see the note at `liProp35_iff`.  What IS true for every `n` is the ⊆ inclusion below:
via the FHL `x ↔ z⁻¹` re-summation each pole vector is a sum of off-diagonal FZ residues
`resHom W j (n+2+s+j) (L₁ʲv) y`, each in `Onm W n 0` by `resHom_offdiag_mem_Onm` (pole excess `s ≥ 0`). -/

/-- **`adjOp` in physical-mode form** (`modeLinear`→`W.smul`, `smul_def`): for a homogeneous vector of
weight `wt`, `adjOp W wt u N x = (-1)^wt ∑_{j≤wt} (1/j!) · (L₁ʲu)₍2wt−N−2−j₎ x` as a genuine sum of
physical modes. -/
theorem adjOp_smul_form (W : VertexOperatorAlgebra 𝒱) (wt N : ℤ) (u x : 𝒱) :
    adjOp W wt u N x
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
          ((j.factorial : ℂ)⁻¹) • W.smul ((W.L 1 ^ j) u) (2 * wt - N - 2 - (j : ℤ)) x := by
  rw [adjOp_apply]
  rfl

/-- **The FHL `x ↔ z⁻¹` re-summation (Li Prop 3.5, circle half).**  For homogeneous `v` of weight `wt`,
the pole operator is a sum of off-diagonal FZ residues of the twisted vectors `L₁ʲv`:
`adjPoleMap W n wt v s y = (-1)^wt ∑_{j≤wt} (1/j!) · resHom W j (n+2+s+j) (L₁ʲv) y`. -/
theorem adjPoleMap_eq_resHomSum (W : VertexOperatorAlgebra 𝒱) (n wt : ℕ) {v : 𝒱}
    (hv : v ∈ W.grading (wt : ℤ)) (s : ℕ) (y : 𝒱) :
    adjPoleMap W n wt v s y
      = (-1 : ℂ) ^ (wt : ℤ) • ∑ j ∈ Finset.range (wt + 1),
          ((j.factorial : ℂ)⁻¹) •
            resHom W (j : ℤ) ((n : ℤ) + 2 + (s : ℤ) + (j : ℤ)) ((W.L 1 ^ j) v) y := by
  -- Reference double sum `REF` (order: j outer, b inner), the common normal form of both sides.
  set REF := ∑ j ∈ Finset.range (wt + 1), ∑ b ∈ Finset.range (wt + 1),
      ((-1 : ℂ) ^ (wt : ℤ) * ((j.factorial : ℂ)⁻¹ * (Nat.choose wt b : ℂ))) •
        W.smul ((W.L 1 ^ j) v) ((b : ℤ) - ((n : ℤ) + 2 + (s : ℤ) + (j : ℤ))) y with hREFdef
  -- (1) `adjPoleMap … y = REF`.
  have hApM : adjPoleMap W n wt v s y = REF := by
    rw [adjPoleMap, LinearMap.sum_apply]
    -- ∑_b C(wt,b) • (adjOp … y), expand adjOp, absorb scalars, swap sums, reflect b ↦ wt-b.
    have hstep : (∑ b ∈ Finset.range (wt + 1),
          ((Nat.choose wt b : ℂ) • adjOp W (wt : ℤ) v ((wt : ℤ) + (n : ℤ) + (b : ℤ) + (s : ℤ))) y)
        = ∑ b ∈ Finset.range (wt + 1), ∑ j ∈ Finset.range (wt + 1),
            ((Nat.choose wt b : ℂ) * ((-1 : ℂ) ^ (wt : ℤ) * (j.factorial : ℂ)⁻¹)) •
              W.smul ((W.L 1 ^ j) v)
                (2 * (wt : ℤ) - ((wt : ℤ) + (n : ℤ) + (b : ℤ) + (s : ℤ)) - 2 - (j : ℤ)) y := by
      apply Finset.sum_congr rfl
      intro b _
      rw [LinearMap.smul_apply, adjOp_smul_form, Int.toNat_natCast, Finset.smul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul, smul_smul, mul_assoc]
    rw [hstep, Finset.sum_comm, hREFdef]
    apply Finset.sum_congr rfl
    intro j _
    conv_lhs => rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro b hb
    have hble : b ≤ wt := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    rw [show wt + 1 - 1 - b = wt - b from by omega]
    have hmode : 2 * (wt : ℤ) - ((wt : ℤ) + (n : ℤ) + ((wt - b : ℕ) : ℤ) + (s : ℤ)) - 2 - (j : ℤ)
        = (b : ℤ) - ((n : ℤ) + 2 + (s : ℤ) + (j : ℤ)) := by
      rw [Nat.cast_sub hble]; ring
    rw [hmode, Nat.choose_symm hble]
    congr 1
    ring
  -- (2) `RHS = REF`.
  have hRHS : ((-1 : ℂ) ^ (wt : ℤ) • ∑ j ∈ Finset.range (wt + 1),
        ((j.factorial : ℂ)⁻¹) •
          resHom W (j : ℤ) ((n : ℤ) + 2 + (s : ℤ) + (j : ℤ)) ((W.L 1 ^ j) v) y) = REF := by
    rw [hREFdef, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ wt := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hmem : (W.L 1 ^ j) v ∈ W.grading ((wt : ℤ) - (j : ℤ)) := L_one_pow_mem W hv j
    rw [resHom_homogeneous W (j : ℤ) _ hmem y]
    have hk : (wt : ℤ) - (j : ℤ) + (j : ℤ) = (wt : ℤ) := by ring
    rw [hk, Int.toNat_natCast, Finset.smul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hble : b ≤ wt := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    rw [smul_smul, smul_smul, cbz_natCast_eq_choose hble, mul_assoc]
  rw [hApM, ← hRHS]

/-- **`adjPoleMap W n wt v s y ∈ Onm W n 0`** — every FHL-adjoint pole vector lies in the DJ ideal. -/
theorem adjPoleMap_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n wt : ℕ) {v : 𝒱}
    (hv : v ∈ W.grading (wt : ℤ)) (s : ℕ) (y : 𝒱) :
    adjPoleMap W n wt v s y ∈ Onm W n 0 := by
  rw [adjPoleMap_eq_resHomSum W n wt hv s y]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
  have hmem : (W.L 1 ^ j) v ∈ W.grading (((wt - j : ℕ) : ℤ)) := by
    have h := L_one_pow_mem W hv j
    rwa [← Nat.cast_sub (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))] at h
  have := resHom_offdiag_mem_Onm W n hmem y (s := j) (t := s + j) (by omega)
  rwa [show ((n : ℤ) + 2 + ((s + j : ℕ) : ℤ)) = (n : ℤ) + 2 + (s : ℤ) + (j : ℤ) by push_cast; ring]
    at this

/-- **`AdjPoleSpace W n ⊆ Onm W n 0`** — the dagger ideal is contained in the diamond ideal (Li Prop 3.5,
circle half; TRUE for every `n`, unlike the equality). -/
theorem adjPoleSpace_le_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    AdjPoleSpace W n ≤ Onm W n 0 := by
  rw [AdjPoleSpace, Submodule.span_le]
  rintro x ⟨wt, v, hv, s, y, rfl⟩
  exact adjPoleMap_mem_Onm W n wt hv s y

/-- **`AdjPoleStable W n` reduced to a per-generator check** (the pole-space analogue of
`anm_right_closure_of_gens`).  Since `AdjPoleSpace W 0 = span (adjPoleSet W 0)` and the right action
`anmRight W n 0 a (·)` is `ℂ`-linear, it suffices that `a` acts on each pole GENERATOR
`adjPoleMap W 0 wt v s y` (homogeneous `v`) landing in `AdjPoleSpace W n`.  This isolates the genuine
Li Lemma 3.13 content to the pole-vector generators. -/
theorem adjPoleStable_of_gens (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (h : ∀ (a : 𝒱) (wt : ℕ) (v : 𝒱), v ∈ W.grading (wt : ℤ) → ∀ (s : ℕ) (y : 𝒱),
      anmRight W n 0 a (adjPoleMap W 0 wt v s y) ∈ AdjPoleSpace W n) :
    AdjPoleStable W n := by
  intro a w hw
  have hle : AdjPoleSpace W 0 ≤ (AdjPoleSpace W n).comap (anmRightR W n 0 a) := by
    rw [AdjPoleSpace, Submodule.span_le]
    rintro x ⟨wt, v, hv, s, y, rfl⟩
    simpa only [SetLike.mem_coe, Submodule.mem_comap, anmRightR_apply] using h a wt v hv s y
  have hx := hle hw
  rwa [Submodule.mem_comap, anmRightR_apply] at hx

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.VacuumSpace
  #print axioms VOA.adjPoleMap_eq_resHomSum
  #print axioms VOA.adjPoleSpace_le_Onm
-/
