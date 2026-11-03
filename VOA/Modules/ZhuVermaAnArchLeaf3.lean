/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchRigidity
import VOA.Modules.ZhuVermaAnArchFaithfulBijection

/-!
# Theorem 5.3.4 — codomain simplicity: the predicate `IsSimpleAMod` and the **independent** half
of the forward direction `bottom-of-irreducible ⟹ simple `A(𝒱)`-module`

The faithful codomain of the Zhu bijection is currently *image-defined*: `IrrAMod W` is the subtype
`{U // IsBottomOfIrr U}` (`ZhuVermaAnArchFaithfulBijection`).  To upgrade it to the genuine
`Irr A(𝒱)` one wants a **module-intrinsic** simplicity predicate on `AMod W` (an `A(𝒱)`-module is
simple iff it is nonzero and has no proper nonzero `A(𝒱)`-submodule), mirroring
`OrdVModule.IsIrreducible`.

This file builds that predicate and discharges the **genuinely keystone-independent** content of the
forward direction `bottom-of-irreducible ⟹ simple A-module`:

* **`AModSubmodule U`** — an `A(𝒱)`-submodule of a bundled `AMod`: a `ℂ`-subspace closed under the
  action `U.ρ a` for every `a : A(𝒱)`.  (The exact analogue of `WeakModule.Submodule'`.)
* **`IsSimpleAMod U`** — nonzero, with no `A(𝒱)`-submodule other than `⊥` and `⊤`.  (The exact
  analogue of `OrdVModule.IsIrreducible`.)
* **`bottomSubmodule_of_vSubmodule`** — *the easy, unconditional reduction*: every `𝒱`-weak-submodule
  `N` of an irreducible `P` restricts to an `A(𝒱)`-submodule of the bottom `P.toAMod` (its carrier is
  `N.carrier ⊓ P_h`, pulled into `P_h`; closure under `U.ρ = actA` is the `oMod`-closure of `N`).
* **`isSimpleAMod_nontrivial`** — *the nontriviality half, fully unconditional*: the bottom of an
  irreducible (hence nonzero, realized) lowest-weight module is a **nontrivial** `A(𝒱)`-module.
* **`AModSubmodule.genVSubmodule`** — *the generated `𝒱`-weak-submodule from a bottom submodule*: for
  an `A(𝒱)`-submodule `S` of `P.toAMod`, the smallest `WeakModule.Submodule'` of `P` whose carrier
  contains `S` (built as the `sInf` of all such carriers).  This is the standard "generate the
  `𝒱`-module from a bottom `A(𝒱)`-submodule" object.
* **`AModSubmodule.le_genVSubmodule`** — `S ⊆ genVSubmodule S ∩ P_h` (unconditional), and the easy
  half of the dichotomy: if `genVSubmodule S = ⊥` then `S = ⊥`
  (**`AModSubmodule.eq_bot_of_genVSubmodule_bot`**).

## The single gated residual (isolated, *not* carried into a faked close)

The remaining half — `S = P.toAMod` once `genVSubmodule S = ⊤` — is the **bottom-recovery**
`genVSubmodule S ⊓ P_h ⊆ S`.  This is *not* a one-liner and it is **not** keystone-independent: it is
the DLM3 / Frenkel–Zhu statement "a `𝒱`-mode word that returns a bottom vector to the bottom acts
through the Zhu algebra `A(𝒱)` on the bottom", i.e. the bottom Borcherds / `A_{n,0}(𝒱)`-bimodule
content that is *the same caliber* as the cross-tower keystone and the PBW-gated bottom survival
(`ZhuVermaAnArchBottomSurvivalPBWFree`).  We therefore **do not** assert the full forward theorem
`isBottomOfIrr_isSimpleAMod`; we name the residual as the explicit predicate

  `BottomRecovers P`  := for every `A(𝒱)`-submodule `S` of `P.toAMod`,
                         `genVSubmodule S ⊓ P_h ⊆ S`

and reduce the full forward direction to it (`isSimpleAMod_of_bottomRecovers`), with `BottomRecovers`
clearly flagged as the gated input — never an axiom, never silently absorbed.

⚠ **Update:** `BottomRecovers P` is proved for every lowest-weight module of every VOA,
downstream: `VOA.Huang.LWBottomRecovery.bottomRecovers P` (and `allBottomRecovers W`), via the
general bottom recovery of `Huang/BottomRecovery.lean`.  The unconditional forward direction is
`VOA.Huang.LWBottomRecovery.isSimpleAMod_toAMod_of_irreducible`.

`#print axioms` on every proved theorem below is exactly `[propext, Classical.choice, Quot.sound]`.

## References
Gannon §5.3.1–§5.3.2, Thm 5.3.4; Zhu [574]; Frenkel–Zhu; Dong–Li–Mason; Dong–Jiang `math/0601626`.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The module zero mode preserves a `𝒱`-weak-submodule

`o(u) = ∑_k (u_k)₍ₖ₋₁₎` is a finite grade-sum of modes; each mode preserves a
`WeakModule.Submodule'` (its defining `act_mem`), so the zero mode does too. -/

section ZeroModeClosure

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
  {N : OrdVModule W M}

/-- **The module zero mode preserves a `𝒱`-weak-submodule.**  For `x` in the carrier of a
`WeakModule.Submodule'` `K` of `N`, `o(u) x ∈ K` for every `u`.  On a homogeneous `u ∈ 𝒱ₖ` this is
`o(u) x = u₍ₖ₋₁₎ x = act u (k-1) x ∈ K` (by `K.act_mem`); extend over the grade decomposition. -/
theorem oMod_mem_of_submodule (K : WeakModule.Submodule' N.toWeakModule) (u : 𝒱) {x : M}
    (hx : x ∈ K.carrier) : oMod N u x ∈ K.carrier := by
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => oMod N u x ∈ K.carrier) hutop ?_ ?_ ?_
  · intro k y hy
    rw [oMod_homogeneous N hy]
    exact K.act_mem y (k - 1) hx
  · simp only [map_zero, LinearMap.zero_apply]; exact K.carrier.zero_mem
  · intro y z hy hz
    rw [map_add, LinearMap.add_apply]
    exact K.carrier.add_mem hy hz

end ZeroModeClosure

/-! ## The intrinsic `A(𝒱)`-module simplicity predicate -/

/-- An **`A(𝒱)`-submodule** of a bundled `AMod` `U`: a `ℂ`-subspace of the carrier closed under the
action `U.ρ a` for every `a : A(𝒱)`.  The exact analogue of `WeakModule.Submodule'`. -/
structure AModSubmodule {W : VertexOperatorAlgebra 𝒱} (U : AMod W) where
  /-- The underlying `ℂ`-subspace. -/
  carrier : Submodule ℂ U.carrier
  /-- Closure under the `A(𝒱)`-action: `x ∈ carrier ⟹ ρ a x ∈ carrier`. -/
  ρ_mem : ∀ (a : A W) {x : U.carrier}, x ∈ carrier → U.ρ a x ∈ carrier

/-- **`IsSimpleAMod U`** — the bundled `A(𝒱)`-module `U` is **simple**: it is nonzero and has no
`A(𝒱)`-submodule other than `⊥` and `⊤`.  The intrinsic, module-level analogue of
`OrdVModule.IsIrreducible`; this is the genuine codomain predicate `Irr A(𝒱)` of Theorem 5.3.4. -/
def IsSimpleAMod {W : VertexOperatorAlgebra 𝒱} (U : AMod W) : Prop :=
  Nontrivial U.carrier ∧ ∀ S : AModSubmodule U, S.carrier = ⊥ ∨ S.carrier = ⊤

/-! ## The bottom of an irreducible `𝒱`-module is a *nontrivial* `A(𝒱)`-module (unconditional) -/

section Bottom

variable {W : VertexOperatorAlgebra 𝒱} (P : LWModule W)

/-- **The bottom `P.toAMod` of a *realized* lowest-weight module is nontrivial.**  `P.realized` says
`P_h ≠ ⊥`, hence the carrier `P.toAMod.carrier = ↥P_h` has a nonzero element — it is nontrivial.
Fully unconditional (no irreducibility, no keystone). -/
theorem nontrivial_toAMod : Nontrivial (P.toAMod).carrier := by
  -- `P.toAMod.carrier` is definitionally `↥(P.isMod.weight P.h)`; `P.realized` gives a nonzero elt.
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.realized
  refine ⟨⟨⟨x, hx⟩, 0, ?_⟩⟩
  intro h
  exact hx0 (congrArg Subtype.val h)

end Bottom

/-! ## From a `𝒱`-weak-submodule of an irreducible `P` to an `A(𝒱)`-submodule of its bottom

This is the *easy*, fully unconditional half of the forward direction.  A `WeakModule.Submodule'` of
`P` (closed under all modes `u₍ₙ₎`) restricts to a subspace of the bottom `P_h` closed under the
zero-mode `o(u) = actA`, i.e. an `AModSubmodule` of `P.toAMod`. -/

section RestrictBottom

variable {W : VertexOperatorAlgebra 𝒱} {P : LWModule W}

/-- The carrier of an `A(𝒱)`-submodule of the bottom obtained from a `𝒱`-weak-submodule `N` of `P`:
the trace of `N` on the bottom `P_h`, viewed as a subspace of `P.toAMod.carrier = ↥P_h`.  This is
`comap` of `N.carrier` along the inclusion `P_h ↪ P`. -/
noncomputable def vSubmoduleBottomCarrier (N : WeakModule.Submodule' P.isMod.toWeakModule) :
    Submodule ℂ (P.toAMod).carrier :=
  N.carrier.comap (P.isMod.weight P.h).subtype

/-- **A `𝒱`-weak-submodule of `P` restricts to an `A(𝒱)`-submodule of the bottom `P.toAMod`.**
Its carrier is the trace on `P_h`; closure under `U.ρ a = actA [u]` is the `o(u)`-closure of `N`
(`o(u) x = u₍ₖ₋₁₎ x ∈ N` by `N.act_mem`, summed over grades), keeping the result inside `P_h` by the
bottom-preservation of the zero mode.  Unconditional. -/
noncomputable def bottomSubmodule_of_vSubmodule
    (N : WeakModule.Submodule' P.isMod.toWeakModule) : AModSubmodule (P.toAMod) where
  carrier := vSubmoduleBottomCarrier N
  ρ_mem a {x} hx := by
    -- Name the underlying bottom vector `x' : P_h`.
    let x' : P.isMod.weight P.h := x
    -- Reduce `a = [u]`.  Then `ρ [u] x = actA [u] x'`, whose `P`-coercion is `o(u) ↑x'`.
    refine Submodule.Quotient.induction_on (O W) a (fun u => ?_)
    -- `hx : ↑x' ∈ N.carrier`; want `↑(actA [u] x') ∈ N.carrier`.
    simp only [vSubmoduleBottomCarrier, Submodule.mem_comap] at hx ⊢
    -- `↑(actA [u] x') = o(u) ↑x'`; and `o(u) ↑x'` is an `N`-closed mode-sum.
    show ((actA P.isMod P.isLow (mk W u) x' : P.isMod.weight P.h) : P.carrier) ∈ N.carrier
    rw [actA_mk_apply_coe P.isMod P.isLow u x']
    -- `o(u)` preserves `N` (mode-closure + grade decomposition).
    exact oMod_mem_of_submodule N u hx

end RestrictBottom

/-! ## The generated `𝒱`-weak-submodule from a bottom `A(𝒱)`-submodule, and the easy dichotomy half -/

section Generated

variable {W : VertexOperatorAlgebra 𝒱} {P : LWModule W}

/-- The image in `P` of an `A(𝒱)`-submodule `S ⊆ P_h` of the bottom: `S.carrier` pushed forward along
the inclusion `P_h ↪ P`. -/
noncomputable def AModSubmodule.toBottomImage (S : AModSubmodule (P.toAMod)) :
    Submodule ℂ P.carrier :=
  S.carrier.map (P.isMod.weight P.h).subtype

/-- **The `𝒱`-weak-submodule generated by a bottom `A(𝒱)`-submodule `S`.**  The smallest
`WeakModule.Submodule'` of `P` whose carrier contains the image of `S` in `P`; built as the infimum
(over the set of all `𝒱`-weak-submodules containing `S.toBottomImage`) of their carriers.  This is the
standard "generate the `𝒱`-module from a bottom `A(𝒱)`-submodule" object. -/
noncomputable def AModSubmodule.genVSubmodule (S : AModSubmodule (P.toAMod)) :
    WeakModule.Submodule' P.isMod.toWeakModule where
  carrier := ⨅ N : {N : WeakModule.Submodule' P.isMod.toWeakModule // S.toBottomImage ≤ N.carrier},
      N.1.carrier
  act_mem u n {x} hx := by
    -- Membership in the infimum: `x ∈ N.carrier` for every closed `N ⊇ S.toBottomImage`.
    rw [Submodule.mem_iInf] at hx ⊢
    intro N
    -- For such an `N`, `x ∈ N.carrier`, hence `u₍ₙ₎ x ∈ N.carrier` by `N.act_mem`.
    exact N.1.act_mem u n (hx N)

/-- The image of `S` lands in the generated submodule. -/
theorem AModSubmodule.toBottomImage_le_genVSubmodule (S : AModSubmodule (P.toAMod)) :
    S.toBottomImage ≤ S.genVSubmodule.carrier := by
  intro x hx
  simp only [genVSubmodule, Submodule.mem_iInf]
  intro N
  exact N.2 hx

/-- **Easy half of the dichotomy (unconditional): if the generated submodule is `⊥` then `S = ⊥`.**
Because `S.toBottomImage ⊆ genVSubmodule S = ⊥`, the image of `S` is `⊥`, and the inclusion
`P_h ↪ P` is injective, so `S.carrier = ⊥`. -/
theorem AModSubmodule.eq_bot_of_genVSubmodule_bot (S : AModSubmodule (P.toAMod))
    (h : S.genVSubmodule.carrier = ⊥) : S.carrier = ⊥ := by
  have himg : S.toBottomImage = ⊥ :=
    le_bot_iff.mp (h ▸ S.toBottomImage_le_genVSubmodule)
  -- `toBottomImage = map subtype S.carrier`; `subtype` injective ⟹ `S.carrier = ⊥`.
  have hinj : Function.Injective (P.isMod.weight P.h).subtype := Submodule.injective_subtype _
  unfold AModSubmodule.toBottomImage at himg
  -- Pull back along the injective `subtype`: `comap subtype (map subtype S) = S`.
  have hcm : (S.carrier.map (P.isMod.weight P.h).subtype).comap (P.isMod.weight P.h).subtype
      = S.carrier := Submodule.comap_map_eq_of_injective hinj S.carrier
  rw [himg, Submodule.comap_bot, Submodule.ker_subtype] at hcm
  exact hcm.symm

end Generated

/-! ## The gated residual, isolated as an explicit named predicate — and the reduction to it

The remaining content (`S = ⊤` once `genVSubmodule S = ⊤`) is the **bottom recovery**: a `𝒱`-mode
word returning a bottom vector to the bottom acts through the Zhu algebra on the bottom.  This is
keystone-caliber (the DLM3 bottom-Borcherds / `A_{n,0}(𝒱)`-bimodule content, == the PBW-gated bottom
survival of `ZhuVermaAnArchBottomSurvivalPBWFree`).  It is **named here as an explicit hypothesis**,
not proved in this file and NOT silently absorbed; the full forward theorem is reduced to it
transparently.  (It is proved downstream: `VOA.Huang.LWBottomRecovery.bottomRecovers`.) -/

section Gated

variable {W : VertexOperatorAlgebra 𝒱} (P : LWModule W)

/-- **`BottomRecovers P`** — the (gated, keystone-caliber) bottom-recovery predicate: for every
`A(𝒱)`-submodule `S` of the bottom `P.toAMod`, the trace of the generated `𝒱`-submodule on the
bottom is again `S`.  Equivalently, returning a bottom vector to the bottom by a `𝒱`-mode word is
already achievable by the Zhu-algebra action on `S`.  This is the genuine deep core (the same caliber
as the cross-tower keystone / PBW-gated bottom survival); it is carried as an explicit hypothesis,
**never** an axiom.  It is proved for every `P`, downstream:
`VOA.Huang.LWBottomRecovery.bottomRecovers P`. -/
def BottomRecovers : Prop :=
  ∀ S : AModSubmodule (P.toAMod),
    vSubmoduleBottomCarrier S.genVSubmodule ≤ S.carrier

/-- **The forward direction, reduced to the gated recovery (transparently, not faked).**
Given `P` irreducible as a `𝒱`-module and the bottom-recovery `BottomRecovers P`, the bottom
`P.toAMod` is a simple `A(𝒱)`-module.

Proof.  Nontriviality is unconditional (`nontrivial_toAMod`).  For the dichotomy, take an
`A(𝒱)`-submodule `S` of the bottom and form the generated `𝒱`-submodule `genVSubmodule S`.  By
irreducibility of `P` it is `⊥` or `⊤`.

* `⊥`: then `S = ⊥` by `eq_bot_of_genVSubmodule_bot` (unconditional).
* `⊤`: then `vSubmoduleBottomCarrier (genVSubmodule S) = comap subtype ⊤ = ⊤`, so by `BottomRecovers`
  `⊤ ≤ S.carrier`, i.e. `S = ⊤`.

The *only* hypothesis beyond irreducibility is the explicitly-flagged gated `BottomRecovers P`. -/
theorem isSimpleAMod_of_bottomRecovers (hirr : P.IsIrreducibleLW) (hrec : BottomRecovers P) :
    IsSimpleAMod (P.toAMod) := by
  refine ⟨nontrivial_toAMod P, fun S => ?_⟩
  rcases hirr.2 S.genVSubmodule with hbot | htop
  · exact Or.inl (S.eq_bot_of_genVSubmodule_bot hbot)
  · refine Or.inr ?_
    -- `vSubmoduleBottomCarrier (genVSubmodule S) = comap subtype ⊤ = ⊤`.
    have htrace : vSubmoduleBottomCarrier S.genVSubmodule = ⊤ := by
      unfold vSubmoduleBottomCarrier
      rw [htop, Submodule.comap_top]
    have := hrec S
    rw [htrace] at this
    exact top_le_iff.mp this

end Gated

end VOA
