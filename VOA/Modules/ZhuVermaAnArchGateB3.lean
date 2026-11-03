/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGateB1Ann
import VOA.Modules.ZhuVermaAnArchDLM3Prop43
import VOA.Modules.ZhuVermaAnArchOnmCollapseZero

/-!
# B3 and the closed `(0,0)` gate — `OnmFull W 0 0 = O W` from PBW + DLM3's `U(V̂)W ⊆ J`

The gate is Dong–Jiang Proposition 4.6 at `(n,m) = (0,0)`:

    (GATE)   OnmFull W 0 0 ≤ O W        (⟹ `A_{0,0}(𝒱) ≅ A(𝒱)`, the bottom of `M(U)` is `U`).

Dong–Jiang's proof is representation-theoretic and has three moving parts.  Two of them are
**theorems** in the repo:

* **B1** (annihilation) — the zero mode of every element of `O_{0,0}(𝒱)` kills the bottom level of
  every non-negatively levelled weak module.  `ZhuVermaAnArchGateB1Ann.gateAnnihilationLev_holds`,
  **unconditional**.
* **B2** (realization) — `M̄_0(U)` realizes `U` as its bottom. `ZhuVermaAnArchDLM3Prop43` proves
  DLM3's Proposition 4.3 at `n = 0` outright; what is still carried in this file is the independent
  bottom-injectivity datum (`PBWFreeness`; level independence is unconditional) and the two
  propagation steps DLM3 Prop 4.6 / 4.7 (`DefectPairsToZero`).
* **B3** (this file) — instantiate at the **regular** module `U = A(𝒱)`, a module over itself by
  the unconditional `zhuRingData_holds`, where

      o(x)·[𝟙] = [x ∗ 𝟙] = [x]     in `A(𝒱)`.

  Hence B1 forces `[x] = 0`, i.e. `x ∈ O(𝒱)`.

## What this file adds

1. **The B3 identity, isolated.**  `regularAMod_rho_one_eq_zhuMul` (`o(x)·[𝟙] = [x ∗ 𝟙]`) and
   `mk_zhuMul_vacuum_right` (`[x ∗ 𝟙] = [x]`, on the nose by the unit law `zhuMul_vacuum_right`)
   spell out the chain that `regularAMod_apply_one` compresses.
2. **The B3 step as a stand-alone implication** (no annihilation input):
   `mem_O_of_oLevW_vanish_at_one` — for *any* `GateRealization` of the regular module, the class
   `[x]` is read off the zero mode at the single vector `emb [𝟙]`.
3. **The gate from a realization alone** (`gate_of_realization_uncond`): B1 is discharged, so the
   only remaining input on this route is a realization of `U = A(𝒱)`.
4. **The gate from the independent bottom-injectivity hypothesis plus DLM3's `U(V̂)W ⊆ J`**
   (`gate_of_pbw`), and the fully expanded three-hypothesis form
   (`gate_of_pbw_props`) carrying B2's `BottomPropagates` (DLM3 Prop 4.6) and `OrbitPropagates`
   (DLM3 Prop 4.7) explicitly.
5. **The round trip through the combinatorial route** — the gate discharges the two generator
   families of `onmFull_zero_zero_eq_O_of_gens` (`ZhuVermaAnArchOnmCollapseZero`) and re-assembling
   through them, together with the proved `Onm_zero_zero_eq_O`, returns the same equality
   (`onmFull_zero_zero_eq_O_via_gens`).  A consistency check, not an independent proof.
6. **The downstream consumers**, each carrying the same explicit hypothesis set: `DJAnnEqAn W 0`,
   `OnmFull W 0 0 = OnFull W 0`, `AnmFull W 0 0 ≃ₗ A_0(𝒱)`, `AnmFull W 0 0 ≃ₗ A(𝒱)`,
   `djPieceMEquiv`, `DJCarrier.degMEquiv` (the bottom of `M(U)` is `U`).

## Honest status — what is proved and what is carried

**proved, unconditional:** everything on the route from a `GateRealization W (regularAMod W)` to
the gate, and every consumer *given* the gate.  In particular B1 contributes nothing carried.

**CARRIED (named hypotheses, never axioms, never `sorry`):** exactly two, both from B2 and both
about the *regular* module `Q = parabolicRepOfAMod W (regularAMod W)`:

* `PBWFreeness Q` — reduced to bottom injectivity (level independence is unconditional), in the
  two-field packaging of `ZhuVermaAnArchDLM3PBWSplit`. The companion
  `voaPBWFreeness` supplies this regular-module instance from the generic relative-induction field
  of the theorem `VOA.pbw : PBWPrinciple`;
* `DefectPairsToZero hP.bottomProjection` — DLM3's `U(V̂)W ⊆ J`.  Its base case (DLM3 Prop 4.3 at
  `n = 0`) **is proved** (`proj_indDefectVec_bottom`); what remains is the propagation from the
  bottom to all of `M_0(U)` (DLM3 Prop 4.6) and across the `U(V̂)`-orbit (DLM3 Prop 4.7), packaged
  in `ZhuVermaAnArchDLM3Prop43` as `BottomPropagates` / `OrbitPropagates`.

So **no** downstream consumer here is unconditional: `PBWFreeness` carries the unproved
regular-module bottom injectivity, and `DefectPairsToZero` is a second named input in this file.
This is stated bluntly
because `#print axioms` does not expose either parameter.

**The gate is NOT claimed.**  Every statement below that uses the
gate takes it as an explicit hypothesis.

## References
Dong–Jiang `math/0601626` §4 (Lemma 4.1, Thm 4.3, Prop. 4.5, Prop. 4.6);
Dong–Li–Mason `q-alg/9612010` §4 (Prop. 4.3, Prop. 4.6, Prop. 4.7, Thm 4.1);
Zhu, J. Amer. Math. Soc. 9 (1996) Thm 2.1.1/2.1.2 (`zhuRingData_holds`);
`ZhuVermaAnArchGate` (`GateRealization`, `gate_le_of_realization`, the consumers),
`ZhuVermaAnArchGateB1Ann` (B1 unconditional, `gate_of_dlm3`),
`ZhuVermaAnArchDLM3PBWSplit` (`PBWFreeness`), `ZhuVermaAnArchDLM3Prop43` (DLM3 Prop 4.3 at `n = 0`),
`ZhuVermaAnArchOnmCollapseZero` (`onmFull_zero_zero_eq_O_of_gens`),
`ZhuVermaAnArchBottomDefectClose` (`Onm_zero_zero_eq_O`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## (A) The B3 identity `o(x)·[𝟙] = [x ∗ 𝟙] = [x]`, spelled out -/

/-- **`o(x)·[𝟙] = [x ∗ 𝟙]`** on the regular `A(𝒱)`-module.  The action of `regularAMod W` *is* the
descended Zhu product `Amul` at the unconditional `zhuRingData_holds`, so this is `Amul_mk`. -/
theorem regularAMod_rho_one_eq_zhuMul (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) :
    (regularAMod W).ρ (mk W x) (one W) = mk W (zhuMul W x W.vacuum) := by
  change Amul (zhuRingData_holds W) (mk W x) (mk W W.vacuum) = _
  rw [Amul_mk]

/-- **`[x ∗ 𝟙] = [x]`** in `A(𝒱)`.  Zhu's right unit law `zhuMul_vacuum_right` holds *on the nose*
in `𝒱` (not merely mod `O(𝒱)`), so no ideal bookkeeping is needed. -/
theorem mk_zhuMul_vacuum_right (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) :
    mk W (zhuMul W x W.vacuum) = mk W x := by
  rw [zhuMul_vacuum_right]

/-- The two steps composed: `o(x)·[𝟙] = [x]` — the proved `regularAMod_apply_one`, re-derived here
through the explicit chain so that the B3 mechanism is visible. -/
theorem regularAMod_rho_one_chain (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) :
    (regularAMod W).ρ (mk W x) (one W) = mk W x := by
  rw [regularAMod_rho_one_eq_zhuMul, mk_zhuMul_vacuum_right]

/-! ## (B) B3 as a stand-alone implication -/

section B3

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The class of `x` is its zero mode at `emb [𝟙]`.**  For any level-`0` realization of the
regular module, `emb [x] = o(x)·emb [𝟙]`.  This is `GateRealization.emb_act_all` at `u = [𝟙]`,
rewritten by the B3 identity of §(A). -/
theorem regularAMod_emb_mk (R : GateRealization W (regularAMod W)) (x : 𝒱) :
    R.emb (mk W x) = oLevW R.weak 0 x (R.emb (one W)) := by
  have h := R.emb_act_all x (one W)
  rwa [regularAMod_rho_one_chain] at h

/-- **B3, isolated.**  If the zero mode of `x` kills the *single* bottom vector `emb [𝟙]` of a
realization of the regular module, then `x ∈ O(𝒱)`.  No annihilation theory is used here — this is
purely the regular-module bookkeeping `o(x)·[𝟙] = [x]` plus injectivity of `emb`. -/
theorem mem_O_of_oLevW_vanish_at_one (R : GateRealization W (regularAMod W)) {x : 𝒱}
    (hx : oLevW R.weak 0 x (R.emb (one W)) = 0) : x ∈ O W := by
  have hemb : R.emb (mk W x) = R.emb 0 := by
    rw [regularAMod_emb_mk, hx, map_zero]
  have h0 : mk W x = 0 := R.emb_inj hemb
  rwa [mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0

/-- **B1 + B3 — the gate from a realization alone, no carried hypothesis.**  `GateAnnihilationLev`
is the *theorem* `gateAnnihilationLev_holds`, so the containment half of the gate needs only a
level-`0` realization of `U = A(𝒱)`. -/
theorem gate_le_of_realization_uncond (R : GateRealization W (regularAMod W)) :
    OnmFull W 0 0 ≤ O W := fun x hx =>
  mem_O_of_oLevW_vanish_at_one R
    (gateAnnihilationLev_holds W R.weak R.levels x hx (R.emb_lev (one W)))

/-- **The reverse containment `O(𝒱) ≤ O_{0,0}(𝒱)`** — unconditional, off the proved
`Onm_zero_zero_eq_O` and `Onm_le_OnmFull`. -/
theorem O_le_onmFull_zero_zero (W : VertexOperatorAlgebra 𝒱) : O W ≤ OnmFull W 0 0 := by
  rw [← Onm_zero_zero_eq_O]
  exact Onm_le_OnmFull W 0 0

/-- **The gate as an equality, from the containment.**  The reverse inclusion is unconditional. -/
theorem gate_eq_of_le (hgate : OnmFull W 0 0 ≤ O W) : OnmFull W 0 0 = O W :=
  le_antisymm hgate (O_le_onmFull_zero_zero W)

/-- **B1 + B3 — the gate as an equality, from a realization alone.** -/
theorem gate_of_realization_uncond (R : GateRealization W (regularAMod W)) :
    OnmFull W 0 0 = O W :=
  gate_eq_of_le (gate_le_of_realization_uncond R)

end B3

/-! ## (C) The gate from the independent bottom-injectivity hypothesis and DLM3's `U(V̂)W ⊆ J` -/

section PBW

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The realization of the regular module supplied by B2.** `M̄_0(A(𝒱))` is a
`GateRealization W (regularAMod W)` as soon as the independent bottom-injectivity hypothesis and
DLM3's `U(V̂)W ⊆ J` are available:
`PBWFreeness.bottomProjection` supplies the `BottomProjection`, and
`gateRealizationOfSurvival` does the rest. -/
noncomputable def gateRealizationOfPbw
    (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) : GateRealization W (regularAMod W) :=
  gateRealizationOfSurvival W (regularAMod W) hP.bottomProjection hdef

/-- **THE `(0,0)` GATE, from exactly two named inputs.**

    (GATE)   OnmFull W 0 0 = O W

* `hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W))` — reduced to bottom injectivity
  because level independence is unconditional; carried as a `Prop`-valued structure, never an
  `axiom`. The companion `voaPBWFreeness` supplies this instance from the generic
  relative-induction field of the theorem `VOA.pbw : PBWPrinciple`;
* `hdef : DefectPairsToZero hP.bottomProjection` — Dong–Li–Mason's `U(V̂)W ⊆ J` at `n = 0`, whose
  base case (DLM3 Prop 4.3) is **proved** in `ZhuVermaAnArchDLM3Prop43`.

Everything else — B1 (annihilation), B3 (the regular-module instantiation), and the reverse
inclusion — is unconditional.  This is **not** a proof of the gate: it is the exact reduction. -/
theorem gate_of_pbw (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) : OnmFull W 0 0 = O W :=
  gate_of_realization_uncond (gateRealizationOfPbw hP hdef)

/-- The containment form of `gate_of_pbw`. -/
theorem gate_le_of_pbw (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) : OnmFull W 0 0 ≤ O W :=
  le_of_eq (gate_of_pbw hP hdef)

/-- **The same gate with B2's two propagation hypotheses displayed.**  `DefectPairsToZero` is
assembled by `defectPairsToZero_of_prop43` from the **proved** DLM3 Proposition 4.3 together with

* `h46 : BottomPropagates hP.bottomProjection` — DLM3 **Proposition 4.6** (bottom ⇝ all vectors);
* `h47 : OrbitPropagates hP.bottomProjection` — DLM3 **Proposition 4.7** (⇝ the `U(V̂)`-orbit).

This is the fully expanded hypothesis set of the gate: PBW plus DLM3 4.6 plus DLM3 4.7. -/
theorem gate_of_pbw_props (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (h46 : BottomPropagates hP.bottomProjection)
    (h47 : OrbitPropagates hP.bottomProjection) : OnmFull W 0 0 = O W :=
  gate_of_pbw hP
    (defectPairsToZero_of_prop43 W (regularAMod W) hP.bottomProjection h46 h47)

/-- **The residual of the `(0,0)` gate, as one named `Prop`.**  A convenience packaging of the two
carried inputs, for the `Prop`-valued consumers below.  Data-valued consumers keep the two
hypotheses explicit, since data cannot be eliminated from an `∃` over a `Prop`. -/
def GateInputs (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∃ hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)),
    DefectPairsToZero hP.bottomProjection

/-- `GateInputs` from the two hypotheses. -/
theorem gateInputs_of_pbw (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) : GateInputs W := ⟨hP, hdef⟩

/-- The gate from the packaged residual. -/
theorem gate_of_gateInputs (h : GateInputs W) : OnmFull W 0 0 = O W := by
  obtain ⟨hP, hdef⟩ := h
  exact gate_of_pbw hP hdef

end PBW

/-! ## (D) The round trip through the combinatorial generator families

`ZhuVermaAnArchOnmCollapseZero.onmFull_zero_zero_eq_O_of_gens` derives the gate from the two
Dong–Jiang generator families `O''_{0,0}` and `O'''_{0,0}`.  Those families are exactly what the
gate discharges (`assocDefect_zero_mem_of_gate`, `levelMix_zero_mem_of_gate`), so feeding them back
returns the same equality.  This is a *consistency check* of the two routes on their common
conclusion — the combinatorial route is refuted as an independent proof. -/

section Gens

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The gate, re-assembled through the two generator families.**  Chains
`assocDefect_zero_mem_of_gate` / `levelMix_zero_mem_of_gate` into
`onmFull_zero_zero_eq_O_of_gens`, which itself goes through the proved `Onm_zero_zero_eq_O`.
Agrees with `gate_eq_of_le` on the nose. -/
theorem onmFull_zero_zero_eq_O_via_gens (hgate : OnmFull W 0 0 ≤ O W) : OnmFull W 0 0 = O W :=
  onmFull_zero_zero_eq_O_of_gens W (assocDefect_zero_mem_of_gate hgate)
    (levelMix_zero_mem_of_gate hgate)

/-- `OnmCollapses W 0` — the generator-family package of `ZhuVermaAnArchOnmCollapseZero` — given the
gate. -/
theorem onmCollapses_zero_of_gate (hgate : OnmFull W 0 0 ≤ O W) : OnmCollapses W 0 :=
  onmCollapses_zero_of_gens W (assocDefect_zero_mem_of_gate hgate)
    (levelMix_zero_mem_of_gate hgate)

section Inputs

open VHat VHat.DLM3

/-- The `O''_{0,0}` (associator-defect) generator family lands in `O(𝒱)`, on the two named
inputs. -/
theorem assocDefect_zero_mem_of_pbw
    (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) (p₁ p₂ p₃ : ℕ) (a b c v : 𝒱) :
    assocDefect W 0 0 p₁ p₂ p₃ a b c v ∈ Onm W 0 0 :=
  assocDefect_zero_mem_of_gate (gate_le_of_pbw hP hdef) p₁ p₂ p₃ a b c v

/-- The `O'''_{0,0}` (level-mixing) generator family lands in `O(𝒱)`, on the two named inputs. -/
theorem levelMix_zero_mem_of_pbw
    (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) (p : ℕ) (a v g : 𝒱) (hg : g ∈ Onm W p p) :
    levelMix W 0 0 p a g v ∈ Onm W 0 0 :=
  levelMix_zero_mem_of_gate (gate_le_of_pbw hP hdef) p a v g hg

/-- The gate through the generator route, on the two named inputs. -/
theorem onmFull_zero_zero_eq_O_of_pbw
    (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) : OnmFull W 0 0 = O W :=
  onmFull_zero_zero_eq_O_via_gens (gate_le_of_pbw hP hdef)

end Inputs

end Gens

/-! ## (E) The downstream consumers -/

section Consumers

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- **`[x]_{0,0} = 0 ↔ x ∈ O(𝒱)`** — vanishing in `A_{0,0}(𝒱)` is Zhu `O(𝒱)`-membership, given the
gate. -/
theorem mkAnmFull_zero_zero_eq_zero_iff (hgate : OnmFull W 0 0 ≤ O W) (x : 𝒱) :
    mkAnmFull W 0 0 x = 0 ↔ x ∈ O W := by
  rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, gate_eq_of_le hgate]

/-- **`A_{0,0}(𝒱) ≃ A(𝒱)`** — Dong–Jiang Prop. 4.6 at `(0,0)` as a linear equivalence onto Zhu's
algebra itself, given the gate. -/
noncomputable def anmFullZeroEquivA (hgate : OnmFull W 0 0 ≤ O W) : AnmFull W 0 0 ≃ₗ[ℂ] A W :=
  Submodule.quotEquivOfEq _ _ (gate_eq_of_le hgate)

@[simp] theorem anmFullZeroEquivA_mk (hgate : OnmFull W 0 0 ≤ O W) (x : 𝒱) :
    anmFullZeroEquivA hgate (mkAnmFull W 0 0 x) = mk W x := rfl

/-! ### On the two named inputs -/

/-- **`DJAnnEqAn W 0`** — the one and only diagonal-collapse instance the chain consumes
on the two named inputs. -/
theorem djAnnEqAn_zero_of_pbw (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) : DJAnnEqAn W 0 :=
  djAnnEqAn_zero_of_gate (gate_le_of_pbw hP hdef)

/-- **`DJAnnEqAn W 0`** from the packaged residual. -/
theorem djAnnEqAn_zero_of_gateInputs (h : GateInputs W) : DJAnnEqAn W 0 := by
  obtain ⟨hP, hdef⟩ := h
  exact djAnnEqAn_zero_of_pbw hP hdef

/-- **`O_{0,0}(𝒱) = O_0(𝒱)`** on the two named inputs. -/
theorem onmFull_diag_zero_eq_of_pbw (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) : OnmFull W 0 0 = OnFull W 0 :=
  onmFull_diag_zero_eq_of_gate (gate_le_of_pbw hP hdef)

/-- **`A_{0,0}(𝒱) ≃ A_0(𝒱)`** on the two named inputs. -/
noncomputable def anmFullDiagEquivOfPbw
    (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) : AnmFull W 0 0 ≃ₗ[ℂ] AnFull W 0 :=
  anmFullDiagEquivZero (gate_le_of_pbw hP hdef)

/-- **`A_{0,0}(𝒱) ≃ A(𝒱)`** on the two named inputs. -/
noncomputable def anmFullZeroEquivAOfPbw
    (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) : AnmFull W 0 0 ≃ₗ[ℂ] A W :=
  anmFullZeroEquivA (gate_le_of_pbw hP hdef)

/-- **`M(U)(0) ≅ U`** on the `DJPiece` carrier, on the two named inputs. -/
noncomputable def djPieceMEquivOfPbw
    (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) (V : AmMod W 0) :
    DJPiece W V 0 ≃ₗ[ℂ] V.carrier :=
  djPieceMEquivZero (gate_le_of_pbw hP hdef) V

/-- **The bottom of `M(U)` is `U`** — `DJCarrier.degMEquiv` at the base level, on the two named
inputs.  This is the statement the Zhu bijection consumes. -/
noncomputable def djCarrierDegZeroEquivOfPbw
    (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) (V : AmMod W 0) :
    DJCarrier.deg W V 0 ≃ₗ[ℂ] V.carrier :=
  djCarrierDegZeroEquiv (gate_le_of_pbw hP hdef) V

/-- **The whole `Prop`-valued downstream package**, recorded in one place so the exact dependency
of the consumers is visible: the gate, `DJAnnEqAn W 0`, the diagonal identification, and the
two combinatorial generator families. -/
theorem downstream_of_pbw (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero hP.bottomProjection) :
    OnmFull W 0 0 = O W ∧ DJAnnEqAn W 0 ∧ OnmFull W 0 0 = OnFull W 0 ∧ OnmCollapses W 0 := by
  have hle : OnmFull W 0 0 ≤ O W := gate_le_of_pbw hP hdef
  exact ⟨gate_eq_of_le hle, djAnnEqAn_zero_of_gate hle, onmFull_diag_zero_eq_of_gate hle,
    onmCollapses_zero_of_gate hle⟩

/-- The same package with B2's two propagation hypotheses (DLM3 Props 4.6 / 4.7) displayed. -/
theorem downstream_of_pbw_props (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (h46 : BottomPropagates hP.bottomProjection)
    (h47 : OrbitPropagates hP.bottomProjection) :
    OnmFull W 0 0 = O W ∧ DJAnnEqAn W 0 ∧ OnmFull W 0 0 = OnFull W 0 ∧ OnmCollapses W 0 :=
  downstream_of_pbw hP
    (defectPairsToZero_of_prop43 W (regularAMod W) hP.bottomProjection h46 h47)

end Consumers

end VOA
