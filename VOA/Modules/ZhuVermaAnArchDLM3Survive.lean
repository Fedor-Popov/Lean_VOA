/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3Propagate
import VOA.Modules.ZhuVermaAnArchDJGeneration

/-!
# B2 assembled — `DefectPairsToZero` proved, and the `(0,0)` gate conditional on `Pr`

This is the **assembly** step of the B2 attack plan (`PHASE4_PLAN` C-11), and it closes the last
representation-theoretic input.  The earlier slices are proved in the imported files:

* **S0** — DLM3 Proposition 3.1's bracket compatibility: *discharged*, `ParabolicRep.act` is a
  bundled Lie morphism and `parabolicRepOfAMod` supplies `map_lie'`
  (`parabolicRepOfAMod_act_lie`, `ZhuVermaAnArchDLM3Pairing`).
* **S1 / S2** — DLM3 Lemma 4.4 at `n = 0` (`indDefectVec_bottom_neg_one`) and Lemma 4.5
  (`indDefectVec_bottom_negPole`), assembled into DLM3 Proposition 4.3 at `n = 0`
  (`proj_indDefectVec_bottom`, `ZhuVermaAnArchDLM3Prop43`).
* **S3 / S4** — DLM3 Propositions 4.6 and 4.7 (`bottomPropagates_of_modeShift`,
  `orbitPropagates_of_modeShift`, `ZhuVermaAnArchDLM3Propagate`), which were proved *modulo* the
  named representation-level hypothesis `VHatRep.DefectModeShift` (DLM2 Proposition 6.1 at the
  canonical pole `ℓ = −1`).

## What this file proves

**`defectModeShift_of_truncated` — `DefectModeShift` is a THEOREM** for every `V̂`-representation
with truncated modes.  Its three ingredients:

1. `gsum_actMode_shift` — pushing `c₍ₖ₎` leftwards through the normal-ordered sum
   `G(a,b,x,0,N)`, which costs one singular-OPE family in each `𝒱`-slot; the `a`-slot family lands
   at the **shifted** left index `s = k − q` (`pterm_actMode_shift`, `qterm_actMode_shift`);
2. the proved `sumR_sub_gsum_shift` (the `a`-slot shift law, itself resting on the hockey stick
   `gsum_sub_gsum_zero`), which turns that shifted sum back into a canonical defect plus a
   `𝒱`-level tail;
3. `vlevel_cancel` — the `𝒱`-level commutator `[c₍ₜ₎, a₍₋₁₎]` cancelling the two tails.  Its
   combinatorial content is the subset-of-subset identity `C(k,t)·C(t,q) = C(k,q)·C(k−q,t−q)`
   (`cbz_subsetOfSubset`) together with the triangle reindex `t = q + r`
   (`finsum_triangle_reindex`).

Consequently:

* `defectPairsToZero_of_bottomProjection` — **`DefectPairsToZero Pr` for a general `U : AMod W`**,
  with *no* hypothesis beyond the projection `Pr`.  This is DLM3's `U(V̂)W ⊆ J` at `n = 0`.
* `indBarBottom_injective_of_bottomProjection` — **`U` survives** (DLM3 Theorem 4.1 at `n = 0`).
* `gate_of_pbwDatum` — **the `(0,0)` gate `OnmFull W 0 0 = O W`**, fed through
  `gate_of_dlm3`, whose **only** remaining hypothesis is input (i), the independent
  `BottomProjection` assumption.
* the downstream package on that same single hypothesis: `DJAnnEqAn W 0`,
  `OnmFull W 0 0 = OnFull W 0`, `OnmCollapses W 0`, `AnmFull W 0 0 ≃ A_0(𝒱)`, `M(U)(0) ≅ U` on
  `DJPiece` and on `DJCarrier.deg`, and DJ Theorem 4.10's generation sentence.

The `hshift`-carrying statements of sections (1)–(3) are kept: they record the exact reduction and
are instances of the unconditional ones.

## Status, stated without over-claim

The gate is **NOT proved outright**.  It is reduced to exactly ONE named hypothesis, carried
explicitly in every signature of section (5):

* `Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))` — an explicit
  bottom-injectivity assumption, carried rather than silently introduced. The project-level witness
  `voaPBWBottomProjection` is supplied from the generic relative-induction field of the
  theorem `VOA.pbw : PBWPrinciple`.

No `sorry`, no `admit`, no `native_decide`, and no new `axiom`. A
clean `#print axioms` result does not report the explicit `Pr` parameter and cannot certify this
conditional gate as unconditional or satisfiable.

## References
DLM3 (`q-alg/9612010v2`) §4: Lemma 4.4 (`refs/dlm3.txt:774`), Lemma 4.5 (`:1029`),
Props 4.6/4.7 (`:1086`, `:1098`); DLM2 (`q-alg/9509005`) Prop 6.1 (`refs/dlm2.txt:784-911`);
DJ (`math/0601626`) Prop 4.6 (`refs/dj.txt:1326`), Thm 4.10 (`:1541`), Thm 4.13 (`:1688`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace DLM3

/-! ## (1) `DefectPairsToZero`, assembled, for a general `A(𝒱)`-module `U` -/

section Assembly

/-- **`DefectPairsToZero Pr`, assembled** — S1 + S2 (proved as DLM3 Proposition 4.3 at `n = 0`,
`proj_indDefectVec_bottom`) followed by S3 + S4 (`bottomPropagates_of_modeShift` /
`orbitPropagates_of_modeShift`).

Stated for a **general** `U : AMod W`, not just the regular module: the Zhu bijection needs
`U` survives at every irreducible `U`, and the proof is the same one.

Carried hypotheses, both explicit: `Pr` (the independent `BottomProjection`/bottom-injectivity
datum) and `hshift` (DLM2 Prop 6.1 at `ℓ = −1`). -/
theorem defectPairsToZero_assembled (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W U))) :
    DefectPairsToZero Pr :=
  defectPairsToZero_of_modeShift_aMod W U Pr hshift

/-- The same statement **fully unfolded** — DLM3's `U(V̂)W ⊆ J` verbatim: the bottom projection
kills every `U(V̂)`-translate of every iterate defect, at every pole `ℓ` and every residue `K`. -/
theorem proj_uenv_defectVec_eq_zero (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W U)))
    (a b : 𝒱) (z : IndMod (parabolicRepOfAMod W U)) (ℓ K : ℤ) (y : UEnv W) :
    Pr.proj ((indRho (parabolicRepOfAMod W U)).toAlgHom y
      (VHatRep.defectVec (indRho (parabolicRepOfAMod W U)) a b z ℓ K)) = 0 :=
  defectPairsToZero_assembled W U Pr hshift a b z ℓ K y

/-- The defect submodule is inside the radical of the pairing — the submodule form of
`defectPairsToZero_assembled`. -/
theorem defectSubmodule_le_radical_assembled (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W U))) :
    VHatRep.defectSubmodule (indRho (parabolicRepOfAMod W U)) ≤ radical Pr :=
  defectSubmodule_le_radical Pr (defectPairsToZero_assembled W U Pr hshift)

/-- **`U` survives in `M̄(U)`** — DLM3's `J ∩ U = 0` at `n = 0`, for a general `U : AMod W`. -/
theorem indBarBottom_injective_assembled (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W U))) :
    Function.Injective (indBarBottom (parabolicRepOfAMod W U)) :=
  indBarBottom_injective_of_defectPairsToZero Pr (defectPairsToZero_assembled W U Pr hshift)

/-- The separating realization of `U` that `indBarBottom_injective_assembled` produces
(`indBarBottom_injective_iff`).  This is DLM3 Theorem 4.1 at `n = 0`, in the repo's phrasing. -/
theorem exists_separating_realization (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W U))) :
    ∃ R : Realization W 0 U.carrier (parabolicRepOfAMod W U), R.Separates :=
  (indBarBottom_injective_iff (parabolicRepOfAMod W U)).mp
    (indBarBottom_injective_assembled W U Pr hshift)

end Assembly

end DLM3
end VHat

/-! ## (2) The gate, fed through `gate_of_dlm3` -/

section Gate

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- **THE `(0,0)` GATE**, fed through `gate_of_dlm3`, on exactly two named hypotheses:

* `Pr` — input (i) of `gate_of_dlm3`, the **PBW / Harish-Chandra datum**, carried as data;
* `hshift` — input (ii)'s residual after S1–S4, DLM2 Proposition 6.1 at `ℓ = −1`.

Both are visible in the signature.  This is a **reduction**, not a proof of the gate. -/
theorem gate_of_bottomProjection_modeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W)))) :
    OnmFull W 0 0 = O W :=
  gate_of_dlm3 Pr (defectPairsToZero_assembled W (regularAMod W) Pr hshift)

/-- The gate as an inclusion, the form the downstream consumers take. -/
theorem gate_le_of_bottomProjection_modeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W)))) :
    OnmFull W 0 0 ≤ O W :=
  le_of_eq (gate_of_bottomProjection_modeShift Pr hshift)

/-! ## (3) The downstream package -/

/-- **DJ Proposition 4.6 at the base level** (`A_{0,0}(𝒱) = A_0(𝒱)` at the ideal level) and the
two identifications it feeds, on the same two hypotheses. -/
theorem downstream_of_bottomProjection_modeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W)))) :
    OnmFull W 0 0 = O W ∧ DJAnnEqAn W 0 ∧ OnmFull W 0 0 = OnFull W 0 :=
  downstream_of_dlm3 Pr (defectPairsToZero_assembled W (regularAMod W) Pr hshift)

/-- `DJAnnEqAn W 0` — the single diagonal-collapse instance the whole chain consumes
(`PHASE4_PLAN` C-1). -/
theorem djAnnEqAn_zero_of_bottomProjection_modeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W)))) :
    DJAnnEqAn W 0 :=
  djAnnEqAn_zero_of_gate (gate_le_of_bottomProjection_modeShift Pr hshift)

/-- The level-`0` collapse predicate `OnmFull W 0 0 ≤ Onm W 0 0`. -/
theorem onmCollapses_zero_of_bottomProjection_modeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W)))) :
    OnmCollapses W 0 :=
  onmCollapses_zero_of_gate (gate_le_of_bottomProjection_modeShift Pr hshift)

/-- **`A_{0,0}(𝒱) ≃ A_0(𝒱)`**, on the two hypotheses. -/
noncomputable def anmFullDiagEquivOfModeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W)))) :
    AnmFull W 0 0 ≃ₗ[ℂ] AnFull W 0 :=
  anmFullDiagEquivZero (gate_le_of_bottomProjection_modeShift Pr hshift)

/-- **`M(U)(0) ≅ U`** on the `DJPiece` carrier, on the two hypotheses. -/
noncomputable def djPieceMEquivOfModeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W))))
    (V : AmMod W 0) : DJPiece W V 0 ≃ₗ[ℂ] V.carrier :=
  djPieceMEquivZero (gate_le_of_bottomProjection_modeShift Pr hshift) V

/-- **The bottom of `M(U)` is `U`** on the graded carrier — the statement the Zhu bijection
consumes, on the two hypotheses. -/
noncomputable def djCarrierDegZeroEquivOfModeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W))))
    (V : AmMod W 0) : DJCarrier.deg W V 0 ≃ₗ[ℂ] V.carrier :=
  djCarrierDegZeroEquiv (gate_le_of_bottomProjection_modeShift Pr hshift) V

/-- **DJ Theorem 4.10's generation sentence** — "`M(U)` is generated by `U`" — at the base level,
on the two hypotheses. -/
theorem djCarrier_generated_by_U_of_modeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W))))
    (U : AmMod W 0) (hD : DJActionDescent W 0) (S : Submodule ℂ (DJCarrier W U))
    (hS : DJModeStable W U hD S)
    (hU : ∀ w : U.carrier,
      (((DJCarrier.degMEquiv W 0
          (djAnnEqAn_zero_of_bottomProjection_modeShift Pr hshift) U).symm w :
          DJCarrier.deg W U 0) : DJCarrier W U) ∈ S) :
    S = ⊤ :=
  djCarrier_generated_by_U (djAnnEqAn_zero_of_bottomProjection_modeShift Pr hshift) U hD S hS hU

/-- The gate discharges the associator generator family of the (refuted) combinatorial route. -/
theorem assocDefect_zero_mem_of_modeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W))))
    (p₁ p₂ p₃ : ℕ) (a b c v : 𝒱) : assocDefect W 0 0 p₁ p₂ p₃ a b c v ∈ Onm W 0 0 :=
  assocDefect_zero_mem_of_gate (gate_le_of_bottomProjection_modeShift Pr hshift) p₁ p₂ p₃ a b c v

/-- The gate discharges the level-mixing generator family of the (refuted) combinatorial route. -/
theorem levelMix_zero_mem_of_modeShift
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W))))
    (p : ℕ) (a v g : 𝒱) (hg : g ∈ Onm W p p) : levelMix W 0 0 p a g v ∈ Onm W 0 0 :=
  levelMix_zero_mem_of_gate (gate_le_of_bottomProjection_modeShift Pr hshift) p a v g hg

/-! ### The same package off the `PBWFreeness` phrasing of the datum -/

/-- The gate off `PBWFreeness` (which *produces* a `BottomProjection`) instead of a raw
`BottomProjection`. -/
theorem gate_of_pbwFreeness_modeShift
    (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W)))) :
    OnmFull W 0 0 = O W :=
  gate_of_bottomProjection_modeShift hP.bottomProjection hshift

end Gate


/-! ## (4) Working towards `DefectModeShift`: `finsum` infrastructure -/

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Support finiteness on `ℕ × ℕ` from a uniform bound on the second index together with
row-wise finiteness in the first. -/
theorem support_pair_finite {N : Type*} [Zero N] (K : ℕ) (F : ℕ → ℕ → N)
    (hcol : ∀ i p : ℕ, K ≤ p → F i p = 0)
    (hrow : ∀ p : ℕ, (Function.support fun i => F i p).Finite) :
    (Function.support fun z : ℕ × ℕ => F z.1 z.2).Finite := by
  refine Set.Finite.subset ((Set.finite_Iio K).biUnion
    (fun p _ => (hrow p).image (fun i => (i, p)))) ?_
  rintro ⟨i, p⟩ hz
  rw [Function.mem_support] at hz
  refine Set.mem_biUnion (show p ∈ Set.Iio K from ?_) ⟨i, hz, rfl⟩
  rw [Set.mem_Iio]
  by_contra h
  rw [not_lt] at h
  exact hz (hcol i p h)

/-- Swapping two `ℕ`-indexed `finsum`s whose joint support on `ℕ × ℕ` is finite. -/
theorem finsum_pair_swap {N : Type*} [AddCommMonoid N] (F : ℕ → ℕ → N)
    (hF : (Function.support fun z : ℕ × ℕ => F z.1 z.2).Finite) :
    (∑ᶠ i : ℕ, ∑ᶠ p : ℕ, F i p) = ∑ᶠ p : ℕ, ∑ᶠ i : ℕ, F i p := by
  have hG : (Function.support fun z : ℕ × ℕ => F z.2 z.1).Finite := by
    refine Set.Finite.subset (hF.image (fun z : ℕ × ℕ => (z.2, z.1))) ?_
    rintro ⟨p, i⟩ hz
    exact ⟨(i, p), hz, rfl⟩
  have h1 : (∑ᶠ z : ℕ × ℕ, F z.1 z.2) = ∑ᶠ (i : ℕ) (p : ℕ), F i p := finsum_curry _ hF
  have h2 : (∑ᶠ z : ℕ × ℕ, F z.2 z.1) = ∑ᶠ (p : ℕ) (i : ℕ), F i p := finsum_curry _ hG
  have h3 : (∑ᶠ z : ℕ × ℕ, F z.2 z.1) = ∑ᶠ z : ℕ × ℕ, F z.1 z.2 :=
    finsum_comp_equiv (Equiv.prodComm ℕ ℕ) (f := fun z : ℕ × ℕ => F z.1 z.2)
  rw [← h1, ← h3, h2]

/-- The singular-OPE family `t ↦ g t • (c₍ₜ₎v)₍m t₎x` has finite support, for **any** mode
assignment `m` — the `𝒱`-level truncation `W.smul_eventually_zero` alone bounds it. -/
theorem opeVec_support_finite (ρ : VHatRep W M) (c v : 𝒱) (x : M) (g : ℕ → ℂ) (m : ℕ → ℤ) :
    (Function.support fun t : ℕ => g t • ρ.actMode (W.smul c (t : ℤ) v) (m t) x).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero c v
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro t ht
  rw [Function.mem_support] at ht
  rw [Set.mem_Iio]
  by_contra hcon
  exact ht (by rw [hNz (t : ℤ) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero])

/-- The vanishing bound behind `opeVec_support_finite`, in the form used for column bounds. -/
theorem opeVec_eq_zero_of_le (ρ : VHatRep W M) (c v : 𝒱) {Nz : ℤ}
    (hNz : ∀ t : ℤ, Nz ≤ t → W.smul c t v = 0) (x : M) (g : ℕ → ℂ) (m : ℕ → ℤ) {t : ℕ}
    (ht : Nz ≤ (t : ℤ)) : g t • ρ.actMode (W.smul c (t : ℤ) v) (m t) x = 0 := by
  rw [hNz (t : ℤ) ht, actMode_zero_left, LinearMap.zero_apply, smul_zero]

/-! ### The two normal-ordered halves under a mode shift -/

/-- **The `p`-half of DLM2 Proposition 6.1**: pushing `c₍ₖ₎` leftwards through
`a₍₋₁₋ᵢ₎ b₍N₊ᵢ₎` costs exactly two singular-OPE families, one in each slot.  The `a`-slot family
lands at the **shifted** left index `s = k − q`; that shift is what the hockey stick
(`gsum_sub_gsum_zero`) later absorbs. -/
theorem pterm_actMode_shift (ρ : VHatRep W M) (a b c : 𝒱) (x : M) (k N : ℤ) (i : ℕ) :
    pterm ρ a b (ρ.actMode c k x) 0 N i
      = ρ.actMode c k (pterm ρ a b x 0 N i)
        - (∑ᶠ p : ℕ, cbz k (p : ℤ) • pterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i)
        - ∑ᶠ q : ℕ, cbz k (q : ℤ) • pterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i := by
  have hfinb : (Function.support fun t : ℕ =>
      cbz k (t : ℤ) • ρ.actMode (W.smul c (t : ℤ) b) (k + (N + (i : ℤ)) - (t : ℤ)) x).Finite :=
    opeVec_support_finite ρ c b x (fun t => cbz k (t : ℤ))
      (fun t => k + (N + (i : ℤ)) - (t : ℤ))
  have hb : ρ.actMode b (N + (i : ℤ)) (ρ.actMode c k x)
      = ρ.actMode c k (ρ.actMode b (N + (i : ℤ)) x)
        - ∑ᶠ t : ℕ, cbz k (t : ℤ) •
            ρ.actMode (W.smul c (t : ℤ) b) (k + (N + (i : ℤ)) - (t : ℤ)) x := by
    rw [← actMode_comm_vec ρ c b x k (N + (i : ℤ))]
    abel
  have h2 : ρ.actMode a ((0 : ℤ) - 1 - (i : ℤ)) (ρ.actMode b (N + (i : ℤ)) (ρ.actMode c k x))
      = ρ.actMode a ((0 : ℤ) - 1 - (i : ℤ)) (ρ.actMode c k (ρ.actMode b (N + (i : ℤ)) x))
        - ∑ᶠ p : ℕ, cbz k (p : ℤ) •
            pterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i := by
    rw [hb, map_sub, map_finsum _ hfinb]
    congr 1
    refine finsum_congr fun t => ?_
    rw [map_smul, pterm, show k + N - (t : ℤ) + (i : ℤ) = k + (N + (i : ℤ)) - (t : ℤ) from by ring]
  have hfina : (Function.support fun q : ℕ =>
      cbz k (q : ℤ) • ρ.actMode (W.smul c (q : ℤ) a) (k + ((0 : ℤ) - 1 - (i : ℤ)) - (q : ℤ))
        (ρ.actMode b (N + (i : ℤ)) x)).Finite :=
    opeVec_support_finite ρ c a (ρ.actMode b (N + (i : ℤ)) x) (fun q => cbz k (q : ℤ))
      (fun q => k + ((0 : ℤ) - 1 - (i : ℤ)) - (q : ℤ))
  have ha : ρ.actMode a ((0 : ℤ) - 1 - (i : ℤ)) (ρ.actMode c k (ρ.actMode b (N + (i : ℤ)) x))
      = ρ.actMode c k (pterm ρ a b x 0 N i)
        - ∑ᶠ q : ℕ, cbz k (q : ℤ) • pterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i := by
    have hcomm := actMode_comm_vec ρ c a (ρ.actMode b (N + (i : ℤ)) x) k ((0 : ℤ) - 1 - (i : ℤ))
    have hre : (∑ᶠ q : ℕ, cbz k (q : ℤ) •
        ρ.actMode (W.smul c (q : ℤ) a) (k + ((0 : ℤ) - 1 - (i : ℤ)) - (q : ℤ))
          (ρ.actMode b (N + (i : ℤ)) x))
        = ∑ᶠ q : ℕ, cbz k (q : ℤ) • pterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i := by
      refine finsum_congr fun q => ?_
      rw [pterm, show k - (q : ℤ) - 1 - (i : ℤ) = k + ((0 : ℤ) - 1 - (i : ℤ)) - (q : ℤ) from by
        ring]
    rw [← hre, ← hcomm, pterm]
    abel
  rw [pterm, h2, ha]
  abel

/-- **The `q`-half of DLM2 Proposition 6.1**, the mirror of `pterm_actMode_shift`. -/
theorem qterm_actMode_shift (ρ : VHatRep W M) (a b c : 𝒱) (x : M) (k N : ℤ) (i : ℕ) :
    qterm ρ a b (ρ.actMode c k x) 0 N i
      = ρ.actMode c k (qterm ρ a b x 0 N i)
        - (∑ᶠ p : ℕ, cbz k (p : ℤ) • qterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i)
        - ∑ᶠ q : ℕ, cbz k (q : ℤ) • qterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i := by
  have hfina : (Function.support fun q : ℕ => cbz k (q : ℤ) •
      ρ.actMode (W.smul c (q : ℤ) a) (k + ((0 : ℤ) + (i : ℤ)) - (q : ℤ)) x).Finite :=
    opeVec_support_finite ρ c a x (fun q => cbz k (q : ℤ))
      (fun q => k + ((0 : ℤ) + (i : ℤ)) - (q : ℤ))
  have ha : ρ.actMode a ((0 : ℤ) + (i : ℤ)) (ρ.actMode c k x)
      = ρ.actMode c k (ρ.actMode a ((0 : ℤ) + (i : ℤ)) x)
        - ∑ᶠ q : ℕ, cbz k (q : ℤ) •
            ρ.actMode (W.smul c (q : ℤ) a) (k + ((0 : ℤ) + (i : ℤ)) - (q : ℤ)) x := by
    rw [← actMode_comm_vec ρ c a x k ((0 : ℤ) + (i : ℤ))]
    abel
  have h2 : ρ.actMode b (N - 1 - (i : ℤ)) (ρ.actMode a ((0 : ℤ) + (i : ℤ)) (ρ.actMode c k x))
      = ρ.actMode b (N - 1 - (i : ℤ)) (ρ.actMode c k (ρ.actMode a ((0 : ℤ) + (i : ℤ)) x))
        - ∑ᶠ q : ℕ, cbz k (q : ℤ) • qterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i := by
    rw [ha, map_sub, map_finsum _ hfina]
    congr 1
    refine finsum_congr fun q => ?_
    rw [map_smul, qterm, show k - (q : ℤ) + (i : ℤ) = k + ((0 : ℤ) + (i : ℤ)) - (q : ℤ) from by
      ring]
  have hfinb : (Function.support fun p : ℕ =>
      cbz k (p : ℤ) • ρ.actMode (W.smul c (p : ℤ) b) (k + (N - 1 - (i : ℤ)) - (p : ℤ))
        (ρ.actMode a ((0 : ℤ) + (i : ℤ)) x)).Finite :=
    opeVec_support_finite ρ c b (ρ.actMode a ((0 : ℤ) + (i : ℤ)) x) (fun p => cbz k (p : ℤ))
      (fun p => k + (N - 1 - (i : ℤ)) - (p : ℤ))
  have hb : ρ.actMode b (N - 1 - (i : ℤ)) (ρ.actMode c k (ρ.actMode a ((0 : ℤ) + (i : ℤ)) x))
      = ρ.actMode c k (qterm ρ a b x 0 N i)
        - ∑ᶠ p : ℕ, cbz k (p : ℤ) • qterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i := by
    have hcomm := actMode_comm_vec ρ c b (ρ.actMode a ((0 : ℤ) + (i : ℤ)) x) k (N - 1 - (i : ℤ))
    have hre : (∑ᶠ p : ℕ, cbz k (p : ℤ) •
        ρ.actMode (W.smul c (p : ℤ) b) (k + (N - 1 - (i : ℤ)) - (p : ℤ))
          (ρ.actMode a ((0 : ℤ) + (i : ℤ)) x))
        = ∑ᶠ p : ℕ, cbz k (p : ℤ) • qterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i := by
      refine finsum_congr fun p => ?_
      rw [qterm, show k + N - (p : ℤ) - 1 - (i : ℤ) = k + (N - 1 - (i : ℤ)) - (p : ℤ) from by ring]
    rw [← hre, ← hcomm, qterm]
    abel
  rw [qterm, h2, hb]

/-! ### Summing a pointwise mode-shift identity over the normal-ordering index -/

/-- A marginal of a jointly finitely supported family is finitely supported. -/
theorem support_marginal_finite {N : Type*} [AddCommMonoid N] (F : ℕ → ℕ → N)
    (hF : (Function.support fun z : ℕ × ℕ => F z.1 z.2).Finite) :
    (Function.support fun i : ℕ => ∑ᶠ p : ℕ, F i p).Finite := by
  refine Set.Finite.subset (hF.image Prod.fst) ?_
  intro i hi
  rw [Function.mem_support] at hi
  by_contra h
  refine hi (finsum_eq_zero_of_forall_eq_zero fun p => ?_)
  by_contra hp
  exact h ⟨(i, p), hp, rfl⟩

/-- The bookkeeping step: a pointwise identity `A i = B i − Σᶠ C i · − Σᶠ D i ·` sums, over the
normal-ordering index `i`, to the same identity with the two correction sums swapped to the
outside. -/
theorem finsum_sub_sub_swap {N : Type*} [AddCommGroup N] (A B : ℕ → N) (C D : ℕ → ℕ → N)
    (hpt : ∀ i, A i = B i - (∑ᶠ p : ℕ, C i p) - ∑ᶠ q : ℕ, D i q)
    (hB : (Function.support B).Finite)
    (hC : (Function.support fun z : ℕ × ℕ => C z.1 z.2).Finite)
    (hD : (Function.support fun z : ℕ × ℕ => D z.1 z.2).Finite) :
    (∑ᶠ i : ℕ, A i)
      = (∑ᶠ i : ℕ, B i) - (∑ᶠ p : ℕ, ∑ᶠ i : ℕ, C i p) - ∑ᶠ q : ℕ, ∑ᶠ i : ℕ, D i q := by
  have hCm := support_marginal_finite C hC
  have hDm := support_marginal_finite D hD
  have hBC : (Function.support fun i : ℕ => B i - ∑ᶠ p : ℕ, C i p).Finite :=
    Set.Finite.subset (hB.union hCm) (Function.support_sub _ _)
  rw [finsum_congr hpt, finsum_sub_distrib hBC hDm, finsum_sub_distrib hB hCm,
    finsum_pair_swap C hC, finsum_pair_swap D hD]

/-! ### Vanishing of the normal-ordered halves in a zero slot -/

@[simp] theorem pterm_zero_left (ρ : VHatRep W M) (b : 𝒱) (x : M) (s N : ℤ) (i : ℕ) :
    pterm ρ (0 : 𝒱) b x s N i = 0 := by
  rw [pterm, actMode_zero_left, LinearMap.zero_apply]

@[simp] theorem pterm_zero_right (ρ : VHatRep W M) (a : 𝒱) (x : M) (s N : ℤ) (i : ℕ) :
    pterm ρ a (0 : 𝒱) x s N i = 0 := by
  rw [pterm, actMode_zero_left, LinearMap.zero_apply, map_zero]

@[simp] theorem qterm_zero_left (ρ : VHatRep W M) (b : 𝒱) (x : M) (s N : ℤ) (i : ℕ) :
    qterm ρ (0 : 𝒱) b x s N i = 0 := by
  rw [qterm, actMode_zero_left, LinearMap.zero_apply, map_zero]

@[simp] theorem qterm_zero_right (ρ : VHatRep W M) (a : 𝒱) (x : M) (s N : ℤ) (i : ℕ) :
    qterm ρ a (0 : 𝒱) x s N i = 0 := by
  rw [qterm, actMode_zero_left, LinearMap.zero_apply]

@[simp] theorem gsum_zero_left (ρ : VHatRep W M) (b : 𝒱) (x : M) (s N : ℤ) :
    gsum ρ (0 : 𝒱) b x s N = 0 := by
  rw [gsum, finsum_eq_zero_of_forall_eq_zero fun i => pterm_zero_left ρ b x s N i,
    finsum_eq_zero_of_forall_eq_zero fun i => qterm_zero_left ρ b x s N i, add_zero]

@[simp] theorem gsum_zero_right (ρ : VHatRep W M) (a : 𝒱) (x : M) (s N : ℤ) :
    gsum ρ a (0 : 𝒱) x s N = 0 := by
  rw [gsum, finsum_eq_zero_of_forall_eq_zero fun i => pterm_zero_right ρ a x s N i,
    finsum_eq_zero_of_forall_eq_zero fun i => qterm_zero_right ρ a x s N i, add_zero]

/-! ### Joint support bookkeeping for the singular-OPE families -/

/-- Finiteness of an OPE-indexed family of vectors that vanishes whenever its `𝒱`-slot does. -/
theorem opeSlot_support_finite (W : VertexOperatorAlgebra 𝒱) (c v : 𝒱) (g : ℕ → ℂ) (H : ℕ → M)
    (hz : ∀ p : ℕ, W.smul c (p : ℤ) v = 0 → H p = 0) :
    (Function.support fun p : ℕ => g p • H p).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero c v
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) fun p hp => ?_
  rw [Function.mem_support] at hp
  rw [Set.mem_Iio]
  by_contra h
  exact hp (by rw [hz p (hNz (p : ℤ) (by omega)), smul_zero])

/-- Joint (`ℕ × ℕ`) support finiteness for an OPE-indexed family of normal-ordered terms: the
`𝒱`-level truncation bounds the OPE index, and each fixed OPE index has finite normal-ordering
support. -/
theorem opeFamily_pair_support_finite (W : VertexOperatorAlgebra 𝒱) (c v : 𝒱) (g : ℕ → ℂ)
    (H : ℕ → ℕ → M) (hz : ∀ p i : ℕ, W.smul c (p : ℤ) v = 0 → H i p = 0)
    (hrow : ∀ p : ℕ, (Function.support fun i : ℕ => H i p).Finite) :
    (Function.support fun z : ℕ × ℕ => g z.2 • H z.1 z.2).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero c v
  refine support_pair_finite Nz.toNat (fun i p => g p • H i p) (fun i p hp => ?_) (fun p => ?_)
  · dsimp only
    rw [hz p i (hNz (p : ℤ) (by omega)), smul_zero]
  · refine Set.Finite.subset (hrow p) fun i hi => ?_
    rw [Function.mem_support] at hi ⊢
    intro h
    exact hi (by dsimp only; rw [h, smul_zero])

/-! ### The mode-shift law for the shifted normal-ordered sum -/

/-- **The normal-ordered sum under a mode shift** — the `G`-level form of DLM2 Proposition 6.1:

    G(a,b,c₍ₖ₎x,0,N) = c₍ₖ₎·G(a,b,x,0,N)
                        − Σ_p C(k,p)·G(a, c₍ₚ₎b, x, 0, k+N−p)
                        − Σ_q C(k,q)·G(c₍q₎a, b, x, k−q, N).

Note the **shifted left index** `k − q` in the last family: pushing `c₍ₖ₎` past the `a`-slot moves
the whole normal-ordering window, and that shift is exactly what the hockey stick
(`gsum_sub_gsum_zero`) / the `a`-slot shift law (`sumR_sub_gsum_shift`) absorb. -/
theorem gsum_actMode_shift (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b c : 𝒱) (x : M)
    (k N : ℤ) :
    gsum ρ a b (ρ.actMode c k x) 0 N
      = ρ.actMode c k (gsum ρ a b x 0 N)
        - (∑ᶠ p : ℕ, cbz k (p : ℤ) • gsum ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)))
        - ∑ᶠ q : ℕ, cbz k (q : ℤ) • gsum ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N := by
  -- joint supports of the four correction families
  have hCp : (Function.support fun z : ℕ × ℕ => cbz k (z.2 : ℤ) •
      pterm ρ a (W.smul c (z.2 : ℤ) b) x 0 (k + N - (z.2 : ℤ)) z.1).Finite :=
    opeFamily_pair_support_finite W c b (fun p => cbz k (p : ℤ))
      (fun i p => pterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i)
      (fun p i h => by dsimp only; rw [h, pterm_zero_right])
      (fun p => pterm_support_finite ρ htr a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)))
  have hDp : (Function.support fun z : ℕ × ℕ => cbz k (z.2 : ℤ) •
      pterm ρ (W.smul c (z.2 : ℤ) a) b x (k - (z.2 : ℤ)) N z.1).Finite :=
    opeFamily_pair_support_finite W c a (fun q => cbz k (q : ℤ))
      (fun i q => pterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i)
      (fun q i h => by dsimp only; rw [h, pterm_zero_left])
      (fun q => pterm_support_finite ρ htr (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N)
  have hCq : (Function.support fun z : ℕ × ℕ => cbz k (z.2 : ℤ) •
      qterm ρ a (W.smul c (z.2 : ℤ) b) x 0 (k + N - (z.2 : ℤ)) z.1).Finite :=
    opeFamily_pair_support_finite W c b (fun p => cbz k (p : ℤ))
      (fun i p => qterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i)
      (fun p i h => by dsimp only; rw [h, qterm_zero_right])
      (fun p => qterm_support_finite ρ htr a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)))
  have hDq : (Function.support fun z : ℕ × ℕ => cbz k (z.2 : ℤ) •
      qterm ρ (W.smul c (z.2 : ℤ) a) b x (k - (z.2 : ℤ)) N z.1).Finite :=
    opeFamily_pair_support_finite W c a (fun q => cbz k (q : ℤ))
      (fun i q => qterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i)
      (fun q i h => by dsimp only; rw [h, qterm_zero_left])
      (fun q => qterm_support_finite ρ htr (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N)
  have hBp : (Function.support fun i : ℕ => ρ.actMode c k (pterm ρ a b x 0 N i)).Finite := by
    refine Set.Finite.subset (pterm_support_finite ρ htr a b x 0 N) fun i hi => ?_
    rw [Function.mem_support] at hi ⊢
    intro h
    exact hi (by rw [h, map_zero])
  have hBq : (Function.support fun i : ℕ => ρ.actMode c k (qterm ρ a b x 0 N i)).Finite := by
    refine Set.Finite.subset (qterm_support_finite ρ htr a b x 0 N) fun i hi => ?_
    rw [Function.mem_support] at hi ⊢
    intro h
    exact hi (by rw [h, map_zero])
  -- the two halves, summed over the normal-ordering index
  have hP := finsum_sub_sub_swap (fun i => pterm ρ a b (ρ.actMode c k x) 0 N i)
    (fun i => ρ.actMode c k (pterm ρ a b x 0 N i))
    (fun i p => cbz k (p : ℤ) • pterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i)
    (fun i q => cbz k (q : ℤ) • pterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i)
    (fun i => pterm_actMode_shift ρ a b c x k N i) hBp hCp hDp
  have hQ := finsum_sub_sub_swap (fun i => qterm ρ a b (ρ.actMode c k x) 0 N i)
    (fun i => ρ.actMode c k (qterm ρ a b x 0 N i))
    (fun i p => cbz k (p : ℤ) • qterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i)
    (fun i q => cbz k (q : ℤ) • qterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i)
    (fun i => qterm_actMode_shift ρ a b c x k N i) hBq hCq hDq
  dsimp only at hP hQ
  -- pull the mode and the scalars out of the inner sums
  rw [← map_finsum (ρ.actMode c k) (pterm_support_finite ρ htr a b x 0 N)] at hP
  rw [← map_finsum (ρ.actMode c k) (qterm_support_finite ρ htr a b x 0 N)] at hQ
  rw [finsum_congr fun p : ℕ => (smul_finsum' (cbz k (p : ℤ))
      (pterm_support_finite ρ htr a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)))).symm,
    finsum_congr fun q : ℕ => (smul_finsum' (cbz k (q : ℤ))
      (pterm_support_finite ρ htr (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N)).symm] at hP
  rw [finsum_congr fun p : ℕ => (smul_finsum' (cbz k (p : ℤ))
      (qterm_support_finite ρ htr a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)))).symm,
    finsum_congr fun q : ℕ => (smul_finsum' (cbz k (q : ℤ))
      (qterm_support_finite ρ htr (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N)).symm] at hQ
  -- merge the `p`-families and the `q`-families back into `G`
  have hsplitP : (∑ᶠ p : ℕ, cbz k (p : ℤ) • gsum ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)))
      = (∑ᶠ p : ℕ, cbz k (p : ℤ) •
          ∑ᶠ i : ℕ, pterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i)
        + ∑ᶠ p : ℕ, cbz k (p : ℤ) •
            ∑ᶠ i : ℕ, qterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i := by
    rw [← finsum_add_distrib
      (opeSlot_support_finite W c b (fun p => cbz k (p : ℤ))
        (fun p => ∑ᶠ i : ℕ, pterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i)
        (fun p h => finsum_eq_zero_of_forall_eq_zero fun i => by rw [h, pterm_zero_right]))
      (opeSlot_support_finite W c b (fun p => cbz k (p : ℤ))
        (fun p => ∑ᶠ i : ℕ, qterm ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)) i)
        (fun p h => finsum_eq_zero_of_forall_eq_zero fun i => by rw [h, qterm_zero_right]))]
    exact finsum_congr fun p => by rw [gsum, smul_add]
  have hsplitQ : (∑ᶠ q : ℕ, cbz k (q : ℤ) • gsum ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N)
      = (∑ᶠ q : ℕ, cbz k (q : ℤ) •
          ∑ᶠ i : ℕ, pterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i)
        + ∑ᶠ q : ℕ, cbz k (q : ℤ) •
            ∑ᶠ i : ℕ, qterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i := by
    rw [← finsum_add_distrib
      (opeSlot_support_finite W c a (fun q => cbz k (q : ℤ))
        (fun q => ∑ᶠ i : ℕ, pterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i)
        (fun q h => finsum_eq_zero_of_forall_eq_zero fun i => by rw [h, pterm_zero_left]))
      (opeSlot_support_finite W c a (fun q => cbz k (q : ℤ))
        (fun q => ∑ᶠ i : ℕ, qterm ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N i)
        (fun q h => finsum_eq_zero_of_forall_eq_zero fun i => by rw [h, qterm_zero_left]))]
    exact finsum_congr fun q => by rw [gsum, smul_add]
  rw [gsum, gsum, hP, hQ, hsplitP, hsplitQ, map_add]
  abel

/-! ### The `𝒱`-level cancellation -/

/-- **The triangle reindex** `t = q + r`.  A doubly indexed family supported on the triangle
`j ≤ t` is reindexed by the injection `(q,r) ↦ (q+r, q)` whose range is exactly that triangle. -/
theorem finsum_triangle_reindex {N : Type*} [AddCommMonoid N] (A B : ℕ → ℕ → N)
    (hA : (Function.support fun z : ℕ × ℕ => A z.1 z.2).Finite)
    (hvan : ∀ t j : ℕ, t < j → A t j = 0) (hre : ∀ q r : ℕ, A (q + r) q = B q r) :
    (∑ᶠ t : ℕ, ∑ᶠ j : ℕ, A t j) = ∑ᶠ q : ℕ, ∑ᶠ r : ℕ, B q r := by
  classical
  have hinj : Function.Injective (fun z : ℕ × ℕ => (z.1 + z.2, z.1)) := by
    rintro ⟨q, r⟩ ⟨q', r'⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 (by omega)
  have hAB : ∀ z : ℕ × ℕ, A (z.1 + z.2) z.1 = B z.1 z.2 := fun z => hre z.1 z.2
  have hB : (Function.support fun z : ℕ × ℕ => B z.1 z.2).Finite := by
    have hpre : (Function.support fun z : ℕ × ℕ => B z.1 z.2)
        = (fun z : ℕ × ℕ => (z.1 + z.2, z.1)) ⁻¹'
            (Function.support fun w : ℕ × ℕ => A w.1 w.2) := by
      ext z
      simp only [Set.mem_preimage, Function.mem_support, hAB z]
    rw [hpre]
    exact hA.preimage hinj.injOn
  have hsupp : (Function.support fun w : ℕ × ℕ => A w.1 w.2)
      ⊆ Set.range (fun z : ℕ × ℕ => (z.1 + z.2, z.1)) := by
    rintro ⟨t, j⟩ hz
    rw [Function.mem_support] at hz
    have hjt : j ≤ t := by
      by_contra h
      exact hz (hvan t j (by omega))
    exact ⟨(j, t - j), Prod.ext (by simp; omega) rfl⟩
  calc (∑ᶠ t : ℕ, ∑ᶠ j : ℕ, A t j)
      = ∑ᶠ w : ℕ × ℕ, A w.1 w.2 := (finsum_curry _ hA).symm
    _ = ∑ᶠ w ∈ (Set.univ : Set (ℕ × ℕ)), A w.1 w.2 := (finsum_mem_univ _).symm
    _ = ∑ᶠ w ∈ Set.range (fun z : ℕ × ℕ => (z.1 + z.2, z.1)), A w.1 w.2 :=
        finsum_mem_inter_support_eq (fun w : ℕ × ℕ => A w.1 w.2) Set.univ
          (Set.range fun z : ℕ × ℕ => (z.1 + z.2, z.1)) (by
            rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp])
    _ = ∑ᶠ z : ℕ × ℕ, A (z.1 + z.2) z.1 := finsum_mem_range hinj
    _ = ∑ᶠ z : ℕ × ℕ, B z.1 z.2 := finsum_congr hAB
    _ = ∑ᶠ q : ℕ, ∑ᶠ r : ℕ, B q r := finsum_curry _ hB


/-- The `𝒱`-slot evaluation `v ↦ v₍ₘ₎x` as a `ℂ`-linear map, so that mode actions can be pushed
through `finsum`s in the `𝒱` argument. -/
noncomputable def actVecLM (ρ : VHatRep W M) (m : ℤ) (x : M) : 𝒱 →ₗ[ℂ] M where
  toFun v := ρ.actMode v m x
  map_add' u v := by rw [actMode_add_left]; rfl
  map_smul' r v := by rw [actMode_smul_left]; rfl

@[simp] theorem actVecLM_apply (ρ : VHatRep W M) (m : ℤ) (x : M) (v : 𝒱) :
    actVecLM ρ m x v = ρ.actMode v m x := rfl

/-- **The `𝒱`-level cancellation.**  The commutator `[c₍ₜ₎, a₍₋₁₎]` inside `𝒱`, summed against
`C(k,t)`, is exactly the pair of correction families produced by `gsum_actMode_shift` after the
`a`-slot shift law has been applied.  The combinatorial content is the subset-of-subset identity
`C(k,t)·C(t,q) = C(k,q)·C(k−q,t−q)` together with the reindexing `t = q + r`. -/
theorem vlevel_cancel (ρ : VHatRep W M) (a b c : 𝒱) (x : M) (k N : ℤ) :
    (∑ᶠ t : ℕ, cbz k (t : ℤ) • ρ.actMode (W.smul c (t : ℤ) (W.smul a (-1) b))
        (k + N - (t : ℤ)) x)
      = (∑ᶠ p : ℕ, cbz k (p : ℤ) • ρ.actMode (W.smul a (-1) (W.smul c (p : ℤ) b))
          (k + N - (p : ℤ)) x)
        + ∑ᶠ q : ℕ, cbz k (q : ℤ) • ∑ᶠ r : ℕ, cbz (k - (q : ℤ)) (r : ℤ) •
            ρ.actMode (W.smul (W.smul c (q : ℤ) a) ((r : ℤ) - 1) b)
              (N + k - (q : ℤ) - (r : ℤ)) x := by
  classical
  obtain ⟨Nca, hNca⟩ := W.smul_eventually_zero c a
  -- (1) the `𝒱`-commutator, evaluated at the mode `k + N − t`
  have hcomm : ∀ t : ℕ, cbz k (t : ℤ) • ρ.actMode (W.smul c (t : ℤ) (W.smul a (-1) b))
      (k + N - (t : ℤ)) x
      = cbz k (t : ℤ) • ρ.actMode (W.smul a (-1) (W.smul c (t : ℤ) b)) (k + N - (t : ℤ)) x
        + ∑ᶠ j : ℕ, (cbz k (t : ℤ) * cbz (t : ℤ) (j : ℤ)) •
            ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - (j : ℤ) - 1) b)
              (k + N - (t : ℤ)) x := by
    intro t
    have hfinZ : (Function.support fun j : ℤ =>
        cbz (t : ℤ) j • W.smul (W.smul c j a) ((t : ℤ) + (-1) - j) b).Finite := by
      refine Set.Finite.subset (Set.finite_Ico (0 : ℤ) Nca) fun j hj => ?_
      rw [Function.mem_support] at hj
      rw [Set.mem_Ico]
      refine ⟨?_, ?_⟩
      · by_contra h
        exact hj (by rw [cbz_apply_neg (t : ℤ) (by omega), zero_smul])
      · by_contra h
        exact hj (by rw [hNca j (by omega), PreVertexAlgebra.smul_zero_left, smul_zero])
    have h := mode_commutator_vec W c a b (t : ℤ) (-1)
    have h2 : ρ.actMode (W.smul c (t : ℤ) (W.smul a (-1) b)) (k + N - (t : ℤ)) x
        = ρ.actMode (W.smul a (-1) (W.smul c (t : ℤ) b)) (k + N - (t : ℤ)) x
          + ∑ᶠ j : ℕ, cbz (t : ℤ) (j : ℤ) •
              ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - (j : ℤ) - 1) b)
                (k + N - (t : ℤ)) x := by
      have hlin := congrArg (actVecLM ρ (k + N - (t : ℤ)) x) h
      rw [map_sub, map_finsum _ hfinZ] at hlin
      have hZN : (∑ᶠ j : ℤ, (actVecLM ρ (k + N - (t : ℤ)) x)
            (cbz (t : ℤ) j • W.smul (W.smul c j a) ((t : ℤ) + (-1) - j) b))
          = ∑ᶠ j : ℕ, cbz (t : ℤ) (j : ℤ) •
              ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - (j : ℤ) - 1) b)
                (k + N - (t : ℤ)) x := by
        rw [finsumZ_eq_finsumN _ Nca.toNat
          (fun j hj => by rw [map_smul, cbz_apply_neg (t : ℤ) hj, zero_smul])
          (fun j hj => by
            rw [map_smul, hNca j (by omega), PreVertexAlgebra.smul_zero_left, actVecLM_apply,
              actMode_zero_left, LinearMap.zero_apply, smul_zero])]
        refine finsum_congr fun j => ?_
        rw [map_smul, actVecLM_apply,
          show (t : ℤ) + (-1) - (j : ℤ) = (t : ℤ) - (j : ℤ) - 1 from by ring]
      rw [hZN] at hlin
      simp only [actVecLM_apply] at hlin
      rw [← hlin]
      abel
    have hfinN : (Function.support fun j : ℕ => cbz (t : ℤ) (j : ℤ) •
        ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - (j : ℤ) - 1) b)
          (k + N - (t : ℤ)) x).Finite := by
      refine Set.Finite.subset (Set.finite_Iio Nca.toNat) fun j hj => ?_
      rw [Function.mem_support] at hj
      rw [Set.mem_Iio]
      by_contra h
      exact hj (by
        rw [hNca (j : ℤ) (by omega), PreVertexAlgebra.smul_zero_left, actMode_zero_left,
          LinearMap.zero_apply, smul_zero])
    rw [h2, smul_add]
    congr 1
    rw [smul_finsum' (cbz k (t : ℤ)) hfinN]
    exact finsum_congr fun j => by rw [smul_smul]
  -- (2) the two families of the triangle reindex
  have hA : (Function.support fun z : ℕ × ℕ =>
      (cbz k (z.1 : ℤ) * cbz (z.1 : ℤ) (z.2 : ℤ)) •
        ρ.actMode (W.smul (W.smul c (z.2 : ℤ) a) ((z.1 : ℤ) - (z.2 : ℤ) - 1) b)
          (k + N - (z.1 : ℤ)) x).Finite := by
    refine support_pair_finite Nca.toNat
      (fun t j => (cbz k (t : ℤ) * cbz (t : ℤ) (j : ℤ)) •
        ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - (j : ℤ) - 1) b) (k + N - (t : ℤ)) x)
      (fun t j hj => ?_) (fun j => ?_)
    · dsimp only
      rw [hNca (j : ℤ) (by omega), PreVertexAlgebra.smul_zero_left, actMode_zero_left,
        LinearMap.zero_apply, smul_zero]
    · obtain ⟨Kj, hKj⟩ := W.smul_eventually_zero (W.smul c (j : ℤ) a) b
      refine Set.Finite.subset (Set.finite_Iio (Kj + (j : ℤ) + 1).toNat) fun t ht => ?_
      rw [Function.mem_support] at ht
      rw [Set.mem_Iio]
      by_contra h
      exact ht (by
        dsimp only
        rw [hKj ((t : ℤ) - (j : ℤ) - 1) (by omega), actMode_zero_left, LinearMap.zero_apply,
          smul_zero])
  have hvan : ∀ t j : ℕ, t < j → (cbz k (t : ℤ) * cbz (t : ℤ) (j : ℤ)) •
      ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - (j : ℤ) - 1) b)
        (k + N - (t : ℤ)) x = 0 := by
    intro t j htj
    rw [cbz_apply_nonneg (t : ℤ) (by exact_mod_cast Nat.zero_le j), Int.toNat_natCast,
      gBinom_natCast_eq_zero htj, mul_zero, zero_smul]
  have hre : ∀ q r : ℕ, (cbz k ((q + r : ℕ) : ℤ) * cbz ((q + r : ℕ) : ℤ) ((q : ℕ) : ℤ)) •
      ρ.actMode (W.smul (W.smul c ((q : ℕ) : ℤ) a) (((q + r : ℕ) : ℤ) - ((q : ℕ) : ℤ) - 1) b)
        (k + N - ((q + r : ℕ) : ℤ)) x
      = (cbz k (q : ℤ) * cbz (k - (q : ℤ)) (r : ℤ)) •
          ρ.actMode (W.smul (W.smul c (q : ℤ) a) ((r : ℤ) - 1) b)
            (N + k - (q : ℤ) - (r : ℤ)) x := by
    intro q r
    have hcoef : cbz k ((q + r : ℕ) : ℤ) * cbz ((q + r : ℕ) : ℤ) ((q : ℕ) : ℤ)
        = cbz k (q : ℤ) * cbz (k - (q : ℤ)) (r : ℤ) := by
      rw [cbz_apply_nonneg k (by exact_mod_cast Nat.zero_le (q + r)), Int.toNat_natCast,
        cbz_apply_nonneg (((q + r : ℕ)) : ℤ) (by exact_mod_cast Nat.zero_le q), Int.toNat_natCast,
        cbz_apply_nonneg k (by exact_mod_cast Nat.zero_le q), Int.toNat_natCast,
        cbz_apply_nonneg (k - (q : ℤ)) (by exact_mod_cast Nat.zero_le r), Int.toNat_natCast,
        cbz_subsetOfSubset k (Nat.le_add_right q r), Nat.add_sub_cancel_left]
    rw [hcoef, show (((q + r : ℕ)) : ℤ) - ((q : ℕ) : ℤ) - 1 = (r : ℤ) - 1 from by push_cast; ring,
      show k + N - (((q + r : ℕ)) : ℤ) = N + k - (q : ℤ) - (r : ℤ) from by push_cast; ring]
  -- (3) split the `t`-sum and reindex
  have hfin1 : (Function.support fun t : ℕ =>
      cbz k (t : ℤ) • ρ.actMode (W.smul a (-1) (W.smul c (t : ℤ) b))
        (k + N - (t : ℤ)) x).Finite := by
    obtain ⟨Ncb, hNcb⟩ := W.smul_eventually_zero c b
    refine Set.Finite.subset (Set.finite_Iio Ncb.toNat) fun t ht => ?_
    rw [Function.mem_support] at ht
    rw [Set.mem_Iio]
    by_contra h
    exact ht (by
      rw [hNcb (t : ℤ) (by omega), PreVertexAlgebra.smul_zero_right, actMode_zero_left,
        LinearMap.zero_apply, smul_zero])
  have hfin2 : (Function.support fun t : ℕ => ∑ᶠ j : ℕ,
      (cbz k (t : ℤ) * cbz (t : ℤ) (j : ℤ)) •
        ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - (j : ℤ) - 1) b)
          (k + N - (t : ℤ)) x).Finite :=
    support_marginal_finite _ hA
  rw [finsum_congr hcomm, finsum_add_distrib hfin1 hfin2]
  congr 1
  rw [finsum_triangle_reindex _ _ hA hvan hre]
  refine finsum_congr fun q => ?_
  have hfinr : (Function.support fun r : ℕ => cbz (k - (q : ℤ)) (r : ℤ) •
      ρ.actMode (W.smul (W.smul c (q : ℤ) a) ((r : ℤ) - 1) b)
        (N + k - (q : ℤ) - (r : ℤ)) x).Finite := by
    obtain ⟨Kq, hKq⟩ := W.smul_eventually_zero (W.smul c (q : ℤ) a) b
    refine Set.Finite.subset (Set.finite_Iio (Kq + 1).toNat) fun r hr => ?_
    rw [Function.mem_support] at hr
    rw [Set.mem_Iio]
    by_contra h
    exact hr (by
      rw [hKq ((r : ℤ) - 1) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero])
  rw [smul_finsum' (cbz k (q : ℤ)) hfinr]
  exact finsum_congr fun r => by rw [smul_smul]

/-! ### `DefectModeShift` is a theorem -/

/-- **DLM2 Proposition 6.1 at the canonical pole `ℓ = −1`.**

    δ(a, b, c₍ₖ₎x, −1, N)
      = c₍ₖ₎·δ(a, b, x, −1, N)
        − Σ_p C(k,p)·δ(a, c₍ₚ₎b, x, −1, k+N−p)
        − Σ_q C(k,q)·δ(c₍q₎a, b, x, −1, N+k−q)

for **every** `V̂`-representation with truncated modes.  The three ingredients are

* `gsum_actMode_shift` — pushing `c₍ₖ₎` leftwards through the normal-ordered sum, which produces
  the `a`-slot family at the **shifted** left index `k − q`;
* `sumR_sub_gsum_shift` (proved) — the `a`-slot shift law that turns that shifted sum back into a
  canonical defect plus a `𝒱`-level tail;
* `vlevel_cancel` — the `𝒱`-level commutator `[c₍ₜ₎, a₍₋₁₎]` cancelling the two tails, whose
  combinatorial content is `C(k,t)·C(t,q) = C(k,q)·C(k−q,t−q)` and the reindex `t = q + r`.

This **discharges** the hypothesis `DefectModeShift` carried by `ZhuVermaAnArchDLM3Propagate`. -/
theorem defectModeShift_of_truncated (ρ : VHatRep W M) (htr : ActModeTruncated ρ) :
    DefectModeShift ρ := by
  intro a b c x k N
  -- the leading `(a₍₋₁₎b)₍N₎` term commutes past `c₍ₖ₎` up to one singular-OPE family
  have hlead : ρ.actMode (W.smul a (-1) b) N (ρ.actMode c k x)
      = ρ.actMode c k (ρ.actMode (W.smul a (-1) b) N x)
        - ∑ᶠ t : ℕ, cbz k (t : ℤ) • ρ.actMode (W.smul c (t : ℤ) (W.smul a (-1) b))
            (k + N - (t : ℤ)) x := by
    rw [← actMode_comm_vec ρ c (W.smul a (-1) b) x k N]
    abel
  -- each `G`-correction is a canonical defect plus a `𝒱`-level term
  have hP : ∀ p : ℕ, gsum ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ))
      = ρ.actMode (W.smul a (-1) (W.smul c (p : ℤ) b)) (k + N - (p : ℤ)) x
        - defectVec ρ a (W.smul c (p : ℤ) b) x (-1) (k + N - (p : ℤ)) := by
    intro p
    rw [defectVec_neg_one_eq ρ htr a (W.smul c (p : ℤ) b) x (k + N - (p : ℤ))]
    abel
  have hQ : ∀ q : ℕ, gsum ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N
      = (∑ᶠ r : ℕ, cbz (k - (q : ℤ)) (r : ℤ) •
          ρ.actMode (W.smul (W.smul c (q : ℤ) a) ((r : ℤ) - 1) b)
            (N + k - (q : ℤ) - (r : ℤ)) x)
        - defectVec ρ (W.smul c (q : ℤ) a) b x (-1) (N + k - (q : ℤ)) := by
    intro q
    have h := sumR_sub_gsum_shift ρ htr (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) (N + k - (q : ℤ))
    rw [show N + k - (q : ℤ) - (k - (q : ℤ)) = N from by ring] at h
    rw [← h]
    abel
  -- finiteness of the four outer families
  have hfP1 : (Function.support fun p : ℕ => cbz k (p : ℤ) •
      ρ.actMode (W.smul a (-1) (W.smul c (p : ℤ) b)) (k + N - (p : ℤ)) x).Finite :=
    opeSlot_support_finite W c b (fun p => cbz k (p : ℤ))
      (fun p => ρ.actMode (W.smul a (-1) (W.smul c (p : ℤ) b)) (k + N - (p : ℤ)) x)
      (fun p h => by
        dsimp only
        rw [h, PreVertexAlgebra.smul_zero_right, actMode_zero_left, LinearMap.zero_apply])
  have hfPd : (Function.support fun p : ℕ => cbz k (p : ℤ) •
      defectVec ρ a (W.smul c (p : ℤ) b) x (-1) (k + N - (p : ℤ))).Finite :=
    opeSlot_support_finite W c b (fun p => cbz k (p : ℤ))
      (fun p => defectVec ρ a (W.smul c (p : ℤ) b) x (-1) (k + N - (p : ℤ)))
      (fun p h => by
        dsimp only
        rw [h, defectVec_zero_left₂ ρ htr a x (-1) (k + N - (p : ℤ))])
  have hfQ1 : (Function.support fun q : ℕ => cbz k (q : ℤ) • ∑ᶠ r : ℕ, cbz (k - (q : ℤ)) (r : ℤ) •
      ρ.actMode (W.smul (W.smul c (q : ℤ) a) ((r : ℤ) - 1) b)
        (N + k - (q : ℤ) - (r : ℤ)) x).Finite :=
    opeSlot_support_finite W c a (fun q => cbz k (q : ℤ))
      (fun q => ∑ᶠ r : ℕ, cbz (k - (q : ℤ)) (r : ℤ) •
        ρ.actMode (W.smul (W.smul c (q : ℤ) a) ((r : ℤ) - 1) b) (N + k - (q : ℤ) - (r : ℤ)) x)
      (fun q h => by
        dsimp only
        exact finsum_eq_zero_of_forall_eq_zero fun r => by
          rw [h, PreVertexAlgebra.smul_zero_left, actMode_zero_left, LinearMap.zero_apply,
            smul_zero])
  have hfQd : (Function.support fun q : ℕ => cbz k (q : ℤ) •
      defectVec ρ (W.smul c (q : ℤ) a) b x (-1) (N + k - (q : ℤ))).Finite :=
    opeSlot_support_finite W c a (fun q => cbz k (q : ℤ))
      (fun q => defectVec ρ (W.smul c (q : ℤ) a) b x (-1) (N + k - (q : ℤ)))
      (fun q h => by
        dsimp only
        rw [h, defectVec_zero_left₁ ρ htr b x (-1) (N + k - (q : ℤ))])
  -- the two outer corrections, split
  have hPsum : (∑ᶠ p : ℕ, cbz k (p : ℤ) • gsum ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)))
      = (∑ᶠ p : ℕ, cbz k (p : ℤ) •
          ρ.actMode (W.smul a (-1) (W.smul c (p : ℤ) b)) (k + N - (p : ℤ)) x)
        - ∑ᶠ p : ℕ, cbz k (p : ℤ) •
            defectVec ρ a (W.smul c (p : ℤ) b) x (-1) (k + N - (p : ℤ)) := by
    rw [← finsum_sub_distrib hfP1 hfPd]
    exact finsum_congr fun p => by rw [hP p, smul_sub]
  have hQsum : (∑ᶠ q : ℕ, cbz k (q : ℤ) • gsum ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) N)
      = (∑ᶠ q : ℕ, cbz k (q : ℤ) • ∑ᶠ r : ℕ, cbz (k - (q : ℤ)) (r : ℤ) •
          ρ.actMode (W.smul (W.smul c (q : ℤ) a) ((r : ℤ) - 1) b)
            (N + k - (q : ℤ) - (r : ℤ)) x)
        - ∑ᶠ q : ℕ, cbz k (q : ℤ) •
            defectVec ρ (W.smul c (q : ℤ) a) b x (-1) (N + k - (q : ℤ)) := by
    rw [← finsum_sub_distrib hfQ1 hfQd]
    exact finsum_congr fun q => by rw [hQ q, smul_sub]
  rw [defectVec_neg_one_eq ρ htr a b (ρ.actMode c k x) N, defectVec_neg_one_eq ρ htr a b x N,
    map_sub, hlead, gsum_actMode_shift ρ htr a b c x k N, hPsum, hQsum,
    vlevel_cancel ρ a b c x k N]
  abel

end VHatRep

/-! ## (5) The gate conditional on the independent `BottomProjection` assumption -/

namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱} {n : ℕ} {U : Type u} [AddCommGroup U] [Module ℂ U]

/-- The induced module's representation satisfies the mode-shift law: it is
`ActModeTruncated` (`ind_actModeTruncated`), and that is all `defectModeShift_of_truncated`
needs. -/
theorem indRho_defectModeShift (P : ParabolicRep W n U) :
    VHatRep.DefectModeShift (indRho P) :=
  VHatRep.defectModeShift_of_truncated (indRho P) (ind_actModeTruncated P)

/-- **`DefectPairsToZero Pr`, conditional on `Pr` alone** — DLM3's `U(V̂)W ⊆ J` at `n = 0`,
for a general `U : AMod W`, with no further hypothesis beyond the independent projection
assumption `Pr` itself. -/
theorem defectPairsToZero_of_bottomProjection (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) : DefectPairsToZero Pr :=
  defectPairsToZero_of_modeShift_aMod W U Pr (indRho_defectModeShift (parabolicRepOfAMod W U))

/-- DLM3 Proposition 4.6 (`BottomPropagates`), conditional on `Pr` alone. -/
theorem bottomPropagates_of_bottomProjection (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) : BottomPropagates Pr :=
  bottomPropagates_of_modeShift W U Pr (indRho_defectModeShift (parabolicRepOfAMod W U))

/-- DLM3 Proposition 4.7 (`OrbitPropagates`), conditional on `Pr` alone. -/
theorem orbitPropagates_of_bottomProjection (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) : OrbitPropagates Pr :=
  orbitPropagates_of_modeShift W U Pr (indRho_defectModeShift (parabolicRepOfAMod W U))

/-- **`U` survives**, conditional on `Pr` alone — DLM3 Theorem 4.1 at `n = 0`. -/
theorem indBarBottom_injective_of_bottomProjection (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) :
    Function.Injective (indBarBottom (parabolicRepOfAMod W U)) :=
  indBarBottom_injective_of_defectPairsToZero Pr (defectPairsToZero_of_bottomProjection W U Pr)

/-- The separating realization of `U`, conditional on `Pr` alone. -/
theorem exists_separating_realization_of_bottomProjection (W : VertexOperatorAlgebra 𝒱)
    (U : AMod W) (Pr : BottomProjection (parabolicRepOfAMod W U)) :
    ∃ R : Realization W 0 U.carrier (parabolicRepOfAMod W U), R.Separates :=
  (indBarBottom_injective_iff (parabolicRepOfAMod W U)).mp
    (indBarBottom_injective_of_bottomProjection W U Pr)

end DLM3
end VHat

section GateOfPBW

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- **THE `(0,0)` GATE, CONDITIONAL ON THE INDEPENDENT `Pr` ASSUMPTION.**

    (GATE)   OnmFull W 0 0 = O W

The **only** hypothesis is `Pr`, an explicit bottom-injectivity assumption
(`PHASE4_PLAN` C-6, C-11 — input (i) of `gate_of_dlm3`). The project-level witness
`voaPBWBottomProjection` is supplied from the generic relative-induction field of the
theorem `VOA.pbw : PBWPrinciple`.
DLM3's second input `DefectPairsToZero` is a **theorem**
(`defectPairsToZero_of_bottomProjection`), so the gate rests on exactly one named hypothesis.

No `sorry`, no `axiom`. -/
theorem gate_of_pbwDatum (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    OnmFull W 0 0 = O W :=
  gate_of_dlm3 Pr (defectPairsToZero_of_bottomProjection W (regularAMod W) Pr)

/-- The gate as an inclusion. -/
theorem gate_le_of_pbwDatum (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    OnmFull W 0 0 ≤ O W :=
  le_of_eq (gate_of_pbwDatum Pr)

/-- The gate off the `PBWFreeness` phrasing of the datum. -/
theorem gate_of_pbwFreeness (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W))) :
    OnmFull W 0 0 = O W :=
  gate_of_pbwDatum hP.bottomProjection

/-! ### The downstream package, conditional on `Pr` alone -/

/-- The whole `Prop`-valued downstream package, conditional on `Pr` alone. -/
theorem downstream_of_pbwDatum (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    OnmFull W 0 0 = O W ∧ DJAnnEqAn W 0 ∧ OnmFull W 0 0 = OnFull W 0 ∧ OnmCollapses W 0 :=
  ⟨gate_of_pbwDatum Pr, djAnnEqAn_zero_of_gate (gate_le_of_pbwDatum Pr),
    onmFull_diag_zero_eq_of_gate (gate_le_of_pbwDatum Pr),
    onmCollapses_zero_of_gate (gate_le_of_pbwDatum Pr)⟩

/-- `DJAnnEqAn W 0` — the single diagonal-collapse instance the chain consumes. -/
theorem djAnnEqAn_zero_of_pbwDatum
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) : DJAnnEqAn W 0 :=
  djAnnEqAn_zero_of_gate (gate_le_of_pbwDatum Pr)

/-- **`A_{0,0}(𝒱) ≃ A_0(𝒱)`**, conditional on `Pr` alone. -/
noncomputable def anmFullDiagEquivOfPbwDatum
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    AnmFull W 0 0 ≃ₗ[ℂ] AnFull W 0 :=
  anmFullDiagEquivZero (gate_le_of_pbwDatum Pr)

/-- **`M(U)(0) ≅ U`** on the `DJPiece` carrier, conditional on `Pr` alone. -/
noncomputable def djPieceMEquivOfPbwDatum
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (V : AmMod W 0) :
    DJPiece W V 0 ≃ₗ[ℂ] V.carrier :=
  djPieceMEquivZero (gate_le_of_pbwDatum Pr) V

/-- **The bottom of `M(U)` is `U`** on the graded carrier, conditional on `Pr` alone. -/
noncomputable def djCarrierDegZeroEquivOfPbwDatum
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) (V : AmMod W 0) :
    DJCarrier.deg W V 0 ≃ₗ[ℂ] V.carrier :=
  djCarrierDegZeroEquiv (gate_le_of_pbwDatum Pr) V

/-- **DJ Theorem 4.10's generation sentence** — "`M(U)` is generated by `U`" — conditional on
`Pr` alone. -/
theorem djCarrier_generated_by_U_of_pbwDatum
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (U : AmMod W 0) (hD : DJActionDescent W 0) (S : Submodule ℂ (DJCarrier W U))
    (hS : DJModeStable W U hD S)
    (hU : ∀ w : U.carrier,
      (((DJCarrier.degMEquiv W 0 (djAnnEqAn_zero_of_pbwDatum Pr) U).symm w :
          DJCarrier.deg W U 0) : DJCarrier W U) ∈ S) :
    S = ⊤ :=
  djCarrier_generated_by_U (djAnnEqAn_zero_of_pbwDatum Pr) U hD S hS hU

end GateOfPBW

end VOA

-- Axiom check. Explicit `BottomProjection`/`PBWFreeness` parameters are not printed.
