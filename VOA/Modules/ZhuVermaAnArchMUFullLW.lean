/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUFullRho
import VOA.Modules.ZhuVermaAnArchMUModuleDataBuild
import VOA.Modules.ZhuVermaAnArchMULW

/-!
# `M(U)` on DJ's genuine ideal as a `WeakModule`, `OrdVModule` and `LWModule`

This file completes the Dong–Jiang Theorem 4.10 pipeline on the full-ideal carrier
`MUFull W U = ⊕ₙ A_{n,0}(𝒱) ⊗ U`, mirroring `ZhuVermaAnArchMULW` (which does the same for the prime
carrier `MU W U`).  Everything below the module Jacobi is **unconditional**:

* `muFullRho_actMode` — the bridge `(muFullRho …).actMode a m = muFullMode W U m a`;
* `muFullActModeTruncated` — DJ Lemma 4.6(1) in `ActModeTruncated` form (proved);
* `muFullVacuumCreation` — DJ Lemma 4.6(2) in `VacuumCreation` form (proved);
* `muFullWeak` — `WeakModule W (MUFull W U)`, modulo exactly the two named DJ leaves
  `MUFullBracket` (Lemma 4.7, the commutator formula) and `ModuleIterate` (the Cor. after
  Lemma 4.9, weak associativity);
* `MUFullModuleData` / `toOrdVModule` / `toLWModule` — the graded packaging, with the same four fields
  as `MUModuleData` (`weak`, `L0_on_deg`, `finrank_deg`, `bottom_ne_bot`);
* `buildMUFullModuleData` — the central builder.

So `U ↦ M(U)` as an `LWModule W` is a term as soon as the two DJ leaves plus the three standard
graded-packaging fields are supplied.  **Nothing is claimed beyond this** — `MUFullBracket` and
`ModuleIterate` are genuine open leaves (DJ prove both, but DJ Lemma 2.3, on which the commutator
rests, is not yet formalized in the repo).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (Lemmas 4.6–4.9, Thm 4.10); Gannon Def. 5.3.1a–c, Thm 5.3.4;
`ZhuVermaAnArchMULW` (the prime-carrier template `MUModuleData`/`toOrdVModule`/`toLWModule`),
`ZhuVermaAnArchMUModuleDataBuild` (`weakModuleOfRep`, `VacuumCreation`),
`ZhuVermaAnArchMUjacobi` (`ActModeTruncated`, `ModuleIterate`, `isModuleJacobi_of_iterate`).
-/

namespace VOA

open VertexOperatorAlgebra
open VHat VHat.VHatRep
open Finsupp
open Module (End)
open scoped TensorProduct DirectSum BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The bridge: the `V̂`-representation's modes are the DJ modes. -/

@[simp] theorem muFullRho_actMode (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hbr : MUFullBracket W U) (a : 𝒱) (m : ℤ) :
    (muFullRho W U hbr).actMode a m = muFullMode W U m a := by
  rw [muFullRho, VHatModeData.toRep_actMode]
  show assembleAct (muFullActGen W U) (single m a) = _
  rw [assembleAct_single]
  rfl

/-- **DJ Lemma 4.6(1)** in the `ActModeTruncated` interface — unconditional. -/
theorem muFullActModeTruncated (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hbr : MUFullBracket W U) : ActModeTruncated (muFullRho W U hbr) := by
  intro a x
  obtain ⟨N, hN⟩ := muFullMode_truncation W U a x
  exact ⟨N, fun m hm => by rw [muFullRho_actMode]; exact hN m hm⟩

/-- **DJ Lemma 4.6(2)** in the `VacuumCreation` interface — unconditional. -/
theorem muFullVacuumCreation (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hbr : MUFullBracket W U) : VacuumCreation (muFullRho W U hbr) := by
  intro m
  rw [muFullRho_actMode]
  exact muFullMode_vacuum W U m

/-! ## `M(U)` as a `WeakModule`, modulo the two DJ leaves. -/

/-- **`M(U)` is a weak `𝒱`-module** (DJ Thm 4.10), modulo the two named Dong–Jiang leaves: the
commutator formula `MUFullBracket` (Lemma 4.7) and weak associativity `ModuleIterate` (the
Corollary after Lemma 4.9).  Truncation and the vacuum normalization are discharged here. -/
noncomputable def muFullWeak (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hbr : MUFullBracket W U) (hit : ModuleIterate (muFullRho W U hbr)) :
    WeakModule W (MUFull W U) :=
  weakModuleOfRep (muFullRho W U hbr) (muFullActModeTruncated W U hbr)
    (muFullVacuumCreation W U hbr)
    (isModuleJacobi_of_iterate (muFullRho W U hbr) (muFullActModeTruncated W U hbr) hit)

@[simp] theorem muFullWeak_act (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hbr : MUFullBracket W U) (hit : ModuleIterate (muFullRho W U hbr))
    (a : 𝒱) (m : ℤ) (x : MUFull W U) :
    (muFullWeak W U hbr hit).act a m x = muFullMode W U m a x := by
  rw [muFullWeak, weakModuleOfRep_act, muFullRho_actMode]

/-! ## The graded packaging: `MUFullModuleData` → `OrdVModule` → `LWModule`. -/

/-- **The genuine module data for DJ's induced module `M(U)` on the full ideal**, at lowest weight
`h`.  The full-ideal mirror of `MUModuleData`: a hypothesis structure bundling exactly what the
`OrdVModule`/`LWModule` interface consumes.  Never an axiom, no `sorry`. -/
structure MUFullModuleData (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (h : ℂ) where
  /-- The `WeakModule` structure on `MUFull W U` (`muFullWeak`, modulo the two DJ leaves). -/
  weak : WeakModule W (MUFull W U)
  /-- **Grading compatibility (5.3.1c):** `L₀ = ω₍₁₎` acts as `h + n` on the level-`n` piece. -/
  L0_on_deg : ∀ (n : ℕ) (x : MUFull W U), x ∈ MUFull.deg W U n →
    mode (weak.YM W.conformalVector) 1 x = ((h : ℂ) + n) • x
  /-- Each level-`n` piece is finite-dimensional (DJ Thm 4.10). -/
  finrank_deg : ∀ n : ℕ, FiniteDimensional ℂ (MUFull.deg W U n)
  /-- The bottom layer is nonzero (DJ: `M(U)(0) = A_{0,0}(𝒱) ⊗ U ≠ 0`). -/
  bottom_ne_bot : MUFull.deg W U 0 ≠ ⊥

namespace MUFullModuleData

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}

/-- **The ℂ-grading of `M(U)`**: the level-`n` piece placed at complex weight `h + n`. -/
noncomputable def cweight (D : MUFullModuleData W U h) (α : ℂ) : Submodule ℂ (MUFull W U) :=
  ⨆ (n : ℕ) (_ : (h : ℂ) + n = α), MUFull.deg W U n

theorem cweight_cast (D : MUFullModuleData W U h) (m : ℕ) :
    D.cweight ((h : ℂ) + m) = MUFull.deg W U m := by
  unfold cweight
  apply le_antisymm
  · refine iSup_le (fun n => iSup_le (fun hn => ?_))
    have : n = m := by
      have : (n : ℂ) = (m : ℂ) := by linear_combination hn
      exact_mod_cast this
    rw [this]
  · exact le_iSup_of_le m (le_iSup_of_le rfl le_rfl)

theorem cweight_eq_bot (D : MUFullModuleData W U h) {α : ℂ}
    (hne : ∀ n : ℕ, (h : ℂ) + n ≠ α) : D.cweight α = ⊥ :=
  iSup_eq_bot.mpr (fun n => iSup_eq_bot.mpr (fun hn => absurd hn (hne n)))

/-- **The ℂ-grading of `M(U)` is a genuine internal direct-sum decomposition.** -/
theorem cweight_isInternal (D : MUFullModuleData W U h) :
    DirectSum.IsInternal D.cweight := by
  have hN := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (MUFull.deg W U)).mp
    (MUFull.isInternal_deg W U)
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · refine iSupIndep_extend (MUFull.deg W U) D.cweight (fun n => (h : ℂ) + n) ?_ ?_ hN.1
    · intro α hα; exact D.cweight_eq_bot (fun n hn => hα n hn)
    · intro n; exact D.cweight_cast n
  · rw [← hN.2]
    apply le_antisymm
    · refine iSup_le (fun α => ?_)
      unfold cweight
      exact iSup_le (fun n => iSup_le (fun _ => le_iSup (MUFull.deg W U) n))
    · exact iSup_le (fun n => le_iSup_of_le ((h : ℂ) + n) (by rw [D.cweight_cast n]))

/-- **The `OrdVModule W (MUFull W U)` upgrade** — `M(U)` on DJ's genuine ideal is a ℂ-graded
`𝒱`-module. -/
noncomputable def toOrdVModule (D : MUFullModuleData W U h) : OrdVModule W (MUFull W U) where
  toWeakModule := D.weak
  weight := D.cweight
  isInternal := D.cweight_isInternal
  L0_weight := by
    intro α x hx
    by_cases hcase : ∃ m : ℕ, (h : ℂ) + m = α
    · obtain ⟨m, rfl⟩ := hcase
      rw [D.cweight_cast m] at hx
      exact D.L0_on_deg m x hx
    · rw [D.cweight_eq_bot (fun n hn => hcase ⟨n, hn⟩), Submodule.mem_bot] at hx
      rw [hx, map_zero, smul_zero]
  finrank := by
    intro α
    by_cases hcase : ∃ m : ℕ, (h : ℂ) + m = α
    · obtain ⟨m, rfl⟩ := hcase
      rw [D.cweight_cast m]; exact D.finrank_deg m
    · rw [D.cweight_eq_bot (fun n hn => hcase ⟨n, hn⟩)]; infer_instance
  boundedBelow := by
    refine ⟨h.re, fun α hα => ?_⟩
    by_cases hcase : ∃ m : ℕ, (h : ℂ) + m = α
    · obtain ⟨m, rfl⟩ := hcase
      simp only [Complex.add_re, Complex.natCast_re]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    · exact absurd (D.cweight_eq_bot (fun n hn => hcase ⟨n, hn⟩)) hα

@[simp] theorem toOrdVModule_weight (D : MUFullModuleData W U h) (α : ℂ) :
    D.toOrdVModule.weight α = D.cweight α := rfl

/-- **`h` is a lowest weight of `M(U)`.** -/
theorem isLowestWeight (D : MUFullModuleData W U h) : IsLowestWeight D.toOrdVModule h := by
  intro α hα
  by_cases hcase : ∃ m : ℕ, (h : ℂ) + m = α
  · obtain ⟨m, rfl⟩ := hcase
    exact ⟨m, by simp⟩
  · exact absurd (D.cweight_eq_bot (fun n hn => hcase ⟨n, hn⟩)) (by simpa using hα)

/-- **The bottom layer `M(U)_h` is nonzero (realized).** -/
theorem bottom_weight_ne_bot (D : MUFullModuleData W U h) : D.toOrdVModule.weight h ≠ ⊥ := by
  rw [toOrdVModule_weight]
  have : D.cweight h = MUFull.deg W U 0 := by
    have := D.cweight_cast 0
    simpa using this
  rw [this]
  exact D.bottom_ne_bot

/-- **`M(U)` as a bundled lowest-weight `𝒱`-module** — the hard-direction object of Zhu Thm 5.3.4,
on Dong–Jiang's genuine (full) ideal. -/
noncomputable def toLWModule (D : MUFullModuleData W U h) : LWModule W where
  carrier := MUFull W U
  isMod := D.toOrdVModule
  h := h
  isLow := D.isLowestWeight
  realized := D.bottom_weight_ne_bot

@[simp] theorem toLWModule_carrier (D : MUFullModuleData W U h) :
    (D.toLWModule).carrier = MUFull W U := rfl

@[simp] theorem toLWModule_h (D : MUFullModuleData W U h) : (D.toLWModule).h = h := rfl

@[simp] theorem toLWModule_isMod (D : MUFullModuleData W U h) :
    (D.toLWModule).isMod = D.toOrdVModule := rfl

end MUFullModuleData

/-! ## The central builder. -/

/-- **`buildMUFullModuleData` — `M(U)` on DJ's genuine ideal, packaged.**  Consumes the two named
Dong–Jiang leaves (`hbr`, `hit`) and the three standard graded-packaging fields (`hL0`, `hfin`,
`hbot`), and returns the headline term. -/
noncomputable def buildMUFullModuleData {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}
    (hbr : MUFullBracket W U) (hit : ModuleIterate (muFullRho W U hbr))
    (hL0 : ∀ (n : ℕ) (x : MUFull W U), x ∈ MUFull.deg W U n →
      muFullMode W U 1 W.conformalVector x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MUFull.deg W U n))
    (hbot : MUFull.deg W U 0 ≠ ⊥) :
    MUFullModuleData W U h where
  weak := muFullWeak W U hbr hit
  L0_on_deg := by
    intro n x hx
    have := hL0 n x hx
    rw [show mode ((muFullWeak W U hbr hit).YM W.conformalVector) 1 x
        = (muFullWeak W U hbr hit).act W.conformalVector 1 x from rfl,
      muFullWeak_act]
    exact this
  finrank_deg := hfin
  bottom_ne_bot := hbot

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.muFullActModeTruncated
  #print axioms VOA.muFullVacuumCreation
  #print axioms VOA.muFullWeak
  #print axioms VOA.MUFullModuleData.toLWModule
  #print axioms VOA.buildMUFullModuleData
-/
