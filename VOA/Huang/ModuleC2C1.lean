/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.ModuleC2Reduction
import VOA.Huang.HuangODEC1

/-!
# `C₁`- versus `C₂`-cofiniteness of irreducible modules of a `C₂`-cofinite VOA

For a lowest-weight module `P` (all weights in `h + ℕ`), Huang's graded `C₁`-cofiniteness
`C1Graded P.isMod P.h B` (above level `B`, every vector is a sum of `u₍₋₁₎w'` with `wt u ≥ 1`)
says exactly that `P` is spanned by negative-mode words on the finitely many levels `≤ B`:

* `exists_finite_lwGenerated_of_C1Graded` — `C1Graded ⟹ LWGenerated` by a finite set;

so, combined with `ModuleC2Reduction.moduleC2Cofinite_of_LWGenerated` and the library's
`HuangODEC1.c1Graded_of_moduleC2Cofinite`, over a `C₂`-cofinite `𝒱` the three properties
"`C₂`-cofinite", "graded `C₁`-cofinite" and "finitely lowest-weight generated" of a lowest-weight
module **coincide** (`lwModule_C2_iff_C1`).  Consequently the four named inputs

  `ModuleC2Input ⟺ ModuleC1Input ⟺ BuhlFiniteLWGenInput ⟺ BuhlBaseClosedInput`

are equivalent (`moduleC2Input_iff_moduleC1Input`, `moduleC2Input_iff_buhlFiniteLWGen`).
`ModuleC1Input` is Huang's own hypothesis ("all modules are `C₁`-cofinite", Huang, Commun.
Contemp. Math. 7 (2005), and Thm. 3.5 of Huang, Commun. Contemp. Math. 10 (2008)), which Huang
derives from `C₂` via Abe–Buhl–Dong / Buhl; the equivalence shows that no form of the input is
cheaper than another: the content is Buhl's spanning theorem.

## Status
No `sorry`, no new axioms, no `Pr`/`VOA.pbw`.
-/

namespace VOA.Huang.ModuleC2

open VOA VOA.Huang.FusionC2 VOA.Huang.LWBottomRecovery VOA.Huang.HuangODEC1
open VOA.Huang.HuangODEProduct
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Graded `C₁`-cofiniteness gives finite lowest-weight generation.**  If above level `B`
every vector of the lowest-weight module `P` is a sum of `u₍₋₁₎w'` (`wt u ≥ 1`), then `P` is
spanned by negative-mode words on a finite spanning set of the levels `≤ B`. -/
theorem exists_finite_lwGenerated_of_C1Graded (P : LWModule W) {B : ℕ}
    (hC1 : C1Graded P.isMod P.h B) :
    ∃ S : Set P.carrier, S.Finite ∧ LWGenerated P.isMod.toWeakModule S := by
  classical
  set A := P.isMod.toWeakModule
  -- a finite spanning set of each weight space
  have hfg : ∀ N : ℕ, ∃ t : Finset P.carrier,
      Submodule.span ℂ (t : Set P.carrier) = P.isMod.weight (P.h + (N : ℂ)) := by
    intro N
    haveI := P.isMod.finrank (P.h + (N : ℂ))
    exact (Submodule.fg_iff_finiteDimensional _).mpr inferInstance
  choose t ht using hfg
  set S : Set P.carrier := ⋃ N ∈ Finset.range (B + 1), (t N : Set P.carrier) with hS
  have hSfin : S.Finite :=
    Set.Finite.biUnion (Finset.range (B + 1)).finite_toSet (fun N _ => (t N).finite_toSet)
  refine ⟨S, hSfin, ?_⟩
  -- every level lies in `Gfil A S 0`
  have hlev : ∀ N : ℕ, ∀ w ∈ P.isMod.weight (P.h + (N : ℂ)), w ∈ Gfil A S 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
    intro w hw
    by_cases hN : N ≤ B
    · rw [← ht N] at hw
      refine (Submodule.span_le.mpr ?_) hw
      intro s hs
      refine mem_Gfil_of_mem_B A S ?_ le_rfl
      rw [hS]
      exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) hs
    · have hspan := hC1 N (by omega) w hw
      refine (Submodule.span_le.mpr ?_) hspan
      rintro _ ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      have hw'G : w' ∈ Gfil A S 0 := IH (N - d) (by omega) w' hw'
      have h := Gfil_prepend A S (c := u) (b := d) (n := 0) hu hw'G
      simpa using h
  rw [LWGenerated, eq_top_iff]
  intro x _
  refine induction_lev (lwAdmissible P) (motive := fun x => x ∈ Gfil A S 0) x
    (Submodule.zero_mem _) (fun _ _ hx hy => Submodule.add_mem _ hx hy) (fun k y hy => ?_)
  rw [lwAdmissible_lev, lwLev_eq_weight] at hy
  rcases lt_or_ge k 0 with hk | hk
  · rw [weight_neg_eq_bot P hk, Submodule.mem_bot] at hy
    rw [hy]; exact Submodule.zero_mem _
  · obtain ⟨K, rfl⟩ : ∃ K : ℕ, k = (K : ℤ) := ⟨k.toNat, by omega⟩
    exact hlev K y (by simpa using hy)

/-- **Over a `C₂`-cofinite `𝒱`, a lowest-weight module is `C₂`-cofinite iff it is graded
`C₁`-cofinite.** -/
theorem lwModule_C2_iff_C1 (hC2 : C2Cofinite W) (P : LWModule W) :
    ModuleC2Cofinite P.isMod.toWeakModule ↔ ∃ B, C1Graded P.isMod P.h B := by
  constructor
  · exact c1Graded_of_moduleC2Cofinite P.isMod P.isLow
  · rintro ⟨B, hB⟩
    obtain ⟨S, hS, hLW⟩ := exists_finite_lwGenerated_of_C1Graded P hB
    exact moduleC2Cofinite_of_LWGenerated _ hC2 hS hLW

/-- **Irreducible modules of a strongly rational VOA are graded `C₁`-cofinite** (Huang's
hypothesis; TRUE by Buhl 2002 / Abe–Buhl–Dong 2004 plus `C₂(M) ⊆ C₁(M)`). -/
def ModuleC1Input : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    StronglyRational W → ∀ P : LWModule W, P.IsIrreducibleLW → ∃ B, C1Graded P.isMod P.h B

/-- **`ModuleC2Input ⟺ ModuleC1Input`.** -/
theorem moduleC2Input_iff_moduleC1Input : ModuleC2Input.{u} ↔ ModuleC1Input.{u} := by
  constructor
  · intro h 𝒱 _ _ W hV P hP
    exact (lwModule_C2_iff_C1 hV.toStronglyFinite.c2Cofinite P).mp (h 𝒱 W hV P hP)
  · intro h 𝒱 _ _ W hV P hP
    exact (lwModule_C2_iff_C1 hV.toStronglyFinite.c2Cofinite P).mpr (h 𝒱 W hV P hP)

/-- **`ModuleC2Input ⟺ BuhlFiniteLWGenInput`.** -/
theorem moduleC2Input_iff_buhlFiniteLWGen : ModuleC2Input.{u} ↔ BuhlFiniteLWGenInput.{u} := by
  refine ⟨fun h => ?_, moduleC2Input_of_buhlFiniteLWGen⟩
  intro 𝒱 _ _ W hV P hP
  obtain ⟨B, hB⟩ := moduleC2Input_iff_moduleC1Input.mp h 𝒱 W hV P hP
  exact exists_finite_lwGenerated_of_C1Graded P hB

/-- **`ModuleC2Input ⟺ BuhlBaseClosedInput`.** -/
theorem moduleC2Input_iff_buhlBaseClosed : ModuleC2Input.{u} ↔ BuhlBaseClosedInput.{u} :=
  moduleC2Input_iff_buhlFiniteLWGen.trans buhlFiniteLWGenInput_iff_baseClosed

end VOA.Huang.ModuleC2
