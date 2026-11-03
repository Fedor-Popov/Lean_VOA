/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorFinSpan

/-!
# No high submodules in a finitely generated logarithmic module (stage T1d, part 3)

`exists_eq_bot_of_high`: for a `C₂`-cofinite VOA and a finitely generated `LogVModule` `N`,
there is a real `C` such that **every weak submodule of `N` all of whose weights have
`Re α ≥ C` is zero**.

This is the dual-free replacement for "`C₂`-cofiniteness of the contragredient `N'`" in the
third slot of the finiteness argument for logarithmic fusion rules.

*Proof.*  `N` has finite length over its mode algebra (`finiteLength_fg_of_c2Cofinite`), hence is
Artinian.  For `c ∈ ℕ` let `highSub N c` be the largest mode-algebra submodule with no
components below `Re = c`; it is antitone in `c` and so stabilizes at some `c₀`.  A vector in
`highSub N c₀` then lies in every `highSub N c`, so all of its components vanish.

No `sorry`, no new axioms.
-/

namespace VOA.LogTensor.LogFin

open Module (End)
open VOA.Classification.COne PlusRational

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M] (N : LogVModule W M)

/-- A finitely generated weak module over a `C₂`-cofinite VOA is Artinian over its mode
algebra. -/
theorem isArtinian_of_finGen (hC2 : C2Cofinite W) (hfg : FinGen N.toWeakModule) :
    IsArtinian (modeAlg N.toWeakModule) M := by
  classical
  obtain ⟨S, hSfin, hgen⟩ := hfg
  set P : Submodule (modeAlg N.toWeakModule) M := Submodule.span _ S with hPdef
  have hFG : P.FG := ⟨hSfin.toFinset, by rw [Set.Finite.coe_toFinset]⟩
  have hres : P.restrictScalars ℂ = ⊤ :=
    hgen _ (fun s hs => Submodule.subset_span hs) (modeStable_restrictScalars N P)
  have htop : P = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have : y ∈ P.restrictScalars ℂ := by rw [hres]; trivial
    exact this
  have hfl := PlusFiniteLength.finiteLength_fg_of_c2Cofinite hC2 N.toWeakModule P hFG
  obtain ⟨_, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  exact isArtinian_of_linearEquiv (LinearEquiv.ofTop P htop)

/-- The largest mode-algebra submodule with no components of real part below `c`. -/
def highSub (c : ℝ) : Submodule (modeAlg N.toWeakModule) M where
  carrier := {y | ∀ a : modeAlg N.toWeakModule, ∀ α : ℂ, α.re < c →
    proj N α ((a : End ℂ M) y) = 0}
  add_mem' := by
    intro y z hy hz a α hα
    simp only [Set.mem_setOf_eq] at hy hz ⊢
    rw [map_add, map_add, hy a α hα, hz a α hα, add_zero]
  zero_mem' := by
    intro a α hα
    simp
  smul_mem' := by
    intro b y hy a α hα
    exact hy (a * b) α hα

theorem highSub_anti {c c' : ℝ} (h : c ≤ c') : highSub N c' ≤ highSub N c :=
  fun _ hy a α hα => hy a α (lt_of_lt_of_le hα h)

/-- **No high weak submodules**: some `C` is such that every mode-stable subspace with no
components of real part `< C` is zero. -/
theorem exists_eq_bot_of_high (hC2 : C2Cofinite W) (hfg : FinGen N.toWeakModule) :
    ∃ C : ℝ, ∀ P : Submodule ℂ M, ModeStable N.toWeakModule P →
      (∀ y ∈ P, ∀ α : ℂ, α.re < C → proj N α y = 0) → P = ⊥ := by
  haveI := isArtinian_of_finGen N hC2 hfg
  let f : ℕ →o (Submodule (modeAlg N.toWeakModule) M)ᵒᵈ :=
    ⟨fun j => OrderDual.toDual (highSub N j), fun i j hij =>
      highSub_anti N (by exact_mod_cast hij)⟩
  obtain ⟨j₀, hj₀⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨j₀, fun P hP hlow => ?_⟩
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  have hy0 : y ∈ highSub N j₀ := fun a α hα =>
    hlow _ (modeAlg_mem_of_modeStable N hP a.2 y hy) α hα
  apply eq_zero_of_proj N
  intro α
  obtain ⟨m, hm⟩ := exists_nat_gt (max α.re (j₀ : ℝ))
  have hjm : j₀ ≤ m := by
    have : (j₀ : ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
    exact_mod_cast this.le
  have heq : highSub N j₀ = highSub N m := congrArg OrderDual.ofDual (hj₀ m hjm)
  have hym : y ∈ highSub N m := by rw [← heq]; exact hy0
  have := hym 1 α (lt_of_le_of_lt (le_max_left _ _) hm)
  simpa using this

end VOA.LogTensor.LogFin
