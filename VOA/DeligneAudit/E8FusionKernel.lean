/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8FusionKernelFacts

/-!
# `E₈`: the kernel table for Ravinder's family

`e8KernelTable : KernelTable E8sector` collects the structure-constant facts, each checked by kernel `decide` on
the table `e8T`. The table scan is `Notes/deligne/campaign/generators/e8_kernel_scan.py`, the data is in
`e7_data/kernel_e8.json`, and `e8_emit_kernel.py` emits this file (as a transform of `E7FusionKernel`).

* `e_θ = x₁₂₇` with `s_θ = -1`, and `θ(h₇) = 1`.
* The one simple lowering vector with `θ(h) = 1` is `f = x₁₂₈`, with `sl₂` partner `e = x₈` and `h = h₇`.
* `β(x)` with `[e_β, f_θ] = κ f_x` is given for the 56 fusion roots `x ≠ f_θ`.
* The seven simple roots orthogonal to `θ` (`x₁₂₉ … x₁₃₅`) are lowering vectors with `lowExp = 0`.

The declarations are in the namespace `UnivG.E8K`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG.E8K

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E8 (E8sector thetaH lowExpE8 fusionE8)

noncomputable section

theorem fus_or_low {x : Fin 248} (hx : E8sector.fusion x ∨ E8sector.lowering x) :
    x.val ∈ fusL ∨ x.val ∈ lowL := by
  rcases hx with hx | hx
  · exact Or.inl ((fusion_iff x).mp hx)
  · exact Or.inr ((lowering_iff x).mp hx)

theorem e8_truncUp (x : Fin 248) (hx : E8sector.fusion x ∨ E8sector.lowering x) :
    ∃ h, E8sector.cartan h ∧ E8sector.f h x x ≠ 0 ∧ ∀ c, c ≠ x → E8sector.f h x c = 0 := by
  obtain ⟨h1, h2, h3⟩ := e8_truncUpZ x (fus_or_low hx)
  refine ⟨hselK x, h1, ?_, fun c hc => ?_⟩
  · rw [fE8K_eq]; exact_mod_cast h2
  · rw [fE8K_eq, h3 c hc, Int.cast_zero]

theorem e8_raisTheta (e : Fin 248) (he : E8sector.raising e) (c : Fin 248)
    (hc : E8sector.f e E8sector.c₀ c ≠ 0) :
    E8sector.cartan c ∨ (E8sector.fusion c ∧ c ≠ E8sector.c₀) := by
  have hc' : fZ brK e 247 c ≠ 0 := by
    intro h0; apply hc; show ((fZ brK e 247 c : ℤ) : ℂ) = 0; rw [h0, Int.cast_zero]
  rcases e8_raisThetaZ e c he.1 he.2 hc' with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨(fusion_iff c).mpr h1, h2⟩

theorem e8_cartTheta (h : Fin 248) (hh : E8sector.cartan h) (c : Fin 248) :
    E8sector.f h E8sector.c₀ c = if c = E8sector.c₀ then -(E8sector.thetaH h : ℂ) else 0 := by
  show ((fZ brK h 247 c : ℤ) : ℂ) = if c = 247 then -((thetaH h : ℕ) : ℂ) else 0
  rw [e8_cartThetaZ h c hh]
  split_ifs <;> simp

theorem e8_lowComm (x : Fin 248) (hx : E8sector.fusion x ∨ E8sector.lowering x) (c : Fin 248) :
    E8sector.f x E8sector.c₀ c = 0 := by
  show ((fZ brK x 247 c : ℤ) : ℂ) = 0
  rw [e8_lowCommZ x c (fus_or_low hx), Int.cast_zero]

theorem e8_lowExp_le (i : Fin 248) : lowExpE8 i ≤ 1 := by
  unfold lowExpE8; split_ifs <;> omega

theorem e8_simple (i : Fin 248) (h1 : lowExpE8 i = 1) :
    ∃ e hi : Fin 248, E8sector.raising e ∧ E8sector.cartan hi ∧
      (∀ c : Fin 248, E8sector.f e i c = if c = hi then 1 else 0) ∧ E8sector.thetaH hi = 1 ∧
      (∀ c : Fin 248, E8sector.f hi i c = if c = i then -2 else 0) := by
  have hi76 : i = (128 : Fin 248) := by
    unfold lowExpE8 at h1
    split_ifs at h1 <;> first | (exfalso; omega) | assumption
  subst hi76
  refine ⟨(8 : Fin 248), (7 : Fin 248), (show 8 ≤ ((8 : Fin 248) : ℕ) ∧ ((8 : Fin 248) : ℕ) < 128 by decide),
    (show ((7 : Fin 248) : ℕ) < 8 by decide), fun c => ?_, by decide, fun c => ?_⟩
  · show ((fZ brK 8 128 c : ℤ) : ℂ) = if (c : Fin 248) = 7 then 1 else 0
    rw [e8_simpleZ.1 c]; split_ifs <;> simp
  · show ((fZ brK 7 128 c : ℤ) : ℂ) = if (c : Fin 248) = 128 then -2 else 0
    rw [e8_simpleZ.2 c]; split_ifs <;> simp

theorem e8_eθ_cartan (c : Fin 248) (hc : E8sector.f (127 : Fin 248) E8sector.c₀ c ≠ 0) : E8sector.cartan c := by
  have : ((fZ brK 127 247 c : ℤ) : ℂ) ≠ 0 := hc
  exact e8_eθZ.1 c (by exact_mod_cast this)

theorem e8_eθ_theta :
    (-1 : ℂ) * ∑ c : Fin 248, E8sector.f (127 : Fin 248) E8sector.c₀ c * (E8sector.thetaH c : ℂ) = 2 := by
  rw [Finset.sum_eq_single (7 : Fin 248)]
  · show (-1 : ℂ) * (((fZ brK 127 247 7 : ℤ) : ℂ) * ((thetaH 7 : ℕ) : ℂ)) = 2
    rw [e8_eθZ.2]; simp [thetaH]
  · intro c _ hc
    have : thetaH c = 0 := by unfold thetaH; simp [hc]
    show _ * ((thetaH c : ℕ) : ℂ) = 0
    rw [this]; simp
  · simp

theorem e8_fusionRoot (x : Fin 248) (hx : E8sector.fusion x) (hx0 : x ≠ E8sector.c₀) :
    (∃ (β : Fin 248) (κ : ℂ), E8sector.raising β ∧ κ ≠ 0 ∧
      ∀ c : Fin 248, E8sector.f β E8sector.c₀ c = if c = x then κ else 0) ∨
      (E8sector.lowering x ∧ E8sector.lowExp x = 0) := by
  left
  obtain ⟨h1, h2, h3, h4⟩ := e8_rootZ x ((fusion_iff x).mp hx) hx0
  refine ⟨bselK x, (kselK x : ℂ), ⟨h1, h2⟩, by exact_mod_cast h3, fun c => ?_⟩
  show ((fZ brK (bselK x) 247 c : ℤ) : ℂ) = if (c : Fin 248) = x then (kselK x : ℂ) else 0
  rw [h4 c]; split_ifs <;> simp

/-- The `E₈` kernel table in the simply-laced interface. -/
def e8KernelTableSL : KernelTableSL E8sector where
  noN := fun _ hh => hh
  c0_fusion := (fusion_iff 247).mpr (by decide)
  truncUp := e8_truncUp
  raisTheta := e8_raisTheta
  cartTheta := e8_cartTheta
  lowComm := e8_lowComm
  lowExp_le i _ := e8_lowExp_le i
  simple i _ h1 := e8_simple i h1
  eθ := (127 : Fin 248)
  sθ := -1
  eθ_raising := show 8 ≤ ((127 : Fin 248) : ℕ) ∧ ((127 : Fin 248) : ℕ) < 128 by decide
  eθ_cartan := e8_eθ_cartan
  eθ_theta := e8_eθ_theta
  fusionRoot := e8_fusionRoot

/-- **The `E₈` kernel table.** -/
def e8KernelTable : KernelTable E8sector := KernelTable.ofSL e8KernelTableSL

/-- **Ravinder's kernel lemma for `E₈`**, from the integrability input `ThetaNilG`. -/
theorem e8_ravinderKernelRel (hN : ThetaNilG E8sector) :
    RavinderKernelRelG E8sector.f (ravFam E8sector) (ravKw E8sector) :=
  ravinderKernelRelG_of_table E8sector e8KernelTable hN

end

end VOA.DeligneAudit.UnivG.E8K

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.E8K.e8KernelTable
#print axioms VOA.DeligneAudit.UnivG.E8K.e8_ravinderKernelRel
end AxiomAudit
