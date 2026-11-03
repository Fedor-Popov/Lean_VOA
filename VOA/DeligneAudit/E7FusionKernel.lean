/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionKernelGeneric
import VOA.DeligneAudit.E7SectorData

/-!
# `E₇`: the kernel table for Ravinder's family

`e7KernelTable : KernelTable E7sector` collects the structure-constant facts, each checked by kernel `decide` on
the integer table `e7T`. The table scan is `Notes/deligne/campaign/generators/e7_kernel_scan.py`, and this file is
emitted by `e7_emit_kernel.py`.

* `e_θ = x₆₉` with `s_θ = -1`, since `[e_θ, f_θ] = -θ^∨` and `θ(h₀) = 1`.
* The one simple lowering vector with `θ(h) = 1` is `f_{α₁} = x₇₆`, with `sl₂` partner `e = x₁₃` and `h = h₀`.
* `β(x)` with `[e_β, f_θ] = κ f_x` is given for the 32 fusion roots `x ≠ f_θ` with `(θ, α_x^∨) = 1`.
* The six simple roots orthogonal to `θ` are lowering vectors with `lowExp = 0`.

`e7_ravinderKernelRel : ThetaNilG E7sector → RavinderKernelRelG …`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E7 (E7sector thetaH lowExpE7 fusionE7)

noncomputable section

/-- The `𝔢₇` brackets: the table `e7T`. -/
def brK (a b : ℕ) : SV := VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T a b

theorem fE7K_eq (a b c : Fin 133) : E7sector.f a b c = (fZ brK a b c : ℂ) := rfl

/-- The fusion set, as indices. -/
def fusL : List ℕ := [76, 82, 88, 93, 94, 99, 100, 103, 104, 105, 108, 109, 110, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]

/-- The simple lowering vectors. -/
def lowL : List ℕ := [70, 71, 72, 73, 74, 75, 76]

theorem fusion_iff : ∀ x : Fin 133, fusionE7 x ↔ x.val ∈ fusL := by
  unfold fusionE7 VOA.DeligneAudit.DeligneCarrier.E7.thetaPair; decide +kernel

theorem lowering_iff (x : Fin 133) : E7sector.lowering x ↔ x.val ∈ lowL := by
  show x.val ∈ [76, 75, 74, 73, 72, 71, 70] ↔ _
  simp only [lowL, List.mem_cons, List.not_mem_nil, or_false]; omega

/-- A Cartan element acting diagonally and invertibly on each fusion and lowering vector. -/
def hselL : List ℕ := [5, 4, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 2, 0, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0]

def hselK (x : Fin 133) : Fin 133 := Fin.ofNat 133 (hselL.getD (x.val - 70) 0)

/-- `β(x)` and `κ(x)`: `[e_β, f_θ] = κ f_x`. -/
def bselL : List ℕ := [7, 7, 7, 7, 7, 7, 68, 7, 7, 7, 7, 7, 67, 7, 7, 7, 7, 7, 66, 7, 7, 7, 7, 65, 64, 7, 7, 7, 7, 63, 62, 7, 7, 61, 60, 59, 7, 7, 58, 57, 56, 7, 55, 54, 53, 7, 51, 50, 49, 47, 46, 45, 42, 41, 40, 37, 36, 31, 30, 25, 19, 13, 7]

def kselL : List ℤ := [1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1]

def bselK (x : Fin 133) : Fin 133 := Fin.ofNat 133 (bselL.getD (x.val - 70) 7)

def kselK (x : Fin 133) : ℤ := kselL.getD (x.val - 70) 1

theorem e7_truncUpZ : ∀ x : Fin 133, x.val ∈ fusL ∨ x.val ∈ lowL →
    (hselK x).val < 7 ∧ fZ brK (hselK x) x x ≠ 0 ∧
      ∀ c : Fin 133, c ≠ x → fZ brK (hselK x) x c = 0 := by
  decide +kernel

theorem e7_raisThetaZ : ∀ e c : Fin 133, 7 ≤ e.val → e.val < 70 → fZ brK e 132 c ≠ 0 →
    c.val < 7 ∨ (c.val ∈ fusL ∧ c ≠ 132) := by decide +kernel

theorem e7_cartThetaZ : ∀ h c : Fin 133, h.val < 7 →
    fZ brK h 132 c = if c = 132 then -(thetaH h : ℤ) else 0 := by decide +kernel

theorem e7_lowCommZ : ∀ x c : Fin 133, x.val ∈ fusL ∨ x.val ∈ lowL → fZ brK x 132 c = 0 := by
  decide +kernel

theorem e7_simpleZ : (∀ c : Fin 133, fZ brK 13 76 c = if c = 0 then 1 else 0) ∧
    (∀ c : Fin 133, fZ brK 0 76 c = if c = 76 then -2 else 0) := by decide +kernel

theorem e7_eθZ : (∀ c : Fin 133, fZ brK 69 132 c ≠ 0 → c.val < 7) ∧ fZ brK 69 132 0 = -2 := by
  decide +kernel

theorem e7_rootZ : ∀ x : Fin 133, x.val ∈ fusL → x ≠ 132 →
    7 ≤ (bselK x).val ∧ (bselK x).val < 70 ∧ kselK x ≠ 0 ∧
      ∀ c : Fin 133, fZ brK (bselK x) 132 c = if c = x then kselK x else 0 := by decide +kernel

theorem fus_or_low {x : Fin 133} (hx : E7sector.fusion x ∨ E7sector.lowering x) :
    x.val ∈ fusL ∨ x.val ∈ lowL := by
  rcases hx with hx | hx
  · exact Or.inl ((fusion_iff x).mp hx)
  · exact Or.inr ((lowering_iff x).mp hx)

theorem e7_truncUp (x : Fin 133) (hx : E7sector.fusion x ∨ E7sector.lowering x) :
    ∃ h, E7sector.cartan h ∧ E7sector.f h x x ≠ 0 ∧ ∀ c, c ≠ x → E7sector.f h x c = 0 := by
  obtain ⟨h1, h2, h3⟩ := e7_truncUpZ x (fus_or_low hx)
  refine ⟨hselK x, h1, ?_, fun c hc => ?_⟩
  · rw [fE7K_eq]; exact_mod_cast h2
  · rw [fE7K_eq, h3 c hc, Int.cast_zero]

theorem e7_raisTheta (e : Fin 133) (he : E7sector.raising e) (c : Fin 133)
    (hc : E7sector.f e E7sector.c₀ c ≠ 0) :
    E7sector.cartan c ∨ (E7sector.fusion c ∧ c ≠ E7sector.c₀) := by
  have hc' : fZ brK e 132 c ≠ 0 := by
    intro h0; apply hc; show ((fZ brK e 132 c : ℤ) : ℂ) = 0; rw [h0, Int.cast_zero]
  rcases e7_raisThetaZ e c he.1 he.2 hc' with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨(fusion_iff c).mpr h1, h2⟩

theorem e7_cartTheta (h : Fin 133) (hh : E7sector.cartan h) (c : Fin 133) :
    E7sector.f h E7sector.c₀ c = if c = E7sector.c₀ then -(E7sector.thetaH h : ℂ) else 0 := by
  show ((fZ brK h 132 c : ℤ) : ℂ) = if c = 132 then -((thetaH h : ℕ) : ℂ) else 0
  rw [e7_cartThetaZ h c hh]
  split_ifs <;> simp

theorem e7_lowComm (x : Fin 133) (hx : E7sector.fusion x ∨ E7sector.lowering x) (c : Fin 133) :
    E7sector.f x E7sector.c₀ c = 0 := by
  show ((fZ brK x 132 c : ℤ) : ℂ) = 0
  rw [e7_lowCommZ x c (fus_or_low hx), Int.cast_zero]

theorem e7_lowExp_le (i : Fin 133) : lowExpE7 i ≤ 1 := by
  unfold lowExpE7; split_ifs <;> omega

theorem e7_simple (i : Fin 133) (h1 : lowExpE7 i = 1) :
    ∃ e hi : Fin 133, E7sector.raising e ∧ E7sector.cartan hi ∧
      (∀ c : Fin 133, E7sector.f e i c = if c = hi then 1 else 0) ∧ E7sector.thetaH hi = 1 ∧
      (∀ c : Fin 133, E7sector.f hi i c = if c = i then -2 else 0) := by
  have hi76 : i = (76 : Fin 133) := by
    unfold lowExpE7 at h1
    split_ifs at h1 with h
    exact h
  subst hi76
  refine ⟨(13 : Fin 133), (0 : Fin 133), (show 7 ≤ ((13 : Fin 133) : ℕ) ∧ ((13 : Fin 133) : ℕ) < 70 by decide),
    (show ((0 : Fin 133) : ℕ) < 7 by decide), fun c => ?_, by decide, fun c => ?_⟩
  · show ((fZ brK 13 76 c : ℤ) : ℂ) = if (c : Fin 133) = 0 then 1 else 0
    rw [e7_simpleZ.1 c]; split_ifs <;> simp
  · show ((fZ brK 0 76 c : ℤ) : ℂ) = if (c : Fin 133) = 76 then -2 else 0
    rw [e7_simpleZ.2 c]; split_ifs <;> simp

theorem e7_eθ_cartan (c : Fin 133) (hc : E7sector.f (69 : Fin 133) E7sector.c₀ c ≠ 0) : E7sector.cartan c := by
  have : ((fZ brK 69 132 c : ℤ) : ℂ) ≠ 0 := hc
  exact e7_eθZ.1 c (by exact_mod_cast this)

theorem e7_eθ_theta :
    (-1 : ℂ) * ∑ c : Fin 133, E7sector.f (69 : Fin 133) E7sector.c₀ c * (E7sector.thetaH c : ℂ) = 2 := by
  rw [Finset.sum_eq_single (0 : Fin 133)]
  · show (-1 : ℂ) * (((fZ brK 69 132 0 : ℤ) : ℂ) * ((thetaH 0 : ℕ) : ℂ)) = 2
    rw [e7_eθZ.2]; simp [thetaH]
  · intro c _ hc
    have : thetaH c = 0 := by unfold thetaH; simp [hc]
    show _ * ((thetaH c : ℕ) : ℂ) = 0
    rw [this]; simp
  · simp

theorem e7_fusionRoot (x : Fin 133) (hx : E7sector.fusion x) (hx0 : x ≠ E7sector.c₀) :
    (∃ (β : Fin 133) (κ : ℂ), E7sector.raising β ∧ κ ≠ 0 ∧
      ∀ c : Fin 133, E7sector.f β E7sector.c₀ c = if c = x then κ else 0) ∨
      (E7sector.lowering x ∧ E7sector.lowExp x = 0) := by
  left
  obtain ⟨h1, h2, h3, h4⟩ := e7_rootZ x ((fusion_iff x).mp hx) hx0
  refine ⟨bselK x, (kselK x : ℂ), ⟨h1, h2⟩, by exact_mod_cast h3, fun c => ?_⟩
  show ((fZ brK (bselK x) 132 c : ℤ) : ℂ) = if (c : Fin 133) = x then (kselK x : ℂ) else 0
  rw [h4 c]; split_ifs <;> simp

/-- The `E₇` kernel table in the simply-laced interface. -/
def e7KernelTableSL : KernelTableSL E7sector where
  noN := fun _ hh => hh
  c0_fusion := (fusion_iff 132).mpr (by decide)
  truncUp := e7_truncUp
  raisTheta := e7_raisTheta
  cartTheta := e7_cartTheta
  lowComm := e7_lowComm
  lowExp_le i _ := e7_lowExp_le i
  simple i _ h1 := e7_simple i h1
  eθ := (69 : Fin 133)
  sθ := -1
  eθ_raising := show 7 ≤ ((69 : Fin 133) : ℕ) ∧ ((69 : Fin 133) : ℕ) < 70 by decide
  eθ_cartan := e7_eθ_cartan
  eθ_theta := e7_eθ_theta
  fusionRoot := e7_fusionRoot

/-- **The `E₇` kernel table.** -/
def e7KernelTable : KernelTable E7sector := KernelTable.ofSL e7KernelTableSL

/-- **Ravinder's kernel lemma for `E₇`**, from the integrability input `ThetaNilG`. -/
theorem e7_ravinderKernelRel (hN : ThetaNilG E7sector) :
    RavinderKernelRelG E7sector.f (ravFam E7sector) (ravKw E7sector) :=
  ravinderKernelRelG_of_table E7sector e7KernelTable hN

end

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.e7KernelTable
#print axioms VOA.DeligneAudit.UnivG.e7_ravinderKernelRel
end AxiomAudit
