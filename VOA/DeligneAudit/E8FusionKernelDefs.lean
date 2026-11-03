/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionKernelGeneric
import VOA.DeligneAudit.E8SectorData

/-!
# `E₈` kernel table: definitions

(See `E8FusionKernel`.)

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

/-- The `𝔢₇` brackets: the table `e7T`. -/
def brK (a b : ℕ) : SV := VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T a b

theorem fE8K_eq (a b c : Fin 248) : E8sector.f a b c = (fZ brK a b c : ℂ) := rfl

/-- The fusion set, as indices. -/
def fusL : List ℕ := [128, 136, 143, 150, 157, 164, 165, 171, 174, 178, 180, 184, 186, 190, 191, 193, 196, 197, 198, 202, 203, 204, 207, 208, 210, 212, 213, 214, 216, 217, 218, 220, 221, 222, 224, 225, 226, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247]

/-- The simple lowering vectors. -/
def lowL : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135]

theorem lowering_iff (x : Fin 248) : E8sector.lowering x ↔ x.val ∈ lowL := by
  show x.val ∈ [135, 134, 133, 132, 131, 130, 129, 128] ↔ _
  simp only [lowL, List.mem_cons, List.not_mem_nil, or_false]; omega

/-- A Cartan element acting diagonally and invertibly on each fusion and lowering vector. -/
def hselL : List ℕ := [6, 5, 4, 3, 1, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0, 0, 2, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 2, 0, 1, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 4, 5, 6, 7]

def hselK (x : Fin 248) : Fin 248 := Fin.ofNat 248 (hselL.getD (x.val - 128) 0)

/-- `β(x)` and `κ(x)`: `[e_β, f_θ] = κ f_x`. -/
def bselL : List ℕ := [126, 8, 8, 8, 8, 8, 8, 8, 125, 8, 8, 8, 8, 8, 8, 124, 8, 8, 8, 8, 8, 8, 123, 8, 8, 8, 8, 8, 8, 122, 8, 8, 8, 8, 8, 8, 121, 120, 8, 8, 8, 8, 8, 119, 8, 8, 118, 8, 8, 8, 117, 8, 116, 8, 8, 8, 115, 8, 114, 8, 8, 8, 113, 112, 8, 111, 8, 8, 110, 109, 108, 8, 8, 8, 106, 105, 104, 8, 8, 102, 101, 8, 100, 8, 98, 97, 96, 8, 94, 93, 92, 8, 90, 88, 87, 8, 84, 83, 82, 8, 78, 77, 76, 73, 71, 70, 66, 64, 60, 58, 54, 51, 45, 44, 37, 30, 23, 16, 8, 8]

def kselL : List ℤ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1, 1]

def bselK (x : Fin 248) : Fin 248 := Fin.ofNat 248 (bselL.getD (x.val - 128) 8)

def kselK (x : Fin 248) : ℤ := kselL.getD (x.val - 128) 1

end

end VOA.DeligneAudit.UnivG.E8K
