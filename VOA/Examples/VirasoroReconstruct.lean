/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroWordFields

/-!
# The basis-free vertex map `YA` of the Virasoro VOA `L(c,0)`

Applying the `Core` operator-first reconstruction theorem to the cyclic module
`VirUniv c = U(𝔙𝔦𝔯)/J(c)`: from the generating word fields `YwordVir` (all `IsField`, pairwise
local, with creation tower `(YwordVir ws)₀|0⟩ = negWordVir ws` spanning `L(c,0)`) and the
translation operator `T = L₋₁` (`Ltrans`, with `T|0⟩ = 0` and generator covariance
`[L₋₁, Y(ω,z)] = ∂_z Y(ω,z)` lifted through `nprod`/`deriv` to every word field), we obtain the
all-states vertex map `virYA` and the basis-free VA axioms (VA3 creation, VA4 locality, VA5
regularity, translation covariance).  `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)
open VOA.Reconstruction

variable (c : ℂ)

/-! ## §1  The translation operator `T = L₋₁` and `T|0⟩ = 0`. -/

/-- The **translation operator** `T = L₋₁ = ω₍₀₎` on `L(c,0)`. -/
noncomputable def Ltrans : End ℂ (VirUniv c) := Lop c (-1)

/-- **`L₋₁` annihilates the vacuum** (`T|0⟩ = 0`): the translation-of-vacuum / highest-weight
condition (`L₋₁|0⟩ = 0`). -/
theorem Ltrans_vacuum : Ltrans c (vacVec c) = 0 := Lop_vacuum c (by omega)

/-! ## §2  The generator covariance `[L₋₁, Y(ω,z)] = ∂_z Y(ω,z)`, lifted to every word field. -/

/-- **The generator covariance** `[L₋₁, ω₍ₘ₎] = (m+1)·ω₍ₘ₊₁₎`, i.e. `DCovariant (L₋₁) Y(ω,z)`.
Immediate from the abstract Virasoro relation `Lop_bracket`: the central cocycle vanishes because
`(−1)³ − (−1) = 0`, so the bracket is purely the mode-shifted term `(m+1)·L₋ₘ₋₃`. -/
theorem YomegaVir_DCovariant : DCovariant (Ltrans c) (YomegaVir c) := by
  intro m
  change Lop c (-1) * (YomegaVir c m) - (YomegaVir c m) * Lop c (-1)
      = ((m + 1 : ℤ)) • (YomegaVir c (m + 1))
  simp only [YomegaVir_apply]
  rw [Lop_bracket, show ((-1 : ℤ)) + (-(m : ℤ) - 2) = -(m + 1) - 2 from by ring,
    ← Int.cast_smul_eq_zsmul ℂ (m + 1)]
  split_ifs with hc
  · rw [show (((-1 : ℤ) : ℂ) ^ 3 - ((-1 : ℤ) : ℂ)) / 12 * c = 0 from by norm_num,
      zero_smul, add_zero]
    congr 1; push_cast; ring
  · rw [zero_smul, add_zero]
    congr 1; push_cast; ring

/-- The identity field is `T`-covariant. -/
theorem idFieldVir_DCovariant : DCovariant (Ltrans c) (idFieldVir c) := by
  have e : ∀ j : ℤ, idFieldVir c j = if j = 0 then (1 : End ℂ (VirUniv c)) else 0 :=
    fun j => rfl
  intro m
  change Ltrans c * (idFieldVir c m) - (idFieldVir c m) * Ltrans c
      = ((m + 1 : ℤ)) • (idFieldVir c (m + 1))
  rw [e m, e (m + 1)]
  split_ifs with h0 h1 h1
  · omega
  · simp
  · rw [show (m + 1 : ℤ) = 0 from h1]; simp
  · simp

/-- The generator fields `genFieldVir i = (i!)⁻¹ ∂_z^i Y(ω,z)` inherit `T`-covariance. -/
theorem genFieldVir_DCovariant (i : ℕ) : DCovariant (Ltrans c) (genFieldVir c i) := by
  rw [genFieldVir]
  exact DCovariant.smul ((i.factorial : ℂ)⁻¹)
    (DCovariant.deriv_iterate (YomegaVir_DCovariant c) i)

/-- Every word field `YwordVir ws` is `T`-covariant (induction over the word, `DCovariant.nprod`
for the step). -/
theorem YwordVir_DCovariant : ∀ ws : List ℕ, DCovariant (Ltrans c) (YwordVir c ws)
  | [] => by rw [YwordVir_nil]; exact idFieldVir_DCovariant c
  | (i :: rest) => by
      rw [YwordVir_cons]
      exact DCovariant.nprod (genFieldVir_isField c i) (YwordVir_isField c rest)
        (genFieldVir_DCovariant c i) (YwordVir_DCovariant rest)

/-! ## §3  The basis-free vertex map `virYA` from the reconstruction theorem. -/

/-- **The basis-free Virasoro `YA`** from the `Core` reconstruction theorem: yields
`virYA (negWordVir ws) = YwordVir ws`, `IsField`, mutual locality, the VA3 creation tower, and
translation covariance — the all-states vertex-map data for the `virasoroVOA c` shell. -/
theorem virYA_exists :
    ∃ YA : VirUniv c →ₗ[ℂ] FormalDist (End ℂ (VirUniv c)),
      (∀ ws : List ℕ, YA (negWordVir c ws) = YwordVir c ws) ∧
      (∀ u : VirUniv c, IsField (YA u)) ∧
      (∀ u v : VirUniv c, Local (YA u) (YA v)) ∧
      (∀ u : VirUniv c, (YA u) 0 (vacVec c) = u) ∧
      (∀ u : VirUniv c, ∀ q : ℤ, q < 0 → (YA u) q (vacVec c) = 0) ∧
      (∀ u : VirUniv c, DCovariant (Ltrans c) (YA u)) :=
  Reconstruction.reconstruct (vacVec c) (negWordVir c) (YwordVir c) (Ltrans c)
    (negSpanVir_eq_top c) (YwordVir_isField c) (YwordVir_local c)
    (fun ws => YwordVir_vacuum_base c ws) (fun ws _q hq => YwordVir_vacuum_neg c ws hq)
    (Ltrans_vacuum c) (YwordVir_DCovariant c)

end VOA.VirModule
