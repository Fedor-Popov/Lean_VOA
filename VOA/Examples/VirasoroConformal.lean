/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroReconstruct

/-!
# The Virasoro vertex map `virYA`, the conformal field, and VOA1

Extracting the all-states vertex map `virYA` from the reconstruction `virYA_exists`, identifying the
field of the conformal vector `ω = L₋₂|0⟩` with `Y(ω,z)` (`virYA_omega`), and proving **VOA1**: the
modes `Lₙ = ω₍ₙ₊₁₎` obey the Virasoro relation at central charge `c` (`virYA_virasoro`), directly
from the abstract relation `Lop_bracket`.  `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)
open VOA.Reconstruction

variable (c : ℂ)

/-! ## §1  The all-states vertex map `virYA` and its reconstruction properties. -/

/-- The state-field map on the universal Virasoro vacuum module. Reconstruction
provides existence, and this definition chooses a linear map satisfying its
word, locality, creation and translation properties. No simple quotient is
taken in this definition. -/
noncomputable def virYA : VirUniv c →ₗ[ℂ] FormalDist (End ℂ (VirUniv c)) := (virYA_exists c).choose

/-- On a state made by applying negative Virasoro modes to the vacuum, the
reconstructed vertex map agrees with the prescribed normally ordered word
field. This identifies the abstract reconstruction with the generating data. -/
theorem virYA_word (ws : List ℕ) : virYA c (negWordVir c ws) = YwordVir c ws :=
  (virYA_exists c).choose_spec.1 ws

/-- Every reconstructed field is lower truncated on each input state: only
finitely many sufficiently singular coefficients act nontrivially. Thus the
formal distribution is a field in the vertex-algebra sense. -/
theorem virYA_isField (u : VirUniv c) : IsField (virYA c u) := (virYA_exists c).choose_spec.2.1 u

/-- Any two reconstructed fields are mutually local: a sufficiently high
power of the difference of their formal variables kills their commutator.
This extends locality of the generators to arbitrary states. -/
theorem virYA_local (u v : VirUniv c) : Local (virYA c u) (virYA c v) :=
  (virYA_exists c).choose_spec.2.2.1 u v

/-- Applying a state field to the vacuum recovers that state in its constant
coefficient. Here the integer argument indexes powers of the formal variable,
so coefficient zero is the usual creation product with mode index minus one. -/
theorem virYA_vacuum0 (u : VirUniv c) : virYA c u 0 (vacVec c) = u :=
  (virYA_exists c).choose_spec.2.2.2.1 u

/-- The field applied to the vacuum has no negative powers of the formal
variable. Together with its constant coefficient, this is the creation
property; the index here is a power index, not the conventional mode index. -/
theorem virYA_vacuum_neg (u : VirUniv c) {q : ℤ} (hq : q < 0) : virYA c u q (vacVec c) = 0 :=
  (virYA_exists c).choose_spec.2.2.2.2.1 u q hq

/-- Commuting the translation operator with any reconstructed field gives
its formal derivative. This is covariance of the field under translation;
it is the operator identity used by reconstruction. -/
theorem virYA_DCov (u : VirUniv c) : DCovariant (Ltrans c) (virYA c u) :=
  (virYA_exists c).choose_spec.2.2.2.2.2 u

/-! ## §2  The field of the conformal vector `ω`. -/

/-- The generator field at order `0` is `Y(ω,z)`: `genFieldVir 0 = ∂⁰Y(ω,z) = Y(ω,z)`. -/
theorem genFieldVir_zero : genFieldVir c 0 = YomegaVir c := by
  rw [genFieldVir, Function.iterate_zero, id, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

/-- The length-one word field is `Y(ω,z)`: `YwordVir [0] = :Y(ω,z)·𝟙: = Y(ω,z)`. -/
theorem YwordVir_zero : YwordVir c [0] = YomegaVir c := by
  rw [YwordVir_cons]
  change nprod (genFieldVir_isField c 0) (idField_isField) = YomegaVir c
  rw [nprod_idField, genFieldVir_zero]

/-- **The field of `ω` is `Y(ω,z)`**: `virYA ω = Y(ω,z) = ∑ Lₙ z^{−n−2}`.  (`ω = negWordVir [0]`.) -/
theorem virYA_omega : virYA c (omegaVir c) = YomegaVir c := by
  have h := virYA_word c [0]
  rw [show negWordVir c [0] = omegaVir c from rfl, YwordVir_zero] at h
  exact h

/-! ## §3  VOA1 — the Virasoro relation for the modes `Lₙ = ω₍ₙ₊₁₎`. -/

/-- **VOA1 (conformal symmetry)**: writing `Lₙ = mode (Y ω) (n+1)`, the modes obey the Virasoro
relation `[Lₘ,Lₙ] = (m−n)L_{m+n} + (c/12)(m³−m)δ_{m+n,0}` at central charge `c` — directly from the
abstract relation `Lop_bracket` (since `mode (Y ω) (m+1) = Lₘ = Lop c m`). -/
theorem virYA_virasoro (m n : ℤ) :
    ⁅mode (virYA c (omegaVir c)) (m + 1), mode (virYA c (omegaVir c)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (virYA c (omegaVir c)) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * c) • (1 : End ℂ (VirUniv c)) else 0) := by
  simp only [virYA_omega, mode_YomegaVir,
    show (m + 1 - 1 : ℤ) = m from by ring, show (n + 1 - 1 : ℤ) = n from by ring,
    show (m + n + 1 - 1 : ℤ) = m + n from by ring]
  rw [LieRing.of_associative_ring_bracket, Lop_bracket]
  congr 1
  split_ifs
  · rfl
  · rw [zero_smul]

/-- The zero mode of the conformal field is the translation operator L₋₁.
This identifies the operator implementing translation with the conformal
structure; it is distinct from the state-field translation identity. -/
theorem mode_virYA_omega_zero : mode (virYA c (omegaVir c)) 0 = Ltrans c := by
  rw [virYA_omega, mode_YomegaVir, show (0 - 1 : ℤ) = -1 from by ring, Ltrans]

end VOA.VirModule
