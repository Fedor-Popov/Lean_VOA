/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroGradedField
import VOA.Examples.VirasoroNonvanishing
import VOA.Examples.LeeYangSingular

/-!
# The general central-charge universal Virasoro VOA `V(c,0) = VirUniv c`

The 19-field `VertexOperatorAlgebra (VirUniv c)` instance for arbitrary central charge `c ∈ ℂ`,
assembled from the reconstruction-derived vertex map `virYA` and the conformal/grading layer:
VA2 vacuum (`virYA_vacuum`), VA3 creation (`virYA_creation`), VA5 regularity (`virYA_regularity`),
VOA1 Virasoro (`virYA_virasoro`), VOA2 `L₀`-grading (`virYA_L0_grading`), VOA3 translation
(`virYA_translation`, operator-first uniqueness via the shared vacuum tower + Goddard), and the
`pbw`-free energy grading (`gradingVir`, `isInternal`, `finrank`, `positivity`, `vacuum_grade`,
`grading_mode`).

This is the universal Virasoro vacuum VOA `V(c,0)` for **any** `c`; `c = 1` recovers the free-boson
realization `virasoroVOA1`.  All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)
open VOA.Reconstruction

variable (c : ℂ)

/-! ## §1  VA2 (vacuum field is the unit), VA3 (creation), VA5 (regularity). -/

/-- The Virasoro identity field is the unit field `1`. -/
theorem idFieldVir_eq_one : idFieldVir c = (1 : FormalDist (End ℂ (VirUniv c))) := by
  funext j
  rw [idFieldVir, FormalDist.one_apply]
  split_ifs <;> rfl

/-- **VA2**: `Y(|0⟩, z) = 1`. -/
theorem virYA_vacuum : virYA c (vacVec c) = (1 : FormalDist (End ℂ (VirUniv c))) := by
  rw [show vacVec c = negWordVir c [] from rfl, virYA_word, YwordVir_nil, idFieldVir_eq_one]

/-- **VA3 (creation)**: `u₍₋₁₎|0⟩ = u` and `u₍ₙ₎|0⟩ = 0` for `n ≥ 0`. -/
theorem virYA_creation (u : VirUniv c) :
    mode (virYA c u) (-1) (vacVec c) = u
      ∧ ∀ n : ℤ, 0 ≤ n → mode (virYA c u) n (vacVec c) = 0 := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [mode_apply, show (-(-1 : ℤ) - 1) = 0 from by ring, virYA_vacuum0]
  · rw [mode_apply]; exact virYA_vacuum_neg c u (by omega)

/-- **VA5 (regularity)**: for each `u, v` the products `u₍ₙ₎v` vanish for `n` large. -/
theorem virYA_regularity (u v : VirUniv c) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (virYA c u) n v = 0 := by
  obtain ⟨B, hB⟩ := virYA_isField c u v
  refine ⟨-B, fun n hn => ?_⟩
  rw [mode_apply]; exact hB (-n - 1) (by omega)

/-! ## §2  VOA2 (`L₀`-grading) and the first creation-tower step. -/

/-- **VOA2**: `L₀ = mode (Y ω) 1` acts on `𝒱ₙ` as multiplication by `n`. -/
theorem virYA_L0_grading {n : ℤ} (v : VirUniv c) (hv : v ∈ gradingVir c n) :
    mode (virYA c (omegaVir c)) 1 v = (n : ℂ) • v := by
  rw [virYA_omega, mode_YomegaVir, show (1 - 1 : ℤ) = 0 from by ring]
  exact L0_grading_gen c v hv

/-- `(Y v)₁|0⟩ = L₋₁ v` (the first creation-tower step, from translation covariance). -/
theorem virYA_one_vac (v : VirUniv c) : (virYA c v) 1 (vacVec c) = Ltrans c v := by
  have h := congrArg (fun (R : End ℂ (VirUniv c)) => R (vacVec c)) (virYA_DCov c v 0)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [Ltrans_vacuum, map_zero, sub_zero, virYA_vacuum0, show ((0 : ℤ) + 1) = 1 from by ring,
    one_smul] at h
  exact h.symm

/-! ## §3  VOA3 (translation) — operator-first uniqueness. -/

/-- **VOA3 (translation), `L₋₁` form**: `Y(L₋₁ v, z) = ∂_z Y(v,z)`.  Both `Y(L₋₁ v)` and `∂Y(v)` are
`T`-covariant, annihilate `|0⟩` below degree `0`, and share the base `(·)₀|0⟩ = L₋₁ v`, so by
`tower_unique` they agree on the whole vacuum tower; being local with a spanning family of creating
word fields, Goddard uniqueness `field_eq_zero_of_vacuum` forces them equal. -/
theorem virYA_translation (v : VirUniv c) :
    virYA c (Ltrans c v) = VOA.deriv (virYA c v) := by
  have hGcov : DCovariant (Ltrans c) (VOA.deriv (virYA c v)) :=
    DCovariant.deriv' (virYA_DCov c v)
  have hGneg : ∀ q : ℤ, q < 0 → (VOA.deriv (virYA c v)) q (vacVec c) = 0 := by
    intro q hq
    rw [deriv_apply, ← Int.cast_smul_eq_zsmul ℂ (q + 1), LinearMap.smul_apply]
    by_cases hq1 : q + 1 < 0
    · rw [virYA_vacuum_neg c v hq1, smul_zero]
    · rw [show q + 1 = (0 : ℤ) from by omega, Int.cast_zero, zero_smul]
  have hbase : (virYA c (Ltrans c v)) 0 (vacVec c) = (VOA.deriv (virYA c v)) 0 (vacVec c) := by
    rw [virYA_vacuum0, deriv_apply, ← Int.cast_smul_eq_zsmul ℂ (0 + 1), LinearMap.smul_apply,
      show (0 + 1 : ℤ) = 1 from by ring, Int.cast_one, one_smul, virYA_one_vac]
  have hAvac : ∀ p : ℤ,
      (virYA c (Ltrans c v) - VOA.deriv (virYA c v)) p (vacVec c) = 0 := by
    intro p
    show ((virYA c (Ltrans c v)) p - (VOA.deriv (virYA c v)) p) (vacVec c) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact tower_unique (virYA_DCov c (Ltrans c v)) hGcov (Ltrans_vacuum c) hbase
      (fun q hq => virYA_vacuum_neg c (Ltrans c v) hq) hGneg p
  have hloc : ∀ ws : List ℕ,
      Local (virYA c (Ltrans c v) - VOA.deriv (virYA c v)) (YwordVir c ws) := by
    intro ws
    have h1 : Local (virYA c (Ltrans c v)) (YwordVir c ws) := by
      rw [← virYA_word]; exact virYA_local c (Ltrans c v) (negWordVir c ws)
    have h2 : Local (VOA.deriv (virYA c v)) (YwordVir c ws) := by
      have hv : Local (virYA c v) (YwordVir c ws) := by
        rw [← virYA_word]; exact virYA_local c v (negWordVir c ws)
      exact Local.derivL hv
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (VOA.deriv (virYA c v))]
    exact Local.add_left h1 (VertexOperatorAlgebra.Local.smul' (-1) h2)
  have hz := field_eq_zero_of_vacuum (vacVec c)
    (virYA c (Ltrans c v) - VOA.deriv (virYA c v)) (negWordVir c) (YwordVir c)
    hloc (fun ws => YwordVir_vacuum_base c ws) (fun ws q hq => YwordVir_vacuum_neg c ws hq)
    hAvac (negSpanVir_eq_top c)
  rwa [sub_eq_zero] at hz

/-- **VOA3** in the structure's `ω₍₀₎` form: `Y(ω₍₀₎ v, z) = ∂_z Y(v,z)`. -/
theorem virYA_omega_translation (v : VirUniv c) :
    virYA c (mode (virYA c (omegaVir c)) 0 v) = VOA.deriv (virYA c v) := by
  rw [mode_virYA_omega_zero]; exact virYA_translation c v

/-! ## §4  The Virasoro vertex operator algebra `Vir(c)`. -/

/-- **The general central-charge Virasoro vertex operator algebra** `V(c,0)` (not the simple
quotient `L(c,0)`, which is `virasoroSimple c`), the universal
Virasoro vacuum VOA of central charge `c ∈ ℂ`, on the carrier `VirUniv c = U(𝔙𝔦𝔯)/J(c)`.  Assembled
`pbw`-free from the operator-first reconstruction (`virYA`) and the energy grading. -/
noncomputable def virasoroVOA : VertexOperatorAlgebra (VirUniv c) where
  grading := gradingVir c
  isInternal := gradingVir_isInternal c
  finrank := gradingVir_finiteDimensional c
  Y := virYA c
  vacuum := vacVec c
  vacuum_mem := vacVec_mem_gradingVir_zero c
  grading_mode := fun u hu v hv n => virYA_grading_mode c u hu v hv n
  vacuum_Y := virYA_vacuum c
  creation := virYA_creation c
  locality := virYA_local c
  regularity := virYA_regularity c
  conformalVector := omegaVir c
  conformal_mem := omegaVir_mem_gradingVir_two c
  centralCharge := c
  virasoro := virYA_virasoro c
  L0_grading := fun {_} v hv => virYA_L0_grading c v hv
  translation := virYA_omega_translation c
  vacuum_grade := gradingVir_zero c
  positivity := gradingVir_neg c

/-- **The central charge of `Vir(c)` is `c`** — for arbitrary `c ∈ ℂ`. -/
theorem virasoroVOA_centralCharge : (virasoroVOA c).centralCharge = c := rfl

/-! ## §5  Non-degeneracy: the conformal vector is genuinely nonzero (every `c`). -/

/-- **`ω ≠ 0` at every central charge** — the conformal vector `ω = L₋₂|0⟩` of the universal
module `V(c,0)` is nonzero for all `c ∈ ℂ`, including `c = 0` (`pbw`-free): under the
linear-dilaton Fock realization its image `½X₀² − λX₁` is nonzero (`LeeYang.L2vac_ne_zero`).
The hypothesis `c ≠ 0` is not needed; note that
`ω` does vanish in the simple quotient `L(0,0) = ℂ𝟙`, but not in `V(0,0)`. -/
theorem omegaVir_ne_zero : omegaVir c ≠ 0 := LeeYang.L2vac_ne_zero c

/-- **The conformal vector of the VOA instance is nonzero** at every central charge. -/
theorem virasoroVOA_conformalVector_ne_zero :
    (virasoroVOA c).conformalVector ≠ 0 := omegaVir_ne_zero c

end VOA.VirModule
