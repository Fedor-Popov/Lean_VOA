/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergVOA
import VOA.Examples.VirasoroFock
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The free boson at general central charge `c = 1 − 12λ²`  (linear dilaton / Feigin–Fuks)

`Examples/VirasoroFock` already proves the **linear-dilaton Virasoro relation** for the
background-charge modes on the rank-1 free-boson Fock space,

  `Lₙ^λ := Lₙ + λ(n+1)aₙ`,   `[Lₘ^λ, Lₙ^λ] = (m−n)L_{m+n}^λ + δ_{m+n,0}(m³−m)/12·(1−12λ²)`,

but never assembles it into a `VertexOperatorAlgebra`.  This file does exactly that:
`freeBosonVOA λ : VertexOperatorAlgebra Fock` with `centralCharge = 1 − 12λ²`.

## The observation that makes this cheap

`Fock` is the rank-1 Heisenberg **vacuum** module, so it carries zero momentum and the zero
mode acts as `0`: `osc 1 0 = 0` (`Examples.HeisenbergFock.osc_zero`, a `@[simp]` lemma —
this is a *definitional* feature of the model, `osc k n` is defined by a three-way split with
the `n = 0` branch literally `0`).  Consequently

* `Lld λ 0 = Lvir 1 0 + (λ·1)·a₀ = L₀`   (`Lld_zero`), and
* `Lld λ (-1) = Lvir 1 (-1) + (λ·0)·a₋₁ = L₋₁` (`Lld_neg_one`, the coefficient `λ(n+1)`
  vanishes at `n = -1`).

So the deformation **does not move `L₀` or `L₋₁`**: the weight grading and the translation
operator are literally unchanged.

### Which of the 19 `VertexOperatorAlgebra` fields move (verified, not assumed)

Transfer *verbatim* from `heisenbergVOA 1 one_ne_zero` (the whole `toPreVertexAlgebra`
is re-used unchanged, i.e. `heisVA 1 one_ne_zero`):

  `grading`, `isInternal`, `finrank`, `Y`, `vacuum`, `vacuum_mem`, `grading_mode`,
  `vacuum_Y`, `creation`, `locality`, `regularity`, `vacuum_grade`, `positivity`.

Transfer *after a one-line rewrite* — the statement is about `mode (Y ω^λ) 1` resp.
`mode (Y ω^λ) 0`, and those two operators are **equal** to the undeformed ones
(`mode_one_omegaLD`, `mode_zero_omegaLD`), so the undeformed proofs apply unchanged:

  `L0_grading` (VOA2), `translation` (VOA3).

Genuinely change:

  `conformalVector`, `conformal_mem`, `centralCharge`, `virasoro` (VOA1).

So the expected picture is confirmed on all counts; `L0_grading` and
`translation` do need the (trivial) rewrite `mode (Y ω^λ) i = mode (Y ω) i` for `i = 1, 0`
rather than being literally the same term, because the *conformal vector* differs.

## The deformed conformal vector and its sign

The repo convention is `Lld λ n = Lvir 1 n + λ(n+1)·aₙ`, and `Y(a₋₂|0⟩) = ∂α(z)` has modes
`mode (Y a₋₂|0⟩) (n+1) = −(n+1)·aₙ` (`mode_Y_a2`; the sign is the `−m` in
`dcurrent_mode`).  Hence the sign is pinned to a **minus**:

  `ω^λ = ω − λ·a₋₂|0⟩`,   giving `mode (Y ω^λ) (n+1) = Lₙ + λ(n+1)aₙ = Lld λ n`.

(`a₋₂|0⟩ = X₁` in the polynomial model, `osc_neg_two_vacuum`.)

## Main result

`exists_centralCharge : ∀ c : ℂ, ∃ λ, (freeBosonVOA λ).centralCharge = c` — solving
`1 − 12λ² = c` over the algebraically closed field `ℂ`.  The free boson realizes **every**
complex central charge.

All `sorry`-free and axiom-clean.

## Dependencies
* `VOA.Examples.HeisenbergVOA` (the undeformed VOA and its `heisVA`),
* `VOA.Examples.VirasoroFock` (`Lld`, `Lld_virasoro`).
-/

namespace VOA.FBgc

open VOA
open MvPolynomial
open Module (End)

/-! ## §1  The state `a₋₂|0⟩` and its vertex operator -/

/-- The creation mode `a₋₂` applied to the vacuum is the second polynomial generator:
`a₋₂|0⟩ = X₁` in `Fock = ℂ[X₀, X₁, …]`. -/
theorem osc_neg_two_vacuum : osc 1 (-2) (vacuum : Fock) = (X 1 : Fock) := by
  have h : (-(-2 : ℤ) - 1).toNat = (1 : ℕ) := by decide
  rw [osc_apply_neg 1 (by norm_num : (-2 : ℤ) < 0), h, vacuum, mul_one]

/-- `Y(a₋₂|0⟩, z) = ∂_z α(z)`: the vertex operator of `a₋₂|0⟩ = X₁` is the first derivative
current (`genField 1 1 = (1!)⁻¹∂α = ∂α`). -/
theorem Y_osc_neg_two_vacuum :
    Y 1 (osc 1 (-2) (vacuum : Fock)) = dcurrent 1 1 := by
  rw [osc_neg_two_vacuum, ← genField_eq_Y_X, genField, Nat.factorial_one, Nat.cast_one,
    inv_one, one_smul]

/-- **The modes of `Y(a₋₂|0⟩, z)`**: `mode (Y a₋₂|0⟩) (n+1) = −(n+1)·aₙ`.  This is the
computation that pins the sign of the deformed conformal vector. -/
theorem mode_Y_a2 (n : ℤ) :
    mode (Y 1 (osc 1 (-2) (vacuum : Fock))) (n + 1) = (-((n : ℂ) + 1)) • osc 1 n := by
  rw [Y_osc_neg_two_vacuum, dcurrent_mode]
  simp only [Finset.prod_range_one, Nat.cast_zero, Nat.cast_one, sub_zero]
  rw [show (n + 1 : ℤ) - 1 = n from by ring, ← Int.cast_smul_eq_zsmul ℂ]
  norm_num

/-! ## §2  The deformed conformal vector `ω^λ = ω − λ a₋₂|0⟩` -/

/-- **The linear-dilaton conformal vector** `ω^λ = ω − λ·a₋₂|0⟩`.  The minus sign is forced by
the repo convention `Lld λ n = Lvir 1 n + λ(n+1)aₙ` together with
`mode (Y a₋₂|0⟩) (n+1) = −(n+1)aₙ` (`mode_Y_a2`). -/
noncomputable def omegaLD (lam : ℂ) : Fock := ω 1 - lam • osc 1 (-2) vacuum

/-- At `λ = 0` the deformed conformal vector is the undeformed Heisenberg one. -/
theorem omegaLD_zero : omegaLD 0 = ω 1 := by
  rw [omegaLD, zero_smul, sub_zero]

/-- `a₋₂|0⟩` has conformal weight `2` (one creation of weight `2` on the weight-`0` vacuum). -/
theorem a2_mem_gradingW_two : osc 1 (-2) (vacuum : Fock) ∈ gradingW 2 := by
  have h := osc_neg_weight 1 (n := -2) (by norm_num) vacuum_mem_gradingW
  have e : (0 + (-(-2 : ℤ)).toNat) = 2 := by decide
  rwa [e] at h

/-- **`conformal_mem`.**  `ω^λ ∈ 𝒱₂`: both `ω` and `a₋₂|0⟩` have weight `2`. -/
theorem omegaLD_mem_gradingZ_two (lam : ℂ) : omegaLD lam ∈ gradingZ 2 := by
  have h2 : osc 1 (-2) (vacuum : Fock) ∈ gradingZ 2 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl]
    exact mem_gradingZ_of_gradingW a2_mem_gradingW_two
  rw [omegaLD]
  exact Submodule.sub_mem _ (omega_mem_gradingZ_two 1) (Submodule.smul_mem _ _ h2)

/-! ## §3  `mode (Y ω^λ) (n+1) = Lld λ n` -/

theorem mode_sub (f g : FormalDist (End ℂ Fock)) (m : ℤ) :
    mode (f - g) m = mode f m - mode g m := rfl

theorem mode_csmul (c : ℂ) (f : FormalDist (End ℂ Fock)) (m : ℤ) :
    mode (c • f) m = c • mode f m := rfl

/-- **The bridge.**  The `(n+1)`-st mode of the deformed conformal vector is exactly the
linear-dilaton Virasoro mode of `Examples/VirasoroFock`:
`ω^λ₍ₙ₊₁₎ = Lₙ + λ(n+1)aₙ = Lld λ n`. -/
theorem mode_Y_omegaLD (lam : ℂ) (n : ℤ) :
    mode (Y 1 (omegaLD lam)) (n + 1) = Lld lam n := by
  rw [omegaLD, map_sub, map_smul, mode_sub, mode_csmul, ← Lvir_eq_mode_Y_omega,
    mode_Y_a2, Lld]
  module

/-! ## §4  The two undeformed modes: `L₀` and `L₋₁` are unchanged -/

/-- **`L₀` is undeformed**: `Lld λ 0 = L₀`, because the zero mode `a₀ = osc 1 0` vanishes on the
zero-momentum Fock space. -/
theorem Lld_zero (lam : ℂ) : Lld lam 0 = Lvir 1 0 := by
  rw [Lld, osc_zero, smul_zero, add_zero]

/-- **`L₋₁` is undeformed**: `Lld λ (-1) = L₋₁`, because the deformation coefficient
`λ(n+1)` vanishes at `n = -1`. -/
theorem Lld_neg_one (lam : ℂ) : Lld lam (-1) = Lvir 1 (-1) := by
  rw [Lld, show (lam * (((-1 : ℤ) : ℂ) + 1)) = 0 from by push_cast; ring, zero_smul, add_zero]

/-- The `L₀`-operator of the deformed VOA equals that of the undeformed one. -/
theorem mode_one_omegaLD (lam : ℂ) :
    mode (Y 1 (omegaLD lam)) 1 = mode (Y 1 (ω 1)) 1 := by
  have h := mode_Y_omegaLD lam 0
  rw [Lld_zero, Lvir_eq_mode_Y_omega 1 0] at h
  rw [show (0 : ℤ) + 1 = 1 from by ring] at h
  exact h

/-- The translation operator `L₋₁` of the deformed VOA equals that of the undeformed one. -/
theorem mode_zero_omegaLD (lam : ℂ) :
    mode (Y 1 (omegaLD lam)) 0 = mode (Y 1 (ω 1)) 0 := by
  have h := mode_Y_omegaLD lam (-1)
  rw [Lld_neg_one, Lvir_eq_mode_Y_omega 1 (-1)] at h
  rw [show (-1 : ℤ) + 1 = 0 from by ring] at h
  exact h

/-! ## §5  The four VOA fields that change (and the two that need the rewrite) -/

/-- **VOA1 for `ω^λ`** in the exact `VertexOperatorAlgebra.virasoro` shape, with
`centralCharge = 1 − 12λ²`.  This is `Lld_virasoro` pushed through the bridge
`mode_Y_omegaLD`. -/
theorem confLD_virasoro (lam : ℂ) (m n : ℤ) :
    ⁅mode (Y 1 (omegaLD lam)) (m + 1), mode (Y 1 (omegaLD lam)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (Y 1 (omegaLD lam)) (m + n + 1)
        + (if m + n = 0 then
              (((m : ℂ) ^ 3 - m) / 12 * (1 - 12 * lam ^ 2)) • (1 : End ℂ Fock)
            else 0) := by
  rw [mode_Y_omegaLD lam m, mode_Y_omegaLD lam n, mode_Y_omegaLD lam (m + n),
    Ring.lie_def, Lld_virasoro,
    show (1 : End ℂ Fock) = (LinearMap.id : End ℂ Fock) from rfl]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
  · rw [if_neg hmn, if_neg hmn, zero_smul]

/-- **VOA2 for `ω^λ`**: `L₀` acts by the conformal weight — the undeformed statement, since
`mode (Y ω^λ) 1 = mode (Y ω) 1`. -/
theorem confLD_L0_grading (lam : ℂ) {n : ℤ} (v : Fock) (hv : v ∈ gradingZ n) :
    mode (Y 1 (omegaLD lam)) 1 v = (n : ℂ) • v := by
  rw [mode_one_omegaLD]
  exact conf_L0_grading 1 one_ne_zero v hv

/-- **VOA3 for `ω^λ`**: `Y(L₋₁v, z) = ∂_z Y(v,z)` — the undeformed statement, since
`mode (Y ω^λ) 0 = mode (Y ω) 0`. -/
theorem confLD_translation (lam : ℂ) (v : Fock) :
    Y 1 (mode (Y 1 (omegaLD lam)) 0 v) = VOA.deriv (Y 1 v) := by
  rw [mode_zero_omegaLD]
  exact conf_translation 1 one_ne_zero v

/-! ## §6  The VOA `freeBosonVOA λ` at central charge `1 − 12λ²` -/

/-- **The free boson at general central charge** (linear-dilaton / Feigin–Fuks / background
charge): the rank-1 Heisenberg vertex algebra on `Fock`, re-graded by the deformed conformal
vector `ω^λ = ω − λ a₋₂|0⟩`.  Central charge `c = 1 − 12λ²`.

Everything except `conformalVector`, `conformal_mem`, `centralCharge` and `virasoro` is the
*same data* as `heisenbergVOA 1 one_ne_zero`: the underlying `PreVertexAlgebra` is literally
`heisVA 1 one_ne_zero`, and VOA2/VOA3 hold because `L₀` and `L₋₁` are undeformed. -/
noncomputable def freeBosonVOA (lam : ℂ) : VertexOperatorAlgebra Fock where
  toPreVertexAlgebra := heisVA 1 one_ne_zero
  conformalVector := omegaLD lam
  conformal_mem := omegaLD_mem_gradingZ_two lam
  centralCharge := 1 - 12 * lam ^ 2
  virasoro := fun m n => confLD_virasoro lam m n
  L0_grading := fun v hv => confLD_L0_grading lam v hv
  translation := fun v => confLD_translation lam v
  vacuum_grade := gradingZ_zero_eq_span_vacuum
  positivity := fun n hn => gradingZ_positivity n hn

/-- **The central charge of the linear-dilaton free boson is `1 − 12λ²`.** -/
theorem freeBosonVOA_centralCharge (lam : ℂ) :
    (freeBosonVOA lam).centralCharge = 1 - 12 * lam ^ 2 := rfl

/-- The conformal vector of `freeBosonVOA λ` is `ω^λ`. -/
theorem freeBosonVOA_conformalVector (lam : ℂ) :
    (freeBosonVOA lam).conformalVector = omegaLD lam := rfl

/-- The underlying vertex algebra is *the* Heisenberg one, untouched by the deformation. -/
theorem freeBosonVOA_toPreVertexAlgebra (lam : ℂ) :
    (freeBosonVOA lam).toPreVertexAlgebra = heisVA 1 one_ne_zero := rfl

/-! ## §7  Sanity checks at `λ = 0`, and the `sl₂`-invariant modes -/

/-- **Sanity 1.**  At `λ = 0` the central charge is the free-boson `c = 1`. -/
theorem freeBosonVOA_zero_centralCharge : (freeBosonVOA 0).centralCharge = 1 := by
  rw [freeBosonVOA_centralCharge]; ring

/-- **Sanity 2.**  At `λ = 0` the conformal vector is the existing Heisenberg one,
`ω 1 = (1/2)a₋₁a₋₁|0⟩`. -/
theorem freeBosonVOA_zero_conformalVector :
    (freeBosonVOA 0).conformalVector = (heisenbergVOA 1 one_ne_zero).conformalVector :=
  omegaLD_zero

/-- **Sanity 3.**  `L₀` is the same operator for every `λ` (the weight grading never moves). -/
theorem freeBosonVOA_L_zero (lam : ℂ) :
    (freeBosonVOA lam).L 0 = (heisenbergVOA 1 one_ne_zero).L 0 := by
  have h := mode_one_omegaLD lam
  rw [show (1 : ℤ) = (0 : ℤ) + 1 from by ring] at h
  exact h

/-- **Sanity 4.**  `L₋₁` is the same operator for every `λ` (translation never moves). -/
theorem freeBosonVOA_L_neg_one (lam : ℂ) :
    (freeBosonVOA lam).L (-1) = (heisenbergVOA 1 one_ne_zero).L (-1) := by
  have h := mode_zero_omegaLD lam
  rw [show (0 : ℤ) = (-1 : ℤ) + 1 from by ring] at h
  exact h

/-! ## §8  Every complex central charge is realized -/

/-- Solving `1 − 12λ² = c`: if `λ² = (1−c)/12` then `freeBosonVOA λ` has central charge `c`. -/
theorem freeBosonVOA_centralCharge_of_sq {lam c : ℂ} (h : lam ^ 2 = (1 - c) / 12) :
    (freeBosonVOA lam).centralCharge = c := by
  rw [freeBosonVOA_centralCharge, h]; ring

/-- **The free boson realizes EVERY complex central charge.**  For each `c ∈ ℂ` pick a square
root `λ` of `(1−c)/12` (available since `ℂ` is algebraically closed); then
`freeBosonVOA λ : VertexOperatorAlgebra Fock` has `centralCharge = c`. -/
theorem exists_centralCharge (c : ℂ) :
    ∃ lam : ℂ, (freeBosonVOA lam).centralCharge = c := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((1 - c) / 12) (n := 2) (by norm_num)
  exact ⟨z, freeBosonVOA_centralCharge_of_sq hz⟩

/-- Restated: the map `λ ↦ centralCharge (freeBosonVOA λ)` is surjective onto `ℂ`. -/
theorem centralCharge_surjective :
    Function.Surjective (fun lam : ℂ => (freeBosonVOA lam).centralCharge) :=
  fun c => exists_centralCharge c

/-! ## §9  Axiom audit

Checked by `#print axioms`: every declaration in this file (in particular
`freeBosonVOA`, `freeBosonVOA_centralCharge`, `confLD_virasoro`, `mode_Y_omegaLD`,
`exists_centralCharge`, `centralCharge_surjective`) depends only on
`[propext, Classical.choice, Quot.sound]` — no `sorry`, no `native_decide`, no new axioms. -/

end VOA.FBgc
