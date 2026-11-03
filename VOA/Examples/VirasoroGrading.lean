/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroConformal
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Set.Finite.List

/-!
# The energy grading of `VirUniv c`

The conformal weight (`L₀`-eigenvalue) of a creation monomial `negWordVir [i₁,…,iₖ]` is its
**energy** `Σ (iⱼ + 2)` (each `L₋ᵢ₋₂` raises the energy by `i+2`).  This file proves the key
straightening identity `L₀ · negWordVir ws = energy(ws) · negWordVir ws` (so each monomial is an
`L₀`-eigenvector), the foundation for the `L₀`-eigenspace grading of the Virasoro VOA.

`sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)

variable (c : ℂ)

/-- The **energy** (conformal weight / `L₀`-eigenvalue) of a creation monomial:
`energyVir [i₁,…,iₖ] = Σ (iⱼ + 2)`. -/
def energyVir : List ℕ → ℕ
  | [] => 0
  | (i :: rest) => (i + 2) + energyVir rest

/-- The empty creation word is the vacuum, so it contributes no conformal weight. -/
@[simp] theorem energyVir_nil : energyVir [] = 0 := rfl

/-- Prefixing the creation mode indexed by i increases the conformal weight by i plus two. Summing these increments gives the energy of the word. -/
theorem energyVir_cons (i : ℕ) (rest : List ℕ) :
    energyVir (i :: rest) = (i + 2) + energyVir rest := rfl

/-- The energy of a nonempty word is at least `2` (every mode is `≤ -2`). -/
theorem energyVir_cons_pos (i : ℕ) (rest : List ℕ) : 0 < energyVir (i :: rest) := by
  rw [energyVir_cons]; omega

/-- The empty word is the unique word of energy `0`. -/
theorem energyVir_eq_zero_iff (ws : List ℕ) : energyVir ws = 0 ↔ ws = [] := by
  cases ws with
  | nil => simp
  | cons i rest =>
      rw [energyVir_cons]
      exact ⟨fun h => absurd h (by omega), fun h => absurd h (by simp)⟩

/-- **The energy straightening identity**: each creation monomial is an `L₀`-eigenvector with
eigenvalue its energy — `L₀ · negWordVir ws = energy(ws) · negWordVir ws`.  Proved by commuting
`L₀` to the right (`[L₀, L₋ᵢ₋₂] = (i+2)·L₋ᵢ₋₂`, no central term since `-i-2 ≠ 0`) where it
annihilates the vacuum. -/
theorem L0_negWord (ws : List ℕ) :
    Lop c 0 (negWordVir c ws) = (energyVir ws : ℂ) • negWordVir c ws := by
  induction ws with
  | nil =>
      rw [negWordVir_nil, energyVir_nil, Nat.cast_zero, zero_smul, Lop_vacuum c (by omega)]
  | cons i rest ih =>
      rw [negWordVir_cons]
      change virVacRho c (L 0) (virVacRho c (L (-(i : ℤ) - 2)) (negWordVir c rest))
          = (energyVir (i :: rest) : ℂ) • virVacRho c (L (-(i : ℤ) - 2)) (negWordVir c rest)
      rw [virVacRho_comm]
      have hfirst : virVacRho c (L (-(i : ℤ) - 2)) (virVacRho c (L 0) (negWordVir c rest))
          = (energyVir rest : ℂ) • virVacRho c (L (-(i : ℤ) - 2)) (negWordVir c rest) := by
        rw [show virVacRho c (L 0) (negWordVir c rest)
            = (energyVir rest : ℂ) • negWordVir c rest from ih, map_smul]
      have hbr : virVacRho c ⁅L 0, L (-(i : ℤ) - 2)⁆ (negWordVir c rest)
          = ((i : ℂ) + 2) • virVacRho c (L (-(i : ℤ) - 2)) (negWordVir c rest) := by
        rw [virasoro_bracket, show ((0 : ℤ) + (-(i : ℤ) - 2)) = -(i : ℤ) - 2 from by ring,
          if_neg (by omega : ¬ -(i : ℤ) - 2 = 0), add_zero, map_smul, LinearMap.smul_apply]
        congr 1; push_cast; ring
      rw [hfirst, hbr, ← add_smul]
      congr 1
      rw [energyVir_cons]; push_cast; ring

/-! ## §2  The energy grading and its `L₀`/vacuum/positivity properties. -/

/-- The **energy grading** `𝒱ₙ = span{ creation monomials of energy n }`. -/
noncomputable def gradingVir (n : ℤ) : Submodule ℂ (VirUniv c) :=
  Submodule.span ℂ {x | ∃ ws : List ℕ, (energyVir ws : ℤ) = n ∧ negWordVir c ws = x}

/-- A creation word belongs to the graded piece indexed by its computed energy, directly from the spanning definition of that piece. -/
theorem negWord_mem_gradingVir (ws : List ℕ) :
    negWordVir c ws ∈ gradingVir c (energyVir ws : ℤ) :=
  Submodule.subset_span ⟨ws, rfl, rfl⟩

/-- **VOA2 core**: `L₀` acts on `𝒱ₙ` as multiplication by `n` (each generator is an `L₀`-eigenvector
of eigenvalue its energy, extended `ℂ`-linearly). -/
theorem L0_grading_gen {n : ℤ} (v : VirUniv c) (hv : v ∈ gradingVir c n) :
    Lop c 0 v = (n : ℂ) • v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨ws, hen, rfl⟩ := hx
      rw [L0_negWord, show ((energyVir ws : ℕ) : ℂ) = (n : ℂ) from by exact_mod_cast hen]
  | zero => rw [map_zero, smul_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, smul_add]
  | smul r a _ ha => rw [map_smul, ha, smul_comm]

/-- **VOA4b (positivity)**: `𝒱ₙ = 0` for `n < 0` (energies are non-negative). -/
theorem gradingVir_neg (n : ℤ) (hn : n < 0) : gradingVir c n = ⊥ := by
  rw [gradingVir, Submodule.span_eq_bot]
  rintro x ⟨ws, hen, rfl⟩
  exact absurd hen (by omega)

/-- **VOA4a (CFT type)**: `𝒱₀ = ℂ·𝟙` (the empty word is the unique energy-`0` monomial). -/
theorem gradingVir_zero : gradingVir c 0 = ℂ ∙ vacVec c := by
  apply le_antisymm
  · rw [gradingVir, Submodule.span_le]
    rintro x ⟨ws, hen, rfl⟩
    have hws : ws = [] := (energyVir_eq_zero_iff ws).mp (by exact_mod_cast hen)
    rw [hws, negWordVir_nil]
    exact Submodule.mem_span_singleton_self _
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨[], by simp, rfl⟩

/-- The vacuum lies in degree `0`. -/
theorem vacVec_mem_gradingVir_zero : vacVec c ∈ gradingVir c 0 := by
  rw [gradingVir_zero]; exact Submodule.mem_span_singleton_self _

/-- **`ω ∈ 𝒱₂`** (`conformal_mem`): `ω = negWordVir [0]` has energy `2`. -/
theorem omegaVir_mem_gradingVir_two : omegaVir c ∈ gradingVir c 2 := by
  have h := negWord_mem_gradingVir c [0]
  rw [show (energyVir [0] : ℤ) = 2 from rfl] at h
  exact h

/-! ## §3  The grading is an internal direct sum (`isInternal`), `pbw`-free. -/

/-- Each graded piece lies in the corresponding `L₀`-eigenspace. -/
theorem gradingVir_le_eigenspace (n : ℤ) :
    gradingVir c n ≤ Module.End.eigenspace (Lop c 0) (n : ℂ) := fun _ hv =>
  Module.End.mem_eigenspace_iff.mpr (L0_grading_gen c _ hv)

/-- The graded pieces span the whole module (from the creation-monomial spanning). -/
theorem iSup_gradingVir : ⨆ n : ℤ, gradingVir c n = ⊤ := by
  rw [eq_top_iff, ← negSpanVir_eq_top c, negSpanVir, Submodule.span_le]
  rintro _ ⟨ws, rfl⟩
  exact Submodule.mem_iSup_of_mem (energyVir ws : ℤ) (negWord_mem_gradingVir c ws)

/-- **The energy grading is an internal direct sum** (`isInternal`): the graded pieces are
independent (they sit inside the independent `L₀`-eigenspaces, indexed injectively by `ℤ ↪ ℂ`) and
span.  **`pbw`-free** — no PBW basis needed (the affine analogue used `pbw`). -/
theorem gradingVir_isInternal : DirectSum.IsInternal (gradingVir c) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, iSup_gradingVir c⟩
  have hindep : iSupIndep (fun n : ℤ => Module.End.eigenspace (Lop c 0) (n : ℂ)) :=
    (Module.End.eigenspaces_iSupIndep (Lop c 0)).comp (fun a b h => by exact_mod_cast h)
  exact hindep.mono (fun n => gradingVir_le_eigenspace c n)

/-! ## §4  Each graded piece is finite-dimensional (`finrank`): finitely many words per energy. -/

/-- Every word of energy `m` has length `≤ m` (each entry contributes `≥ 2`). -/
theorem two_mul_length_le_energy (ws : List ℕ) : 2 * ws.length ≤ energyVir ws := by
  induction ws with
  | nil => simp
  | cons i rest ih => rw [energyVir_cons, List.length_cons]; omega

/-- Every entry of a word is `< energy + 1` (each entry `iⱼ ≤ energy − 2`). -/
theorem mem_lt_energy_succ (ws : List ℕ) : ∀ x ∈ ws, x < energyVir ws + 1 := by
  induction ws with
  | nil => simp
  | cons i rest ih =>
      intro x hx
      rw [energyVir_cons]
      rcases List.mem_cons.mp hx with h | h
      · omega
      · have := ih x h; omega

/-- **Finitely many words of a given energy** (bounded length + bounded entries): inject into
`List (Fin (m+1))`, whose length-`≤ m` sublists are finite. -/
theorem finite_energyEq (m : ℕ) : {ws : List ℕ | energyVir ws = m}.Finite := by
  set f : List ℕ → List (Fin (m + 1)) := fun ws => ws.map (fun i => ⟨min i m, by omega⟩) with hf
  have recover : ∀ ws ∈ {ws : List ℕ | energyVir ws = m}, (f ws).map Fin.val = ws := by
    intro ws hws
    simp only [Set.mem_setOf_eq] at hws
    rw [hf, List.map_map]
    conv_rhs => rw [← List.map_id ws]
    apply List.map_congr_left
    intro x hx
    have : x < m + 1 := hws ▸ mem_lt_energy_succ ws x hx
    simp only [Function.comp_apply, id_eq]; omega
  apply Set.Finite.of_finite_image (f := f)
  · apply Set.Finite.subset (List.finite_length_le (Fin (m + 1)) (n := m))
    rintro _ ⟨ws, hws, rfl⟩
    simp only [Set.mem_setOf_eq] at hws
    change (f ws).length ≤ m
    simp only [hf, List.length_map]
    have := two_mul_length_le_energy ws; omega
  · intro ws1 h1 ws2 h2 heq
    rw [← recover ws1 h1, ← recover ws2 h2, heq]

/-- **`finrank`**: each graded piece `𝒱ₙ` is finite-dimensional (finitely many creation monomials
of energy `n`). -/
theorem gradingVir_finiteDimensional (n : ℤ) : FiniteDimensional ℂ (gradingVir c n) := by
  rw [gradingVir]
  apply FiniteDimensional.span_of_finite
  rcases lt_or_ge n 0 with hn | hn
  · convert Set.finite_empty
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    rintro ws ⟨hen, -⟩; omega
  · apply Set.Finite.subset ((finite_energyEq n.toNat).image (negWordVir c))
    rintro x ⟨ws, hen, rfl⟩
    exact ⟨ws, by simp only [Set.mem_setOf_eq]; omega, rfl⟩

end VOA.VirModule
