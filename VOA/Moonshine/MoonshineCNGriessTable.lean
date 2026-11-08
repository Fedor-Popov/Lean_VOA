/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MonsterGriess.AutO

/-!
# The block multiplication table of the rational Griess algebra `SpaceB`

`SpaceB = symMat × SpaceX × SpaceW` (the port of AxiomMath's rational Griess algebra,
`VOA/Moonshine/MonsterGriess/Algebra.lean`) has three blocks:

* `symBlock A = (A, 0, 0)` — symmetric `24 × 24` matrices (the image of `S²𝔥`);
* `shortBlock x = (0, x, 0)` — functions on the `98280` short classes (the `e^α + e^{−α}` part);
* `spinBlock N = (0, 0, N)` — `SpinIdx × 24` matrices (the twisted part `h(−½) ⊗ T`).

This file evaluates the product `gmul` and the form `bform` on every pair of blocks, by unfolding
the definitions `gmulA`, `gmulX`, `gmulWHalf`.  These are the formulas the explicit isomorphism
with the weight-two space of `V♮` has to match block by block.

## Main results
* `spaceB_eq_blocks` — every element is the sum of its three block parts.
* product table, stated componentwise (`.1`: the `symMat` part, `.2.1`: `SpaceX`, `.2.2`: `SpaceW`):
  - `gmul_symBlock_symBlock_fst/_snd` — `A·B = 2(AB + BA)`;
  - `gmul_symBlock_shortBlock_*`, `gmul_shortBlock_symBlock_*` — `A·x = (qf c A / 8)·x_c`;
  - `gmul_shortBlock_shortBlock_*` — `x·y = (⅛ Σ_c x_c y_c U_c, Σ_{d,e} x_d y_e τ(d,e,c), 0)`;
  - `gmul_symBlock_spinBlock_*`, `gmul_spinBlock_symBlock_*` — `A·N = (tr A / 8) N + N A`;
  - `gmul_shortBlock_spinBlock_*`, `gmul_spinBlock_shortBlock_*` —
    `x·N = ⅛ Σ_c x_c (R_c N − ¼ R_c N U_c)`;
  - `gmul_spinBlock_spinBlock_*` — `N·M = ((tr NᵀM / 8) 1 + ½(NᵀM + MᵀN),
    c ↦ (tr(Nᵀ R_c M) − qf c (Nᵀ R_c M)/4)/8, 0)`.
* form table: `bform_symBlock_symBlock` (`tr(AB)`), `bform_shortBlock_shortBlock` (`Σ x_c y_c`),
  `bform_spinBlock_spinBlock` (`Σ N_{ji} M_{ji}`), and the vanishing of the mixed pairings.

## Status
No hypotheses; every statement is an unfolding of the ported definitions.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.MonsterGriess

open Matrix

/-- The `symMat` block `(A, 0, 0)` of `SpaceB`. -/
def symBlock (A : symMat) : SpaceB := (A, 0, 0)

/-- The short-class block `(0, x, 0)` of `SpaceB`. -/
def shortBlock (x : SpaceX) : SpaceB := (0, x, 0)

/-- The spin block `(0, 0, N)` of `SpaceB`. -/
def spinBlock (N : SpaceW) : SpaceB := (0, 0, N)

/-- Every element of `SpaceB` is the sum of its three block parts. -/
theorem spaceB_eq_blocks (u : SpaceB) : u = symBlock u.1 + shortBlock u.2.1 + spinBlock u.2.2 := by
  obtain ⟨A, x, N⟩ := u
  simp [symBlock, shortBlock, spinBlock]

@[simp] theorem Am_symBlock (A : symMat) : Am (symBlock A) = (A : Matrix (Fin 24) (Fin 24) ℚ) := rfl
@[simp] theorem xs_symBlock (A : symMat) : xs (symBlock A) = 0 := rfl
@[simp] theorem Nm_symBlock (A : symMat) : Nm (symBlock A) = 0 := rfl
@[simp] theorem Am_shortBlock (x : SpaceX) : Am (shortBlock x) = 0 := rfl
@[simp] theorem xs_shortBlock (x : SpaceX) : xs (shortBlock x) = x := rfl
@[simp] theorem Nm_shortBlock (x : SpaceX) : Nm (shortBlock x) = 0 := rfl
@[simp] theorem Am_spinBlock (N : SpaceW) : Am (spinBlock N) = 0 := rfl
@[simp] theorem xs_spinBlock (N : SpaceW) : xs (spinBlock N) = 0 := rfl
@[simp] theorem Nm_spinBlock (N : SpaceW) : Nm (spinBlock N) = N := rfl

@[simp] theorem qf_zero (c : ShortIdx) : qf c 0 = 0 := by
  simp [qf]

theorem gmul_fst (u v : SpaceB) :
    ((gmul u v).1 : Matrix (Fin 24) (Fin 24) ℚ) = gmulA u v := rfl

theorem gmul_snd_fst (u v : SpaceB) : (gmul u v).2.1 = gmulX u v := rfl

theorem gmul_snd_snd (u v : SpaceB) : (gmul u v).2.2 = gmulW u v := rfl

/-! ## The `symMat · symMat` channel -/

theorem gmul_symBlock_symBlock_fst (A B : symMat) :
    ((gmul (symBlock A) (symBlock B)).1 : Matrix (Fin 24) (Fin 24) ℚ)
      = (2 : ℚ) • ((A : Matrix (Fin 24) (Fin 24) ℚ) * B + (B : Matrix (Fin 24) (Fin 24) ℚ) * A) := by
  rw [gmul_fst]
  simp [gmulA]

theorem gmul_symBlock_symBlock_snd (A B : symMat) : (gmul (symBlock A) (symBlock B)).2 = 0 := by
  refine Prod.ext ?_ ?_
  · funext c
    rw [gmul_snd_fst]
    simp [gmulX]
  · rw [gmul_snd_snd]
    simp [gmulW, gmulWHalf]

/-! ## The `symMat · SpaceX` channels -/

theorem gmul_symBlock_shortBlock_fst (A : symMat) (x : SpaceX) :
    ((gmul (symBlock A) (shortBlock x)).1 : Matrix (Fin 24) (Fin 24) ℚ) = 0 := by
  rw [gmul_fst]
  simp [gmulA]

theorem gmul_symBlock_shortBlock_snd_fst (A : symMat) (x : SpaceX) :
    (gmul (symBlock A) (shortBlock x)).2.1 = fun c => x c * qf c A / 8 := by
  funext c
  rw [gmul_snd_fst]
  simp [gmulX]

theorem gmul_symBlock_shortBlock_snd_snd (A : symMat) (x : SpaceX) :
    (gmul (symBlock A) (shortBlock x)).2.2 = 0 := by
  rw [gmul_snd_snd]
  simp [gmulW, gmulWHalf]

theorem gmul_shortBlock_symBlock_fst (x : SpaceX) (A : symMat) :
    ((gmul (shortBlock x) (symBlock A)).1 : Matrix (Fin 24) (Fin 24) ℚ) = 0 := by
  rw [gmul_fst]
  simp [gmulA]

theorem gmul_shortBlock_symBlock_snd_fst (x : SpaceX) (A : symMat) :
    (gmul (shortBlock x) (symBlock A)).2.1 = fun c => x c * qf c A / 8 := by
  funext c
  rw [gmul_snd_fst]
  simp [gmulX]

theorem gmul_shortBlock_symBlock_snd_snd (x : SpaceX) (A : symMat) :
    (gmul (shortBlock x) (symBlock A)).2.2 = 0 := by
  rw [gmul_snd_snd]
  simp [gmulW, gmulWHalf]

/-! ## The `SpaceX · SpaceX` channel -/

theorem gmul_shortBlock_shortBlock_fst (x y : SpaceX) :
    ((gmul (shortBlock x) (shortBlock y)).1 : Matrix (Fin 24) (Fin 24) ℚ)
      = (8 : ℚ)⁻¹ • ∑ c, (x c * y c) • Umat c := by
  rw [gmul_fst]
  simp [gmulA]

theorem gmul_shortBlock_shortBlock_snd_fst (x y : SpaceX) :
    (gmul (shortBlock x) (shortBlock y)).2.1 = fun c => ∑ d, ∑ e, x d * y e * tau d e c := by
  funext c
  rw [gmul_snd_fst]
  simp [gmulX]

theorem gmul_shortBlock_shortBlock_snd_snd (x y : SpaceX) :
    (gmul (shortBlock x) (shortBlock y)).2.2 = 0 := by
  rw [gmul_snd_snd]
  simp [gmulW, gmulWHalf]

/-! ## The `symMat · SpaceW` channels -/

theorem gmul_symBlock_spinBlock_fst (A : symMat) (N : SpaceW) :
    ((gmul (symBlock A) (spinBlock N)).1 : Matrix (Fin 24) (Fin 24) ℚ) = 0 := by
  rw [gmul_fst]
  simp [gmulA]

theorem gmul_symBlock_spinBlock_snd_fst (A : symMat) (N : SpaceW) :
    (gmul (symBlock A) (spinBlock N)).2.1 = 0 := by
  funext c
  rw [gmul_snd_fst]
  simp [gmulX]

theorem gmul_symBlock_spinBlock_snd_snd (A : symMat) (N : SpaceW) :
    (gmul (symBlock A) (spinBlock N)).2.2
      = (trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8) • N + N * (A : Matrix (Fin 24) (Fin 24) ℚ) := by
  rw [gmul_snd_snd]
  simp [gmulW, gmulWHalf]

theorem gmul_spinBlock_symBlock_fst (N : SpaceW) (A : symMat) :
    ((gmul (spinBlock N) (symBlock A)).1 : Matrix (Fin 24) (Fin 24) ℚ) = 0 := by
  rw [gmul_fst]
  simp [gmulA]

theorem gmul_spinBlock_symBlock_snd_fst (N : SpaceW) (A : symMat) :
    (gmul (spinBlock N) (symBlock A)).2.1 = 0 := by
  funext c
  rw [gmul_snd_fst]
  simp [gmulX]

theorem gmul_spinBlock_symBlock_snd_snd (N : SpaceW) (A : symMat) :
    (gmul (spinBlock N) (symBlock A)).2.2
      = (trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8) • N + N * (A : Matrix (Fin 24) (Fin 24) ℚ) := by
  rw [gmul_snd_snd]
  simp [gmulW, gmulWHalf]

/-! ## The `SpaceX · SpaceW` channels -/

theorem gmul_shortBlock_spinBlock_fst (x : SpaceX) (N : SpaceW) :
    ((gmul (shortBlock x) (spinBlock N)).1 : Matrix (Fin 24) (Fin 24) ℚ) = 0 := by
  rw [gmul_fst]
  simp [gmulA]

theorem gmul_shortBlock_spinBlock_snd_fst (x : SpaceX) (N : SpaceW) :
    (gmul (shortBlock x) (spinBlock N)).2.1 = 0 := by
  funext c
  rw [gmul_snd_fst]
  simp [gmulX]

theorem gmul_shortBlock_spinBlock_snd_snd (x : SpaceX) (N : SpaceW) :
    (gmul (shortBlock x) (spinBlock N)).2.2
      = (8 : ℚ)⁻¹ • ∑ c, x c • (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c)) := by
  rw [gmul_snd_snd]
  simp [gmulW, gmulWHalf]

theorem gmul_spinBlock_shortBlock_fst (N : SpaceW) (x : SpaceX) :
    ((gmul (spinBlock N) (shortBlock x)).1 : Matrix (Fin 24) (Fin 24) ℚ) = 0 := by
  rw [gmul_fst]
  simp [gmulA]

theorem gmul_spinBlock_shortBlock_snd_fst (N : SpaceW) (x : SpaceX) :
    (gmul (spinBlock N) (shortBlock x)).2.1 = 0 := by
  funext c
  rw [gmul_snd_fst]
  simp [gmulX]

theorem gmul_spinBlock_shortBlock_snd_snd (N : SpaceW) (x : SpaceX) :
    (gmul (spinBlock N) (shortBlock x)).2.2
      = (8 : ℚ)⁻¹ • ∑ c, x c • (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c)) := by
  rw [gmul_snd_snd]
  simp [gmulW, gmulWHalf]

/-! ## The `SpaceW · SpaceW` channel -/

theorem gmul_spinBlock_spinBlock_fst (N M : SpaceW) :
    ((gmul (spinBlock N) (spinBlock M)).1 : Matrix (Fin 24) (Fin 24) ℚ)
      = (trace (Nᵀ * M) / 8) • (1 : Matrix (Fin 24) (Fin 24) ℚ) + (2 : ℚ)⁻¹ • (Nᵀ * M + Mᵀ * N) := by
  rw [gmul_fst]
  simp [gmulA]

theorem gmul_spinBlock_spinBlock_snd_fst (N M : SpaceW) :
    (gmul (spinBlock N) (spinBlock M)).2.1
      = fun c => (trace (Nᵀ * Rmat c * M) - qf c (Nᵀ * Rmat c * M) / 4) / 8 := by
  funext c
  rw [gmul_snd_fst]
  simp [gmulX]

theorem gmul_spinBlock_spinBlock_snd_snd (N M : SpaceW) :
    (gmul (spinBlock N) (spinBlock M)).2.2 = 0 := by
  rw [gmul_snd_snd]
  simp [gmulW, gmulWHalf]

/-! ## The form on blocks -/

theorem bform_symBlock_symBlock (A B : symMat) :
    bform (symBlock A) (symBlock B)
      = trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ)) := by
  simp [bform_apply, symBlock]

theorem bform_shortBlock_shortBlock (x y : SpaceX) :
    bform (shortBlock x) (shortBlock y) = ∑ c, x c * y c := by
  simp [bform_apply, shortBlock]

theorem bform_spinBlock_spinBlock (N M : SpaceW) :
    bform (spinBlock N) (spinBlock M) = ∑ j, ∑ i, N j i * M j i := by
  simp [bform_apply, spinBlock]

theorem bform_symBlock_shortBlock (A : symMat) (x : SpaceX) :
    bform (symBlock A) (shortBlock x) = 0 := by
  simp [bform_apply, symBlock, shortBlock]

theorem bform_shortBlock_symBlock (x : SpaceX) (A : symMat) :
    bform (shortBlock x) (symBlock A) = 0 := by
  simp [bform_apply, symBlock, shortBlock]

theorem bform_symBlock_spinBlock (A : symMat) (N : SpaceW) :
    bform (symBlock A) (spinBlock N) = 0 := by
  simp [bform_apply, symBlock, spinBlock]

theorem bform_spinBlock_symBlock (N : SpaceW) (A : symMat) :
    bform (spinBlock N) (symBlock A) = 0 := by
  simp [bform_apply, symBlock, spinBlock]

theorem bform_shortBlock_spinBlock (x : SpaceX) (N : SpaceW) :
    bform (shortBlock x) (spinBlock N) = 0 := by
  simp [bform_apply, shortBlock, spinBlock]

theorem bform_spinBlock_shortBlock (N : SpaceW) (x : SpaceX) :
    bform (spinBlock N) (shortBlock x) = 0 := by
  simp [bform_apply, shortBlock, spinBlock]

end VOA.Moonshine.MonsterGriess
