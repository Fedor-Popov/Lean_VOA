/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorGraded
import VOA.Examples.AffineSl3BracketTable
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Current-algebra modules and the fusion-module bound (input U5)

A `CurrentModule f V` is a representation of the current algebra `g[t]` with structure constants
`f`: operators `x ⊗ t^r` satisfying `[x ⊗ t^r, y ⊗ t^s] = Σ_e f(x,y,e) e ⊗ t^{r+s}`.  For a vector
`w`, `cycDeg ρ w b` is the span of the loop words of `t`-degree `b` applied to `w`.

For `sl₃` (`AffineSl3.bracketTable`, basis `e₁,e₂,e₁₂,f₁,f₂,f₁₂,h₁,h₂`), `LocalWeylRel ρ w m` are
the defining relations of the local Weyl module `W_loc(mθ)` (θ the highest root, `θ(h₁)=θ(h₂)=1`)
together with the fusion relations `(f_α ⊗ t^m) w = 0` for the positive roots `α` (all satisfy
`(θ,α) = 1` or `α = θ`).

**Input U5 in its smallest form, `FusionModuleBound F`**: every such module has `t`-graded
dimension at most `[q^b] F_m`.  Since every module satisfying the relations is a graded quotient
of `W_loc(mθ)/⟨(f_α ⊗ t^m) w⟩`, this is exactly Ravinder Prop. 1 + Prop. 5 (Feigin) with `F_m` the
graded character of that module (`f_m` in the audit's ledger).  U4 (Chari–Fourier–Khandai) is not
needed for this bound.
-/

namespace VOA.DeligneAudit.SectorWeyl

open VOA.DeligneAudit.SectorGraded

noncomputable section

variable {K σ : Type*} [Field K] (f : σ → σ → σ → K)

/-- A representation of the current algebra with structure constants `f` (finite sums over `σ`). -/
structure CurrentModule [Fintype σ] (V : Type*) [AddCommGroup V] [Module K V] where
  op : σ → ℕ → V →ₗ[K] V
  comm : ∀ a b r s v, op a r (op b s v) - op b s (op a r v) = ∑ e, f a b e • op e (r + s) v

variable {f} [Fintype σ] {V : Type*} [AddCommGroup V] [Module K V]

/-- A loop word applied to a vector. -/
def wordOp (ρ : CurrentModule f V) : List (σ × ℕ) → V → V
  | [], v => v
  | (xs :: l), v => ρ.op xs.1 xs.2 (wordOp ρ l v)

/-- The span of the loop words of `t`-degree `b` applied to `w`. -/
def cycDeg (ρ : CurrentModule f V) (w : V) (b : ℕ) : Submodule K V :=
  Submodule.span K {v | ∃ l, SectorGraded.wordDeg l = b ∧ v = wordOp ρ l w}

end

/-! ## The `sl₃` local Weyl relations and input U5 -/

open VOA.AffineSl3 PowerSeries

/-- The local Weyl relations for `W_loc(mθ)` of `sl₃`, with the fusion relations
`(f_α ⊗ t^m) w = 0`. -/
structure LocalWeylRel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule (bracketTable) V) (w : V) (m : ℕ) : Prop where
  raising : ∀ (e : Fin 8), e.val < 3 → ∀ r, ρ.op e r w = 0
  cartan_pos : ∀ (h : Fin 8), 6 ≤ h.val → ∀ r, 1 ≤ r → ρ.op h r w = 0
  cartan_zero : ∀ (h : Fin 8), 6 ≤ h.val → ρ.op h 0 w = (m : ℂ) • w
  lowering_f1 : (ρ.op 3 0)^[m + 1] w = 0
  lowering_f2 : (ρ.op 4 0)^[m + 1] w = 0
  fusion : ∀ (fα : Fin 8), 3 ≤ fα.val → fα.val < 6 → ρ.op fα m w = 0

/-- **Input U5 (smallest form)**: every graded cyclic `sl₃[t]`-module on a vector satisfying the
local Weyl and fusion relations for `mθ` has `t`-graded dimension at most `[q^b] F_m`. -/
structure FusionModuleBound (F : ℕ → PowerSeries ℚ) : Prop where
  le : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V)
    (w : V), LocalWeylRel ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (F m)
  /-- The total-dimension form of U5 (Ravinder Prop. 1): `dim W_loc(mθ)/⟨(f_α ⊗ t^m) w⟩ ≤ 8^m`,
  read on the `t`-graded pieces of any module satisfying the relations. -/
  total : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V)
    (w : V), LocalWeylRel ρ w m → ∀ B : ℕ,
      ∑ b ∈ Finset.range B, Module.finrank ℂ (cycDeg ρ w b) ≤ 8 ^ m

end VOA.DeligneAudit.SectorWeyl
