/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCarrierData
import VOA.DeligneAudit.A2SectorRep

/-!
# Type data for the Deligne sector chain

The sector side (B2–B8) needs, beyond the carrier data `DeligneCarrierData` (`n`, `I₂ⁿˢ`, `Q`, U3):

* the structure constants `f` of `g` in the basis of the currents, with the Jacobi identity;
* **ad-stability of `I₂ = I₂ⁿˢ ⊕ ℂQ`** (B5);
* the coadjoint highest vector `δ_{c₀}` (`c₀` dual to the lowest root vector `f_θ`), with
  `c₀² ∉ I₂` (no relation has a `(c₀,c₀)` entry);
* the local Weyl data of `W_loc(mθ)`: raising basis vectors (killing `δ_{c₀}`), Cartan basis
  vectors with `θ(h) ∈ ℕ` (acting on `δ_{c₀}` by `θ(h)`), the simple lowering vectors with their
  exponents `θ(h_i)`, the fusion set, and a weight function with the combinatorial fact that makes
  `(f_i ⊗ 1)^{mθ(h_i)+1}` vanish on `δ_{c₀}^{⊗m}`;
* **coadjoint cyclicity in bounded depth**: every basis vector of `g*` is a combination of words of
  length `≤ L` in the coadjoint operators applied to `δ_{c₀}` (`L = 3` for A₂).
-/

namespace VOA.DeligneAudit.DeligneSector

open MvPolynomial VOA.DeligneAudit.DeligneCarrier VOA.DeligneAudit.SectorLoop

noncomputable section

/-- The coadjoint operator of `x` on `g*` (functions `Fin n → ℂ`). -/
def slotA {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (x : Fin n) (v : Fin n → ℂ) : Fin n → ℂ :=
  fun y => -∑ d, f x y d * v d

/-- A word of coadjoint operators. -/
def wordA {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) : List (Fin n) → (Fin n → ℂ) → (Fin n → ℂ)
  | [], v => v
  | (x :: l), v => slotA f x (wordA f l v)

/-- The span of the coadjoint words of length `≤ L` applied to `δ_{c₀}`. -/
def slotWords {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (c₀ : Fin n) (L : ℕ) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ {v | ∃ l : List (Fin n), l.length ≤ L ∧ v = wordA f l (Pi.single c₀ 1)}

/-- **Type data for the Deligne sector chain.** -/
structure DeligneSectorData extends DeligneCarrierData where
  /-- Finitely many relations. -/
  ρFin : Fintype ρ
  /-- Structure constants: `[x_a, x_b] = Σ_c f a b c x_c`. -/
  f : Fin n → Fin n → Fin n → ℂ
  jacobi : JacobiCoord f
  /-- **B5 input**: `I₂ = I₂ⁿˢ ⊕ ℂQ` is `ad`-stable. -/
  stable : RelationsStable f toDeligneCarrierData.fullMatrix
  /-- The coadjoint highest vector `δ_{c₀}`. -/
  c₀ : Fin n
  diag : ∀ r, toDeligneCarrierData.fullMatrix r (c₀, c₀) = 0
  /-- Raising basis vectors. -/
  raising : Fin n → Prop
  raising_table : ∀ e, raising e → ∀ y, f e y c₀ = 0
  /-- Cartan basis vectors and `θ(h)`. -/
  cartan : Fin n → Prop
  thetaH : Fin n → ℕ
  cartan_table : ∀ h, cartan h → ∀ y, f h y c₀ = if y = c₀ then -(thetaH h : ℂ) else 0
  /-- A Cartan vector with `θ(h) ≠ 0` (power sums act through it). -/
  hθ : Fin n
  hθ_cartan : cartan hθ
  hθ_ne : thetaH hθ ≠ 0
  /-- Simple lowering vectors and their exponents `θ(h_i)`. -/
  lowering : Fin n → Prop
  lowExp : Fin n → ℕ
  /-- Weights (in any lattice `Fin R → ℤ`). -/
  R : ℕ
  wt : Fin n → Fin R → ℤ
  table_wt : ∀ x y c, wt c ≠ wt x + wt y → f x y c = 0
  lowering_noweight : ∀ i, lowering i → ∀ (m : ℕ) (t : Fin m → Fin n),
    ∑ j, wt (t j) ≠ m • wt c₀ - (m * lowExp i + 1) • wt i
  /-- The fusion set `{f_α : (θ,α) = 1 or α = θ}`. -/
  fusion : Fin n → Prop
  /-- **Coadjoint cyclicity in depth `L`.** -/
  depth : ℕ
  cyclic : ∀ c, (Pi.single c 1 : Fin n → ℂ) ∈ slotWords f c₀ depth
  /-- Cartan basis vectors with `θ(h) = -thetaN h ≤ 0` (non-simply-laced bases; empty by default). -/
  cartanN : Fin n → Prop := fun _ => False
  thetaN : Fin n → ℕ := fun _ => 0
  cartanN_table : ∀ h, cartanN h → ∀ y, f h y c₀ = if y = c₀ then (thetaN h : ℂ) else 0 := by
    intro h hh; exact False.elim hh

attribute [instance] DeligneSectorData.ρFin

end

end VOA.DeligneAudit.DeligneSector
