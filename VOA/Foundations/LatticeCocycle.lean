/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Foundations.Lattices
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The FLM 2-cocycle of an even lattice  (FLM Ch. 8; Gannon §5.2.2)

For a general even lattice `L` the vertex operators `Y(e^α)` do NOT commute on the nose — the
lattice group algebra `ℂ{L}` (`Foundations.Lattices.latticeAlgebra`, the untwisted
`eᵘ·eᵛ = e^{u+v}`) must be **twisted by a 2-cocycle** `ε : L × L → ℂ_ε{L}` with
`eᵅ·eᵝ = ε(α,β) e^{α+β}`, so that `Y(e^α), Y(e^β)` are mutually local (Frenkel–Lepowsky–Meurman
Ch. 8).  The `A₁` case never needed this: there every pairing `⟨mα,nα⟩ = 2mn` is *even*, so the
cocycle sign `(−1)^{⟨α,β⟩} = 1` is trivial.

This file constructs the FLM cocycle for an **arbitrary** integral lattice, keyed to a chosen
`ℤ`-basis `B` (`Fin n → L`), via the **upper-triangular Gram exponent**
`coc(α,β) = ∑_{j < i} ⟨Bᵢ,Bⱼ⟩ αᵢ βⱼ` (`cocExp`) and `ε(α,β) = (−1)^{coc(α,β)}` (`cocycle`).

The two structural properties FLM need:

* **`cocycle_cocycleLaw`** — the **2-cocycle law** `ε(α,β)·ε(α+β,γ) = ε(β,γ)·ε(α,β+γ)`.  Holds for
  *any* `ℤ`-bilinear exponent (`cocExp` is bi-additive, `cocExp_add_left`/`cocExp_add_right`), so
  the twisted product `eᵅ·eᵝ = ε(α,β) e^{α+β}` is **associative**.
* **`cocycle_comm`** — the **commutator property** `ε(α,β)·ε(β,α) = (−1)^{⟨α,β⟩}` (equivalently
  `ε(α,β)/ε(β,α) = (−1)^{⟨α,β⟩}` since `ε = ±1`).  This is what makes `Y(e^α),Y(e^β)`
  (anti)commute into locality for *odd* `⟨α,β⟩`.  Its proof uses **evenness** exactly on the
  diagonal `⟨Bᵢ,Bᵢ⟩`, which is where `L.Even` enters.

Plus the normalisation `cocycle_zero_left`/`cocycle_zero_right` (`ε(0,·) = ε(·,0) = 1`) and the
sign fact `cocycle_sq` (`ε(α,β)² = 1`).

## References
* Frenkel–Lepowsky–Meurman, *Vertex Operator Algebras and the Monster*, Ch. 8; Gannon §5.2.2.
-/

namespace VOA.IntegralLattice

open scoped BigOperators
open Module

variable (L : IntegralLattice) {n : ℕ} (B : Basis (Fin n) ℤ L.carrier)

/-! ## The upper-triangular Gram exponent `coc` -/

/-- The **cocycle exponent** `coc(α,β) = ∑_{j < i} ⟨Bᵢ,Bⱼ⟩ αᵢ βⱼ` — the upper-triangular part of
the Gram matrix in the basis `B`, evaluated on the coordinates of `α, β`. -/
noncomputable def cocExp (α β : L.carrier) : ℤ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (if j < i then L.form (B i) (B j) else 0) * B.repr α i * B.repr β j

/-- `coc` is additive in the first slot. -/
theorem cocExp_add_left (α α' β : L.carrier) :
    cocExp L B (α + α') β = cocExp L B α β + cocExp L B α' β := by
  simp only [cocExp, map_add, Finsupp.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- `coc` is additive in the second slot. -/
theorem cocExp_add_right (α β β' : L.carrier) :
    cocExp L B α (β + β') = cocExp L B α β + cocExp L B α β' := by
  simp only [cocExp, map_add, Finsupp.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- `coc(0, β) = 0`. -/
theorem cocExp_zero_left (β : L.carrier) : cocExp L B 0 β = 0 := by
  simp only [cocExp, map_zero, Finsupp.coe_zero, Pi.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero]

/-- `coc(α, 0) = 0`. -/
theorem cocExp_zero_right (α : L.carrier) : cocExp L B α 0 = 0 := by
  simp only [cocExp, map_zero, Finsupp.coe_zero, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero]

/-! ## Symmetry helper and the basis expansion of the Gram form -/

/-- The Gram form is symmetric: `⟨x,y⟩ = ⟨y,x⟩`. -/
theorem form_symm (x y : L.carrier) : L.form x y = L.form y x := by
  have h : L.form.IsSymm := L.isSymm
  rw [LinearMap.BilinForm.isSymm_def] at h
  exact h x y

/-- The Gram form in coordinates: `⟨α,β⟩ = ∑ᵢ ∑ⱼ αᵢ βⱼ ⟨Bᵢ,Bⱼ⟩`. -/
theorem form_eq_sum_repr (α β : L.carrier) :
    L.form α β = ∑ i : Fin n, ∑ j : Fin n, B.repr α i * B.repr β j * L.form (B i) (B j) := by
  conv_lhs => rw [← B.sum_repr α]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, LinearMap.smul_apply]
  conv_lhs => rw [← B.sum_repr β]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-! ## The cocycle `ε(α,β) = (−1)^{coc(α,β)}` -/

/-- The **FLM 2-cocycle** `ε(α,β) = (−1)^{coc(α,β)} ∈ ℂ`. -/
noncomputable def cocycle (α β : L.carrier) : ℂ := (-1 : ℂ) ^ (cocExp L B α β)

theorem cocycle_neg_one_ne : (-1 : ℂ) ≠ 0 := by norm_num

/-- Multiplicativity in the first slot: `ε(α+α',β) = ε(α,β)·ε(α',β)`. -/
theorem cocycle_add_left (α α' β : L.carrier) :
    cocycle L B (α + α') β = cocycle L B α β * cocycle L B α' β := by
  simp only [cocycle, cocExp_add_left]
  rw [zpow_add₀ cocycle_neg_one_ne]

/-- Multiplicativity in the second slot: `ε(α,β+β') = ε(α,β)·ε(α,β')`. -/
theorem cocycle_add_right (α β β' : L.carrier) :
    cocycle L B α (β + β') = cocycle L B α β * cocycle L B α β' := by
  simp only [cocycle, cocExp_add_right]
  rw [zpow_add₀ cocycle_neg_one_ne]

/-- Normalisation: `ε(0,β) = 1`. -/
theorem cocycle_zero_left (β : L.carrier) : cocycle L B 0 β = 1 := by
  simp only [cocycle, cocExp_zero_left, zpow_zero]

/-- Normalisation: `ε(α,0) = 1`. -/
theorem cocycle_zero_right (α : L.carrier) : cocycle L B α 0 = 1 := by
  simp only [cocycle, cocExp_zero_right, zpow_zero]

/-- `ε(α,β)` is a sign: `ε(α,β)² = 1`. -/
theorem cocycle_sq (α β : L.carrier) : cocycle L B α β * cocycle L B α β = 1 := by
  simp only [cocycle]
  rw [← zpow_add₀ cocycle_neg_one_ne, ← two_mul, zpow_mul]
  norm_num

/-! ## The 2-cocycle law (associativity of the twisted product) -/

/-- **The 2-cocycle law** `ε(α,β)·ε(α+β,γ) = ε(β,γ)·ε(α,β+γ)`.  Immediate from bi-additivity of
`coc`: both sides are `(−1)^{coc(α,β)+coc(α,γ)+coc(β,γ)}`.  This makes the twisted product
`eᵅ·eᵝ = ε(α,β) e^{α+β}` **associative**. -/
theorem cocycle_cocycleLaw (α β γ : L.carrier) :
    cocycle L B α β * cocycle L B (α + β) γ = cocycle L B β γ * cocycle L B α (β + γ) := by
  simp only [cocycle]
  rw [← zpow_add₀ cocycle_neg_one_ne, ← zpow_add₀ cocycle_neg_one_ne]
  congr 1
  rw [cocExp_add_left, cocExp_add_right]
  ring

/-! ## The commutator property (evenness enters) -/

/-- The key algebraic identity: `coc(α,β) + coc(β,α) = ⟨α,β⟩ − ∑ᵢ ⟨Bᵢ,Bᵢ⟩ αᵢ βᵢ`.  The
diagonal correction is where evenness will kill the sign. -/
theorem cocExp_add_swap (α β : L.carrier) :
    cocExp L B α β + cocExp L B β α
      = L.form α β - ∑ i : Fin n, L.form (B i) (B i) * B.repr α i * B.repr β i := by
  -- reindex `coc β α` so both coordinate-sums pair `repr α` (first index) with `repr β` (second)
  have hswap : cocExp L B β α
      = ∑ i : Fin n, ∑ j : Fin n,
          (if i < j then L.form (B i) (B j) else 0) * B.repr α i * B.repr β j := by
    rw [cocExp, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : a < b
    · rw [if_pos h, if_pos h, form_symm L (B b) (B a)]; ring
    · rw [if_neg h, if_neg h]; ring
  -- express the diagonal correction `D` as a double sum
  have hD : (∑ i : Fin n, L.form (B i) (B i) * B.repr α i * B.repr β i)
      = ∑ i : Fin n, ∑ j : Fin n,
          (if j = i then L.form (B i) (B j) * B.repr α i * B.repr β j else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_ite_eq' Finset.univ i
      (fun j => L.form (B i) (B j) * B.repr α i * B.repr β j), if_pos (Finset.mem_univ i)]
  rw [cocExp, hswap, form_eq_sum_repr L B α β, hD]
  -- combine into single `∑ i ∑ j` on both sides, then compare termwise
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- termwise: `[j<i]⟨⟩αβ + [i<j]⟨⟩αβ = ⟨⟩αβ − [j=i]⟨⟩αβ`
  by_cases hij : j = i
  · subst hij
    rw [if_pos rfl, if_neg (lt_irrefl j)]; ring
  · rw [if_neg hij]
    rcases lt_trichotomy j i with h | h | h
    · rw [if_pos h, if_neg (by omega : ¬ i < j)]; ring
    · exact absurd h hij
    · rw [if_neg (by omega : ¬ j < i), if_pos h]; ring

/-! ## The commutator property (evenness enters) -/

/-- **The commutator property** `ε(α,β)·ε(β,α) = (−1)^{⟨α,β⟩}` — the FLM sign that (anti)commutes
`Y(e^α), Y(e^β)` into locality.  Uses **evenness** on the diagonal: the correction
`∑ᵢ ⟨Bᵢ,Bᵢ⟩ αᵢ βᵢ` is even (each `⟨Bᵢ,Bᵢ⟩` is), so it drops out of the sign. -/
theorem cocycle_comm (hEven : L.Even) (α β : L.carrier) :
    cocycle L B α β * cocycle L B β α = (-1 : ℂ) ^ (L.form α β) := by
  simp only [cocycle]
  rw [← zpow_add₀ cocycle_neg_one_ne, cocExp_add_swap L B α β]
  -- the diagonal correction is even, hence contributes `(−1)^{even} = 1`
  have hDeven : (2 : ℤ) ∣ ∑ i : Fin n, L.form (B i) (B i) * B.repr α i * B.repr β i := by
    refine Finset.dvd_sum (fun i _ => ?_)
    exact ((hEven (B i)).mul_right (B.repr α i)).mul_right (B.repr β i)
  rw [zpow_sub₀ cocycle_neg_one_ne, (even_iff_two_dvd.mpr hDeven).neg_one_zpow, div_one]

/-! ## The canonical cocycle of a lattice (via a chosen `ℤ`-basis) -/

/-- A canonical `Fin`-indexed `ℤ`-basis of the lattice (any choice; the cocycle properties hold for
every basis). -/
noncomputable def latticeBasis :
    Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ L.carrier))) ℤ L.carrier :=
  (Module.Free.chooseBasis ℤ L.carrier).reindex (Fintype.equivFin _)

/-- **The canonical FLM 2-cocycle** `ε_L : L × L → ℂ` of the lattice `L`. -/
noncomputable def latticeCocycle (α β : L.carrier) : ℂ := cocycle L (latticeBasis L) α β

/-- `ε_L` satisfies the 2-cocycle law (associativity of the twisted product). -/
theorem latticeCocycle_cocycleLaw (α β γ : L.carrier) :
    latticeCocycle L α β * latticeCocycle L (α + β) γ
      = latticeCocycle L β γ * latticeCocycle L α (β + γ) :=
  cocycle_cocycleLaw L (latticeBasis L) α β γ

/-- `ε_L` satisfies the commutator property `ε_L(α,β)·ε_L(β,α) = (−1)^{⟨α,β⟩}` (uses `L.Even`). -/
theorem latticeCocycle_comm (hEven : L.Even) (α β : L.carrier) :
    latticeCocycle L α β * latticeCocycle L β α = (-1 : ℂ) ^ (L.form α β) :=
  cocycle_comm L (latticeBasis L) hEven α β

/-- `ε_L(0,β) = 1`. -/
theorem latticeCocycle_zero_left (β : L.carrier) : latticeCocycle L 0 β = 1 :=
  cocycle_zero_left L (latticeBasis L) β

/-- `ε_L(α,0) = 1`. -/
theorem latticeCocycle_zero_right (α : L.carrier) : latticeCocycle L α 0 = 1 :=
  cocycle_zero_right L (latticeBasis L) α

/-- `ε_L` is bi-multiplicative in the first slot. -/
theorem latticeCocycle_add_left (α α' β : L.carrier) :
    latticeCocycle L (α + α') β = latticeCocycle L α β * latticeCocycle L α' β :=
  cocycle_add_left L (latticeBasis L) α α' β

/-- `ε_L` is bi-multiplicative in the second slot. -/
theorem latticeCocycle_add_right (α β β' : L.carrier) :
    latticeCocycle L α (β + β') = latticeCocycle L α β * latticeCocycle L α β' :=
  cocycle_add_right L (latticeBasis L) α β β'

/-- `ε_L(α,β)² = 1` (it is a sign). -/
theorem latticeCocycle_sq (α β : L.carrier) :
    latticeCocycle L α β * latticeCocycle L α β = 1 :=
  cocycle_sq L (latticeBasis L) α β

/-- The **rank** of the lattice `L` (`= finrank_ℤ L`), the central charge of `𝒱(L)` (Goal 6). -/
noncomputable def rank : ℕ := Module.finrank ℤ L.carrier

/-- **Bounded lattice vectors are finite**: `{α | ⟨α,α⟩ ≤ N}` is finite for every `N`.  The one
analytic input for the general lattice-VOA `L₀`-grading (ℤ-posdef ⇒ ℝ-posdef discreteness); proved
from `L.PosDef` in `Foundations.LatticeFinite`. -/
def BoundedFinite (L : IntegralLattice) : Prop :=
  ∀ N : ℤ, {α : L.carrier | L.form α α ≤ N}.Finite

end VOA.IntegralLattice
