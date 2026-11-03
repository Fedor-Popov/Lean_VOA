/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.LowestWeightExistence

/-!
# `ι ≃ Φ(𝒱)` — the index of the module family IS the set of irreducibles

Every modularity statement is indexed by an abstract `Fintype ι` carrying a family
`Mfam : ι → IrrModule 𝒱`, and compares `Fintype.card ι` with the rank of a block ambient.  The
*count* (`Modularity.ZhuCount`) delivers a bound by `Nat.card (Φ 𝒱)`.  **Nothing connected
the two**: without the bridge below, `hrank` and the count are statements about different numbers.

This file supplies it.  A family is the right index exactly when it is

* **irredundant** — pairwise non-isomorphic, and
* **complete** — every irreducible module is isomorphic to a member,

and then `i ↦ [Mfam i]` is a bijection `ι ≃ Φ 𝒱`.

## Main results

* `IrrModule.toΦ` — the class of an irreducible module;
* `equivΦ_of_irredundant_complete`, `nonempty_equiv_Φ`;
* `card_eq_card_Φ` — `Fintype.card ι = Nat.card (Φ 𝒱)`, the bridge the count needs.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  `Irredundant` and `Complete` are *properties of the
chosen family*, not new mathematical gates: any enumeration of `Φ 𝒱` satisfies both by construction
(`irredundant_complete_of_equiv`).
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The iso-class of an irreducible module. -/
def IrrModule.toΦ (V : IrrModule W) : Φ W := Quotient.mk (IrrModule.setoid W) V

@[simp] theorem IrrModule.toΦ_eq_iff (V V' : IrrModule W) :
    V.toΦ = V'.toΦ ↔ IrrModule.Iso W V V' :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

section

variable {ι : Type*} (Mfam : ι → IrrModule W)

/-- The family is **irredundant**: its members are pairwise non-isomorphic. -/
def Irredundant : Prop := ∀ i j, IrrModule.Iso W (Mfam i) (Mfam j) → i = j

/-- The family is **complete**: every irreducible module is isomorphic to a member. -/
def Complete : Prop := ∀ V : IrrModule W, ∃ i, IrrModule.Iso W V (Mfam i)

/-- **An irredundant complete family is indexed by `Φ(𝒱)`.** -/
noncomputable def equivΦ_of_irredundant_complete
    (hirr : Irredundant Mfam) (hcomp : Complete Mfam) : ι ≃ Φ W := by
  refine Equiv.ofBijective (fun i => (Mfam i).toΦ) ⟨?_, ?_⟩
  · intro i j hij
    exact hirr i j ((IrrModule.toΦ_eq_iff _ _).mp hij)
  · refine Quotient.ind fun V => ?_
    obtain ⟨i, hi⟩ := hcomp V
    exact ⟨i, Quotient.sound ((IrrModule.setoid W).iseqv.symm hi)⟩

theorem nonempty_equiv_Φ (hirr : Irredundant Mfam) (hcomp : Complete Mfam) :
    Nonempty (ι ≃ Φ W) :=
  ⟨equivΦ_of_irredundant_complete Mfam hirr hcomp⟩

/-- **The bridge the count needs**: the family's index has exactly `#Φ(𝒱)` elements, so
`Modularity.ZhuCount`'s bound `≤ Nat.card (Φ 𝒱)` is a bound on `Fintype.card ι`. -/
theorem card_eq_card_Φ [Fintype ι] (hirr : Irredundant Mfam) (hcomp : Complete Mfam) :
    Fintype.card ι = Nat.card (Φ W) := by
  classical
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (equivΦ_of_irredundant_complete Mfam hirr hcomp)

/-- `Φ(𝒱)` is finite as soon as an irredundant complete family on a finite index exists. -/
theorem finite_Φ_of_family [Finite ι] (hirr : Irredundant Mfam) (hcomp : Complete Mfam) :
    Finite (Φ W) :=
  Finite.of_equiv _ (equivΦ_of_irredundant_complete Mfam hirr hcomp)

end

/-- Conversely, any enumeration of `Φ(𝒱)` yields an irredundant complete family, so the two
conditions cost nothing: they only say the family *is* an enumeration. -/
theorem irredundant_complete_of_equiv {ι : Type*} (e : ι ≃ Φ W)
    (Mfam : ι → IrrModule W) (hMfam : ∀ i, (Mfam i).toΦ = e i) :
    Irredundant Mfam ∧ Complete Mfam := by
  constructor
  · intro i j hij
    exact e.injective (by rw [← hMfam i, ← hMfam j]; exact Quotient.sound hij)
  · intro V
    refine ⟨e.symm (Quotient.mk (IrrModule.setoid W) V), ?_⟩
    have : (Mfam (e.symm (Quotient.mk (IrrModule.setoid W) V))).toΦ
        = Quotient.mk (IrrModule.setoid W) V := by
      rw [hMfam, Equiv.apply_symm_apply]
    exact Quotient.exact this.symm

end VOA
