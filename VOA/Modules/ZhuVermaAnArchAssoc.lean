/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnIdeal

/-!
# `Aₙ(𝒱)` associativity: reduction to the homogeneous FZ associator.

This file attacks `AnFull.AssocLaw W n (anIdeal_holds W n)` — i.e.
`([a]·[b])·[c] = [a]·([b]·[c])` in `Aₙ(𝒱) = 𝒱/OnFull W n`, equivalently the Frenkel–Zhu /
Dong–Li–Mason associator membership
`(a *ₙ b) *ₙ c − a *ₙ (b *ₙ c) ∈ Oₙ(𝒱)`  (DLM Lemma 2.1, the depth-`n` lift of Zhu's `n = 0`
associativity proved in `ZhuAssociator.associator_core`).

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `AnFull.assocCore W n` — the precise associator-membership target Prop
  `∀ a b c, leftProd n (leftProd n a b) c − leftProd n a (leftProd n b c) ∈ OnFull W n`.
* `AnFull.assoc W n a b c` — the associator vector, and the trilinearity lemmas
  `assoc_add_left/mid/right`, `assoc_smul_left/mid/right` (each slot is ℂ-linear, since `leftProd`
  is bilinear). These show the associator is a genuine trilinear form on `𝒱`.
* **`AnFull.AssocLaw_of_assocCore`** — the clean reduction: `assocCore W n` ⟹
  `AnFull.AssocLaw W n (anIdeal_holds W n)`. (Quotient algebra associativity ⇔ associator in the
  ideal.) This proves that the OPEN law of `ZhuVermaAnArchAlgebra` is *exactly* `assocCore`.
* **`AnFull.assocCore_of_homogeneous`** — the **trilinear homogeneity reduction**: it suffices to
  prove the associator membership for *homogeneous* `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`, `c ∈ 𝒱ᵣ`. Proved by three
  nested `Submodule.iSup_induction`s over the internal grading (`W.isInternal`), using the slotwise
  trilinearity and the submodule-closure of `OnFull`. This is the genuine reduction that pins the
  remaining content to the homogeneous combinatorial core.
* `AnFull.AssocLaw_of_homogeneous` — chains the two: a homogeneous associator-membership hypothesis
  discharges the full quotient `AssocLaw`.

## What is OPEN (precise, NOT faked — no `sorry`, no axiom)

* `AnFull.AssocHom W n` — the **homogeneous** FZ associator membership: for homogeneous
  `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`, `c ∈ 𝒱ᵣ`, the associator `(a *ₙ b) *ₙ c − a *ₙ (b *ₙ c) ∈ OnFull W n`.
  This is the depth-`n` analogue of the `n = 0` `ZhuAssociator.assoc_eq` identity
  `(u*v)*w − u*(v*w) = Ufam + Vfam` with `Ufam, Vfam ∈ O W` (each a `Pres`-tower in `O`). The
  depth-`n` version requires the depth-`n` `Pres`-tower decomposition of
  `leftProd (leftProd a b) c`, whose two outer families would land in `OnFull W n` via the proved
  keystone `Pres_mem_OnFull` (`= PresOn ∈ Oₙ`). The genuine missing inputs are the **depth-`n`
  scalar cores**: the depth-`n` analogues of `ZhuMu.mu_identity`, `ZhuUCore.u_core`,
  `ZhuVCore.v_core` (the `n = 0` cores carry the
  `cbz` Vandermonde/μ-absorption identities; their `2n`-pole-shifted lifts are not among the
  imported lemmas). Stated precisely below as `AnFull.AssocHom`; `assocCore_of_homogeneous` shows it
  is the *only* remaining content.

## References
Dong–Li–Mason, J. Algebra 206 (1998) 67–96 (`q-alg/9612010`), Lemma 2.1; Frenkel–Zhu, Duke 66
(1992); Zhu, J. AMS 9 (1996); mirror of `ZhuAssociator.lean` (`associator_core`, the `n = 0` case).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace AnFull

variable (W : VertexOperatorAlgebra 𝒱) (n : ℕ)

/-! ## The associator vector and its trilinearity. -/

/-- The **FZ associator vector** `Assoc(a,b,c) = (a *ₙ b) *ₙ c − a *ₙ (b *ₙ c)`. -/
noncomputable def assoc (a b c : 𝒱) : 𝒱 :=
  leftProd W n (leftProd W n a b) c - leftProd W n a (leftProd W n b c)

theorem assoc_add_left (a₁ a₂ b c : 𝒱) :
    assoc W n (a₁ + a₂) b c = assoc W n a₁ b c + assoc W n a₂ b c := by
  simp only [assoc, leftProd_add_left]
  abel

theorem assoc_smul_left (s : ℂ) (a b c : 𝒱) :
    assoc W n (s • a) b c = s • assoc W n a b c := by
  simp only [assoc, leftProd_smul_left, smul_sub]

theorem assoc_add_mid (a b₁ b₂ c : 𝒱) :
    assoc W n a (b₁ + b₂) c = assoc W n a b₁ c + assoc W n a b₂ c := by
  simp only [assoc, leftProd_add_right, leftProd_add_left]
  abel

theorem assoc_smul_mid (s : ℂ) (a b c : 𝒱) :
    assoc W n a (s • b) c = s • assoc W n a b c := by
  simp only [assoc, leftProd_smul_right, leftProd_smul_left, smul_sub]

theorem assoc_add_right (a b c₁ c₂ : 𝒱) :
    assoc W n a b (c₁ + c₂) = assoc W n a b c₁ + assoc W n a b c₂ := by
  simp only [assoc, leftProd_add_right]
  abel

theorem assoc_smul_right (s : ℂ) (a b c : 𝒱) :
    assoc W n a b (s • c) = s • assoc W n a b c := by
  simp only [assoc, leftProd_smul_right, smul_sub]

theorem assoc_zero_left (b c : 𝒱) : assoc W n 0 b c = 0 := by
  rw [← zero_smul ℂ (0 : 𝒱), assoc_smul_left]; simp

theorem assoc_zero_mid (a c : 𝒱) : assoc W n a 0 c = 0 := by
  rw [← zero_smul ℂ (0 : 𝒱), assoc_smul_mid]; simp

theorem assoc_zero_right (a b : 𝒱) : assoc W n a b 0 = 0 := by
  rw [← zero_smul ℂ (0 : 𝒱), assoc_smul_right]; simp

/-! ## The associator-membership targets (Props, NOT axioms). -/

/-- **The associator-membership target** `assocCore W n`: the FZ associator lies in `Oₙ(𝒱)` for ALL
`a, b, c` (DLM Lemma 2.1). Equivalent to `AnFull.AssocLaw` (see `AssocLaw_of_assocCore`). -/
def assocCore : Prop := ∀ a b c : 𝒱, assoc W n a b c ∈ OnFull W n

/-- **The homogeneous associator-membership target** `AssocHom W n`: the FZ associator lies in
`Oₙ(𝒱)` for HOMOGENEOUS `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`, `c ∈ 𝒱ᵣ`. This is the depth-`n` analogue of the
`n = 0` `ZhuAssociator.assoc_eq` (where it equals `Ufam + Vfam ∈ O`). The remaining combinatorial
content; NOT available among the imported lemmas. -/
def AssocHom : Prop :=
  ∀ (p q r : ℤ), ∀ a ∈ W.grading p, ∀ b ∈ W.grading q, ∀ c ∈ W.grading r,
    assoc W n a b c ∈ OnFull W n

/-! ## Trilinear homogeneity reduction: `AssocHom ⟹ assocCore`. -/

/-- Reduce the right (`c`) slot of `assocCore` to homogeneous `c`, given homogeneous `a, b`. -/
theorem assocCore_right_of_hom (hH : AssocHom W n) {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (c : 𝒱) :
    assoc W n a b c ∈ OnFull W n := by
  have hctop : c ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun c => assoc W n a b c ∈ OnFull W n) hctop ?_ ?_ ?_
  · intro r c hc
    exact hH p q r a ha b hb c hc
  · change assoc W n a b 0 ∈ OnFull W n
    rw [assoc_zero_right]; exact (OnFull W n).zero_mem
  · intro c₁ c₂ h₁ h₂
    change assoc W n a b (c₁ + c₂) ∈ OnFull W n
    rw [assoc_add_right]; exact (OnFull W n).add_mem h₁ h₂

/-- Reduce the middle (`b`) slot to homogeneous `b`, given homogeneous `a`. -/
theorem assocCore_mid_of_hom (hH : AssocHom W n) {p : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading p) (b c : 𝒱) :
    assoc W n a b c ∈ OnFull W n := by
  have hbtop : b ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun b => ∀ c : 𝒱, assoc W n a b c ∈ OnFull W n) hbtop ?_ ?_ ?_ c
  · intro q b hb c
    exact assocCore_right_of_hom W n hH ha hb c
  · intro c
    change assoc W n a 0 c ∈ OnFull W n
    rw [assoc_zero_mid]; exact (OnFull W n).zero_mem
  · intro b₁ b₂ h₁ h₂ c
    change assoc W n a (b₁ + b₂) c ∈ OnFull W n
    rw [assoc_add_mid]; exact (OnFull W n).add_mem (h₁ c) (h₂ c)

/-- **The trilinear homogeneity reduction**: the homogeneous associator membership `AssocHom W n`
implies the full associator membership `assocCore W n`. (Three nested `iSup_induction`s over the
internal grading, using slotwise trilinearity and submodule closure of `OnFull`.) -/
theorem assocCore_of_homogeneous (hH : AssocHom W n) : assocCore W n := by
  intro a b c
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun a => ∀ b c : 𝒱, assoc W n a b c ∈ OnFull W n) hatop ?_ ?_ ?_ b c
  · intro p a ha b c
    exact assocCore_mid_of_hom W n hH ha b c
  · intro b c
    change assoc W n 0 b c ∈ OnFull W n
    rw [assoc_zero_left]; exact (OnFull W n).zero_mem
  · intro a₁ a₂ h₁ h₂ b c
    change assoc W n (a₁ + a₂) b c ∈ OnFull W n
    rw [assoc_add_left]; exact (OnFull W n).add_mem (h₁ b c) (h₂ b c)

/-! ## The associator membership discharges the quotient `AssocLaw`. -/

/-- **The reduction `assocCore ⟹ AssocLaw`.** If the FZ associator lies in `Oₙ(𝒱)` for all
`a, b, c`, then the descended product on `Aₙ(𝒱) = 𝒱/Oₙ` is associative. (Quotient: the associator
class is `0` iff the associator vector is in the ideal.) -/
theorem AssocLaw_of_assocCore (hcore : assocCore W n) :
    AnFull.AssocLaw W n (anIdeal_holds W n) := by
  intro P Q R
  refine Submodule.Quotient.induction_on _ P fun a => ?_
  refine Submodule.Quotient.induction_on _ Q fun b => ?_
  refine Submodule.Quotient.induction_on _ R fun c => ?_
  -- rewrite each class as `mkAnFull`, evaluate the products via `mul_mk`.
  change AnFull.mul W n (anIdeal_holds W n)
        (AnFull.mul W n (anIdeal_holds W n) (mkAnFull W n a) (mkAnFull W n b)) (mkAnFull W n c)
      = AnFull.mul W n (anIdeal_holds W n) (mkAnFull W n a)
          (AnFull.mul W n (anIdeal_holds W n) (mkAnFull W n b) (mkAnFull W n c))
  rw [AnFull.mul_mk, AnFull.mul_mk, AnFull.mul_mk, AnFull.mul_mk]
  -- both sides are `mkAnFull` of the two leftProd iterates; equal iff their difference ∈ OnFull.
  rw [mkAnFull_apply, mkAnFull_apply, Submodule.Quotient.eq]
  -- `OnFull` is closed under negation, and `x - y ∈ Oₙ ⟺ y - x ∈ Oₙ`.
  have h := hcore a b c
  rw [assoc] at h
  -- `Submodule.Quotient.eq` gives goal `lhs - rhs ∈ OnFull`; `h` is exactly that.
  exact h

/-- **The end-to-end reduction**: the homogeneous associator membership discharges the full
`AnFull.AssocLaw`. Discharging `AssocHom W n` (the depth-`n` FZ scalar cores) flips associativity of
`Aₙ(𝒱)` unconditionally with zero extra wiring. -/
theorem AssocLaw_of_homogeneous (hH : AssocHom W n) :
    AnFull.AssocLaw W n (anIdeal_holds W n) :=
  AssocLaw_of_assocCore W n (assocCore_of_homogeneous W n hH)

end AnFull

end VOA
