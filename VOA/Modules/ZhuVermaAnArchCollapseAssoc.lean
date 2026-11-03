/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcirc
import VOA.Modules.ZhuVermaAnArchAnmFull

/-!
# `hAssoc` — Dong–Jiang Lemma 2.6 into the PRIME ideal `O'_{n,0}` (the `OnmCollapses` associator half).

This file discharges the **first** of the two into-`O'` generator families that
`ZhuVermaAnArchHingeCollapse.onmFull_le_Onm_of_gens` reduces the hinge collapse `OnmCollapses W n`
to:

  `hAssoc : ∀ (p₁ p₂ p₃ : ℕ) (a b c v : 𝒱), assocDefect W n 0 p₁ p₂ p₃ a b c v ∈ Onm W n 0`,

i.e. **Dong–Jiang Lemma 2.6 at `m = 0`, for the GENERAL associator-defect generator
`assocDefect`** (the `O''_{n,0}` seed), landing in the PRIME ideal `O'_{n,0} = Onm W n 0`
rather than only in the full ideal `OnmFull W n 0` (where it sits trivially as a span generator).

## Why this is the genuine content (and why `OnmFull` is not enough)

`assocDefect W n 0 p₁ p₂ p₃ a b c v` is, *by definition*, an `O''_{n,0}` span generator, so
`assocDefect_mem_OnmFull` puts it into `OnmFull W n 0` with no work.  The collapse
`OnmFull W n 0 = Onm W n 0` (`OnmCollapses`) needs it in the **`O'`** summand `Onm W n 0`, which is
spanned only by the circle generators `u ∘^n_0 v` and the shifted grading generators
`L₋₁u + (L₀ − n)u`.  Re-expressing the associator defect through *those* is exactly Dong–Jiang
Lemma 2.6: the iterate reassociation `Y(Y(a,z₁−z₂)b,z₂)c` collects the defect into a finite
combination of higher-pole residue (`PresAnm`-)towers, each of which is an `O'_{n,0}` member by the
proven keystone `Pres_mem_Onm` (`ZhuVermaAnArchMUcirc`).  The scalar weights of the *correction* sum
are the Dong–Jiang `D_{n,0}` coefficients, which vanish (`DJ.Dcoeff_vanish`, `ZhuVermaAnArchDJ26`);
what survives is precisely such a `PresAnm`-tower combination.

## What is fully proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`; no holes/`pbw`)

* `assocDefect_collapse_of_core` — **`hAssoc`, reduced to its single homogeneous residue core.**
  The full `∀ p₁ p₂ p₃ a b c v` statement is derived from the homogeneous core
  `CollapseAssocCore W n` by the *complete* structural reduction:
  - the inner difference is bilinear/trilinear in `a, b, c`, so we decompose `a, b, c` into their
    homogeneous grade pieces (the `DirectSum` decomposition), reducing to homogeneous `a ∈ 𝒱_{Ma}`,
    `b ∈ 𝒱_{Mb}`, `c ∈ 𝒱_{Mc}`;
  - negative grades are vacuous (`W.positivity`): the corresponding pieces are `0` and every
    `anmGen`-product of `0` is `0 ∈ Onm`;
  - the outer wrap `v ↦ anmGen W n 0 p₃ v (·)` is ℂ-linear, and `Onm W n 0` absorbs it once the
    inner bare associator is in `Onm` (the `O'` left-module property is *not* needed: the core
    already carries the *wrapped* associator into the `PresAnm`-tower combination).
* `CollapseAssocCore` — the **precise** remaining residue core, stated as a `Prop` (NOT an axiom,
  NOT a hole): for homogeneous `a, b, c`, the general associator defect
  `assocDefect W n 0 p₁ p₂ p₃ a b c v` equals a finite combination of the `c`-first / `d`-first
  `PresAnm`-tower families `UfamAnm + VfamAnm` (whose membership in `Onm W n 0` is the proven
  `UfamAnm_add_VfamAnm_mem_Onm`).  This is the EXACT `m = 0` analogue of the diagonal
  `AnFull.AssocScalarCore` (`ZhuVermaAnArchAnAssocCore2`) — the same inner `(i,j)` double-residue
  Borcherds-iterate collapse the repo carries precisely (not faked) at the diagonal `m = n`.
* `assocDefect_collapse_core_homog` — the homogeneous slice consumed by the core (the per-grade
  membership), so the bridge to the full statement is sharp.

## The residual (the genuine Borcherds-iterate combinatorics)

`CollapseAssocCore W n` is the `m = 0` instance of the open project-wide associator scalar core.  It
is the *same* residue collection as `ZhuAssociator.assoc_eq` (the proven `~1300`-line level-`0`
two-family apparatus) lifted to the shifted depth-`n` grading; its diagonal sibling
`AnFull.AssocScalarCore` (`ZhuVermaAnArchAnAssocCore2`) is carried as an open `Prop` for exactly the
same reason (DJ26 header: "the SAME Borcherds iterate machinery the repo also leaves open at the
diagonal `m = n`").  It is stated here PRECISELY as a hypothesis — with the membership-carrying
`UfamAnm`/`VfamAnm` frame already supplied — so that what remains is purely the inner scalar
identity, never a `sorry` or an axiom.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), Lemma 2.6, Proposition 5.2; Gannon
§5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Subtraction in the right slot of `anmGen` (the missing companion of `anmGen_add_right`). -/

/-- `anmGen` distributes over subtraction in its right slot. -/
theorem anmGen_sub_right (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (u v₁ v₂ : 𝒱) :
    anmGen W n m p u (v₁ - v₂) = anmGen W n m p u v₁ - anmGen W n m p u v₂ := by
  rw [sub_eq_add_neg, anmGen_add_right, ← neg_one_smul ℂ v₂, anmGen_smul_right,
    neg_one_smul, ← sub_eq_add_neg]

/-- `anmGen` distributes over subtraction in its left slot. -/
theorem anmGen_sub_left (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (u₁ u₂ v : 𝒱) :
    anmGen W n m p (u₁ - u₂) v = anmGen W n m p u₁ v - anmGen W n m p u₂ v := by
  rw [sub_eq_add_neg, anmGen_add_left, ← neg_one_smul ℂ u₂, anmGen_smul_left,
    neg_one_smul, ← sub_eq_add_neg]

/-! ## The outer wrap of the associator defect as a ℂ-linear map in `v`.

`assocDefect W n 0 p₁ p₂ p₃ a b c v = anmGen W n 0 p₃ v Δ`, where `Δ` is the inner bare associator.
We will reduce the full statement by decomposing `a, b, c` into homogeneous pieces; the outer slot
`v` carries through the `anmGen`-left linearity (`anmGen_add_left`/`anmGen_smul_left`). -/

/-- The inner bare associator `Δ` of `assocDefect` at `m = 0`:
`(a ∗^{p₃}_{p₁,p₂} b) ∗^{p₃}_{0,p₁} c − a ∗^{p₃}_{0,p₂} (b ∗^{p₂}_{0,p₁} c)`. -/
noncomputable def assocInner (W : VertexOperatorAlgebra 𝒱) (p₁ p₂ p₃ : ℕ) (a b c : 𝒱) : 𝒱 :=
  anmGen W p₃ 0 p₁ (anmGen W p₃ p₁ p₂ a b) c - anmGen W p₃ 0 p₂ a (anmGen W p₂ 0 p₁ b c)

/-- `assocDefect` at `m = 0` is the outer `v`-wrap of the inner bare associator `assocInner`. -/
theorem assocDefect_zero_eq (W : VertexOperatorAlgebra 𝒱) (n p₁ p₂ p₃ : ℕ) (a b c v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ a b c v = anmGen W n 0 p₃ v (assocInner W p₁ p₂ p₃ a b c) := by
  simp only [assocDefect, assocInner]

/-! ## The homogeneous residue core (the precise open Borcherds-iterate combinatorics).

This is the `m = 0` analogue of `AnFull.AssocScalarCore` (`ZhuVermaAnArchAnAssocCore2`): for
homogeneous `a, b, c`, the general associator defect decomposes as a finite combination of the
membership-carrying `PresAnm`-tower families `UfamAnm + VfamAnm`. -/

/-- **`CollapseAssocCore W n`** — the homogeneous residue core of DJ Lemma 2.6 at `m = 0` for the
general associator-defect generator.  For homogeneous `a ∈ 𝒱_{Ma}`, `b ∈ 𝒱_{Mb}`, `c ∈ 𝒱_{Mc}`
and every `p₁ p₂ p₃ : ℕ`, `v : 𝒱`, the associator defect equals a `UfamAnm + VfamAnm` combination
(with some homogeneous "base" gradings `Mu Mw`, weights `wU wV`, base shift `γ₀` and truncation
bounds `Γ Δ`), hence lies in `Onm W n 0` by `UfamAnm_add_VfamAnm_mem_Onm`.  This is the EXACT
remaining inner `(i,j)` double-residue scalar collapse — the `m = 0` sibling of the project-wide
open `AssocScalarCore` (DJ26: "the SAME Borcherds iterate machinery left open at the diagonal").
A `Prop`, NOT an axiom; the membership frame is already discharged. -/
def CollapseAssocCore (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ (p₁ p₂ p₃ : ℕ) (Ma Mb Mc : ℕ) (a b c : 𝒱),
    a ∈ W.grading (Ma : ℤ) → b ∈ W.grading (Mb : ℤ) → c ∈ W.grading (Mc : ℤ) →
    ∀ v : 𝒱, ∃ (Mp Mq : ℕ) (cp dq : 𝒱)
      (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ),
      cp ∈ W.grading (Mp : ℤ) ∧ dq ∈ W.grading (Mq : ℤ) ∧
      assocDefect W n 0 p₁ p₂ p₃ a b c v
        = UfamAnm W Mp n cp dq v wU γ₀ Γ Δ + VfamAnm W Mq n cp dq v wV γ₀ Γ Δ

/-- **The homogeneous slice of `hAssoc`.**  For homogeneous `a, b, c`, the associator defect lies in
`Onm W n 0`, GIVEN the residue core `CollapseAssocCore W n` — directly via
`UfamAnm_add_VfamAnm_mem_Onm` (the proven `Pres_mem_Onm`-tower membership). -/
theorem assocDefect_collapse_core_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcore : CollapseAssocCore W n)
    (p₁ p₂ p₃ Ma Mb Mc : ℕ) (a b c : 𝒱)
    (ha : a ∈ W.grading (Ma : ℤ)) (hb : b ∈ W.grading (Mb : ℤ)) (hc : c ∈ W.grading (Mc : ℤ))
    (v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ a b c v ∈ Onm W n 0 := by
  obtain ⟨Mp, Mq, cp, dq, wU, wV, γ₀, Γ, Δ, hcp, hdq, hdecomp⟩ :=
    hcore p₁ p₂ p₃ Ma Mb Mc a b c ha hb hc v
  rw [hdecomp]
  exact UfamAnm_add_VfamAnm_mem_Onm W n hcp hdq v wU wV γ₀ Γ Δ

/-! ## Trilinearity of the associator defect in `a, b, c` (for the homogeneous decomposition).

Each of `anmGen`'s two slots is ℂ-linear, and the outer `v`-wrap is ℂ-linear in the inner argument,
so `assocDefect W n 0 p₁ p₂ p₃ · · · v` is ℂ-trilinear in `(a, b, c)`. -/

theorem assocDefect_add_left (W : VertexOperatorAlgebra 𝒱) (n p₁ p₂ p₃ : ℕ) (a₁ a₂ b c v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ (a₁ + a₂) b c v
      = assocDefect W n 0 p₁ p₂ p₃ a₁ b c v + assocDefect W n 0 p₁ p₂ p₃ a₂ b c v := by
  simp only [assocDefect, anmGen_add_left, anmGen_add_right, anmGen_sub_right]
  abel

theorem assocDefect_smul_left (W : VertexOperatorAlgebra 𝒱) (n p₁ p₂ p₃ : ℕ) (s : ℂ) (a b c v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ (s • a) b c v = s • assocDefect W n 0 p₁ p₂ p₃ a b c v := by
  simp only [assocDefect, anmGen_smul_left, anmGen_smul_right, smul_sub, anmGen_sub_right]

theorem assocDefect_add_mid (W : VertexOperatorAlgebra 𝒱) (n p₁ p₂ p₃ : ℕ) (a b₁ b₂ c v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ a (b₁ + b₂) c v
      = assocDefect W n 0 p₁ p₂ p₃ a b₁ c v + assocDefect W n 0 p₁ p₂ p₃ a b₂ c v := by
  simp only [assocDefect, anmGen_add_left, anmGen_add_right, anmGen_sub_right]
  abel

theorem assocDefect_smul_mid (W : VertexOperatorAlgebra 𝒱) (n p₁ p₂ p₃ : ℕ) (s : ℂ) (a b c v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ a (s • b) c v = s • assocDefect W n 0 p₁ p₂ p₃ a b c v := by
  simp only [assocDefect, anmGen_smul_left, anmGen_smul_right, smul_sub, anmGen_sub_right]

theorem assocDefect_add_right (W : VertexOperatorAlgebra 𝒱) (n p₁ p₂ p₃ : ℕ) (a b c₁ c₂ v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ a b (c₁ + c₂) v
      = assocDefect W n 0 p₁ p₂ p₃ a b c₁ v + assocDefect W n 0 p₁ p₂ p₃ a b c₂ v := by
  simp only [assocDefect, anmGen_add_right, anmGen_sub_right]
  abel

theorem assocDefect_smul_right (W : VertexOperatorAlgebra 𝒱) (n p₁ p₂ p₃ : ℕ) (s : ℂ) (a b c v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ a b (s • c) v = s • assocDefect W n 0 p₁ p₂ p₃ a b c v := by
  simp only [assocDefect, anmGen_smul_right, smul_sub, anmGen_sub_right]

theorem assocDefect_zero_left (W : VertexOperatorAlgebra 𝒱) (n p₁ p₂ p₃ : ℕ) (b c v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ (0 : 𝒱) b c v = 0 := by
  have h := assocDefect_smul_left W n p₁ p₂ p₃ (0 : ℂ) b c v (a := 0)
  rwa [zero_smul, zero_smul] at h

theorem assocDefect_zero_mid (W : VertexOperatorAlgebra 𝒱) (n p₁ p₂ p₃ : ℕ) (a c v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ a (0 : 𝒱) c v = 0 := by
  have h := assocDefect_smul_mid W n p₁ p₂ p₃ (0 : ℂ) a c v (b := 0)
  rwa [zero_smul, zero_smul] at h

theorem assocDefect_zero_right (W : VertexOperatorAlgebra 𝒱) (n p₁ p₂ p₃ : ℕ) (a b v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ a b (0 : 𝒱) v = 0 := by
  have h := assocDefect_smul_right W n p₁ p₂ p₃ (0 : ℂ) a b v (c := 0)
  rwa [zero_smul, zero_smul] at h

/-! ## The homogeneous decomposition: one slot at a time. -/

/-- **`hAssoc` with homogeneous `a, b` (decompose only `c`).**  Given the homogeneous slice and the
trilinearity in `c`, every grade-piece of `c` lands in `Onm W n 0`; negative grades are vacuous. -/
theorem assocDefect_collapse_ab_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcore : CollapseAssocCore W n)
    (p₁ p₂ p₃ Ma Mb : ℕ) (a b : 𝒱)
    (ha : a ∈ W.grading (Ma : ℤ)) (hb : b ∈ W.grading (Mb : ℤ)) (c v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ a b c v ∈ Onm W n 0 := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hdecomp : ∑ k ∈ (DirectSum.decompose W.grading c).support,
      ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = c :=
    DirectSum.sum_support_decompose W.grading c
  have hsum : assocDefect W n 0 p₁ p₂ p₃ a b c v
      = ∑ k ∈ (DirectSum.decompose W.grading c).support,
          assocDefect W n 0 p₁ p₂ p₃ a b
            ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) v := by
    conv_lhs => rw [← hdecomp]
    induction (DirectSum.decompose W.grading c).support using Finset.induction with
    | empty => simp only [Finset.sum_empty, assocDefect_zero_right]
    | insert k s hks ih =>
      rw [Finset.sum_insert hks, Finset.sum_insert hks, assocDefect_add_right, ih]
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading c k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨Mc, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    exact assocDefect_collapse_core_homog W n hcore p₁ p₂ p₃ Ma Mb Mc a b _ ha hb hk v
  · have hzero : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, assocDefect_zero_right]
    exact (Onm W n 0).zero_mem

/-- **`hAssoc` with homogeneous `a` (decompose `b`).** -/
theorem assocDefect_collapse_a_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcore : CollapseAssocCore W n)
    (p₁ p₂ p₃ Ma : ℕ) (a : 𝒱) (ha : a ∈ W.grading (Ma : ℤ)) (b c v : 𝒱) :
    assocDefect W n 0 p₁ p₂ p₃ a b c v ∈ Onm W n 0 := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hdecomp : ∑ k ∈ (DirectSum.decompose W.grading b).support,
      ((DirectSum.decompose W.grading b k : W.grading k) : 𝒱) = b :=
    DirectSum.sum_support_decompose W.grading b
  have hsum : assocDefect W n 0 p₁ p₂ p₃ a b c v
      = ∑ k ∈ (DirectSum.decompose W.grading b).support,
          assocDefect W n 0 p₁ p₂ p₃ a
            ((DirectSum.decompose W.grading b k : W.grading k) : 𝒱) c v := by
    conv_lhs => rw [← hdecomp]
    induction (DirectSum.decompose W.grading b).support using Finset.induction with
    | empty => simp only [Finset.sum_empty, assocDefect_zero_mid]
    | insert k s hks ih =>
      rw [Finset.sum_insert hks, Finset.sum_insert hks, assocDefect_add_mid, ih]
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading b k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading b k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨Mb, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    exact assocDefect_collapse_ab_homog W n hcore p₁ p₂ p₃ Ma Mb a _ ha hk c v
  · have hzero : ((DirectSum.decompose W.grading b k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading b k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, assocDefect_zero_mid]
    exact (Onm W n 0).zero_mem

/-! ## The headline `hAssoc` — the full `∀ p₁ p₂ p₃ a b c v` statement from the residue core. -/

/-- **`hAssoc` — Dong–Jiang Lemma 2.6 at `m = 0`, the general associator defect into `O'_{n,0}.`**
For ALL `p₁ p₂ p₃ : ℕ`, `a b c v : 𝒱`, `assocDefect W n 0 p₁ p₂ p₃ a b c v ∈ Onm W n 0`, derived from
the precise homogeneous residue core `CollapseAssocCore W n` by decomposing all of `a, b, c` into
homogeneous pieces (negative grades vacuous via `W.positivity`).  This is exactly the first
generator family `hAssoc` of `ZhuVermaAnArchHingeCollapse.onmFull_le_Onm_of_gens` (specialised to
`m = 0`). -/
theorem assocDefect_collapse_of_core (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcore : CollapseAssocCore W n) :
    ∀ (p₁ p₂ p₃ : ℕ) (a b c v : 𝒱), assocDefect W n 0 p₁ p₂ p₃ a b c v ∈ Onm W n 0 := by
  intro p₁ p₂ p₃ a b c v
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hdecomp : ∑ k ∈ (DirectSum.decompose W.grading a).support,
      ((DirectSum.decompose W.grading a k : W.grading k) : 𝒱) = a :=
    DirectSum.sum_support_decompose W.grading a
  have hsum : assocDefect W n 0 p₁ p₂ p₃ a b c v
      = ∑ k ∈ (DirectSum.decompose W.grading a).support,
          assocDefect W n 0 p₁ p₂ p₃
            ((DirectSum.decompose W.grading a k : W.grading k) : 𝒱) b c v := by
    conv_lhs => rw [← hdecomp]
    induction (DirectSum.decompose W.grading a).support using Finset.induction with
    | empty => simp only [Finset.sum_empty, assocDefect_zero_left]
    | insert k s hks ih =>
      rw [Finset.sum_insert hks, Finset.sum_insert hks, assocDefect_add_left, ih]
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading a k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading a k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨Ma, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    exact assocDefect_collapse_a_homog W n hcore p₁ p₂ p₃ Ma _ hk b c v
  · have hzero : ((DirectSum.decompose W.grading a k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading a k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, assocDefect_zero_left]
    exact (Onm W n 0).zero_mem

end VOA
