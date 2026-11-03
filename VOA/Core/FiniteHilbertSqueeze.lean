/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The finite-dimensional Hilbert squeeze

Classical-freeness arguments are applied one conformal weight and one filtration degree at a
time.  The canonical jet-to-Li map is already surjective.  A normal-form or carrier theorem gives
the opposite dimension inequality.  These elementary lemmas record that this is enough for
injectivity, without introducing a formal-power-series Hilbert-series layer.

The last two lemmas implement the slightly coarser comparison actually supplied by a character
identity.  At one fixed conformal weight there are only finitely many Li degrees.  If the proposed
normal-form dimensions, the actual dimensions, and the ambient dimensions form a pointwise
sandwich, while the two outside dimensions have equal total sums, then every pointwise inequality
is an equality.
-/

namespace VOA.FiniteHilbertSqueeze

universe u v w

variable {K : Type u} [DivisionRing K]
variable {A : Type v} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
variable {B : Type w} [AddCommGroup B] [Module K B] [FiniteDimensional K B]

/-- A surjection between finite-dimensional spaces is injective as soon as the source has no
larger dimension than the target.  In applications, surjectivity is the canonical Li map and the
displayed inequality is the carrier or normal-form bound. -/
theorem injective_of_surjective_of_finrank_le
    (f : A →ₗ[K] B) (hsurj : Function.Surjective f)
    (hle : Module.finrank K A ≤ Module.finrank K B) :
    Function.Injective f := by
  have hge : Module.finrank K B ≤ Module.finrank K A :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  have heq : Module.finrank K A = Module.finrank K B := le_antisymm hle hge
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).2 hsurj

/-- The same squeeze, packaged as bijectivity. -/
theorem bijective_of_surjective_of_finrank_le
    (f : A →ₗ[K] B) (hsurj : Function.Surjective f)
    (hle : Module.finrank K A ≤ Module.finrank K B) :
    Function.Bijective f :=
  ⟨injective_of_surjective_of_finrank_le f hsurj hle, hsurj⟩

/-- The linear equivalence produced by the finite-dimensional Hilbert squeeze. -/
noncomputable def linearEquivOfSurjectiveOfFinrankLE
    (f : A →ₗ[K] B) (hsurj : Function.Surjective f)
    (hle : Module.finrank K A ≤ Module.finrank K B) : A ≃ₗ[K] B :=
  LinearEquiv.ofBijective f (bijective_of_surjective_of_finrank_le f hsurj hle)

@[simp] theorem linearEquivOfSurjectiveOfFinrankLE_apply
    (f : A →ₗ[K] B) (hsurj : Function.Surjective f)
    (hle : Module.finrank K A ≤ Module.finrank K B) (a : A) :
    linearEquivOfSurjectiveOfFinrankLE f hsurj hle a = f a := rfl

/-- A finite sum of natural numbers detects equality in a pointwise inequality.

This is the basic weightwise Hilbert-squeeze lemma: `s` is the finite set of filtration degrees
occurring in one conformal weight. -/
theorem eqOn_of_pointwise_le_of_sum_eq {ι : Type*} (s : Finset ι) (c b : ι → ℕ)
    (hcb : ∀ i ∈ s, c i ≤ b i)
    (hsum : ∑ i ∈ s, c i = ∑ i ∈ s, b i) :
    ∀ i ∈ s, c i = b i := by
  intro i hi
  by_contra hne
  have hlt : c i < b i := lt_of_le_of_ne (hcb i hi) hne
  have hsumLt : ∑ j ∈ s, c j < ∑ j ∈ s, b j := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact hcb j hj
    · exact ⟨i, hi, hlt⟩
  exact (Nat.ne_of_lt hsumLt) hsum

/-- Weightwise three-term Hilbert squeeze over a finite set of filtration degrees.

Only equality of the *total* outside dimensions is assumed.  Thus a one-variable character
identity, together with pointwise carrier and quotient inequalities, recovers equality in every
filtration degree; no independently proved bigraded character identity is needed. -/
theorem pointwise_eq_of_sandwich_of_sum_eq {ι : Type*} (s : Finset ι)
    (c a b : ι → ℕ)
    (hca : ∀ i ∈ s, c i ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i)
    (hsum : ∑ i ∈ s, c i = ∑ i ∈ s, b i) :
    ∀ i ∈ s, c i = a i ∧ a i = b i := by
  have hcb : ∀ i ∈ s, c i ≤ b i := fun i hi => (hca i hi).trans (hab i hi)
  have houter : ∀ i ∈ s, c i = b i :=
    eqOn_of_pointwise_le_of_sum_eq s c b hcb hsum
  intro i hi
  exact ⟨le_antisymm (hca i hi) ((hab i hi).trans_eq (houter i hi).symm),
    le_antisymm (hab i hi) ((houter i hi).symm.le.trans (hca i hi))⟩

/-- Fintype adapter for `pointwise_eq_of_sandwich_of_sum_eq`.

This form is convenient when the Li degrees in a fixed conformal weight have already been packaged
as a finite type. -/
theorem pointwise_eq_of_fintype_sandwich_of_sum_eq {ι : Type*} [Fintype ι]
    (c a b : ι → ℕ) (hca : ∀ i, c i ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hsum : ∑ i, c i = ∑ i, b i) :
    ∀ i, c i = a i ∧ a i = b i := by
  classical
  intro i
  exact pointwise_eq_of_sandwich_of_sum_eq Finset.univ c a b
    (fun j _ => hca j) (fun j _ => hab j) hsum i (Finset.mem_univ i)

end VOA.FiniteHilbertSqueeze
