/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFockGramTransfer
import VOA.Examples.VirasoroKacRootBootstrap

/-!
# General actual Kac roots from integer screenings

At every positive square parameter the finite, nonzero screening polynomial
is an actual Fock singular state. The proved representation transfer makes
this a zero of the actual Verma Gram determinant. Positive squares supply
infinitely many distinct parameters; Laurent interpolation then proves the
root identity at every nonzero complex parameter, for all positive labels.
-/
namespace VOA.VirasoroScreening
open HeisenbergN InverseDS.VirasoroVerma
open scoped Classical
set_option maxHeartbeats 1200000

/-- The screening background realizes the usual Kac central charge at
parameter beta squared. This fixes the free-field normalization explicitly. -/
theorem screening_central_charge (β : ℚ) (hβ : β ≠ 0) :
    1-24*(screeningBackground β : ℂ)^2 = vermaBSACharge ((β:ℂ)^2) := by
  have hb : (β:ℂ) ≠ 0 := by exact_mod_cast hβ
  unfold screeningBackground vermaBSACharge
  push_cast
  field_simp
  <;> ring

/-- The charged Fock vacuum has exactly the positive-label Kac highest
weight; the screening polynomial lies rs levels above that vacuum. -/
theorem screening_highest_weight (r s : ℕ) (β : ℚ) (hβ : β ≠ 0) :
    (screeningMomentum r s β : ℂ)^2 -
      2*(screeningBackground β : ℂ)*(screeningMomentum r s β : ℂ) =
        fusionKacWeight r s ((β:ℂ)^2) := by
  have hb : (β:ℂ) ≠ 0 := by exact_mod_cast hβ
  unfold screeningMomentum screeningBackground fusionKacWeight
  push_cast
  field_simp
  <;> ring

/-- Every positive integer square is an ACTUAL Verma Gram root for every
pair of positive Kac labels. Nonvanishing and both Ward equations come from
the finite screening construction, not an assumed Kac determinant formula. -/
theorem integer_screening_kac_root (r s m : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hm : 0 < m) :
    (vermaGramMatrix (vermaBSACharge ((m:ℂ)^2))
      (fusionKacWeight r s ((m:ℂ)^2)) (r*s)).det = 0 := by
  obtain ⟨hne,hgrade,h1,h2⟩ := integer_screening_nonzero_singular r s m hr hm
  have hh := chargedFock_singular_gram_root (screeningBackground (m:ℚ))
    (screeningMomentum r s (m:ℚ)) (r*s) (Nat.mul_pos hr hs)
    (screeningFockState r s (m^2) (m:ℚ)) hgrade hne h1 h2
  have hm' : (m:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [screening_central_charge _ hm', screening_highest_weight _ _ _ hm'] at hh
  simpa only [Rat.cast_natCast] using hh

/-- The positive squares form an infinite set of distinct nonzero complex
parameters, and every one is an actual root for any fixed positive labels. -/
theorem infinite_integer_screening_roots (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∃ S : Set ℂ, S.Infinite ∧ (∀ t ∈ S, t ≠ 0) ∧
      ∀ t ∈ S, (vermaGramMatrix (vermaBSACharge t)
        (fusionKacWeight r s t) (r*s)).det = 0 := by
  let f : ℕ → ℂ := fun m => ((m+1:ℕ):ℂ)^2
  refine ⟨Set.range f, Set.infinite_range_of_injective ?_, ?_, ?_⟩
  · intro i j he
    dsimp [f] at he
    have hn : (i+1)^2 = (j+1)^2 := by exact_mod_cast he
    nlinarith
  · rintro t ⟨m,rfl⟩
    apply pow_ne_zero
    exact_mod_cast (Nat.succ_ne_zero m)
  · rintro t ⟨m,rfl⟩
    exact integer_screening_kac_root r s (m+1) hr hs (by omega)

/-- The general ACTUAL Kac root identity, at every nonzero complex
parameter and every pair of positive labels. Laurent interpolation extends
the constructed integer-screening roots without assuming a dense sample. -/
theorem screening_kac_root (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (t : ℂ) (ht : t ≠ 0) :
    (vermaGramMatrix (vermaBSACharge t) (fusionKacWeight r s t) (r*s)).det = 0 := by
  obtain ⟨S,hS,hne,hroots⟩ := infinite_integer_screening_roots r s hr hs
  exact kacGram_root_of_infinite r s (r*s) S hS hne hroots t ht

/-- Genuine nonzero singular Verma states at ALL positive Kac labels on
nonreal parameters. Level induction and the actual roots prove existence;
this does not infer it from uniqueness or from possibly zero fusion outputs. -/
theorem screening_nonreal_kac_singular (t : ℂ) (ht : t.im ≠ 0)
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∃ v : sortedSpan (vermaBSACharge t) (fusionKacWeight r s t) (r*s),
      v ≠ 0 ∧ vermaMode (vermaBSACharge t) (fusionKacWeight r s t) 1 v = 0 ∧
        vermaMode (vermaBSACharge t) (fusionKacWeight r s t) 2 v = 0 := by
  apply verma_singular_of_nonreal_kac_roots t ht (r*s) ?_ r s hr hs le_rfl
  intro a b ha hb _
  exact screening_kac_root a b ha hb t (by intro he; apply ht; simp [he])

end VOA.VirasoroScreening
