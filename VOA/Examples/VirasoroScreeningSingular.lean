/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningModeCoefficients
import VOA.Examples.VirasoroChargedFockGrading

/-!
# Genuine nonzero integer-screening singular Fock states

The residue Ward identities kill the actual first two charged Virasoro
modes of the finite screening polynomial. The zero-mode grading argument
handles every other coefficient, including output energies below zero.
Nonvanishing is inherited from the proved finite Vandermonde moment.
These are actual Fock singular states; transfer to a Verma Gram root is a
separate representation-theoretic step.
-/
namespace VOA.VirasoroScreening
open HeisenbergN MvPolynomial
open InverseDS.LeeYangFockVirasoro

/-- Restoring the unique colour also recovers every actual Fock occupation. -/
theorem fock_plainOccupation (d : (ℕ × Fin 1) →₀ ℕ) :
    fockOccupation (plainOccupation d) = d := by
  simp only [plainOccupation, fockOccupation, ← Finsupp.mapDomain_comp]
  have he : (fun i : ℕ => (i, (0:Fin 1))) ∘ Prod.fst =
      (id : ℕ × Fin 1 → ℕ × Fin 1) := by
    funext ⟨i,a⟩
    simp only [Function.comp_apply, id_eq]
    congr 1
    exact Subsingleton.elim _ _
  rw [he]
  exact Finsupp.mapDomain_id

/-- Background charge corresponding to a nonzero screening parameter beta. -/
def screeningBackground (β : ℚ) : ℚ := (β - 1/β)/2

/-- Momentum of the output Fock sector for the r-fold screening at level rs. -/
def screeningMomentum (r s : ℕ) (β : ℚ) : ℚ :=
  screeningBackground β + ((r:ℚ)*β - (s:ℚ)/β)/2

/-- The first actual charged-mode scalar equals the first residue coefficient. -/
theorem screening_first_charge (r s : ℕ) (β : ℚ) (hβ : β ≠ 0) :
    2*β*(screeningMomentum r s β - 2*screeningBackground β) =
      ((r:ℚ)-1)*β^2 + 1 - (s:ℚ) := by
  unfold screeningMomentum screeningBackground
  field_simp
  <;> ring

/-- The second charged-mode scalar equals the signed second residue coefficient,
including the negative rank-one contribution. -/
theorem screening_second_charge (r s : ℕ) (β : ℚ) (hβ : β ≠ 0) :
    2*β*(screeningMomentum r s β - 3*screeningBackground β) =
      ((r:ℚ)-2)*β^2 + 2 - (s:ℚ) := by
  unfold screeningMomentum screeningBackground
  field_simp
  <;> ring

/-- The ACTUAL first charged Virasoro mode annihilates the finite screening
state whenever beta squared is the integer Vandermonde parameter. -/
theorem screeningFockState_L1_zero (r s t : ℕ) (hr : 0 < r) (β : ℚ)
    (hβ : β ≠ 0) (ht : β^2 = (t:ℚ)) :
    sectorVirasoro (screeningBackground β : ℂ) (screeningMomentum r s β : ℂ) 1
      (screeningFockState r s t β) = 0 := by
  apply MvPolynomial.ext
  intro e
  rw [coeff_zero, ← fock_plainOccupation e]
  let d := plainOccupation e
  change coeff (fockOccupation d) _ = 0
  by_cases hd : Finsupp.weight (fun k => k+1) d + 1 = r*s
  · rw [screeningFockState_L1_coefficient r s t β _ _ d hd]
    norm_cast
    rw [screening_first_charge r s β hβ, ht, screeningFunctional_first_ward r s t hr,
      mul_zero]
  · have h := chargedFock_mode_coeff_zero (screeningBackground β : ℂ)
      (screeningMomentum r s β : ℂ) 1 (r*s) (screeningFockState r s t β)
      (screeningFockState_mem_grade r s t β) (fockOccupation d)
      (by simpa only [fockOccupation_weight] using hd)
    simpa only [Nat.cast_one] using h

/-- The ACTUAL second charged Virasoro mode also annihilates the finite
state, including the low-energy truncation case rs<2. -/
theorem screeningFockState_L2_zero (r s t : ℕ) (hr : 0 < r) (β : ℚ)
    (hβ : β ≠ 0) (ht : β^2 = (t:ℚ)) :
    sectorVirasoro (screeningBackground β : ℂ) (screeningMomentum r s β : ℂ) 2
      (screeningFockState r s t β) = 0 := by
  apply MvPolynomial.ext
  intro e
  rw [coeff_zero, ← fock_plainOccupation e]
  let d := plainOccupation e
  change coeff (fockOccupation d) _ = 0
  by_cases hd : Finsupp.weight (fun k => k+1) d + 2 = r*s
  · rw [screeningFockState_L2_coefficient r s t β _ _ d hd]
    norm_cast
    rw [screening_second_charge r s β hβ, ht, screeningFunctional_second_ward r s t hr,
      mul_zero]
  · have h := chargedFock_mode_coeff_zero (screeningBackground β : ℂ)
      (screeningMomentum r s β : ℂ) 2 (r*s) (screeningFockState r s t β)
      (screeningFockState_mem_grade r s t β) (fockOccupation d)
      (by simpa only [fockOccupation_weight] using hd)
    simpa only [Nat.cast_ofNat] using h

/-- At EVERY positive integer square parameter the explicitly defined
screening polynomial is nonzero, has energy rs, and is killed by both actual
positive generators. No singularity or nonvanishing premise is assumed. -/
theorem integer_screening_nonzero_singular (r s m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    screeningFockState r s (m^2) (m:ℚ) ≠ 0 ∧
    screeningFockState r s (m^2) (m:ℚ) ∈ gradingWN 1 (r*s) ∧
    sectorVirasoro (screeningBackground (m:ℚ) : ℂ)
      (screeningMomentum r s (m:ℚ) : ℂ) 1 (screeningFockState r s (m^2) (m:ℚ)) = 0 ∧
    sectorVirasoro (screeningBackground (m:ℚ) : ℂ)
      (screeningMomentum r s (m:ℚ) : ℂ) 2 (screeningFockState r s (m^2) (m:ℚ)) = 0 := by
  have hβ : (m:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have ht : (m:ℚ)^2 = ((m^2:ℕ):ℚ) := by norm_cast
  exact ⟨screeningFockState_ne_zero r s (m^2) hβ,
    screeningFockState_mem_grade r s (m^2) (m:ℚ),
    screeningFockState_L1_zero r s (m^2) hr (m:ℚ) hβ ht,
    screeningFockState_L2_zero r s (m^2) hr (m:ℚ) hβ ht⟩

end VOA.VirasoroScreening
