/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BoundaryWakimotoPDE
import VOA.Filtered.AffineSl2WakimotoLiBridge
import VOA.Examples.AffineSl2BoundaryRelationBridge

/-!
# Nonvanishing of the boundary singular vector's C2 symbol

The charge-one Wakimoto differential equations force a depth-zero monomial.
Faithfulness and Li compatibility of the actual Wakimoto map therefore prove
that every boundary candidate has nonzero C2 image. No maximal-generation or
classical-symbol nonvanishing hypothesis is used.
-/
namespace VOA.AffineSl2BoundarySingularFamily
open VertexOperatorAlgebra AffineVOA AffineVOA.Inst AffineVOA.Strong
open AffineSl2BoundaryC2 QuasiLisseSl2 Sl2Pres Sl2Symbol
open AffineSl2PBWWakimotoReduction AffineSl2WakimotoLiLeading
open AffineSl2GeneralRigidity MvPolynomial
noncomputable section

private theorem coeff_zero_of_freeLiAtLeast {P : Wak.WakFock} {p : ℕ}
    (hP : P ∈ freeLiAtLeast p) (d : Fin 3 × ℕ →₀ ℕ)
    (hd : Finsupp.weight freeLiWeight d < p) : coeff d P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨e, he, rfl⟩ := hP
    have hne : e ≠ d := by intro hh; subst e; omega
    simp [coeff_monomial, hne]
  | zero => simp
  | add P Q _ _ hP hQ => simp [hP, hQ]
  | smul c P _ hP => simp [hP]

/-- Actual affine highest vectors of horizontal weight two have nonzero C2
symbol at every noncritical level. This specializes the general AJM
nonvanishing phenomenon to the boundary family needed here. -/
theorem charge_two_highest_symbol_ne_zero (k : ℂ) (hk : k+2 ≠ 0)
    (x : WakModule k) (hne : x ≠ 0)
    (hE : J k colE 0 x = 0) (hH : J k colH 0 x = (2 : ℂ) • x)
    (hpos : SingP k x) :
    mk₂ (affineSl2VOA_closed k hk) x ≠ 0 := by
  let P := vacuumToWak k hk x
  have hPn : P ≠ 0 := fun hh => hne ((vacuumToWak_injective k hk)
    (by simpa [P] using hh))
  have hgamma : P ∈ Wak.Screening.gammaFree := by
    intro j
    have he : J k colE (j : ℤ) x = 0 := by
      by_cases hj : j = 0
      · simpa [hj] using hE
      · exact hpos colE (j : ℤ) (by omega)
    have hh := congrArg (vacuumToWak k hk) he
    rw [vacuumToWak_J, map_zero] at hh
    simpa [P, colE, Wak.Jw_E, Wak.Ecur, Wak.Bet_of_nonneg (Int.natCast_nonneg j),
      Wak.cD_of_nonneg (Int.natCast_nonneg j), Wak.dV_apply] using hh
  have hcharge : Wak.Dch P = P := by
    have hh := congrArg (vacuumToWak k hk) hH
    rw [vacuumToWak_J, map_smul] at hh
    change Wak.Jw k 2 0 P = (2 : ℂ) • P at hh
    rw [Wak.Jw_H, Wak.Screening.Hcur_zero_eq, LinearMap.smul_apply] at hh
    exact (smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0)) hh
  have hcartan : ∀ n : ℕ, 0 < n → Wak.Hcur k (n : ℤ) P = 0 := by
    intro n hn
    have hh := congrArg (vacuumToWak k hk) (hpos colH (n : ℤ) (by omega))
    rw [vacuumToWak_J, map_zero] at hh
    change Wak.Jw k 2 (n : ℤ) P = 0 at hh
    rwa [Wak.Jw_H] at hh
  obtain ⟨d, hd⟩ := Wak.BoundaryPDE.exists_depth_zero_coefficient
    k hk P hgamma hcharge hcartan hPn
  intro hz
  have hx : x ∈ O₂ (AffineSl2GeneralRigidity.universal k hk) :=
    (mk₂_eq_zero_iff _).mp hz
  have hli := vacuumToWak_mem_freeLiAtLeast_one_of_mem_O₂ k hk hx
  exact hd (coeff_zero_of_freeLiAtLeast hli _ (by simp [Finsupp.weight_single, freeLiWeight]))

/-- The nonvanishing hypothesis in the harmonic-symbol classification is
proved from the boundary candidate's actual highest-vector equations. -/
theorem Candidate.symbol_ne_zero {k : ℂ} {n : ℕ} (C : Candidate k n) :
    mk₂ (affineSl2VOA_closed k C.noncritical) C.vector ≠ 0 :=
  charge_two_highest_symbol_ne_zero k C.noncritical C.vector C.nonzero
    C.horizontalRaising C.horizontalCharge C.positiveSingular

/-- Every actual boundary candidate has the claimed nonzero harmonic symbol. -/
theorem Candidate.exists_highestSymbol {k : ℂ} {n : ℕ} (C : Candidate k n) :
    ∃ c : ℂ, c ≠ 0 ∧ mk₂ (affineSl2VOA_closed k C.noncritical) C.vector =
      c • symbolAlg k C.noncritical
        (eSym * casSym ^ n) :=
  C.exists_highestSymbol_of_symbol_ne_zero C.symbol_ne_zero

/-- The boundary source relations hold for every actual candidate, without an
additional classical-symbol or maximal-generation assumption. -/
theorem Candidate.boundaryIdeal_le_kernel {k : ℂ} {n : ℕ} (C : Candidate k n) :
    AffineSl2BoundaryC2.boundaryIdeal n ≤
      RingHom.ker (simpleSymbol C) :=
  C.boundaryIdeal_le_kernel_of_symbol_ne_zero C.symbol_ne_zero

/-- The boundary presentation maps onto the actual simple C2 algebra with
all relation hypotheses discharged. -/
def Candidate.boundaryC2Surjection {k : ℂ} {n : ℕ} (C : Candidate k n) :
    (SymSl2 ⧸ boundaryIdeal n) →ₐ[ℂ]
      A₂ (QuotVOA.maxQuotientVOA (affineSl2VOA_closed k C.noncritical)) :=
  boundaryC2Map C C.boundaryIdeal_le_kernel

theorem Candidate.boundaryC2Surjection_surjective {k : ℂ} {n : ℕ}
    (C : Candidate k n) : Function.Surjective C.boundaryC2Surjection :=
  boundaryC2Map_surjective C C.boundaryIdeal_le_kernel

/-- The uniform determinant-constructed primitive gives the genuine boundary
relation inclusion for every positive boundary index. -/
theorem uniform_boundaryIdeal_le_kernel (n : ℕ) (hn : 1 ≤ n) :
    boundaryIdeal n ≤ RingHom.ker (simpleSymbol (uniformCandidate n hn)) :=
  (uniformCandidate n hn).boundaryIdeal_le_kernel

end
end VOA.AffineSl2BoundarySingularFamily
