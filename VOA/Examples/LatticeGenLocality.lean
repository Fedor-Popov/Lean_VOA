/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenVertex

/-!
# Toward mutual locality `Local Y(e^α) Y(e^β)` of the general lattice VOA

The foundational commutativity bricks of the same-sign locality analysis (FLM Ch. 8; Gannon §5.2.2):
the two half-currents each self-commute across charges,
* `EminusVecField_comm` — the creation halves `E⁻(α,z₁), E⁻(β,z₂)` commute (they are polynomial
  multiplications; `mul_left_comm`);
* `EplusVecField_comm` — the annihilation halves `E⁺(α,z₁), E⁺(β,z₂)` commute (the charge
  annihilation modes `α(m), β(n)` commute for `m,n>0`: `[α(m),β(n)] = ⟨α,β⟩ m δ_{m+n,0} = 0`).

These are the cross-charge generalizations of A₁'s `Eminus_comm`/`Eplus_comm`, and are the inputs
to the symmetric normal-ordered four-fold operator `T` (the `Tv_symm` analog).  The remaining deep
crux of mutual locality is the FLM **reordering** `E⁺(β,z₁)E⁻(α,z₂) = (contraction)·E⁻(α,z₂)E⁺(β,z₁)` with
the `(z₁-z₂)^{⟨α,β⟩}` contraction factor (generalizing `Eplus_comp_Eminus`/`EEMaster`), plus the
**odd-`⟨α,β⟩` cocycle sign** `ε(α,β)ε(β,α) = (−1)^{⟨α,β⟩}` (`latticeCocycle_comm`).

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice)

/-! ## Creation–creation commutativity -/

/-- **The creation halves commute across charges**: `E⁻(α,z₁), E⁻(β,z₂)` commute, because both act
by polynomial multiplication (`mulLeft (vSchur …)`) and `FockN (rank L)` is commutative.  The
cross-charge generalization of A₁'s `Eminus_comm`. -/
theorem EminusVecField_comm (α β : L.carrier) (a b : ℤ) :
    (EminusVecField L α a).comp (EminusVecField L β b)
      = (EminusVecField L β b).comp (EminusVecField L α a) := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply]
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [EminusVecField_apply, if_pos ha, EminusVecField_apply, if_pos hb, EminusVec, EminusVec,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
        LinearMap.mulLeft_apply, mul_left_comm]
    · rw [EminusVecField_neg L β (show b < 0 by omega)]; simp
  · rw [EminusVecField_neg L α (show a < 0 by omega)]; simp

/-! ## Annihilation–annihilation commutativity -/

/-- **The charge annihilation modes commute**: `[α(m), β(n)] = 0` for `m,n ≥ 1` (since
`m + n > 0`, so the `δ_{m+n,0}` of `chargeOsc_comm` vanishes).  The vector generalization of A₁'s
`alpha_commute`. -/
theorem chargeOsc_commute (hPos : L.PosDef) (α β : L.carrier) {m n : ℤ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) : Commute (chargeOsc L α m) (chargeOsc L β n) := by
  have h := chargeOsc_comm L hPos α β m n
  rw [if_neg (by omega : ¬ m + n = 0), zero_smul, sub_eq_zero] at h
  exact h

/-- `E⁺(α)_{-N} = aExpVec α N` commutes with any positive charge mode `β(j+1)` (mirror
`aExp_commute_alpha`). -/
theorem aExpVec_commute_charge (hPos : L.PosDef) (α β : L.carrier) (N j : ℕ) :
    Commute (aExpVec L α N) (chargeOsc L β ((j : ℤ) + 1)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExpVec_zero]; exact Commute.one_left _
    | (M + 1) =>
      rw [aExpVec_succ]
      refine Commute.smul_left ?_ _
      refine Commute.sum_left _ _ _ (fun m hm => ?_)
      refine Commute.mul_left ?_ (ih (M - m) (by simp only [Finset.mem_range] at hm; omega))
      exact (chargeOsc_commute L hPos α β (by omega) (by omega)).neg_left

/-- **The annihilation halves commute across charges**: `aExpVec α M ∘ aExpVec β N = aExpVec β N ∘
aExpVec α M` (mirror `aExp_commute`). -/
theorem aExpVec_commute (hPos : L.PosDef) (α β : L.carrier) (M N : ℕ) :
    Commute (aExpVec L α M) (aExpVec L β N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExpVec_zero]; exact Commute.one_right _
    | (K + 1) =>
      rw [aExpVec_succ]
      refine Commute.smul_right ?_ _
      refine Commute.sum_right _ _ _ (fun m hm => ?_)
      refine Commute.mul_right ?_ (ih (K - m) (by simp only [Finset.mem_range] at hm; omega))
      exact (aExpVec_commute_charge L hPos α β M m).neg_right

/-- **The annihilation halves `E⁺(α,z₁), E⁺(β,z₂)` commute across charges** (cross-charge
generalization of A₁'s `Eplus_comm`). -/
theorem EplusVecField_comm (hPos : L.PosDef) (α β : L.carrier) (a b : ℤ) :
    (EplusVecField L α a).comp (EplusVecField L β b)
      = (EplusVecField L β b).comp (EplusVecField L α a) := by
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · rw [EplusVecField_nonpos L α ha, EplusVecField_nonpos L β hb]
      exact (aExpVec_commute L hPos α β _ _).eq
    · refine LinearMap.ext fun p => ?_
      simp only [LinearMap.comp_apply, EplusVecField_apply, if_neg hb, LinearMap.zero_apply,
        map_zero]
  · refine LinearMap.ext fun p => ?_
    simp only [LinearMap.comp_apply, EplusVecField_apply, if_neg ha, LinearMap.zero_apply,
      map_zero]

/-! ## The odd-pairing cocycle sign — the one genuinely-new ingredient of mutual locality

For A₁ the pairing `⟨mα,nα⟩ = 2mn` is always **even**, so the boson reordering `shift_comm_P` picks
up `(−1)^P = 1` and the two operator orders coincide with no sign.  For a general lattice `⟨α,β⟩`
can be **odd**, and then the boson part carries a `(−1)^{⟨α,β⟩} = −1`.  That sign is exactly
cancelled by the **cocycle asymmetry** of the vertex operators: `Y(e^α)Y(e^β)` and `Y(e^β)Y(e^α)`
differ by `ε(α,β)/ε(β,α) = (−1)^{⟨α,β⟩}` — so the boson sign and the cocycle sign multiply to `+1`
and locality holds.  This is the FLM mechanism that A₁ never exhibits. -/

/-- **The cocycle swap sign** `ε(α,β) = (−1)^{⟨α,β⟩}·ε(β,α)` — the key sign that makes
`Y(e^α), Y(e^β)` mutually local for **odd** `⟨α,β⟩`.  From `latticeCocycle_comm`
(`ε(α,β)ε(β,α) = (−1)^{⟨α,β⟩}`) and `latticeCocycle_sq` (`ε(β,α)² = 1`). -/
theorem latticeCocycle_swap_sign (hEven : L.Even) (α β : L.carrier) :
    latticeCocycle L α β = (-1 : ℂ) ^ (L.form α β) * latticeCocycle L β α := by
  have hcomm := latticeCocycle_comm L hEven α β
  have hsq := latticeCocycle_sq L β α
  calc latticeCocycle L α β
      = latticeCocycle L α β * (latticeCocycle L β α * latticeCocycle L β α) := by rw [hsq, mul_one]
    _ = (latticeCocycle L α β * latticeCocycle L β α) * latticeCocycle L β α := by ring
    _ = (-1 : ℂ) ^ (L.form α β) * latticeCocycle L β α := by rw [hcomm]

/-! ## The symmetric normal-ordered four-fold operator -/

/-- The fully normal-ordered **symmetric four-fold operator** `T_{α,β}(C,D) =
E⁻(α,z₁)E⁻(β,z₂)E⁺(α,z₁)E⁺(β,z₂)` applied to a vector (a single `finsum` over `ℤ × ℤ`).  The
cross-charge generalization of A₁'s `Tv`. -/
noncomputable def TvVec (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) : FockN (rank L) :=
  ∑ᶠ pq : ℤ × ℤ, EminusVecField L α pq.1 (EminusVecField L β pq.2
    (EplusVecField L α (C - pq.1) (EplusVecField L β (D - pq.2) x)))

/-- **`T` is symmetric** under swapping the two charge/mode pairs: `T_{α,β}(C,D) = T_{β,α}(D,C)`
(swap the summation pair `Prod.swap` via `finsum_comp_equiv`, then the half-current
commutativities).  The cross-charge generalization of A₁'s `Tv_symm`. -/
theorem TvVec_symm (hPos : L.PosDef) (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    TvVec L α β C D x = TvVec L β α D C x := by
  rw [TvVec, TvVec, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
    (f := fun pq : ℤ × ℤ => EminusVecField L β pq.1 (EminusVecField L α pq.2
      (EplusVecField L β (D - pq.1) (EplusVecField L α (C - pq.2) x))))]
  refine finsum_congr fun pq => ?_
  obtain ⟨p, q⟩ := pq
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  have hE : ∀ Y, EminusVecField L α p (EminusVecField L β q Y)
      = EminusVecField L β q (EminusVecField L α p Y) := fun Y => by
    have := DFunLike.congr_fun (EminusVecField_comm L α β p q) Y
    simpa [LinearMap.comp_apply] using this
  have hP : ∀ x', EplusVecField L α (C - p) (EplusVecField L β (D - q) x')
      = EplusVecField L β (D - q) (EplusVecField L α (C - p) x') := fun x' => by
    have := DFunLike.congr_fun (EplusVecField_comm L hPos α β (C - p) (D - q)) x'
    simpa [LinearMap.comp_apply] using this
  rw [hE, hP]

end VOA.LatGen
