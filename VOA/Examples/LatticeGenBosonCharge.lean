/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenBosonFields

/-!
# Boson ↔ charge locality `Local (α^a(z)) (Y(e^α,z))`

The boson current `α^a(z)` and the charge vertex operator `Y(e^α,z)` are mutually local (bound `1`):
`[α^a(z₁), Y(e^α,z₂)] = chargeCoord α a · Y(e^α,z₂)` — a simple pole whose residue is the
direction-`a` charge of `α`.  The direction-`a` current contracts with the boson dressing `EEVec α`
(residue `chargeCoord α a`), and the zero-mode momentum `α^a₀` supplies the same charge on the
`z₁⁻¹`-coefficient; the two combine to the clean `δ`-commutator.  Cross-charge lift of A₁'s
`LatticeGeneralLocality` §12–15.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice)

/-- Operator Leibniz on `FockN (rank L)` vectors: `f(g(h x)) - g(h(f x)) = [f,g](h x) + g([f,h]x)`. -/
theorem leibniz_vecGen (f g h : End ℂ (FockN (rank L))) (x : FockN (rank L)) :
    f (g (h x)) - g (h (f x)) = (f * g - g * f) (h x) + g ((f * h - h * f) x) := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub]; abel

/-- `chargeOsc α m = ∑_b chargeCoord α b • α^b(m)` (folding the frame coordinates into `chargeCoord`). -/
theorem chargeOsc_eq_sum (α : L.carrier) (m : ℤ) :
    chargeOsc L α m = ∑ b, chargeCoord L α b • oscN (rank L) 1 b m := rfl

/-- **The single-direction current / charge commutator** `[α^a(m), chargeOsc β(n)]`: only the `b=a`
term of `chargeOsc β = ∑_b chargeCoord β b · α^b` survives (orthonormal `δ^{ab}`), leaving the
residue `chargeCoord β a · m · δ_{m+n,0}`. -/
theorem oscN_chargeOsc_comm (a : Fin (rank L)) (β : L.carrier) (m n : ℤ) :
    oscN (rank L) 1 a m * chargeOsc L β n - chargeOsc L β n * oscN (rank L) 1 a m
      = (if m + n = 0 then chargeCoord L β a * (m : ℂ) else 0) • LinearMap.id := by
  rw [chargeOsc_eq_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  rw [show (∑ b, (oscN (rank L) 1 a m * (chargeCoord L β b • oscN (rank L) 1 b n)
          - (chargeCoord L β b • oscN (rank L) 1 b n) * oscN (rank L) 1 a m))
      = ∑ b, chargeCoord L β b • (if a = b ∧ m + n = 0 then (m : ℂ) * 1 else 0) • LinearMap.id from
    Finset.sum_congr rfl fun b _ => by
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, oscN_comm]]
  rw [Finset.sum_eq_single a]
  · by_cases hmn : m + n = 0
    · rw [if_pos ⟨rfl, hmn⟩, if_pos hmn, mul_one, smul_smul]
    · rw [if_neg (fun h => hmn h.2), if_neg hmn]; simp
  · intro b _ hba
    rw [if_neg (fun h => hba h.1.symm)]; simp
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **The E⁺ creation-mode contraction** `α^a(-k) ∘ E⁺(β)ℤ_M = E⁺(β)ℤ_M ∘ α^a(-k)
+ chargeCoord β a · E⁺(β)ℤ_{M-k}` (`1 ≤ k`).  Strong induction on `M.toNat` via the `aExpVecZ`
Newton recursion; the residue tracks the single-direction charge `chargeCoord β a`.  Cross-charge
lift of A₁'s `alphaNeg_comp_aExpZ`. -/
theorem oscNeg_comp_aExpVecZ (a : Fin (rank L)) (β : L.carrier) (k : ℕ) (hk : 1 ≤ k) :
    ∀ M : ℤ, (oscN (rank L) 1 a (-(k : ℤ))).comp (aExpVecZ L β M)
      = (aExpVecZ L β M).comp (oscN (rank L) 1 a (-(k : ℤ)))
        + chargeCoord L β a • aExpVecZ L β (M - k) := by
  have hmove : ∀ m : ℕ, (oscN (rank L) 1 a (-(k : ℤ))).comp (-(chargeOsc L β ((m : ℤ) + 1)))
      = (-(chargeOsc L β ((m : ℤ) + 1))).comp (oscN (rank L) 1 a (-(k : ℤ)))
        + (if (m : ℤ) + 1 = (k : ℤ) then chargeCoord L β a * (k : ℂ) else 0) • LinearMap.id := by
    intro m
    have hAB := sub_eq_iff_eq_add'.mp (oscN_chargeOsc_comm L a β (-(k : ℤ)) ((m : ℤ) + 1))
    rw [LinearMap.comp_neg, LinearMap.neg_comp,
      show (oscN (rank L) 1 a (-(k : ℤ))).comp (chargeOsc L β ((m : ℤ) + 1))
          = oscN (rank L) 1 a (-(k : ℤ)) * chargeOsc L β ((m : ℤ) + 1) from rfl,
      show (chargeOsc L β ((m : ℤ) + 1)).comp (oscN (rank L) 1 a (-(k : ℤ)))
          = chargeOsc L β ((m : ℤ) + 1) * oscN (rank L) 1 a (-(k : ℤ)) from rfl, hAB]
    by_cases hc : (m : ℤ) + 1 = (k : ℤ)
    · rw [if_pos (show -(k : ℤ) + ((m : ℤ) + 1) = 0 by omega), if_pos hc]
      push_cast; module
    · rw [if_neg (show ¬ (-(k : ℤ) + ((m : ℤ) + 1) = 0) by omega), if_neg hc]; simp
  suffices H : ∀ n : ℕ, ∀ M : ℤ, M.toNat ≤ n →
      (oscN (rank L) 1 a (-(k : ℤ))).comp (aExpVecZ L β M)
        = (aExpVecZ L β M).comp (oscN (rank L) 1 a (-(k : ℤ)))
          + chargeCoord L β a • aExpVecZ L β (M - k) by
    exact fun M => H M.toNat M le_rfl
  intro n
  induction n with
  | zero =>
    intro M hM
    by_cases h0 : M = 0
    · subst h0
      rw [aExpVecZ_zero, LinearMap.comp_id, LinearMap.id_comp,
        aExpVecZ_neg L β (show (0 : ℤ) - k < 0 by omega), smul_zero, add_zero]
    · rw [aExpVecZ_neg L β (by omega : M < 0), aExpVecZ_neg L β (show M - k < 0 by omega),
        LinearMap.comp_zero, LinearMap.zero_comp, smul_zero, add_zero]
  | succ n ih =>
    intro M hM
    by_cases hsmall : M.toNat ≤ n
    · exact ih M hsmall
    · have hM1 : 1 ≤ M := by omega
      have hMne : (M : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      conv_lhs => rw [aExpVecZ_recursion L β M hM1]
      rw [LinearMap.comp_smul, comp_sum']
      have hterm : ∀ m ∈ Finset.range M.toNat,
          (oscN (rank L) 1 a (-(k : ℤ))).comp
              ((-(chargeOsc L β ((m : ℤ) + 1))).comp (aExpVecZ L β (M - 1 - m)))
            = (-(chargeOsc L β ((m : ℤ) + 1))).comp
                ((aExpVecZ L β (M - 1 - m)).comp (oscN (rank L) 1 a (-(k : ℤ))))
              + chargeCoord L β a • (-(chargeOsc L β ((m : ℤ) + 1))).comp
                  (aExpVecZ L β ((M - k) - 1 - m))
              + (if (m : ℤ) + 1 = (k : ℤ) then chargeCoord L β a * (k : ℂ) else 0)
                • aExpVecZ L β (M - 1 - m) := by
        intro m _
        rw [← LinearMap.comp_assoc, hmove m, LinearMap.add_comp, LinearMap.comp_assoc,
          ih (M - 1 - m) (by omega)]
        simp only [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.smul_comp,
          LinearMap.id_comp]
        rw [show M - 1 - (m : ℤ) - k = (M - k) - 1 - m from by ring]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hcol1 : (∑ m ∈ Finset.range M.toNat,
            (-(chargeOsc L β ((m : ℤ) + 1))).comp
              ((aExpVecZ L β (M - 1 - m)).comp (oscN (rank L) 1 a (-(k : ℤ)))))
          = (M : ℂ) • ((aExpVecZ L β M).comp (oscN (rank L) 1 a (-(k : ℤ)))) := by
        simp only [← LinearMap.comp_assoc, ← sum_comp',
          aExpVecZ_sum_reassembly L β M M.toNat le_rfl, LinearMap.smul_comp]
      have hcol2 : (∑ m ∈ Finset.range M.toNat,
            chargeCoord L β a • (-(chargeOsc L β ((m : ℤ) + 1))).comp
              (aExpVecZ L β ((M - k) - 1 - m)))
          = chargeCoord L β a • (((M - k : ℤ) : ℂ) • aExpVecZ L β (M - k)) := by
        rw [← Finset.smul_sum, aExpVecZ_sum_reassembly L β (M - k) M.toNat (by omega)]
      have hcol3 : (∑ m ∈ Finset.range M.toNat,
            (if (m : ℤ) + 1 = (k : ℤ) then chargeCoord L β a * (k : ℂ) else 0)
              • aExpVecZ L β (M - 1 - m))
          = (chargeCoord L β a * (k : ℂ)) • aExpVecZ L β (M - k) := by
        by_cases hkM : k ≤ M.toNat
        · rw [Finset.sum_eq_single (k - 1)]
          · rw [if_pos (by omega), show M - 1 - ((k : ℕ) - 1 : ℕ) = M - k from by
                rw [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 from by omega]; ring]
          · intro b _ hb; rw [if_neg (by omega), zero_smul]
          · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
        · rw [aExpVecZ_neg L β (show M - k < 0 by omega), smul_zero]
          refine Finset.sum_eq_zero fun m hm => ?_
          simp only [Finset.mem_range] at hm
          rw [if_neg (by omega), zero_smul]
      rw [hcol1, hcol2, hcol3, inv_smul_eq_iff₀ hMne]
      push_cast
      module

/-! ## §2  The field-level boson OPE `[α^a(z₁), E⁻(α,z₂)]`. -/

/-- Positive-mode current contraction with the creation half `E⁻` (field index `t`). -/
theorem oscN_pos_comp_EminusVecField (a : Fin (rank L)) (α : L.carrier) {m : ℕ} (hm : 1 ≤ m)
    (t : ℤ) :
    (oscN (rank L) 1 a (m : ℤ)).comp (EminusVecField L α t)
      = (EminusVecField L α t).comp (oscN (rank L) 1 a (m : ℤ))
        + chargeCoord L α a • EminusVecField L α (t - m) := by
  by_cases ht : 0 ≤ t
  · rw [EminusVecField_apply, if_pos ht, oscN_comp_EminusVec L α a m t.toNat hm]
    congr 1
    by_cases hmN : m ≤ t.toNat
    · rw [if_pos hmN, EminusVecField_apply, if_pos (by omega : (0 : ℤ) ≤ t - m),
        show (t - (m : ℤ)).toNat = t.toNat - m from by omega]
    · rw [if_neg hmN, EminusVecField_apply, if_neg (by omega : ¬ (0 : ℤ) ≤ t - m), smul_zero]
  · rw [EminusVecField_apply, if_neg ht, LinearMap.comp_zero, LinearMap.zero_comp,
      EminusVecField_apply, if_neg (by omega : ¬ (0 : ℤ) ≤ t - m), smul_zero, add_zero]

/-- Negative-mode (creation) current commutes with `E⁻` (both left-multiplications on `FockN`). -/
theorem oscN_neg_comp_EminusVecField (a : Fin (rank L)) (α : L.carrier) {m : ℤ} (hm : m < 0)
    (t : ℤ) :
    (oscN (rank L) 1 a m).comp (EminusVecField L α t)
      = (EminusVecField L α t).comp (oscN (rank L) 1 a m) := by
  refine LinearMap.ext fun q => ?_
  rw [EminusVecField_apply]
  split_ifs with ht
  · simp only [LinearMap.comp_apply, EminusVec, LinearMap.mulLeft_apply,
      oscN_apply_neg (rank L) 1 a hm]
    ring
  · simp

/-- **The field-level boson OPE `[α^a(z₁), E⁻(α,z₂)]`**: coefficient `chargeCoord α a · E⁻(α)_{t+j+1}`
for `j ≤ -2`, else `0`. -/
theorem alphaFieldGen_comm_EminusVecField (a : Fin (rank L)) (α : L.carrier) (j t : ℤ) :
    bracketDist (currentN (rank L) 1 a) (EminusVecField L α) j t
      = if j ≤ -2 then chargeCoord L α a • EminusVecField L α (t + j + 1) else 0 := by
  rw [bracketDist_apply, currentN_apply]
  change (oscN (rank L) 1 a (-j - 1)).comp (EminusVecField L α t)
      - (EminusVecField L α t).comp (oscN (rank L) 1 a (-j - 1)) = _
  by_cases hj : j ≤ -2
  · rw [if_pos hj]
    have hmval : ((-j - 1).toNat : ℤ) = -j - 1 := Int.toNat_of_nonneg (by omega)
    have hm1 : 1 ≤ (-j - 1).toNat := by omega
    rw [show (-j - 1 : ℤ) = ((-j - 1).toNat : ℤ) from hmval.symm,
      oscN_pos_comp_EminusVecField L a α hm1 t,
      show t - ((-j - 1).toNat : ℤ) = t + j + 1 from by rw [hmval]; ring]
    abel
  · rw [if_neg hj]
    rcases (show -j - 1 < 0 ∨ -j - 1 = 0 from by omega) with hlt | heq
    · rw [oscN_neg_comp_EminusVecField L a α hlt t, sub_self]
    · rw [heq, oscN_zero, LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]

/-! ## §3  The field-level boson OPE `[α^a(z₁), E⁺(α,z₂)]`. -/

/-- The charge current and a single positive direction mode commute (both positive, `m+p ≠ 0`). -/
theorem chargeOsc_commute_oscN (β : L.carrier) (a : Fin (rank L)) {m p : ℤ} (hm : 1 ≤ m)
    (hp : 1 ≤ p) : Commute (chargeOsc L β m) (oscN (rank L) 1 a p) := by
  have h := oscN_chargeOsc_comm L a β p m
  rw [if_neg (by omega : ¬ p + m = 0), zero_smul, sub_eq_zero] at h
  exact h.symm

/-- `E⁺(β) = aExpVec β N` commutes with any positive single-direction mode `α^a(p)`. -/
theorem aExpVec_commute_oscN (β : L.carrier) (a : Fin (rank L)) (N : ℕ) {p : ℤ} (hp : 1 ≤ p) :
    Commute (aExpVec L β N) (oscN (rank L) 1 a p) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExpVec_zero]; exact Commute.one_left _
    | (M + 1) =>
      rw [aExpVec_succ]
      refine Commute.smul_left ?_ _
      refine Commute.sum_left _ _ _ (fun m hm => ?_)
      refine Commute.mul_left ?_ (ih (M - m) (by simp only [Finset.mem_range] at hm; omega))
      exact (chargeOsc_commute_oscN L β a (by omega) hp).neg_left

theorem aExpVecZ_commute_oscPos (β : L.carrier) (a : Fin (rank L)) (M : ℤ) {p : ℤ} (hp : 1 ≤ p) :
    Commute (aExpVecZ L β M) (oscN (rank L) 1 a p) := by
  by_cases hM : 0 ≤ M
  · rw [aExpVecZ_nonneg L β hM]; exact aExpVec_commute_oscN L β a M.toNat hp
  · rw [aExpVecZ_neg L β (by omega)]; exact Commute.zero_left _

/-- **The field-level boson OPE `[α^a(z₁), E⁺(α,z₂)]`**: coefficient `chargeCoord α a · E⁺(α)_{t+j+1}`
for `0 ≤ j`, else `0`. -/
theorem alphaFieldGen_comm_EplusVecField (a : Fin (rank L)) (α : L.carrier) (j t : ℤ) :
    bracketDist (currentN (rank L) 1 a) (EplusVecField L α) j t
      = if 0 ≤ j then chargeCoord L α a • EplusVecField L α (t + j + 1) else 0 := by
  rw [bracketDist_apply, currentN_apply]
  change (oscN (rank L) 1 a (-j - 1)).comp (EplusVecField L α t)
      - (EplusVecField L α t).comp (oscN (rank L) 1 a (-j - 1)) = _
  by_cases hj : 0 ≤ j
  · rw [if_pos hj, show -j - 1 = -((j + 1).toNat : ℤ) from by omega,
      EplusVecField_eq_aExpVecZ L α t, EplusVecField_eq_aExpVecZ L α (t + j + 1),
      oscNeg_comp_aExpVecZ L a α (j + 1).toNat (by omega) (-t),
      show -t - ((j + 1).toNat : ℤ) = -(t + j + 1) from by omega]
    abel
  · rw [if_neg hj]
    rcases (show -j - 1 = 0 ∨ 1 ≤ -j - 1 from by omega) with h0 | h1
    · rw [h0, oscN_zero, LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]
    · rw [EplusVecField_eq_aExpVecZ L α t,
        show (oscN (rank L) 1 a (-j - 1)).comp (aExpVecZ L α (-t))
            = (aExpVecZ L α (-t)).comp (oscN (rank L) 1 a (-j - 1)) from
          (aExpVecZ_commute_oscPos L α a (-t) h1).eq.symm, sub_self]

/-! ## §4  The boson-current/dressing commutator `[α^a(z₁), EE(α,z₂)]`. -/

/-- **The boson-current/dressing commutator** `[α^a(z₁), EE(α,z₂)]`: coefficient
`chargeCoord α a · EE(α)_{t+j+1}` except at `j = -1`.  Leibniz split of the `E⁻`/`E⁺` OPEs. -/
theorem alphaFieldGen_comm_EEVec (a : Fin (rank L)) (α : L.carrier) (j t : ℤ) :
    bracketDist (currentN (rank L) 1 a) (EEVec L α) j t
      = if j = -1 then 0 else chargeCoord L α a • EEVec L α (t + j + 1) := by
  refine LinearMap.ext fun x => ?_
  have hsupp1 : (Function.support (fun m : ℤ =>
      currentN (rank L) 1 a j (EminusVecField L α m (EplusVecField L α (t - m) x)))).Finite := by
    apply Set.Finite.subset (EEVecMarg_finite L α t x)
    intro m hm; rw [Function.mem_support] at hm ⊢
    intro h; exact hm (by rw [h, map_zero])
  have hsupp2 : (Function.support (fun m : ℤ =>
      EminusVecField L α m (EplusVecField L α (t - m) (currentN (rank L) 1 a j x)))).Finite :=
    EEVecMarg_finite L α t (currentN (rank L) 1 a j x)
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    show EEVec L α t (currentN (rank L) 1 a j x)
        = ∑ᶠ m : ℤ, EminusVecField L α m (EplusVecField L α (t - m) (currentN (rank L) 1 a j x)) from
      EEVec_apply_conv L α t (currentN (rank L) 1 a j x),
    show currentN (rank L) 1 a j (EEVec L α t x)
        = ∑ᶠ m : ℤ, currentN (rank L) 1 a j (EminusVecField L α m (EplusVecField L α (t - m) x)) from by
      rw [EEVec_apply_conv L α t x, map_finsum (currentN (rank L) 1 a j) (EEVecMarg_finite L α t x)],
    ← finsum_sub_distrib hsupp1 hsupp2,
    show (∑ᶠ m : ℤ, (currentN (rank L) 1 a j (EminusVecField L α m (EplusVecField L α (t - m) x))
            - EminusVecField L α m (EplusVecField L α (t - m) (currentN (rank L) 1 a j x))))
          = ∑ᶠ m : ℤ, ((bracketDist (currentN (rank L) 1 a) (EminusVecField L α) j m)
                (EplusVecField L α (t - m) x)
              + EminusVecField L α m
                ((bracketDist (currentN (rank L) 1 a) (EplusVecField L α) j (t - m)) x)) from
      finsum_congr fun m => by
        rw [bracketDist_apply, bracketDist_apply]
        exact leibniz_vecGen L (currentN (rank L) 1 a j) (EminusVecField L α m)
          (EplusVecField L α (t - m)) x]
  simp only [alphaFieldGen_comm_EminusVecField, alphaFieldGen_comm_EplusVecField]
  rcases (show j ≤ -2 ∨ j = -1 ∨ 0 ≤ j from by omega) with hj | hj | hj
  · rw [if_neg (by omega : ¬ j = -1),
      show (∑ᶠ m : ℤ, ((if j ≤ -2 then chargeCoord L α a • EminusVecField L α (m + j + 1) else 0)
                (EplusVecField L α (t - m) x)
              + EminusVecField L α m ((if 0 ≤ j then chargeCoord L α a • EplusVecField L α (t - m + j + 1)
                else 0) x)))
          = ∑ᶠ m : ℤ, chargeCoord L α a • EminusVecField L α (m + j + 1) (EplusVecField L α (t - m) x) from
        finsum_congr fun m => by
          rw [if_pos hj, if_neg (by omega : ¬ 0 ≤ j), LinearMap.smul_apply,
            LinearMap.zero_apply, map_zero, add_zero],
      show (chargeCoord L α a • EEVec L α (t + j + 1)) x
          = chargeCoord L α a • EEVec L α (t + j + 1) x from rfl,
      EEVec_apply_conv L α (t + j + 1) x, smul_finsum' (chargeCoord L α a)
        (EEVecMarg_finite L α (t + j + 1) x),
      ← finsum_comp_equiv (Equiv.addRight (j + 1))
        (f := fun m : ℤ => chargeCoord L α a • EminusVecField L α m (EplusVecField L α (t + j + 1 - m) x))]
    refine finsum_congr fun m => ?_
    simp only [Equiv.coe_addRight]
    rw [show m + (j + 1) = m + j + 1 from by ring,
      show t + j + 1 - (m + j + 1) = t - m from by ring]
  · subst hj
    rw [if_pos rfl]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [if_neg (by omega : ¬ (-1 : ℤ) ≤ -2), if_neg (by omega : ¬ (0 : ℤ) ≤ -1)]
    simp
  · rw [if_neg (by omega : ¬ j = -1),
      show (∑ᶠ m : ℤ, ((if j ≤ -2 then chargeCoord L α a • EminusVecField L α (m + j + 1) else 0)
                (EplusVecField L α (t - m) x)
              + EminusVecField L α m ((if 0 ≤ j then chargeCoord L α a • EplusVecField L α (t - m + j + 1)
                else 0) x)))
          = ∑ᶠ m : ℤ, chargeCoord L α a • EminusVecField L α m (EplusVecField L α (t + j + 1 - m) x) from
        finsum_congr fun m => by
          rw [if_neg (by omega : ¬ j ≤ -2), if_pos hj, LinearMap.zero_apply, zero_add,
            LinearMap.smul_apply, map_smul, show t - m + j + 1 = t + j + 1 - m from by ring],
      show (chargeCoord L α a • EEVec L α (t + j + 1)) x
          = chargeCoord L α a • EEVec L α (t + j + 1) x from rfl,
      EEVec_apply_conv L α (t + j + 1) x, smul_finsum' (chargeCoord L α a)
        (EEVecMarg_finite L α (t + j + 1) x)]

/-! ## §5  The boson ↔ charge mutual locality `Local (α^a(z)) (Y(e^α,z))`. -/

/-- `chargeCoord` is additive in the lattice vector (the momentum eigenvalue is linear). -/
theorem chargeCoord_add (α β : L.carrier) (a : Fin (rank L)) :
    chargeCoord L (α + β) a = chargeCoord L α a + chargeCoord L β a := by
  have hcoord : coordR L (α + β) = coordR L α + coordR L β := by
    funext i
    simp only [coordR, coord, map_add, Finsupp.add_apply, Int.cast_add, Pi.add_apply]
  simp only [chargeCoord, orthCoord, hcoord, Matrix.mulVec_add, Pi.add_apply, Complex.ofReal_add]

/-- The boson current on a basis state: `α^a(j)(p ⊗ e^δ) = (currentN a j p) ⊗ e^δ` plus the
momentum eigenvalue `chargeCoord δ a` at `j = -1`. -/
theorem alphaLatGen_tmul (a : Fin (rank L)) (j : ℤ) (q : FockN (rank L)) (δ : L.carrier) :
    alphaLatGen L a j (latStateGen L q δ)
      = latStateGen L (currentN (rank L) 1 a j q) δ
        + (if j = -1 then chargeCoord L δ a • latStateGen L q δ else 0) := by
  rw [alphaLatGen_apply, LinearMap.add_apply]
  have h1 : LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a j) (latStateGen L q δ)
      = latStateGen L (currentN (rank L) 1 a j q) δ := by
    show LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a j) (q ⊗ₜ[ℂ] eGen L δ)
        = (currentN (rank L) 1 a j q) ⊗ₜ[ℂ] eGen L δ
    rw [LinearMap.rTensor_tmul]
  rw [h1]
  congr 1
  by_cases hj : j = -1
  · rw [if_pos hj, if_pos hj, zGradeOpGen_latStateGen]
  · rw [if_neg hj, if_neg hj, LinearMap.zero_apply]

/-- **The boson ↔ charge commutator on a basis state** `[α^a(z₁), Y(e^β,z₂)] = chargeCoord β a ·
Y(e^β,z₂)`.  At `j = -1` the boson zero-mode `α^a(-1) = 0` vanishes and the momentum supplies the
charge (`chargeCoord (β+γ) a − chargeCoord γ a = chargeCoord β a`); at `j ≠ -1` the dressing
commutator `alphaFieldGen_comm_EEVec` carries it (cocycle spectator). -/
theorem alphaLatGen_comm_Yeαvec_tmul (a : Fin (rank L)) (β : L.carrier) (j t : ℤ)
    (p : FockN (rank L)) (γ : L.carrier) :
    bracketDist (alphaLatGen L a) (Yeαvec L β) j t (latStateGen L p γ)
      = chargeCoord L β a • Yeαvec L β (t + j + 1) (latStateGen L p γ) := by
  have hcur1 : currentN (rank L) 1 a (-1) = (0 : End ℂ (FockN (rank L))) := by
    rw [currentN_apply, show -(-1 : ℤ) - 1 = 0 from by ring, oscN_zero]
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Yeαvec_tmul, map_smul, alphaLatGen_tmul, alphaLatGen_tmul]
  by_cases hj : j = -1
  · -- j = -1: boson zero-mode `α^a(-1) = 0` vanishes; the momentum supplies the charge
    subst hj
    rw [if_pos rfl, if_pos rfl, hcur1, LinearMap.zero_apply, LinearMap.zero_apply,
      show latStateGen L (0 : FockN (rank L)) (β + γ) = 0 from by
        rw [latStateGen, TensorProduct.zero_tmul],
      show latStateGen L (0 : FockN (rank L)) γ = 0 from by
        rw [latStateGen, TensorProduct.zero_tmul],
      zero_add, zero_add, map_smul, show t + -1 + 1 = t from by ring, Yeαvec_tmul,
      chargeCoord_add]
    module
  · -- j ≠ -1: momentum absent; the dressing commutator carries the charge
    rw [if_neg hj, if_neg hj, add_zero, add_zero, Yeαvec_tmul, Yeαvec_tmul]
    have hbe : currentN (rank L) 1 a j (EEVec L β (t - L.form β γ) p)
          - EEVec L β (t - L.form β γ) (currentN (rank L) 1 a j p)
        = chargeCoord L β a • EEVec L β (t - L.form β γ + j + 1) p := by
      have h0 := alphaFieldGen_comm_EEVec L a β j (t - L.form β γ)
      rw [if_neg hj] at h0
      have hp := LinearMap.congr_fun h0 p
      rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.smul_apply] at hp
      exact hp
    rw [← smul_sub, ← latStateGen_sub_boson, hbe, latStateGen_smul_boson, smul_smul, smul_smul,
      mul_comm (latticeCocycle L β γ) (chargeCoord L β a),
      show t - L.form β γ + j + 1 = t + j + 1 - L.form β γ from by ring]

/-- **Operator lift**: `[α^a(z₁), Y(e^β,z₂)]_{j,t} = chargeCoord β a · Y(e^β)_{t+j+1}` on all of
`V_L`. -/
theorem alphaLatGen_comm_Yeαvec (a : Fin (rank L)) (β : L.carrier) (j t : ℤ) :
    bracketDist (alphaLatGen L a) (Yeαvec L β) j t
      = chargeCoord L β a • Yeαvec L β (t + j + 1) := by
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y1 y2 h1 h2 => rw [map_add, map_add, h1, h2]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, map_add, h1, h2]
      | single γ a' =>
          rw [show (Finsupp.single γ a' : L.carrier →₀ ℂ) = a' • eGen L γ from
            (Finsupp.smul_single_one γ a').symm]
          erw [TensorProduct.tmul_smul, map_smul, map_smul,
            show p ⊗ₜ[ℂ] eGen L γ = latStateGen L p γ from rfl,
            alphaLatGen_comm_Yeαvec_tmul, LinearMap.smul_apply]

/-- **The boson ↔ charge mutual locality** `Local (α^a(z)) (Y(e^β,z))`, bound `1`: the commutator
`chargeCoord β a · Y(e^β)_{t+j+1}` telescopes to `0` under `mulBySub`. -/
theorem alphaLatGen_Yeαvec_local (a : Fin (rank L)) (β : L.carrier) :
    Local (alphaLatGen L a) (Yeαvec L β) := by
  refine ⟨1, ?_⟩
  rw [mulBySubPow_one]
  funext s t
  rw [mulBySub_apply, alphaLatGen_comm_Yeαvec, alphaLatGen_comm_Yeαvec,
    show t + (s - 1) + 1 = (t - 1) + s + 1 from by ring, sub_self]
  rfl

/-- **Boson-generator / charge locality** `Local (genFieldLatGen a i) (Y(e^β,z))` (lift along
`∂_z` and the `(i!)⁻¹` scalar). -/
theorem genFieldLatGen_local_Yeαvec (a : Fin (rank L)) (i : ℕ) (β : L.carrier) :
    Local (genFieldLatGen L a i) (Yeαvec L β) := by
  change Local ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (alphaLatGen L a))) (Yeαvec L β)
  exact VertexOperatorAlgebra.Local.smul' _ ((alphaLatGen_Yeαvec_local L a β).deriv_iterate_left i)

end VOA.LatGen
