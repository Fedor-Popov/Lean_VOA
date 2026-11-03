/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenContraction
import VOA.Examples.LatticeGenEEMaster
import VOA.Examples.LatticeOppSignLocality

/-!
# The general (any-sign) `kappa`-kernel contraction

The generalized-binomial `(1-x)^{⟨α,β⟩}` contraction valid for **any** sign of `⟨α,β⟩` (the
opposite-sign case `⟨α,β⟩<0` is the `ι_z` infinite series, truncated to a finite sum by the
`aExpVecZ` support).  Cross-charge lift of A₁'s `aExpCZ_comp_EminusC_gen`, driven by the same atomic
move as the finite `crossContr` but with the generalized binomial kernel `LatExp.kappa`; the vector
build is again cleaner (no `m×2m'` product, `P = ⟨α,β⟩` direct).

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatExp (kappa kappa_zero kappa_combine partB_reindex_gen kZ kZ_neg kZ_nonneg)

variable (L : IntegralLattice)

/-- The RHS of the general contraction: the `kappa`-weighted binomial sum (range `N+1`). -/
noncomputable def RHScontrK (α β : L.carrier) (N b : ℤ) : End ℂ (FockN (rank L)) :=
  ∑ i ∈ Finset.range (N.toNat + 1),
    kappa ((L.form α β : ℤ) : ℂ) i •
      (EminusVecField L α (b - (i : ℤ))).comp (aExpVecZ L β (N - (i : ℤ)))

theorem RHScontrK_range (α β : L.carrier) (N b : ℤ) (K : ℕ) (hK : N.toNat ≤ K) :
    RHScontrK L α β N b
      = ∑ i ∈ Finset.range (K + 1),
          kappa ((L.form α β : ℤ) : ℂ) i •
            (EminusVecField L α (b - (i : ℤ))).comp (aExpVecZ L β (N - (i : ℤ))) := by
  rw [RHScontrK]
  refine Finset.sum_subset (by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_
  intro i _ hi
  simp only [Finset.mem_range, not_lt] at hi
  rw [aExpVecZ_neg L β (show N - (i : ℤ) < 0 by omega), LinearMap.comp_zero, smul_zero]

/-- **The general single-mode contraction** (any sign of `⟨α,β⟩`):
`E⁺(β)_·N ∘ E⁻(α)_b = ∑_{i=0}^{N} kappa ⟨α,β⟩ i • E⁻(α)_{b-i} ∘ E⁺(β)_{N-i}` (`aExpVecZ`/`EminusVecField`
form).  Cross-charge lift of A₁'s `aExpCZ_comp_EminusC_gen`, with `kappa` the generalized binomial
kernel; the finite `crossContr` is the special case `⟨α,β⟩ ≥ 0` (`kappa (n:ℂ) = wC n`). -/
theorem aExpVecZ_comp_EminusVec_gen (hPos : L.PosDef) (α β : L.carrier) (N : ℤ) (hN : 0 ≤ N)
    (b : ℤ) : (aExpVecZ L β N).comp (EminusVecField L α b) = RHScontrK L α β N b := by
  set PC : ℂ := ((L.form α β : ℤ) : ℂ) with hPCdef
  suffices H : ∀ n : ℕ, ∀ N b : ℤ, N.toNat ≤ n → 0 ≤ N →
      (aExpVecZ L β N).comp (EminusVecField L α b) = RHScontrK L α β N b by
    exact H N.toNat N b le_rfl hN
  intro n
  induction n with
  | zero =>
    intro N b hN hN0
    have hN0' : N = 0 := by omega
    subst hN0'
    rw [RHScontrK, aExpVecZ_zero, LinearMap.id_comp, Int.toNat_zero, Finset.sum_range_one]
    simp only [Nat.cast_zero, sub_zero, kappa_zero, one_smul, aExpVecZ_zero, LinearMap.comp_id]
  | succ n ih =>
    intro N b hN hN0
    by_cases hsmall : N.toNat ≤ n
    · exact ih N b hsmall hN0
    · have hN1 : 1 ≤ N := by omega
      have hNne : (N : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      set op : ℤ → End ℂ (FockN (rank L)) :=
        fun j => (EminusVecField L α (b - j)).comp (aExpVecZ L β (N - j)) with hop
      have hopvanish : ∀ j : ℤ, N.toNat < j → op j = 0 := fun j hj => by
        rw [hop]; dsimp only
        rw [aExpVecZ_neg L β (show N - j < 0 by omega), LinearMap.comp_zero]
      have hLHS : (aExpVecZ L β N).comp (EminusVecField L α b)
          = (N : ℂ)⁻¹ • ∑ r ∈ Finset.range N.toNat,
              (-(chargeOsc L β ((r : ℤ) + 1))).comp
                ((aExpVecZ L β (N - 1 - r)).comp (EminusVecField L α b)) := by
        rw [aExpVecZ_recursion L β N hN1, LinearMap.smul_comp, sum_comp']
        simp only [LinearMap.comp_assoc]
      have hexp : ∀ r ∈ Finset.range N.toNat,
          (-(chargeOsc L β ((r : ℤ) + 1))).comp
              ((aExpVecZ L β (N - 1 - r)).comp (EminusVecField L α b))
            = ∑ i ∈ Finset.range (N.toNat + 1),
                kappa PC i • ((EminusVecField L α (b - (i : ℤ))).comp
                    ((-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β (N - 1 - r - (i : ℤ))))
                  - PC • (EminusVecField L α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                      (aExpVecZ L β (N - 1 - r - (i : ℤ)))) := by
        intro r hr
        simp only [Finset.mem_range] at hr
        rw [ih (N - 1 - r) b (by omega) (by omega),
          RHScontrK_range L α β (N - 1 - r) b N.toNat (by omega), comp_sum']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.comp_smul,
          move_chargeOsc_past_EminusVecField L hPos α β r (b - (i : ℤ))
            (aExpVecZ L β (N - 1 - r - (i : ℤ)))]
      have hMain : ∀ i ∈ Finset.range (N.toNat + 1),
          (EminusVecField L α (b - (i : ℤ))).comp
              (∑ r ∈ Finset.range N.toNat,
                (-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β (N - 1 - r - (i : ℤ))))
            = ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [show (∑ r ∈ Finset.range N.toNat,
                (-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β (N - 1 - r - (i : ℤ))))
              = ∑ r ∈ Finset.range N.toNat,
                (-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β ((N - i) - 1 - r)) from
            Finset.sum_congr rfl fun r _ => by
              rw [show (N : ℤ) - 1 - r - (i : ℤ) = (N - i) - 1 - r from by ring],
          aExpVecZ_sum_reassembly L β (N - i) N.toNat (by omega), LinearMap.comp_smul]
      rw [hLHS, Finset.sum_congr rfl hexp, Finset.sum_comm]
      have hcollapse : ∀ i ∈ Finset.range (N.toNat + 1),
          (∑ r ∈ Finset.range N.toNat,
              kappa PC i • ((EminusVecField L α (b - (i : ℤ))).comp
                  ((-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β (N - 1 - r - (i : ℤ))))
                - PC • (EminusVecField L α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                    (aExpVecZ L β (N - 1 - r - (i : ℤ)))))
            = kappa PC i • ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ)
              - PC • kappa PC i • (∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1)) := by
        intro i hi
        rw [show (∑ r ∈ Finset.range N.toNat,
              kappa PC i • ((EminusVecField L α (b - (i : ℤ))).comp
                  ((-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β (N - 1 - r - (i : ℤ))))
                - PC • (EminusVecField L α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                    (aExpVecZ L β (N - 1 - r - (i : ℤ)))))
            = (∑ r ∈ Finset.range N.toNat,
                kappa PC i • (EminusVecField L α (b - (i : ℤ))).comp
                  ((-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β (N - 1 - r - (i : ℤ)))))
              - (∑ r ∈ Finset.range N.toNat,
                  PC • kappa PC i • op ((i : ℤ) + r + 1)) from by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [smul_sub, smul_comm (kappa PC i) PC]
          rw [hop]; dsimp only
          rw [show b - (i : ℤ) - ((r : ℤ) + 1) = b - ((i : ℤ) + r + 1) from by ring,
            show N - 1 - (r : ℤ) - (i : ℤ) = N - ((i : ℤ) + r + 1) from by ring]]
        rw [← Finset.smul_sum, ← comp_sum', hMain i hi, ← Finset.smul_sum, ← Finset.smul_sum]
      rw [Finset.sum_congr rfl hcollapse, Finset.sum_sub_distrib, inv_smul_eq_iff₀ hNne, RHScontrK]
      rw [show (∑ i ∈ Finset.range (N.toNat + 1),
              kappa PC i • ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ))
            = ∑ j ∈ Finset.range (N.toNat + 1),
                (kappa PC j * ((N - (j : ℤ) : ℤ) : ℂ)) • op (j : ℤ) from
          Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
      rw [show (∑ i ∈ Finset.range (N.toNat + 1),
                PC • kappa PC i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
            = ∑ j ∈ Finset.range (N.toNat + 1),
                (PC * ∑ i ∈ Finset.range j, kappa PC i) • op (j : ℤ) from by
          rw [← Finset.smul_sum,
            show (∑ i ∈ Finset.range (N.toNat + 1),
                    kappa PC i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
                = ∑ j ∈ Finset.range N.toNat, ∑ i ∈ Finset.range (N.toNat + 1),
                    kappa PC i • (fun s : ℕ => op (s : ℤ)) (i + j + 1) from by
              rw [show (∑ i ∈ Finset.range (N.toNat + 1),
                        kappa PC i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
                    = ∑ i ∈ Finset.range (N.toNat + 1), ∑ r ∈ Finset.range N.toNat,
                        kappa PC i • op ((i : ℤ) + r + 1) from by
                  simp only [Finset.smul_sum]]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
              rw [show (i : ℤ) + (r : ℤ) + 1 = ((i + r + 1 : ℕ) : ℤ) from by push_cast; ring],
            partB_reindex_gen (fun s => op (s : ℤ)) N.toNat (kappa PC)
              (fun s hs => hopvanish (s : ℤ) (by exact_mod_cast hs)), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
      rw [show ((N : ℂ) • ∑ i ∈ Finset.range (N.toNat + 1),
                kappa PC i • (EminusVecField L α (b - (i : ℤ))).comp (aExpVecZ L β (N - (i : ℤ))))
            = ∑ j ∈ Finset.range (N.toNat + 1), ((N : ℂ) * kappa PC j) • op (j : ℤ) from by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [smul_smul, hop]]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      rw [← sub_smul]
      congr 1
      have hcomb := kappa_combine PC j
      push_cast
      push_cast at hcomb
      linear_combination -hcomb

/-- The `E⁺(β)`/`E⁻(α)` coefficient form of the general contraction (for `a ≤ 0`). -/
theorem EplusVec_comp_EminusVec_gen (hPos : L.PosDef) (α β : L.carrier) (a b : ℤ) (ha : a ≤ 0) :
    (EplusVecField L β a).comp (EminusVecField L α b)
      = ∑ m ∈ Finset.range ((-a).toNat + 1),
          kappa ((L.form α β : ℤ) : ℂ) m •
            (EminusVecField L α (b - (m : ℤ))).comp (EplusVecField L β (a + (m : ℤ))) := by
  rw [EplusVecField_eq_aExpVecZ L β a, aExpVecZ_comp_EminusVec_gen L hPos α β (-a) (by omega) b,
    RHScontrK]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [EplusVecField_eq_aExpVecZ L β (a + (m : ℤ)), show -(a + (m : ℤ)) = -a - (m : ℤ) from by ring]

/-- **The pointwise geometric contraction as a `ℤ`-finsum** (uniform in `a`, any sign):
`E⁺(β)_a E⁻(α)_q Z = ∑ᶠ_m kZ ⟨α,β⟩ m • E⁻(α)_{q-m} E⁺(β)_{a+m} Z`.  Cross-charge lift of A₁'s
`EplusC_EminusC_geom`. -/
theorem EplusVec_EminusVec_geom (hPos : L.PosDef) (α β : L.carrier) (a q : ℤ)
    (Z : FockN (rank L)) :
    EplusVecField L β a (EminusVecField L α q Z)
      = ∑ᶠ m : ℤ, kZ ((L.form α β : ℤ) : ℂ) m •
          EminusVecField L α (q - m) (EplusVecField L β (a + m) Z) := by
  set PC : ℂ := ((L.form α β : ℤ) : ℂ) with hPCdef
  have hsub : (Function.support
      (fun m : ℤ => kZ PC m • EminusVecField L α (q - m) (EplusVecField L β (a + m) Z)))
      ⊆ (Finset.Icc (0 : ℤ) (-a) : Finset ℤ) := by
    intro m hm
    rw [Function.mem_support] at hm
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra h; exact hm (by rw [kZ_neg PC (by omega), zero_smul])
    · by_contra h
      rw [EplusVecField_pos L β (show (0 : ℤ) < a + m by omega), LinearMap.zero_apply, map_zero,
        smul_zero] at hm
      exact hm rfl
  rw [finsum_eq_sum_of_support_subset _ hsub]
  by_cases ha : a ≤ 0
  · have happ := DFunLike.congr_fun (EplusVec_comp_EminusVec_gen L hPos α β a q ha) Z
    simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply] at happ
    rw [happ]
    refine Finset.sum_nbij' (fun (i : ℕ) => (i : ℤ)) (fun (m : ℤ) => m.toNat) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
    · intro i _; simp
    · intro m hm; simp only [Finset.mem_Icc] at hm; exact Int.toNat_of_nonneg hm.1
    · intro i hi
      simp only [Finset.mem_range] at hi
      rw [kZ_nonneg PC (show (0 : ℤ) ≤ (i : ℤ) by positivity), Int.toNat_natCast]
  · push_neg at ha
    rw [EplusVecField_pos L β ha, LinearMap.zero_apply]
    refine (Finset.sum_eq_zero fun m hm => ?_).symm
    simp only [Finset.mem_Icc] at hm
    rw [EplusVecField_pos L β (show (0 : ℤ) < a + m by omega), LinearMap.zero_apply, map_zero,
      smul_zero]

end VOA.LatGen
