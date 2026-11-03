/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenSameSign
import VOA.Examples.LatticeSameSignLocality

/-!
# The vector-charge exponential contraction `crossContr`

The `(1-x)^{⟨α,β⟩}` binomial reordering `E⁺(β,z₁) E⁻(α,z₂) = (z₁-z₂)^{⟨α,β⟩} E⁻(α,z₂) E⁺(β,z₁)` in
coefficient form, the heart of same-sign lattice locality.  Cross-charge lift of A₁'s `crossContr`
(`Examples/LatticeSameSignLocality`), with the atomic move `chargeOsc_succ_comp_EminusVecField`
(structure constant `⟨α,β⟩`) driving the induction and the charge-agnostic binomial weights
`LatExp.wC`/`wC_combine`/`wC_vanish` reused verbatim.

**Structural simplification over A₁**: since the lattice charge lives inside `chargeOsc` (not as an
outside factor of `aExpVec`), the binomial exponent `P = ⟨α,β⟩` comes *directly* from the atomic
move — no `m×2m'` product, no `hPeqC` step.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatExp (wC wC_vanish wC_combine)

variable (L : IntegralLattice)

/-! ## §4.1  Helpers over `FockN (rank L)` -/

/-- `(∑ Fᵢ) ∘ g = ∑ (Fᵢ ∘ g)`. -/
theorem sum_comp' {ι : Type*} (s : Finset ι) (F : ι → End ℂ (FockN (rank L)))
    (g : End ℂ (FockN (rank L))) : (∑ i ∈ s, F i).comp g = ∑ i ∈ s, (F i).comp g := by
  rw [← Module.End.mul_eq_comp, Finset.sum_mul]
  simp only [Module.End.mul_eq_comp]

/-- `g ∘ (∑ Fᵢ) = ∑ (g ∘ Fᵢ)`. -/
theorem comp_sum' {ι : Type*} (s : Finset ι) (g : End ℂ (FockN (rank L)))
    (F : ι → End ℂ (FockN (rank L))) : g.comp (∑ i ∈ s, F i) = ∑ i ∈ s, g.comp (F i) := by
  rw [← Module.End.mul_eq_comp, Finset.mul_sum]
  simp only [Module.End.mul_eq_comp]

/-- The RHS of the cross contraction: a `(P+1)`-term binomial sum (range `N+1`; extra terms vanish
since `aExpVecZ β (N-i) = 0` for `i > N`). -/
noncomputable def RHScontr (α β : L.carrier) (P : ℕ) (N b : ℤ) : End ℂ (FockN (rank L)) :=
  ∑ i ∈ Finset.range (N.toNat + 1),
    wC P i • (EminusVecField L α (b - (i : ℤ))).comp (aExpVecZ L β (N - (i : ℤ)))

/-- `RHScontr` is insensitive to enlarging the summation range past `N.toNat`. -/
theorem RHScontr_range (α β : L.carrier) (P : ℕ) (N b : ℤ) (K : ℕ) (hK : N.toNat ≤ K) :
    RHScontr L α β P N b
      = ∑ i ∈ Finset.range (K + 1),
          wC P i • (EminusVecField L α (b - (i : ℤ))).comp (aExpVecZ L β (N - (i : ℤ))) := by
  rw [RHScontr]
  refine Finset.sum_subset (by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_
  intro i _ hi
  simp only [Finset.mem_range, not_lt] at hi
  rw [aExpVecZ_neg L β (show N - (i : ℤ) < 0 by omega), LinearMap.comp_zero, smul_zero]

/-- **The shift double-sum reindex** (charge-agnostic, over `FockN (rank L)`; mirror A₁'s
`shift_reindex`).  For an operator family `g` vanishing above `T`,
`∑_{i≤T} wᵢ · ∑_{r<T} g(i+r+1) = ∑_{j≤T} (∑_{i<j} wᵢ) · g j`. -/
theorem shift_reindex (P T : ℕ) (g : ℕ → End ℂ (FockN (rank L))) (hg : ∀ j, T < j → g j = 0) :
    (∑ i ∈ Finset.range (T + 1), wC P i • ∑ r ∈ Finset.range T, g (i + r + 1))
      = ∑ j ∈ Finset.range (T + 1), (∑ i ∈ Finset.range j, wC P i) • g j := by
  have hinner : ∀ i ∈ Finset.range (T + 1),
      (∑ r ∈ Finset.range T, g (i + r + 1))
        = ∑ j ∈ Finset.range (T + 1), if i < j then g j else 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hdrop : (∑ r ∈ Finset.range T, g (i + r + 1))
        = ∑ r ∈ Finset.range (T - i), g (i + r + 1) := by
      refine (Finset.sum_subset (by
        intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
      intro r _ hr; simp only [Finset.mem_range, not_lt] at hr
      exact hg (i + r + 1) (by omega)
    rw [hdrop, ← Finset.sum_filter]
    refine Finset.sum_nbij' (i := fun r => i + r + 1) (j := fun j => j - i - 1) ?_ ?_ ?_ ?_ ?_
    · intro r hr; simp only [Finset.mem_range] at hr
      simp only [Finset.mem_filter, Finset.mem_range]; omega
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp only [Finset.mem_range]; omega
    · intro r hr; simp only [Finset.mem_range] at hr; simp only []; omega
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj; simp only []; omega
    · intro r _; rfl
  rw [Finset.sum_congr rfl (fun i hi => by rw [hinner i hi])]
  rw [show (∑ i ∈ Finset.range (T + 1),
            wC P i • ∑ j ∈ Finset.range (T + 1), if i < j then g j else 0)
        = ∑ i ∈ Finset.range (T + 1), ∑ j ∈ Finset.range (T + 1),
            (if i < j then wC P i • g j else 0) from
      Finset.sum_congr rfl fun i _ => by
        rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hc : i < j
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc, smul_zero]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rw [Finset.sum_smul, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-! ## §4.2  The vector-charge single-mode binomial contraction -/

/-- **The cross-charge single-mode contraction** (same-sign, `P = ⟨α,β⟩ ≥ 0` finite binomial):
`E⁺(β)_·a ∘ E⁻(α)_·b = ∑_{i} (-1)^i C(P,i) • E⁻(α)_{b-i} ∘ E⁺(β)_{a+i}` in `aExpVecZ`/`EminusVecField`
coefficient form.  Cross-charge lift of A₁'s `crossContr`; the exponent `P = ⟨α,β⟩` enters *directly*
through the atomic move `move_chargeOsc_past_EminusVecField` (no `m×2m'` product), the coefficient
telescope closed by `wC_combine`. -/
theorem crossContr (hPos : L.PosDef) (α β : L.carrier) (P : ℕ) (hP : (P : ℤ) = L.form α β)
    (N b : ℤ) : (aExpVecZ L β N).comp (EminusVecField L α b) = RHScontr L α β P N b := by
  have hPC : ((L.form α β : ℤ) : ℂ) = (P : ℂ) := by rw [← hP]; push_cast; ring
  suffices H : ∀ n : ℕ, ∀ N b : ℤ, N.toNat ≤ n →
      (aExpVecZ L β N).comp (EminusVecField L α b) = RHScontr L α β P N b by
    exact H N.toNat N b le_rfl
  intro n
  induction n with
  | zero =>
    intro N b hN
    rw [RHScontr]
    by_cases h0 : N = 0
    · subst h0
      rw [aExpVecZ_zero, LinearMap.id_comp, show (0 : ℤ).toNat + 1 = 1 from rfl,
        Finset.sum_range_one, wC, pow_zero, Nat.choose_zero_right]
      simp only [Nat.cast_one, mul_one, one_smul, Nat.cast_zero, sub_zero, aExpVecZ_zero,
        LinearMap.comp_id]
    · rw [aExpVecZ_neg L β (by omega : N < 0), LinearMap.zero_comp,
        show N.toNat + 1 = 1 from by omega, Finset.sum_range_one,
        aExpVecZ_neg L β (show N - ((0 : ℕ) : ℤ) < 0 by omega), LinearMap.comp_zero, smul_zero]
  | succ n ih =>
    intro N b hN
    by_cases hsmall : N.toNat ≤ n
    · exact ih N b hsmall
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
                wC P i • ((EminusVecField L α (b - (i : ℤ))).comp
                    ((-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β (N - 1 - r - (i : ℤ))))
                  - (P : ℂ) • (EminusVecField L α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                      (aExpVecZ L β (N - 1 - r - (i : ℤ)))) := by
        intro r hr
        simp only [Finset.mem_range] at hr
        rw [ih (N - 1 - r) b (by omega), RHScontr_range L α β P (N - 1 - r) b N.toNat (by omega),
          comp_sum']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.comp_smul,
          move_chargeOsc_past_EminusVecField L hPos α β r (b - (i : ℤ))
            (aExpVecZ L β (N - 1 - r - (i : ℤ))), hPC]
      -- main reassembly per `i`
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
      -- transform: recursion, expand via `hexp`, interchange `∑_r ∑_i`.
      rw [hLHS, Finset.sum_congr rfl hexp, Finset.sum_comm]
      have hcollapse : ∀ i ∈ Finset.range (N.toNat + 1),
          (∑ r ∈ Finset.range N.toNat,
              wC P i • ((EminusVecField L α (b - (i : ℤ))).comp
                  ((-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β (N - 1 - r - (i : ℤ))))
                - (P : ℂ) • (EminusVecField L α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                    (aExpVecZ L β (N - 1 - r - (i : ℤ)))))
            = wC P i • ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ)
              - (P : ℂ) • wC P i • (∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1)) := by
        intro i hi
        rw [show (∑ r ∈ Finset.range N.toNat,
              wC P i • ((EminusVecField L α (b - (i : ℤ))).comp
                  ((-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β (N - 1 - r - (i : ℤ))))
                - (P : ℂ) • (EminusVecField L α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                    (aExpVecZ L β (N - 1 - r - (i : ℤ)))))
            = (∑ r ∈ Finset.range N.toNat,
                wC P i • (EminusVecField L α (b - (i : ℤ))).comp
                  ((-(chargeOsc L β ((r : ℤ) + 1))).comp (aExpVecZ L β (N - 1 - r - (i : ℤ)))))
              - (∑ r ∈ Finset.range N.toNat,
                  (P : ℂ) • wC P i • op ((i : ℤ) + r + 1)) from by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [smul_sub, smul_comm (wC P i) (P : ℂ)]
          rw [hop]; dsimp only
          rw [show b - (i : ℤ) - ((r : ℤ) + 1) = b - ((i : ℤ) + r + 1) from by ring,
            show N - 1 - (r : ℤ) - (i : ℤ) = N - ((i : ℤ) + r + 1) from by ring]]
        rw [← Finset.smul_sum, ← comp_sum', hMain i hi, ← Finset.smul_sum, ← Finset.smul_sum]
      rw [Finset.sum_congr rfl hcollapse, Finset.sum_sub_distrib, inv_smul_eq_iff₀ hNne, RHScontr]
      -- MAIN total: per-`j` scalar
      rw [show (∑ i ∈ Finset.range (N.toNat + 1), wC P i • ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ))
            = ∑ j ∈ Finset.range (N.toNat + 1), (wC P j * ((N - (j : ℤ) : ℤ) : ℂ)) • op (j : ℤ) from
          Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
      -- SHIFT total via `shift_reindex`
      rw [show (∑ i ∈ Finset.range (N.toNat + 1),
                (P : ℂ) • wC P i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
            = ∑ j ∈ Finset.range (N.toNat + 1), ((P : ℂ) * ∑ i ∈ Finset.range j, wC P i) • op (j : ℤ)
          from by
          rw [← Finset.smul_sum,
            show (∑ i ∈ Finset.range (N.toNat + 1),
                    wC P i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
                = ∑ i ∈ Finset.range (N.toNat + 1),
                    wC P i • ∑ r ∈ Finset.range N.toNat, (fun s : ℕ => op (s : ℤ)) (i + r + 1) from
              Finset.sum_congr rfl fun i _ => congrArg (fun t => wC P i • t)
                (Finset.sum_congr rfl fun r _ => by
                  rw [show (i : ℤ) + (r : ℤ) + 1 = ((i + r + 1 : ℕ) : ℤ) from by push_cast; ring]),
            shift_reindex L P N.toNat (fun s => op (s : ℤ))
              (fun j hj => hopvanish (j : ℤ) (by exact_mod_cast hj)), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
      -- RHS: `N • RHScontr` per-`j` scalar
      rw [show ((N : ℂ) • ∑ j ∈ Finset.range (N.toNat + 1),
                wC P j • (EminusVecField L α (b - (j : ℤ))).comp (aExpVecZ L β (N - (j : ℤ))))
            = ∑ j ∈ Finset.range (N.toNat + 1), ((N : ℂ) * wC P j) • op (j : ℤ) from by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [smul_smul, hop]]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      rw [← sub_smul]
      congr 1
      have hcomb := wC_combine P j
      push_cast
      push_cast at hcomb
      linear_combination -hcomb

/-- **The `(P+1)`-term cross contraction** in `E⁺(β)`/`E⁻(α)` coefficient form (same-sign,
`P = ⟨α,β⟩ ≥ 0`): `E⁺(β)_a ∘ E⁻(α)_b = ∑_{i=0}^{P} (-1)^i C(P,i) • E⁻(α)_{b-i} ∘ E⁺(β)_{a+i}`.
Cross-charge lift of A₁'s `contr_P`. -/
theorem contr_P (hPos : L.PosDef) (α β : L.carrier) (P : ℕ) (hP : (P : ℤ) = L.form α β) (a b : ℤ) :
    (EplusVecField L β a).comp (EminusVecField L α b)
      = ∑ i ∈ Finset.range (P + 1),
          wC P i • (EminusVecField L α (b - (i : ℤ))).comp (EplusVecField L β (a + (i : ℤ))) := by
  rw [EplusVecField_eq_aExpVecZ L β a, crossContr L hPos α β P hP (-a) b, RHScontr]
  have hEqterm : ∀ i : ℕ, (EminusVecField L α (b - (i : ℤ))).comp (aExpVecZ L β (-a - (i : ℤ)))
      = (EminusVecField L α (b - (i : ℤ))).comp (EplusVecField L β (a + (i : ℤ))) := fun i => by
    rw [EplusVecField_eq_aExpVecZ L β (a + (i : ℤ)), show -(a + (i : ℤ)) = -a - (i : ℤ) from by ring]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hEqterm i])]
  set term : ℕ → End ℂ (FockN (rank L)) :=
    fun i => wC P i • (EminusVecField L α (b - (i : ℤ))).comp (EplusVecField L β (a + (i : ℤ)))
    with hterm
  have hvanA : ∀ i, (-a).toNat < i → term i = 0 := fun i hi => by
    rw [hterm]; dsimp only
    rw [EplusVecField_eq_aExpVecZ L β (a + (i : ℤ)),
      aExpVecZ_neg L β (show -(a + (i : ℤ)) < 0 by omega), LinearMap.comp_zero, smul_zero]
  have hvanP : ∀ i, P < i → term i = 0 := fun i hi => by
    rw [hterm]; dsimp only; rw [wC_vanish hi, zero_smul]
  set K := max (P + 1) ((-a).toNat + 1) with hK
  rw [show (∑ i ∈ Finset.range ((-a).toNat + 1), term i) = ∑ i ∈ Finset.range K, term i from
      (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
        (fun i _ hi => by simp only [Finset.mem_range, not_lt] at hi; exact hvanA i (by omega))),
    show (∑ i ∈ Finset.range (P + 1), term i) = ∑ i ∈ Finset.range K, term i from
      (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
        (fun i _ hi => by simp only [Finset.mem_range, not_lt] at hi; exact hvanP i (by omega)))]

end VOA.LatGen
