/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeReconstruct

/-!
# Same-sign + charge-0 lattice locality (STAGE 2, the `mm' ≥ 0` half)

The general charge-pair mutual locality `Local (Yemα m) (Yemα m')` for `m*m' ≥ 0`:

* `Yemα_zeroLeft_local` / `Yemα_zeroRight_local` — the charge-`0` case (`Yemα 0` is the
  identity-spectator field, so it commutes with every `Yemα m'`).
* `Yemα_sameSign_local (hsign : 1 ≤ m*m')` — the strictly-same-sign case, via the generalized
  four-fold resummation `eeMaster_P` / `shift_comm_P` for pairing `P = 2mm' ≥ 2` (the `(1-x)^P`
  binomial generalization of the diagonal three-term `(1,-2,1)` contraction): the even-lattice
  same-sign operators commute exactly (locality bound `0`).

All `pbw`-free / axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open VOA VOA.LatExp VOA.LatticeVOA
open Module (End)
open scoped TensorProduct BigOperators
namespace VOA.LatExp

/-! ## §0  The charge-`0` collapse: `Yemα 0` is the identity-spectator field -/

/-- At charge `0` the creation Schur core vanishes above degree `0`. -/
theorem cSchurC0_collapse : ∀ N : ℕ, 1 ≤ N → cSchurC 0 N = 0 := by
  intro N hN
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  rw [cSchurC_succ]; simp

/-- At charge `0` the annihilation exponential core vanishes above degree `0`. -/
theorem aExpC0_collapse : ∀ N : ℕ, 1 ≤ N → aExpC 0 N = 0 := by
  intro N hN
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  rw [aExpC_succ]; simp

/-- `aExpCZ 0 N = 0` for `N ≠ 0`. -/
theorem aExpCZ0_collapse {N : ℤ} (hN : N ≠ 0) : aExpCZ 0 N = 0 := by
  by_cases h : 0 ≤ N
  · rw [aExpCZ_nonneg 0 h, aExpC0_collapse N.toNat (by omega)]
  · rw [aExpCZ_neg 0 (by omega)]

/-- `EminusC 0 t = if t = 0 then id else 0`. -/
theorem EminusC0 (t : ℤ) : EminusC 0 t = if t = 0 then LinearMap.id else 0 := by
  by_cases ht : 0 ≤ t
  · rw [EminusC_nonneg 0 ht]
    by_cases h0 : t = 0
    · rw [if_pos h0, EminusOpC, show t.toNat = 0 from by omega, cSchurC_zero]
      exact LinearMap.ext fun x => by rw [LinearMap.mulLeft_apply, one_mul]; rfl
    · rw [if_neg h0, EminusOpC, cSchurC0_collapse t.toNat (by omega)]
      exact LinearMap.ext fun x => by rw [LinearMap.mulLeft_apply, zero_mul]; rfl
  · rw [EminusC_neg 0 (by omega), if_neg (by omega)]

/-- `EplusC 0 t = if t = 0 then id else 0`. -/
theorem EplusC0 (t : ℤ) : EplusC 0 t = if t = 0 then LinearMap.id else 0 := by
  rw [EplusC_eq_aExpCZ]
  by_cases h0 : t = 0
  · rw [if_pos h0, h0, neg_zero, aExpCZ_zero]
  · rw [if_neg h0, aExpCZ0_collapse (by omega : -t ≠ 0)]

/-- `EEC 0 t = if t = 0 then id else 0`. -/
theorem EEC0 (t : ℤ) : EEC 0 t = if t = 0 then LinearMap.id else 0 := by
  refine LinearMap.ext fun x => ?_
  rw [EEC_apply_conv 0 t x]
  rw [finsum_eq_single (fun m : ℤ => EminusC 0 m (EplusC 0 (t - m) x)) 0 (fun m hm => by
    show EminusC 0 m (EplusC 0 (t - m) x) = 0
    rw [EminusC0, if_neg hm, LinearMap.zero_apply])]
  show EminusC 0 0 (EplusC 0 (t - 0) x) = (if t = 0 then LinearMap.id else 0) x
  rw [EminusC0, if_pos rfl, sub_zero, EplusC0]
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0, LinearMap.zero_apply]; rfl

/-! ## §R  The mixed bracket reduction on a basis state -/

/-- **The general-charge bracket on a basis state** `p ⊗ e^{nα}`: the lattice bracket
`[Y(e^{mα},z₁), Y(e^{m'α},z₂)]` reduces to a boson-level `EEC`-commutator on `B = FockN 1`,
shifted into the sector `n+m+m'` with sector shifts `2mn`, `2m'n` and the pairing `P = 2mm'`. -/
theorem reduce_mixed (m m' j k n : ℤ) (p : B) :
    bracketDist (Yemα m) (Yemα m') j k (p ⊗ₜ[ℂ] eVec n)
      = (EEC (m : ℂ) ((j - 2 * m * n) - 2 * m * m') (EEC (m' : ℂ) (k - 2 * m' * n) p)
          - EEC (m' : ℂ) ((k - 2 * m' * n) - 2 * m' * m) (EEC (m : ℂ) (j - 2 * m * n) p))
        ⊗ₜ[ℂ] eVec (n + m + m') := by
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Yemα_tmul, Yemα_tmul, Yemα_tmul, Yemα_tmul]
  rw [show (k - 2 * m' * (n + m) : ℤ) = (k - 2 * m' * n) - 2 * m' * m from by ring,
    show (j - 2 * m * (n + m') : ℤ) = (j - 2 * m * n) - 2 * m * m' from by ring,
    show (n + m' + m : ℤ) = n + m + m' from by ring, show (n + m + m' : ℤ) = n + m + m' from rfl]
  rw [← TensorProduct.sub_tmul]

/-! ## §0loc  The charge-`0` locality (both orientations) -/

/-- The charge-`0`-on-the-left bracket vanishes on every basis state. -/
theorem Yemα_zeroLeft_bracket_on_state (m' j k n : ℤ) (p : B) :
    bracketDist (Yemα 0) (Yemα m') j k (p ⊗ₜ[ℂ] eVec n) = 0 := by
  rw [reduce_mixed]
  rw [show ((0 : ℤ) : ℂ) = (0 : ℂ) from by norm_num]
  rw [show (j - 2 * 0 * n - 2 * 0 * m' : ℤ) = j from by ring,
    show (k - 2 * m' * n - 2 * m' * 0 : ℤ) = k - 2 * m' * n from by ring,
    show (j - 2 * 0 * n : ℤ) = j from by ring]
  by_cases hj : j = 0
  · rw [hj, EEC0, if_pos rfl]
    simp only [LinearMap.id_apply, sub_self, TensorProduct.zero_tmul]
  · rw [EEC0, if_neg hj]
    simp only [LinearMap.zero_apply, map_zero, sub_zero, TensorProduct.zero_tmul]

/-- The charge-`0`-on-the-right bracket vanishes on every basis state. -/
theorem Yemα_zeroRight_bracket_on_state (m j k n : ℤ) (p : B) :
    bracketDist (Yemα m) (Yemα 0) j k (p ⊗ₜ[ℂ] eVec n) = 0 := by
  rw [reduce_mixed]
  rw [show ((0 : ℤ) : ℂ) = (0 : ℂ) from by norm_num]
  rw [show (k - 2 * 0 * n - 2 * 0 * m : ℤ) = k from by ring,
    show (j - 2 * m * n - 2 * m * 0 : ℤ) = j - 2 * m * n from by ring,
    show (k - 2 * 0 * n : ℤ) = k from by ring]
  by_cases hk : k = 0
  · rw [hk, EEC0, if_pos rfl]
    simp only [LinearMap.id_apply, sub_self, TensorProduct.zero_tmul]
  · rw [EEC0, if_neg hk]
    simp only [LinearMap.zero_apply, map_zero, sub_zero, TensorProduct.zero_tmul]

/-- Lift a "bracket vanishes on every basis state" hypothesis to `Local`. -/
theorem local_of_bracket_on_state {F G : FormalDist (End ℂ LatModule)}
    (h : ∀ (j k n : ℤ) (p : B), bracketDist F G j k (p ⊗ₜ[ℂ] eVec n) = 0) : Local F G := by
  refine local_of_bracketDist_eq_zero ?_
  refine FormalDist₂.ext fun j k => ?_
  refine LinearMap.ext fun y => ?_
  change bracketDist F G j k y = 0
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add y1 y2 h1 h2 => rw [map_add, h1, h2, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, h1, h2, add_zero]
      | single n a =>
          rw [(Finsupp.smul_single_one n a).symm]
          erw [TensorProduct.tmul_smul, map_smul,
            show (Finsupp.single n (1 : ℂ) : LatGrp) = eVec n from rfl, h, smul_zero]

theorem Yemα_zeroLeft_local (m' : ℤ) : Local (Yemα 0) (Yemα m') :=
  local_of_bracket_on_state (Yemα_zeroLeft_bracket_on_state m')

theorem Yemα_zeroRight_local (m : ℤ) : Local (Yemα m) (Yemα 0) :=
  local_of_bracket_on_state (Yemα_zeroRight_bracket_on_state m)

/-! ## §S0  The binomial weights `w(P,i) = (-1)^i · C(P,i)` and their recursion -/

/-- The signed binomial weight `w(P,i) = (-1)^i · C(P,i)` as a complex scalar. -/
noncomputable def wC (P i : ℕ) : ℂ := (-1) ^ i * (P.choose i : ℂ)

theorem wC_zero_right (P : ℕ) : wC P 0 = 1 := by simp [wC]

theorem wC_vanish {P i : ℕ} (h : P < i) : wC P i = 0 := by
  rw [wC, Nat.choose_eq_zero_of_lt h]; simp

/-- The alternating partial-sum identity `∑_{i≤m} w(P,i) = (-1)^m C(P-1,m)` for `P = Q+1`. -/
theorem wC_partial_sum (Q m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), wC (Q + 1) i) = (-1) ^ m * (Q.choose m : ℂ) := by
  have h := Int.alternating_sum_range_choose_eq_choose (n := Q) (m := m)
  have hcast : ((∑ i ∈ Finset.range (m + 1), ((-1) ^ i * ((Q + 1).choose i) : ℤ) : ℤ) : ℂ)
      = ((-1) ^ m * (Q.choose m : ℤ) : ℤ) := by exact_mod_cast h
  rw [Int.cast_sum] at hcast
  rw [show (∑ i ∈ Finset.range (m + 1), wC (Q + 1) i)
        = ∑ i ∈ Finset.range (m + 1), (((-1) ^ i * ((Q + 1).choose i : ℤ) : ℤ) : ℂ) from
      Finset.sum_congr rfl fun i _ => by rw [wC]; push_cast; ring]
  rw [hcast]; push_cast; ring

/-- **The combine recursion** `m · w(P,m) = -P · ∑_{i<m} w(P,i)`. -/
theorem wC_combine (P m : ℕ) :
    (m : ℂ) * wC P m = -(P : ℂ) * ∑ i ∈ Finset.range m, wC P i := by
  cases P with
  | zero =>
    cases m with
    | zero => simp [wC]
    | succ k => rw [wC_vanish (by omega : (0 : ℕ) < k + 1)]; simp
  | succ Q =>
    cases m with
    | zero => simp [wC]
    | succ k =>
      rw [wC_partial_sum Q k, wC]
      have habs : (Q + 1) * Q.choose k = (Q + 1).choose (k + 1) * (k + 1) :=
        Nat.add_one_mul_choose_eq Q k
      have habsC : ((Q + 1 : ℕ) : ℂ) * (Q.choose k : ℂ)
          = ((Q + 1).choose (k + 1) : ℂ) * ((k + 1 : ℕ) : ℂ) := by exact_mod_cast habs
      push_cast at habsC ⊢
      rw [pow_succ]
      ring_nf
      ring_nf at habsC
      linear_combination ((-1 : ℂ) ^ k) * habsC

/-! ## §S1  The cross-charge single-mode binomial contraction (same-sign) -/

/-- The RHS of the cross contraction: a `(P+1)`-term binomial sum (range `N+1`, extra terms
vanish since `aExpCZ m (N-i) = 0` for `i > N`). -/
noncomputable def RHScontr (m m' : ℤ) (P : ℕ) (N b : ℤ) : End ℂ B :=
  ∑ i ∈ Finset.range (N.toNat + 1),
    wC P i • (EminusC m' (b - (i : ℤ))).comp (aExpCZ m (N - (i : ℤ)))

/-- `RHScontr` is insensitive to enlarging the summation range past `N.toNat`. -/
theorem RHScontr_range (m m' : ℤ) (P : ℕ) (N b : ℤ) (K : ℕ) (hK : N.toNat ≤ K) :
    RHScontr m m' P N b
      = ∑ i ∈ Finset.range (K + 1),
          wC P i • (EminusC m' (b - (i : ℤ))).comp (aExpCZ m (N - (i : ℤ))) := by
  rw [RHScontr]
  refine Finset.sum_subset (by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_
  intro i _ hi
  simp only [Finset.mem_range, not_lt] at hi
  rw [aExpCZ_neg m (show N - (i : ℤ) < 0 by omega), LinearMap.comp_zero, smul_zero]

/-- **The shift double-sum reindex.**  For an operator family `g : ℕ → End ℂ B` that vanishes
above `T` (`g j = 0` for `T < j`), the convolution
`∑_{i≤T} wᵢ · ∑_{r<T} g(i+r+1) = ∑_{j≤T} (∑_{i<j} wᵢ) · g j`.
The pair `(i,r) ↦ j = i+r+1` is the engine of the `wC_combine` telescope. -/
theorem shift_reindex (P T : ℕ) (g : ℕ → End ℂ B) (hg : ∀ j, T < j → g j = 0) :
    (∑ i ∈ Finset.range (T + 1), wC P i • ∑ r ∈ Finset.range T, g (i + r + 1))
      = ∑ j ∈ Finset.range (T + 1), (∑ i ∈ Finset.range j, wC P i) • g j := by
  -- Per-`i`: drop the vanishing tail then reindex `r ↦ i+r+1` to `∑_{i<j≤T} g j`.
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
  -- now swap the two finite sums and pull the indicator into the inner range
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

/-- **The cross-charge single-mode contraction** (same-sign, `P = 2mm' ≥ 0` finite binomial):
`(aExpCZ m N) ∘ (EminusC m' b) = ∑_{i} (-1)^i C(P,i) • (EminusC m' (b-i)) ∘ (aExpCZ m (N-i))`.
Mirrors `EminusCm1_contraction` (charge `(-1,-1)`, `P = 2`) but with general binomial weights;
the coefficient telescope is closed by `wC_combine` instead of `sdiff_telescope`. -/
theorem crossContr (m m' : ℤ) (P : ℕ) (hP : (P : ℤ) = 2 * m * m') (N b : ℤ) :
    (aExpCZ m N).comp (EminusC m' b) = RHScontr m m' P N b := by
  suffices H : ∀ n : ℕ, ∀ N b : ℤ, N.toNat ≤ n →
      (aExpCZ m N).comp (EminusC m' b) = RHScontr m m' P N b by
    exact H N.toNat N b le_rfl
  intro n
  induction n with
  | zero =>
    intro N b hN
    rw [RHScontr]
    by_cases h0 : N = 0
    · subst h0
      rw [aExpCZ_zero, LinearMap.id_comp, show (0 : ℤ).toNat + 1 = 1 from rfl,
        Finset.sum_range_one, wC, pow_zero, Nat.choose_zero_right]
      simp only [Nat.cast_one, mul_one, one_smul, Nat.cast_zero, sub_zero, aExpCZ_zero,
        LinearMap.comp_id]
    · rw [aExpCZ_neg m (by omega), LinearMap.zero_comp,
        show N.toNat + 1 = 1 from by omega, Finset.sum_range_one,
        aExpCZ_neg m (show N - (0 : ℕ) < 0 by omega), LinearMap.comp_zero, smul_zero]
  | succ n ih =>
    intro N b hN
    by_cases hsmall : N.toNat ≤ n
    · exact ih N b hsmall
    · have hN1 : 1 ≤ N := by omega
      have hNne : (N : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      have hLHS : (aExpCZ m N).comp (EminusC m' b)
          = (N : ℂ)⁻¹ • (m : ℂ) • ∑ r ∈ Finset.range N.toNat,
              (-(α ((r : ℤ) + 1))).comp ((aExpCZ m (N - 1 - r)).comp (EminusC m' b)) := by
        rw [aExpCZ_recursion m N hN1, LinearMap.smul_comp, LinearMap.smul_comp, sum_comp']
        simp only [LinearMap.comp_assoc]
      have hexp : ∀ r ∈ Finset.range N.toNat,
          (-(α ((r : ℤ) + 1))).comp ((aExpCZ m (N - 1 - r)).comp (EminusC m' b))
            = ∑ i ∈ Finset.range (N.toNat + 1),
                wC P i • ((EminusC m' (b - (i : ℤ))).comp
                    ((-(α ((r : ℤ) + 1))).comp (aExpCZ m (N - 1 - r - (i : ℤ))))
                  - (2 * m' : ℂ) • (EminusC m' (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                      (aExpCZ m (N - 1 - r - (i : ℤ)))) := by
        intro r hr
        simp only [Finset.mem_range] at hr
        rw [ih (N - 1 - r) b (by omega), RHScontr_range m m' P (N - 1 - r) b N.toNat (by omega),
          comp_sum']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.comp_smul, move_alphaC_past_EminusC, smul_sub]
      set op : ℤ → End ℂ B := fun j => (EminusC m' (b - j)).comp (aExpCZ m (N - j)) with hop
      have hopvanish : ∀ j : ℤ, N.toNat < j → op j = 0 := fun j hj => by
        rw [hop]; dsimp only
        rw [aExpCZ_neg m (show N - j < 0 by omega), LinearMap.comp_zero]
      -- MAIN reassembly (per i): m • ∑_r (-α_{r+1})∘aExpCZ((N-i)-1-r) = (N-i) • aExpCZ(N-i)
      have hMain : ∀ i ∈ Finset.range (N.toNat + 1),
          (m : ℂ) • ((EminusC m' (b - (i : ℤ))).comp
              (∑ r ∈ Finset.range N.toNat,
                (-(α ((r : ℤ) + 1))).comp (aExpCZ m (N - 1 - r - (i : ℤ)))))
            = ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [show (∑ r ∈ Finset.range N.toNat,
                (-(α ((r : ℤ) + 1))).comp (aExpCZ m (N - 1 - r - (i : ℤ))))
              = ∑ r ∈ Finset.range N.toNat,
                (-(α ((r : ℤ) + 1))).comp (aExpCZ m ((N - i) - 1 - r)) from
            Finset.sum_congr rfl fun r _ => by
              rw [show (N : ℤ) - 1 - r - (i : ℤ) = (N - i) - 1 - r from by ring],
          ← LinearMap.comp_smul, aExpCZ_sum_reassembly m (N - i) N.toNat (by omega),
          LinearMap.comp_smul]
      -- Transform the main goal: recursion, expand inner via `hexp`, interchange `∑_r ∑_i`.
      rw [hLHS, Finset.sum_congr rfl hexp, Finset.sum_comm]
      -- Per-`i`: collapse `∑_r` of the summand using `hMain` (MAIN) and the shift form (SHIFT).
      have hcollapse : ∀ i ∈ Finset.range (N.toNat + 1),
          (∑ r ∈ Finset.range N.toNat,
              wC P i • ((EminusC m' (b - (i : ℤ))).comp
                  ((-(α ((r : ℤ) + 1))).comp (aExpCZ m (N - 1 - r - (i : ℤ))))
                - (2 * m' : ℂ) • (EminusC m' (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                    (aExpCZ m (N - 1 - r - (i : ℤ)))))
            = wC P i • (EminusC m' (b - (i : ℤ))).comp
                  (∑ r ∈ Finset.range N.toNat,
                    (-(α ((r : ℤ) + 1))).comp (aExpCZ m (N - 1 - r - (i : ℤ))))
              - (2 * m' : ℂ) • wC P i • (∑ r ∈ Finset.range N.toNat,
                  op ((i : ℤ) + r + 1)) := by
        intro i _
        rw [show (∑ r ∈ Finset.range N.toNat,
              wC P i • ((EminusC m' (b - (i : ℤ))).comp
                  ((-(α ((r : ℤ) + 1))).comp (aExpCZ m (N - 1 - r - (i : ℤ))))
                - (2 * m' : ℂ) • (EminusC m' (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                    (aExpCZ m (N - 1 - r - (i : ℤ)))))
            = (∑ r ∈ Finset.range N.toNat,
                wC P i • (EminusC m' (b - (i : ℤ))).comp
                  ((-(α ((r : ℤ) + 1))).comp (aExpCZ m (N - 1 - r - (i : ℤ)))))
              - (∑ r ∈ Finset.range N.toNat,
                  (2 * m' : ℂ) • wC P i • op ((i : ℤ) + r + 1)) from by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [smul_sub, smul_comm (wC P i) (2 * m' : ℂ)]
          rw [hop]; dsimp only
          rw [show b - (i : ℤ) - ((r : ℤ) + 1) = b - ((i : ℤ) + r + 1) from by ring,
            show N - 1 - (r : ℤ) - (i : ℤ) = N - ((i : ℤ) + r + 1) from by ring]]
        rw [← Finset.smul_sum, comp_sum', ← Finset.smul_sum, ← Finset.smul_sum]
      rw [Finset.sum_congr rfl hcollapse]
      -- distribute m• and N⁻¹•, split into MAIN and SHIFT totals
      rw [Finset.sum_sub_distrib, smul_sub]
      -- MAIN total = ∑_i wC i • (N-i)•op i
      have hMtot : (m : ℂ) • (∑ i ∈ Finset.range (N.toNat + 1),
            wC P i • (EminusC m' (b - (i : ℤ))).comp
              (∑ r ∈ Finset.range N.toNat,
                (-(α ((r : ℤ) + 1))).comp (aExpCZ m (N - 1 - r - (i : ℤ)))))
          = ∑ i ∈ Finset.range (N.toNat + 1),
              wC P i • (((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ)) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [smul_comm (m : ℂ) (wC P i), hMain i hi]
      -- SHIFT total: pull P = m•2m', use shift_reindex
      have hPeqC : (m : ℂ) * (2 * m' : ℂ) = (P : ℂ) := by
        have hPc : ((P : ℤ) : ℂ) = ((2 * m * m' : ℤ) : ℂ) := by rw [hP]
        push_cast at hPc; rw [hPc]; ring
      have hStot : (m : ℂ) • (∑ i ∈ Finset.range (N.toNat + 1),
            (2 * m' : ℂ) • wC P i • (∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1)))
          = (P : ℂ) • ∑ j ∈ Finset.range (N.toNat + 1),
              (∑ i ∈ Finset.range j, wC P i) • op (j : ℤ) := by
        rw [Finset.smul_sum]
        rw [show (∑ i ∈ Finset.range (N.toNat + 1),
              (m : ℂ) • (2 * m' : ℂ) • wC P i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
            = (P : ℂ) • ∑ i ∈ Finset.range (N.toNat + 1),
                wC P i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1) from by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, hPeqC]]
        congr 1
        -- reindex via shift_reindex (with op shifted to ℕ-indices)
        rw [show (∑ i ∈ Finset.range (N.toNat + 1),
                wC P i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
              = ∑ i ∈ Finset.range (N.toNat + 1),
                  wC P i • ∑ r ∈ Finset.range N.toNat,
                    (fun s : ℕ => op (s : ℤ)) (i + r + 1) from
            Finset.sum_congr rfl fun i _ => by
              refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
              push_cast; ring_nf,
          shift_reindex P N.toNat (fun s => op (s : ℤ))
            (fun j hj => hopvanish (j : ℤ) (by exact_mod_cast hj))]
      rw [hMtot, hStot, inv_smul_eq_iff₀ hNne]
      -- assemble RHS as ∑_j (N • wC j) • op j and compare coefficient-wise via wC_combine
      rw [RHScontr]
      rw [show ((N : ℂ) • ∑ i ∈ Finset.range (N.toNat + 1),
              wC P i • (EminusC m' (b - (i : ℤ))).comp (aExpCZ m (N - (i : ℤ))))
            = ∑ j ∈ Finset.range (N.toNat + 1), ((N : ℂ) * wC P j) • op (j : ℤ) from by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      rw [smul_smul, smul_smul, ← sub_smul]
      congr 1
      -- coefficient identity: wC j • (N - j) - P • ∑_{i<j} wC i = N * wC j
      have hcomb := wC_combine P j
      push_cast
      linear_combination (-1 : ℂ) * hcomb

/-- **The `(P+1)`-term cross contraction** in `E⁺(mα)`/`E⁻(m'α)` coefficient form (same-sign):
`(E⁺(mα)_a) ∘ (E⁻(m'α)_b) = ∑_{i=0}^{P} (-1)^i C(P,i) • (E⁻(m'α)_{b-i}) ∘ (E⁺(mα)_{a+i})`. -/
theorem contr_P (m m' : ℤ) (P : ℕ) (hP : (P : ℤ) = 2 * m * m') (a b : ℤ) :
    (EplusC m a).comp (EminusC m' b)
      = ∑ i ∈ Finset.range (P + 1),
          wC P i • (EminusC m' (b - (i : ℤ))).comp (EplusC m (a + (i : ℤ))) := by
  rw [EplusC_eq_aExpCZ m a, crossContr m m' P hP (-a) b, RHScontr]
  -- both sides as binomial sums; first reconcile the EplusC/aExpCZ index, then the range.
  have hEqterm : ∀ i : ℕ, (EminusC m' (b - (i : ℤ))).comp (aExpCZ m (-a - (i : ℤ)))
      = (EminusC m' (b - (i : ℤ))).comp (EplusC m (a + (i : ℤ))) := fun i => by
    rw [EplusC_eq_aExpCZ m (a + (i : ℤ)), show -(a + (i : ℤ)) = -a - (i : ℤ) from by ring]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hEqterm i])]
  -- reconcile ranges: term i vanishes for i > P (wC) and for i > (-a).toNat (EplusC = 0).
  set term : ℕ → End ℂ B :=
    fun i => wC P i • (EminusC m' (b - (i : ℤ))).comp (EplusC m (a + (i : ℤ))) with hterm
  have hvanA : ∀ i, (-a).toNat < i → term i = 0 := fun i hi => by
    rw [hterm]; dsimp only
    rw [EplusC_eq_aExpCZ m (a + (i : ℤ)),
      aExpCZ_neg m (show -(a + (i : ℤ)) < 0 by omega), LinearMap.comp_zero, smul_zero]
  have hvanP : ∀ i, P < i → term i = 0 := fun i hi => by
    rw [hterm]; dsimp only; rw [wC_vanish hi, zero_smul]
  set K := max (P + 1) ((-a).toNat + 1) with hK
  rw [show (∑ i ∈ Finset.range ((-a).toNat + 1), term i) = ∑ i ∈ Finset.range K, term i from
      (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
        (fun i _ hi => by simp only [Finset.mem_range, not_lt] at hi; exact hvanA i (by omega))),
    show (∑ i ∈ Finset.range (P + 1), term i) = ∑ i ∈ Finset.range K, term i from
      (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
        (fun i _ hi => by simp only [Finset.mem_range, not_lt] at hi; exact hvanP i (by omega)))]

/-! ## §S2  Cross-charge commutativities and the cross four-fold `TvX` -/

/-- General cross-charge creation-half commutativity (both left-mult on commutative `B`). -/
theorem EminusC_comm_cross (m m' a b : ℤ) :
    (EminusC m a).comp (EminusC m' b) = (EminusC m' b).comp (EminusC m a) := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply]
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [EminusC_apply, EminusC_apply, if_pos ha, if_pos hb, EminusOpC, EminusOpC,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
        LinearMap.mulLeft_apply, mul_left_comm]
    · rw [EminusC_neg m' (show b < 0 by omega)]; simp
  · rw [EminusC_neg m (show a < 0 by omega)]; simp

/-- General cross-charge annihilation-half commutativity. -/
theorem EplusC_comm_cross (m m' a b : ℤ) :
    (EplusC m a).comp (EplusC m' b) = (EplusC m' b).comp (EplusC m a) := by
  rw [EplusC_eq_aExpCZ, EplusC_eq_aExpCZ]
  by_cases ha : 0 ≤ -a
  · by_cases hb : 0 ≤ -b
    · rw [aExpCZ_nonneg m ha, aExpCZ_nonneg m' hb]
      exact aExpC_commute_cross m m' _ _
    · rw [aExpCZ_neg m' (show -b < 0 by omega)]; simp
  · rw [aExpCZ_neg m (show -a < 0 by omega)]; simp

/-- The cross four-fold operator `TvX m m' C D' = E⁻(mα)E⁻(m'α)E⁺(mα)E⁺(m'α)` (symmetric in the
two charge/index pairs). -/
noncomputable def TvX (m m' : ℤ) (C D' : ℤ) (x : B) : B :=
  ∑ᶠ pq : ℤ × ℤ, EminusC m pq.1 (EminusC m' pq.2 (EplusC m (C - pq.1) (EplusC m' (D' - pq.2) x)))

/-- `TvX` is symmetric under swapping the two charge/index pairs. -/
theorem TvX_symm (m m' C D' : ℤ) (x : B) : TvX m m' C D' x = TvX m' m D' C x := by
  rw [TvX, TvX, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
    (f := fun pq : ℤ × ℤ =>
      EminusC m' pq.1 (EminusC m pq.2 (EplusC m' (D' - pq.1) (EplusC m (C - pq.2) x))))]
  refine finsum_congr fun pq => ?_
  obtain ⟨p, q⟩ := pq
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  have hPP : EplusC m (C - p) (EplusC m' (D' - q) x)
      = EplusC m' (D' - q) (EplusC m (C - p) x) := by
    have := DFunLike.congr_fun (EplusC_comm_cross m m' (C - p) (D' - q)) x
    simpa [LinearMap.comp_apply] using this
  have hE : EminusC m p (EminusC m' q (EplusC m (C - p) (EplusC m' (D' - q) x)))
      = EminusC m' q (EminusC m p (EplusC m (C - p) (EplusC m' (D' - q) x))) := by
    have := DFunLike.congr_fun (EminusC_comm_cross m m' p q)
      (EplusC m (C - p) (EplusC m' (D' - q) x))
    simpa [LinearMap.comp_apply] using this
  rw [hE, hPP]

/-! ## §S3  Support finiteness and nesting for the cross four-fold -/

/-- For fixed `b`, `q ↦ E⁺(m'α)_{b-q} y` has finite support. -/
theorem EpCm_shift_support_finite (m' b : ℤ) (y : B) :
    (Function.support (fun q : ℤ => EplusC m' (b - q) y)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField m' y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h; exact hq (by rw [EplusC_pos m' (show 0 < b - q by omega)]; rfl)
  · by_contra h; exact hq (hB0 (b - q) (by omega))

/-- The double `E⁺E⁺` shift has finite support. -/
theorem EpEpX_support_finite (m m' a b : ℤ) (x : B) :
    (Function.support
      (fun pq : ℤ × ℤ => EplusC m (a - pq.1) (EplusC m' (b - pq.2) x))).Finite := by
  set Sq := Function.support (fun q : ℤ => EplusC m' (b - q) x) with hSq
  have hSqfin : Sq.Finite := EpCm_shift_support_finite m' b x
  set Pr := ⋃ q ∈ Sq, Function.support (fun p : ℤ => EplusC m (a - p) (EplusC m' (b - q) x)) with hP
  have hPfin : Pr.Finite := hSqfin.biUnion (fun q _ => EpCm_shift_support_finite m a _)
  apply Set.Finite.subset (hPfin.prod hSqfin)
  intro pq hpq
  rw [Function.mem_support] at hpq
  have hq : pq.2 ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h; exact hpq (by rw [h, map_zero])
  refine Set.mem_prod.mpr ⟨?_, hq⟩
  rw [hP]; exact Set.mem_biUnion hq (Function.mem_support.mpr hpq)

/-- The cross four-fold has finite support. -/
theorem TvX_fourfold_support_finite (m m' a b : ℤ) (x : B) :
    (Function.support
      (fun pq : ℤ × ℤ =>
        EminusC m pq.1 (EminusC m' pq.2 (EplusC m (a - pq.1) (EplusC m' (b - pq.2) x))))).Finite := by
  apply Set.Finite.subset (EpEpX_support_finite m m' a b x)
  intro pq hpq
  rw [Function.mem_support] at hpq ⊢
  intro h; exact hpq (by rw [h, map_zero, map_zero])

/-- `TvX` as a nested `q`-then-`p` double sum. -/
theorem TvX_eq_nestQ (m m' C D' : ℤ) (x : B) :
    TvX m m' C D' x = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      EminusC m p (EminusC m' q (EplusC m (C - p) (EplusC m' (D' - q) x))) := by
  rw [TvX, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
      (f := fun pq : ℤ × ℤ =>
        EminusC m pq.1 (EminusC m' pq.2 (EplusC m (C - pq.1) (EplusC m' (D' - pq.2) x))))]
  rw [finsum_curry _ ((TvX_fourfold_support_finite m m' C D' x).preimage
      ((Equiv.prodComm ℤ ℤ).injective.injOn))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]

/-- The `EEC c`-defining marginal `q ↦ E⁻(cα)_q E⁺(cα)_{s-q} x` has finite support. -/
theorem EECc_marg_finite (c s : ℤ) (x : B) :
    (Function.support (fun q : ℤ => EminusC c q (EplusC c (s - q) x))).Finite := by
  apply Set.Finite.subset (EpCm_shift_support_finite c s x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h; exact hq (by rw [h, map_zero])

/-- The cross `EE`-nesting: `EEC m c (EEC m' d x)` as a nested `q,p` double finsum. -/
theorem EEC_nest_cross (m m' c d : ℤ) (x : B) :
    EEC m c (EEC m' d x) = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      EminusC m p (EplusC m (c - p) (EminusC m' q (EplusC m' (d - q) x))) := by
  rw [EEC_apply_conv m' d x, map_finsum (EEC m c) (EECc_marg_finite m' d x)]
  refine finsum_congr fun q => ?_
  rw [EEC_apply_conv m c]

/-- The inner reorder via `contr_P`: swap the middle `E⁺(mα)_{c-p} E⁻(m'α)_q` into the
`(P+1)`-term binomial sum, leaving `TvX`-aligned `E⁻(m'α)_{q-i} E⁺(mα)_{c-p+i}`. -/
theorem inner_reorder_P (m m' : ℤ) (P : ℕ) (hP : (P : ℤ) = 2 * m * m') (c d p q : ℤ) (x : B) :
    EminusC m p (EplusC m (c - p) (EminusC m' q (EplusC m' (d - q) x)))
      = ∑ i ∈ Finset.range (P + 1),
          wC P i • EminusC m p (EminusC m' (q - (i : ℤ))
            (EplusC m (c - p + (i : ℤ)) (EplusC m' (d - q) x))) := by
  have h := DFunLike.congr_fun (contr_P m m' P hP (c - p) q) (EplusC m' (d - q) x)
  rw [LinearMap.sum_apply] at h
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]

/-- The `i`-th resummed piece equals the shifted cross four-fold `TvX (c+i) (d-i)`. -/
theorem termX_i (m m' c d : ℤ) (i : ℕ) (x : B) :
    (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
        EminusC m p (EminusC m' (q - (i : ℤ))
          (EplusC m (c - p + (i : ℤ)) (EplusC m' (d - q) x))))
      = TvX m m' (c + (i : ℤ)) (d - (i : ℤ)) x := by
  rw [TvX_eq_nestQ,
    ← finsum_comp_equiv (Equiv.addRight (i : ℤ))
      (f := fun q : ℤ =>
        ∑ᶠ p : ℤ, EminusC m p (EminusC m' (q - (i : ℤ))
          (EplusC m (c - p + (i : ℤ)) (EplusC m' (d - q) x))))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.coe_addRight]
  rw [show q + (i : ℤ) - (i : ℤ) = q from by ring,
    show c - p + (i : ℤ) = (c + (i : ℤ)) - p from by ring,
    show d - (q + (i : ℤ)) = (d - (i : ℤ)) - q from by ring]

/-- Interchange a `finsum` with a `Finset.sum` (each summand finitely supported). -/
theorem finsum_finset_sum_comm {ι : Type*} (s : Finset ι) (g : ι → ℤ → B)
    (hg : ∀ i ∈ s, (Function.support (g i)).Finite) :
    (∑ᶠ q : ℤ, ∑ i ∈ s, g i q) = ∑ i ∈ s, ∑ᶠ q : ℤ, g i q := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hga : (Function.support (g a)).Finite := hg a (Finset.mem_insert_self a s)
      have hgs : ∀ i ∈ s, (Function.support (g i)).Finite :=
        fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hsum_fin : (Function.support (fun q => ∑ i ∈ s, g i q)).Finite := by
        apply Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet s)
          (fun i _ => hgs i (by simpa using ‹i ∈ s›)))
        intro q hq; rw [Function.mem_support] at hq
        rw [Set.mem_iUnion]
        by_contra h
        exact hq (Finset.sum_eq_zero fun i hi => by
          by_contra hne
          exact h ⟨i, by rw [Set.mem_iUnion]; exact ⟨hi, Function.mem_support.mpr hne⟩⟩)
      rw [Finset.sum_insert ha, ← ih hgs]
      rw [show (fun q => ∑ i ∈ insert a s, g i q)
            = fun q => g a q + ∑ i ∈ s, g i q from
          funext fun q => by rw [Finset.sum_insert ha]]
      rw [finsum_add_distrib hga hsum_fin]

/-- Per-`i` `p`-support finiteness: bounded by the `E⁺(mα)` field factor. -/
theorem ee_p_finite (m m' c d i q : ℤ) (x : B) :
    (Function.support (fun p : ℤ =>
      EminusC m p (EminusC m' (q - i) (EplusC m (c - p + i) (EplusC m' (d - q) x))))).Finite := by
  apply Set.Finite.subset (EpCm_shift_support_finite m (c + i) (EplusC m' (d - q) x))
  intro p hp; rw [Function.mem_support] at hp ⊢
  intro h
  apply hp
  rw [show c - p + i = c + i - p from by ring, h, map_zero, map_zero]

/-- Per-`i` `q`-support finiteness for the outer sum. -/
theorem ee_q_finite (m m' c d i : ℤ) (x : B) :
    (Function.support (fun q : ℤ => ∑ᶠ p : ℤ,
      EminusC m p (EminusC m' (q - i) (EplusC m (c - p + i) (EplusC m' (d - q) x))))).Finite := by
  apply Set.Finite.subset (EpCm_shift_support_finite m' d x)
  intro q hq; rw [Function.mem_support] at hq ⊢
  intro h
  refine hq (finsum_eq_zero_of_forall_eq_zero fun p => ?_)
  rw [h, map_zero, map_zero, map_zero]

/-- **The cross four-fold re-summation** (same-sign): `EEC m c (EEC m' d x) =
∑_{i=0}^{P} (-1)^i C(P,i) • TvX m m' (c+i) (d-i) x`. -/
theorem eeMaster_P (m m' : ℤ) (P : ℕ) (hP : (P : ℤ) = 2 * m * m') (c d : ℤ) (x : B) :
    EEC m c (EEC m' d x)
      = ∑ i ∈ Finset.range (P + 1), wC P i • TvX m m' (c + (i : ℤ)) (d - (i : ℤ)) x := by
  rw [EEC_nest_cross]
  -- apply inner_reorder_P per (q,p), then interchange the finite i-sum out
  rw [show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
            EminusC m p (EplusC m (c - p) (EminusC m' q (EplusC m' (d - q) x))))
        = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ, ∑ i ∈ Finset.range (P + 1),
            wC P i • EminusC m p (EminusC m' (q - (i : ℤ))
              (EplusC m (c - p + (i : ℤ)) (EplusC m' (d - q) x))) from
      finsum_congr fun q => finsum_congr fun p => inner_reorder_P m m' P hP c d p q x]
  -- interchange inner p-sum with the finite i-sum
  -- interchange the inner p-sum with the finite i-sum (per q)
  rw [show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ, ∑ i ∈ Finset.range (P + 1),
            wC P i • EminusC m p (EminusC m' (q - (i : ℤ))
              (EplusC m (c - p + (i : ℤ)) (EplusC m' (d - q) x))))
        = ∑ᶠ q : ℤ, ∑ i ∈ Finset.range (P + 1), wC P i • ∑ᶠ p : ℤ,
            EminusC m p (EminusC m' (q - (i : ℤ))
              (EplusC m (c - p + (i : ℤ)) (EplusC m' (d - q) x))) from
      finsum_congr fun q => by
        rw [finsum_finset_sum_comm (Finset.range (P + 1))
          (fun i p => wC P i • EminusC m p (EminusC m' (q - (i : ℤ))
            (EplusC m (c - p + (i : ℤ)) (EplusC m' (d - q) x)))
            ) (fun i _ => (ee_p_finite m m' c d (i : ℤ) q x).subset
              (fun p hp => by
                rw [Function.mem_support] at hp ⊢
                simp only [] at hp ⊢
                exact fun h => hp (by rw [h, smul_zero])))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_finsum' (wC P i) (ee_p_finite m m' c d (i : ℤ) q x)]]
  -- interchange the outer q-sum with the finite i-sum
  rw [finsum_finset_sum_comm (Finset.range (P + 1))
      (fun i q => wC P i • ∑ᶠ p : ℤ, EminusC m p (EminusC m' (q - (i : ℤ))
        (EplusC m (c - p + (i : ℤ)) (EplusC m' (d - q) x)))
        ) (fun i _ => (ee_q_finite m m' c d (i : ℤ) x).subset
          (fun q hq => by
            rw [Function.mem_support] at hq ⊢
            simp only [] at hq ⊢
            exact fun h => hq (by rw [h, smul_zero])))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_finsum' (wC P i) (ee_q_finite m m' c d (i : ℤ) x), termX_i]

/-! ## §S4  The shifted cross-commutativity and same-sign locality -/

/-- Binomial weight symmetry `wC P (P-i) = (-1)^P · wC P i` for `i ≤ P`. -/
theorem wC_symm {P i : ℕ} (hi : i ≤ P) : wC P (P - i) = (-1 : ℂ) ^ P * wC P i := by
  rw [wC, wC, Nat.choose_symm hi]
  have hpow : ((-1 : ℂ)) ^ (P - i) = (-1 : ℂ) ^ P * (-1 : ℂ) ^ i := by
    have hmul : ((-1 : ℂ)) ^ (P - i) * (-1 : ℂ) ^ i = (-1 : ℂ) ^ P := by
      rw [← pow_add, show P - i + i = P from by omega]
    have hsq : ((-1 : ℂ)) ^ i * (-1 : ℂ) ^ i = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc ((-1 : ℂ)) ^ (P - i)
        = ((-1 : ℂ)) ^ (P - i) * ((-1 : ℂ) ^ i * (-1 : ℂ) ^ i) := by rw [hsq, mul_one]
      _ = (((-1 : ℂ)) ^ (P - i) * (-1 : ℂ) ^ i) * (-1 : ℂ) ^ i := by ring
      _ = (-1 : ℂ) ^ P * (-1 : ℂ) ^ i := by rw [hmul]
  rw [hpow]; ring

/-- **The shifted cross-commutativity** `EEC m (a-P) (EEC m' b x) = EEC m' (b-P) (EEC m a x)`
for `P = 2mm'` (even).  The algebraic heart of the same-sign locality (bound `0`). -/
theorem shift_comm_P (m m' : ℤ) (P : ℕ) (hP : (P : ℤ) = 2 * m * m') (a b : ℤ) (x : B) :
    EEC m (a - P) (EEC m' b x) = EEC m' (b - P) (EEC m a x) := by
  have hPeven : Even P := by
    have hPe : (P : ℤ) = 2 * (m * m') := by rw [hP]; ring
    have h2 : (2 : ℤ) ∣ (P : ℤ) := ⟨m * m', hPe⟩
    have h2' : (2 : ℕ) ∣ P := by exact_mod_cast h2
    exact (even_iff_two_dvd).mpr h2'
  have hpowP : ((-1 : ℂ)) ^ P = 1 := hPeven.neg_one_pow
  rw [eeMaster_P m m' P hP (a - P) b x, eeMaster_P m' m P (by rw [hP]; ring) (b - P) a x]
  -- RHS: reindex i ↦ P - i and use TvX_symm + wC_symm + (-1)^P = 1
  rw [show (∑ i ∈ Finset.range (P + 1), wC P i • TvX m' m (b - P + (i : ℤ)) (a - (i : ℤ)) x)
        = ∑ i ∈ Finset.range (P + 1),
            wC P (P - i) • TvX m' m (b - P + ((P - i : ℕ) : ℤ)) (a - ((P - i : ℕ) : ℤ)) x from
      (Finset.sum_nbij' (i := fun i => P - i) (j := fun i => P - i)
        (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
        (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
        (fun i hi => by simp only [Finset.mem_range] at hi; simp only []; omega)
        (fun i hi => by simp only [Finset.mem_range] at hi; simp only []; omega)
        (fun i _ => rfl)).symm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [wC_symm (by omega : i ≤ P), hpowP, one_mul,
    TvX_symm m' m (b - P + ((P - i : ℕ) : ℤ)) (a - ((P - i : ℕ) : ℤ)) x]
  congr 2 <;> (rw [show ((P - i : ℕ) : ℤ) = (P : ℤ) - (i : ℤ) from by omega]; ring)

/-- **The same-sign bracket vanishes on every basis state** (`m*m' ≥ 1`, bound `0`). -/
theorem Yemα_sameSign_bracket_on_state (m m' : ℤ) (hsign : 1 ≤ m * m')
    (j k n : ℤ) (p : B) :
    bracketDist (Yemα m) (Yemα m') j k (p ⊗ₜ[ℂ] eVec n) = 0 := by
  have hpos : 0 ≤ 2 * m * m' := by nlinarith [hsign]
  obtain ⟨P, hP⟩ : ∃ P : ℕ, (P : ℤ) = 2 * m * m' := ⟨(2 * m * m').toNat, by omega⟩
  rw [reduce_mixed]
  rw [show ((j - 2 * m * n) - 2 * m * m' : ℤ) = (j - 2 * m * n) - P from by rw [hP],
    show ((k - 2 * m' * n) - 2 * m' * m : ℤ) = (k - 2 * m' * n) - P from by rw [hP]; ring,
    shift_comm_P m m' P hP (j - 2 * m * n) (k - 2 * m' * n) p, sub_self,
    TensorProduct.zero_tmul]

theorem Yemα_sameSign_local (m m' : ℤ) (hsign : 1 ≤ m * m') :
    Local (Yemα m) (Yemα m') :=
  local_of_bracket_on_state (Yemα_sameSign_bracket_on_state m m' hsign)

end VOA.LatExp
