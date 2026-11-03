/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeExpMomentum

/-!
# `L₋₁`-covariance of the lattice exponential dressing — crux A, half (**)

For the reconstruction translation `Trec = rTensor(L₋₁) + ½·rTensor(α₋₁)·zGradeOp`, the covariance
`DCovariant Trec (Yemα m)` reduces (on a basis state `p ⊗ e^{nα}`) to two boson identities on the
Fock factor `B`.  The first, `(*)`, is `alphaNeg1_comm_EEC` (in `LatticeExpMomentum`).  This file
builds the second, `(**)`, the `L₋₁`-on-dressing derivative.  Its first ingredient — proved here —
is that the annihilation half `E⁺` is *cleanly* `L₋₁`-covariant (no boundary defect, because the
exponent's would-be boundary term is `α₀ = 0`):

* `LvirN_comm_aExpCZ c N : [L₋₁, aExpCZ c N] = (1-N)·aExpCZ c (N-1)`

proved by strong induction on `N.toNat` via the `aExpC` Newton recursion: the bracket of each
Newton summand splits (Leibniz) into an `α_j`-piece and an IH-piece; after reindexing the `α_j`-sum
(`j=0` term vanishes since `α₀ = 0`) and dropping the `j=N-1` IH-boundary (`aExpCZ c (-1) = 0`), the
two combine to `-N·(Newton sum for N-1)`, which reassembles via `aExpCZ_sum_reassembly`.

All `pbw`-free / axiom-clean.  (Algebra note: `End ℂ B`'s `Neg` is `LinearMap.instNeg`, which the
ring lemmas `mul_neg`/`neg_mul`/`smul_sub` cannot key on; we route negations through
`(-1 : ℂ) • ·` + `neg_one_smul` and use term-mode `(smul_sub _ _ _).symm`.)
-/

open VOA VOA.LatExp VOA.LatticeVOA
open Module (End)
open scoped TensorProduct BigOperators

namespace VOA.LatExp

/-- `[L₋₁, α_{j+1}] = -(j+1)·α_j` (the boson current is L₋₁-covariant). -/
theorem LvirN_comm_alpha_succ (j : ℤ) :
    HeisenbergN.LvirN 1 2 (-1) * α (j + 1) - α (j + 1) * HeisenbergN.LvirN 1 2 (-1)
      = (-((j + 1 : ℤ) : ℂ)) • α j := by
  have h := HeisenbergN.LvirN_comm_oscN 1 2 (by norm_num : (2 : ℂ) ≠ 0) 0 (-1) (j + 1)
  rw [show (-1 : ℤ) + (j + 1) = j from by ring] at h
  exact h

/-- **E⁺ is `L₋₁`-covariant**: `[LvirN(-1), aExpCZ c N] = (1-N)·aExpCZ c (N-1)`. The annihilation
exponential has NO boundary defect (`α₀ = 0`).  Proved by strong induction on `N.toNat` via the
`aExpC` Newton recursion: the bracket of each `(-α_{j+1})∘aExpCZ` term splits (Leibniz) into an
`α_j`-piece and an IH-piece; after reindexing the `α_j`-sum (`j=0` term vanishes since `α₀=0`) and
dropping the `j=N-1` IH-boundary (`aExpCZ c (-1) = 0`), the two combine to `-N·(Newton sum N-1)`,
which reassembles to `(1-N)·aExpCZ c (N-1)`. -/
theorem LvirN_comm_aExpCZ (c : ℂ) :
    ∀ N : ℤ, HeisenbergN.LvirN 1 2 (-1) * aExpCZ c N - aExpCZ c N * HeisenbergN.LvirN 1 2 (-1)
      = (1 - (N : ℂ)) • aExpCZ c (N - 1) := by
  set L : Module.End ℂ B := HeisenbergN.LvirN 1 2 (-1) with hL
  -- bracket-of-product is a derivation
  have hderiv : ∀ X Y : End ℂ B, L * (X * Y) - (X * Y) * L
      = (L * X - X * L) * Y + X * (L * Y - Y * L) := by
    intro X Y; simp only [sub_mul, mul_sub, mul_assoc]; abel
  suffices H : ∀ n : ℕ, ∀ N : ℤ, N.toNat ≤ n →
      L * aExpCZ c N - aExpCZ c N * L = (1 - (N : ℂ)) • aExpCZ c (N - 1) by
    exact fun N => H N.toNat N le_rfl
  intro n
  induction n with
  | zero =>
    intro N hN
    by_cases h0 : N = 0
    · subst h0
      rw [aExpCZ_zero, aExpCZ_neg c (show (0 : ℤ) - 1 < 0 by omega), ← Module.End.one_eq_id,
        mul_one, one_mul, sub_self]
      exact (smul_zero _).symm
    · rw [aExpCZ_neg c (by omega : N < 0), aExpCZ_neg c (show N - 1 < 0 by omega),
        mul_zero, zero_mul, sub_self]
      exact (smul_zero _).symm
  | succ n ih =>
    intro N hM
    by_cases hsmall : N.toNat ≤ n
    · exact ih N hsmall
    · have hN1 : 1 ≤ N := by omega
      have hNne : (N : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      have hNtoNat : N.toNat = (N - 1).toNat + 1 := by omega
      -- per-term bracket of each Newton summand (Leibniz + α-bracket + IH)
      have pt : ∀ j : ℕ,
          L * ((-(α ((j : ℤ) + 1))) * aExpCZ c (N - 1 - j))
            - ((-(α ((j : ℤ) + 1))) * aExpCZ c (N - 1 - j)) * L
          = ((j : ℂ) + 1) • (α (j : ℤ) * aExpCZ c (N - 1 - j))
            + ((j : ℂ) + 2 - (N : ℂ)) • ((-(α ((j : ℤ) + 1))) * aExpCZ c (N - 2 - j)) := by
        intro j
        rw [hderiv]
        have hfst : L * (-(α ((j : ℤ) + 1))) - (-(α ((j : ℤ) + 1))) * L
            = ((j : ℂ) + 1) • α (j : ℤ) := by
          have h := LvirN_comm_alpha_succ (j : ℤ)
          rw [← hL] at h
          rw [show (-(α ((j : ℤ) + 1))) = ((-1 : ℂ)) • α ((j : ℤ) + 1) from (neg_one_smul ℂ _).symm,
            mul_smul_comm, smul_mul_assoc,
            show ((-1 : ℂ)) • (L * α ((j : ℤ) + 1)) - ((-1 : ℂ)) • (α ((j : ℤ) + 1) * L)
              = ((-1 : ℂ)) • (L * α ((j : ℤ) + 1) - α ((j : ℤ) + 1) * L) from (smul_sub _ _ _).symm,
            h, smul_smul]
          congr 1; push_cast; ring
        have hsnd : L * aExpCZ c (N - 1 - j) - aExpCZ c (N - 1 - j) * L
            = ((j : ℂ) + 2 - (N : ℂ)) • aExpCZ c (N - 2 - j) := by
          have hih := ih (N - 1 - j) (by omega)
          rw [show (N - 1 - (j : ℤ)) - 1 = N - 2 - j from by ring] at hih
          rw [hih]; congr 1; push_cast; ring
        rw [hfst, hsnd, smul_mul_assoc, mul_smul_comm]
      -- the Newton sum (in `*` form) and the recursion in terms of it
      set R := ∑ j ∈ Finset.range N.toNat, (-(α ((j : ℤ) + 1))) * aExpCZ c (N - 1 - j) with hRdef
      have hrecR : aExpCZ c N = (N : ℂ)⁻¹ • c • R := by
        rw [aExpCZ_recursion c N hN1, hRdef]; simp only [Module.End.mul_eq_comp]
      -- SA: reindex (the `j=0` term vanishes since `α 0 = 0`)
      have hSA : (∑ j ∈ Finset.range N.toNat, ((j : ℂ) + 1) • (α (j : ℤ) * aExpCZ c (N - 1 - j)))
          = ∑ i ∈ Finset.range (N - 1).toNat,
              ((i : ℂ) + 2) • (α ((i : ℤ) + 1) * aExpCZ c (N - 2 - i)) := by
        rw [hNtoNat, Finset.sum_range_succ']
        rw [show (α ((0 : ℕ) : ℤ) * aExpCZ c (N - 1 - ((0 : ℕ) : ℤ))) = 0 from by
          rw [show ((0 : ℕ) : ℤ) = 0 from rfl,
            show α (0 : ℤ) = 0 from HeisenbergN.oscN_zero 1 2 0, zero_mul], smul_zero, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 from by push_cast; ring,
          show N - 1 - ((i : ℤ) + 1) = N - 2 - i from by ring]
        congr 1
        push_cast; ring
      -- SB: the `j=N-1` term vanishes since `aExpCZ c (-1) = 0`
      have hSB : (∑ j ∈ Finset.range N.toNat,
              ((j : ℂ) + 2 - (N : ℂ)) • ((-(α ((j : ℤ) + 1))) * aExpCZ c (N - 2 - j)))
          = ∑ i ∈ Finset.range (N - 1).toNat,
              ((i : ℂ) + 2 - (N : ℂ)) • ((-(α ((i : ℤ) + 1))) * aExpCZ c (N - 2 - i)) := by
        rw [hNtoNat, Finset.sum_range_succ]
        rw [show aExpCZ c (N - 2 - ((N - 1).toNat : ℤ)) = 0 from by
          rw [show ((N - 1).toNat : ℤ) = N - 1 from by omega]
          exact aExpCZ_neg c (by omega), mul_zero, smul_zero, add_zero]
      -- bracket of R telescopes to `N • ∑ (α_{i+1} · aExpCZ c (N-2-i))`
      have hBrR : L * R - R * L
          = (N : ℂ) • ∑ i ∈ Finset.range (N - 1).toNat, α ((i : ℤ) + 1) * aExpCZ c (N - 2 - i) := by
        rw [hRdef, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
          Finset.sum_congr rfl (fun j _ => pt j), Finset.sum_add_distrib, hSA, hSB,
          ← Finset.sum_add_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (-(α ((i : ℤ) + 1))) * aExpCZ c (N - 2 - i)
            = ((-1 : ℂ)) • (α ((i : ℤ) + 1) * aExpCZ c (N - 2 - i)) from by
              rw [show (-(α ((i : ℤ) + 1))) = ((-1 : ℂ)) • α ((i : ℤ) + 1) from
                  (neg_one_smul ℂ _).symm, smul_mul_assoc],
          smul_smul, ← add_smul]
        congr 1
        ring
      -- the reassembly of the telescoped sum to the single `aExpCZ c (N-1)`
      have hfinal : c • (∑ i ∈ Finset.range (N - 1).toNat, α ((i : ℤ) + 1) * aExpCZ c (N - 2 - i))
          = (1 - (N : ℂ)) • aExpCZ c (N - 1) := by
        have hreass := aExpCZ_sum_reassembly c (N - 1) (N - 1).toNat le_rfl
        simp only [← Module.End.mul_eq_comp] at hreass
        rw [show (N - 1) - 1 = N - 2 from by ring] at hreass
        rw [show (∑ i ∈ Finset.range (N - 1).toNat, α ((i : ℤ) + 1) * aExpCZ c (N - 2 - i))
            = -(∑ i ∈ Finset.range (N - 1).toNat,
                (-(α ((i : ℤ) + 1))) * aExpCZ c (N - 2 - i)) from by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => by
            rw [show (-(α ((i : ℤ) + 1))) * aExpCZ c (N - 2 - i)
                = ((-1 : ℂ)) • (α ((i : ℤ) + 1) * aExpCZ c (N - 2 - i)) from by
                  rw [show (-(α ((i : ℤ) + 1))) = ((-1 : ℂ)) • α ((i : ℤ) + 1) from
                      (neg_one_smul ℂ _).symm, smul_mul_assoc],
              show ((-1 : ℂ)) • (α ((i : ℤ) + 1) * aExpCZ c (N - 2 - i))
                  = -(α ((i : ℤ) + 1) * aExpCZ c (N - 2 - i)) from
                    neg_one_smul ℂ (α ((i : ℤ) + 1) * aExpCZ c (N - 2 - i)), neg_neg]]
        rw [smul_neg, hreass,
          show (1 : ℂ) - (N : ℂ) = -((N - 1 : ℤ) : ℂ) from by push_cast; ring]
        exact (neg_smul ((N - 1 : ℤ) : ℂ) (aExpCZ c (N - 1))).symm
      -- assemble: pull scalars, cancel `N⁻¹·N`, finish via `hfinal`
      rw [hrecR]
      rw [show L * ((N : ℂ)⁻¹ • c • R) - ((N : ℂ)⁻¹ • c • R) * L
          = (N : ℂ)⁻¹ • c • (L * R - R * L) from by
        rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
          show (N : ℂ)⁻¹ • c • (L * R) - (N : ℂ)⁻¹ • c • (R * L)
            = (N : ℂ)⁻¹ • (c • (L * R) - c • (R * L)) from (smul_sub _ _ _).symm,
          show c • (L * R) - c • (R * L) = c • (L * R - R * L) from (smul_sub _ _ _).symm]]
      rw [hBrR, smul_comm c (N : ℂ), smul_smul, inv_mul_cancel₀ hNne, one_smul, hfinal]

/-! ## E⁻ `α₋₁`-defect covariance (the second half of `(**)`) -/

/-- `mulXN m 0 = α₋ₘ₋₁` (a creation oscillator). -/
theorem mulXN_eq_alpha (m : ℕ) : (HeisenbergN.mulXN m (0 : Fin 1) : End ℂ B) = α (-((m : ℤ) + 1)) := by
  rw [α, HeisenbergN.oscN_neg 1 2 0 (show -((m : ℤ) + 1) < 0 by omega)]
  congr 1
  omega

/-- `[L₋₁, mulXN m 0] = (m+1)·mulXN (m+1) 0` (the creation oscillator is L₋₁-covariant). -/
theorem LvirN_comm_mulXN (m : ℕ) :
    HeisenbergN.LvirN 1 2 (-1) * HeisenbergN.mulXN m (0 : Fin 1)
      - HeisenbergN.mulXN m (0 : Fin 1) * HeisenbergN.LvirN 1 2 (-1)
      = ((m : ℂ) + 1) • HeisenbergN.mulXN (m + 1) (0 : Fin 1) := by
  rw [mulXN_eq_alpha m,
    show (HeisenbergN.mulXN (m + 1) (0 : Fin 1) : End ℂ B) = α (-((m : ℤ) + 2)) from by
      rw [mulXN_eq_alpha, show -(((m + 1 : ℕ) : ℤ) + 1) = -((m : ℤ) + 2) from by push_cast; ring]]
  have h := HeisenbergN.LvirN_comm_oscN 1 2 (by norm_num : (2 : ℂ) ≠ 0) 0 (-1) (-((m : ℤ) + 1))
  rw [show (-1 : ℤ) + -((m : ℤ) + 1) = -((m : ℤ) + 2) from by ring] at h
  rw [show α (-((m : ℤ) + 1)) = HeisenbergN.oscN 1 2 0 (-((m : ℤ) + 1)) from rfl,
    show α (-((m : ℤ) + 2)) = HeisenbergN.oscN 1 2 0 (-((m : ℤ) + 2)) from rfl, h]
  congr 1; push_cast; ring

/-- `mulLeft` is ℂ-linear in its multiplier. -/
theorem mulLeft_smulC (c : ℂ) (p : B) :
    LinearMap.mulLeft ℂ (c • p) = c • LinearMap.mulLeft ℂ p := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.mulLeft_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, smul_mul_assoc]

/-- `α₋₁ = mulLeft (cVar 0)`. -/
theorem alphaNeg1_eq_mulLeft : (α (-1) : End ℂ B) = LinearMap.mulLeft ℂ (cVar 0) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.mulLeft_apply, α, HeisenbergN.oscN_apply_neg 1 2 0 (by norm_num : (-1 : ℤ) < 0), cVar]
  norm_num

/-- The `EminusOpC` Newton recursion in operator (composition) form:
`E⁻(cα)_{N+1} = (N+1)⁻¹·c·∑_{m<N+1} (mulXN m 0)·E⁻(cα)_{N-m}`. -/
theorem EminusOpC_succ_op (c : ℂ) (N : ℕ) :
    EminusOpC c (N + 1)
      = ((N : ℂ) + 1)⁻¹ • c • ∑ m ∈ Finset.range (N + 1),
          (HeisenbergN.mulXN m (0 : Fin 1) : End ℂ B) * EminusOpC c (N - m) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    EminusOpC, LinearMap.mulLeft_apply, cSchurC_succ, smul_mul_assoc, smul_mul_assoc, Finset.sum_mul]
  congr 2
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Module.End.mul_apply, HeisenbergN.mulXN_apply, EminusOpC, LinearMap.mulLeft_apply, cVar,
    mul_assoc]

/-- The abstract index-combine behind the E⁻ telescoping: `P + Q = (n+1)·∑g`. -/
theorem combinePQ (n : ℕ) (g : ℕ → End ℂ B) :
    (∑ m ∈ Finset.range (n + 1), ((m : ℂ) + 1) • g (m + 1))
      + (∑ m ∈ Finset.range (n + 1), (((n - m : ℕ) : ℂ) + 1) • g m)
    = ((n : ℂ) + 1) • ∑ i ∈ Finset.range (n + 2), g i := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, zero_add,
      Nat.sub_self, one_smul]
    abel
  | succ n ih =>
    rw [Finset.sum_range_succ (fun m => ((m : ℂ) + 1) • g (m + 1)),
      Finset.sum_range_succ (fun m => (((n + 1 - m : ℕ) : ℂ) + 1) • g m),
      Finset.sum_range_succ (fun i => g i)]
    have hQ : (∑ m ∈ Finset.range (n + 1), (((n + 1 - m : ℕ) : ℂ) + 1) • g m)
        = (∑ m ∈ Finset.range (n + 1), (((n - m : ℕ) : ℂ) + 1) • g m)
          + ∑ m ∈ Finset.range (n + 1), g m := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      simp only [Finset.mem_range] at hm
      rw [show ((n + 1 - m : ℕ) : ℂ) + 1 = (((n - m : ℕ) : ℂ) + 1) + 1 from by
        rw [show n + 1 - m = (n - m) + 1 from by omega]; push_cast; ring, add_smul, one_smul]
    rw [hQ]
    have hP : (∑ m ∈ Finset.range (n + 1), ((m : ℂ) + 1) • g (m + 1))
        = ((n : ℂ) + 1) • ∑ i ∈ Finset.range (n + 2), g i
          - (∑ m ∈ Finset.range (n + 1), (((n - m : ℕ) : ℂ) + 1) • g m) := by
      rw [eq_sub_iff_add_eq, ih]
    rw [hP, Finset.sum_range_succ (fun i => g i)]
    simp only [Nat.sub_self, Nat.cast_zero, zero_add]
    push_cast
    module

/-- **The E⁻ `α₋₁`-defect `L₋₁`-covariance**:
`[L₋₁, EminusOpC c N] = (N+1)·EminusOpC c (N+1) - c·α₋₁·EminusOpC c N`. -/
theorem LvirN_comm_EminusOpC (c : ℂ) :
    ∀ N : ℕ, HeisenbergN.LvirN 1 2 (-1) * EminusOpC c N - EminusOpC c N * HeisenbergN.LvirN 1 2 (-1)
      = ((N : ℂ) + 1) • EminusOpC c (N + 1)
        - c • (α (-1) * EminusOpC c N) := by
  set L : Module.End ℂ B := HeisenbergN.LvirN 1 2 (-1) with hL
  have hderiv : ∀ X Y : End ℂ B, L * (X * Y) - (X * Y) * L
      = (L * X - X * L) * Y + X * (L * Y - Y * L) := by
    intro X Y; simp only [sub_mul, mul_sub, mul_assoc]; abel
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  match N with
  | 0 =>
    have h0 : EminusOpC c 0 = 1 := by
      rw [EminusOpC, cSchurC_zero, LinearMap.mulLeft_one]; exact Module.End.one_eq_id.symm
    have h1 : EminusOpC c 1 = c • α (-1) := by
      rw [EminusOpC, cSchurC_one, mulLeft_smulC, ← alphaNeg1_eq_mulLeft]
    rw [h0, h1, mul_one, one_mul, sub_self, Nat.cast_zero, zero_add, one_smul, mul_one, sub_self]
  | (n + 1) =>
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hcomm : ∀ m : ℕ, (HeisenbergN.mulXN m (0 : Fin 1) : End ℂ B) * α (-1)
        = α (-1) * HeisenbergN.mulXN m 0 := by
      intro m
      refine LinearMap.ext fun x => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, HeisenbergN.mulXN_apply, alphaNeg1_eq_mulLeft,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, HeisenbergN.mulXN_apply]
      ring
    -- per-term Leibniz bracket
    have pt : ∀ m ∈ Finset.range (n + 1),
        L * ((HeisenbergN.mulXN m (0 : Fin 1)) * EminusOpC c (n - m))
          - ((HeisenbergN.mulXN m (0 : Fin 1)) * EminusOpC c (n - m)) * L
        = ((m : ℂ) + 1) • ((HeisenbergN.mulXN (m + 1) (0 : Fin 1)) * EminusOpC c ((n + 1) - (m + 1)))
          + (((n - m : ℕ) : ℂ) + 1) • ((HeisenbergN.mulXN m (0 : Fin 1)) * EminusOpC c ((n + 1) - m))
          - c • (α (-1) * ((HeisenbergN.mulXN m (0 : Fin 1)) * EminusOpC c (n - m))) := by
      intro m hm
      simp only [Finset.mem_range] at hm
      rw [hderiv, LvirN_comm_mulXN, ih (n - m) (by omega), smul_mul_assoc, mul_sub, mul_smul_comm,
        mul_smul_comm, show (n + 1) - (m + 1) = n - m from by omega,
        show (n + 1) - m = (n - m) + 1 from by omega,
        show (HeisenbergN.mulXN m (0 : Fin 1) : End ℂ B) * (α (-1) * EminusOpC c (n - m))
            = α (-1) * ((HeisenbergN.mulXN m 0) * EminusOpC c (n - m)) from by
          rw [← mul_assoc, hcomm m, mul_assoc]]
      abel
    -- expand the LHS via the recursion (only the LHS)
    conv_lhs => rw [EminusOpC_succ_op c n]
    set R₀ := ∑ m ∈ Finset.range (n + 1),
      (HeisenbergN.mulXN m (0 : Fin 1) : End ℂ B) * EminusOpC c (n - m) with hR₀
    -- c·R₀ = (n+1)·E⁻_{n+1}
    have hcR : c • R₀ = ((n : ℂ) + 1) • EminusOpC c (n + 1) := by
      rw [EminusOpC_succ_op c n, ← hR₀, smul_smul, mul_inv_cancel₀ hn1, one_smul]
    -- the bracket of R₀ telescopes (combinePQ) with the defect
    have hBrR : L * R₀ - R₀ * L
        = ((n : ℂ) + 1) • (∑ i ∈ Finset.range (n + 2),
            (HeisenbergN.mulXN i (0 : Fin 1) : End ℂ B) * EminusOpC c ((n + 1) - i))
          - c • (α (-1) * R₀) := by
      rw [hR₀, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
        Finset.sum_congr rfl pt, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        combinePQ n (fun i => (HeisenbergN.mulXN i (0 : Fin 1) : End ℂ B) * EminusOpC c ((n + 1) - i))]
      congr 1
      rw [Finset.mul_sum, Finset.smul_sum]
    -- pull scalars out of the bracket, then substitute the telescoped bracket
    rw [show L * (((n : ℂ) + 1)⁻¹ • c • R₀) - (((n : ℂ) + 1)⁻¹ • c • R₀) * L
          = ((n : ℂ) + 1)⁻¹ • c • (L * R₀ - R₀ * L) from by
        rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
          show ((n : ℂ) + 1)⁻¹ • c • (L * R₀) - ((n : ℂ) + 1)⁻¹ • c • (R₀ * L)
              = ((n : ℂ) + 1)⁻¹ • (c • (L * R₀) - c • (R₀ * L)) from (smul_sub _ _ _).symm,
          show c • (L * R₀) - c • (R₀ * L) = c • (L * R₀ - R₀ * L) from (smul_sub _ _ _).symm],
      hBrR]
    set Rp := ∑ i ∈ Finset.range (n + 2),
      (HeisenbergN.mulXN i (0 : Fin 1) : End ℂ B) * EminusOpC c ((n + 1) - i) with hRp
    have hcR' : c • Rp = (((n + 1 : ℕ) : ℂ) + 1) • EminusOpC c (n + 1 + 1) := by
      rw [hRp, EminusOpC_succ_op c (n + 1), ← hRp, smul_smul,
        mul_inv_cancel₀ (Nat.cast_add_one_ne_zero (n + 1)), one_smul]
    rw [show c • (((n : ℂ) + 1) • Rp - c • (α (-1) * R₀))
          = c • (((n : ℂ) + 1) • Rp) - c • (c • (α (-1) * R₀)) from smul_sub _ _ _,
      smul_comm c ((n : ℂ) + 1) Rp, hcR',
      show c • (c • (α (-1) * R₀)) = ((n : ℂ) + 1) • (c • (α (-1) * EminusOpC c (n + 1))) from by
        rw [← mul_smul_comm, hcR, mul_smul_comm, smul_comm],
      show ((n : ℂ) + 1) • ((((n + 1 : ℕ) : ℂ) + 1) • EminusOpC c (n + 1 + 1))
            - ((n : ℂ) + 1) • (c • (α (-1) * EminusOpC c (n + 1)))
          = ((n : ℂ) + 1) • ((((n + 1 : ℕ) : ℂ) + 1) • EminusOpC c (n + 1 + 1)
            - c • (α (-1) * EminusOpC c (n + 1))) from (smul_sub _ _ _).symm,
      smul_smul, inv_mul_cancel₀ hn1, one_smul]


/-! ## EEC `α₋₁`-defect L₋₁-covariance (combining E⁺ and E⁻) -/

/-- E⁺ is L₋₁-covariant (ℤ-indexed): `[L₋₁, EplusC c t] = (t+1)·EplusC c (t+1)`. -/
theorem LvirN_comm_EplusC (c : ℂ) (t : ℤ) :
    HeisenbergN.LvirN 1 2 (-1) * EplusC c t - EplusC c t * HeisenbergN.LvirN 1 2 (-1)
      = ((t + 1 : ℤ)) • EplusC c (t + 1) := by
  rw [EplusC_eq_aExpCZ, EplusC_eq_aExpCZ, show -(t + 1) = -t - 1 from by ring,
    LvirN_comm_aExpCZ c (-t),
    show (1 : ℂ) - ((-t : ℤ) : ℂ) = (((t + 1 : ℤ)) : ℂ) from by push_cast; ring]
  exact Int.cast_smul_eq_zsmul ℂ (t + 1) (aExpCZ c (-t - 1))

/-- E⁻ is L₋₁-covariant with the `α₋₁` defect (ℤ-indexed):
`[L₋₁, EminusC c t] = (t+1)·EminusC c (t+1) − c·α₋₁·EminusC c t`. -/
theorem LvirN_comm_EminusC (c : ℂ) (t : ℤ) :
    HeisenbergN.LvirN 1 2 (-1) * EminusC c t - EminusC c t * HeisenbergN.LvirN 1 2 (-1)
      = ((t + 1 : ℤ)) • EminusC c (t + 1) - c • (α (-1) * EminusC c t) := by
  by_cases ht : 0 ≤ t
  · have key : ((t.toNat : ℕ) : ℂ) = (t : ℂ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg ht]
    rw [show EminusC c t = EminusOpC c t.toNat from EminusC_nonneg c ht,
      show EminusC c (t + 1) = EminusOpC c (t.toNat + 1) from by
        rw [EminusC_nonneg c (by omega), show (t + 1).toNat = t.toNat + 1 from by omega],
      LvirN_comm_EminusOpC c t.toNat]
    congr 1
    rw [show ((t.toNat : ℂ) + 1) = (((t + 1 : ℤ)) : ℂ) from by rw [key]; push_cast; ring]
    exact Int.cast_smul_eq_zsmul ℂ (t + 1) (EminusOpC c (t.toNat + 1))
  · rw [EminusC_neg c (by omega : t < 0), mul_zero, zero_mul, sub_self, mul_zero, smul_zero,
      sub_zero]
    rcases lt_or_eq_of_le (show t + 1 ≤ 0 by omega) with h | h
    · rw [EminusC_neg c h]; exact (smul_zero _).symm
    · rw [h, zero_smul]

/-- **The boson dressing `EEC` is `L₋₁`-covariant with the `α₋₁` defect**:
`[L₋₁, EEC c r] = (r+1)·EEC c (r+1) − c·α₋₁·EEC c r`. Leibniz on `nprod(E⁻,E⁺)`: the clean parts
telescope to `(r+1)·EEC c (r+1)` (as in `DCovariant.nprod`), the E⁻ defect sums to the `α₋₁` term. -/
theorem LvirN_comm_EEC (c : ℂ) (r : ℤ) :
    HeisenbergN.LvirN 1 2 (-1) * EEC c r - EEC c r * HeisenbergN.LvirN 1 2 (-1)
      = ((r + 1 : ℤ)) • EEC c (r + 1) - c • (α (-1) * EEC c r) := by
  set L : Module.End ℂ B := HeisenbergN.LvirN 1 2 (-1) with hL
  have ha := EminusC_isField c
  have hb := EplusC_isField c
  -- per-term Leibniz bracket (with the E⁻ `α₋₁` defect)
  have NO_term_EEC : ∀ k : ℤ,
      L * normalOrdered (EminusC c) (EplusC c) k (r - k)
        - normalOrdered (EminusC c) (EplusC c) k (r - k) * L
      = normalOrdered (VOA.deriv (EminusC c)) (EplusC c) k (r - k)
        + normalOrdered (EminusC c) (VOA.deriv (EplusC c)) k (r - k)
        - c • (α (-1) * normalOrdered (EminusC c) (EplusC c) k (r - k)) := by
    intro k
    by_cases hk : 0 ≤ k
    · simp only [normalOrdered_apply, if_pos hk, deriv_apply]
      rw [show L * (EminusC c k * EplusC c (r - k)) - EminusC c k * EplusC c (r - k) * L
            = (L * EminusC c k - EminusC c k * L) * EplusC c (r - k)
              + EminusC c k * (L * EplusC c (r - k) - EplusC c (r - k) * L) from by
            simp only [sub_mul, mul_sub, mul_assoc]; abel,
        LvirN_comm_EminusC, LvirN_comm_EplusC]
      simp only [sub_mul, smul_mul_assoc, mul_smul_comm]
      rw [show (α (-1) * EminusC c k) * EplusC c (r - k)
          = α (-1) * (EminusC c k * EplusC c (r - k)) from mul_assoc _ _ _]
      abel
    · simp only [normalOrdered_apply, if_neg hk]
      have hEm0 : EminusC c k = 0 := EminusC_neg c (by omega)
      have hdEm0 : VOA.deriv (EminusC c) k = 0 := by
        rw [deriv_apply]
        rcases lt_or_eq_of_le (show k + 1 ≤ 0 by omega) with h | h
        · rw [EminusC_neg c h]; exact smul_zero _
        · rw [h, zero_smul]
      rw [hEm0, hdEm0]; simp
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, EEC, nprod_apply,
    map_finsum L (normalOrdered_diag_support_finite ha hb r x), nprod_apply]
  have hfinDL : (Function.support
      (fun k : ℤ => L (normalOrdered (EminusC c) (EplusC c) k (r - k) x))).Finite := by
    apply Set.Finite.subset (normalOrdered_diag_support_finite ha hb r x)
    intro k hk
    rw [Function.mem_support] at hk ⊢
    exact fun hz => hk (by rw [hz, map_zero])
  have hcleanFin : (Function.support (fun k : ℤ =>
      normalOrdered (VOA.deriv (EminusC c)) (EplusC c) k (r - k) x
        + normalOrdered (EminusC c) (VOA.deriv (EplusC c)) k (r - k) x)).Finite := by
    apply Set.Finite.subset ((normalOrdered_diag_support_finite ha.deriv hb r x).union
      (normalOrdered_diag_support_finite ha hb.deriv r x))
    intro k hk
    rw [Function.mem_support] at hk
    simp only [Set.mem_union, Function.mem_support]
    by_contra hcon
    push_neg at hcon
    exact hk (by rw [hcon.1, hcon.2, add_zero])
  have hdefectFin : (Function.support (fun k : ℤ =>
      c • α (-1) (normalOrdered (EminusC c) (EplusC c) k (r - k) x))).Finite := by
    apply Set.Finite.subset (normalOrdered_diag_support_finite ha hb r x)
    intro k hk
    rw [Function.mem_support] at hk ⊢
    exact fun hz => hk (by rw [hz, map_zero, smul_zero])
  -- clean part = ((r+1)•EEC c (r+1)) x
  have hclean : (∑ᶠ k : ℤ, (normalOrdered (VOA.deriv (EminusC c)) (EplusC c) k (r - k) x
        + normalOrdered (EminusC c) (VOA.deriv (EplusC c)) k (r - k) x))
      = ((r + 1 : ℤ) • EEC c (r + 1)) x := by
    rw [finsum_add_distrib (normalOrdered_diag_support_finite ha.deriv hb r x)
        (normalOrdered_diag_support_finite ha hb.deriv r x),
      show (∑ᶠ k : ℤ, normalOrdered (VOA.deriv (EminusC c)) (EplusC c) k (r - k) x)
          = VOA.nprod ha.deriv hb r x from (nprod_apply ha.deriv hb r x).symm,
      show (∑ᶠ k : ℤ, normalOrdered (EminusC c) (VOA.deriv (EplusC c)) k (r - k) x)
          = VOA.nprod ha hb.deriv r x from (nprod_apply ha hb.deriv r x).symm]
    have hadd : (VOA.nprod ha.deriv hb r) x + (VOA.nprod ha hb.deriv r) x
        = (VOA.deriv (VOA.nprod ha hb)) r x := by rw [deriv_nprod]; rfl
    rw [hadd, deriv_apply]; rfl
  -- defect part = (c•(α(-1)*EEC c r)) x
  have hdefect : (∑ᶠ k : ℤ, c • α (-1) (normalOrdered (EminusC c) (EplusC c) k (r - k) x))
      = (c • (α (-1) * EEC c r)) x := by
    rw [LinearMap.smul_apply, Module.End.mul_apply, EEC, nprod_apply,
      map_finsum (α (-1)) (normalOrdered_diag_support_finite ha hb r x),
      smul_finsum' c ((normalOrdered_diag_support_finite ha hb r x).subset
        (fun k hk => by rw [Function.mem_support] at hk ⊢; exact fun hz => hk (by rw [hz, map_zero])))]
  rw [← finsum_sub_distrib hfinDL (normalOrdered_diag_support_finite ha hb r (L x)),
    finsum_congr (fun k => by
      have := congrArg (fun (T : End ℂ B) => T x) (NO_term_EEC k)
      simpa only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
        LinearMap.smul_apply] using this),
    finsum_sub_distrib hcleanFin hdefectFin, hclean, hdefect]
  exact (LinearMap.sub_apply _ _ x).symm

/-- The action of `Trec` on a basis state `q ⊗ e^{kα}`. -/
theorem Trec_tmul (q : B) (k : ℤ) :
    Trec (q ⊗ₜ[ℂ] eVec k) = (HeisenbergN.LvirN 1 2 (-1) q) ⊗ₜ[ℂ] eVec k
      + ((k : ℤ) : ℂ) • ((α (-1) q) ⊗ₜ[ℂ] eVec k) := by
  rw [Trec, LinearMap.add_apply, LinearMap.rTensor_tmul, momOp, LinearMap.smul_apply,
    Module.End.mul_apply, zGradeOp, LinearMap.lTensor_tmul, zGradeL_eVec, TensorProduct.tmul_smul,
    map_smul, LinearMap.rTensor_tmul, smul_smul]
  congr 2
  push_cast; ring

/-- **Operator-level boson identity** behind the charged covariance: combines the EEC `L₋₁`
covariance (with `α₋₁` defect) and the momentum charge-shift `(*)`, closed by `module`. -/
theorem Trec_Yemα_bosonOp (m s n : ℤ) :
    HeisenbergN.LvirN 1 2 (-1) * EEC (m : ℂ) (s - 2 * m * n)
        - EEC (m : ℂ) (s - 2 * m * n) * HeisenbergN.LvirN 1 2 (-1)
        + ((n + m : ℤ) : ℂ) • (α (-1) * EEC (m : ℂ) (s - 2 * m * n))
        - ((n : ℤ) : ℂ) • (EEC (m : ℂ) (s - 2 * m * n) * α (-1))
      = ((s + 1 : ℤ) : ℂ) • EEC (m : ℂ) (s + 1 - 2 * m * n) := by
  rw [show s + 1 - 2 * m * n = s - 2 * m * n + 1 from by ring]
  have hL := LvirN_comm_EEC (m : ℂ) (s - 2 * m * n)
  have hα := alphaNeg1_comm_EEC (m : ℂ) (s - 2 * m * n)
  rw [← Int.cast_smul_eq_zsmul ℂ (s - 2 * m * n + 1)] at hL
  have hEZ : EEC (m : ℂ) (s - 2 * m * n) * α (-1)
      = α (-1) * EEC (m : ℂ) (s - 2 * m * n) - (2 * (m : ℂ)) • EEC (m : ℂ) (s - 2 * m * n + 1) := by
    rw [← hα]; abel
  have hLZ : HeisenbergN.LvirN 1 2 (-1) * EEC (m : ℂ) (s - 2 * m * n)
      = EEC (m : ℂ) (s - 2 * m * n) * HeisenbergN.LvirN 1 2 (-1)
        + (((s - 2 * m * n + 1 : ℤ) : ℂ) • EEC (m : ℂ) (s - 2 * m * n + 1)
          - (m : ℂ) • (α (-1) * EEC (m : ℂ) (s - 2 * m * n))) := by
    rw [← hL]; abel
  rw [hLZ, hEZ]
  push_cast
  module

/-- The charged-generator covariance on a basis state `p ⊗ e^{nα}` (the `(✦)` computation):
the boson factor is `Trec_Yemα_bosonOp` applied to `p`, tensored with `e^{(n+m)α}`. -/
theorem Trec_Yemα_on_state (m s n : ℤ) (p : B) :
    (Trec * Yemα m s - Yemα m s * Trec) (p ⊗ₜ[ℂ] eVec n)
      = ((s + 1 : ℤ)) • Yemα m (s + 1) (p ⊗ₜ[ℂ] eVec n) := by
  have hp := congrArg (fun T : End ℂ B => T p) (Trec_Yemα_bosonOp m s n)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply] at hp
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Yemα_tmul, Trec_tmul,
    Trec_tmul, map_add, map_smul, Yemα_tmul, Yemα_tmul, Yemα_tmul]
  simp only [TensorProduct.smul_tmul', ← TensorProduct.add_tmul, ← TensorProduct.sub_tmul]
  congr 1
  rw [show HeisenbergN.LvirN 1 2 (-1) (EEC (m : ℂ) (s - 2 * m * n) p)
        + ((n + m : ℤ) : ℂ) • α (-1) (EEC (m : ℂ) (s - 2 * m * n) p)
        - (EEC (m : ℂ) (s - 2 * m * n) (HeisenbergN.LvirN 1 2 (-1) p)
          + ((n : ℤ) : ℂ) • EEC (m : ℂ) (s - 2 * m * n) (α (-1) p))
      = ((s + 1 : ℤ) : ℂ) • EEC (m : ℂ) (s + 1 - 2 * m * n) p from by rw [← hp]; abel,
    Int.cast_smul_eq_zsmul]

/-- **The charged generator `Yemα m` is `Trec`-covariant**: `DCovariant Trec (Yemα m)`. This is the
`STAGE 1` crux for the lattice-VOA reconstruction (charged analogue of `Trec_alphaLat_DCovariant`). -/
theorem Trec_Yemα_DCovariant (m : ℤ) : Reconstruction.DCovariant Trec (Yemα m) := by
  intro s
  refine LinearMap.ext fun y => ?_
  change (Trec * Yemα m s - Yemα m s * Trec) y = ((s + 1 : ℤ)) • Yemα m (s + 1) y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y1 y2 h1 h2 =>
      rw [map_add (Trec * Yemα m s - Yemα m s * Trec) y1 y2, h1, h2,
        map_add (Yemα m (s + 1)) y1 y2]
      exact (smul_add _ _ _).symm
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; simp
      | add g1 g2 h1 h2 =>
          erw [TensorProduct.tmul_add]
          simp only [map_add, h1, h2]
          exact (smul_add _ _ _).symm
      | single k a =>
          rw [(Finsupp.smul_single_one k a).symm,
            show (Finsupp.single k 1 : LatGrp) = eVec k from rfl]
          erw [TensorProduct.tmul_smul, map_smul, map_smul, Trec_Yemα_on_state]
          rw [← Int.cast_smul_eq_zsmul ℂ (s + 1) (Yemα m (s + 1) (p ⊗ₜ[ℂ] eVec k)),
            ← Int.cast_smul_eq_zsmul ℂ (s + 1) (a • Yemα m (s + 1) (p ⊗ₜ[ℂ] eVec k)), smul_comm]

end VOA.LatExp
