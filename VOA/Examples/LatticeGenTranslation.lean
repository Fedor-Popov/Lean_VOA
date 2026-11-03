/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenBosonCharge
import VOA.Examples.HeisenbergNVOA
import VOA.Core.ReconstructionExistence

/-!
# The lattice translation operator `TrecGen` and the boson generator covariance

`TrecGen = rTensor(L₋₁^Heis) + momGen`, where `momGen = ∑_a rTensor(α^a₋₁)·α^a₀` is the momentum
coupling from the lattice zero mode.  For the orthonormal level-`1` frame the Sugawara `½∑:α^aα^a:`
gives the `α^a₋₁α^a₀` cross term with coefficient `1` (A₁'s `½` came from its level-`2` normalization).

This file proves `TrecGen_vacuum` and the **boson generator covariance**
`TrecGen_alphaLatGen_DCovariant`, lifted from `currentN_DCovariant` plus the `s=-2` momentum bracket.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-- Scaling a commutator: `[c•M, X] = c•[M, X]`. -/
theorem smul_bracketGen (c : ℂ) (M X : End ℂ (LatModuleGen L)) :
    (c • M) * X - X * (c • M) = c • (M * X - X * M) := by
  rw [smul_mul_assoc, mul_smul_comm]; exact (smul_sub c (M * X) (X * M)).symm

/-- The **momentum coupling** `momGen = ∑_a rTensor(α^a₋₁)·α^a₀` (the `α^a₋₁α^a₀` Sugawara cross
term for the level-`1` orthonormal frame). -/
noncomputable def momGen : End ℂ (LatModuleGen L) :=
  ∑ a : Fin (rank L), (LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1))) * zGradeOpGen L a

/-- The **reconstruction translation operator** `TrecGen = rTensor(L₋₁) + momGen`. -/
noncomputable def TrecGen : End ℂ (LatModuleGen L) :=
  LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.LvirN (rank L) 1 (-1)) + momGen L

/-- `TrecGen |0⟩ = 0`. -/
theorem TrecGen_vacuum : TrecGen L (latVacuumGen L) = 0 := by
  rw [TrecGen, LinearMap.add_apply]
  have h1 : LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.LvirN (rank L) 1 (-1))
      (latVacuumGen L) = 0 := by
    rw [latVacuumGen, latStateGen, LinearMap.rTensor_tmul,
      HeisenbergN.LvirN_vacuum (rank L) 1 (by norm_num : (-1 : ℤ) ≤ -1), TensorProduct.zero_tmul]
  have h2 : momGen L (latVacuumGen L) = 0 := by
    rw [momGen, LinearMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Module.End.mul_apply, zGradeOpGen_vacuum, map_zero]
  rw [h1, h2, add_zero]

/-- Per-direction boson commutator: `[rTensor(α^a₋₁), rTensor(α^c(s))] = (a=c ∧ s=-2 ? -1 : 0)•1`. -/
theorem rTensor_osc_comm_gen (a c : Fin (rank L)) (s : ℤ) :
    (LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)))
        * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
      - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
        * (LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)))
      = (if a = c ∧ s = -2 then (-1 : ℂ) else 0) • (1 : End ℂ (LatModuleGen L)) := by
  rw [currentN_apply, ← rTensorGen_mul, ← rTensorGen_mul, ← LinearMap.rTensor_sub,
    show oscN (rank L) 1 a (-1) * oscN (rank L) 1 c (-s - 1)
          - oscN (rank L) 1 c (-s - 1) * oscN (rank L) 1 a (-1)
        = (if a = c ∧ s = -2 then (-1 : ℂ) else 0) • LinearMap.id from by
      rw [oscN_comm]
      by_cases hac : a = c ∧ s = -2
      · rw [if_pos ⟨hac.1, by omega⟩, if_pos hac]; norm_num
      · rw [if_neg (fun h => hac ⟨h.1, by omega⟩), if_neg hac],
    LinearMap.rTensor_smul, LinearMap.rTensor_id]
  rfl

/-- The momentum bracket `[momGen, rTensor(α^c(s))] = (s=-2 ? -1 : 0)•α^c₀`. -/
theorem momGen_comm_rTensor (c : Fin (rank L)) (s : ℤ) :
    momGen L * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
      - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)) * momGen L
      = (if s = -2 then (-1 : ℂ) else 0) • zGradeOpGen L c := by
  have hterm : ∀ a : Fin (rank L),
      (LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)) * zGradeOpGen L a)
          * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)
        - LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)
          * (LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)) * zGradeOpGen L a)
      = (if a = c ∧ s = -2 then (-1 : ℂ) else 0) • zGradeOpGen L a := by
    intro a
    set A := LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)) with hA
    set B := LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s) with hB
    set Z := zGradeOpGen L a with hZ
    have hZB : Z * B = B * Z := zGradeOpGen_comm_rTensor L a (currentN (rank L) 1 c s)
    have hAB := rTensor_osc_comm_gen L a c s
    rw [← hA, ← hB] at hAB
    have e1 : (A * Z) * B - B * (A * Z) = (A * B - B * A) * Z := by
      rw [mul_assoc, hZB, ← mul_assoc, ← mul_assoc]
      exact (sub_mul (A * B) (B * A) Z).symm
    rw [e1, hAB, smul_mul_assoc, one_mul]
  rw [momGen, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun a _ => hterm a),
    show (∑ a : Fin (rank L), (if a = c ∧ s = -2 then (-1 : ℂ) else 0) • zGradeOpGen L a)
        = ∑ a : Fin (rank L),
            (if a = c then (if s = -2 then (-1 : ℂ) else 0) • zGradeOpGen L a else 0) from
      Finset.sum_congr rfl fun a _ => by
        by_cases hac : a = c
        · by_cases hs : s = -2
          · rw [if_pos ⟨hac, hs⟩, if_pos hac, if_pos hs]
          · rw [if_neg (fun h => hs h.2), if_pos hac, if_neg hs, zero_smul]
        · rw [if_neg (fun h => hac h.1), if_neg hac, zero_smul],
    Finset.sum_ite_eq' Finset.univ c, if_pos (Finset.mem_univ c)]

/-- `[momGen, α^c₀] = 0` (the momenta all commute; the boson halves commute with the charge factor). -/
theorem momGen_comm_zG (c : Fin (rank L)) :
    momGen L * zGradeOpGen L c - zGradeOpGen L c * momGen L = 0 := by
  rw [momGen, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  set A := LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)) with hA
  have hAc : A * zGradeOpGen L c = zGradeOpGen L c * A :=
    (zGradeOpGen_comm_rTensor L c (oscN (rank L) 1 a (-1))).symm
  have hac : zGradeOpGen L a * zGradeOpGen L c = zGradeOpGen L c * zGradeOpGen L a :=
    zGradeOpGen_comm L a c
  rw [mul_assoc, hac, ← mul_assoc, hAc, mul_assoc, sub_self]

/-- **The boson generator covariance** `DCovariant TrecGen (α^c(z))`
(`[L₋₁, α^c(s)] = (s+1)•α^c(s+1)`): boson half from `currentN_DCovariant`, momentum from the
`s=-2` bracket. -/
theorem TrecGen_alphaLatGen_DCovariant (c : Fin (rank L)) :
    Reconstruction.DCovariant (TrecGen L) (alphaLatGen L c) := by
  intro s
  change TrecGen L * alphaLatGen L c s - alphaLatGen L c s * TrecGen L
    = ((s + 1 : ℤ)) • alphaLatGen L c (s + 1)
  set Lv := LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.LvirN (rank L) 1 (-1)) with hLdef
  have hL : Lv * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
      - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)) * Lv
      = ((s + 1 : ℤ)) • LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c (s + 1)) := by
    have hc := HeisenbergN.currentN_DCovariant (rank L) 1 (by norm_num : (1 : ℂ) ≠ 0) c s
    rw [hLdef, ← rTensorGen_mul, ← rTensorGen_mul, ← LinearMap.rTensor_sub,
      show HeisenbergN.LvirN (rank L) 1 (-1) * currentN (rank L) 1 c s
            - currentN (rank L) 1 c s * HeisenbergN.LvirN (rank L) 1 (-1)
          = ((s + 1 : ℤ)) • currentN (rank L) 1 c (s + 1) from hc,
      ← Int.cast_smul_eq_zsmul ℂ (s + 1) (currentN (rank L) 1 c (s + 1)), LinearMap.rTensor_smul]
    exact Int.cast_smul_eq_zsmul ℂ (s + 1)
      (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c (s + 1)))
  have hLc : Lv * (if s = -1 then zGradeOpGen L c else 0)
      - (if s = -1 then zGradeOpGen L c else 0) * Lv = 0 := by
    by_cases hs : s = -1
    · rw [if_pos hs, hLdef]
      exact sub_eq_zero_of_eq (zGradeOpGen_comm_rTensor L c (HeisenbergN.LvirN (rank L) 1 (-1))).symm
    · rw [if_neg hs, mul_zero, zero_mul, sub_zero]
  have hMc : momGen L * (if s = -1 then zGradeOpGen L c else 0)
      - (if s = -1 then zGradeOpGen L c else 0) * momGen L = 0 := by
    by_cases hs : s = -1
    · rw [if_pos hs]; exact momGen_comm_zG L c
    · rw [if_neg hs, mul_zero, zero_mul, sub_zero]
  have hM := momGen_comm_rTensor L c s
  have key : TrecGen L * alphaLatGen L c s - alphaLatGen L c s * TrecGen L
      = ((s + 1 : ℤ)) • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c (s + 1)))
        + (if s = -2 then (-1 : ℂ) else 0) • zGradeOpGen L c := by
    have expand : TrecGen L * alphaLatGen L c s - alphaLatGen L c s * TrecGen L
        = (Lv * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
            - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)) * Lv)
          + (Lv * (if s = -1 then zGradeOpGen L c else 0)
            - (if s = -1 then zGradeOpGen L c else 0) * Lv)
          + (momGen L * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
            - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)) * momGen L)
          + (momGen L * (if s = -1 then zGradeOpGen L c else 0)
            - (if s = -1 then zGradeOpGen L c else 0) * momGen L) := by
      rw [TrecGen, hLdef, alphaLatGen_apply]
      noncomm_ring
    rw [expand, hL, hLc, hM, hMc, add_zero, add_zero]
  rw [key, alphaLatGen_apply,
    show ((s + 1 : ℤ)) • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c (s + 1))
          + (if s + 1 = -1 then zGradeOpGen L c else 0))
        = ((s + 1 : ℤ)) • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c (s + 1)))
          + ((s + 1 : ℤ)) • (if s + 1 = -1 then zGradeOpGen L c else 0) from smul_add _ _ _]
  congr 1
  by_cases hs : s = -2
  · rw [if_pos hs, if_pos (by omega : s + 1 = -1), hs, show ((-2 : ℤ) + 1) = -1 from by ring]
    exact (neg_one_smul ℂ (zGradeOpGen L c)).trans (neg_one_smul ℤ (zGradeOpGen L c)).symm
  · rw [if_neg hs, if_neg (by omega : ¬ s + 1 = -1), zero_smul]
    exact (smul_zero _).symm

/-! ## §6  The charge-seed covariance `DCovariant TrecGen (Y(e^β,z))`. -/

/-- The charge current zero mode vanishes on the Fock factor: `chargeOsc β 0 = 0`. -/
theorem chargeOsc_zero (β : L.carrier) : chargeOsc L β 0 = 0 := by
  rw [chargeOsc]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [oscN_zero, smul_zero]

/-- `[L₋₁, chargeOsc β (j+1)] = -(j+1)·chargeOsc β j` (linearity of the frame sum over
`LvirN_comm_oscN`). -/
theorem LvirN_comm_chargeOsc_succ (β : L.carrier) (j : ℤ) :
    HeisenbergN.LvirN (rank L) 1 (-1) * chargeOsc L β (j + 1)
      - chargeOsc L β (j + 1) * HeisenbergN.LvirN (rank L) 1 (-1)
      = (-((j : ℤ) + 1) : ℂ) • chargeOsc L β j := by
  rw [chargeOsc, chargeOsc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
    LvirN_comm_oscN (rank L) 1 (by norm_num : (1 : ℂ) ≠ 0) b (-1) (j + 1),
    show (-1 : ℤ) + (j + 1) = j from by ring, smul_comm]
  congr 2
  push_cast; ring

/-- **The `[L₋₁, E⁺(β)]` commutator** `[L₋₁, E⁺(β)_N] = (1-N)·E⁺(β)_{N-1}` — the single hardest
proof of the reconstruction.  Strong induction on `N.toNat` via the `aExpVecZ` Newton recursion
(Leibniz `hderiv` + per-term `pt` from `LvirN_comm_chargeOsc_succ` and the IH + Newton reindex).
Cross-charge lift of A₁'s `LvirN_comm_aExpCZ` (SIMPLER: no separate charge scalar). -/
theorem LvirN_comm_aExpVecZ (β : L.carrier) :
    ∀ N : ℤ, HeisenbergN.LvirN (rank L) 1 (-1) * aExpVecZ L β N
        - aExpVecZ L β N * HeisenbergN.LvirN (rank L) 1 (-1)
      = (1 - (N : ℂ)) • aExpVecZ L β (N - 1) := by
  set Lv : End ℂ (FockN (rank L)) := HeisenbergN.LvirN (rank L) 1 (-1) with hLv
  have hderiv : ∀ X Y : End ℂ (FockN (rank L)), Lv * (X * Y) - (X * Y) * Lv
      = (Lv * X - X * Lv) * Y + X * (Lv * Y - Y * Lv) := by
    intro X Y; simp only [sub_mul, mul_sub, mul_assoc]; abel
  suffices H : ∀ n : ℕ, ∀ N : ℤ, N.toNat ≤ n →
      Lv * aExpVecZ L β N - aExpVecZ L β N * Lv = (1 - (N : ℂ)) • aExpVecZ L β (N - 1) by
    exact fun N => H N.toNat N le_rfl
  intro n
  induction n with
  | zero =>
    intro N hN
    by_cases h0 : N = 0
    · subst h0
      rw [aExpVecZ_zero, aExpVecZ_neg L β (show (0 : ℤ) - 1 < 0 by omega), ← Module.End.one_eq_id,
        mul_one, one_mul, sub_self]
      exact (smul_zero _).symm
    · rw [aExpVecZ_neg L β (by omega : N < 0), aExpVecZ_neg L β (show N - 1 < 0 by omega),
        mul_zero, zero_mul, sub_self]
      exact (smul_zero _).symm
  | succ n ih =>
    intro N hM
    by_cases hsmall : N.toNat ≤ n
    · exact ih N hsmall
    · have hN1 : 1 ≤ N := by omega
      have hNne : (N : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      have hNtoNat : N.toNat = (N - 1).toNat + 1 := by omega
      have pt : ∀ j : ℕ,
          Lv * ((-(chargeOsc L β ((j : ℤ) + 1))) * aExpVecZ L β (N - 1 - j))
            - ((-(chargeOsc L β ((j : ℤ) + 1))) * aExpVecZ L β (N - 1 - j)) * Lv
          = ((j : ℂ) + 1) • (chargeOsc L β (j : ℤ) * aExpVecZ L β (N - 1 - j))
            + ((j : ℂ) + 2 - (N : ℂ)) • ((-(chargeOsc L β ((j : ℤ) + 1))) * aExpVecZ L β (N - 2 - j)) := by
        intro j
        rw [hderiv]
        have hfst : Lv * (-(chargeOsc L β ((j : ℤ) + 1))) - (-(chargeOsc L β ((j : ℤ) + 1))) * Lv
            = ((j : ℂ) + 1) • chargeOsc L β (j : ℤ) := by
          have h := LvirN_comm_chargeOsc_succ L β (j : ℤ)
          rw [← hLv] at h
          rw [show (-(chargeOsc L β ((j : ℤ) + 1))) = ((-1 : ℂ)) • chargeOsc L β ((j : ℤ) + 1) from
              (neg_one_smul ℂ _).symm, mul_smul_comm, smul_mul_assoc,
            show ((-1 : ℂ)) • (Lv * chargeOsc L β ((j : ℤ) + 1))
                  - ((-1 : ℂ)) • (chargeOsc L β ((j : ℤ) + 1) * Lv)
                = ((-1 : ℂ)) • (Lv * chargeOsc L β ((j : ℤ) + 1)
                    - chargeOsc L β ((j : ℤ) + 1) * Lv) from (smul_sub _ _ _).symm,
            h, smul_smul]
          congr 1; push_cast; ring
        have hsnd : Lv * aExpVecZ L β (N - 1 - j) - aExpVecZ L β (N - 1 - j) * Lv
            = ((j : ℂ) + 2 - (N : ℂ)) • aExpVecZ L β (N - 2 - j) := by
          have hih := ih (N - 1 - j) (by omega)
          rw [show (N - 1 - (j : ℤ)) - 1 = N - 2 - j from by ring] at hih
          rw [hih]; congr 1; push_cast; ring
        rw [hfst, hsnd, smul_mul_assoc, mul_smul_comm]
      set R := ∑ j ∈ Finset.range N.toNat, (-(chargeOsc L β ((j : ℤ) + 1))) * aExpVecZ L β (N - 1 - j)
        with hRdef
      have hrecR : aExpVecZ L β N = (N : ℂ)⁻¹ • R := by
        rw [aExpVecZ_recursion L β N hN1, hRdef]; simp only [Module.End.mul_eq_comp]
      have hSA : (∑ j ∈ Finset.range N.toNat,
              ((j : ℂ) + 1) • (chargeOsc L β (j : ℤ) * aExpVecZ L β (N - 1 - j)))
          = ∑ i ∈ Finset.range (N - 1).toNat,
              ((i : ℂ) + 2) • (chargeOsc L β ((i : ℤ) + 1) * aExpVecZ L β (N - 2 - i)) := by
        rw [hNtoNat, Finset.sum_range_succ']
        rw [show (chargeOsc L β ((0 : ℕ) : ℤ) * aExpVecZ L β (N - 1 - ((0 : ℕ) : ℤ))) = 0 from by
          rw [show ((0 : ℕ) : ℤ) = 0 from rfl, chargeOsc_zero, zero_mul], smul_zero, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 from by push_cast; ring,
          show N - 1 - ((i : ℤ) + 1) = N - 2 - i from by ring]
        congr 1; push_cast; ring
      have hSB : (∑ j ∈ Finset.range N.toNat,
              ((j : ℂ) + 2 - (N : ℂ)) • ((-(chargeOsc L β ((j : ℤ) + 1))) * aExpVecZ L β (N - 2 - j)))
          = ∑ i ∈ Finset.range (N - 1).toNat,
              ((i : ℂ) + 2 - (N : ℂ)) • ((-(chargeOsc L β ((i : ℤ) + 1))) * aExpVecZ L β (N - 2 - i)) := by
        rw [hNtoNat, Finset.sum_range_succ]
        rw [show aExpVecZ L β (N - 2 - ((N - 1).toNat : ℤ)) = 0 from by
          rw [show ((N - 1).toNat : ℤ) = N - 1 from by omega]
          exact aExpVecZ_neg L β (by omega), mul_zero, smul_zero, add_zero]
      have hBrR : Lv * R - R * Lv
          = (N : ℂ) • ∑ i ∈ Finset.range (N - 1).toNat,
              chargeOsc L β ((i : ℤ) + 1) * aExpVecZ L β (N - 2 - i) := by
        rw [hRdef, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
          Finset.sum_congr rfl (fun j _ => pt j), Finset.sum_add_distrib, hSA, hSB,
          ← Finset.sum_add_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (-(chargeOsc L β ((i : ℤ) + 1))) * aExpVecZ L β (N - 2 - i)
            = ((-1 : ℂ)) • (chargeOsc L β ((i : ℤ) + 1) * aExpVecZ L β (N - 2 - i)) from by
              rw [show (-(chargeOsc L β ((i : ℤ) + 1))) = ((-1 : ℂ)) • chargeOsc L β ((i : ℤ) + 1) from
                  (neg_one_smul ℂ _).symm, smul_mul_assoc],
          smul_smul, ← add_smul]
        congr 1; ring
      have hfinal : (∑ i ∈ Finset.range (N - 1).toNat,
              chargeOsc L β ((i : ℤ) + 1) * aExpVecZ L β (N - 2 - i))
          = (1 - (N : ℂ)) • aExpVecZ L β (N - 1) := by
        have hreass := aExpVecZ_sum_reassembly L β (N - 1) (N - 1).toNat le_rfl
        simp only [← Module.End.mul_eq_comp] at hreass
        rw [show (N - 1) - 1 = N - 2 from by ring] at hreass
        rw [show (∑ i ∈ Finset.range (N - 1).toNat,
                chargeOsc L β ((i : ℤ) + 1) * aExpVecZ L β (N - 2 - i))
            = -(∑ i ∈ Finset.range (N - 1).toNat,
                (-(chargeOsc L β ((i : ℤ) + 1))) * aExpVecZ L β (N - 2 - i)) from by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => by
            rw [show (-(chargeOsc L β ((i : ℤ) + 1))) * aExpVecZ L β (N - 2 - i)
                = ((-1 : ℂ)) • (chargeOsc L β ((i : ℤ) + 1) * aExpVecZ L β (N - 2 - i)) from by
                  rw [show (-(chargeOsc L β ((i : ℤ) + 1))) = ((-1 : ℂ)) • chargeOsc L β ((i : ℤ) + 1) from
                      (neg_one_smul ℂ _).symm, smul_mul_assoc],
              neg_one_smul, neg_neg]]
        rw [hreass, ← neg_smul]
        congr 1; push_cast; ring
      rw [hrecR, show Lv * ((N : ℂ)⁻¹ • R) - ((N : ℂ)⁻¹ • R) * Lv
          = (N : ℂ)⁻¹ • (Lv * R - R * Lv) from by
        rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]]
      rw [hBrR, smul_smul, inv_mul_cancel₀ hNne, one_smul, hfinal]

end VOA.LatGen
