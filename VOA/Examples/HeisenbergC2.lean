/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergVOA
import VOA.Modules.C2Cofinite
import VOA.Examples.HeisenbergGrading
import VOA.Examples.HeisenbergCreation

/-!
# `¬ C2Cofinite (heisenbergVOA k hk)` (free boson `M(1)`)

The rank-1 Heisenberg / free-boson VOA `M(1)` is the canonical example of a VOA that is **NOT**
`C₂`-cofinite: `A₂(M(1)) ≅ ℂ[x]` is infinite-dimensional (Zhu, Gaberdiel–Neitzke).

This file proves that fact, culminating in the main theorem
`heisenberg_not_C2Cofinite`. Along the way:

* `heis_smul_neg_two` — the `O₂`-generator on Heisenberg is `u₍₋₂₎v = (Y k u) 1 v`.
* `heis_X_succ_mem_O₂` — every higher generator `X i = a₋(i+1)𝟙 ∈ O₂` for `i ≥ 1`
  (`= (i!)⁻¹ Tⁱ(X₀)`, a translate, via `creation_pow`/`Tpow_mem_O₂`).
* `constantCoeff_smul_neg_two_eq_zero` — the **augmentation `ε = constantCoeff` kills `O₂`**
  (every `O₂`-generator `u₍₋₂₎v` has weight `≥ 1`, hence no constant term), so `O₂` lies in the
  augmentation ideal.
* `heisenberg_vacuum_notMem_O₂` — the vacuum `𝟙` is **not** in `O₂` (its augmentation is `1 ≠ 0`).
* `heisenberg_A2_nontrivial` — `A₂(M(1)) ≠ 0`.
* `osc1_mem_O₂_of_mem` / `pderiv0_mem_O₂_of_mem` — the annihilation `osc k 1 = k·∂₀ = (X₀)₍₁₎`
  preserves `O₂` (a derivation of the `₍₋₂₎`-product, via the commutator formula `mode_commutator`).
* `coeff_single0_eq_zero_of_mem_O₂` — hence the `X₀ⁿ`-coordinate functional `coeff (single 0 n)`
  kills `O₂` (read off by `∂₀ⁿ` then constant term).
* `heisenberg_A2_tower_linearIndependent` — the classes `{[X₀ⁿ]}` are `ℂ`-linearly independent.
* `heisenberg_not_C2Cofinite` — **the main theorem**: `¬ C2Cofinite (heisenbergVOA k hk)`.

All declarations are fully proved, build-clean, and free of holes or new postulates.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical
open MvPolynomial
open Module (End)

universe u

/-! ## §1  The `O₂`-generator on Heisenberg, and the higher generators are translates -/

/-- On the Heisenberg VOA, the `O₂`-generator `u₍₋₂₎v` is the `z¹`-coefficient of `Y(u,z)`
applied to `v`: `u₍₋₂₎v = (Y k u) 1 v` (`mode (Y k u) (-2) v = (Y k u) (-(-2)-1) v = (Y k u) 1 v`). -/
theorem heis_smul_neg_two (k : ℂ) (hk : k ≠ 0) (u v : Fock) :
    (heisenbergVOA k hk).smul u (-2) v = (Y k u) 1 v := by
  rw [PreVertexAlgebra.smul_def, mode_apply]
  norm_num
  rfl

/-- The Heisenberg generator `X i = a₋(i+1)𝟙` is the `(-i-1)`-product of `X₀` with the vacuum:
`X i = (X₀)₍₋ᵢ₋₁₎𝟙`. -/
theorem heis_X_eq_smul (k : ℂ) (hk : k ≠ 0) (i : ℕ) :
    (X i : Fock) = (heisenbergVOA k hk).smul (X 0 : Fock) (-(i:ℤ) - 1) vacuum := by
  rw [PreVertexAlgebra.smul_def, mode_apply]
  show (X i : Fock) = (Y k (X 0)) (-(-(i:ℤ) - 1) - 1) vacuum
  rw [show (-(-(i:ℤ) - 1) - 1) = (i:ℤ) from by ring]
  rw [show (X 0 : Fock) = (X (0:ℕ) : Fock) from rfl, ← genField_eq_Y_X]
  rw [genField_vacuum_coeff k 0 (by positivity)]
  simp

/-- The Heisenberg generator `X i = (i!)⁻¹ Tⁱ(X₀)` is the `i`-th translate of `X₀ = a₋₁𝟙`
(the creation theorem `creation_pow`). -/
theorem heis_X_eq_Tpow (k : ℂ) (hk : k ≠ 0) (i : ℕ) :
    (X i : Fock)
      = ((i.factorial : ℂ)⁻¹) • (((heisenbergVOA k hk).toPreVertexAlgebra.T ^ i) (X 0 : Fock)) := by
  rw [heis_X_eq_smul k hk i]
  exact creation_pow (heisenbergVOA k hk) (X 0) i

/-- **Every higher generator lies in `O₂`**: `X i = a₋(i+1)𝟙 ∈ O₂(M(1))` for `i ≥ 1`, since it
is a translate `(i!)⁻¹ Tⁱ(X₀)` and `Tⁱ(𝒱) ⊆ O₂` (`Tpow_mem_O₂`). -/
theorem heis_X_succ_mem_O₂ (k : ℂ) (hk : k ≠ 0) {i : ℕ} (hi : 1 ≤ i) :
    (X i : Fock) ∈ O₂ (heisenbergVOA k hk) := by
  rw [heis_X_eq_Tpow k hk i]
  exact Submodule.smul_mem _ _ (Tpow_mem_O₂ (heisenbergVOA k hk) hi (X 0))

/-! ## §2  The augmentation `ε = constantCoeff` kills `O₂` -/

/-- A positive-weight homogeneous Fock element has vanishing constant term: for `n ≥ 1` and
`p ∈ gradingZ n`, `constantCoeff p = 0` (the constant monomial `1` has weight `0 ≠ n`). -/
theorem constantCoeff_eq_zero_of_mem_gradingZ {n : ℤ} (hn : 1 ≤ n) {p : Fock}
    (hp : p ∈ gradingZ n) : MvPolynomial.constantCoeff p = 0 := by
  rw [gradingZ_of_nonneg (by omega)] at hp
  rw [mem_gradingW] at hp
  rw [MvPolynomial.constantCoeff_eq]
  by_contra hne
  have hw := hp hne
  rw [map_zero] at hw
  omega

/-- **The augmentation kills a monomial-pair `O₂`-generator**: `constantCoeff (a₍₋₂₎ b) = 0` for
monomial states `a, b`. The generator `(monomial a 1)₍₋₂₎(monomial b 1)` is weighted-homogeneous of
weight `wa + wb + 1 ≥ 1` (VA1 grading), hence has no constant term. -/
theorem constantCoeff_smul_neg_two_monomial (k : ℂ) (hk : k ≠ 0) (a b : ℕ →₀ ℕ) :
    MvPolynomial.constantCoeff
      ((heisenbergVOA k hk).smul (monomial a 1 : Fock) (-2) (monomial b 1)) = 0 := by
  set wa : ℕ := Finsupp.weight weightFn a with hwa
  set wb : ℕ := Finsupp.weight weightFn b with hwb
  have hua : (monomial a 1 : Fock) ∈ gradingW wa := by
    rw [mem_gradingW]; exact isWeightedHomogeneous_monomial _ _ _ rfl
  have hvb : (monomial b 1 : Fock) ∈ gradingW wb := by
    rw [mem_gradingW]; exact isWeightedHomogeneous_monomial _ _ _ rfl
  have hmem := (heisenbergVOA k hk).smul_mem_grading
    (show (monomial a 1 : Fock) ∈ (heisenbergVOA k hk).grading wa from
      mem_gradingZ_of_gradingW hua)
    (show (monomial b 1 : Fock) ∈ (heisenbergVOA k hk).grading wb from
      mem_gradingZ_of_gradingW hvb) (-2)
  rw [show ((wa:ℤ) + wb - (-2) - 1) = (wa:ℤ) + wb + 1 from by ring] at hmem
  have hmem' : (heisenbergVOA k hk).smul (monomial a 1 : Fock) (-2) (monomial b 1)
      ∈ gradingZ ((wa:ℤ) + wb + 1) := hmem
  refine constantCoeff_eq_zero_of_mem_gradingZ ?_ hmem'
  have h1 : (0 : ℤ) ≤ wa := Int.natCast_nonneg wa
  have h2 : (0 : ℤ) ≤ wb := Int.natCast_nonneg wb
  omega

/-- The `ℂ`-linear "evaluate the `zʲ`-coefficient on `v`" functional
`evalAt v j : FormalDist (End Fock) →ₗ[ℂ] Fock`, `f ↦ f j v`. -/
noncomputable def evalAt (v : Fock) (j : ℤ) : FormalDist (End ℂ Fock) →ₗ[ℂ] Fock where
  toFun f := f j v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evalAt_apply (v : Fock) (j : ℤ) (f : FormalDist (End ℂ Fock)) :
    evalAt v j f = f j v := rfl

/-- The augmentation of `u₍₋₂₎v`, as a `ℂ`-linear functional in `v` (for fixed `u`):
`Φ k u v = constantCoeff ((Y k u) 1 v) = lcoeff 0 ((Y k u) 1 v)`. -/
noncomputable def augSmulRight (k : ℂ) (u : Fock) : Fock →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff (R := ℂ) (σ := ℕ) 0).comp ((Y k u) 1)

@[simp] theorem augSmulRight_apply (k : ℂ) (u v : Fock) :
    augSmulRight k u v = MvPolynomial.constantCoeff ((Y k u) 1 v) := by
  rw [augSmulRight, LinearMap.comp_apply, MvPolynomial.lcoeff_apply,
    ← MvPolynomial.constantCoeff_eq]

/-- **The augmentation kills `O₂`, right slot fixed to monomials**: for a monomial state
`u = monomial a 1`, `constantCoeff (u₍₋₂₎v) = 0` for **every** `v` (extend the monomial-pair fact
by `ℂ`-linearity in `v`). -/
theorem augSmulRight_monomial_eq_zero (k : ℂ) (hk : k ≠ 0) (a : ℕ →₀ ℕ) :
    augSmulRight k (monomial a 1) = 0 := by
  -- linear-extension over `v`: check on each monomial basis vector `monomial b ·`
  refine MvPolynomial.linearMap_ext fun b => ?_
  refine LinearMap.ext fun c => ?_
  show augSmulRight k (monomial a 1) (monomial b c) = 0
  rw [show (monomial b c : Fock) = c • monomial b 1 from by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul]
  rw [augSmulRight_apply]
  -- (Y k (monomial a 1)) 1 (monomial b 1) = W.smul (monomial a 1) (-2) (monomial b 1)
  rw [show (Y k (monomial a 1)) 1 (monomial b 1)
        = (heisenbergVOA k hk).smul (monomial a 1 : Fock) (-2) (monomial b 1) from by
      rw [heis_smul_neg_two]]
  rw [constantCoeff_smul_neg_two_monomial k hk a b, smul_zero]

/-- The augmentation of `u₍₋₂₎v`, as a `ℂ`-linear functional in `u` (for fixed `v`):
`u ↦ constantCoeff ((Y k u) 1 v)`. -/
noncomputable def augSmulLeft (k : ℂ) (v : Fock) : Fock →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff (R := ℂ) (σ := ℕ) 0).comp ((evalAt v 1).comp (Y k))

@[simp] theorem augSmulLeft_apply (k : ℂ) (u v : Fock) :
    augSmulLeft k v u = MvPolynomial.constantCoeff ((Y k u) 1 v) := by
  rw [augSmulLeft, LinearMap.comp_apply, LinearMap.comp_apply, evalAt_apply,
    MvPolynomial.lcoeff_apply, ← MvPolynomial.constantCoeff_eq]

/-- **The augmentation kills `O₂`**: `constantCoeff (u₍₋₂₎v) = 0` for **all** `u, v`. By
`ℂ`-linearity in the left slot, reduce to monomial `u`; then `augSmulRight_monomial_eq_zero`. -/
theorem constantCoeff_smul_neg_two_eq_zero (k : ℂ) (hk : k ≠ 0) (u v : Fock) :
    MvPolynomial.constantCoeff ((heisenbergVOA k hk).smul u (-2) v) = 0 := by
  rw [heis_smul_neg_two]
  -- it is `augSmulLeft k v u`; show this linear functional is 0, by checking on monomials of `u`
  have hzero : augSmulLeft k v = 0 := by
    refine MvPolynomial.linearMap_ext fun a => ?_
    refine LinearMap.ext fun c => ?_
    show augSmulLeft k v (monomial a c) = 0
    rw [show (monomial a c : Fock) = c • monomial a 1 from by
          rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul]
    rw [augSmulLeft_apply]
    -- = augSmulRight k (monomial a 1) v = 0
    rw [show MvPolynomial.constantCoeff ((Y k (monomial a 1)) 1 v)
          = augSmulRight k (monomial a 1) v from (augSmulRight_apply k (monomial a 1) v).symm]
    rw [augSmulRight_monomial_eq_zero k hk a, LinearMap.zero_apply, smul_zero]
  have := congrArg (fun (f : Fock →ₗ[ℂ] ℂ) => f u) hzero
  simp only [augSmulLeft_apply, LinearMap.zero_apply] at this
  exact this

/-! ## §3a  The annihilation `osc k 1 = (X₀)₍₁₎` is a derivation that preserves `O₂` -/

/-- `Y k (X 0) = current k`, so its modes are the oscillators `mode (Y k (X 0)) j = osc k j`. -/
theorem mode_Y_X0 (k : ℂ) (j : ℤ) : mode (Y k (X 0 : Fock)) j = osc k j := by
  rw [show (X 0 : Fock) = (X (0:ℕ) : Fock) from rfl, ← genField_eq_Y_X, genField_zero, current_mode]

/-- The Heisenberg state product `(X₀)₍ⱼ₎u = osc k j u` (mode-`j` of the current on `u`). -/
theorem heis_smul_X0 (k : ℂ) (hk : k ≠ 0) (j : ℤ) (u : Fock) :
    (heisenbergVOA k hk).smul (X 0 : Fock) j u = osc k j u := by
  show mode (Y k (X 0 : Fock)) j u = osc k j u
  rw [mode_Y_X0]

/-- **`osc k 1` preserves the `O₂`-generators**: `osc k 1 (u₍₋₂₎v) ∈ O₂` for all `u, v`.
By the commutator formula `mode_commutator`, `osc k 1 (u₍₋₂₎v) = (osc k 1 u)₍₋₂₎v + u₍₋₂₎(osc k 1 v)`
(the only surviving commutator term is `j = 1`, since `(X₀)₍₀₎ = osc k 0 = 0` and the falling-factorial
`gBinom 1 j = 0` for `j ≥ 2`); both surviving products are `₍₋₂₎`-generators, hence in `O₂`. -/
theorem osc1_smul_neg_two_mem_O₂ (k : ℂ) (hk : k ≠ 0) (u v : Fock) :
    osc k 1 ((heisenbergVOA k hk).smul u (-2) v) ∈ O₂ (heisenbergVOA k hk) := by
  set W := heisenbergVOA k hk
  -- write osc k 1 = mode (Y k (X 0)) 1 and use the bracket
  have hosc1 : ∀ p : Fock, osc k 1 p = mode (W.Y (X 0)) 1 p := by
    intro p; rw [show W.Y = Y k from rfl, mode_Y_X0]
  -- bracket: mode(Y(X0))1 ∘ mode(Y u)(-2) = [.,.] + mode(Y u)(-2) ∘ mode(Y(X0))1
  obtain ⟨N, hcomm⟩ := mode_commutator W (X 0) u 1 (-2)
  -- expand: osc1 (u₍₋₂₎v) = mode(Y(X0))1 (mode(Y u)(-2) v)
  have hexp : osc k 1 (W.smul u (-2) v)
      = ⁅mode (W.Y (X 0)) 1, mode (W.Y u) (-2)⁆ v
        + mode (W.Y u) (-2) (mode (W.Y (X 0)) 1 v) := by
    rw [hosc1]
    show mode (W.Y (X 0)) 1 (mode (W.Y u) (-2) v) = _
    rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
    show mode (W.Y (X 0)) 1 (W.smul u (-2) v) = _
    rw [PreVertexAlgebra.smul_def]; ring
  rw [hexp]
  apply Submodule.add_mem
  · -- the commutator term, expanded as a finite sum, each summand ∈ O₂
    rw [hcomm, LinearMap.coe_sum, Finset.sum_apply]
    apply Submodule.sum_mem
    intro j _
    rw [LinearMap.smul_apply]
    -- term : gBinom 1 j • mode (Y (W.smul (X0) (j:ℕ) u)) (1 + (-2) - (j:ℕ)) v
    rcases Nat.lt_or_ge (j : ℕ) 2 with hj2 | hj2
    · rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with hjv | hjv
      · -- j = 0 : W.smul (X0) 0 u = osc k 0 u = 0
        rw [hjv]
        have h0 : W.smul (X 0 : Fock) ((0:ℕ):ℤ) u = 0 := by
          rw [show ((0:ℕ):ℤ) = (0:ℤ) from rfl, heis_smul_X0 k hk, osc_zero, LinearMap.zero_apply]
        rw [h0, map_zero, mode_zero, LinearMap.zero_apply, smul_zero]
        exact Submodule.zero_mem _
      · -- j = 1 : mode index = 1 + (-2) - 1 = -2, a ₍₋₂₎-generator
        rw [hjv, show (1 : ℤ) + (-2) - ((1 : ℕ) : ℤ) = -2 from by norm_num]
        rw [show mode (W.Y (W.smul (X 0 : Fock) ((1:ℕ):ℤ) u)) (-2) v
              = W.smul (W.smul (X 0 : Fock) ((1:ℕ):ℤ) u) (-2) v from
            (PreVertexAlgebra.smul_def _ _ _ _)]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)
    · -- j ≥ 2 : gBinom 1 j = 0
      have hz : gBinom 1 (j : ℕ) = 0 := by
        rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl]
        exact gBinom_natCast_eq_zero (by omega)
      rw [hz, zero_smul]
      exact Submodule.zero_mem _
  · -- u₍₋₂₎(osc k 1 v) ∈ O₂
    rw [show mode (W.Y u) (-2) (mode (W.Y (X 0)) 1 v)
          = W.smul u (-2) (osc k 1 v) from by
      rw [show mode (W.Y (X 0)) 1 v = osc k 1 v from by
            rw [show W.Y = Y k from rfl, mode_Y_X0]]
      rw [PreVertexAlgebra.smul_def]]
    exact Submodule.subset_span ⟨_, _, rfl⟩

/-! ## §3  `O₂ ⊆ ker ε`, the vacuum survives, `A₂(M(1)) ≠ 0` -/

/-- **`O₂` lies in the augmentation ideal**: `O₂(M(1)) ⊆ ker(constantCoeff)`. Every generator
`u₍₋₂₎v` has vanishing constant term, and the kernel of a linear functional is a submodule. -/
theorem O₂_le_ker_constantCoeff (k : ℂ) (hk : k ≠ 0) :
    O₂ (heisenbergVOA k hk) ≤ LinearMap.ker (MvPolynomial.lcoeff (R := ℂ) (σ := ℕ) 0) := by
  rw [O₂, Submodule.span_le]
  rintro x ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, MvPolynomial.lcoeff_apply,
    ← MvPolynomial.constantCoeff_eq]
  exact constantCoeff_smul_neg_two_eq_zero k hk u v

/-- **The vacuum survives the `O₂`-quotient**: `𝟙 ∉ O₂(M(1))` (its augmentation is
`constantCoeff 1 = 1 ≠ 0`, while `O₂ ⊆ ker(constantCoeff)`). -/
theorem heisenberg_vacuum_notMem_O₂ (k : ℂ) (hk : k ≠ 0) :
    (vacuum : Fock) ∉ O₂ (heisenbergVOA k hk) := by
  intro hmem
  have h := O₂_le_ker_constantCoeff k hk hmem
  rw [LinearMap.mem_ker, MvPolynomial.lcoeff_apply, ← MvPolynomial.constantCoeff_eq] at h
  -- constantCoeff (1 : Fock) = 1
  rw [show (vacuum : Fock) = (1 : Fock) from rfl, map_one] at h
  exact one_ne_zero h

/-- **`A₂(M(1))` is nonzero** (`Nontrivial`): the class of the vacuum `[𝟙] ≠ 0` in the quotient
`A₂ = Fock ⧸ O₂`, since `𝟙 ∉ O₂`. This is the nonzero base of the infinite-dimensional
`A₂(M(1)) ≅ ℂ[x]` (Zhu, Gaberdiel–Neitzke) — the obstruction to `C₂`-cofiniteness of the free
boson. -/
theorem heisenberg_A2_nontrivial (k : ℂ) (hk : k ≠ 0) :
    Nontrivial (A₂ (heisenbergVOA k hk)) := by
  refine ⟨mk₂ (heisenbergVOA k hk) vacuum, 0, ?_⟩
  rw [mk₂, Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]
  exact heisenberg_vacuum_notMem_O₂ k hk

/-! ## §4  Reading off the `X₀ⁿ`-coefficient via `∂₀ⁿ` then constant term -/

/-- A monomial `monomial s c` is a pure power of `X₀` iff its exponent vector is `single 0 (s 0)`
(no support outside `0`). -/
theorem single_zero_eq_iff (s : ℕ →₀ ℕ) (n : ℕ) :
    s = Finsupp.single 0 n ↔ (s 0 = n ∧ ∀ i, i ≠ 0 → s i = 0) := by
  constructor
  · rintro rfl
    refine ⟨by simp, fun i hi => ?_⟩
    rw [Finsupp.single_apply, if_neg (by exact fun h => hi h.symm)]
  · rintro ⟨h0, hrest⟩
    apply Finsupp.ext; intro i
    rw [Finsupp.single_apply]
    by_cases hi : (0 : ℕ) = i
    · subst hi; rw [if_pos rfl, h0]
    · rw [if_neg hi, hrest i (fun h => hi h.symm)]

/-- Iterated `pderiv 0` on a monomial, then constant term: survives iff the monomial is exactly
`X₀ⁿ`, with value `n!·c`.  `∂₀ⁿ (X^s·c)` is a falling-factorial multiple of `X^{s - n·e₀}·c`,
whose constant term is nonzero only when `s = n·e₀ = single 0 n`. -/
theorem constantCoeff_pderiv0_iterate_monomial (n : ℕ) (s : ℕ →₀ ℕ) (c : ℂ) :
    MvPolynomial.constantCoeff ((pderiv (0 : ℕ))^[n] (monomial s c))
      = if s = Finsupp.single 0 n then (n.factorial : ℂ) * c else 0 := by
  classical
  induction n generalizing s c with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.factorial_zero, Nat.cast_one, one_mul]
    rw [MvPolynomial.constantCoeff_monomial]
    by_cases h : s = 0
    · rw [if_pos h, if_pos (by rw [h]; simp)]
    · rw [if_neg h, if_neg (by rw [Finsupp.single_zero]; exact h)]
  | succ m ih =>
    rw [Function.iterate_succ, Function.comp_apply, pderiv_monomial, ih]
    -- inner if-condition is `s - e₀ = single 0 m`, value `m! * (c * s 0)`
    by_cases hs : s = Finsupp.single 0 (m + 1)
    · -- pure power: s = single 0 (m+1); then s - e₀ = single 0 m
      rw [if_pos hs]
      have hsub : s - Finsupp.single 0 1 = Finsupp.single 0 m := by
        rw [hs]; apply Finsupp.ext; intro i
        rw [Finsupp.tsub_apply, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply]
        by_cases hi : (0:ℕ) = i <;> simp [hi]
      rw [if_pos hsub, hs, Finsupp.single_eq_same, Nat.factorial_succ]
      push_cast; ring
    · -- not a pure power; show the inner `if` is also false (or the coefficient `s 0` vanishes)
      rw [if_neg hs]
      by_cases hsub : s - Finsupp.single 0 1 = Finsupp.single 0 m
      · rw [if_pos hsub]
        -- here `s - e₀ = single 0 m` but `s ≠ single 0 (m+1)`, so necessarily `s 0 = 0`,
        -- making the falling coefficient `c * (s 0) = 0`.
        have hs0 : s 0 = 0 := by
          by_contra hne
          apply hs
          rw [single_zero_eq_iff]
          refine ⟨?_, ?_⟩
          · -- s 0 = m + 1 from (s - e₀) 0 = m and s 0 ≥ 1
            have := congrArg (fun (t : ℕ →₀ ℕ) => t 0) hsub
            simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at this
            omega
          · -- s i = 0 for i ≠ 0, from (s - e₀) i = 0 for i ≠ 0
            intro i hi
            have := congrArg (fun (t : ℕ →₀ ℕ) => t i) hsub
            simp only [Finsupp.tsub_apply, Finsupp.single_apply] at this
            rw [if_neg (by exact fun h => hi h.symm), if_neg (by exact fun h => hi h.symm)] at this
            omega
        rw [hs0]; push_cast; ring
      · rw [if_neg hsub]

/-- The linear-map power `((pderiv 0).toLinearMap)^n` agrees with the function-iterate
`(pderiv 0)^[n]`. -/
theorem pderiv0_pow_eq_iterate (n : ℕ) (p : Fock) :
    (((pderiv (0:ℕ)).toLinearMap : Fock →ₗ[ℂ] Fock) ^ n) p = (pderiv (0:ℕ))^[n] p := by
  rw [Module.End.coe_pow]; rfl

/-- **Reading off the `X₀ⁿ`-coefficient**: for every `p`,
`constantCoeff (∂₀ⁿ p) = n! · coeff (single 0 n) p`. By `ℂ`-linearity from the monomial case. -/
theorem constantCoeff_pderiv0_iterate (n : ℕ) (p : Fock) :
    MvPolynomial.constantCoeff ((pderiv (0 : ℕ))^[n] p)
      = (n.factorial : ℂ) * MvPolynomial.coeff (Finsupp.single 0 n) p := by
  classical
  -- Package both sides as linear maps `Fock →ₗ[ℂ] ℂ` and check on monomials.
  set LHS : Fock →ₗ[ℂ] ℂ :=
    (MvPolynomial.lcoeff (R := ℂ) (σ := ℕ) 0).comp
      (((pderiv (0:ℕ)).toLinearMap : Fock →ₗ[ℂ] Fock) ^ n) with hLHS
  set RHS : Fock →ₗ[ℂ] ℂ :=
    (n.factorial : ℂ) • (MvPolynomial.lcoeff (R := ℂ) (σ := ℕ) (Finsupp.single 0 n)) with hRHS
  have heq : LHS = RHS := by
    refine MvPolynomial.linearMap_ext fun s => ?_
    refine LinearMap.ext fun c => ?_
    show LHS (monomial s c) = RHS (monomial s c)
    rw [hLHS, hRHS, LinearMap.comp_apply, MvPolynomial.lcoeff_apply,
      ← MvPolynomial.constantCoeff_eq, pderiv0_pow_eq_iterate,
      constantCoeff_pderiv0_iterate_monomial, LinearMap.smul_apply,
      MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial, smul_eq_mul]
    by_cases h : s = Finsupp.single 0 n
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  have := congrArg (fun (f : Fock →ₗ[ℂ] ℂ) => f p) heq
  simp only [hLHS, hRHS, LinearMap.comp_apply, MvPolynomial.lcoeff_apply,
    ← MvPolynomial.constantCoeff_eq, pderiv0_pow_eq_iterate, LinearMap.smul_apply,
    smul_eq_mul] at this
  exact this

/-! ## §5  `osc k 1 = (X₀)₍₁₎` preserves `O₂`; the `X₀ⁿ`-coefficient functional kills `O₂` -/

/-- **`osc k 1` preserves `O₂`**: `p ∈ O₂ → osc k 1 p ∈ O₂`. Reduce (`Submodule.span_le`,
`comap`) to the generators, where `osc1_smul_neg_two_mem_O₂` applies. -/
theorem osc1_mem_O₂_of_mem (k : ℂ) (hk : k ≠ 0) {p : Fock} (hp : p ∈ O₂ (heisenbergVOA k hk)) :
    osc k 1 p ∈ O₂ (heisenbergVOA k hk) := by
  have hle : O₂ (heisenbergVOA k hk)
      ≤ Submodule.comap (osc k 1) (O₂ (heisenbergVOA k hk)) := by
    rw [O₂, Submodule.span_le]
    rintro x ⟨u, v, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact osc1_smul_neg_two_mem_O₂ k hk u v
  exact hle hp

/-- **`pderiv 0` preserves `O₂`**: `p ∈ O₂ → pderiv 0 p ∈ O₂`. Since `osc k 1 = k·pderiv 0`
(`k ≠ 0`), `pderiv 0 p = k⁻¹ • osc k 1 p ∈ O₂`. -/
theorem pderiv0_mem_O₂_of_mem (k : ℂ) (hk : k ≠ 0) {p : Fock} (hp : p ∈ O₂ (heisenbergVOA k hk)) :
    pderiv (0 : ℕ) p ∈ O₂ (heisenbergVOA k hk) := by
  have hosc : osc k 1 p = k • pderiv (0 : ℕ) p := by
    rw [osc_apply_pos k (by norm_num : (0:ℤ) < 1),
      show ((1:ℤ) - 1).toNat = 0 from rfl, Int.cast_one, one_smul]
  have hk1 : pderiv (0 : ℕ) p = k⁻¹ • osc k 1 p := by
    rw [hosc, smul_smul, inv_mul_cancel₀ hk, one_smul]
  rw [hk1]
  exact Submodule.smul_mem _ _ (osc1_mem_O₂_of_mem k hk hp)

/-- **`∂₀ⁿ` preserves `O₂`** (iterating `pderiv0_mem_O₂_of_mem`). -/
theorem pderiv0_iterate_mem_O₂ (k : ℂ) (hk : k ≠ 0) (n : ℕ) {p : Fock}
    (hp : p ∈ O₂ (heisenbergVOA k hk)) :
    (pderiv (0 : ℕ))^[n] p ∈ O₂ (heisenbergVOA k hk) := by
  induction n with
  | zero => simpa using hp
  | succ m ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact pderiv0_mem_O₂_of_mem k hk ih

/-- **The `X₀ⁿ`-coefficient functional kills `O₂`**: for `p ∈ O₂`, `coeff (single 0 n) p = 0`.
Read off via `∂₀ⁿ` then constant term: `n!·coeff(single 0 n) p = constantCoeff(∂₀ⁿ p) = 0`, since
`∂₀ⁿ p ∈ O₂` (`pderiv0_iterate_mem_O₂`) and `O₂` has no constant term (`O₂_le_ker_constantCoeff`). -/
theorem coeff_single0_eq_zero_of_mem_O₂ (k : ℂ) (hk : k ≠ 0) (n : ℕ) {p : Fock}
    (hp : p ∈ O₂ (heisenbergVOA k hk)) :
    MvPolynomial.coeff (Finsupp.single 0 n) p = 0 := by
  have hcc : MvPolynomial.constantCoeff ((pderiv (0 : ℕ))^[n] p) = 0 := by
    have h := O₂_le_ker_constantCoeff k hk (pderiv0_iterate_mem_O₂ k hk n hp)
    rwa [LinearMap.mem_ker, MvPolynomial.lcoeff_apply, ← MvPolynomial.constantCoeff_eq] at h
  have hkey := constantCoeff_pderiv0_iterate n p
  rw [hcc] at hkey
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [eq_comm, mul_eq_zero] at hkey
  rcases hkey with h | h
  · exact absurd h hfac
  · exact h

/-! ## §6  The infinite linearly-independent family `{[X₀ⁿ]}` and `¬ C2Cofinite` -/

/-- **The pure-`X₀` tower `{X₀ⁿ}` is linearly independent modulo `O₂`**: the classes
`[X₀ⁿ] = mk₂(X₀ⁿ) ∈ A₂(M(1))` are `ℂ`-linearly independent. The `n`-th coordinate functional
`coeff (single 0 ·)` separates them: it is `δ` on the tower and (by `coeff_single0_eq_zero_of_mem_O₂`)
vanishes on `O₂`, hence descends to `A₂` and witnesses independence. -/
theorem heisenberg_A2_tower_linearIndependent (k : ℂ) (hk : k ≠ 0) :
    LinearIndependent ℂ (fun n : ℕ => mk₂ (heisenbergVOA k hk) ((X 0 : Fock) ^ n)) := by
  classical
  -- Use the coefficient functionals as a separating dual family.
  rw [linearIndependent_iff]
  intro ℓ hℓ
  set W := heisenbergVOA k hk
  -- the lifted element `q = ∑ ℓ n • X₀ⁿ ∈ Fock`
  set q : Fock := ℓ.sum (fun n c => c • (X 0 : Fock) ^ n) with hq
  -- hℓ : `mk₂ W q = 0`, hence `q ∈ O₂`
  have hmkq : mk₂ W q = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hℓ
    rw [hq, Finsupp.sum, map_sum]
    simp only [map_smul]
    exact hℓ
  have hqmem : q ∈ O₂ W := by
    rwa [mk₂, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmkq
  -- each coefficient: coeff (single 0 m) q = ℓ m, and it must be 0 (kills O₂)
  ext m
  have hcm : MvPolynomial.coeff (Finsupp.single 0 m) q = ℓ m := by
    rw [hq, Finsupp.sum]
    rw [show MvPolynomial.coeff (Finsupp.single 0 m) (∑ n ∈ ℓ.support, ℓ n • (X 0 : Fock) ^ n)
          = (MvPolynomial.lcoeff (R := ℂ) (σ := ℕ) (Finsupp.single 0 m))
              (∑ n ∈ ℓ.support, ℓ n • (X 0 : Fock) ^ n) from by rw [MvPolynomial.lcoeff_apply],
      map_sum]
    have hterm : ∀ n ∈ ℓ.support,
        (MvPolynomial.lcoeff (R := ℂ) (σ := ℕ) (Finsupp.single 0 m)) (ℓ n • (X 0 : Fock) ^ n)
          = if m = n then ℓ n else 0 := by
      intro n _
      rw [map_smul, MvPolynomial.lcoeff_apply, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.coeff_monomial, smul_eq_mul]
      by_cases h : m = n
      · rw [if_pos h, if_pos (by rw [h]), mul_one]
      · rw [if_neg h, if_neg (by intro he; exact h (by
          have := congrArg (fun t : ℕ →₀ ℕ => t 0) he; simpa using this.symm)), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq ℓ.support m (fun n => ℓ n)]
    by_cases hm : m ∈ ℓ.support
    · rw [if_pos hm]
    · rw [if_neg hm, Finsupp.notMem_support_iff.mp hm]
  rw [← hcm]
  exact coeff_single0_eq_zero_of_mem_O₂ k hk m hqmem

/-- **The free boson `M(1)` is NOT `C₂`-cofinite** (Gannon §5.3.2; Zhu [574];
Gaberdiel–Neitzke [229]): `A₂(M(1))` is infinite-dimensional — it contains the infinite
`ℂ`-linearly-independent family `{[X₀ⁿ] : n ∈ ℕ}` (the classes `[a₋₁ⁿ𝟙]`, generating
`A₂(M(1)) ≅ ℂ[x]`). Hence `¬ C2Cofinite (heisenbergVOA k hk)`. -/
theorem heisenberg_not_C2Cofinite (k : ℂ) (hk : k ≠ 0) :
    ¬ C2Cofinite (heisenbergVOA k hk) := by
  intro hfin
  -- C2Cofinite W := FiniteDimensional ℂ (A₂ W); an infinite independent family contradicts it.
  rw [C2Cofinite] at hfin
  -- with `hfin : Module.Finite ℂ (A₂ W)`, the ℕ-indexed independent family forces `Finite ℕ`.
  haveI : Module.Finite ℂ (A₂ (heisenbergVOA k hk)) := hfin
  haveI hfinite : Finite ℕ :=
    (heisenberg_A2_tower_linearIndependent k hk).finite
  exact not_finite ℕ

end VOA
