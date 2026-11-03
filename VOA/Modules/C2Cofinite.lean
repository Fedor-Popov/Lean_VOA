/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuAlgebra
import VOA.Core.SkewSymmetry
import VOA.Core.Identities

/-!
# `C₂`-cofiniteness and the Poisson algebra `A₂(𝒱)`  (Gannon §5.3.2, Def 5.3.5)

The finiteness condition that guarantees convergence of characters and hence modularity —
"the key technical role in the statement and proof of the modularity of VOA characters".

* `O₂(𝒱) := span{u₍₋₂₎ v}`; `A₂(𝒱) := 𝒱 / O₂(𝒱)`, built here as the `ℂ`-module quotient.
* `A₂(𝒱)` is a **commutative Poisson algebra**: associative-commutative product
  `[u·v] = u₍₋₁₎v` (= `normalMul`) and Lie bracket `[uv] = u₍₀₎v`.
* **`C₂`-cofinite** (Def 5.3.5): `dim A₂(𝒱) < ∞` (`C2Cofinite`). ("`C₂`" is Zhu's name for
  `O₂`.)

## Status

Axiom-clean for the **definitional layer + the representative-level Poisson identities**:
`O₂`, the `ℂ`-module `A₂(𝒱)`, the projection `mk₂`, the Poisson product/bracket *operations on
`𝒱`* (`poissonMul = u₍₋₁₎v`, `poissonBracket = u₍₀₎v`), the predicate `C2Cofinite`, and the
genuine mode-algebra inputs to the Poisson structure: **`L_neg_one_mem_O₂`/`T_mem_O₂`/
`Tpow_mem_O₂`** (`Tᵏ𝒱 ⊆ O₂`), **`poissonMul_sub_swap_mem_O₂`** (commutativity of the product
mod `O₂`, via skew-symmetry 5.1.8), **`poissonBracket_add_swap_mem_O₂`** (antisymmetry of the
bracket mod `O₂`, via skew), and **`poissonBracket_leibniz`** (the bracket Leibniz rule, via the
`a = 0` commutator formula).

The **descent of the Poisson structure** to a `CommRing`/`LieRing` on `A₂(𝒱)` is **proved**
in `Modules.PoissonDescent` (`A₂CommRing`, `A₂LieRing`, off `O₂` being a two-sided ideal via
`mode_iterate`), and **`¬ C2Cofinite`** for the free boson in `Examples.HeisenbergC2`. The
**finite generation `5.3.11a`** target — if `C2Cofinite W` then `𝒱` is spanned by iterated
products of an `A₂(𝒱)`-basis lift — is **proved unconditionally** in `Modules.FiniteGeneration`
(reduction to one degree step) + `Modules.FiniteGenerationProof` (`iterProdSpan_eq_top`, the PBW
`mode_iterate` master peeling), axiom-clean.

## ⚠ The Heisenberg instance — the correct direction

One might ask to "verify `C2Cofinite` for the Heisenberg VOA". This is
**mathematically the wrong way round**: the rank-1 Heisenberg / free-boson VOA `M(1) =
𝒱(ĥ, k)` (`Examples.Heisenberg`, central charge `c = 1`) is the *canonical example of a VOA
that is **NOT** `C₂`-cofinite* — one has `A₂(M(1)) ≅ ℂ[x]` (the classes of `aₙ₋₁ 𝟙`), which
is **infinite-dimensional** (Zhu [574]; Gaberdiel–Neitzke [229]). `C₂`-cofiniteness is
exactly the nontrivial extra condition that the free boson *fails* and that the `C₂`-cofinite
examples — lattice VOAs `𝒱(L)` for positive-definite `L`, rational VOAs, the Moonshine
module `V♮` — satisfy. So the honest worked statement is **`¬ C2Cofinite (heisenbergVOA k hk)`**,
**proved** as `Examples.HeisenbergC2.heisenberg_not_C2Cofinite` (axiom-clean): the infinite
tower `{[X₀ⁿ] : n ∈ ℕ}` in `A₂(M(1))` is linearly independent (separated by the augmentation
`coeff (single 0 ·)`, which `δ`s the tower and kills `O₂`), contradicting finite-dimensionality.

## Dependencies
* `VOA.Modules.ZhuAlgebra` (the parallel quotient construction and `normalMul`).

## References
* Gannon §5.3.2, Def 5.3.5, eqs. (5.3.11); Zhu [574]; Gaberdiel–Neitzke [229];
  Dong–Li–Mason; Li (Poisson structure).
-/

namespace VOA

open Module (End)
open scoped BigOperators
open Classical
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `O₂(𝒱)` and the Poisson algebra `A₂(𝒱)` -/

/-- `O₂(𝒱) := span{u₍₋₂₎ v : u, v ∈ 𝒱}` (Gannon Def. 5.3.5; "`C₂`" in Zhu's notation). -/
def O₂ (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ u v : 𝒱, x = W.smul u (-2) v}

/-- The **Poisson algebra** `A₂(𝒱) := 𝒱 / O₂(𝒱)` = `𝒱 / C₂(𝒱)`, as a `ℂ`-module (Gannon §5.3.2;
Gaberdiel–Neitzke's `A_{[2]}(𝒱)`, Arakawa's `R_𝒱`).  **Notation clash:** this is *not* the second
higher Zhu algebra `A_2(𝒱)` of Dong–Li–Mason, which is `An W 2` (`Modules.ZhuVermaAn`).  Its
commutative product `[u·v] = u₍₋₁₎v` and Lie bracket `[uv] = u₍₀₎v` descend from `𝒱` — see
the status note. -/
abbrev A₂ (W : VertexOperatorAlgebra 𝒱) : Type u := 𝒱 ⧸ O₂ W

/-- The canonical projection `𝒱 → A₂(𝒱)`. -/
def mk₂ (W : VertexOperatorAlgebra 𝒱) : 𝒱 →ₗ[ℂ] A₂ W := (O₂ W).mkQ

/-- The Poisson **product** representative `u₍₋₁₎ v` on `𝒱` (descends to the
associative-commutative product of `A₂(𝒱)`; Gannon §5.3.2). Equal to `normalMul`. -/
def poissonMul (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) : 𝒱 := W.smul u (-1) v

/-- The Poisson **bracket** representative `u₍₀₎ v` on `𝒱` (descends to the Lie bracket of
`A₂(𝒱)`; Gannon §5.3.2). -/
def poissonBracket (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) : 𝒱 := W.smul u 0 v

@[simp] theorem poissonMul_def (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    poissonMul W u v = W.smul u (-1) v := rfl

@[simp] theorem poissonMul_eq_normalMul (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    poissonMul W u v = normalMul W u v := rfl

@[simp] theorem poissonBracket_def (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    poissonBracket W u v = W.smul u 0 v := rfl

/-! ## The Poisson structure at the representative level (proved, axiom-clean)

The Poisson-algebra identities of `A₂(𝒱)` (Gannon §5.3.2) are established here on `𝒱`, at the
level of representatives modulo `O₂` — the genuine mode-algebra inputs to the structure: the
translation-image `T(𝒱) ⊆ O₂`, commutativity of the product mod `O₂` (via skew-symmetry
5.1.8), and the bracket Leibniz rule (the `a = 0` commutator formula). Their *descent* to a
`CommRing`/`LieRing` on the quotient additionally needs `O₂` to be a two-sided ideal for
`₍₋₁₎` (Zhu/Li's structure theorem); see the status note. -/

/-- **`L₋₁(𝒱) ⊆ O₂`**: every translate `L₋₁ x = T x = x₍₋₂₎𝟙` lies in `O₂` (Gannon §5.3.2).
The creation theorem `creation_pow` (`x₍₋₂₎𝟙 = Tx`) lands `Tx` on a generator of `O₂`. -/
theorem L_neg_one_mem_O₂ (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) : W.L (-1) x ∈ O₂ W := by
  have hc := creation_pow W x 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul] at hc
  rw [T_eq_Lneg1, show (-(1 : ℤ) - 1) = -2 from by norm_num] at hc
  rw [← hc]
  exact Submodule.subset_span ⟨x, W.vacuum, rfl⟩

/-- **`T(𝒱) ⊆ O₂`** (the translation operator lands in `O₂`). -/
theorem T_mem_O₂ (W : VertexOperatorAlgebra 𝒱) (y : 𝒱) : W.toPreVertexAlgebra.T y ∈ O₂ W := by
  rw [T_eq_Lneg1]; exact L_neg_one_mem_O₂ W y

/-- **`Tᵏ(𝒱) ⊆ O₂` for `k ≥ 1`** (iterating `T_mem_O₂`). -/
theorem Tpow_mem_O₂ (W : VertexOperatorAlgebra 𝒱) {k : ℕ} (hk : 1 ≤ k) (x : 𝒱) :
    (W.toPreVertexAlgebra.T ^ k) x ∈ O₂ W := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ', Module.End.mul_apply]
  exact T_mem_O₂ W _

/-- **Commutativity of the Poisson product mod `O₂`** (Gannon §5.3.2, via skew-symmetry 5.1.8):
`u₍₋₁₎v − v₍₋₁₎u ∈ O₂`. The skew mode formula `skew_mode` writes
`u₍₋₁₎v = v₍₋₁₎u + ∑_{j≥1} (1/j!)(±) Tʲ(…)`, whose `j = 0` term is exactly `v₍₋₁₎u` and whose
`j ≥ 1` tail is a finite sum of translates `Tʲ(…) ∈ O₂` (`Tpow_mem_O₂`). So the descended
product on `A₂(𝒱)` is commutative. -/
theorem poissonMul_sub_swap_mem_O₂ (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    poissonMul W u v - poissonMul W v u ∈ O₂ W := by
  simp only [poissonMul_def]
  have hsum := skew_mode W u v (-1)
  set c : ℕ → 𝒱 := fun j => ((j.factorial : ℂ)⁻¹) • (sgn (-(-1) - 1 - (j : ℤ))) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-(-1) - 1 - (j : ℤ)) u)) with hc
  have hceq : c = fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn ((0 : ℤ) - (j : ℤ))) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) ((0 : ℤ) - (j : ℤ)) u)) := by
    funext j; simp only [hc]; rw [show (-(-1 : ℤ) - 1 - (j : ℤ)) = (0 : ℤ) - (j : ℤ) from by ring]
  have hfin : (Function.support c).Finite := by rw [hceq]; exact skew_support_finite W u v 0
  set s : Finset ℕ := insert 0 hfin.toFinset with hs
  have hsubset : Function.support c ⊆ ↑s := by
    intro j hj
    exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hj))
  have hsum' : W.smul u (-1) v = ∑ j ∈ s, c j := by
    rw [hsum]; exact finsum_eq_finsetSum_of_support_subset c hsubset
  have hc0 : c 0 = W.smul v (-1) u := by
    simp only [hc, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
      Module.End.one_apply, Nat.cast_zero]
    rw [show (-(-1 : ℤ) - 1 - (0 : ℤ)) = 0 from by ring,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) from by norm_num, sgn_natCast, pow_zero, one_smul,
      PreVertexAlgebra.smul_def, mode_apply]
    norm_num
  have h0s : (0 : ℕ) ∈ s := Finset.mem_insert_self 0 _
  rw [hsum', ← Finset.sum_erase_add s c h0s, hc0, add_sub_cancel_right]
  apply Submodule.sum_mem
  intro j hj
  have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
  simp only [hc]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (Tpow_mem_O₂ W (Nat.one_le_iff_ne_zero.mpr hj0) _))

/-- **Antisymmetry of the Poisson bracket mod `O₂`** (Gannon §5.3.2, via skew-symmetry 5.1.8):
`u₍₀₎v + v₍₀₎u ∈ O₂`. The skew mode formula at `n = 0` gives `u₍₀₎v = −v₍₀₎u + ∑_{j≥1} Tʲ(…)`
(the `j = 0` term is `sgn(−1)·v₍₀₎u = −v₍₀₎u`), whose `j ≥ 1` tail lies in `O₂`. So the descended
bracket on `A₂(𝒱)` is antisymmetric (a Lie bracket). -/
theorem poissonBracket_add_swap_mem_O₂ (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    poissonBracket W u v + poissonBracket W v u ∈ O₂ W := by
  simp only [poissonBracket_def]
  have hsum := skew_mode W u v 0
  set c : ℕ → 𝒱 := fun j => ((j.factorial : ℂ)⁻¹) • (sgn (-(0 : ℤ) - 1 - (j : ℤ))) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-(0 : ℤ) - 1 - (j : ℤ)) u)) with hc
  have hceq : c = fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn ((-1 : ℤ) - (j : ℤ))) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) ((-1 : ℤ) - (j : ℤ)) u)) := by
    funext j; simp only [hc]; rw [show (-(0 : ℤ) - 1 - (j : ℤ)) = (-1 : ℤ) - (j : ℤ) from by ring]
  have hfin : (Function.support c).Finite := by rw [hceq]; exact skew_support_finite W u v (-1)
  set s : Finset ℕ := insert 0 hfin.toFinset with hs
  have hsubset : Function.support c ⊆ ↑s := fun j hj =>
    Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hj))
  have hsum' : W.smul u 0 v = ∑ j ∈ s, c j := by
    rw [hsum]; exact finsum_eq_finsetSum_of_support_subset c hsubset
  have hc0 : c 0 = -(W.smul v 0 u) := by
    simp only [hc, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
      Module.End.one_apply, Nat.cast_zero]
    rw [show (-(0 : ℤ) - 1 - (0 : ℤ)) = -1 from by ring, sgn_neg_one, neg_one_smul,
      PreVertexAlgebra.smul_def, mode_apply, show (-(0 : ℤ) - 1) = -1 from by ring]
  have h0s : (0 : ℕ) ∈ s := Finset.mem_insert_self 0 _
  rw [hsum', show W.smul v 0 u = -(c 0) from by rw [hc0, neg_neg],
    ← Finset.sum_erase_add s c h0s, add_neg_cancel_right]
  apply Submodule.sum_mem
  intro j hj
  have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
  simp only [hc]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (Tpow_mem_O₂ W (Nat.one_le_iff_ne_zero.mpr hj0) _))

/-- **Leibniz rule for the Poisson bracket** (Gannon §5.3.2): the bracket `u₍₀₎·` is a
derivation of the product `v₍₋₁₎w`,
`u₍₀₎(v₍₋₁₎w) − v₍₋₁₎(u₍₀₎w) = (u₍₀₎v)₍₋₁₎w`. This is the `n = −1` case of the derivation
property `zeroMode_isDerivation` (the `a = 0` commutator formula 5.1.7c), and descends to the
Poisson compatibility `[u, v·w] = [u,v]·w + v·[u,w]` on `A₂(𝒱)`. -/
theorem poissonBracket_leibniz (W : VertexOperatorAlgebra 𝒱) (u v w : 𝒱) :
    poissonBracket W u (poissonMul W v w) - poissonMul W v (poissonBracket W u w)
      = poissonMul W (poissonBracket W u v) w := by
  simp only [poissonBracket_def, poissonMul_def]
  exact W.zeroMode_isDerivation u v w (-1)

/-! ## `C₂`-cofiniteness -/

/-- **`C₂`-cofinite** (Gannon Def. 5.3.5, after [574]): `A₂(𝒱)` is finite-dimensional.
The key hypothesis of Zhu's modularity theorem (`Modularity.ZhuTheorem`). -/
def C2Cofinite (W : VertexOperatorAlgebra 𝒱) : Prop := FiniteDimensional ℂ (A₂ W)

/-!
### The Poisson descent, `¬C2Cofinite`, and finite generation

* **The Poisson algebra structure is** in `Modules.PoissonDescent`: `O₂` is a two-sided
  ideal for `₍₋₁₎`/`₍₀₎` (off `mode_iterate`), and the descended product/bracket give the
  `CommRing (A₂ W)` (`A₂CommRing`, with associativity mod `O₂`) and `LieRing (A₂ W)`
  (`A₂LieRing`) — axiom-clean, built on the representative identities above.

* **`¬ C2Cofinite (heisenbergVOA k hk)` is** in `Examples.HeisenbergC2`
  (`heisenberg_not_C2Cofinite`): the free boson `M(1)` is the canonical *non*-`C₂`-cofinite VOA.
  The infinite `ℂ`-linearly-independent tower `{[X₀ⁿ] : n ∈ ℕ}` in `A₂(M(1)) = Fock ⧸ O₂` is
  separated by the augmentation `coeff (single 0 ·)` (which `δ`s the tower and kills `O₂`), so
  `A₂(M(1))` is infinite-dimensional — axiom-clean, not faked.

* **Finite generation (5.3.11a)** is not proved in this file: if
  `C2Cofinite W`, then `𝒱` is finitely generated — lifts `u¹,…,uⁿ` of an `A₂(𝒱)`-basis give a
  spanning set `{u^{i₁}₍₋m₁₎⋯u^{iₖ}₍₋mₖ₎ 𝟙 : m₁ > ⋯ > mₖ > 0}` (a PBW-style reduction off the
  `O₂` definition). Built on the `O₂`/`A₂` scaffolding here; not faked or axiomatized.
-/

end VOA
