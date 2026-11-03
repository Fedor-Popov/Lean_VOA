/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionVOA

/-!
# `C₂`-cofiniteness of the symplectic fermions

`A₂SF_finiteDimensional` — the `C₂` (Poisson) quotient `FockSF ⧸ O₂SF` of the symplectic-fermion
super vertex operator algebra is **finite-dimensional**, with an explicit four-element spanning
set and the bound `dim ≤ 4`.

## Why the quotient is taken by hand here

`Modules.C2Cofinite` defines `O₂ W` and `C2Cofinite W` for a **bosonic**
`W : VertexOperatorAlgebra 𝒱`, and there is no super analogue anywhere in the library.  The
ambient symplectic fermions are `sympFermSVOA : SuperVertexOperatorAlgebra FockSF`, so the
predicate cannot be applied to them.  `O₂SF` below is therefore the *same formula*,
`span{u₍₋₂₎v}`, written for the super `SuperVertexAlgebra.smul`; nothing else about it is new.

## The argument

Symplectic fermions are a free fermionic Fock space `FockSF = Λ(χᵃ₋ₖ₋₁ : k ≥ 0, a ∈ {0,1})`
(literally: `CliffordAlgebra` at quadratic form `0`), and `stWordSF_span` says the creation
words span it.  Three steps:

1. **Only one vertex-algebra input is needed** (`sfCre_one_mul_mem_O₂SF`).  The weight-one
   state `χᵃ₋₁|0⟩` is a single Clifford generator, its vertex operator is the undifferentiated
   field `χᵃ(z)` (`YSF_sfCre_zero`, off `YwordSF_singleton`), and so its `₍₋₂₎` mode is the
   *level-one creation operator*:
   `(χᵃ₋₁|0⟩)₍₋₂₎ v = χᵃ₋₂ v = ι(single (1,a) 1) · v`.
   Hence **every** state with a level-`1` creation operator in front of it is in `O₂SF` — a
   statement about arbitrary `v`, not just about `T`-translates.
2. **Levels `≥ 2` follow by translation** (`sfCre_succ_mul_mem_O₂SF`).  `T` is an even
   derivation with `T(χᵃ₋ₖ₋₁|0⟩) = (k+1)χᵃ₋ₖ₋₂|0⟩` (`T_sfCre`), and `T 𝒱 ⊆ O₂SF`
   (`T_mem_O₂SF`, because `T y = y₍₋₂₎𝟙` — in the super structure this is the *definition* of
   `T`, so no creation theorem is needed).  So
   `(k+2)·χᵃ₋ₖ₋₃ v = T(χᵃ₋ₖ₋₂ v) − χᵃ₋ₖ₋₂ (T v)`, and induction on the level closes.
3. **The exterior-algebra bookkeeping** (`stWordSF_mem_sup`).  Peel the leftmost creation
   operator off a word.  If its level is `≥ 1`, step 2 puts the whole word in `O₂SF`.  If its
   level is `0`, the inductive hypothesis propagates, because both `sfBottom` (the span of the
   four bottom states) and `sfHigh` (the span of the level-`≥ 1` states, which is contained in
   `O₂SF`) are stable under left multiplication by a weight-one generator — the latter by plain
   anticommutation, `χᵃ₋₁(χᵇ₋ₖ₋₁ v) = −χᵇ₋ₖ₋₁(χᵃ₋₁ v)`.

## ⚠ `T 𝒱 ⊆ O₂` alone is **not** enough

It is tempting to run the whole argument off `Tpow_mem_O₂` (`Tᵏ𝒱 ⊆ O₂`) alone, using
`χᵃ₋ₙ₋₁ ∝ (T χᵃ)₋ₙ` to trade every mode of index `≤ −2` for a translate.  That does not close.
The move `χᵃ₋ₙ w ≡ −(n−1)⁻¹ χᵃ₋ₙ₊₁ (T w)  (mod T𝒱)` lowers the level of the leading operator but
raises the level of one of the others, so the total excess `∑ᵢ nᵢ − (length)` is *preserved* and
the recursion never terminates.  And this is not a defect of the bookkeeping: `𝒱 ⧸ T𝒱` really is
infinite-dimensional here.  As a `ℂ[T]`-module `𝒱₁ = ℂ[T]χ⁰ ⊕ ℂ[T]χ¹`, so the two-fermion sector
`χ⁰ ∧ χ¹` is `ℂ[x] ⊗ ℂ[y]` with `T = ∂ₓ + ∂ᵧ`, whose cokernel `ℂ[x,y]/(∂ₓ+∂ᵧ)ℂ[x,y] ≅ ℂ[x−y]`
is infinite-dimensional.

What makes the argument work is the strictly stronger generator: `O₂` is spanned by `u₍₋₂₎v` for
**arbitrary** `v`, and at `u = χᵃ₋₁|0⟩` that is `χᵃ₋₂ v` for arbitrary `v` — an operator
statement, not a statement about a single translate.  `T` is then needed only to climb from
level `1` to level `k`, where it *does* terminate because the level of a *single* operator is a
genuine induction variable.

The bottom states are the words in the two weight-one modes only, and a generator squares to
zero, so the only survivors are `|0⟩, χ⁰₋₁|0⟩, χ¹₋₁|0⟩, χ⁰₋₁χ¹₋₁|0⟩` — the exterior algebra on
two odd generators, dimension at most `4`.

`sfHigh` is deliberately *smaller* than `O₂SF`: the induction needs stability under left
multiplication by `χᵃ₋₁`, which the full `O₂SF` (a span of `u₍₋₂₎v` over **all** `u`) does not
visibly have, while `sfHigh` has it by one anticommutation.

## ⚠ What this does **not** prove

This is the **ambient** computation.  `tripletW2` is the *even part* `(FockSF)₀̄`, and its `O₂`
is formed from its **own** vertex operators.  The easy inclusion
`O₂ tripletW2 ⊆ O₂SF ∩ (FockSF)₀̄` runs the **wrong way** to transfer finiteness: it gives a
surjection `A₂(W(2)) ↠ (even part)/(O₂SF ∩ even)`, i.e. it bounds the wrong quotient from
below.  What a triplet proof needs is the reverse inclusion `O₂SF ∩ even ⊆ O₂ tripletW2`
(up to finite defect), which is exactly the orbifold step and is *not* established here.
Nothing in this file should be read as `C2Cofinite tripletW2`.

## Main results

* `A₂SF_finiteDimensional` — `FiniteDimensional ℂ (FockSF ⧸ O₂SF)`.
* `A₂SF_span` — the explicit spanning set: the classes of
  `|0⟩, χ⁰₋₁|0⟩, χ¹₋₁|0⟩, χ⁰₋₁χ¹₋₁|0⟩`.
* `finrank_A₂SF_le_four` — `dim A₂(SF) ≤ 4` (an upper bound only; no basis is computed).
* `sfCre_mul_mem_O₂SF` — every creation operator of level `≥ 1` pushes any state into `O₂SF`.
* `sfBottom_sup_O₂SF_eq_top` — the four bottom states and `O₂SF` exhaust `FockSF`.

## Status

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); no `sorry`, no
new axioms, no use of `VOA.pbw`.

## References
* Abe, *A ℤ₂-orbifold model of the symplectic fermionic vertex operator superalgebra*,
  Math. Z. 255 (2007) 755–792 — for the orbifold step this file does not do.
* Kausch, *Symplectic fermions*, Nucl. Phys. B583 (2000) 513.
* `Modules.C2Cofinite` for the bosonic `O₂`/`A₂`/`C2Cofinite`; `Examples.HeisenbergC2` for the
  opposite (negative) worked example.
-/
namespace VOA.SympFerm

open VOA
open CliffordAlgebra

/-! ## §1  `O₂` for the ambient super vertex operator algebra -/

/-- `O₂(𝒱) := span{u₍₋₂₎v}` for the symplectic-fermion **super** vertex operator algebra. -/
noncomputable def O₂SF : Submodule ℂ FockSF :=
  Submodule.span ℂ {x | ∃ u v : FockSF, x = sympFermSVOA.smul u (-2) v}

theorem O₂SF_def :
    O₂SF = Submodule.span ℂ {x | ∃ u v : FockSF, x = sympFermSVOA.smul u (-2) v} := rfl

/-- Every `u₍₋₂₎v` lies in `O₂SF`. -/
theorem smul_neg_two_mem_O₂SF (u v : FockSF) : sympFermSVOA.smul u (-2) v ∈ O₂SF :=
  Submodule.subset_span ⟨u, v, rfl⟩

/-- The `C₂` (Poisson) quotient of the symplectic fermions. -/
abbrev A₂SF : Type := FockSF ⧸ O₂SF

/-- `u₍₋₂₎v` is the `z¹`-coefficient of `Y(u,z)` on `v`. -/
theorem smul_neg_two_eq (u v : FockSF) : sympFermSVOA.smul u (-2) v = YSF u 1 v := by
  rw [SuperVertexAlgebra.smul_def, mode_apply, show -(-2 : ℤ) - 1 = 1 from by norm_num]
  rfl

/-- **`T(𝒱) ⊆ O₂SF`.** -/
theorem T_mem_O₂SF (y : FockSF) : T y ∈ O₂SF := by
  have h : sympFermSVOA.smul y (-2) vacSF = T y := by rw [smul_neg_two_eq, YSF_one_vac]
  rw [← h]
  exact smul_neg_two_mem_O₂SF y vacSF

/-! ## §2  The creation generators, and the level-`≥ 1` ones lie in `O₂SF` -/

/-- The creation state `χᵃ₋ₖ₋₁|0⟩ = ι(single (k,a) 1)`, the `k`-th generator of species `a`. -/
noncomputable def sfCre (k : ℕ) (a : Fin 2) : FockSF :=
  ι QSF (Finsupp.single ((k, a) : ℕ × Fin 2) (1 : ℂ))

/-- `creBase` is left multiplication by the corresponding generator. -/
theorem creBase_eq_sfCre_mul (k : ℕ) (a : Fin 2) (v : FockSF) :
    creBase ((k, a) : ℕ × Fin 2) v = sfCre k a * v := rfl

/-- The vertex operator of a *weight-one* generator is the undifferentiated field `χᵃ`. -/
theorem YSF_sfCre_zero (a : Fin 2) : YSF (sfCre 0 a) = chi a := by
  rw [sfCre, YSF_single, YwordSF_singleton]
  exact sfGenField_zero_eq a

/-- **The base case**: `(χᵃ₋₁|0⟩)₍₋₂₎ v = χᵃ₋₂ v`, so every state with a level-`1` creation
operator in front of it lies in `O₂SF`.  This is the one genuinely vertex-algebraic input. -/
theorem sfCre_one_mul_mem_O₂SF (a : Fin 2) (v : FockSF) : sfCre 1 a * v ∈ O₂SF := by
  have h : sympFermSVOA.smul (sfCre 0 a) (-2) v = sfCre 1 a * v := by
    rw [smul_neg_two_eq, YSF_sfCre_zero, chi, if_pos (by norm_num : (0 : ℤ) ≤ 1)]
    rfl
  rw [← h]
  exact smul_neg_two_mem_O₂SF _ _

/-- `T` raises the level of a generator: `T χᵃ₋ₖ₋₁|0⟩ = (k+1) χᵃ₋ₖ₋₂|0⟩`. -/
theorem T_sfCre (k : ℕ) (a : Fin 2) : T (sfCre k a) = ((k : ℂ) + 1) • sfCre (k + 1) a := by
  rw [sfCre, T_ι, shiftMap_single, one_smul, map_smul]
  rfl

/-- **Every creation operator of level `≥ 1` pushes any state into `O₂SF`.**
Induction on the level: the base case is `sfCre_one_mul_mem_O₂SF`, and the step trades one
level for a translate, `T(χᵃ₋ₖ₋₁ v) = χᵃ₋ₖ₋₁ (T v) + (k+1) χᵃ₋ₖ₋₂ v`, both of whose other
terms are already known to lie in `O₂SF`. -/
theorem sfCre_succ_mul_mem_O₂SF (k : ℕ) (a : Fin 2) (v : FockSF) :
    sfCre (k + 1) a * v ∈ O₂SF := by
  induction k generalizing v with
  | zero => exact sfCre_one_mul_mem_O₂SF a v
  | succ n ih =>
      have hc : ((n : ℂ) + 1 + 1) ≠ 0 := by
        have h : ((n : ℂ) + 1 + 1) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
        rw [h]
        exact_mod_cast Nat.succ_ne_zero (n + 1)
      have hT : ((n : ℂ) + 1 + 1) • (sfCre (n + 1 + 1) a * v)
          = T (sfCre (n + 1) a * v) - sfCre (n + 1) a * T v := by
        rw [T_mul, T_sfCre, smul_mul_assoc, add_sub_cancel_left]
        congr 1
        push_cast
        ring
      have hmem : ((n : ℂ) + 1 + 1) • (sfCre (n + 1 + 1) a * v) ∈ O₂SF := by
        rw [hT]
        exact Submodule.sub_mem _ (T_mem_O₂SF _) (ih (T v))
      have h2 := Submodule.smul_mem O₂SF ((n : ℂ) + 1 + 1)⁻¹ hmem
      rwa [inv_smul_smul₀ hc] at h2

/-- The same statement with the hypothesis in the form `1 ≤ k`. -/
theorem sfCre_mul_mem_O₂SF {k : ℕ} (hk : 1 ≤ k) (a : Fin 2) (v : FockSF) :
    sfCre k a * v ∈ O₂SF := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact sfCre_succ_mul_mem_O₂SF n a v

/-! ## §3  The exterior-algebra bookkeeping -/

/-- Generators anticommute (the quadratic form is `0`): `χᵃ₋ⱼ₋₁(χᵇ₋ₖ₋₁ v) = -χᵇ₋ₖ₋₁(χᵃ₋ⱼ₋₁ v)`. -/
theorem sfCre_mul_sfCre_swap (j k : ℕ) (a b : Fin 2) (v : FockSF) :
    sfCre j a * (sfCre k b * v) = -(sfCre k b * (sfCre j a * v)) := by
  have h : sfCre j a * (sfCre k b * v) + sfCre k b * (sfCre j a * v) = 0 :=
    creBase_anticomm ((j, a) : ℕ × Fin 2) ((k, b) : ℕ × Fin 2) v
  rw [eq_neg_iff_add_eq_zero]
  exact h

/-- The same, without a trailing state. -/
theorem sfCre_mul_swap (j k : ℕ) (a b : Fin 2) :
    sfCre j a * sfCre k b = -(sfCre k b * sfCre j a) := by
  have h := sfCre_mul_sfCre_swap j k a b 1
  rwa [mul_one, mul_one] at h

/-- A generator squares to zero. -/
theorem sfCre_sq (k : ℕ) (a : Fin 2) : sfCre k a * sfCre k a = 0 := by
  rw [sfCre, ι_sq_scalar]
  have hQ : QSF (Finsupp.single ((k, a) : ℕ × Fin 2) (1 : ℂ)) = 0 := rfl
  rw [hQ, map_zero]

/-- The span of the states obtained by applying **one creation operator of level `≥ 1`** to an
arbitrary state.  This is the piece of `O₂SF` that the word induction actually consumes; it is
strictly smaller than `O₂SF`, and (unlike `O₂SF`) it is visibly stable under left multiplication
by a weight-one generator, which is what makes the induction close. -/
noncomputable def sfHigh : Submodule ℂ FockSF :=
  Submodule.span ℂ {x | ∃ (k : ℕ) (a : Fin 2) (v : FockSF), 1 ≤ k ∧ x = sfCre k a * v}

theorem sfHigh_def :
    sfHigh = Submodule.span ℂ {x | ∃ (k : ℕ) (a : Fin 2) (v : FockSF), 1 ≤ k ∧ x = sfCre k a * v} :=
  rfl

/-- `sfHigh ⊆ O₂SF` — the content of §2. -/
theorem sfHigh_le_O₂SF : sfHigh ≤ O₂SF := by
  rw [sfHigh_def, Submodule.span_le]
  rintro _ ⟨k, a, v, hk, rfl⟩
  exact sfCre_mul_mem_O₂SF hk a v

/-- **The exhibited finite spanning set**: the four states
`|0⟩, χ⁰₋₁|0⟩, χ¹₋₁|0⟩, χ⁰₋₁χ¹₋₁|0⟩` — the exterior algebra on the two weight-one modes. -/
noncomputable def sfBottomSet : Set FockSF :=
  {1, sfCre 0 0, sfCre 0 1, sfCre 0 0 * sfCre 0 1}

theorem sfBottomSet_finite : sfBottomSet.Finite := by
  rw [sfBottomSet]
  exact (((Set.finite_singleton _).insert _).insert _).insert _

/-- The span of the four bottom states. -/
noncomputable def sfBottom : Submodule ℂ FockSF := Submodule.span ℂ sfBottomSet

theorem sfBottom_def : sfBottom = Submodule.span ℂ sfBottomSet := rfl

theorem one_mem_sfBottom : (1 : FockSF) ∈ sfBottom :=
  Submodule.subset_span (by simp [sfBottomSet])

theorem sfCre_zero_mem_sfBottom (a : Fin 2) : sfCre 0 a ∈ sfBottom := by
  refine Submodule.subset_span ?_
  rcases sfFin2_cases a with rfl | rfl <;> simp [sfBottomSet]

/-- **The bottom span is stable under left multiplication by a weight-one generator.**
Eight small exterior-algebra computations: everything either lands back in the four-element
set, or dies because a generator is repeated. -/
theorem sfBottom_mul_closed (a : Fin 2) {y : FockSF} (hy : y ∈ sfBottom) :
    sfCre 0 a * y ∈ sfBottom := by
  rw [sfBottom_def] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      simp only [sfBottomSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · rw [mul_one]; exact sfCre_zero_mem_sfBottom a
      · rcases sfFin2_cases a with rfl | rfl
        · rw [sfCre_sq]; exact Submodule.zero_mem _
        · rw [sfCre_mul_swap]
          exact Submodule.neg_mem _ (Submodule.subset_span (by simp [sfBottomSet]))
      · rcases sfFin2_cases a with rfl | rfl
        · exact Submodule.subset_span (by simp [sfBottomSet])
        · rw [sfCre_sq]; exact Submodule.zero_mem _
      · rcases sfFin2_cases a with rfl | rfl
        · rw [← mul_assoc, sfCre_sq, zero_mul]; exact Submodule.zero_mem _
        · rw [sfCre_mul_sfCre_swap, sfCre_sq, mul_zero, neg_zero]
          exact Submodule.zero_mem _
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

/-- **`sfHigh` is stable under left multiplication by a weight-one generator** — by
anticommutation, which moves the level-`≥ 1` operator back to the front at the cost of a sign. -/
theorem sfHigh_mul_closed (a : Fin 2) {y : FockSF} (hy : y ∈ sfHigh) :
    sfCre 0 a * y ∈ sfHigh := by
  rw [sfHigh_def] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨k, b, v, hk, rfl⟩ := hz
      rw [sfCre_mul_sfCre_swap]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨k, b, sfCre 0 a * v, hk, rfl⟩)
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

/-! ## §4  Every creation word is a bottom state modulo `O₂SF` -/

/-- **The key induction.**  Peeling the *leftmost* creation operator off a word:
if its level is `≥ 1` the whole word is already in `sfHigh`, and if its level is `0` the two
stability lemmas of §3 propagate the inductive hypothesis. -/
theorem stWordSF_mem_sup (l : SFWord) : stWordSF l ∈ sfBottom ⊔ sfHigh := by
  induction l with
  | nil =>
      rw [stWordSF_nil]
      exact Submodule.mem_sup_left one_mem_sfBottom
  | cons p rest ih =>
      obtain ⟨k, a⟩ := p
      have hcons : stWordSF ((k, a) :: rest) = sfCre k a * stWordSF rest := rfl
      rw [hcons]
      cases k with
      | zero =>
          obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp ih
          rw [← hyz, mul_add]
          exact Submodule.add_mem _ (Submodule.mem_sup_left (sfBottom_mul_closed a hy))
            (Submodule.mem_sup_right (sfHigh_mul_closed a hz))
      | succ n =>
          exact Submodule.mem_sup_right
            (Submodule.subset_span ⟨n + 1, a, stWordSF rest, by omega, rfl⟩)

/-- The four bottom states together with `sfHigh` exhaust `FockSF`. -/
theorem sfBottom_sup_sfHigh_eq_top : sfBottom ⊔ sfHigh = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← stWordSF_span, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact stWordSF_mem_sup l

/-- **The four bottom states together with `O₂SF` exhaust `FockSF`.** -/
theorem sfBottom_sup_O₂SF_eq_top : sfBottom ⊔ O₂SF = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← sfBottom_sup_sfHigh_eq_top]
  exact sup_le_sup_left sfHigh_le_O₂SF sfBottom

/-! ## §5  `A₂SF` is finite-dimensional -/

/-- The image of the bottom span in the `C₂` quotient is everything. -/
theorem map_mkQ_sfBottom_eq_top : sfBottom.map O₂SF.mkQ = ⊤ := by
  refine eq_top_iff.mpr fun q _ => ?_
  obtain ⟨x, rfl⟩ := (O₂SF.mkQ_surjective) q
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp
    (by rw [sfBottom_sup_O₂SF_eq_top]; trivial : x ∈ sfBottom ⊔ O₂SF)
  have hz0 : O₂SF.mkQ z = 0 := (Submodule.Quotient.mk_eq_zero O₂SF).mpr hz
  rw [map_add, hz0, add_zero]
  exact Submodule.mem_map_of_mem hy

/-- **The exhibited finite spanning set of the `C₂` quotient**: the classes of
`|0⟩, χ⁰₋₁|0⟩, χ¹₋₁|0⟩, χ⁰₋₁χ¹₋₁|0⟩`. -/
theorem A₂SF_span : Submodule.span ℂ (O₂SF.mkQ '' sfBottomSet) = (⊤ : Submodule ℂ A₂SF) := by
  rw [Submodule.span_image, ← sfBottom_def]
  exact map_mkQ_sfBottom_eq_top

/-- **The `C₂` quotient of the symplectic fermions is finite-dimensional.** -/
theorem A₂SF_finiteDimensional : FiniteDimensional ℂ A₂SF :=
  Module.finite_def.mpr
    (Submodule.fg_def.mpr ⟨_, sfBottomSet_finite.image _, A₂SF_span⟩)

/-- **The dimension bound `dim A₂(SF) ≤ 4`** — the exterior algebra on the two weight-one
modes.  Only an upper bound is claimed: no basis and no exact dimension are computed, and none
is needed for `C₂`-cofiniteness. -/
theorem finrank_A₂SF_le_four : Module.finrank ℂ A₂SF ≤ 4 := by
  classical
  have hcoe : ((({O₂SF.mkQ 1, O₂SF.mkQ (sfCre 0 0), O₂SF.mkQ (sfCre 0 1),
      O₂SF.mkQ (sfCre 0 0 * sfCre 0 1)} : Finset A₂SF) : Set A₂SF))
        = O₂SF.mkQ '' sfBottomSet := by
    simp [sfBottomSet, Set.image_insert_eq]
  have hspan : Submodule.span ℂ ((({O₂SF.mkQ 1, O₂SF.mkQ (sfCre 0 0), O₂SF.mkQ (sfCre 0 1),
      O₂SF.mkQ (sfCre 0 0 * sfCre 0 1)} : Finset A₂SF) : Set A₂SF)) = ⊤ := by
    rw [hcoe]; exact A₂SF_span
  have hcard : (({O₂SF.mkQ 1, O₂SF.mkQ (sfCre 0 0), O₂SF.mkQ (sfCre 0 1),
      O₂SF.mkQ (sfCre 0 0 * sfCre 0 1)} : Finset A₂SF)).card ≤ 4 := by
    have a1 := Finset.card_insert_le (O₂SF.mkQ 1)
      ({O₂SF.mkQ (sfCre 0 0), O₂SF.mkQ (sfCre 0 1),
        O₂SF.mkQ (sfCre 0 0 * sfCre 0 1)} : Finset A₂SF)
    have a2 := Finset.card_insert_le (O₂SF.mkQ (sfCre 0 0))
      ({O₂SF.mkQ (sfCre 0 1), O₂SF.mkQ (sfCre 0 0 * sfCre 0 1)} : Finset A₂SF)
    have a3 := Finset.card_insert_le (O₂SF.mkQ (sfCre 0 1))
      ({O₂SF.mkQ (sfCre 0 0 * sfCre 0 1)} : Finset A₂SF)
    have a4 : (({O₂SF.mkQ (sfCre 0 0 * sfCre 0 1)} : Finset A₂SF)).card = 1 :=
      Finset.card_singleton _
    omega
  have hle : Module.finrank ℂ
      (Submodule.span ℂ ((({O₂SF.mkQ 1, O₂SF.mkQ (sfCre 0 0), O₂SF.mkQ (sfCre 0 1),
        O₂SF.mkQ (sfCre 0 0 * sfCre 0 1)} : Finset A₂SF) : Set A₂SF)))
      ≤ (({O₂SF.mkQ 1, O₂SF.mkQ (sfCre 0 0), O₂SF.mkQ (sfCre 0 1),
        O₂SF.mkQ (sfCre 0 0 * sfCre 0 1)} : Finset A₂SF)).card :=
    finrank_span_finset_le_card (R := ℂ) _
  rw [hspan, finrank_top] at hle
  omega

end VOA.SympFerm
