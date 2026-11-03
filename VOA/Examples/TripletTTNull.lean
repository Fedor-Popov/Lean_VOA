/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.TripletW2
import VOA.Modules.C2Cofinite

/-!
# The level-4 null relation in `W(2)`: `ω₍₋₁₎ω` is **not** a translate

**Answer: negative.**  `:TT:` is *not* a linear combination of the `∂W^a`, and `[ω]² ≠ 0`
in the Poisson algebra `A₂(W(2))`.

## The question

`W(2) = (FockSF)₀̄` is the even part of the symplectic fermions (`Examples.TripletW2`).  Its
strong generators are the conformal vector `ω` (weight `2`) and a weight-`3` triplet
`W⁺, W⁰, W⁻`.  The nilpotency route to `C₂`-cofiniteness wants `[ω]` nilpotent in
`R_{W(2)} = W(2)/C₂(W(2))`, and the cheapest possible statement is `[ω]² = 0`, i.e.

`ω₍₋₁₎ω ∈ O₂(W(2))`.

Weight bookkeeping (verified here, not assumed): `wt(a₍₋₂₎b) = wt a + wt b + 1`
(`PreVertexAlgebra.smul_mem_grading` at `n = -2`), the weights of `W(2)` are `0, 2, 3, 4, …`
(`tripletW2_grading_one : W(2)₁ = ⊥`, and `W(2)₀ = ℂ|0⟩`), so the weight-`4` part of `O₂` comes
only from the splits `(0,3)` and `(3,0)` of `3`; the first vanishes (`𝟙₍₋₂₎v = 0`) and the second
is `a₍₋₂₎𝟙 = L₋₁a`.  Hence

`O₂(W(2))₄ = L₋₁(W(2)₃)`,

and `W(2)₃` is **`4`**-dimensional, not `3`: it is `span{W⁺, W⁰, W⁻} ⊕ ℂ·L₋₁ω`.  (The
symmetric/antisymmetric split of the two-letter words `χᵃ₋₁χᵇ₋₂|0⟩`; the *anti*symmetric
combination is `L₋₁ω`, `T_omega` below.)

## Convention

`FormalDist` is indexed by the `z`-exponent, `mode a m = a (-m-1)`, and
`stWordSF [(k₁,a₁), …, (kₙ,aₙ)] = χ^{a₁}_{-k₁-1} ⋯ χ^{aₙ}_{-kₙ-1}|0⟩`.  So a letter `(k,a)`
is the creation mode `χᵃ_{-k-1}`, of conformal weight `k+1`, and `ωSF = -χ⁰₋₁χ¹₋₁|0⟩`.

## The computation

In the weight-`4` word basis `e := χ⁰₋₂χ¹₋₂|0⟩ = stWordSF [(1,0),(1,1)]` and
`w_{ab} := χᵃ₋₁χᵇ₋₃|0⟩ = stWordSF [(0,a),(2,b)]`:

* `ω₍₋₁₎ω = w₁₀ - w₀₁` (`omega_poissonMul_omega`),
* `L₋₁W⁺ = 2w₀₀`, `L₋₁W⁻ = 2w₁₁`, `L₋₁W⁰ = 2(w₀₁ + w₁₀)`, `L₋₁²ω = -2e + 2(w₁₀ - w₀₁)`.

`ω₍₋₁₎ω` is the **antisymmetric** combination and every translate is **symmetric** (in `e` and
in `w₀₁ ↔ w₁₀` jointly), so the relation fails — by a single explicit functional.

## Why the "`T = λ₁λ₂`, so `T² = 0`" argument does not apply

In the ambient `R_SF` one has `χ⁰₋₂χ¹₋₂|0⟩ = (χ⁰₋₁|0⟩)₍₋₂₎(χ¹₋₂|0⟩) ∈ O₂(SF)`, but the state
`χ⁰₋₁|0⟩` is **odd**, hence not in `W(2)`.  That single generator is exactly what is lost on
passing to the even part, and exactly what `T² = 0` would have needed.

## Main results

* `augSF`, `wordCoeff` — an augmentation `ε : FockSF →ₐ[ℂ] ℂ` (free of charge: `QSF = 0`) and the
  two-letter coefficient functionals `⟨p q | ·⟩ = ε ∘ (ι_q ⌋) ∘ (ι_p ⌋)` it generates, with
  `⟨p q | r s⟩ = δ_{pr}δ_{qs} - δ_{ps}δ_{qr}`.  This is the separating device the
  symplectic-fermion chain did not have: `Examples.SymplecticFermionGrading` deliberately avoids
  building a basis, so no *negative* statement about `FockSF` was reachable before.
* `WplusSF`, `WzeroSF`, `WminusSF` (and `Wplus`, `Wzero`, `Wminus` as states of `W(2)`) — the
  weight-`3` triplet generators, **constructed here for the first time**; they did not exist
  anywhere in the repository.  With `Wplus_mem_grading` etc. (weight `3`), `Wplus_ne_zero` etc.
  (non-degeneracy) and `LSF_one_WplusSF`, `LSF_one_WzeroSF`, `LSF_one_WminusSF`
  (`L₁W^a = 0`: they are **primary**).
* `LSF_one_T_omega : L₁L₋₁ω = 4ω` — the fourth weight-`3` direction is *not* primary, and this
  value is exactly what `[L₁,L₋₁] = 2L₀`, `L₀ω = 2ω` demand: an independent Virasoro check of the
  sign conventions used in the whole file.
* `triplet_and_descendant_indep` — `W⁺, W⁰, W⁻, L₋₁ω` are linearly independent, so
  `dim W(2)₃ ≥ 4` (it is exactly `4`).
* `omega_poissonMul_omega` — `ω₍₋₁₎ω = -χ⁰₋₃χ¹₋₁|0⟩ - χ⁰₋₁χ¹₋₃|0⟩`, and
  `omega_poissonMul_omega_basis` — `ω₍₋₁₎ω = w₁₀ - w₀₁`.
* `T_WplusSF`, `T_WzeroSF`, `T_WminusSF`, `T_T_omega` — the four translates spanning
  `O₂(W(2))₄`.
* `sepF` — the separating functional `F = 2⟨(1,0)(1,1)| + ⟨(0,1)(2,0)| - ⟨(0,0)(2,1)|`, with
  `sepF_of_mem_gradingSF` (it sees conformal weight `4` only) and `sepF_smul_neg_two` (it kills
  every generator of `O₂`).
* `not_exists_omega_sq_eq_translates` / `omega_sq_not_mem_translates` — the decision in the
  exact formulation of the question: `ω₍₋₁₎ω ≠ Σₐ cₐ L₋₁W^a`, and not even with `L₋₁²ω` adjoined.
* `omega_sq_not_mem_T_grading_three` — the basis-free strengthening: `ω₍₋₁₎ω ∉ L₋₁(𝒱₃)`
  for the **whole** weight-`3` space of the ambient Fock space, odd states included.
* `omega_sq_not_mem_O₂` and `poissonMul_omega_omega_ne_zero_in_A₂` —
  `ω₍₋₁₎ω ∉ O₂(W(2))`, i.e. **`[ω]² ≠ 0` in `A₂(W(2))`**.

## The explicit data, for an independent check

Convention: `mode a m = a (-m-1)`; a letter `(k,a)` is `χᵃ_{-k-1}`, of weight `k+1`;
`{χᵃ_m, χᵇ_n} = m δ_{m+n,0} ωᵃᵇ` with `ω⁰¹ = 1`; `ω = -χ⁰₋₁χ¹₋₁|0⟩`; `L₋₁ = T`.

Weight `3` (four states, `u_{ab} = χᵃ₋₁χᵇ₋₂|0⟩`):

`W⁺ = u₀₀`,  `W⁰ = u₀₁ + u₁₀`,  `W⁻ = u₁₁`,  `L₋₁ω = u₁₀ - u₀₁`.

Weight `4` (five states, `e = χ⁰₋₂χ¹₋₂|0⟩`, `w_{ab} = χᵃ₋₁χᵇ₋₃|0⟩`):

`L₋₁W⁺ = 2w₀₀`,  `L₋₁W⁰ = 2(w₀₁ + w₁₀)`,  `L₋₁W⁻ = 2w₁₁`,  `L₋₁²ω = -2e + 2(w₁₀ - w₀₁)`,

`ω₍₋₁₎ω = w₁₀ - w₀₁`.

The functional `F(e) = 2, F(w₁₀) = 1, F(w₀₁) = -1, F(w₀₀) = F(w₁₁) = 0` kills all four
translates and gives `F(ω₍₋₁₎ω) = 2`.  Equivalently: `ω₍₋₁₎ω - ½L₋₁²ω = e`, and `e` is not a
translate.  (In the ambient symplectic fermions `e = (χ⁰₋₁|0⟩)₍₋₂₎(χ¹₋₂|0⟩) ∈ O₂(SF)` — but
`χ⁰₋₁|0⟩` is odd.)

## Status

Complete and axiom-clean: no `sorry`, no `admit`, no `native_decide`, no new axioms; the only
axioms used are `propext`, `Classical.choice`, `Quot.sound`.

## Consequence for the nilpotency programme

`T² = 0` is false, so the nilpotency exponent for `ω` in `Modules.NilpotentGenerators` is `≥ 3`.
`T³ ≠ 0` as well: at weight `6` the splits of `5` are `(0,5), (5,0), (2,3), (3,2)`, and
`(3,2) ≡ -(2,3)` modulo `T𝒱` (`poissonMul_sub_swap_mem_O₂`), so `O₂` in weight `6` is
`L₋₁(𝒱₅) + ω₍₋₂₎𝒱₃`.  The first weight at which genuinely new generators appear is `7` (the
split `(3,3)`, i.e. `W^a₍₋₂₎W^b`), so the earliest possible vanishing is `T⁴` at weight `8` —
and that mechanism *requires* the triplet generators constructed here.  **Try `ω⁴` next**,
not `ω²`.  (The `T³ ≠ 0` claim is *not* formalised here; only `T² ≠ 0` is.)

## References
* Kausch, *Symplectic fermions*; Gaberdiel–Kausch; Adamović–Milas on `W(p)`.
* `Modules.C2Cofinite` for `O₂`, `A₂`, `poissonMul`; `Examples.TripletW2` for `W(2)`.
-/

namespace VOA.SympFerm

open VOA CliffordAlgebra

/-! ## §1  An augmentation on `FockSF`

`QSF = 0`, so `FockSF` is the exterior algebra and the zero map on generators lifts to an
algebra map `ε : FockSF → ℂ`.  It kills every nonempty word, which is all we need. -/

/-- **The augmentation** `ε : FockSF →ₐ[ℂ] ℂ`, `ε(1) = 1`, `ε(χᵃ_{-k-1} ⋯) = 0`.  Free of
charge because the quadratic form is zero. -/
noncomputable def augSF : FockSF →ₐ[ℂ] ℂ :=
  CliffordAlgebra.lift QSF ⟨0, by intro m; simp⟩

/-- `ε` kills the generators. -/
@[simp] theorem augSF_ι (v : SFModes) : augSF (ι QSF v) = 0 := by
  rw [augSF, CliffordAlgebra.lift_ι_apply]
  rfl

/-- `ε(1) = 1`. -/
@[simp] theorem augSF_one : augSF (1 : FockSF) = 1 := map_one _

attribute [irreducible] augSF

/-- `ε` kills anything with a creation operator in front. -/
theorem augSF_creBase (p : ℕ × Fin 2) (x : FockSF) : augSF (creBase p x) = 0 := by
  rw [creBase, LinearMap.mulLeft_apply, map_mul, augSF_ι, zero_mul]

/-- `ε` kills every nonempty word state. -/
theorem augSF_stWordSF {l : SFWord} (hl : l ≠ []) : augSF (stWordSF l) = 0 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons p rest => rw [stWordSF_cons, map_mul, augSF_ι, zero_mul]

/-! ## §2  Words: the two-letter calculus

`stWordSF [p,q] = χ^{p}χ^{q}|0⟩` with the two Clifford generators multiplied out. -/

/-- A generator squares to zero (`QSF = 0`). -/
theorem sfGen_sq (p : ℕ × Fin 2) :
    ι QSF (Finsupp.single p (1 : ℂ)) * ι QSF (Finsupp.single p (1 : ℂ)) = 0 := by
  rw [ι_sq_scalar]
  change (algebraMap ℂ FockSF) (0 : ℂ) = 0
  rw [map_zero]

/-- Two generators anticommute (`QSF = 0`, so the polar form vanishes too). -/
theorem sfGen_swap (p q : ℕ × Fin 2) :
    ι QSF (Finsupp.single p (1 : ℂ)) * ι QSF (Finsupp.single q (1 : ℂ))
      = -(ι QSF (Finsupp.single q (1 : ℂ)) * ι QSF (Finsupp.single p (1 : ℂ))) := by
  have h := ι_mul_ι_add_swap (Q := QSF) (Finsupp.single p (1 : ℂ)) (Finsupp.single q (1 : ℂ))
  rw [show (algebraMap ℂ FockSF) (QuadraticMap.polar (⇑QSF) (Finsupp.single p (1 : ℂ))
      (Finsupp.single q (1 : ℂ))) = 0 by
    rw [show QuadraticMap.polar (⇑QSF) (Finsupp.single p (1 : ℂ)) (Finsupp.single q (1 : ℂ)) = 0 by
      rw [QuadraticMap.polar]; simp, map_zero]] at h
  linear_combination (norm := module) h

/-- A two-letter word is the product of its two generators. -/
theorem stWordSF_pair (p q : ℕ × Fin 2) :
    stWordSF [p, q] = ι QSF (Finsupp.single p (1 : ℂ)) * ι QSF (Finsupp.single q (1 : ℂ)) := by
  rw [stWordSF_cons, stWordSF_cons, stWordSF_nil, mul_one]

/-- Swapping the two letters of a word flips the sign. -/
theorem stWordSF_pair_swap (p q : ℕ × Fin 2) : stWordSF [p, q] = -stWordSF [q, p] := by
  rw [stWordSF_pair, stWordSF_pair, sfGen_swap]

/-- A repeated letter kills the word: `(χᵃ_{-k-1})² = 0`. -/
@[simp] theorem stWordSF_pair_self (p : ℕ × Fin 2) : stWordSF [p, p] = 0 := by
  rw [stWordSF_pair, sfGen_sq]

/-! ## §3  Contraction and the coefficient functionals

`annBase p` is contraction against the coordinate functional at `p` — the derivation dual to
the generator `p`.  Two contractions followed by `ε` read off the coefficient of a two-letter
word, which is the separating device this file is built on. -/

/-- Contraction kills the unit. -/
@[simp] theorem annBase_one (p : ℕ × Fin 2) : annBase p (1 : FockSF) = 0 := by
  rw [annBase]
  exact contractLeft_one QSF _

/-- A one-letter word is its generator. -/
theorem stWordSF_single (q : ℕ × Fin 2) :
    stWordSF [q] = ι QSF (Finsupp.single q (1 : ℂ)) := by
  rw [stWordSF_cons, stWordSF_nil, mul_one]

/-- Contraction of a one-letter word.  (The recursion `annBase_stWordSF_cons` is already in
`Examples.SymplecticFermionInstance`.) -/
theorem annBase_stWordSF_single (p q : ℕ × Fin 2) :
    annBase p (stWordSF [q]) = (if p = q then (1 : ℂ) else 0) • (1 : FockSF) := by
  rw [annBase_stWordSF_cons, annBase_stWordSF_nil, mul_zero, sub_zero, stWordSF_nil]

/-- Contraction of a two-letter word. -/
theorem annBase_stWordSF_pair (p q r : ℕ × Fin 2) :
    annBase p (stWordSF [q, r])
      = (if p = q then (1 : ℂ) else 0) • stWordSF [r]
        - (if p = r then (1 : ℂ) else 0) • stWordSF [q] := by
  rw [annBase_stWordSF_cons, annBase_stWordSF_single, mul_smul_comm, mul_one,
    stWordSF_single q]

/-- **The two-letter coefficient functional** `⟨p q | · ⟩ := ε ∘ (ι_q ⌋) ∘ (ι_p ⌋)`.
On words it is `⟨p q | r s⟩ = δ_{pr}δ_{qs} - δ_{ps}δ_{qr}`. -/
noncomputable def wordCoeff (p q : ℕ × Fin 2) : FockSF →ₗ[ℂ] ℂ :=
  augSF.toLinearMap ∘ₗ (annBase q) ∘ₗ (annBase p)

theorem wordCoeff_apply (p q : ℕ × Fin 2) (x : FockSF) :
    wordCoeff p q x = augSF (annBase q (annBase p x)) := rfl

@[simp] theorem wordCoeff_one (p q : ℕ × Fin 2) : wordCoeff p q (1 : FockSF) = 0 := by
  rw [wordCoeff_apply, annBase_one, map_zero, map_zero]

@[simp] theorem wordCoeff_stWordSF_nil (p q : ℕ × Fin 2) : wordCoeff p q (stWordSF []) = 0 := by
  rw [stWordSF_nil, wordCoeff_one]

@[simp] theorem wordCoeff_stWordSF_single (p q r : ℕ × Fin 2) :
    wordCoeff p q (stWordSF [r]) = 0 := by
  rw [wordCoeff_apply, annBase_stWordSF_single, map_smul, annBase_one, smul_zero, map_zero]

/-- The defining evaluation: `⟨p q | r s⟩ = δ_{pr}δ_{qs} - δ_{ps}δ_{qr}`. -/
theorem wordCoeff_stWordSF_pair (p q r s : ℕ × Fin 2) :
    wordCoeff p q (stWordSF [r, s])
      = (if p = r then (1 : ℂ) else 0) * (if q = s then (1 : ℂ) else 0)
        - (if p = s then (1 : ℂ) else 0) * (if q = r then (1 : ℂ) else 0) := by
  rw [wordCoeff_apply, annBase_stWordSF_pair]
  simp only [map_sub, map_smul, annBase_stWordSF_single, smul_eq_mul, augSF_one, mul_one,
    smul_smul]

/-- `ε ∘ (ι_q ⌋)` kills anything of the form `χ_r · x` with `ε x = 0`. -/
theorem augSF_annBase_ι_mul (q r : ℕ × Fin 2) {x : FockSF} (hx : augSF x = 0) :
    augSF (annBase q (ι QSF (Finsupp.single r (1 : ℂ)) * x)) = 0 := by
  rw [annBase, contractLeft_ι_mul, map_sub, map_smul, hx, smul_zero, map_mul, augSF_ι,
    zero_mul, sub_zero]

/-- `ε ∘ (ι_q ⌋)` kills every word of length `≥ 2`. -/
theorem augSF_annBase_stWordSF (q r : ℕ × Fin 2) {rest : SFWord} (hrest : rest ≠ []) :
    augSF (annBase q (stWordSF (r :: rest))) = 0 := by
  rw [annBase_stWordSF_cons, map_sub, map_smul, augSF_stWordSF hrest, smul_zero, zero_sub,
    map_mul, augSF_ι, zero_mul, neg_zero]

/-- The coefficient functionals kill every word of length `≥ 3` — they see two-letter words
only.  (Together with `wordCoeff_stWordSF_nil` and `wordCoeff_stWordSF_single`: they see
*exactly* the two-letter words.) -/
theorem wordCoeff_stWordSF_long (p q r s : ℕ × Fin 2) {rest : SFWord} (hrest : rest ≠ []) :
    wordCoeff p q (stWordSF (r :: s :: rest)) = 0 := by
  rw [wordCoeff_apply, annBase_stWordSF_cons, map_sub, map_smul, map_sub, map_smul,
    augSF_annBase_stWordSF q s hrest, smul_zero, zero_sub,
    augSF_annBase_ι_mul q r (augSF_annBase_stWordSF p s hrest), neg_zero]

/-! ## §4  The separating functional

`F := 2⟨(1,0)(1,1)| + ⟨(0,1)(2,0)| - ⟨(0,0)(2,1)|`, i.e. in the weight-`4` basis
`e, w₀₀, w₀₁, w₁₀, w₁₁`,

`F(e) = 2`,  `F(w₁₀) = 1`,  `F(w₀₁) = -1`,  `F(w₀₀) = F(w₁₁) = 0`. -/

/-- **The separating functional.**  It annihilates every translate `L₋₁(𝒱₃)` and takes the
value `2` on `ω₍₋₁₎ω`. -/
noncomputable def sepF : FockSF →ₗ[ℂ] ℂ :=
  (2 : ℂ) • wordCoeff (1, 0) (1, 1) + wordCoeff (0, 1) (2, 0) - wordCoeff (0, 0) (2, 1)

theorem sepF_apply (x : FockSF) :
    sepF x = 2 * wordCoeff (1, 0) (1, 1) x + wordCoeff (0, 1) (2, 0) x
      - wordCoeff (0, 0) (2, 1) x := by
  simp only [sepF, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

/-- `F` on a two-letter word, fully expanded. -/
theorem sepF_stWordSF_pair (r s : ℕ × Fin 2) :
    sepF (stWordSF [r, s])
      = 2 * ((if ((1 : ℕ), (0 : Fin 2)) = r then (1 : ℂ) else 0)
              * (if ((1 : ℕ), (1 : Fin 2)) = s then (1 : ℂ) else 0)
            - (if ((1 : ℕ), (0 : Fin 2)) = s then (1 : ℂ) else 0)
              * (if ((1 : ℕ), (1 : Fin 2)) = r then (1 : ℂ) else 0))
        + ((if ((0 : ℕ), (1 : Fin 2)) = r then (1 : ℂ) else 0)
              * (if ((2 : ℕ), (0 : Fin 2)) = s then (1 : ℂ) else 0)
            - (if ((0 : ℕ), (1 : Fin 2)) = s then (1 : ℂ) else 0)
              * (if ((2 : ℕ), (0 : Fin 2)) = r then (1 : ℂ) else 0))
        - ((if ((0 : ℕ), (0 : Fin 2)) = r then (1 : ℂ) else 0)
              * (if ((2 : ℕ), (1 : Fin 2)) = s then (1 : ℂ) else 0)
            - (if ((0 : ℕ), (0 : Fin 2)) = s then (1 : ℂ) else 0)
              * (if ((2 : ℕ), (1 : Fin 2)) = r then (1 : ℂ) else 0)) := by
  rw [sepF_apply, wordCoeff_stWordSF_pair, wordCoeff_stWordSF_pair, wordCoeff_stWordSF_pair]

/-- `F` kills words of length `≠ 2`. -/
theorem sepF_stWordSF_long (r s : ℕ × Fin 2) {rest : SFWord} (hrest : rest ≠ []) :
    sepF (stWordSF (r :: s :: rest)) = 0 := by
  rw [sepF_apply, wordCoeff_stWordSF_long _ _ _ _ hrest, wordCoeff_stWordSF_long _ _ _ _ hrest,
    wordCoeff_stWordSF_long _ _ _ _ hrest]
  ring

@[simp] theorem sepF_stWordSF_nil : sepF (stWordSF []) = 0 := by
  rw [sepF_apply, wordCoeff_stWordSF_nil, wordCoeff_stWordSF_nil, wordCoeff_stWordSF_nil]
  ring

@[simp] theorem sepF_stWordSF_single (r : ℕ × Fin 2) : sepF (stWordSF [r]) = 0 := by
  rw [sepF_apply, wordCoeff_stWordSF_single, wordCoeff_stWordSF_single,
    wordCoeff_stWordSF_single]
  ring

/-! ## §5  The translation operator on two-letter words -/

/-- `L₋₁ = T` on a two-letter word: the Leibniz rule for the mode shift
`χᵃ_{-k-1} ↦ (k+1)χᵃ_{-k-2}`. -/
theorem T_stWordSF_two (p q : ℕ × Fin 2) :
    T (stWordSF [p, q])
      = ((p.1 : ℂ) + 1) • stWordSF [(p.1 + 1, p.2), q]
        + ((q.1 : ℂ) + 1) • stWordSF [p, (q.1 + 1, q.2)] := by
  simp only [stWordSF_pair, T_mul, T_ι, shiftMap_single, one_smul, map_smul, smul_mul_assoc,
    mul_smul_comm]
  abel

/-- `L₋₁ = T` on a one-letter word. -/
theorem T_stWordSF_single (p : ℕ × Fin 2) :
    T (stWordSF [p]) = ((p.1 : ℂ) + 1) • stWordSF [(p.1 + 1, p.2)] := by
  rw [stWordSF_single, T_ι, shiftMap_single, one_smul, map_smul, stWordSF_single]

/-- `L₋₁ = T` on a three-letter word. -/
theorem T_stWordSF_triple (p q r : ℕ × Fin 2) :
    T (stWordSF [p, q, r])
      = ((p.1 : ℂ) + 1) • stWordSF [(p.1 + 1, p.2), q, r]
        + ((q.1 : ℂ) + 1) • stWordSF [p, (q.1 + 1, q.2), r]
        + ((r.1 : ℂ) + 1) • stWordSF [p, q, (r.1 + 1, r.2)] := by
  simp only [stWordSF_cons, stWordSF_nil, mul_one, T_mul, T_ι, shiftMap_single, one_smul,
    map_smul, mul_add, smul_mul_assoc, mul_smul_comm]
  abel

/-! ## §6  The weight-`3` triplet generators of `W(2)`

⚠ These did not exist anywhere in the repository (`Examples.TripletWp.Etrip` is a *lattice*
state of a different model, and even its non-vanishing is open there).  They are constructed
here.

`W(2)₃` is spanned by the four two-letter words `u_{ab} := χᵃ₋₁χᵇ₋₂|0⟩`, and splits as

* the **triplet** `W⁺ = u₀₀`, `W⁰ = u₀₁ + u₁₀`, `W⁻ = u₁₁` (the symmetric part), and
* `ℂ·L₋₁ω`, the **antisymmetric** part: `L₋₁ω = u₁₀ - u₀₁` (`T_omega`).

The split is the `𝔰𝔩₂ = 𝔰𝔭(2)` decomposition on the species index: the symplectic form is
antisymmetric, so the invariant (singlet) direction is the antisymmetric one, and that is the
descendant `L₋₁ω`, leaving the symmetric part as the genuine weight-`3` primaries. -/

/-- The four weight-`3` two-letter states `u_{ab} = χᵃ₋₁χᵇ₋₂|0⟩`. -/
noncomputable def sfWgen (a b : Fin 2) : FockSF := stWordSF [((0 : ℕ), a), ((1 : ℕ), b)]

/-- `W⁺ = χ⁰₋₁χ⁰₋₂|0⟩`. -/
noncomputable def WplusSF : FockSF := sfWgen 0 0

/-- `W⁰ = χ⁰₋₁χ¹₋₂|0⟩ + χ¹₋₁χ⁰₋₂|0⟩` (the symmetric combination). -/
noncomputable def WzeroSF : FockSF := sfWgen 0 1 + sfWgen 1 0

/-- `W⁻ = χ¹₋₁χ¹₋₂|0⟩`. -/
noncomputable def WminusSF : FockSF := sfWgen 1 1

/-- Each `u_{ab}` has conformal weight `3`. -/
theorem sfWgen_mem_gradingSF (a b : Fin 2) : sfWgen a b ∈ gradingSF 3 := by
  have h := stWordSF_mem_gradingSF [((0 : ℕ), a), ((1 : ℕ), b)]
  rwa [show sfWeight [((0 : ℕ), a), ((1 : ℕ), b)] = 3 from rfl, Nat.cast_ofNat] at h

/-- Each `u_{ab}` is even (a two-letter word), hence lies in `W(2)`. -/
theorem sfWgen_mem_evenPart (a b : Fin 2) : sfWgen a b ∈ evenOdd QSF (0 : ZMod 2) :=
  stWordSF_mem_evenPart (l := [((0 : ℕ), a), ((1 : ℕ), b)]) ⟨1, rfl⟩

/-- `W⁺` as a state of `W(2)`. -/
noncomputable def Wplus : evenOdd QSF (0 : ZMod 2) := ⟨WplusSF, sfWgen_mem_evenPart 0 0⟩

/-- `W⁰` as a state of `W(2)`. -/
noncomputable def Wzero : evenOdd QSF (0 : ZMod 2) :=
  ⟨WzeroSF, Submodule.add_mem _ (sfWgen_mem_evenPart 0 1) (sfWgen_mem_evenPart 1 0)⟩

/-- `W⁻` as a state of `W(2)`. -/
noncomputable def Wminus : evenOdd QSF (0 : ZMod 2) := ⟨WminusSF, sfWgen_mem_evenPart 1 1⟩

@[simp] theorem Wplus_coe : ((Wplus : evenOdd QSF 0) : FockSF) = WplusSF := rfl
@[simp] theorem Wzero_coe : ((Wzero : evenOdd QSF 0) : FockSF) = WzeroSF := rfl
@[simp] theorem Wminus_coe : ((Wminus : evenOdd QSF 0) : FockSF) = WminusSF := rfl

/-- Membership in `gradingSF 3` transfers to the `ℤ`-graded weight-`3` piece of `W(2)`. -/
theorem mem_tripletW2_grading_three {x : evenOdd QSF (0 : ZMod 2)}
    (hx : (x : FockSF) ∈ gradingSF 3) : x ∈ tripletW2.grading 3 := by
  rw [tripletW2_grading]
  refine Submodule.mem_comap.mpr ?_
  rwa [show (((3 : ℤ) : ℂ)) = 3 by norm_num]

/-- `W⁺` has conformal weight `3`. -/
theorem Wplus_mem_grading : Wplus ∈ tripletW2.grading 3 :=
  mem_tripletW2_grading_three (sfWgen_mem_gradingSF 0 0)

/-- `W⁰` has conformal weight `3`. -/
theorem Wzero_mem_grading : Wzero ∈ tripletW2.grading 3 :=
  mem_tripletW2_grading_three
    (Submodule.add_mem _ (sfWgen_mem_gradingSF 0 1) (sfWgen_mem_gradingSF 1 0))

/-- `W⁻` has conformal weight `3`. -/
theorem Wminus_mem_grading : Wminus ∈ tripletW2.grading 3 :=
  mem_tripletW2_grading_three (sfWgen_mem_gradingSF 1 1)

/-! ## §7  `ω₍₋₁₎ω`

The one genuinely dynamical computation: `ω₍₋₁₎ω = L₋₂ω`, evaluated by commuting `L₋₂` past the
two creation modes of `ω` and using `L₋₂|0⟩ = ω`, `χ⁰₋₁χ¹₋₁ω = 0`. -/

local notation "gSF" p => ι QSF (Finsupp.single p (1 : ℂ))

/-- `χ⁰₋₁χ¹₋₁ω = 0`: the word `χ⁰₋₁χ¹₋₁χ⁰₋₁χ¹₋₁|0⟩` repeats a mode. -/
theorem chiM_neg_one_omega_ann : chiM 0 (-1) (chiM 1 (-1) ωSF) = 0 := by
  rw [chiM_neg_one, chiM_neg_one, ωSF, stWordSF_pair]
  change (gSF ((0 : ℕ), (0 : Fin 2))) * ((gSF ((0 : ℕ), (1 : Fin 2)))
    * (-((gSF ((0 : ℕ), (0 : Fin 2))) * (gSF ((0 : ℕ), (1 : Fin 2)))))) = 0
  rw [mul_neg, mul_neg, neg_eq_zero, ← mul_assoc, ← mul_assoc,
    mul_assoc (gSF ((0 : ℕ), (0 : Fin 2))) (gSF ((0 : ℕ), (1 : Fin 2)))
      (gSF ((0 : ℕ), (0 : Fin 2))),
    sfGen_swap ((0 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2)), mul_neg, neg_mul, neg_eq_zero,
    ← mul_assoc, sfGen_sq ((0 : ℕ), (0 : Fin 2)), zero_mul, zero_mul]

/-- **`ω₍₋₁₎ω = -χ⁰₋₃χ¹₋₁|0⟩ - χ⁰₋₁χ¹₋₃|0⟩`**, in ordered-word form. -/
theorem omega_poissonMul_omega :
    ((tripletW2.smul tripletW2.conformalVector (-1) tripletW2.conformalVector :
        evenOdd QSF 0) : FockSF)
      = -(stWordSF [(2, 0), (0, 1)]) - stWordSF [(0, 0), (2, 1)] := by
  have hEq : ((tripletW2.smul tripletW2.conformalVector (-1) tripletW2.conformalVector :
      evenOdd QSF 0) : FockSF) = LSF (-2) ωSF := by
    rw [tripletW2_smul_coe, LSF_eq_mode]; norm_num
  have h1 := LSF_comm_chiM_apply (-2) 0 (-1) (chiM 1 (-1) vacSF)
  have h2 := LSF_comm_chiM_apply (-2) 1 (-1) vacSF
  norm_num at h1 h2
  have hw : ωSF = -(chiM 0 (-1) (chiM 1 (-1) vacSF)) := by
    rw [ωSF, chiM_neg_one, chiM_neg_one, show vacSF = stWordSF [] from rfl,
      creBase_stWordSF, creBase_stWordSF]
  have h3 : LSF (-2) ωSF
      = -(chiM 0 (-3) (chiM 1 (-1) vacSF)) - chiM 0 (-1) (chiM 1 (-3) vacSF)
        - chiM 0 (-1) (chiM 1 (-1) (LSF (-2) vacSF)) := by
    rw [hw, map_neg,
      show LSF (-2) (chiM 0 (-1) (chiM 1 (-1) vacSF))
          = chiM 0 (-1) (LSF (-2) (chiM 1 (-1) vacSF)) + chiM 0 (-3) (chiM 1 (-1) vacSF) from by
        linear_combination (norm := module) h1,
      show LSF (-2) (chiM 1 (-1) vacSF) = chiM 1 (-1) (LSF (-2) vacSF) + chiM 1 (-3) vacSF from by
        linear_combination (norm := module) h2]
    simp only [map_add]; module
  have hc3 : (-3 : ℤ) = -((2 : ℕ) : ℤ) - 1 := by norm_num
  rw [hEq, h3, LSF_neg_two_vacuum, chiM_neg_one_omega_ann, sub_zero, hc3, chiM_eq_creBase 0 2,
    chiM_eq_creBase 1 2, chiM_neg_one, chiM_neg_one,
    show vacSF = stWordSF [] from rfl, creBase_stWordSF, creBase_stWordSF, creBase_stWordSF,
    creBase_stWordSF]

/-- `ω₍₋₁₎ω = w₁₀ - w₀₁` in the weight-`4` word basis `w_{ab} = χᵃ₋₁χᵇ₋₃|0⟩`: it is the
**antisymmetric** combination. -/
theorem omega_poissonMul_omega_basis :
    ((tripletW2.smul tripletW2.conformalVector (-1) tripletW2.conformalVector :
        evenOdd QSF 0) : FockSF)
      = stWordSF [((0 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))]
        - stWordSF [((0 : ℕ), (0 : Fin 2)), ((2 : ℕ), (1 : Fin 2))] := by
  rw [omega_poissonMul_omega,
    stWordSF_pair_swap ((2 : ℕ), (0 : Fin 2)) ((0 : ℕ), (1 : Fin 2)), neg_neg]

/-! ## §8  The four translates `L₋₁(𝒱₃)` -/

/-- `L₋₁` on `W(2)` is the symplectic-fermion translation operator. -/
theorem tripletW2_L_neg_one_coe (x : evenOdd QSF 0) :
    ((tripletW2.L (-1) x : evenOdd QSF 0) : FockSF) = T (x : FockSF) := by
  rw [tripletW2_L_coe, LSF_neg_one_eq_T]

/-- `L₋₁u_{ab} = χᵃ₋₂χᵇ₋₂|0⟩ + 2χᵃ₋₁χᵇ₋₃|0⟩`. -/
theorem T_sfWgen (a b : Fin 2) :
    T (sfWgen a b) = stWordSF [((1 : ℕ), a), ((1 : ℕ), b)]
      + (2 : ℂ) • stWordSF [((0 : ℕ), a), ((2 : ℕ), b)] := by
  rw [sfWgen, T_stWordSF_two]
  norm_num

/-- `L₋₁W⁺ = 2w₀₀`. -/
theorem T_WplusSF :
    T WplusSF = (2 : ℂ) • stWordSF [((0 : ℕ), (0 : Fin 2)), ((2 : ℕ), (0 : Fin 2))] := by
  rw [WplusSF, T_sfWgen, stWordSF_pair_self, zero_add]

/-- `L₋₁W⁻ = 2w₁₁`. -/
theorem T_WminusSF :
    T WminusSF = (2 : ℂ) • stWordSF [((0 : ℕ), (1 : Fin 2)), ((2 : ℕ), (1 : Fin 2))] := by
  rw [WminusSF, T_sfWgen, stWordSF_pair_self, zero_add]

/-- `L₋₁W⁰ = 2(w₀₁ + w₁₀)` — the `e = χ⁰₋₂χ¹₋₂|0⟩` terms cancel, because `W⁰` is the
symmetric combination. -/
theorem T_WzeroSF :
    T WzeroSF = (2 : ℂ) • stWordSF [((0 : ℕ), (0 : Fin 2)), ((2 : ℕ), (1 : Fin 2))]
      + (2 : ℂ) • stWordSF [((0 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))] := by
  rw [WzeroSF, map_add, T_sfWgen, T_sfWgen,
    stWordSF_pair_swap ((1 : ℕ), (1 : Fin 2)) ((1 : ℕ), (0 : Fin 2))]
  abel

/-- `L₋₁ω = u₁₀ - u₀₁`: the **antisymmetric** weight-`3` state, the fourth direction of
`W(2)₃` alongside the triplet. -/
theorem T_omega : T ωSF = sfWgen 1 0 - sfWgen 0 1 := by
  rw [ωSF, map_neg, T_stWordSF_two, sfWgen, sfWgen,
    stWordSF_pair_swap ((1 : ℕ), (0 : Fin 2)) ((0 : ℕ), (1 : Fin 2))]
  norm_num
  abel

/-- `L₋₁²ω = -2e + 2(w₁₀ - w₀₁)`. -/
theorem T_T_omega :
    T (T ωSF) = (-2 : ℂ) • stWordSF [((1 : ℕ), (0 : Fin 2)), ((1 : ℕ), (1 : Fin 2))]
      + (2 : ℂ) • stWordSF [((0 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))]
      - (2 : ℂ) • stWordSF [((0 : ℕ), (0 : Fin 2)), ((2 : ℕ), (1 : Fin 2))] := by
  rw [T_omega, map_sub, T_sfWgen, T_sfWgen,
    stWordSF_pair_swap ((1 : ℕ), (1 : Fin 2)) ((1 : ℕ), (0 : Fin 2))]
  module


/-! ## §9  The values of `F` on the weight-`4` basis

`F(e) = 2`, `F(w₁₀) = 1`, `F(w₀₁) = -1`, `F(w₀₀) = F(w₁₁) = 0`. -/

/-- `F(e) = 2`, `e = χ⁰₋₂χ¹₋₂|0⟩`. -/
@[simp] theorem sepF_e :
    sepF (stWordSF [((1 : ℕ), (0 : Fin 2)), ((1 : ℕ), (1 : Fin 2))]) = 2 := by
  rw [sepF_stWordSF_pair]; norm_num

/-- `F(w₀₀) = 0`. -/
@[simp] theorem sepF_w00 :
    sepF (stWordSF [((0 : ℕ), (0 : Fin 2)), ((2 : ℕ), (0 : Fin 2))]) = 0 := by
  rw [sepF_stWordSF_pair]; norm_num

/-- `F(w₁₁) = 0`. -/
@[simp] theorem sepF_w11 :
    sepF (stWordSF [((0 : ℕ), (1 : Fin 2)), ((2 : ℕ), (1 : Fin 2))]) = 0 := by
  rw [sepF_stWordSF_pair]; norm_num

/-- `F(w₀₁) = -1`. -/
@[simp] theorem sepF_w01 :
    sepF (stWordSF [((0 : ℕ), (0 : Fin 2)), ((2 : ℕ), (1 : Fin 2))]) = -1 := by
  rw [sepF_stWordSF_pair]; norm_num

/-- `F(w₁₀) = 1`. -/
@[simp] theorem sepF_w10 :
    sepF (stWordSF [((0 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))]) = 1 := by
  rw [sepF_stWordSF_pair]; norm_num

/-! ## §10  The decision

`F` kills all four translates and takes the value `2` on `ω₍₋₁₎ω`. -/

/-- `F(L₋₁W⁺) = 0`. -/
@[simp] theorem sepF_T_WplusSF : sepF (T WplusSF) = 0 := by
  rw [T_WplusSF, map_smul, sepF_w00, smul_zero]

/-- `F(L₋₁W⁻) = 0`. -/
@[simp] theorem sepF_T_WminusSF : sepF (T WminusSF) = 0 := by
  rw [T_WminusSF, map_smul, sepF_w11, smul_zero]

/-- `F(L₋₁W⁰) = 0`: the `w₀₁` and `w₁₀` contributions cancel because `W⁰` is symmetric. -/
@[simp] theorem sepF_T_WzeroSF : sepF (T WzeroSF) = 0 := by
  rw [T_WzeroSF, map_add, map_smul, map_smul, sepF_w01, sepF_w10]
  norm_num

/-- `F(L₋₁²ω) = 0`: here the `e`-term is what cancels the `w`-terms. -/
@[simp] theorem sepF_T_T_omega : sepF (T (T ωSF)) = 0 := by
  rw [T_T_omega, map_sub, map_add, map_smul, map_smul, map_smul, sepF_e, sepF_w10, sepF_w01]
  norm_num

/-- **`F(ω₍₋₁₎ω) = 2 ≠ 0`.**  This single number is the whole decision. -/
theorem sepF_omega_poissonMul_omega :
    sepF ((tripletW2.smul tripletW2.conformalVector (-1) tripletW2.conformalVector :
      evenOdd QSF 0) : FockSF) = 2 := by
  rw [omega_poissonMul_omega_basis, map_sub, sepF_w10, sepF_w01]
  norm_num

/-- `F` pulled back to `W(2)`. -/
noncomputable def sepFW : (evenOdd QSF (0 : ZMod 2)) →ₗ[ℂ] ℂ :=
  sepF ∘ₗ (evenOdd QSF (0 : ZMod 2)).subtype

@[simp] theorem sepFW_apply (x : evenOdd QSF (0 : ZMod 2)) : sepFW x = sepF (x : FockSF) := rfl

/-- **THE DECISION, negative form.**  `ω₍₋₁₎ω` is **not** a linear combination of the
translates `L₋₁W⁺, L₋₁W⁰, L₋₁W⁻` of the weight-`3` triplet — nor does adding the fourth
weight-`3` direction `L₋₁²ω` help.  So `:TT:` is *not* `∑ₐ cₐ ∂W^a`, and the null relation the
nilpotency argument needed does **not** hold. -/
theorem not_exists_omega_sq_eq_translates :
    ¬ ∃ cp c0 cm cd : ℂ,
        tripletW2.smul tripletW2.conformalVector (-1) tripletW2.conformalVector
          = cp • tripletW2.L (-1) Wplus + c0 • tripletW2.L (-1) Wzero
            + cm • tripletW2.L (-1) Wminus
            + cd • tripletW2.L (-1) (tripletW2.L (-1) tripletW2.conformalVector) := by
  rintro ⟨cp, c0, cm, cd, h⟩
  have h' := congrArg sepFW h
  rw [sepFW_apply, sepF_omega_poissonMul_omega] at h'
  simp only [map_add, map_smul, sepFW_apply, tripletW2_L_neg_one_coe, Wplus_coe, Wzero_coe,
    Wminus_coe, tripletW2_conformalVector_coe, sepF_T_WplusSF, sepF_T_WzeroSF, sepF_T_WminusSF,
    sepF_T_T_omega, smul_zero, add_zero] at h'
  norm_num at h'

/-- The question, literally: `ω₍₋₁₎ω` is **not** `∑ₐ cₐ ∂W^a`.  (A special case
of `not_exists_omega_sq_eq_translates`, which also allows the fourth weight-`3` direction.) -/
theorem not_exists_omega_sq_eq_triplet_translates :
    ¬ ∃ cp c0 cm : ℂ,
        tripletW2.smul tripletW2.conformalVector (-1) tripletW2.conformalVector
          = cp • tripletW2.L (-1) Wplus + c0 • tripletW2.L (-1) Wzero
            + cm • tripletW2.L (-1) Wminus := by
  rintro ⟨cp, c0, cm, h⟩
  exact not_exists_omega_sq_eq_translates ⟨cp, c0, cm, 0, by rw [h]; module⟩

/-- The same statement as a span membership, inside `W(2)`. -/
theorem omega_sq_not_mem_translates :
    tripletW2.smul tripletW2.conformalVector (-1) tripletW2.conformalVector
      ∉ Submodule.span ℂ {tripletW2.L (-1) Wplus, tripletW2.L (-1) Wzero,
          tripletW2.L (-1) Wminus,
          tripletW2.L (-1) (tripletW2.L (-1) tripletW2.conformalVector)} := by
  intro hmem
  have hle : Submodule.span ℂ {tripletW2.L (-1) Wplus, tripletW2.L (-1) Wzero,
      tripletW2.L (-1) Wminus,
      tripletW2.L (-1) (tripletW2.L (-1) tripletW2.conformalVector)} ≤ LinearMap.ker sepFW := by
    rw [Submodule.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, sepFW_apply, tripletW2_L_neg_one_coe,
        Wplus_coe, Wzero_coe, Wminus_coe, tripletW2_conformalVector_coe, sepF_T_WplusSF,
        sepF_T_WzeroSF, sepF_T_WminusSF, sepF_T_T_omega]
  have h0 := hle hmem
  rw [LinearMap.mem_ker, sepFW_apply, sepF_omega_poissonMul_omega] at h0
  norm_num at h0


/-! ## §11  `F` sees only conformal weight `4`

Each of the three coefficient functionals in `F` reads off a two-letter word of weight `4`, so
`F` annihilates every word of any other weight, hence all of `gradingSF h` for `h ≠ 4`.  This
is what upgrades §10 from "not in the span of these four vectors" to "not in `O₂`". -/

/-- A coefficient functional vanishes on a word of the wrong weight. -/
theorem wordCoeff_stWordSF_pair_of_weight {p q r s : ℕ × Fin 2} (h : p.1 + q.1 ≠ r.1 + s.1) :
    wordCoeff p q (stWordSF [r, s]) = 0 := by
  rw [wordCoeff_stWordSF_pair]
  have e1 : (if p = r then (1 : ℂ) else 0) * (if q = s then (1 : ℂ) else 0) = 0 := by
    by_cases hpr : p = r
    · by_cases hqs : q = s
      · exact absurd (by rw [hpr, hqs]) h
      · rw [if_neg hqs, mul_zero]
    · rw [if_neg hpr, zero_mul]
  have e2 : (if p = s then (1 : ℂ) else 0) * (if q = r then (1 : ℂ) else 0) = 0 := by
    by_cases hps : p = s
    · by_cases hqr : q = r
      · exact absurd (by rw [hps, hqr]; omega) h
      · rw [if_neg hqr, mul_zero]
    · rw [if_neg hps, zero_mul]
  rw [e1, e2, sub_zero]

/-- `F` kills every word whose conformal weight is not `4`. -/
theorem sepF_stWordSF_of_sfWeight_ne_four {l : SFWord} (hl : sfWeight l ≠ 4) :
    sepF (stWordSF l) = 0 := by
  rcases l with _ | ⟨r, _ | ⟨s, _ | ⟨t, rest⟩⟩⟩
  · exact sepF_stWordSF_nil
  · exact sepF_stWordSF_single r
  · have h : r.1 + s.1 ≠ 2 := by
      intro hc
      apply hl
      simp only [sfWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    have h1 := wordCoeff_stWordSF_pair_of_weight (p := ((1 : ℕ), (0 : Fin 2)))
      (q := ((1 : ℕ), (1 : Fin 2))) (r := r) (s := s) (by change (1 : ℕ) + 1 ≠ r.1 + s.1; omega)
    have h2 := wordCoeff_stWordSF_pair_of_weight (p := ((0 : ℕ), (1 : Fin 2)))
      (q := ((2 : ℕ), (0 : Fin 2))) (r := r) (s := s) (by change (0 : ℕ) + 2 ≠ r.1 + s.1; omega)
    have h3 := wordCoeff_stWordSF_pair_of_weight (p := ((0 : ℕ), (0 : Fin 2)))
      (q := ((2 : ℕ), (1 : Fin 2))) (r := r) (s := s) (by change (0 : ℕ) + 2 ≠ r.1 + s.1; omega)
    rw [sepF_apply, h1, h2, h3]
    ring
  · exact sepF_stWordSF_long r s (List.cons_ne_nil t rest)

/-- `F` vanishes on every conformal weight other than `4`. -/
theorem sepF_of_mem_gradingSF {h : ℂ} (hh : h ≠ 4) {x : FockSF} (hx : x ∈ gradingSF h) :
    sepF x = 0 := by
  rw [gradingSF] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      refine sepF_stWordSF_of_sfWeight_ne_four (fun hw => hh ?_)
      have hc : ((sfWeight l : ℕ) : ℂ) = h := hl
      rw [hw] at hc
      rw [← hc]
      norm_num
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

/-! ## §12  `F` annihilates **all** of `L₋₁(𝒱₃)`

Not just the four translates of §10: the whole image of the weight-`3` space of the *ambient*
Fock space — odd states included.  So the failure of the relation cannot be repaired by a
better choice of weight-`3` generators. -/

/-- `F(L₋₁u_{ab}) = 0` for each of the four weight-`3` two-letter words. -/
@[simp] theorem sepF_T_sfWgen (a b : Fin 2) : sepF (T (sfWgen a b)) = 0 := by
  fin_cases a <;> fin_cases b <;>
    rw [T_sfWgen, map_add, map_smul, sepF_stWordSF_pair, sepF_stWordSF_pair] <;> norm_num

/-- `F ∘ L₋₁` kills every word of conformal weight `3`. -/
theorem sepF_T_stWordSF_of_weight_three {l : SFWord} (hl : sfWeight l = 3) :
    sepF (T (stWordSF l)) = 0 := by
  have hlen : l.length ≤ 3 := hl ▸ sfWeight_length_le l
  rcases l with _ | ⟨r, _ | ⟨s, _ | ⟨t, rest⟩⟩⟩
  · simp only [sfWeight, List.map_nil, List.sum_nil] at hl
    exact absurd hl (by decide)
  · rw [T_stWordSF_single, map_smul, sepF_stWordSF_single, smul_zero]
  · have h : r.1 + s.1 = 1 := by
      simp only [sfWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hl
      omega
    obtain ⟨r1, r2⟩ := r
    obtain ⟨s1, s2⟩ := s
    simp only at h
    rcases (show (r1 = 0 ∧ s1 = 1) ∨ (r1 = 1 ∧ s1 = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact sepF_T_sfWgen r2 s2
    · rw [stWordSF_pair_swap ((1 : ℕ), r2) ((0 : ℕ), s2), map_neg, map_neg,
        show stWordSF [((0 : ℕ), s2), ((1 : ℕ), r2)] = sfWgen s2 r2 from rfl,
        sepF_T_sfWgen, neg_zero]
  · rcases rest with _ | ⟨u, rest'⟩
    · rw [T_stWordSF_triple]
      simp only [map_add, map_smul,
        sepF_stWordSF_long _ _ (List.cons_ne_nil (t.1 + 1, t.2) []),
        sepF_stWordSF_long _ _ (List.cons_ne_nil t []),
        smul_zero, add_zero]
    · simp only [List.length_cons] at hlen
      omega

/-- `F ∘ L₋₁ = 0` on the whole weight-`3` space `𝒱₃` of `FockSF`. -/
theorem sepF_T_of_mem_gradingSF_three {x : FockSF} (hx : x ∈ gradingSF 3) : sepF (T x) = 0 := by
  rw [gradingSF] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      have hc : ((sfWeight l : ℕ) : ℂ) = 3 := hl
      exact sepF_T_stWordSF_of_weight_three (by exact_mod_cast hc)
  | zero => rw [map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, map_smul, hy, smul_zero]

/-- **The strengthened decision.**  `ω₍₋₁₎ω` is not `L₋₁` of *anything* of conformal
weight `3` — not of a triplet element, not of `L₋₁ω`, not even of an odd state of the ambient
symplectic-fermion algebra. -/
theorem omega_sq_not_mem_T_grading_three :
    ((tripletW2.smul tripletW2.conformalVector (-1) tripletW2.conformalVector :
        evenOdd QSF 0) : FockSF) ∉ Submodule.map T (gradingSF 3) := by
  rintro ⟨y, hy, hEq⟩
  have h0 := sepF_T_of_mem_gradingSF_three hy
  rw [hEq, sepF_omega_poissonMul_omega] at h0
  norm_num at h0


/-! ## §13  `ω₍₋₁₎ω ∉ O₂(W(2))`

The separating functional `F` annihilates **every** generator `u₍₋₂₎v` of `O₂(W(2))`, hence all
of `O₂`, while `F(ω₍₋₁₎ω) = 2`.  The generator argument is exactly the weight bookkeeping of the
module docstring, carried out inside Lean:

* `F` only sees weight `4` (§11), so only `wt u + wt v = 3` can contribute;
* `W(2)` is spanned by **even-length** words, and an even word of weight `1` does not exist
  (`length_eq_one_of_sfWeight_eq_one`), so the only splits are `(0,3)` and `(3,0)`;
* `(0,3)`: `𝟙₍₋₂₎v = 0`;  `(3,0)`: `u₍₋₂₎𝟙 = L₋₁u` with `u` of weight `3`, killed by §12. -/

/-- An even word state, packaged as a state of `W(2)`, sits in its own weight. -/
theorem mem_tripletW2_grading_of_word {l : SFWord} (hl : Even l.length) :
    (⟨stWordSF l, stWordSF_mem_evenPart hl⟩ : evenOdd QSF (0 : ZMod 2))
      ∈ tripletW2.grading (sfWeight l : ℤ) := by
  rw [tripletW2_grading]
  refine Submodule.mem_comap.mpr ?_
  change stWordSF l ∈ gradingSF (((sfWeight l : ℤ) : ℂ))
  rw [show (((sfWeight l : ℤ) : ℂ)) = ((sfWeight l : ℕ) : ℂ) by push_cast; ring]
  exact stWordSF_mem_gradingSF l

/-- The even word states, as states of `W(2)`. -/
def evenWordStates : Set (evenOdd QSF (0 : ZMod 2)) :=
  {y | ∃ (l : SFWord) (hl : Even l.length), y = ⟨stWordSF l, stWordSF_mem_evenPart hl⟩}

/-- `W(2)` is spanned by the even word states (`evenPartSF_eq_span`, transferred to the
subtype). -/
theorem span_evenWordStates : Submodule.span ℂ evenWordStates = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have himg : (evenOdd QSF (0 : ZMod 2)).subtype '' evenWordStates
      = stWordSF '' {l : SFWord | Even l.length} := by
    ext x
    constructor
    · rintro ⟨z, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨stWordSF l, stWordSF_mem_evenPart hl⟩, ⟨l, hl, rfl⟩, rfl⟩
  have hmap : Submodule.map (evenOdd QSF (0 : ZMod 2)).subtype
      (Submodule.span ℂ evenWordStates) = (evenOdd QSF (0 : ZMod 2) : Submodule ℂ FockSF) := by
    rw [Submodule.map_span, himg, ← evenPartSF_eq_span]
  have hy : (y : FockSF) ∈ Submodule.map (evenOdd QSF (0 : ZMod 2)).subtype
      (Submodule.span ℂ evenWordStates) := by rw [hmap]; exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  rwa [Subtype.ext hzy] at hz

/-- The generator case: `F` kills `u₍₋₂₎v` for two even **word** states. -/
theorem sepF_smul_word_word {l m : SFWord} (hl : Even l.length) (hm : Even m.length) :
    sepF ((tripletW2.smul ⟨stWordSF l, stWordSF_mem_evenPart hl⟩ (-2)
      ⟨stWordSF m, stWordSF_mem_evenPart hm⟩ : evenOdd QSF 0) : FockSF) = 0 := by
  by_cases hw : sfWeight l + sfWeight m + 1 = 4
  · have hsum : sfWeight l + sfWeight m = 3 := by omega
    have hne1 : ∀ n : SFWord, Even n.length → sfWeight n ≠ 1 := by
      intro n hn h1
      rw [length_eq_one_of_sfWeight_eq_one h1] at hn
      exact absurd hn (by simp)
    have hzero : sfWeight l = 0 ∨ sfWeight m = 0 := by
      rcases Nat.eq_zero_or_pos (sfWeight l) with h | h
      · exact Or.inl h
      · rcases Nat.eq_zero_or_pos (sfWeight m) with h' | h'
        · exact Or.inr h'
        · rcases (show sfWeight l = 1 ∨ sfWeight l = 2 by omega) with h1 | h2
          · exact absurd h1 (hne1 l hl)
          · exact absurd (show sfWeight m = 1 by omega) (hne1 m hm)
    rcases hzero with h0 | h0
    · have hlnil : l = [] :=
        List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (h0 ▸ sfWeight_length_le l))
      have huvac : (⟨stWordSF l, stWordSF_mem_evenPart hl⟩ : evenOdd QSF (0 : ZMod 2))
          = tripletW2.vacuum := by
        apply Subtype.ext
        rw [tripletW2_vacuum_coe]
        change stWordSF l = (1 : FockSF)
        rw [hlnil, stWordSF_nil]
      rw [huvac, PreVertexAlgebra.smul_vacuum_left, if_neg (by decide : ¬ (-2 : ℤ) = -1)]
      simp
    · have hmnil : m = [] :=
        List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (h0 ▸ sfWeight_length_le m))
      have hvvac : (⟨stWordSF m, stWordSF_mem_evenPart hm⟩ : evenOdd QSF (0 : ZMod 2))
          = tripletW2.vacuum := by
        apply Subtype.ext
        rw [tripletW2_vacuum_coe]
        change stWordSF m = (1 : FockSF)
        rw [hmnil, stWordSF_nil]
      have hwt : sfWeight l = 3 := by omega
      have hc := VertexOperatorAlgebra.creation_pow tripletW2
        ⟨stWordSF l, stWordSF_mem_evenPart hl⟩ 1
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul] at hc
      rw [VertexOperatorAlgebra.T_eq_Lneg1, show (-(1 : ℤ) - 1) = -2 from by norm_num] at hc
      rw [hvvac, hc, tripletW2_L_neg_one_coe]
      exact sepF_T_stWordSF_of_weight_three hwt
  · have hmem := PreVertexAlgebra.smul_mem_grading tripletW2.toPreVertexAlgebra
      (mem_tripletW2_grading_of_word hl) (mem_tripletW2_grading_of_word hm) (-2)
    rw [show ((sfWeight l : ℤ) + (sfWeight m : ℤ) - (-2) - 1)
        = ((sfWeight l + sfWeight m + 1 : ℕ) : ℤ) from by push_cast; ring,
      tripletW2_grading] at hmem
    refine sepF_of_mem_gradingSF (fun hc => hw ?_) hmem
    exact_mod_cast hc

/-- `F` kills `u₍₋₂₎v` for `u` an even word state and `v` arbitrary in `W(2)`. -/
theorem sepF_smul_word_right {l : SFWord} (hl : Even l.length)
    (v : evenOdd QSF (0 : ZMod 2)) :
    sepF ((tripletW2.smul ⟨stWordSF l, stWordSF_mem_evenPart hl⟩ (-2) v :
      evenOdd QSF 0) : FockSF) = 0 := by
  have hv : v ∈ Submodule.span ℂ evenWordStates := by rw [span_evenWordStates]; trivial
  induction hv using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      exact sepF_smul_word_word hl hm
  | zero => rw [PreVertexAlgebra.smul_zero_right]; simp
  | add y z _ _ hy hz =>
      rw [PreVertexAlgebra.smul_add_right]
      simp only [Submodule.coe_add, map_add, hy, hz, add_zero]
  | smul c y _ hy =>
      rw [PreVertexAlgebra.smul_smul_right]
      simp only [Submodule.coe_smul, map_smul, hy, smul_zero]

/-- `F` annihilates every generator `u₍₋₂₎v` of `O₂(W(2))`. -/
theorem sepF_smul_neg_two (u v : evenOdd QSF (0 : ZMod 2)) :
    sepF ((tripletW2.smul u (-2) v : evenOdd QSF 0) : FockSF) = 0 := by
  have hu : u ∈ Submodule.span ℂ evenWordStates := by rw [span_evenWordStates]; trivial
  induction hu using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      exact sepF_smul_word_right hl v
  | zero => rw [PreVertexAlgebra.smul_zero_left]; simp
  | add y z _ _ hy hz =>
      rw [PreVertexAlgebra.smul_add_left]
      simp only [Submodule.coe_add, map_add, hy, hz, add_zero]
  | smul c y _ hy =>
      rw [PreVertexAlgebra.smul_smul_left]
      simp only [Submodule.coe_smul, map_smul, hy, smul_zero]

/-- `F` annihilates all of `O₂(W(2))`. -/
theorem sepFW_eq_zero_of_mem_O₂ {x : evenOdd QSF (0 : ZMod 2)} (hx : x ∈ O₂ tripletW2) :
    sepFW x = 0 := by
  rw [O₂] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨u, v, rfl⟩ := hy
      exact sepF_smul_neg_two u v
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

/-- **THE THEOREM.**  `ω₍₋₁₎ω ∉ O₂(W(2))`: the Poisson square of the conformal vector
is **not** zero modulo `C₂`.  The `T² = 0` shortcut to `C₂`-cofiniteness of the triplet is
therefore closed. -/
theorem omega_sq_not_mem_O₂ :
    poissonMul tripletW2 tripletW2.conformalVector tripletW2.conformalVector
      ∉ O₂ tripletW2 := by
  intro hmem
  have h0 := sepFW_eq_zero_of_mem_O₂ hmem
  rw [sepFW_apply, poissonMul_def, sepF_omega_poissonMul_omega] at h0
  norm_num at h0

/-- **`[ω]² ≠ 0` in `A₂(W(2))`**, the same statement in the Poisson algebra. -/
theorem poissonMul_omega_omega_ne_zero_in_A₂ :
    mk₂ tripletW2 (poissonMul tripletW2 tripletW2.conformalVector tripletW2.conformalVector)
      ≠ 0 := by
  intro h
  exact omega_sq_not_mem_O₂ ((Submodule.Quotient.mk_eq_zero _).mp h)


/-! ## §14  The triplet generators are genuine: nonzero, and **primary**

`L₁` is what distinguishes the triplet from the descendant inside `W(2)₃`: it kills the three
symmetric combinations and does *not* kill the antisymmetric one.  The value it takes there,
`L₁L₋₁ω = 4ω`, is exactly what the Virasoro algebra demands (`[L₁,L₋₁] = 2L₀` and `L₀ω = 2ω`),
so this section is simultaneously a construction and an independent check of the sign
conventions used throughout the file. -/

/-- The zero mode acts as zero: the symplectic pairing `{χᵃ_m, χᵇ_n} = m δ_{m+n,0} ωᵃᵇ` carries
a factor of the mode number.  (Stated here to avoid depending on `SymplecticFermionVirasoroB`,
which has its own copy in a nested namespace.) -/
theorem chiM_zero_eq_zero (a : Fin 2) : chiM a 0 = 0 := by
  rw [chiM_def, show (-(0 : ℤ) - 1) = -1 from by ring, chi,
    if_neg (by omega : ¬ ((0 : ℤ) ≤ -1)), show (-(-1 : ℤ) - 1).toNat = 0 from by norm_num]
  exact annSF_zero a

/-- `L₁u_{ab} = 2χᵃ₋₁χᵇ₋₁|0⟩`, from `[L₁, χᶜ_r] = -r χᶜ_{1+r}` and `χᶜ_0 = 0`. -/
theorem LSF_one_sfWgen (a b : Fin 2) :
    LSF 1 (sfWgen a b) = (2 : ℂ) • stWordSF [((0 : ℕ), a), ((0 : ℕ), b)] := by
  have hword : sfWgen a b = chiM a (-1) (chiM b (-2) vacSF) := by
    rw [sfWgen, chiM_neg_one, show (-2 : ℤ) = -((1 : ℕ) : ℤ) - 1 from by norm_num,
      chiM_eq_creBase b 1, show vacSF = stWordSF [] from rfl, creBase_stWordSF, creBase_stWordSF]
  have h1 := LSF_comm_chiM_apply 1 a (-1) (chiM b (-2) vacSF)
  have h2 := LSF_comm_chiM_apply 1 b (-2) vacSF
  norm_num at h1 h2
  have hv : LSF 1 vacSF = 0 := LSF_vacuum (by norm_num)
  rw [hword,
    show LSF 1 (chiM a (-1) (chiM b (-2) vacSF))
        = chiM a (-1) (LSF 1 (chiM b (-2) vacSF)) + chiM a 0 (chiM b (-2) vacSF) from by
      linear_combination (norm := module) h1,
    show LSF 1 (chiM b (-2) vacSF)
        = chiM b (-2) (LSF 1 vacSF) + (2 : ℂ) • chiM b (-1) vacSF from by
      linear_combination (norm := module) h2,
    hv, map_zero, zero_add, map_smul, chiM_zero_eq_zero, LinearMap.zero_apply, add_zero,
    chiM_neg_one, chiM_neg_one, show vacSF = stWordSF [] from rfl, creBase_stWordSF,
    creBase_stWordSF]

/-- `L₁W⁺ = 0`: `W⁺` is **primary**. -/
theorem LSF_one_WplusSF : LSF 1 WplusSF = 0 := by
  rw [WplusSF, LSF_one_sfWgen, stWordSF_pair_self, smul_zero]

/-- `L₁W⁻ = 0`: `W⁻` is **primary**. -/
theorem LSF_one_WminusSF : LSF 1 WminusSF = 0 := by
  rw [WminusSF, LSF_one_sfWgen, stWordSF_pair_self, smul_zero]

/-- `L₁W⁰ = 0`: `W⁰` is **primary** — the two words cancel because `W⁰` is the symmetric
combination and the words are antisymmetric. -/
theorem LSF_one_WzeroSF : LSF 1 WzeroSF = 0 := by
  rw [WzeroSF, map_add, LSF_one_sfWgen, LSF_one_sfWgen,
    stWordSF_pair_swap ((0 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2))]
  module

/-- `L₁L₋₁ω = 4ω ≠ 0`: the antisymmetric direction of `W(2)₃` is **not** primary — it is the
descendant.  This is the Virasoro consistency check `[L₁,L₋₁] = 2L₀`, `L₀ω = 2ω`, and it
independently confirms the sign in `T_omega` (hence in the whole computation). -/
theorem LSF_one_T_omega : LSF 1 (T ωSF) = (4 : ℂ) • ωSF := by
  rw [T_omega, map_sub, LSF_one_sfWgen, LSF_one_sfWgen,
    stWordSF_pair_swap ((0 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2)), ωSF]
  module

/-! ## §15  Non-degeneracy -/

/-- `⟨(0,0)(1,0)|W⁺⟩ = 1`. -/
theorem wordCoeff_WplusSF :
    wordCoeff ((0 : ℕ), (0 : Fin 2)) ((1 : ℕ), (0 : Fin 2)) WplusSF = 1 := by
  rw [WplusSF, sfWgen, wordCoeff_stWordSF_pair]; norm_num

/-- `⟨(0,1)(1,1)|W⁻⟩ = 1`. -/
theorem wordCoeff_WminusSF :
    wordCoeff ((0 : ℕ), (1 : Fin 2)) ((1 : ℕ), (1 : Fin 2)) WminusSF = 1 := by
  rw [WminusSF, sfWgen, wordCoeff_stWordSF_pair]; norm_num

/-- `⟨(0,0)(1,1)|W⁰⟩ = 1`. -/
theorem wordCoeff_WzeroSF :
    wordCoeff ((0 : ℕ), (0 : Fin 2)) ((1 : ℕ), (1 : Fin 2)) WzeroSF = 1 := by
  rw [WzeroSF, sfWgen, sfWgen, map_add, wordCoeff_stWordSF_pair, wordCoeff_stWordSF_pair]
  norm_num

/-- `W⁺ ≠ 0`. -/
theorem WplusSF_ne_zero : WplusSF ≠ 0 := by
  intro h
  have := wordCoeff_WplusSF
  rw [h, map_zero] at this
  norm_num at this

/-- `W⁰ ≠ 0`. -/
theorem WzeroSF_ne_zero : WzeroSF ≠ 0 := by
  intro h
  have := wordCoeff_WzeroSF
  rw [h, map_zero] at this
  norm_num at this

/-- `W⁻ ≠ 0`. -/
theorem WminusSF_ne_zero : WminusSF ≠ 0 := by
  intro h
  have := wordCoeff_WminusSF
  rw [h, map_zero] at this
  norm_num at this

/-- `W⁺ ≠ 0` in `W(2)`. -/
theorem Wplus_ne_zero : Wplus ≠ 0 := fun h => WplusSF_ne_zero (congrArg Subtype.val h)

/-- `W⁰ ≠ 0` in `W(2)`. -/
theorem Wzero_ne_zero : Wzero ≠ 0 := fun h => WzeroSF_ne_zero (congrArg Subtype.val h)

/-- `W⁻ ≠ 0` in `W(2)`. -/
theorem Wminus_ne_zero : Wminus ≠ 0 := fun h => WminusSF_ne_zero (congrArg Subtype.val h)


/-! ## §16  `dim W(2)₃ ≥ 4`

⚠ The naive reduction targets a **3**-dimensional space `span{L₋₁W^a}`.  The correct
target is `L₋₁(W(2)₃)` with `W(2)₃` of dimension `4`: the triplet *and* `L₋₁ω`.  (The answer is
negative for both, §10, but the enlarged statement is the one that matches `O₂`.) -/

/-- `W⁺, W⁰, W⁻, L₋₁ω` are linearly independent, so `dim W(2)₃ ≥ 4`.  (It is exactly `4`:
the weight-`3` even words are the four `u_{ab}`.) -/
theorem triplet_and_descendant_indep {cp c0 cm cd : ℂ}
    (h : cp • WplusSF + c0 • WzeroSF + cm • WminusSF + cd • T ωSF = 0) :
    cp = 0 ∧ c0 = 0 ∧ cm = 0 ∧ cd = 0 := by
  have e1 := congrArg (wordCoeff ((0 : ℕ), (0 : Fin 2)) ((1 : ℕ), (0 : Fin 2))) h
  have e2 := congrArg (wordCoeff ((0 : ℕ), (1 : Fin 2)) ((1 : ℕ), (1 : Fin 2))) h
  have e3 := congrArg (wordCoeff ((0 : ℕ), (0 : Fin 2)) ((1 : ℕ), (1 : Fin 2))) h
  have e4 := congrArg (wordCoeff ((0 : ℕ), (1 : Fin 2)) ((1 : ℕ), (0 : Fin 2))) h
  simp only [WplusSF, WzeroSF, WminusSF, T_omega, sfWgen, map_add, map_sub, map_smul, map_zero,
    wordCoeff_stWordSF_pair, smul_eq_mul] at e1 e2 e3 e4
  norm_num at e1 e2 e3 e4
  refine ⟨e1, ?_, e2, ?_⟩
  · linear_combination (e3 + e4) / 2
  · linear_combination (e4 - e3) / 2

end VOA.SympFerm
