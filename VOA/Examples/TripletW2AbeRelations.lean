/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.TripletW2Gens

/-!
# Abe's `C₂`-relations for the triplet `W(2) = SF(1)⁺` at `c = -2`

T. Abe, *A `ℤ₂`-orbifold model of the symplectic fermionic vertex operator superalgebra*,
Math. Z. **255** (2007) 755–792 = `arXiv:math/0503472`, §3.3, lists the relations that cut
`A₂(W(2)) = W(2)/C₂(W(2))` down to dimension `≤ 11` (his Prop. 3.11), in terms of the classes of
the four strong generators `ω, E, H, F` of `Examples.TripletW2Gens`:

```
  Ē² = F̄² = H̄Ē = H̄F̄ = 0,      2H̄² = -ĒF̄ = (16/9)ω̄³,
  ω̄²Ē = ω̄²H̄ = ω̄²F̄ = 0,        ω̄⁵ = 0.
```

⚠ Abe asserts the underlying `4`-term product formula (his unnumbered displayed equation in
§3.3) as "a direct calculation using the associativity formula", with **no derivation**.  This
file does not use it: everything is redone from scratch in the concrete Clifford model
`FockSF = CliffordAlgebra QSF` (`QSF = 0`, an exterior algebra), where the vertex operators are
explicit normal-ordered products of the fermion modes `chiM a p` and every product below is a
finite Wick sum.

## Main results — **seven of Abe's relations are proved**

* `Ebar_sq`, `Fbar_sq` — `Ē² = 0` and `F̄² = 0`.  Proved in the strictly stronger form
  `abeE_poissonMul_abeE`, `abeF_poissonMul_abeF`: **`E₍₋₁₎E = 0` and `F₍₋₁₎F = 0` exactly, in
  `FockSF`**, not merely modulo `O₂`.  Reason: `E = e₍₋₂₎e` and `F = f₍₋₂₎f` live in a single
  fermion flavour, where `ωᵃᵃ = 0` forbids every contraction, and a `4`-letter word of weight
  `6` in one flavour would need four *distinct* levels summing to `6` (minimum `1+2+3+4 = 10`).
* `Ebar_mul_Hbar`, `Fbar_mul_Hbar` — `ĒH̄ = 0` and `F̄H̄ = 0`.  Via the explicit vectors
  `abeE_poissonMul_abeH : E₍₋₁₎H = (5/2)·χ¹₋₄χ¹₋₂|0⟩ - 7·χ¹₋₅χ¹₋₁|0⟩` and
  `abeF_poissonMul_abeH : F₍₋₁₎H = 7·χ⁰₋₅χ⁰₋₁|0⟩ - (5/2)·χ⁰₋₄χ⁰₋₂|0⟩`, both of which are
  translates: `L₋₁(χᵃ₋₃χᵃ₋₂|0⟩) = 3χᵃ₋₄χᵃ₋₂|0⟩` and
  `L₋₁(χᵃ₋₄χᵃ₋₁|0⟩) = χᵃ₋₄χᵃ₋₂|0⟩ + 4χᵃ₋₅χᵃ₋₁|0⟩` (`w2pair_31_mem_O₂`, `w2pair_40_mem_O₂`).
* `two_Hbar_sq_add_Ebar_Fbar` — **`ĒF̄ = -2H̄²`**.  The five weight-`6` products
  `G¹⁰₍₋₁₎G¹⁰`, `G¹⁰₍₋₁₎G⁰¹`, `G⁰¹₍₋₁₎G¹⁰`, `G⁰¹₍₋₁₎G⁰¹`, `E₍₋₁₎F` are each computed in the word
  basis (§7, §11); the two four-letter words cancel (`N₂ = N`, `N = -N'`), and the residue is a
  translate (`two_HH_add_EF_fock`).
* `two_Hbar_sq_eq` / `Hbar_sq_eq` — **`2H̄² = (16/9)ω̄³`**, i.e. `H̄² = (8/9)ω̄³`.  Here
  `ω̄³` is computed as `L₋₂L₋₂ω` (`omega_cube_fock`), and the residue needs one `O₂`-generator
  beyond the translates, namely `ω₍₋₂₎G¹⁰ = L₋₃G¹⁰` (`omegaG10_fock`) — which is exactly the
  generator carrying the four-letter word.  Combined with the previous item,
  `Ebar_mul_Fbar_omega : ĒF̄ = -(16/9)ω̄³`.
* `Hbar_pow_four` — **`H̄⁴ = 0`**, *derived*, not assumed: `0 = Ē²F̄² = (ĒF̄)² = 4H̄⁴`.
* `wbar_pow_six` — **`ω̄⁶ = 0`**: from `H̄⁴ = 0` and `H̄² = (8/9)ω̄³`, so
  `0 = H̄⁴ = (64/81)ω̄⁶`.  Hence `wbar_isNilpotent`, `Hbar_isNilpotent`, together with
  `Ebar_isNilpotent`, `Fbar_isNilpotent`: **all four generators of `A₂(W(2))` are nilpotent**,
  with exponents `ω̄ → 6`, `Ē → 2`, `H̄ → 4`, `F̄ → 2`.

## The engine

* `selfProd_single_contraction` — the one-contraction formula
  `Gᵃᵃ₍₋₁₎x = (2P+3)·χᵃ_{-P-3}(χᵃ_P x)` when `χᵃ_P x` is the only surviving annihilation.
* `gTerm`, `gTerm_pos`, `gTerm_neg`, `genProd_of_support` — the general master formula
  `Gᵃᵇ₍₋₁₎x = χᵃ₋₂(χᵇ₋₁x) + Σ_{p≥0}(p+2)χᵃ_{-p-3}(χᵇ_p x) + Σ_{p≥0}(p+1)χᵇ_{-p-3}(χᵃ_p x)`,
  as a finite sum over an explicitly given finset.
* `chiM_nonneg_pair` — Wick contraction of one mode against a two-letter word.
* `LSF_stWordSF_pair`, `LSF_neg_two_pair`, `LSF_neg_three_pair` — `Lₙ` on a two-letter word,
  from the commutator `[Lₙ, χᶜ_r] = -r·χᶜ_{n+r}` alone.  These are what make the `ω`-products
  cheap: `ω₍₋₁₎ = L₋₂`, `ω₍₋₂₎ = L₋₃`, and `L₋₂|0⟩ = ω`, `L₋₃|0⟩ = L₋₁ω`.
* `T_stWordSF_pair` and `T_mem_O₂` — `L₋₁v = v₍₋₂₎𝟙` is literally an `O₂`-generator, and `L₋₁`
  on a two-letter word is `(j+1)χᵃ₋ₖ₋₁χᵇ₋ⱼ₋₂|0⟩ + (k+1)χᵃ₋ₖ₋₂χᵇ₋ⱼ₋₁|0⟩`.

## ⚠ What is **not** proved

The three weight-`7` relations `ω̄²Ē = ω̄²H̄ = ω̄²F̄ = 0` (`OmegaSqEbarZero`, `OmegaSqHbarZero`,
`OmegaSqFbarZero`) did **not** close, and neither did Abe's sharp `ω̄⁵ = 0`
(`OmegaPowFiveZero`); the file proves the weaker `ω̄⁶ = 0` instead.  What *is* supplied is the
**left-hand sides, computed and verified**:

```
  ω₍₋₁₎E   = χ¹₋₂χ¹₋₃|0⟩ + 2·χ¹₋₄χ¹₋₁|0⟩                                  (omega_E_fock)
  ω₍₋₁₎ω₍₋₁₎E = -χ¹₋₂χ¹₋₃χ⁰₋₁χ¹₋₁|0⟩ + 3·χ¹₋₂χ¹₋₅|0⟩
                 + 4·χ¹₋₄χ¹₋₃|0⟩ + 8·χ¹₋₆χ¹₋₁|0⟩                          (omega_sq_E_fock)
  ω₍₋₁₎ω₍₋₁₎F = -χ⁰₋₂χ⁰₋₃χ⁰₋₁χ¹₋₁|0⟩ + 3·χ⁰₋₂χ⁰₋₅|0⟩
                 + 4·χ⁰₋₄χ⁰₋₃|0⟩ + 8·χ⁰₋₆χ⁰₋₁|0⟩                          (omega_sq_F_fock)
  ω₍₋₁₎ω₍₋₁₎H = ½(ω₍₋₁₎ω₍₋₁₎G¹⁰ + ω₍₋₁₎ω₍₋₁₎G⁰¹)   (omega_sq_G10_fock, omega_sq_G01_fock)
```

The missing half is the membership of these weight-`7` vectors in `O₂(W(2))`.  Weight `7` is
harder than weights `6`: `dim W(2)₇ = 16`, the mixed and same-flavour two-letter sectors are
joined by **four** four-letter words, and the translates `L₋₁(W(2)₆)` do not suffice — one
needs `L₋₄E`, `E₍₋₃₎ω`, `ω₍₋₂₎(W(2)₄)` and `u₍₋₂₎v` with `u, v ∈ W(2)₃`, i.e. a genuinely larger
linear system than the ones solved in §12 and §14.  An explicit cokernel check done while
preparing this file (not formalised) shows the `χ¹`-only part of `ω₍₋₁₎ω₍₋₁₎E` is *not* a
translate, so the extra generators are really needed; that is the precise remaining gap.

`omegaPowFive_of_omegaSqHbar` records the one implication that closes Abe's exponent:
`ω̄²H̄ = 0 ⟹ ω̄⁵ = 0`, using the proved `H̄² = (8/9)ω̄³`.

## ⚠ `C2Cofinite tripletW2` does **not** close here

Both in-repo entry points want a hypothesis this file does not supply.

* `Modules.NilpotentGenerators.finiteDimensional_of_four_isNilpotent` / `finrank_le_of_four`
  need, besides the four nilpotency statements — **all available**, with exponents
  `6, 2, 4, 2`, so the bound would be `dim_ℂ A₂(W(2)) ≤ 6·2·4·2 = 96` — the hypothesis
  `Algebra.adjoin ℂ {ω̄, Ē, H̄, F̄} = ⊤`.  In the repo that is
  `Examples.TripletW2Gens.StrongGenAbe` (Abe Prop. 3.7 / Cor. 3.8: `SF⁺` is strongly generated
  by `SF⁺₂ ⊕ SF⁺₃`), which is **not proved anywhere**.  It is the *single* missing input on
  that route.
* `c2Cofinite_of_abeSpanningEleven` needs `AbeSpanningEleven` (Abe Prop. 3.11), whose proof
  runs through exactly the three weight-`7` relations left open above.

So the honest status is: the nilpotency half of the nilpotency route is **complete**; the
strong-generation half is untouched.  Nothing here is stated as if `C2Cofinite tripletW2` were
available.

## Convention (for external checks, e.g. with `OPEdefs`)

`mode a m = a (-m-1)`; `FormalDist` is indexed by the `z`-**exponent**;
`stWordSF [(k₁,a₁), …, (kₙ,aₙ)] = χ^{a₁}_{-k₁-1} ⋯ χ^{aₙ}_{-kₙ-1}|0⟩`, so a letter `(k,a)` is
the creation mode `χᵃ_{-k-1}` of conformal weight `k+1`;
`{χᵃ_p, χᵇ_q} = p·δ_{p+q,0}·ωᵃᵇ` with `ω⁰¹ = 1`, `ω¹⁰ = -1`, `ωᵃᵃ = 0`;
`ω = -χ⁰₋₁χ¹₋₁|0⟩`; `L₋₁ = T`; `ω₍₋₁₎ = L₋₂`, `ω₍₋₂₎ = L₋₃`.
Abe's generators are (`Examples.TripletW2Gens`, whose normalisation `e = χ¹₋₁|0⟩`,
`f = χ⁰₋₁|0⟩` is used throughout)
`E = χ¹₋₂χ¹₋₁|0⟩`, `F = χ⁰₋₂χ⁰₋₁|0⟩`, `H = ½(χ¹₋₂χ⁰₋₁ + χ⁰₋₂χ¹₋₁)|0⟩`, `ω = -χ⁰₋₁χ¹₋₁|0⟩`.

## Status

No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axiom; the theorem
`VOA.pbw` is **not** used.  Every checked declaration depends
only on `[propext, Classical.choice, Quot.sound]`.  `OmegaSqEbarZero`, `OmegaSqHbarZero`,
`OmegaSqFbarZero`, `OmegaPowFiveZero` are `def`s of type `Prop` — deliberately unproved
*statements*; no theorem in this file depends on them.

## References

* T. Abe, Math. Z. **255** (2007) 755–792 = `arXiv:math/0503472`, Prop. 2.2, Prop. 3.7,
  Cor. 3.8, Thm 3.9, Prop. 3.11 and §3.3.
* `Examples.TripletW2Gens` (`abeOmega`, `abeE`, `abeH`, `abeF`, `abeGen`, `chiM_cons`,
  `StrongGenAbe`, `AbeSpanningEleven`).
* `Examples.TripletTTNull` (`sfGen_sq`, `sfGen_swap`, `stWordSF_pair`, `T_omega`,
  `omega_poissonMul_omega` — the last agrees with `omega_sq_fock` here, an independent check).
* `Examples.SymplecticFermionVirasoroA` (`chiM`, `chiM_swap`, `LSF`, `LSF_comm_chiM_apply`,
  `LSF_neg_two_vacuum`, `LSF_neg_one_eq_T`).
* `Modules.C2Cofinite`, `Modules.PoissonDescent` (`O₂`, `A₂`, `mk₂`, `A₂mul`, `A₂CommRing`).
-/

namespace VOA.AbeRel

open VOA
open VOA.SympFerm
open VOA.AbeGens
open CliffordAlgebra

/-! ## §1  The same-flavour sector -/

/-- The CAR scalar vanishes identically when the two flavours agree: `ωᵃᵃ = 0`. -/
theorem carC_self (a : Fin 2) (p q : ℤ) : carC a a p q = 0 := by
  rw [carC_apply, sfOmega_same, mul_zero, ite_self]

/-- Two modes of the **same** fermion strictly anticommute. -/
theorem chiM_swap_self (a : Fin 2) (p q : ℤ) (x : FockSF) :
    chiM a p (chiM a q x) = -(chiM a q (chiM a p x)) := by
  rw [chiM_swap, carC_self, zero_smul, add_zero]

/-- **Annihilation in the same-flavour sector.**  If every letter of `l` carries the flavour
`a`, then every non-negative mode `χᵃ_p` (`p ≥ 0`) kills `stWordSF l`: the CAR scalar
`ωᵃᵃ = 0` lets `χᵃ_p` be moved through the whole word, and it kills the vacuum. -/
theorem chiM_nonneg_sameFlavour (a : Fin 2) :
    ∀ l : SFWord, (∀ q ∈ l, q.2 = a) → ∀ {p : ℤ}, 0 ≤ p → chiM a p (stWordSF l) = 0 := by
  intro l
  induction l with
  | nil =>
      intro _ p hp
      rw [stWordSF_nil]
      exact chiM_vacuum a hp
  | cons q rest ih =>
      intro hall p hp
      obtain ⟨k, b⟩ := q
      have hb : b = a := hall (k, b) (by simp)
      subst hb
      have hrest : ∀ r ∈ rest, r.2 = b := fun r hr => hall r (by simp [hr])
      rw [← chiM_cons b k rest, chiM_swap_self, ih hrest hp, map_zero, neg_zero]

/-- A word with a **repeated** letter (in positions `1` and `3`) vanishes. -/
theorem stWordSF_dup_outer (p q : ℕ × Fin 2) (l : SFWord) :
    stWordSF (p :: q :: p :: l) = 0 := by
  rw [stWordSF_cons, stWordSF_cons, stWordSF_cons, ← mul_assoc, sfGen_swap p q, neg_mul,
    mul_assoc, ← mul_assoc (ι QSF (Finsupp.single p (1 : ℂ))), sfGen_sq, zero_mul, mul_zero,
    neg_zero]

/-! ## §2  The vertex operator of a two-letter word `Gᵃᵇ = χᵃ₋ₖ₋₁χᵇ₋₁|0⟩` -/

/-- The `k = 1` generator field is the plain formal derivative of `χᵃ`. -/
theorem sfGenField_one_apply (a : Fin 2) (q : ℤ) :
    sfGenField a 1 q = ((q + 1 : ℤ)) • chi a (q + 1) := by
  rw [sfGenField]
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul, Function.iterate_one]
  rfl

/-- `Y(χᵃ₋ₖ₋₁χᵇ₋₁|0⟩, z) = :(∂^{(k)}χᵃ)(z) χᵇ(z):` at the odd/odd Koszul sign `-1`. -/
theorem YSF_two_letter (a b : Fin 2) (k : ℕ) :
    YSF (stWordSF [(k, a), ((0 : ℕ), b)])
      = nprodε (-1 : ℂ) (sfGenField_isField a k) (chi_isField b) := by
  have h2 : YwordSF [((0 : ℕ), b)] = chi b := by
    rw [YwordSF_singleton]
    exact sfGenField_zero_eq b
  rw [YSF_word, YwordSF_cons]
  simp only [List.length_cons, List.length_nil]
  exact nprodε_congr' _ _ _ _ _ rfl h2

/-! ## §3  The same-flavour square vanishes **exactly**

Abe's `Ē² = F̄² = 0` in `A₂(W(2))` (§3.3) are here proved in the strictly stronger form
`E₍₋₁₎E = 0` and `F₍₋₁₎F = 0` **in `FockSF` itself** — no quotient, no `O₂`.  The reason is
structural: `E = e₍₋₂₎e` and `F = f₍₋₂₎f` involve only *one* of the two fermions, and
`ωᵃᵃ = 0`, so nothing inside the same-flavour sector can ever contract.  A `4`-letter word of
weight `6` in a single flavour would need four *distinct* levels `k₁+…+k₄ = 6` with
`kᵢ ≥ 1`, i.e. at least `1+2+3+4 = 10`; there is no room. -/

/-- **The kill criterion.**  If every mode `χᵃ_p` with `p ≥ -1` annihilates `x`, then the
`(-1)`-st product of the same-flavour generator `Gᵃᵃ = χᵃ₋₂χᵃ₋₁|0⟩` with `x` vanishes.

Both branches of the normal ordering are covered by the *same* hypothesis: for `m ≥ 0` the
inner operator is `χᵃ_{m-1}` (and `m - 1 ≥ -1`), for `m < 0` it is `χᵃ_{-m-2}` (and
`-m - 2 ≥ -1`). -/
theorem selfProd_neg_one_eq_zero (a : Fin 2) (x : FockSF)
    (hx : ∀ p : ℤ, -1 ≤ p → chiM a p x = 0) :
    mode (YSF (stWordSF [((1 : ℕ), a), ((0 : ℕ), a)])) (-1) x = 0 := by
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 from by norm_num, YSF_two_letter, nprodε_apply]
  have hzero : ∀ m : ℤ,
      normalOrderedε (-1 : ℂ) (sfGenField a 1) (chi a) m ((0 : ℤ) - m) x = 0 := by
    intro m
    rw [normalOrderedε_apply]
    by_cases hm : (0 : ℤ) ≤ m
    · have h1 : chi a ((0 : ℤ) - m) x = 0 := by
        rw [chi_eq_chiM]
        exact hx _ (by omega)
      rw [if_pos hm, Module.End.mul_apply, h1, map_zero]
    · have h2 : sfGenField a 1 m x = 0 := by
        rw [sfGenField_one_apply, LinearMap.smul_apply,
          show chi a (m + 1) x = 0 from by rw [chi_eq_chiM]; exact hx _ (by omega), smul_zero]
      rw [if_neg hm, LinearMap.smul_apply, Module.End.mul_apply, h2, map_zero, smul_zero]
  rw [finsum_congr hzero, finsum_zero]

/-- Every mode `χᵃ_p` with `p ≥ -1` kills the same-flavour generator `Gᵃᵃ = χᵃ₋₂χᵃ₋₁|0⟩`:
for `p ≥ 0` because nothing contracts (`chiM_nonneg_sameFlavour`), for `p = -1` because the
created letter `(0,a)` is already present (`stWordSF_dup_outer`). -/
theorem chiM_ge_neg_one_gen_self (a : Fin 2) (p : ℤ) (hp : -1 ≤ p) :
    chiM a p (stWordSF [((1 : ℕ), a), ((0 : ℕ), a)]) = 0 := by
  rcases eq_or_lt_of_le hp with h | h
  · rw [← h, show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 from by norm_num, chiM_cons]
    exact stWordSF_dup_outer ((0 : ℕ), a) ((1 : ℕ), a) []
  · refine chiM_nonneg_sameFlavour a _ ?_ (by omega)
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq'
    · rfl
    · rcases List.mem_cons.1 hq' with rfl | hq''
      · rfl
      · exact absurd hq'' (List.not_mem_nil)

/-! ## §4  `Ē² = 0` and `F̄² = 0` -/

/-- The classes of Abe's four generators in `A₂(W(2)) = W(2)/C₂(W(2))`. -/
noncomputable def wbar : A₂ tripletW2 := mk₂ tripletW2 abeOmega

/-- `Ē = [E] ∈ A₂(W(2))`. -/
noncomputable def Ebar : A₂ tripletW2 := mk₂ tripletW2 abeE

/-- `H̄ = [H] ∈ A₂(W(2))`. -/
noncomputable def Hbar : A₂ tripletW2 := mk₂ tripletW2 abeH

/-- `F̄ = [F] ∈ A₂(W(2))`. -/
noncomputable def Fbar : A₂ tripletW2 := mk₂ tripletW2 abeF

/-- `E₍₋₁₎E = 0` in the ambient Fock space. -/
theorem abeE_selfProd_coe :
    mode (YSF ((abeE : evenOdd QSF (0 : ZMod 2)) : FockSF)) (-1)
      ((abeE : evenOdd QSF (0 : ZMod 2)) : FockSF) = 0 := by
  rw [abeE_coe]
  exact selfProd_neg_one_eq_zero 1 _ (chiM_ge_neg_one_gen_self 1)

/-- `F₍₋₁₎F = 0` in the ambient Fock space. -/
theorem abeF_selfProd_coe :
    mode (YSF ((abeF : evenOdd QSF (0 : ZMod 2)) : FockSF)) (-1)
      ((abeF : evenOdd QSF (0 : ZMod 2)) : FockSF) = 0 := by
  rw [abeF_coe]
  exact selfProd_neg_one_eq_zero 0 _ (chiM_ge_neg_one_gen_self 0)

/-- **`E₍₋₁₎E = 0` in `W(2)`** — an exact identity, not a congruence. -/
theorem abeE_poissonMul_abeE : poissonMul tripletW2 abeE abeE = 0 := by
  apply Subtype.ext
  simpa using abeE_selfProd_coe

/-- **`F₍₋₁₎F = 0` in `W(2)`** — an exact identity, not a congruence. -/
theorem abeF_poissonMul_abeF : poissonMul tripletW2 abeF abeF = 0 := by
  apply Subtype.ext
  simpa using abeF_selfProd_coe

/-- **Abe §3.3, first relation: `Ē² = 0` in `A₂(W(2))`.** -/
theorem Ebar_sq : Ebar * Ebar = 0 := by
  rw [Ebar, A₂_mul_mk, abeE_poissonMul_abeE, map_zero]

/-- **Abe §3.3, second relation: `F̄² = 0` in `A₂(W(2))`.** -/
theorem Fbar_sq : Fbar * Fbar = 0 := by
  rw [Fbar, A₂_mul_mk, abeF_poissonMul_abeF, map_zero]

/-- `Ē` is nilpotent of index `2`. -/
theorem Ebar_isNilpotent : IsNilpotent Ebar := ⟨2, by rw [pow_two]; exact Ebar_sq⟩

/-- `F̄` is nilpotent of index `2`. -/
theorem Fbar_isNilpotent : IsNilpotent Fbar := ⟨2, by rw [pow_two]; exact Fbar_sq⟩

/-! ## §5  The one-contraction product formula

For `x` in the *mixed* sector, `Gᵃᵃ₍₋₁₎x` does not vanish: exactly one of the modes
`χᵃ_p` (`p ≥ -1`) can contract against the opposite-flavour letter of `x`.  The following
lemma evaluates the whole normal-ordered sum in that situation.  It says: if `χᵃ_P x = y` is
the *only* surviving contraction, then

  `Gᵃᵃ₍₋₁₎x = (2P + 3) · χᵃ_{-P-3} y`,

the two summands `P + 2` and `P + 1` coming from the `m ≥ 0` and `m < 0` halves of the normal
ordering. -/

/-- `sfGenField a 1` with a complex coefficient. -/
theorem sfGenField_one_apply' (a : Fin 2) (q : ℤ) :
    sfGenField a 1 q = (((q : ℂ) + 1)) • chi a (q + 1) := by
  rw [sfGenField_one_apply, ← Int.cast_smul_eq_zsmul ℂ (q + 1) (chi a (q + 1))]
  push_cast
  rfl

/-- **The one-contraction product formula.**

Hypotheses: `χᵃ_P x = y` is the only surviving *annihilation* (`p ≥ 0`), and the one
`m = 0` normal-ordering term — where `χᵃ₋₁` *creates* a letter and `χᵃ₋₂` creates a second
one — vanishes as well (`hdup`; in practice because the created letter duplicates one already
present).  The `m = -1` term carries the coefficient `m + 1 = 0` and never contributes. -/
theorem selfProd_single_contraction (a : Fin 2) (x y : FockSF) (P : ℤ) (hP : 1 ≤ P)
    (hy : chiM a P x = y)
    (hother : ∀ p : ℤ, 0 ≤ p → p ≠ P → chiM a p x = 0)
    (hdup : chiM a (-2) (chiM a (-1) x) = 0) :
    mode (YSF (stWordSF [((1 : ℕ), a), ((0 : ℕ), a)])) (-1) x
      = ((2 * (P : ℂ) + 3)) • chiM a (-P - 3) y := by
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 from by norm_num, YSF_two_letter, nprodε_apply]
  set g : ℤ → FockSF :=
    fun m => normalOrderedε (-1 : ℂ) (sfGenField a 1) (chi a) m ((0 : ℤ) - m) x with hg
  have hpos : g (P + 1) = (((P : ℂ) + 2)) • chiM a (-P - 3) y := by
    have hchi : chi a ((0 : ℤ) - (P + 1)) x = y := by
      rw [chi_eq_chiM, show -((0 : ℤ) - (P + 1)) - 1 = P from by ring, hy]
    rw [hg]
    simp only []
    rw [normalOrderedε_apply, if_pos (by omega : (0 : ℤ) ≤ P + 1), Module.End.mul_apply, hchi,
      sfGenField_one_apply', LinearMap.smul_apply, chi_eq_chiM,
      show -(P + 1 + 1) - 1 = -P - 3 from by ring]
    congr 1
    push_cast
    ring
  have hneg : g (-P - 2) = (((P : ℂ) + 1)) • chiM a (-P - 3) y := by
    have hchi : chi a (-P - 2 + 1) x = y := by
      rw [chi_eq_chiM, show -(-P - 2 + 1) - 1 = P from by ring, hy]
    rw [hg]
    simp only []
    rw [normalOrderedε_apply, if_neg (by omega : ¬ (0 : ℤ) ≤ -P - 2), LinearMap.smul_apply,
      Module.End.mul_apply, sfGenField_one_apply', LinearMap.smul_apply, hchi, map_smul,
      chi_eq_chiM, show -((0 : ℤ) - (-P - 2)) - 1 = -P - 3 from by ring, smul_smul]
    congr 1
    push_cast
    ring
  have hsupp : Function.support g ⊆ (({P + 1, -P - 2} : Finset ℤ) : Set ℤ) := by
    intro m hm
    by_contra hmem
    refine hm ?_
    have h1 : m ≠ P + 1 := fun h => hmem (by simp [h])
    have h2 : m ≠ -P - 2 := fun h => hmem (by simp [h])
    rw [hg]
    simp only []
    rw [normalOrderedε_apply]
    rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
    · rcases eq_or_lt_of_le (show m ≤ -1 by omega) with hm1 | hm1
      · -- `m = -1`: the coefficient `m + 1` vanishes
        subst hm1
        have hz : sfGenField a 1 (-1) = 0 := by
          rw [sfGenField_one_apply']
          simp
        rw [if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1), LinearMap.smul_apply, Module.End.mul_apply, hz,
          LinearMap.zero_apply, map_zero, smul_zero]
      · -- `m ≤ -2`: a genuine annihilation `χᵃ_{-m-2}`, killed by `hother`
        have hz : sfGenField a 1 m x = 0 := by
          rw [sfGenField_one_apply', LinearMap.smul_apply, chi_eq_chiM,
            hother (-(m + 1) - 1) (by omega) (by omega), smul_zero]
        rw [if_neg (by omega), LinearMap.smul_apply, Module.End.mul_apply, hz, map_zero, smul_zero]
    · -- `m = 0`: the double-creation term, killed by `hdup`
      subst hm0
      have e1 : chi a ((0 : ℤ) - 0) = chiM a (-1) := by rw [chi_eq_chiM]; norm_num
      have e2 : chi a ((0 : ℤ) + 1) = chiM a (-2) := by rw [chi_eq_chiM]; norm_num
      rw [if_pos (le_refl (0 : ℤ)), Module.End.mul_apply, sfGenField_one_apply',
        LinearMap.smul_apply, e1, e2, hdup, smul_zero]
    · -- `m ≥ 1`: a genuine annihilation `χᵃ_{m-1}`, killed by `hother`
      have hz : chi a ((0 : ℤ) - m) x = 0 := by
        rw [chi_eq_chiM]
        exact hother _ (by omega) (by omega)
      rw [if_pos (by omega), Module.End.mul_apply, hz, map_zero]
  rw [finsum_eq_finsetSum_of_support_subset g hsupp,
    Finset.sum_pair (by omega : P + 1 ≠ -P - 2), hpos, hneg, ← add_smul]
  congr 1
  ring

/-! ## §6  Wick contraction on a two-letter word

`χᶜ_p` (`p ≥ 0`) applied to `χᵃ₋ₖ₋₁χᵇ₋ⱼ₋₁|0⟩` contracts against each letter in turn; the two
CAR scalars `ωᶜᵇ` and `ωᶜᵃ` (gated on the mode sum) are the only survivors. -/

/-- Non-negative modes kill the vacuum. -/
theorem chiM_nonneg_nil (c : Fin 2) {p : ℤ} (hp : 0 ≤ p) :
    chiM c p (stWordSF ([] : SFWord)) = 0 :=
  chiM_vacuum c hp

/-- One letter: `χᶜ_p χᵇ₋ⱼ₋₁|0⟩ = ⟨χᶜ,χᵇ⟩_{p,-j-1}|0⟩`. -/
theorem chiM_nonneg_single (c b : Fin 2) (j : ℕ) {p : ℤ} (hp : 0 ≤ p) :
    chiM c p (stWordSF [(j, b)]) = carC c b p (-(j : ℤ) - 1) • stWordSF ([] : SFWord) := by
  rw [← chiM_cons b j [], chiM_swap, chiM_nonneg_nil c hp, map_zero, neg_zero, zero_add]

/-- **Two letters**: `χᶜ_p (χᵃ₋ₖ₋₁χᵇ₋ⱼ₋₁|0⟩) = -⟨χᶜ,χᵇ⟩·χᵃ₋ₖ₋₁|0⟩ + ⟨χᶜ,χᵃ⟩·χᵇ₋ⱼ₋₁|0⟩`. -/
theorem chiM_nonneg_pair (c a b : Fin 2) (k j : ℕ) {p : ℤ} (hp : 0 ≤ p) :
    chiM c p (stWordSF [(k, a), (j, b)])
      = (-carC c b p (-(j : ℤ) - 1)) • stWordSF [(k, a)]
        + carC c a p (-(k : ℤ) - 1) • stWordSF [(j, b)] := by
  rw [← chiM_cons a k [(j, b)], chiM_swap, chiM_nonneg_single c b j hp, map_smul,
    chiM_cons a k [], ← neg_smul]

/-! ### The four contractions used below

`H = ½(G¹⁰ + G⁰¹)` with `G¹⁰ = χ¹₋₂χ⁰₋₁|0⟩` and `G⁰¹ = χ⁰₋₂χ¹₋₁|0⟩`.  Against `E` (flavour `1`)
the surviving contraction is `p = 1` on `G¹⁰` and `p = 2` on `G⁰¹`; against `F` (flavour `0`)
it is `p = 2` on `G¹⁰` and `p = 1` on `G⁰¹`. -/

/-- `χ¹_p G¹⁰ = δ_{p,1}·χ¹₋₂|0⟩`  (`p ≥ 0`). -/
theorem chiM_one_G10 {p : ℤ} (hp : 0 ≤ p) :
    chiM 1 p (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = (if p = 1 then (1 : ℂ) else 0) • stWordSF [((1 : ℕ), (1 : Fin 2))] := by
  rw [chiM_nonneg_pair 1 1 0 1 0 hp, carC_self, zero_smul, add_zero, carC_apply]
  by_cases h : p = 1
  · rw [if_pos (by omega : p + (-((0 : ℕ) : ℤ) - 1) = 0), if_pos h, h]
    norm_num
  · rw [if_neg (by omega : ¬ (p + (-((0 : ℕ) : ℤ) - 1) = 0)), if_neg h, neg_zero]

/-- `χ¹_p G⁰¹ = -2δ_{p,2}·χ¹₋₁|0⟩`  (`p ≥ 0`). -/
theorem chiM_one_G01 {p : ℤ} (hp : 0 ≤ p) :
    chiM 1 p (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])
      = (if p = 2 then (-2 : ℂ) else 0) • stWordSF [((0 : ℕ), (1 : Fin 2))] := by
  rw [chiM_nonneg_pair 1 0 1 1 0 hp, carC_self, neg_zero, zero_smul, zero_add, carC_apply]
  by_cases h : p = 2
  · rw [if_pos (by omega : p + (-((1 : ℕ) : ℤ) - 1) = 0), if_pos h, h]
    norm_num
  · rw [if_neg (by omega : ¬ (p + (-((1 : ℕ) : ℤ) - 1) = 0)), if_neg h]

/-- `χ⁰_p G¹⁰ = 2δ_{p,2}·χ⁰₋₁|0⟩`  (`p ≥ 0`). -/
theorem chiM_zero_G10 {p : ℤ} (hp : 0 ≤ p) :
    chiM 0 p (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = (if p = 2 then (2 : ℂ) else 0) • stWordSF [((0 : ℕ), (0 : Fin 2))] := by
  rw [chiM_nonneg_pair 0 1 0 1 0 hp, carC_self, neg_zero, zero_smul, zero_add, carC_apply]
  by_cases h : p = 2
  · rw [if_pos (by omega : p + (-((1 : ℕ) : ℤ) - 1) = 0), if_pos h, h]
    norm_num
  · rw [if_neg (by omega : ¬ (p + (-((1 : ℕ) : ℤ) - 1) = 0)), if_neg h]

/-- `χ⁰_p G⁰¹ = -δ_{p,1}·χ⁰₋₂|0⟩`  (`p ≥ 0`). -/
theorem chiM_zero_G01 {p : ℤ} (hp : 0 ≤ p) :
    chiM 0 p (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])
      = (if p = 1 then (-1 : ℂ) else 0) • stWordSF [((1 : ℕ), (0 : Fin 2))] := by
  rw [chiM_nonneg_pair 0 0 1 1 0 hp, carC_self, zero_smul, add_zero, carC_apply]
  by_cases h : p = 1
  · rw [if_pos (by omega : p + (-((0 : ℕ) : ℤ) - 1) = 0), if_pos h, h]
    norm_num
  · rw [if_neg (by omega : ¬ (p + (-((0 : ℕ) : ℤ) - 1) = 0)), if_neg h, neg_zero]

/-! ## §7  The four products `E₍₋₁₎G^{ab}`, `F₍₋₁₎G^{ab}` -/

/-- Creation with a convenient index. -/
theorem chiM_create (a : Fin 2) (k : ℕ) (n : ℤ) (hn : n = -(k : ℤ) - 1) (l : SFWord) :
    chiM a n (stWordSF l) = stWordSF ((k, a) :: l) := by
  rw [hn]; exact chiM_cons a k l

/-- `E₍₋₁₎G¹⁰ = 5·χ¹₋₄χ¹₋₂|0⟩`. -/
theorem E_prod_G10 :
    mode (YSF (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])) (-1)
        (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = (5 : ℂ) • stWordSF [((3 : ℕ), (1 : Fin 2)), ((1 : ℕ), (1 : Fin 2))] := by
  have hdup : chiM 1 (-2) (chiM 1 (-1)
      (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])) = 0 := by
    rw [chiM_create 1 0 (-1) (by norm_num), chiM_create 1 1 (-2) (by norm_num)]
    exact stWordSF_dup_outer ((1 : ℕ), (1 : Fin 2)) ((0 : ℕ), (1 : Fin 2)) [((0 : ℕ), (0 : Fin 2))]
  have h := selfProd_single_contraction 1 _ (stWordSF [((1 : ℕ), (1 : Fin 2))]) 1 le_rfl
    (by simpa using chiM_one_G10 (p := 1) (by norm_num))
    (fun p hp hne => by simpa [hne] using chiM_one_G10 (p := p) hp) hdup
  rw [h, chiM_create 1 3 (-1 - 3) (by norm_num)]
  norm_num

/-- `E₍₋₁₎G⁰¹ = -14·χ¹₋₅χ¹₋₁|0⟩`. -/
theorem E_prod_G01 :
    mode (YSF (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])) (-1)
        (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])
      = (-14 : ℂ) • stWordSF [((4 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] := by
  have hdup : chiM 1 (-2) (chiM 1 (-1)
      (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])) = 0 := by
    rw [chiM_create 1 0 (-1) (by norm_num),
      stWordSF_dup_outer ((0 : ℕ), (1 : Fin 2)) ((1 : ℕ), (0 : Fin 2)) [], map_zero]
  have h := selfProd_single_contraction 1 _ ((-2 : ℂ) • stWordSF [((0 : ℕ), (1 : Fin 2))]) 2
    (by norm_num) (by simpa using chiM_one_G01 (p := 2) (by norm_num))
    (fun p hp hne => by simpa [hne] using chiM_one_G01 (p := p) hp) hdup
  rw [h, map_smul, chiM_create 1 4 (-2 - 3) (by norm_num), smul_smul]
  norm_num

/-- `F₍₋₁₎G¹⁰ = 14·χ⁰₋₅χ⁰₋₁|0⟩`. -/
theorem F_prod_G10 :
    mode (YSF (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])) (-1)
        (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = (14 : ℂ) • stWordSF [((4 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))] := by
  have hdup : chiM 0 (-2) (chiM 0 (-1)
      (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])) = 0 := by
    rw [chiM_create 0 0 (-1) (by norm_num),
      stWordSF_dup_outer ((0 : ℕ), (0 : Fin 2)) ((1 : ℕ), (1 : Fin 2)) [], map_zero]
  have h := selfProd_single_contraction 0 _ ((2 : ℂ) • stWordSF [((0 : ℕ), (0 : Fin 2))]) 2
    (by norm_num) (by simpa using chiM_zero_G10 (p := 2) (by norm_num))
    (fun p hp hne => by simpa [hne] using chiM_zero_G10 (p := p) hp) hdup
  rw [h, map_smul, chiM_create 0 4 (-2 - 3) (by norm_num), smul_smul]
  norm_num

/-- `F₍₋₁₎G⁰¹ = -5·χ⁰₋₄χ⁰₋₂|0⟩`. -/
theorem F_prod_G01 :
    mode (YSF (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])) (-1)
        (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])
      = (-5 : ℂ) • stWordSF [((3 : ℕ), (0 : Fin 2)), ((1 : ℕ), (0 : Fin 2))] := by
  have hdup : chiM 0 (-2) (chiM 0 (-1)
      (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])) = 0 := by
    rw [chiM_create 0 0 (-1) (by norm_num), chiM_create 0 1 (-2) (by norm_num)]
    exact stWordSF_dup_outer ((1 : ℕ), (0 : Fin 2)) ((0 : ℕ), (0 : Fin 2)) [((0 : ℕ), (1 : Fin 2))]
  have h := selfProd_single_contraction 0 _ ((-1 : ℂ) • stWordSF [((1 : ℕ), (0 : Fin 2))]) 1 le_rfl
    (by simpa using chiM_zero_G01 (p := 1) (by norm_num))
    (fun p hp hne => by simpa [hne] using chiM_zero_G01 (p := p) hp) hdup
  rw [h, map_smul, chiM_create 0 3 (-1 - 3) (by norm_num), smul_smul]
  norm_num

/-! ## §8  The weight-`6` same-flavour states are translates, hence lie in `O₂`

`L₋₁v = v₍₋₂₎𝟙` is literally an `O₂`-generator.  The two same-flavour weight-`6` two-letter
states `χᵃ₋₅χᵃ₋₁|0⟩` and `χᵃ₋₄χᵃ₋₂|0⟩` are both translates of weight-`5` states of `W(2)`:

  `L₋₁(χᵃ₋₃χᵃ₋₂|0⟩) = 3·χᵃ₋₄χᵃ₋₂|0⟩`,
  `L₋₁(χᵃ₋₄χᵃ₋₁|0⟩) = χᵃ₋₄χᵃ₋₂|0⟩ + 4·χᵃ₋₅χᵃ₋₁|0⟩`,

so both lie in `O₂(W(2))`. -/

/-- `T` on a two-letter word: the derivation property `T(xy) = xTy + (Tx)y` with
`T(χᵃ₋ₖ₋₁) = (k+1)χᵃ₋ₖ₋₂`. -/
theorem T_stWordSF_pair (p q : ℕ × Fin 2) :
    SympFerm.T (stWordSF [p, q])
      = ((q.1 : ℂ) + 1) • stWordSF [p, (q.1 + 1, q.2)]
        + ((p.1 : ℂ) + 1) • stWordSF [(p.1 + 1, p.2), q] := by
  rw [stWordSF_pair, T_mul, T_ι, T_ι, shiftMap_single, shiftMap_single, one_smul, one_smul,
    map_smul, map_smul, mul_smul_comm, smul_mul_assoc, ← stWordSF_pair, ← stWordSF_pair]

/-- The same, with the components spelled out. -/
theorem T_stWordSF_pair' (k j : ℕ) (a b : Fin 2) :
    SympFerm.T (stWordSF [(k, a), (j, b)])
      = ((j : ℂ) + 1) • stWordSF [(k, a), (j + 1, b)]
        + ((k : ℂ) + 1) • stWordSF [(k + 1, a), (j, b)] :=
  T_stWordSF_pair (k, a) (j, b)

/-- A two-letter word state, as an element of `W(2)`. -/
noncomputable def w2pair (p q : ℕ × Fin 2) : evenOdd QSF (0 : ZMod 2) :=
  ⟨stWordSF [p, q], stWord_two_mem_even p q⟩

@[simp] theorem w2pair_coe (p q : ℕ × Fin 2) :
    ((w2pair p q : evenOdd QSF (0 : ZMod 2)) : FockSF) = stWordSF [p, q] := rfl

/-- `T u = u₍₋₂₎𝟙` is literally a generator of `O₂`. -/
theorem T_mem_O₂ (u : evenOdd QSF (0 : ZMod 2)) :
    tripletW2.toPreVertexAlgebra.T u ∈ O₂ tripletW2 :=
  Submodule.subset_span ⟨u, tripletW2.vacuum, rfl⟩

/-- The translation operator of `W(2)` is the ambient one. -/
theorem tripletW2_T_coe (u : evenOdd QSF (0 : ZMod 2)) :
    ((tripletW2.toPreVertexAlgebra.T u : evenOdd QSF (0 : ZMod 2)) : FockSF)
      = SympFerm.T ((u : evenOdd QSF (0 : ZMod 2)) : FockSF) := by
  rw [show tripletW2.toPreVertexAlgebra.T u = tripletW2.L (-1) u from by
        rw [VertexOperatorAlgebra.T_eq_Lneg1], tripletW2_L_coe, LSF_neg_one_eq_T]

/-- `L₋₁(χᵃ₋₃χᵃ₋₂|0⟩) = 3·χᵃ₋₄χᵃ₋₂|0⟩` (the other term has a repeated letter). -/
theorem T_w2pair_21 (a : Fin 2) :
    tripletW2.toPreVertexAlgebra.T (w2pair ((2 : ℕ), a) ((1 : ℕ), a))
      = (3 : ℂ) • w2pair ((3 : ℕ), a) ((1 : ℕ), a) := by
  apply Subtype.ext
  have hL : ((tripletW2.toPreVertexAlgebra.T (w2pair ((2 : ℕ), a) ((1 : ℕ), a)) :
        evenOdd QSF (0 : ZMod 2)) : FockSF)
      = (2 : ℂ) • stWordSF [((2 : ℕ), a), ((2 : ℕ), a)]
        + (3 : ℂ) • stWordSF [((3 : ℕ), a), ((1 : ℕ), a)] := by
    rw [tripletW2_T_coe, w2pair_coe, T_stWordSF_pair']
    norm_num
  rw [hL, stWordSF_pair_self, smul_zero, zero_add]
  rfl

/-- `L₋₁(χᵃ₋₄χᵃ₋₁|0⟩) = χᵃ₋₄χᵃ₋₂|0⟩ + 4·χᵃ₋₅χᵃ₋₁|0⟩`. -/
theorem T_w2pair_30 (a : Fin 2) :
    tripletW2.toPreVertexAlgebra.T (w2pair ((3 : ℕ), a) ((0 : ℕ), a))
      = w2pair ((3 : ℕ), a) ((1 : ℕ), a) + (4 : ℂ) • w2pair ((4 : ℕ), a) ((0 : ℕ), a) := by
  apply Subtype.ext
  rw [tripletW2_T_coe, w2pair_coe, T_stWordSF_pair']
  norm_num

/-- `χᵃ₋₄χᵃ₋₂|0⟩ ∈ O₂(W(2))`. -/
theorem w2pair_31_mem_O₂ (a : Fin 2) : w2pair ((3 : ℕ), a) ((1 : ℕ), a) ∈ O₂ tripletW2 := by
  have h := T_mem_O₂ (w2pair ((2 : ℕ), a) ((1 : ℕ), a))
  rw [T_w2pair_21 a] at h
  have hx : w2pair ((3 : ℕ), a) ((1 : ℕ), a)
      = ((3 : ℂ)⁻¹) • ((3 : ℂ) • w2pair ((3 : ℕ), a) ((1 : ℕ), a)) := by
    rw [smul_smul]
    norm_num
  rw [hx]
  exact Submodule.smul_mem _ _ h

/-- `χᵃ₋₅χᵃ₋₁|0⟩ ∈ O₂(W(2))`. -/
theorem w2pair_40_mem_O₂ (a : Fin 2) : w2pair ((4 : ℕ), a) ((0 : ℕ), a) ∈ O₂ tripletW2 := by
  have h := T_mem_O₂ (w2pair ((3 : ℕ), a) ((0 : ℕ), a))
  rw [T_w2pair_30 a] at h
  have h4 : (4 : ℂ) • w2pair ((4 : ℕ), a) ((0 : ℕ), a) ∈ O₂ tripletW2 := by
    have hs := Submodule.sub_mem (O₂ tripletW2) h (w2pair_31_mem_O₂ a)
    simpa using hs
  have hx : w2pair ((4 : ℕ), a) ((0 : ℕ), a)
      = ((4 : ℂ)⁻¹) • ((4 : ℂ) • w2pair ((4 : ℕ), a) ((0 : ℕ), a)) := by
    rw [smul_smul]
    norm_num
  rw [hx]
  exact Submodule.smul_mem _ _ h4

/-! ## §9  `Ē·H̄ = 0` and `H̄·F̄ = 0` -/

/-- **`E₍₋₁₎H = (5/2)·χ¹₋₄χ¹₋₂|0⟩ - 7·χ¹₋₅χ¹₋₁|0⟩`** — the explicit weight-`6` vector. -/
theorem abeE_poissonMul_abeH :
    poissonMul tripletW2 abeE abeH
      = ((5 : ℂ) / 2) • w2pair ((3 : ℕ), (1 : Fin 2)) ((1 : ℕ), (1 : Fin 2))
        + (-7 : ℂ) • w2pair ((4 : ℕ), (1 : Fin 2)) ((0 : ℕ), (1 : Fin 2)) := by
  apply Subtype.ext
  rw [poissonMul_def, tripletW2_smul_coe, abeE_coe, abeH_coe, map_smul, map_add,
    E_prod_G10, E_prod_G01]
  simp only [w2pair_coe, Submodule.coe_add, SetLike.val_smul]
  module

/-- **`F₍₋₁₎H = 7·χ⁰₋₅χ⁰₋₁|0⟩ - (5/2)·χ⁰₋₄χ⁰₋₂|0⟩`**. -/
theorem abeF_poissonMul_abeH :
    poissonMul tripletW2 abeF abeH
      = (7 : ℂ) • w2pair ((4 : ℕ), (0 : Fin 2)) ((0 : ℕ), (0 : Fin 2))
        + (-(5 : ℂ) / 2) • w2pair ((3 : ℕ), (0 : Fin 2)) ((1 : ℕ), (0 : Fin 2)) := by
  apply Subtype.ext
  rw [poissonMul_def, tripletW2_smul_coe, abeF_coe, abeH_coe, map_smul, map_add,
    F_prod_G10, F_prod_G01]
  simp only [w2pair_coe, Submodule.coe_add, SetLike.val_smul]
  module

/-- `E₍₋₁₎H ∈ O₂(W(2))`: both weight-`6` basis vectors are translates (§8). -/
theorem abeE_poissonMul_abeH_mem_O₂ : poissonMul tripletW2 abeE abeH ∈ O₂ tripletW2 := by
  rw [abeE_poissonMul_abeH]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (w2pair_31_mem_O₂ 1))
    (Submodule.smul_mem _ _ (w2pair_40_mem_O₂ 1))

/-- `F₍₋₁₎H ∈ O₂(W(2))`. -/
theorem abeF_poissonMul_abeH_mem_O₂ : poissonMul tripletW2 abeF abeH ∈ O₂ tripletW2 := by
  rw [abeF_poissonMul_abeH]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (w2pair_40_mem_O₂ 0))
    (Submodule.smul_mem _ _ (w2pair_31_mem_O₂ 0))

/-- **Abe §3.3, third relation: `H̄·Ē = 0` in `A₂(W(2))`.** -/
theorem Ebar_mul_Hbar : Ebar * Hbar = 0 := by
  rw [Ebar, Hbar, A₂_mul_mk]
  exact (mk₂_eq_zero_iff tripletW2).2 abeE_poissonMul_abeH_mem_O₂

/-- **Abe §3.3, fourth relation: `H̄·F̄ = 0` in `A₂(W(2))`.** -/
theorem Fbar_mul_Hbar : Fbar * Hbar = 0 := by
  rw [Fbar, Hbar, A₂_mul_mk]
  exact (mk₂_eq_zero_iff tripletW2).2 abeF_poissonMul_abeH_mem_O₂

/-- `H̄·Ē = 0` (the commuted form). -/
theorem Hbar_mul_Ebar : Hbar * Ebar = 0 := by rw [mul_comm]; exact Ebar_mul_Hbar

/-- `H̄·F̄ = 0` (the commuted form). -/
theorem Hbar_mul_Fbar : Hbar * Fbar = 0 := by rw [mul_comm]; exact Fbar_mul_Hbar

/-! ## §10  The general `Gᵃᵇ₍₋₁₎` machinery

`Y(Gᵃᵇ, z) = :(∂χᵃ)(z)χᵇ(z):` at Koszul sign `-1`, so

  `Gᵃᵇ₍₋₁₎x = Σ_{m ∈ ℤ} gTerm a b x m`,
  `gTerm a b x m = (m+1)·χᵃ_{-m-2}(χᵇ_{m-1}x)`      for `m ≥ 0`,
  `gTerm a b x m = -(m+1)·χᵇ_{m-1}(χᵃ_{-m-2}x)`      for `m < 0`.

Reindexing (`p = m-1 ≥ 0` in the first half, `p = -m-2 ≥ 0` in the second, the `m = -1` term
having coefficient `0`) this is the **master formula**

  `Gᵃᵇ₍₋₁₎x = χᵃ₋₂(χᵇ₋₁x) + Σ_{p≥0} (p+2)·χᵃ_{-p-3}(χᵇ_p x) + Σ_{p≥0} (p+1)·χᵇ_{-p-3}(χᵃ_p x)`,

the first term being the "no-contraction" (word-concatenation) term and the two sums the
Wick contractions.  Everything below evaluates this on explicit `x`. -/

/-- The `m`-th normal-ordering term of `Gᵃᵇ₍₋₁₎x`. -/
noncomputable def gTerm (a b : Fin 2) (x : FockSF) (m : ℤ) : FockSF :=
  normalOrderedε (-1 : ℂ) (sfGenField a 1) (chi b) m ((0 : ℤ) - m) x

/-- `Gᵃᵇ₍₋₁₎x` is the (finite) sum of the `gTerm`s. -/
theorem genProd_eq_finsum (a b : Fin 2) (x : FockSF) :
    mode (YSF (stWordSF [((1 : ℕ), a), ((0 : ℕ), b)])) (-1) x = ∑ᶠ m : ℤ, gTerm a b x m := by
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 from by norm_num, YSF_two_letter, nprodε_apply]
  rfl

/-- The `m ≥ 0` branch. -/
theorem gTerm_pos (a b : Fin 2) (x : FockSF) {m : ℤ} (hm : 0 ≤ m) :
    gTerm a b x m = (((m : ℂ) + 1)) • chiM a (-m - 2) (chiM b (m - 1) x) := by
  rw [gTerm, normalOrderedε_apply, if_pos hm, Module.End.mul_apply, sfGenField_one_apply',
    LinearMap.smul_apply, chi_eq_chiM, chi_eq_chiM,
    show -(m + 1) - 1 = -m - 2 from by ring, show -((0 : ℤ) - m) - 1 = m - 1 from by ring]

/-- The `m < 0` branch. -/
theorem gTerm_neg (a b : Fin 2) (x : FockSF) {m : ℤ} (hm : m < 0) :
    gTerm a b x m = (-((m : ℂ) + 1)) • chiM b (m - 1) (chiM a (-m - 2) x) := by
  rw [gTerm, normalOrderedε_apply, if_neg (by omega), LinearMap.smul_apply, Module.End.mul_apply,
    sfGenField_one_apply', LinearMap.smul_apply, map_smul, chi_eq_chiM, chi_eq_chiM,
    show -(m + 1) - 1 = -m - 2 from by ring, show -((0 : ℤ) - m) - 1 = m - 1 from by ring,
    smul_smul]
  congr 1
  ring

/-- The `m = -1` term always vanishes: its coefficient is `m + 1 = 0`. -/
theorem gTerm_neg_one (a b : Fin 2) (x : FockSF) : gTerm a b x (-1) = 0 := by
  rw [gTerm_neg a b x (by norm_num)]
  norm_num

/-- A `gTerm` vanishes as soon as the relevant *annihilation* does. -/
theorem gTerm_vanish (a b : Fin 2) (x : FockSF) (m : ℤ)
    (hb : 0 ≤ m → chiM b (m - 1) x = 0)
    (ha : m ≤ -2 → chiM a (-m - 2) x = 0) : gTerm a b x m = 0 := by
  rcases le_or_gt 0 m with h | h
  · rw [gTerm_pos a b x h, hb h, map_zero, smul_zero]
  · rcases eq_or_lt_of_le (show m ≤ -1 by omega) with h1 | h1
    · rw [h1]; exact gTerm_neg_one a b x
    · rw [gTerm_neg a b x (by omega), ha (by omega), map_zero, smul_zero]

/-- `Gᵃᵇ₍₋₁₎x` as a **finite** sum, once a finset containing the support is known. -/
theorem genProd_of_support (a b : Fin 2) (x : FockSF) (S : Finset ℤ)
    (h : ∀ m : ℤ, m ∉ S → gTerm a b x m = 0) :
    mode (YSF (stWordSF [((1 : ℕ), a), ((0 : ℕ), b)])) (-1) x = ∑ m ∈ S, gTerm a b x m := by
  rw [genProd_eq_finsum]
  refine finsum_eq_finsetSum_of_support_subset _ ?_
  intro m hm
  by_contra hmem
  exact hm (h m (by simpa using hmem))

/-! ## §11  The five weight-`6` products

Notation for the weight-`6` two-letter words:
`A₁ = χ¹₋₅χ⁰₋₁|0⟩`, `B₁ = χ⁰₋₄χ¹₋₂|0⟩`, `C₁ = χ¹₋₄χ⁰₋₂|0⟩`, `D₁ = χ⁰₋₅χ¹₋₁|0⟩`,
and `N = χ¹₋₂χ⁰₋₁χ⁰₋₂χ¹₋₁|0⟩`, `N' = χ¹₋₂χ¹₋₁χ⁰₋₂χ⁰₋₁|0⟩` (with `N = -N'`). -/

/-! ### The contraction values at their single surviving mode -/

/-- `χ¹_p F = δ_{p,1}·χ⁰₋₂|0⟩ - 2δ_{p,2}·χ⁰₋₁|0⟩`  (`p ≥ 0`). -/
theorem chiM_one_F {p : ℤ} (hp : 0 ≤ p) :
    chiM 1 p (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = (if p = 1 then (1 : ℂ) else 0) • stWordSF [((1 : ℕ), (0 : Fin 2))]
        + (if p = 2 then (-2 : ℂ) else 0) • stWordSF [((0 : ℕ), (0 : Fin 2))] := by
  rw [chiM_nonneg_pair 1 0 0 1 0 hp, carC_apply, carC_apply]
  congr 1
  · by_cases h : p = 1
    · rw [if_pos (by omega : p + (-((0 : ℕ) : ℤ) - 1) = 0), if_pos h, h]
      norm_num
    · rw [if_neg (by omega : ¬ (p + (-((0 : ℕ) : ℤ) - 1) = 0)), if_neg h, neg_zero]
  · by_cases h : p = 2
    · rw [if_pos (by omega : p + (-((1 : ℕ) : ℤ) - 1) = 0), if_pos h, h]
      norm_num
    · rw [if_neg (by omega : ¬ (p + (-((1 : ℕ) : ℤ) - 1) = 0)), if_neg h]

theorem chiM_one_G10_at_one :
    chiM 1 1 (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = stWordSF [((1 : ℕ), (1 : Fin 2))] := by
  rw [chiM_one_G10 (p := 1) (by norm_num)]; norm_num

theorem chiM_zero_G10_at_two :
    chiM 0 2 (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = (2 : ℂ) • stWordSF [((0 : ℕ), (0 : Fin 2))] := by
  rw [chiM_zero_G10 (p := 2) (by norm_num)]; norm_num

theorem chiM_one_G01_at_two :
    chiM 1 2 (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])
      = (-2 : ℂ) • stWordSF [((0 : ℕ), (1 : Fin 2))] := by
  rw [chiM_one_G01 (p := 2) (by norm_num)]; norm_num

theorem chiM_zero_G01_at_one :
    chiM 0 1 (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])
      = (-1 : ℂ) • stWordSF [((1 : ℕ), (0 : Fin 2))] := by
  rw [chiM_zero_G01 (p := 1) (by norm_num)]; norm_num

theorem chiM_one_F_at_one :
    chiM 1 1 (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = stWordSF [((1 : ℕ), (0 : Fin 2))] := by
  rw [chiM_one_F (p := 1) (by norm_num)]; norm_num

theorem chiM_one_F_at_two :
    chiM 1 2 (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = (-2 : ℂ) • stWordSF [((0 : ℕ), (0 : Fin 2))] := by
  rw [chiM_one_F (p := 2) (by norm_num)]; norm_num

/-- `G¹⁰₍₋₁₎G¹⁰ = 8·χ¹₋₅χ⁰₋₁|0⟩ + 2·χ⁰₋₄χ¹₋₂|0⟩`. -/
theorem G10_prod_G10 :
    mode (YSF (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])) (-1)
        (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = (8 : ℂ) • stWordSF [((4 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))]
        + (2 : ℂ) • stWordSF [((3 : ℕ), (0 : Fin 2)), ((1 : ℕ), (1 : Fin 2))] := by
  have hzero : chiM 0 (-1) (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))]) = 0 := by
    rw [chiM_create 0 0 (-1) (by norm_num)]
    exact stWordSF_dup_outer ((0 : ℕ), (0 : Fin 2)) ((1 : ℕ), (1 : Fin 2)) []
  rw [genProd_of_support 1 0 _ ({0, 3, -3} : Finset ℤ) ?_]
  · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      gTerm_pos 1 0 _ (by norm_num : (0 : ℤ) ≤ 0),
      gTerm_pos 1 0 _ (by norm_num : (0 : ℤ) ≤ 3),
      gTerm_neg 1 0 _ (by norm_num : (-3 : ℤ) < 0),
      show ((0 : ℤ) - 1) = -1 from by norm_num, hzero, map_zero, smul_zero, zero_add,
      show ((3 : ℤ) - 1) = 2 from by norm_num, chiM_zero_G10_at_two, map_smul,
      chiM_create 1 4 (-(3 : ℤ) - 2) (by norm_num),
      show ((-3 : ℤ) - 1) = -4 from by norm_num,
      show (-(-3 : ℤ) - 2) = 1 from by norm_num, chiM_one_G10_at_one,
      chiM_create 0 3 (-4 : ℤ) (by norm_num), smul_smul]
    norm_num
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨h0, h3, hm3⟩ := hm
    refine gTerm_vanish 1 0 _ m (fun hmn => ?_) (fun hmn => ?_)
    · rw [chiM_zero_G10 (p := m - 1) (by omega), if_neg (by omega), zero_smul]
    · rw [chiM_one_G10 (p := -m - 2) (by omega), if_neg (by omega), zero_smul]

/-! ### Adjacent transpositions of letters -/

/-- Swapping the first two letters flips the sign. -/
theorem stWordSF_swap12 (p q : ℕ × Fin 2) (l : SFWord) :
    stWordSF (p :: q :: l) = -stWordSF (q :: p :: l) := by
  rw [stWordSF_cons, stWordSF_cons, stWordSF_cons, stWordSF_cons, ← mul_assoc, ← mul_assoc,
    sfGen_swap p q, neg_mul]

/-- Swapping letters `2, 3`. -/
theorem stWordSF_swap23 (r p q : ℕ × Fin 2) (l : SFWord) :
    stWordSF (r :: p :: q :: l) = -stWordSF (r :: q :: p :: l) := by
  rw [stWordSF_cons, stWordSF_cons (rest := q :: p :: l), stWordSF_swap12 p q l, mul_neg]

/-- Swapping letters `3, 4`. -/
theorem stWordSF_swap34 (r s p q : ℕ × Fin 2) (l : SFWord) :
    stWordSF (r :: s :: p :: q :: l) = -stWordSF (r :: s :: q :: p :: l) := by
  rw [stWordSF_cons, stWordSF_cons (rest := s :: q :: p :: l), stWordSF_swap23 s p q l, mul_neg]

/-! ### The remaining four products -/

/-- `G¹⁰₍₋₁₎G⁰¹ = N - 3·χ¹₋₄χ⁰₋₂|0⟩ - 6·χ⁰₋₅χ¹₋₁|0⟩`, `N = χ¹₋₂χ⁰₋₁χ⁰₋₂χ¹₋₁|0⟩`. -/
theorem G10_prod_G01 :
    mode (YSF (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])) (-1)
        (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])
      = stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2)), ((1 : ℕ), (0 : Fin 2)),
            ((0 : ℕ), (1 : Fin 2))]
        + (-3 : ℂ) • stWordSF [((3 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))]
        + (-6 : ℂ) • stWordSF [((4 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] := by
  rw [genProd_of_support 1 0 _ ({0, 2, -4} : Finset ℤ) ?_]
  · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      gTerm_pos 1 0 _ (by norm_num : (0 : ℤ) ≤ 0),
      gTerm_pos 1 0 _ (by norm_num : (0 : ℤ) ≤ 2),
      gTerm_neg 1 0 _ (by norm_num : (-4 : ℤ) < 0),
      show ((0 : ℤ) - 1) = -1 from by norm_num, show (-(0 : ℤ) - 2) = -2 from by norm_num,
      show ((2 : ℤ) - 1) = 1 from by norm_num, show (-(2 : ℤ) - 2) = -4 from by norm_num,
      show ((-4 : ℤ) - 1) = -5 from by norm_num, show (-(-4 : ℤ) - 2) = 2 from by norm_num,
      chiM_create 0 0 (-1 : ℤ) (by norm_num), chiM_zero_G01_at_one, chiM_one_G01_at_two,
      chiM_create 1 1 (-2 : ℤ) (by norm_num), map_smul, map_smul,
      chiM_create 1 3 (-4 : ℤ) (by norm_num), chiM_create 0 4 (-5 : ℤ) (by norm_num)]
    push_cast
    module
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨h0, h2, h4⟩ := hm
    refine gTerm_vanish 1 0 _ m (fun hmn => ?_) (fun hmn => ?_)
    · rw [chiM_zero_G01 (p := m - 1) (by omega), if_neg (by omega), zero_smul]
    · rw [chiM_one_G01 (p := -m - 2) (by omega), if_neg (by omega), zero_smul]

/-- `G⁰¹₍₋₁₎G¹⁰ = N₂ + 3·χ⁰₋₄χ¹₋₂|0⟩ + 6·χ¹₋₅χ⁰₋₁|0⟩`, `N₂ = χ⁰₋₂χ¹₋₁χ¹₋₂χ⁰₋₁|0⟩`. -/
theorem G01_prod_G10 :
    mode (YSF (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])) (-1)
        (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2)), ((1 : ℕ), (1 : Fin 2)),
            ((0 : ℕ), (0 : Fin 2))]
        + (3 : ℂ) • stWordSF [((3 : ℕ), (0 : Fin 2)), ((1 : ℕ), (1 : Fin 2))]
        + (6 : ℂ) • stWordSF [((4 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))] := by
  rw [genProd_of_support 0 1 _ ({0, 2, -4} : Finset ℤ) ?_]
  · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      gTerm_pos 0 1 _ (by norm_num : (0 : ℤ) ≤ 0),
      gTerm_pos 0 1 _ (by norm_num : (0 : ℤ) ≤ 2),
      gTerm_neg 0 1 _ (by norm_num : (-4 : ℤ) < 0),
      show ((0 : ℤ) - 1) = -1 from by norm_num, show (-(0 : ℤ) - 2) = -2 from by norm_num,
      show ((2 : ℤ) - 1) = 1 from by norm_num, show (-(2 : ℤ) - 2) = -4 from by norm_num,
      show ((-4 : ℤ) - 1) = -5 from by norm_num, show (-(-4 : ℤ) - 2) = 2 from by norm_num,
      chiM_create 1 0 (-1 : ℤ) (by norm_num), chiM_one_G10_at_one, chiM_zero_G10_at_two,
      chiM_create 0 1 (-2 : ℤ) (by norm_num), chiM_create 0 3 (-4 : ℤ) (by norm_num), map_smul,
      chiM_create 1 4 (-5 : ℤ) (by norm_num)]
    push_cast
    module
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨h0, h2, h4⟩ := hm
    refine gTerm_vanish 0 1 _ m (fun hmn => ?_) (fun hmn => ?_)
    · rw [chiM_one_G10 (p := m - 1) (by omega), if_neg (by omega), zero_smul]
    · rw [chiM_zero_G10 (p := -m - 2) (by omega), if_neg (by omega), zero_smul]

/-- `G⁰¹₍₋₁₎G⁰¹ = -8·χ⁰₋₅χ¹₋₁|0⟩ - 2·χ¹₋₄χ⁰₋₂|0⟩`. -/
theorem G01_prod_G01 :
    mode (YSF (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])) (-1)
        (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])
      = (-8 : ℂ) • stWordSF [((4 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]
        + (-2 : ℂ) • stWordSF [((3 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))] := by
  have hzero : chiM 1 (-1) (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]) = 0 := by
    rw [chiM_create 1 0 (-1 : ℤ) (by norm_num)]
    exact stWordSF_dup_outer ((0 : ℕ), (1 : Fin 2)) ((1 : ℕ), (0 : Fin 2)) []
  rw [genProd_of_support 0 1 _ ({0, 3, -3} : Finset ℤ) ?_]
  · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      gTerm_pos 0 1 _ (by norm_num : (0 : ℤ) ≤ 0),
      gTerm_pos 0 1 _ (by norm_num : (0 : ℤ) ≤ 3),
      gTerm_neg 0 1 _ (by norm_num : (-3 : ℤ) < 0),
      show ((0 : ℤ) - 1) = -1 from by norm_num,
      show ((3 : ℤ) - 1) = 2 from by norm_num, show (-(3 : ℤ) - 2) = -5 from by norm_num,
      show ((-3 : ℤ) - 1) = -4 from by norm_num, show (-(-3 : ℤ) - 2) = 1 from by norm_num,
      hzero, map_zero, smul_zero, zero_add,
      chiM_one_G01_at_two, chiM_zero_G01_at_one, map_smul, map_smul,
      chiM_create 0 4 (-5 : ℤ) (by norm_num), chiM_create 1 3 (-4 : ℤ) (by norm_num)]
    push_cast
    module
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨h0, h3, h3'⟩ := hm
    refine gTerm_vanish 0 1 _ m (fun hmn => ?_) (fun hmn => ?_)
    · rw [chiM_one_G01 (p := m - 1) (by omega), if_neg (by omega), zero_smul]
    · rw [chiM_zero_G01 (p := -m - 2) (by omega), if_neg (by omega), zero_smul]

/-- `E₍₋₁₎F = N' + 5·χ¹₋₄χ⁰₋₂|0⟩ - 14·χ¹₋₅χ⁰₋₁|0⟩`, `N' = χ¹₋₂χ¹₋₁χ⁰₋₂χ⁰₋₁|0⟩`. -/
theorem E_prod_F :
    mode (YSF (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])) (-1)
        (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2)),
            ((0 : ℕ), (0 : Fin 2))]
        + (5 : ℂ) • stWordSF [((3 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))]
        + (-14 : ℂ) • stWordSF [((4 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))] := by
  rw [genProd_of_support 1 1 _ ({0, 2, 3, -3, -4} : Finset ℤ) ?_]
  · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton,
      gTerm_pos 1 1 _ (by norm_num : (0 : ℤ) ≤ 0),
      gTerm_pos 1 1 _ (by norm_num : (0 : ℤ) ≤ 2),
      gTerm_pos 1 1 _ (by norm_num : (0 : ℤ) ≤ 3),
      gTerm_neg 1 1 _ (by norm_num : (-3 : ℤ) < 0),
      gTerm_neg 1 1 _ (by norm_num : (-4 : ℤ) < 0),
      show ((0 : ℤ) - 1) = -1 from by norm_num, show (-(0 : ℤ) - 2) = -2 from by norm_num,
      show ((2 : ℤ) - 1) = 1 from by norm_num, show (-(2 : ℤ) - 2) = -4 from by norm_num,
      show ((3 : ℤ) - 1) = 2 from by norm_num, show (-(3 : ℤ) - 2) = -5 from by norm_num,
      show ((-3 : ℤ) - 1) = -4 from by norm_num, show (-(-3 : ℤ) - 2) = 1 from by norm_num,
      show ((-4 : ℤ) - 1) = -5 from by norm_num, show (-(-4 : ℤ) - 2) = 2 from by norm_num,
      chiM_create 1 0 (-1 : ℤ) (by norm_num), chiM_one_F_at_one, chiM_one_F_at_two,
      chiM_create 1 1 (-2 : ℤ) (by norm_num), chiM_create 1 3 (-4 : ℤ) (by norm_num), map_smul,
      chiM_create 1 4 (-5 : ℤ) (by norm_num)]
    push_cast
    module
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨h0, h2, h3, h3', h4'⟩ := hm
    refine gTerm_vanish 1 1 _ m (fun hmn => ?_) (fun hmn => ?_)
    · rw [chiM_one_F (p := m - 1) (by omega), if_neg (by omega), if_neg (by omega), zero_smul,
        zero_smul, add_zero]
    · rw [chiM_one_F (p := -m - 2) (by omega), if_neg (by omega), if_neg (by omega), zero_smul,
        zero_smul, add_zero]

/-! ## §12  Assembling `Ē·F̄ = -2·H̄²`

The five products of §7/§11 combine (after the two four-letter words are reordered) into a
pure translate, hence into `O₂`. -/

/-- `mode (YSF ·) (-1)` is linear in the *state* slot: scalars. -/
theorem mode_YSF_left_smul (c : ℂ) (u v : FockSF) :
    mode (YSF (c • u)) (-1) v = c • mode (YSF u) (-1) v := by
  rw [map_smul]; rfl

/-- `mode (YSF ·) (-1)` is linear in the *state* slot: sums. -/
theorem mode_YSF_left_add (u u' v : FockSF) :
    mode (YSF (u + u')) (-1) v = mode (YSF u) (-1) v + mode (YSF u') (-1) v := by
  rw [map_add]; rfl

/-- Bilinear expansion of `(c(u₁+u₂))₍₋₁₎(d(v₁+v₂))`. -/
theorem mode_YSF_bilin_expand (c d : ℂ) (u₁ u₂ v₁ v₂ : FockSF) :
    mode (YSF (c • (u₁ + u₂))) (-1) (d • (v₁ + v₂))
      = (c * d) • (mode (YSF u₁) (-1) v₁ + mode (YSF u₁) (-1) v₂
          + mode (YSF u₂) (-1) v₁ + mode (YSF u₂) (-1) v₂) := by
  rw [mode_YSF_left_smul, mode_YSF_left_add, map_smul, map_smul, map_add, map_add]
  module

/-! ### Reordering the two four-letter words -/

/-- `N₂ = N`: moving a two-letter block past a two-letter block costs four transpositions. -/
theorem N2_eq_N :
    stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2)), ((1 : ℕ), (1 : Fin 2)),
        ((0 : ℕ), (0 : Fin 2))]
      = stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2)), ((1 : ℕ), (0 : Fin 2)),
          ((0 : ℕ), (1 : Fin 2))] := by
  rw [stWordSF_swap23 ((1 : ℕ), (0 : Fin 2)) ((0 : ℕ), (1 : Fin 2)) ((1 : ℕ), (1 : Fin 2))
        [((0 : ℕ), (0 : Fin 2))],
    stWordSF_swap12 ((1 : ℕ), (0 : Fin 2)) ((1 : ℕ), (1 : Fin 2))
        [((0 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))],
    stWordSF_swap34 ((1 : ℕ), (1 : Fin 2)) ((1 : ℕ), (0 : Fin 2)) ((0 : ℕ), (1 : Fin 2))
        ((0 : ℕ), (0 : Fin 2)) [],
    stWordSF_swap23 ((1 : ℕ), (1 : Fin 2)) ((1 : ℕ), (0 : Fin 2)) ((0 : ℕ), (0 : Fin 2))
        [((0 : ℕ), (1 : Fin 2))], neg_neg, neg_neg]

/-- `N = -N'`: the two four-letter words differ by a transposition. -/
theorem N_eq_neg_N' :
    stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2)), ((1 : ℕ), (0 : Fin 2)),
        ((0 : ℕ), (1 : Fin 2))]
      = -stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2)),
          ((0 : ℕ), (0 : Fin 2))] := by
  rw [stWordSF_swap34 ((1 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2)) ((1 : ℕ), (0 : Fin 2))
        ((0 : ℕ), (1 : Fin 2)) [],
    stWordSF_swap23 ((1 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2)) ((0 : ℕ), (1 : Fin 2))
        [((1 : ℕ), (0 : Fin 2))],
    stWordSF_swap34 ((1 : ℕ), (1 : Fin 2)) ((0 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2))
        ((1 : ℕ), (0 : Fin 2)) [], neg_neg]

/-- `χ⁰₋₄χ¹₋₂|0⟩ = -χ¹₋₂χ⁰₋₄|0⟩`. -/
theorem B'_eq :
    stWordSF [((3 : ℕ), (0 : Fin 2)), ((1 : ℕ), (1 : Fin 2))]
      = -stWordSF [((1 : ℕ), (1 : Fin 2)), ((3 : ℕ), (0 : Fin 2))] :=
  stWordSF_swap12 _ _ []

/-- `χ⁰₋₅χ¹₋₁|0⟩ = -χ¹₋₁χ⁰₋₅|0⟩`. -/
theorem D'_eq :
    stWordSF [((4 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]
      = -stWordSF [((0 : ℕ), (1 : Fin 2)), ((4 : ℕ), (0 : Fin 2))] :=
  stWordSF_swap12 _ _ []

/-! ### The four translates -/

theorem T_word_03 :
    SympFerm.T (stWordSF [((0 : ℕ), (1 : Fin 2)), ((3 : ℕ), (0 : Fin 2))])
      = (4 : ℂ) • stWordSF [((0 : ℕ), (1 : Fin 2)), ((4 : ℕ), (0 : Fin 2))]
        + (1 : ℂ) • stWordSF [((1 : ℕ), (1 : Fin 2)), ((3 : ℕ), (0 : Fin 2))] := by
  rw [T_stWordSF_pair' 0 3 1 0]; norm_num

theorem T_word_12 :
    SympFerm.T (stWordSF [((1 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))])
      = (3 : ℂ) • stWordSF [((1 : ℕ), (1 : Fin 2)), ((3 : ℕ), (0 : Fin 2))]
        + (2 : ℂ) • stWordSF [((2 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))] := by
  rw [T_stWordSF_pair' 1 2 1 0]; norm_num

theorem T_word_21 :
    SympFerm.T (stWordSF [((2 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))])
      = (2 : ℂ) • stWordSF [((2 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))]
        + (3 : ℂ) • stWordSF [((3 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))] := by
  rw [T_stWordSF_pair' 2 1 1 0]; norm_num

theorem T_word_30 :
    SympFerm.T (stWordSF [((3 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = (1 : ℂ) • stWordSF [((3 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))]
        + (4 : ℂ) • stWordSF [((4 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))] := by
  rw [T_stWordSF_pair' 3 0 1 0]; norm_num

/-- **The key weight-`6` identity in `FockSF`**:

`2·H₍₋₁₎H + E₍₋₁₎F = (7/4)L₋₁(χ¹₋₁χ⁰₋₄|0⟩) - (17/12)L₋₁(χ¹₋₂χ⁰₋₃|0⟩)
                      + (17/12)L₋₁(χ¹₋₃χ⁰₋₂|0⟩) - (7/4)L₋₁(χ¹₋₄χ⁰₋₁|0⟩)`.

The two four-letter terms cancel (`N = -N'`, `N₂ = N`), and what is left is exactly a
translate — which is what Abe's relation `ĒF̄ = -2H̄²` asserts. -/
theorem two_HH_add_EF_fock :
    (2 : ℂ) • mode (YSF ((2⁻¹ : ℂ) • (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))]
          + stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]))) (-1)
        ((2⁻¹ : ℂ) • (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))]
          + stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]))
      + mode (YSF (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])) (-1)
        (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = ((7 : ℂ) / 4) • SympFerm.T (stWordSF [((0 : ℕ), (1 : Fin 2)), ((3 : ℕ), (0 : Fin 2))])
        + (-(17 : ℂ) / 12) • SympFerm.T
            (stWordSF [((1 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))])
        + ((17 : ℂ) / 12) • SympFerm.T
            (stWordSF [((2 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))])
        + (-(7 : ℂ) / 4) • SympFerm.T
            (stWordSF [((3 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))]) := by
  rw [mode_YSF_bilin_expand, G10_prod_G10, G10_prod_G01, G01_prod_G10, G01_prod_G01, E_prod_F,
    T_word_03, T_word_12, T_word_21, T_word_30, N2_eq_N, N_eq_neg_N', B'_eq, D'_eq]
  module

/-- The same identity inside `W(2)`, with the right-hand side an explicit combination of
`O₂`-generators `v₍₋₂₎𝟙`. -/
theorem two_HH_add_EF_eq :
    (2 : ℂ) • poissonMul tripletW2 abeH abeH + poissonMul tripletW2 abeE abeF
      = ((7 : ℂ) / 4) • tripletW2.toPreVertexAlgebra.T
            (w2pair ((0 : ℕ), (1 : Fin 2)) ((3 : ℕ), (0 : Fin 2)))
        + (-(17 : ℂ) / 12) • tripletW2.toPreVertexAlgebra.T
            (w2pair ((1 : ℕ), (1 : Fin 2)) ((2 : ℕ), (0 : Fin 2)))
        + ((17 : ℂ) / 12) • tripletW2.toPreVertexAlgebra.T
            (w2pair ((2 : ℕ), (1 : Fin 2)) ((1 : ℕ), (0 : Fin 2)))
        + (-(7 : ℂ) / 4) • tripletW2.toPreVertexAlgebra.T
            (w2pair ((3 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2))) := by
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul, poissonMul_def, tripletW2_smul_coe,
    tripletW2_T_coe, w2pair_coe, abeH_coe, abeE_coe, abeF_coe]
  exact two_HH_add_EF_fock

/-- `2·H₍₋₁₎H + E₍₋₁₎F ∈ O₂(W(2))`. -/
theorem two_HH_add_EF_mem_O₂ :
    (2 : ℂ) • poissonMul tripletW2 abeH abeH + poissonMul tripletW2 abeE abeF
      ∈ O₂ tripletW2 := by
  rw [two_HH_add_EF_eq]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (T_mem_O₂ _)) (Submodule.smul_mem _ _ (T_mem_O₂ _)))
    (Submodule.smul_mem _ _ (T_mem_O₂ _))) (Submodule.smul_mem _ _ (T_mem_O₂ _))

/-- **Abe §3.3, fifth relation: `Ē·F̄ = -2·H̄²` in `A₂(W(2))`.** -/
theorem two_Hbar_sq_add_Ebar_Fbar : (2 : ℂ) • (Hbar * Hbar) + Ebar * Fbar = 0 := by
  have h := (mk₂_eq_zero_iff tripletW2).2 two_HH_add_EF_mem_O₂
  rw [map_add, map_smul, ← A₂_mul_mk, ← A₂_mul_mk] at h
  exact h

/-- The same relation in Abe's form `-Ē·F̄ = 2·H̄²`. -/
theorem Ebar_mul_Fbar_eq : Ebar * Fbar = -((2 : ℂ) • (Hbar * Hbar)) := by
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact two_Hbar_sq_add_Ebar_Fbar

/-! ## §13  The Virasoro modes on two-letter words

For products with `ω` the commutator form `[Lₙ, χᶜ_r] = -r·χᶜ_{n+r}` (`LSF_comm_chiM_apply`) is
far cheaper than the normal-ordering sum: it turns `Lₙ` on a word into (a creation on `Lₙ|0⟩`)
plus two one-letter shifts.  Recall `ω₍₋₁₎ = L₋₂` and `ω₍₋₂₎ = L₋₃`. -/

/-- `Lₙ` on a two-letter word, from the commutator relation alone. -/
theorem LSF_stWordSF_pair (n : ℤ) (k j : ℕ) (a b : Fin 2) :
    LSF n (stWordSF [(k, a), (j, b)])
      = chiM a (-(k : ℤ) - 1) (chiM b (-(j : ℤ) - 1) (LSF n (stWordSF ([] : SFWord))))
        + ((j : ℂ) + 1) • chiM a (-(k : ℤ) - 1)
            (chiM b (n + (-(j : ℤ) - 1)) (stWordSF ([] : SFWord)))
        + ((k : ℂ) + 1) • chiM a (n + (-(k : ℤ) - 1))
            (chiM b (-(j : ℤ) - 1) (stWordSF ([] : SFWord))) := by
  have hw : stWordSF [(k, a), (j, b)]
      = chiM a (-(k : ℤ) - 1) (chiM b (-(j : ℤ) - 1) (stWordSF ([] : SFWord))) := by
    rw [chiM_cons b j [], chiM_cons a k [(j, b)]]
  rw [hw]
  have h1 := LSF_comm_chiM_apply n a (-(k : ℤ) - 1)
    (chiM b (-(j : ℤ) - 1) (stWordSF ([] : SFWord)))
  have h2 := LSF_comm_chiM_apply n b (-(j : ℤ) - 1) (stWordSF ([] : SFWord))
  have h2' := congrArg (chiM a (-(k : ℤ) - 1)) h2
  simp only [map_sub, map_smul] at h2'
  push_cast at h1 h2' ⊢
  linear_combination (norm := module) h1 + h2'

/-- `L₋₂|0⟩ = ω`. -/
theorem LSF_neg_two_nil : LSF (-2) (stWordSF ([] : SFWord)) = ωSF := LSF_neg_two_vacuum

/-- `L₋₃|0⟩ = L₋₁ω = Tω` — the creation axiom `ω₍₋₂₎𝟙 = Tω`. -/
theorem LSF_neg_three_nil : LSF (-3) (stWordSF ([] : SFWord)) = SympFerm.T ωSF := by
  have h : ((tripletW2.toPreVertexAlgebra.T tripletW2.conformalVector :
      evenOdd QSF (0 : ZMod 2)) : FockSF) = SympFerm.T ωSF := by
    rw [tripletW2_T_coe, tripletW2_conformalVector_coe]
  rw [← h, PreVertexAlgebra.T_apply, tripletW2_smul_coe, tripletW2_conformalVector_coe,
    tripletW2_vacuum_coe, LSF_eq_mode]
  norm_num

/-- A word with two **adjacent** equal letters vanishes. -/
theorem stWordSF_dup_adj (p : ℕ × Fin 2) (l : SFWord) : stWordSF (p :: p :: l) = 0 := by
  rw [stWordSF_cons, stWordSF_cons, ← mul_assoc, sfGen_sq, zero_mul]

/-- Prepending a letter to a vanishing word keeps it zero. -/
theorem stWordSF_cons_of_zero (p : ℕ × Fin 2) {l : SFWord} (h : stWordSF l = 0) :
    stWordSF (p :: l) = 0 := by
  rw [stWordSF_cons, h, mul_zero]

/-- `ω₍₋₁₎ = L₋₂` on a two-letter word. -/
theorem LSF_neg_two_pair (k j : ℕ) (a b : Fin 2) :
    LSF (-2) (stWordSF [(k, a), (j, b)])
      = -stWordSF [(k, a), (j, b), ((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]
        + ((j : ℂ) + 1) • stWordSF [(k, a), (j + 2, b)]
        + ((k : ℂ) + 1) • stWordSF [(k + 2, a), (j, b)] := by
  rw [LSF_stWordSF_pair, LSF_neg_two_nil, ωSF, map_neg, map_neg,
    show stWordSF [((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]
        = stWordSF [((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] from rfl,
    chiM_cons b j [((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))],
    chiM_cons a k [(j, b), ((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))],
    chiM_create b (j + 2) (-2 + (-(j : ℤ) - 1)) (by push_cast; ring) [],
    chiM_create a k (-(k : ℤ) - 1) rfl [(j + 2, b)],
    chiM_create b j (-(j : ℤ) - 1) rfl [],
    chiM_create a (k + 2) (-2 + (-(k : ℤ) - 1)) (by push_cast; ring) [(j, b)]]

/-- `ω₍₋₂₎ = L₋₃` on a two-letter word. -/
theorem LSF_neg_three_pair (k j : ℕ) (a b : Fin 2) :
    LSF (-3) (stWordSF [(k, a), (j, b)])
      = stWordSF [(k, a), (j, b), ((0 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))]
        - stWordSF [(k, a), (j, b), ((0 : ℕ), (0 : Fin 2)), ((1 : ℕ), (1 : Fin 2))]
        + ((j : ℂ) + 1) • stWordSF [(k, a), (j + 3, b)]
        + ((k : ℂ) + 1) • stWordSF [(k + 3, a), (j, b)] := by
  rw [LSF_stWordSF_pair, LSF_neg_three_nil, T_omega, sfWgen, sfWgen, map_sub, map_sub,
    chiM_cons b j [((0 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))],
    chiM_cons a k [(j, b), ((0 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))],
    chiM_cons b j [((0 : ℕ), (0 : Fin 2)), ((1 : ℕ), (1 : Fin 2))],
    chiM_cons a k [(j, b), ((0 : ℕ), (0 : Fin 2)), ((1 : ℕ), (1 : Fin 2))],
    chiM_create b (j + 3) (-3 + (-(j : ℤ) - 1)) (by push_cast; ring) [],
    chiM_create a k (-(k : ℤ) - 1) rfl [(j + 3, b)],
    chiM_create b j (-(j : ℤ) - 1) rfl [],
    chiM_create a (k + 3) (-3 + (-(k : ℤ) - 1)) (by push_cast; ring) [(j, b)]]

/-! ### The powers of `ω` and the generator `ω₍₋₂₎G¹⁰` -/

/-- `ω₍₋₁₎ω = -χ⁰₋₁χ¹₋₃|0⟩ - χ⁰₋₃χ¹₋₁|0⟩` (agrees with
`Examples.TripletTTNull.omega_poissonMul_omega`). -/
theorem omega_sq_fock :
    LSF (-2) ωSF
      = -stWordSF [((0 : ℕ), (0 : Fin 2)), ((2 : ℕ), (1 : Fin 2))]
        - stWordSF [((2 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] := by
  rw [ωSF, map_neg, LSF_neg_two_pair 0 0 0 1,
    stWordSF_dup_outer ((0 : ℕ), (0 : Fin 2)) ((0 : ℕ), (1 : Fin 2)) [((0 : ℕ), (1 : Fin 2))]]
  norm_num
  module

/-- `ω₍₋₁₎ω₍₋₁₎ω = -3·χ⁰₋₁χ¹₋₅|0⟩ - 2·χ⁰₋₃χ¹₋₃|0⟩ - 3·χ⁰₋₅χ¹₋₁|0⟩`. -/
theorem omega_cube_fock :
    LSF (-2) (LSF (-2) ωSF)
      = (-3 : ℂ) • stWordSF [((0 : ℕ), (0 : Fin 2)), ((4 : ℕ), (1 : Fin 2))]
        + (-2 : ℂ) • stWordSF [((2 : ℕ), (0 : Fin 2)), ((2 : ℕ), (1 : Fin 2))]
        + (-3 : ℂ) • stWordSF [((4 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] := by
  rw [omega_sq_fock, map_sub, map_neg, LSF_neg_two_pair 0 2 0 1, LSF_neg_two_pair 2 0 0 1,
    stWordSF_dup_outer ((0 : ℕ), (0 : Fin 2)) ((2 : ℕ), (1 : Fin 2)) [((0 : ℕ), (1 : Fin 2))],
    stWordSF_cons_of_zero ((2 : ℕ), (0 : Fin 2))
      (stWordSF_dup_outer ((0 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2)) [])]
  norm_num
  module

/-- `ω₍₋₂₎G¹⁰ = -N + χ¹₋₂χ⁰₋₄|0⟩ + 2·χ¹₋₅χ⁰₋₁|0⟩` — an `O₂`-generator that is *not* a
translate (it has a four-letter component). -/
theorem omegaG10_fock :
    LSF (-3) (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2)),
            ((1 : ℕ), (0 : Fin 2))]
        + (1 : ℂ) • stWordSF [((1 : ℕ), (1 : Fin 2)), ((3 : ℕ), (0 : Fin 2))]
        + (2 : ℂ) • stWordSF [((4 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))] := by
  rw [LSF_neg_three_pair 1 0 1 0,
    stWordSF_cons_of_zero ((1 : ℕ), (1 : Fin 2))
      (stWordSF_dup_adj ((0 : ℕ), (0 : Fin 2)) [((1 : ℕ), (1 : Fin 2))])]
  norm_num

/-! ### Two more transpositions -/

theorem swap_00_41 :
    stWordSF [((0 : ℕ), (0 : Fin 2)), ((4 : ℕ), (1 : Fin 2))]
      = -stWordSF [((4 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))] :=
  stWordSF_swap12 _ _ []

theorem swap_20_21 :
    stWordSF [((2 : ℕ), (0 : Fin 2)), ((2 : ℕ), (1 : Fin 2))]
      = -stWordSF [((2 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))] :=
  stWordSF_swap12 _ _ []

theorem swap_N_four :
    stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2)),
        ((1 : ℕ), (0 : Fin 2))]
      = -stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2)), ((1 : ℕ), (0 : Fin 2)),
          ((0 : ℕ), (1 : Fin 2))] :=
  stWordSF_swap34 _ _ _ _ []

/-! ## §14  Assembling `2·H̄² = (16/9)·ω̄³` -/

theorem mode_omega_neg_one (x : FockSF) : mode (YSF ωSF) (-1) x = LSF (-2) x := by
  rw [LSF_eq_mode]; norm_num

theorem mode_omega_neg_two (x : FockSF) : mode (YSF ωSF) (-2) x = LSF (-3) x := by
  rw [LSF_eq_mode]; norm_num

/-- **The weight-`6` identity behind Abe's `2H̄² = (16/9)ω̄³`**, in `FockSF`:

`2·H₍₋₁₎H - (16/9)·ω₍₋₁₎ω₍₋₁₎ω + ω₍₋₂₎G¹⁰
   = (5/12)L₋₁(χ¹₋₁χ⁰₋₄) - (23/36)L₋₁(χ¹₋₂χ⁰₋₃) - (41/36)L₋₁(χ¹₋₃χ⁰₋₂) + (11/12)L₋₁(χ¹₋₄χ⁰₋₁)`.

The four-letter parts cancel between `2H₍₋₁₎H` and `ω₍₋₂₎G¹⁰`; the remaining mixed weight-`6`
vector is annihilated by the cokernel functional `(1,-4,6,-4,1)` of `L₋₁`, hence is a
translate. -/
theorem abe_HH_omega_identity_fock :
    (2 : ℂ) • mode (YSF ((2⁻¹ : ℂ) • (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))]
          + stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]))) (-1)
        ((2⁻¹ : ℂ) • (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))]
          + stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]))
      + (-(16 : ℂ) / 9) • LSF (-2) (LSF (-2) ωSF)
      + LSF (-3) (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = ((5 : ℂ) / 12) • SympFerm.T (stWordSF [((0 : ℕ), (1 : Fin 2)), ((3 : ℕ), (0 : Fin 2))])
        + (-(23 : ℂ) / 36) • SympFerm.T
            (stWordSF [((1 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))])
        + (-(41 : ℂ) / 36) • SympFerm.T
            (stWordSF [((2 : ℕ), (1 : Fin 2)), ((1 : ℕ), (0 : Fin 2))])
        + ((11 : ℂ) / 12) • SympFerm.T
            (stWordSF [((3 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))]) := by
  rw [mode_YSF_bilin_expand, G10_prod_G10, G10_prod_G01, G01_prod_G10, G01_prod_G01,
    omega_cube_fock, omegaG10_fock, T_word_03, T_word_12, T_word_21, T_word_30,
    N2_eq_N, swap_N_four, B'_eq, D'_eq, swap_00_41, swap_20_21]
  module

/-- The same identity inside `W(2)`. -/
theorem abe_HH_omega_identity :
    (2 : ℂ) • poissonMul tripletW2 abeH abeH
      + (-(16 : ℂ) / 9) • poissonMul tripletW2 abeOmega
          (poissonMul tripletW2 abeOmega abeOmega)
      + tripletW2.smul abeOmega (-2) (abeGen 1 0)
      = ((5 : ℂ) / 12) • tripletW2.toPreVertexAlgebra.T
            (w2pair ((0 : ℕ), (1 : Fin 2)) ((3 : ℕ), (0 : Fin 2)))
        + (-(23 : ℂ) / 36) • tripletW2.toPreVertexAlgebra.T
            (w2pair ((1 : ℕ), (1 : Fin 2)) ((2 : ℕ), (0 : Fin 2)))
        + (-(41 : ℂ) / 36) • tripletW2.toPreVertexAlgebra.T
            (w2pair ((2 : ℕ), (1 : Fin 2)) ((1 : ℕ), (0 : Fin 2)))
        + ((11 : ℂ) / 12) • tripletW2.toPreVertexAlgebra.T
            (w2pair ((3 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2))) := by
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul, poissonMul_def, tripletW2_smul_coe,
    tripletW2_T_coe, w2pair_coe, abeH_coe, abeOmega_coe, abeGen_coe, mode_omega_neg_one,
    mode_omega_neg_two]
  exact abe_HH_omega_identity_fock

/-- `2·H₍₋₁₎H - (16/9)·ω₍₋₁₎ω₍₋₁₎ω ∈ O₂(W(2))`. -/
theorem abe_HH_omega_mem_O₂ :
    (2 : ℂ) • poissonMul tripletW2 abeH abeH
      + (-(16 : ℂ) / 9) • poissonMul tripletW2 abeOmega
          (poissonMul tripletW2 abeOmega abeOmega) ∈ O₂ tripletW2 := by
  have hgen : tripletW2.smul abeOmega (-2) (abeGen 1 0) ∈ O₂ tripletW2 :=
    Submodule.subset_span ⟨abeOmega, abeGen 1 0, rfl⟩
  have hsum : (2 : ℂ) • poissonMul tripletW2 abeH abeH
      + (-(16 : ℂ) / 9) • poissonMul tripletW2 abeOmega
          (poissonMul tripletW2 abeOmega abeOmega)
      + tripletW2.smul abeOmega (-2) (abeGen 1 0) ∈ O₂ tripletW2 := by
    rw [abe_HH_omega_identity]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (T_mem_O₂ _)) (Submodule.smul_mem _ _ (T_mem_O₂ _)))
      (Submodule.smul_mem _ _ (T_mem_O₂ _))) (Submodule.smul_mem _ _ (T_mem_O₂ _))
  simpa using Submodule.sub_mem _ hsum hgen

/-- **Abe §3.3, sixth relation: `2·H̄² = (16/9)·ω̄³` in `A₂(W(2))`.** -/
theorem two_Hbar_sq_eq : (2 : ℂ) • (Hbar * Hbar) = ((16 : ℂ) / 9) • (wbar * (wbar * wbar)) := by
  have h := (mk₂_eq_zero_iff tripletW2).2 abe_HH_omega_mem_O₂
  rw [map_add, map_smul, map_smul, ← A₂_mul_mk, ← A₂_mul_mk, ← A₂_mul_mk] at h
  have h2 : (2 : ℂ) • (Hbar * Hbar) + (-(16 : ℂ) / 9) • (wbar * (wbar * wbar)) = 0 := h
  linear_combination (norm := module) h2

/-- `H̄² = (8/9)·ω̄³` — Abe's normalisation. -/
theorem Hbar_sq_eq : Hbar * Hbar = ((8 : ℂ) / 9) • (wbar * (wbar * wbar)) := by
  have h := two_Hbar_sq_eq
  rw [show ((16 : ℂ) / 9) = (2 : ℂ) * ((8 : ℂ) / 9) from by norm_num, ← smul_smul] at h
  exact smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0) h

/-! ## §15  Consequences: `H̄⁴ = 0` and `ω̄⁶ = 0` — all four generators are nilpotent

The relations of §4, §9 and §14 already force nilpotency of *every* generator, with no further
Fock-space computation:

* `Ē² = 0` and `ĒF̄ = -2H̄²` give `0 = (Ē²)(F̄²) = (ĒF̄)² = 4H̄⁴`, hence `H̄⁴ = 0`;
* `H̄² = (8/9)ω̄³` then gives `0 = H̄⁴ = (64/81)ω̄⁶`, hence `ω̄⁶ = 0`.

⚠ Abe's sharper `ω̄⁵ = 0` needs his relations `ω̄²Ē = ω̄²H̄ = ω̄²F̄ = 0`, which are **not** proved
here (see the "What is not proved" section of the module docstring).  `ω̄⁶ = 0` is what the
relations established here actually yield, and it is proved. -/

/-- Scalars pass through the `A₂`-product on the left (the product is `ℂ`-bilinear). -/
theorem A₂_smul_mul (c : ℂ) (p q : A₂ tripletW2) : (c • p) * q = c • (p * q) := by
  change A₂mul tripletW2 (c • p) q = c • A₂mul tripletW2 p q
  rw [map_smul, LinearMap.smul_apply]

/-- Scalars pass through the `A₂`-product on the right. -/
theorem A₂_mul_smul (c : ℂ) (p q : A₂ tripletW2) : p * (c • q) = c • (p * q) := by
  change A₂mul tripletW2 p (c • q) = c • A₂mul tripletW2 p q
  rw [map_smul]

/-- **`H̄⁴ = 0`** — one of Abe's stated nilpotency exponents, here *derived* from
`Ē² = 0` and `ĒF̄ = -2H̄²`. -/
theorem Hbar_pow_four : Hbar ^ 4 = 0 := by
  have h0 : (Ebar * Fbar) ^ 2 = 0 := by
    have h : (Ebar * Fbar) ^ 2 = (Ebar * Ebar) * (Fbar * Fbar) := by ring
    rw [h, Ebar_sq, zero_mul]
  rw [Ebar_mul_Fbar_eq] at h0
  have h1 : (-((2 : ℂ) • (Hbar * Hbar))) ^ 2 = (4 : ℂ) • (Hbar ^ 4) := by
    rw [pow_two, neg_mul_neg, A₂_smul_mul, A₂_mul_smul, smul_smul]
    congr 1
    · norm_num
    · ring
  rw [h1] at h0
  have h2 := congrArg (fun z : A₂ tripletW2 => ((4 : ℂ)⁻¹) • z) h0
  simp only [smul_smul, smul_zero] at h2
  norm_num at h2
  exact h2

/-- **`ω̄⁶ = 0`**: the conformal class is nilpotent in `A₂(W(2))`. -/
theorem wbar_pow_six : wbar ^ 6 = 0 := by
  have h := Hbar_pow_four
  have h2 : Hbar ^ 4 = ((64 : ℂ) / 81) • (wbar ^ 6) := by
    have e : Hbar ^ 4 = (Hbar * Hbar) * (Hbar * Hbar) := by ring
    rw [e, Hbar_sq_eq, A₂_smul_mul, A₂_mul_smul, smul_smul]
    congr 1
    · norm_num
    · ring
  rw [h2] at h
  have h3 := congrArg (fun z : A₂ tripletW2 => (((64 : ℂ) / 81)⁻¹) • z) h
  simp only [smul_smul, smul_zero] at h3
  norm_num at h3
  exact h3

/-- `ĒF̄ = -(16/9)ω̄³`, combining §9 and §14. -/
theorem Ebar_mul_Fbar_omega : Ebar * Fbar = (-(16 : ℂ) / 9) • (wbar ^ 3) := by
  rw [Ebar_mul_Fbar_eq, Hbar_sq_eq, smul_smul]
  have e : wbar * (wbar * wbar) = wbar ^ 3 := by ring
  rw [e, ← neg_smul]
  congr 1
  norm_num

/-- `ω̄` is nilpotent (exponent `6`). -/
theorem wbar_isNilpotent : IsNilpotent wbar := ⟨6, wbar_pow_six⟩

/-- `H̄` is nilpotent (exponent `4`). -/
theorem Hbar_isNilpotent : IsNilpotent Hbar := ⟨4, Hbar_pow_four⟩

/-! ## §16  The three relations that did **not** close, with their exact vectors

Abe's remaining §3.3 relations are the weight-`7` statements `ω̄²Ē = ω̄²H̄ = ω̄²F̄ = 0`.  Their
left-hand sides are computed here **explicitly and verifiably** (`ω₍₋₁₎ = L₋₂`), so that they can
be checked or completed externally; what is missing is only the second half — exhibiting these
weight-`7` vectors inside `O₂(W(2))`, which needs `O₂`-generators beyond the translates
(`L₋₄E`, `E₍₋₃₎ω`, `ω₍₋₂₎(W(2)₄)`, …) and a genuinely larger linear system than §12/§14.

Convention reminder for external checks: `mode a m = a (-m-1)`; `FormalDist` is indexed by the
`z`-**exponent**; a letter `(k,a)` of `stWordSF` is the creation mode `χᵃ_{-k-1}` of conformal
weight `k+1`; `{χᵃ_p, χᵇ_q} = p δ_{p+q,0} ωᵃᵇ` with `ω⁰¹ = 1`; `ω = -χ⁰₋₁χ¹₋₁|0⟩`. -/

/-- `ω₍₋₁₎E = L₋₂E = χ¹₋₂χ¹₋₃|0⟩ + 2·χ¹₋₄χ¹₋₁|0⟩`. -/
theorem omega_E_fock :
    LSF (-2) (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])
      = stWordSF [((1 : ℕ), (1 : Fin 2)), ((2 : ℕ), (1 : Fin 2))]
        + (2 : ℂ) • stWordSF [((3 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] := by
  rw [LSF_neg_two_pair 1 0 1 1,
    stWordSF_cons_of_zero ((1 : ℕ), (1 : Fin 2))
      (stWordSF_dup_outer ((0 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2)) [])]
  norm_num

/-- `ω̄²Ē` has representative
`L₋₂L₋₂E = -χ¹₋₂χ¹₋₃χ⁰₋₁χ¹₋₁|0⟩ + 3·χ¹₋₂χ¹₋₅|0⟩ + 4·χ¹₋₄χ¹₋₃|0⟩ + 8·χ¹₋₆χ¹₋₁|0⟩`. -/
theorem omega_sq_E_fock :
    LSF (-2) (LSF (-2) (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]))
      = -stWordSF [((1 : ℕ), (1 : Fin 2)), ((2 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2)),
            ((0 : ℕ), (1 : Fin 2))]
        + (3 : ℂ) • stWordSF [((1 : ℕ), (1 : Fin 2)), ((4 : ℕ), (1 : Fin 2))]
        + (4 : ℂ) • stWordSF [((3 : ℕ), (1 : Fin 2)), ((2 : ℕ), (1 : Fin 2))]
        + (8 : ℂ) • stWordSF [((5 : ℕ), (1 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] := by
  rw [omega_E_fock, map_add, map_smul, LSF_neg_two_pair 1 2 1 1, LSF_neg_two_pair 3 0 1 1,
    stWordSF_cons_of_zero ((3 : ℕ), (1 : Fin 2))
      (stWordSF_dup_outer ((0 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2)) [])]
  norm_num
  module

/-- `ω₍₋₁₎F = L₋₂F = χ⁰₋₂χ⁰₋₃|0⟩ + 2·χ⁰₋₄χ⁰₋₁|0⟩`. -/
theorem omega_F_fock :
    LSF (-2) (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = stWordSF [((1 : ℕ), (0 : Fin 2)), ((2 : ℕ), (0 : Fin 2))]
        + (2 : ℂ) • stWordSF [((3 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))] := by
  rw [LSF_neg_two_pair 1 0 0 0,
    stWordSF_cons_of_zero ((1 : ℕ), (0 : Fin 2))
      (stWordSF_dup_adj ((0 : ℕ), (0 : Fin 2)) [((0 : ℕ), (1 : Fin 2))])]
  norm_num

/-- `ω̄²F̄` has representative
`L₋₂L₋₂F = -χ⁰₋₂χ⁰₋₃χ⁰₋₁χ¹₋₁|0⟩ + 3·χ⁰₋₂χ⁰₋₅|0⟩ + 4·χ⁰₋₄χ⁰₋₃|0⟩ + 8·χ⁰₋₆χ⁰₋₁|0⟩`. -/
theorem omega_sq_F_fock :
    LSF (-2) (LSF (-2) (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))]))
      = -stWordSF [((1 : ℕ), (0 : Fin 2)), ((2 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2)),
            ((0 : ℕ), (1 : Fin 2))]
        + (3 : ℂ) • stWordSF [((1 : ℕ), (0 : Fin 2)), ((4 : ℕ), (0 : Fin 2))]
        + (4 : ℂ) • stWordSF [((3 : ℕ), (0 : Fin 2)), ((2 : ℕ), (0 : Fin 2))]
        + (8 : ℂ) • stWordSF [((5 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2))] := by
  rw [omega_F_fock, map_add, map_smul, LSF_neg_two_pair 1 2 0 0, LSF_neg_two_pair 3 0 0 0,
    stWordSF_cons_of_zero ((3 : ℕ), (0 : Fin 2))
      (stWordSF_dup_adj ((0 : ℕ), (0 : Fin 2)) [((0 : ℕ), (1 : Fin 2))])]
  norm_num
  module

/-- `ω₍₋₁₎G¹⁰ = χ¹₋₂χ⁰₋₃|0⟩ + 2·χ¹₋₄χ⁰₋₁|0⟩`. -/
theorem omega_G10_fock :
    LSF (-2) (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))])
      = stWordSF [((1 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))]
        + (2 : ℂ) • stWordSF [((3 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))] := by
  rw [LSF_neg_two_pair 1 0 1 0,
    stWordSF_cons_of_zero ((1 : ℕ), (1 : Fin 2))
      (stWordSF_dup_adj ((0 : ℕ), (0 : Fin 2)) [((0 : ℕ), (1 : Fin 2))])]
  norm_num

/-- `ω₍₋₁₎G⁰¹ = χ⁰₋₂χ¹₋₃|0⟩ + 2·χ⁰₋₄χ¹₋₁|0⟩`. -/
theorem omega_G01_fock :
    LSF (-2) (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))])
      = stWordSF [((1 : ℕ), (0 : Fin 2)), ((2 : ℕ), (1 : Fin 2))]
        + (2 : ℂ) • stWordSF [((3 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] := by
  rw [LSF_neg_two_pair 1 0 0 1,
    stWordSF_cons_of_zero ((1 : ℕ), (0 : Fin 2))
      (stWordSF_dup_outer ((0 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2)) [])]
  norm_num

/-- `L₋₂L₋₂G¹⁰`, the first half of `ω̄²H̄`. -/
theorem omega_sq_G10_fock :
    LSF (-2) (LSF (-2) (stWordSF [((1 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))]))
      = -stWordSF [((1 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2)), ((0 : ℕ), (0 : Fin 2)),
            ((0 : ℕ), (1 : Fin 2))]
        + (3 : ℂ) • stWordSF [((1 : ℕ), (1 : Fin 2)), ((4 : ℕ), (0 : Fin 2))]
        + (4 : ℂ) • stWordSF [((3 : ℕ), (1 : Fin 2)), ((2 : ℕ), (0 : Fin 2))]
        + (8 : ℂ) • stWordSF [((5 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2))] := by
  rw [omega_G10_fock, map_add, map_smul, LSF_neg_two_pair 1 2 1 0, LSF_neg_two_pair 3 0 1 0,
    stWordSF_cons_of_zero ((3 : ℕ), (1 : Fin 2))
      (stWordSF_dup_adj ((0 : ℕ), (0 : Fin 2)) [((0 : ℕ), (1 : Fin 2))])]
  norm_num
  module

/-- `L₋₂L₋₂G⁰¹`, the second half of `ω̄²H̄`. -/
theorem omega_sq_G01_fock :
    LSF (-2) (LSF (-2) (stWordSF [((1 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]))
      = -stWordSF [((1 : ℕ), (0 : Fin 2)), ((2 : ℕ), (1 : Fin 2)), ((0 : ℕ), (0 : Fin 2)),
            ((0 : ℕ), (1 : Fin 2))]
        + (3 : ℂ) • stWordSF [((1 : ℕ), (0 : Fin 2)), ((4 : ℕ), (1 : Fin 2))]
        + (4 : ℂ) • stWordSF [((3 : ℕ), (0 : Fin 2)), ((2 : ℕ), (1 : Fin 2))]
        + (8 : ℂ) • stWordSF [((5 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] := by
  rw [omega_G01_fock, map_add, map_smul, LSF_neg_two_pair 1 2 0 1, LSF_neg_two_pair 3 0 0 1,
    stWordSF_cons_of_zero ((3 : ℕ), (0 : Fin 2))
      (stWordSF_dup_outer ((0 : ℕ), (1 : Fin 2)) ((0 : ℕ), (0 : Fin 2)) [])]
  norm_num
  module

/-! ### The open relations, as named `Prop`s -/

/-- **(R1) Abe's `ω̄²Ē = 0`.**  Equivalently `L₋₂L₋₂E ∈ O₂(W(2))`, with `L₋₂L₋₂E` the explicit
weight-`7` vector of `omega_sq_E_fock`.  **Not proved here.** -/
def OmegaSqEbarZero : Prop := wbar * (wbar * Ebar) = 0

/-- **(R2) Abe's `ω̄²H̄ = 0`** (`omega_sq_G10_fock`, `omega_sq_G01_fock` give the representative
`½(L₋₂L₋₂G¹⁰ + L₋₂L₋₂G⁰¹)`).  **Not proved here.** -/
def OmegaSqHbarZero : Prop := wbar * (wbar * Hbar) = 0

/-- **(R3) Abe's `ω̄²F̄ = 0`** (`omega_sq_F_fock`).  **Not proved here.** -/
def OmegaSqFbarZero : Prop := wbar * (wbar * Fbar) = 0

/-- **(R4) Abe's `ω̄⁵ = 0`.**  It is a *consequence* of `(R2)` together with the proved
`H̄² = (8/9)ω̄³`: `ω̄⁵ = ω̄²·ω̄³ = (9/8)·ω̄²H̄² = (9/8)·(ω̄²H̄)·H̄`.  What **is** proved here
unconditionally is the weaker `wbar_pow_six : ω̄⁶ = 0`. -/
def OmegaPowFiveZero : Prop := wbar ^ 5 = 0

/-- **`ω̄⁵ = 0` follows from `ω̄²H̄ = 0`** — the one implication that closes Abe's exponent. -/
theorem omegaPowFive_of_omegaSqHbar (h : OmegaSqHbarZero) : OmegaPowFiveZero := by
  have h' : wbar * (wbar * Hbar) = 0 := h
  have e : ((9 : ℂ) / 8) • ((wbar * (wbar * Hbar)) * Hbar) = wbar ^ 5 := by
    have e1 : (wbar * (wbar * Hbar)) * Hbar = (wbar * wbar) * (Hbar * Hbar) := by ring
    rw [e1, Hbar_sq_eq, A₂_mul_smul, smul_smul]
    have e3 : wbar * wbar * (wbar * (wbar * wbar)) = wbar ^ 5 := by ring
    rw [e3]
    norm_num
  change wbar ^ 5 = 0
  rw [← e, h', zero_mul, smul_zero]

end VOA.AbeRel
