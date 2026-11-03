/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.TripletW2
import VOA.Examples.SympFermC2
import VOA.Modules.C2Cofinite

/-!
# `C₂` for the triplet `W(2)`: descending to the even part

`tripletW2` is the **even part** `(FockSF)₀̄` of the symplectic fermions, and its `O₂` is formed
from its **own** vertex operators.  `Examples.SympFermC2` computes the *ambient* `C₂` quotient
(`dim A₂(SF) ≤ 4`); as its docstring warns, that does **not** transfer, because the only
available inclusion `O₂(W(2)) ⊆ O₂(SF)` (proved here as `O₂W2_le_O₂SF`) runs the wrong way.

This file builds the descent machinery, proves everything about the even part that is pure
exterior algebra, and **isolates the one remaining input** — which turns out to be exactly Abe's
orbifold step, in the sharpest form the free-field realization allows.

## What is proved

* `c2Cofinite_tripletW2_of_evSF_le_sup` — the **engine**: to get `C2Cofinite tripletW2` it is
  enough to cover the even part of `FockSF` by `O₂(W(2))` together with one finite-dimensional
  submodule of `FockSF`.  (`O₂ tripletW2` lives in the subtype `↥𝒱₀̄`; `O₂W2` is its image in
  `FockSF`, where it can be compared with the symplectic-fermion submodules.)
* `evSF_le_sfBottom_sup_sfHighPar_one` — the **even part, spanned modulo the odd–odd
  sector**: every even state is a combination of `|0⟩`, `χ⁰₋₁χ¹₋₁|0⟩` and states `χᵃ₋ₖ₋₁ v`
  with `k ≥ 1` and `v` **odd**.  (Parity-refined form of `SympFermC2.stWordSF_mem_sup`; the
  parity of the trailing state is what the even part needs and the ambient argument discards.)
* `oddCreationBounded_of_level_one` — the residual family collapses to **level one**: `T`
  trades a level for a translate, `(k+2)·χᵃ₋ₖ₋₂ v = T(χᵃ₋ₖ₋₁ v) − χᵃ₋ₖ₋₁(T v)`, the first term
  is in `O₂(W(2))` because `χᵃ₋ₖ₋₁ v` is even, and `T` preserves parity.
* `c2Cofinite_tripletW2_of_levelOne` — **the reduction**.  `C2Cofinite tripletW2` follows
  from: `χᵃ₋₂ v ∈ O₂(W(2)) + M` for `a ∈ {0,1}`, all **odd** `v`, and one fixed
  finite-dimensional `M`.  Equivalently — since `χᵃ₋₂ v = (χᵃ₋₁|0⟩)₍₋₂₎v` — *the `₍₋₂₎`-products
  of two odd states are, up to finitely many classes, `₍₋₂₎`-products of two even states*.
* `O₂W2_le_O₂SF` — the easy inclusion, and why it is the wrong one.
* `tripletW2_vacuumGradeZero` — `𝒱₀ = ℂ|0⟩` for `W(2)` (definitionally `VacuumGradeZero
  tripletW2`), free from the VOA axiom `vacuum_grade`.

## ⚠ The remaining gap, stated once

`c2Cofinite_tripletW2_of_levelOne` carries the hypothesis

  `∀ a v, v ∈ 𝒱₁̄ → χᵃ₋₂ v ∈ M ⊔ O₂W2`   (`M` finite-dimensional).

It is **not proved here**, and nothing in this file may be read as `C2Cofinite tripletW2`.  It is
true (Abe, Math. Z. 255 (2007) 755–792, proves `C₂`-cofiniteness of `SF⁺`), and by
`sfHighPar_le_O₂SF` these states are all in the *ambient* `O₂` already — the missing step is
purely the descent from the super `O₂` to the even one.

## ⚠ Two findings that bear on the plan of attack

**(a) There is no low-weight null state to find.**  The naive hope — that `A₂(W(2))` is killed
by one or two singular vectors and is `3p−1 = 5`-dimensional — is false.  `A₂(W(2))` is graded,
and its low-weight pieces are forced by *dimension counting alone*, using only
`tripletW2_grading_one` (`𝒱₁ = 0`), `𝟙₍₋₂₎v = 0` and `u₍₋₂₎𝟙 = Tu`:

| weight `w`             | 0 | 1 | 2 | 3 | 4 | 5 |
|------------------------|---|---|---|---|---|---|
| `dim W(2)_w`           | 1 | 0 | 1 | 4 | 5 | 8 |
| `dim O₂(W(2))_w`       | 0 | 0 | 0 | 1 | 4 | 5 |
| `dim A₂(W(2))_w`       | 1 | 0 | 1 | 3 | 1 | 3 |

because at weight `w` the only `u₍₋₂₎v` with `u,v` even are `wt u + wt v = w − 1` and `𝒱₁ = 0`
leaves only `(0, w−1)` (which gives `0`) and `(w−1, 0)` (which gives `T·W(2)_{w−1}`), except
at `w = 5` where `ω₍₋₂₎ω = L₋₃ω` also occurs — and that one is *already* in `T·W(2)₄`
(checked by hand:
`L₋₃ω ∝ χ⁺₋₄χ⁻₋₁ + χ⁺₋₁χ⁻₋₄ = T(⅓A + ⅓B − ⅙C)` with `A = χ⁺₋₃χ⁻₋₁`, `B = χ⁺₋₁χ⁻₋₃`,
`C = χ⁺₋₂χ⁻₋₂`).  So **`dim A₂(W(2)) ≥ 9`**, with surviving classes `𝟙`, `ω`, `Wᵃ` (3), `ω²`,
`ωWᵃ` (3), and equality iff `A₂` vanishes above weight `5`.  In particular `ω² ≠ 0` in
`A₂(W(2))`: the weight-4 piece is `W(2)₄/T·W(2)₃`, and `T·W(2)₃ = span{2A+C, −2B−C,
2χ⁺₋₃χ⁺₋₁, 2χ⁻₋₃χ⁻₋₁}` is 4-dimensional inside the 5-dimensional `W(2)₄`, while
`ω² = ω₍₋₁₎ω = −(A+B)` is not in it.  The relations that must do the work are therefore
`ω³` and `WᵃWᵇ` at **weight 6**, not anything at weight 3 or 4.

**(b) The excess filtration does not work.**  The tempting even-part analogue of the ambient
argument — "every even state whose creation levels sum to `≥ 2` is in `O₂`" — is false for
exactly the same reason: `ω²` has excess 2.  Any correct argument must reach weight 6.

## Status

Everything stated in this file is proved, `sorry`-free, axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`), no new axioms, `VOA.pbw` unused.  The single
unproved input is carried as an explicit hypothesis of
`c2Cofinite_tripletW2_of_levelOne` / `c2Cofinite_tripletW2_of_oddCreationBounded`.

## References
* Abe, *A ℤ₂-orbifold model of the symplectic fermionic vertex operator superalgebra*,
  Math. Z. 255 (2007) 755–792 — the orbifold step this file reduces to.
* Kausch, *Symplectic fermions*, Nucl. Phys. B583 (2000) 513; Adamović–Milas on `W(p)`.
* `Examples.SympFermC2` (the ambient computation), `Modules.C2Cofinite` (`O₂`, `A₂`,
  `C2Cofinite`), `Examples.TripletW2` (`tripletW2`, `tripletW2_grading_one`).
-/

namespace VOA.TripletDirect

open VOA VOA.SympFerm CliffordAlgebra

/-! ## §1  `O₂(W(2))`, transported to `FockSF` -/

/-- The even part of `FockSF`, as a submodule: the underlying space of `W(2)`. -/
noncomputable abbrev evSF : Submodule ℂ FockSF := evenOdd QSF (0 : ZMod 2)

/-- The odd part of `FockSF`, as a submodule. -/
noncomputable abbrev oddSF : Submodule ℂ FockSF := evenOdd QSF (1 : ZMod 2)

/-- **`O₂(W(2))` pushed into `FockSF`.**  `O₂ tripletW2` lives in the subtype `↥evSF`;
`O₂W2` is its image under the inclusion, so that it can be compared with the
symplectic-fermion submodules of `FockSF`. -/
noncomputable def O₂W2 : Submodule ℂ FockSF := (O₂ tripletW2).map evSF.subtype

/-- `O₂(W(2))` consists of even states. -/
theorem O₂W2_le_evSF : O₂W2 ≤ evSF := by
  rintro x ⟨y, _, rfl⟩
  exact y.2

/-- Membership in `O₂W2` is membership of a lift in `O₂ tripletW2`. -/
theorem mem_O₂W2_iff {x : FockSF} :
    x ∈ O₂W2 ↔ ∃ y : ↥evSF, y ∈ O₂ tripletW2 ∧ (y : FockSF) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

/-- **The generator of `O₂(W(2))`, read in `FockSF`**: for two *even* states `u, v` the
symplectic-fermion product `u₍₋₂₎v = YSF u 1 v` lies in `O₂(W(2))`.  This is the only place
where the vertex operators of `W(2)` enter: they are the ambient ones, restricted
(`tripletW2_smul_coe`), so the `W(2)`-product of two even states is computed by `YSF`. -/
theorem YSF_one_mem_O₂W2 {u v : FockSF} (hu : u ∈ evSF) (hv : v ∈ evSF) :
    YSF u 1 v ∈ O₂W2 := by
  refine ⟨tripletW2.smul ⟨u, hu⟩ (-2) ⟨v, hv⟩, Submodule.subset_span ⟨⟨u, hu⟩, ⟨v, hv⟩, rfl⟩, ?_⟩
  change mode (YSF u) (-2) v = YSF u 1 v
  rw [mode_apply]
  norm_num

/-- The translation operator of `W(2)` is the ambient one: `T` maps the even part into
`O₂(W(2))`.  (`T y = y₍₋₂₎𝟙`, and `𝟙` is even.) -/
theorem T_mem_O₂W2 {y : FockSF} (hy : y ∈ evSF) : T y ∈ O₂W2 := by
  have hvac : (vacSF : FockSF) ∈ evSF := by
    have h : (1 : FockSF) ∈ evSF := SetLike.one_mem_graded (evenOdd QSF)
    exact h
  have h := YSF_one_mem_O₂W2 hy hvac
  rwa [YSF_one_vac] at h

/-! ## §2  The reduction engine -/

/-- **The engine.**  To prove `C2Cofinite tripletW2` it suffices to cover the even part of
`FockSF` by `O₂(W(2))` together with **one finite-dimensional submodule of `FockSF`** — which
need not even be contained in the even part.  Everything downstream in this file feeds this
lemma. -/
theorem c2Cofinite_tripletW2_of_evSF_le_sup (M : Submodule ℂ FockSF)
    [FiniteDimensional ℂ M] (h : evSF ≤ M ⊔ O₂W2) : C2Cofinite tripletW2 := by
  classical
  set N : Submodule ℂ ↥evSF := Submodule.comap evSF.subtype M with hN
  -- `N` is finite-dimensional: it injects into `M`.
  have hfin : FiniteDimensional ℂ ↥N := by
    have hmap : N.map evSF.subtype ≤ M := Submodule.map_comap_le _ _
    haveI : FiniteDimensional ℂ ↥(N.map evSF.subtype) := Submodule.finiteDimensional_of_le hmap
    exact Module.Finite.equiv
      (Submodule.equivMapOfInjective evSF.subtype (Submodule.injective_subtype _) N).symm
  -- `N` together with `O₂` exhausts the even part.
  have hsup : N ⊔ O₂ tripletW2 = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨m, hm, o, ho, hmo⟩ := Submodule.mem_sup.mp (h x.2)
    obtain ⟨o', ho', rfl⟩ := mem_O₂W2_iff.mp ho
    refine Submodule.mem_sup.mpr ⟨x - o', ?_, o', ho', by abel⟩
    have : ((x - o' : ↥evSF) : FockSF) = m := by
      rw [Submodule.coe_sub, ← hmo]; abel
    exact Submodule.mem_comap.mpr (by rw [show evSF.subtype (x - o') = m from this]; exact hm)
  -- so `A₂(W(2))` is a quotient of `N`.
  refine Module.Finite.of_surjective ((O₂ tripletW2).mkQ.comp N.subtype) ?_
  intro q
  obtain ⟨x, rfl⟩ := (O₂ tripletW2).mkQ_surjective q
  obtain ⟨n, hn, o, ho, rfl⟩ := Submodule.mem_sup.mp (by rw [hsup]; trivial : x ∈ N ⊔ O₂ tripletW2)
  refine ⟨⟨n, hn⟩, ?_⟩
  change (O₂ tripletW2).mkQ n = (O₂ tripletW2).mkQ (n + o)
  have ho0 : (O₂ tripletW2).mkQ o = 0 := by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ho
  rw [map_add, ho0, add_zero]

/-! ## §3  The parity-refined creation span

`Examples.SympFermC2` works with `sfHigh`, the span of `χᵃ₋ₖ₋₁ v` over **all** `v`.  For the
even part one has to know the parity of `v`: the states `χᵃ₋ₖ₋₁ v` that are *even* are exactly
those with `v` **odd**, and those are precisely the products `u₍₋₂₎w` of two **odd** states —
the sector that `O₂(W(2))` does not see. -/

/-- The span of `χᵃ₋ₖ₋₁ v` with level `k ≥ 1` and `v` of parity `ε`. -/
noncomputable def sfHighPar (ε : ZMod 2) : Submodule ℂ FockSF :=
  Submodule.span ℂ {x | ∃ (k : ℕ) (a : Fin 2) (v : FockSF),
    1 ≤ k ∧ v ∈ evenOdd QSF ε ∧ x = sfCre k a * v}

/-- The defining span of `sfHighPar`, for rewriting. -/
theorem sfHighPar_def (ε : ZMod 2) :
    sfHighPar ε = Submodule.span ℂ {x | ∃ (k : ℕ) (a : Fin 2) (v : FockSF),
      1 ≤ k ∧ v ∈ evenOdd QSF ε ∧ x = sfCre k a * v} := rfl

/-- `sfHighPar 1` — the even half — sits in the **ambient** `O₂`, by `Examples.SympFermC2`.
This is exactly why the gap below is the orbifold step and nothing else: these states are
already killed by the symplectic-fermion `C₂`, just not visibly by the even one. -/
theorem sfHighPar_le_O₂SF (ε : ZMod 2) : sfHighPar ε ≤ O₂SF := by
  rw [sfHighPar_def, Submodule.span_le]
  rintro _ ⟨k, a, v, hk, _, rfl⟩
  exact sfCre_mul_mem_O₂SF hk a v

/-- One creation operator on an odd state is even. -/
theorem sfCre_mul_odd_mem_evSF (k : ℕ) (a : Fin 2) {v : FockSF} (hv : v ∈ oddSF) :
    sfCre k a * v ∈ evSF := by
  have h : sfCre k a * v ∈ evenOdd QSF ((1 : ZMod 2) + 1) :=
    SetLike.mul_mem_graded (ι_mem_evenOdd_one QSF _) hv
  rwa [show (1 : ZMod 2) + 1 = 0 from rfl] at h

/-- `sfHighPar 1` lies in the even part of `FockSF`. -/
theorem sfHighPar_one_le_evSF : sfHighPar 1 ≤ evSF := by
  rw [sfHighPar_def, Submodule.span_le]
  rintro _ ⟨k, a, v, _, hv, rfl⟩
  exact sfCre_mul_odd_mem_evSF k a hv

/-- Parity bookkeeping in `ZMod 2`: `1 + (m + 1) = m`. -/
theorem zmod_two_shift (m : ZMod 2) : 1 + (m + 1) = m := by
  rw [add_comm (1 : ZMod 2) (m + 1), add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]

/-- **Left multiplication by a weight-one generator flips the parity index of `sfHighPar`.**
One anticommutation moves the level-`≥ 1` operator back to the front. -/
theorem sfCre_zero_mul_sfHighPar (a : Fin 2) {ε : ZMod 2} {y : FockSF} (hy : y ∈ sfHighPar ε) :
    sfCre 0 a * y ∈ sfHighPar (1 + ε) := by
  rw [sfHighPar_def] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨k, b, v, hk, hv, rfl⟩ := hz
      rw [sfCre_mul_sfCre_swap]
      refine Submodule.neg_mem _ (Submodule.subset_span ⟨k, b, sfCre 0 a * v, hk, ?_, rfl⟩)
      exact SetLike.mul_mem_graded (ι_mem_evenOdd_one QSF _) hv
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

/-- **The parity-refined word induction.**  A creation word of length `n` is, modulo the four
`SympFermC2` bottom states, a sum of states `χᵃ₋ₖ₋₁ v` with `k ≥ 1` and `v` of parity `n + 1`.
Same peeling as `SympFermC2.stWordSF_mem_sup`, but here the parity of the *trailing* state is
carried along, which is what the even part needs. -/
theorem stWordSF_mem_bottom_sup_highPar (l : SFWord) :
    stWordSF l ∈ sfBottom ⊔ sfHighPar (((l.length : ℕ) : ZMod 2) + 1) := by
  induction l with
  | nil =>
      rw [stWordSF_nil]
      exact Submodule.mem_sup_left one_mem_sfBottom
  | cons p rest ih =>
      obtain ⟨k, a⟩ := p
      have hcons : stWordSF ((k, a) :: rest) = sfCre k a * stWordSF rest := rfl
      have hlen : ((((k, a) :: rest).length : ℕ) : ZMod 2) + 1
          = ((rest.length : ℕ) : ZMod 2) := by
        rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc,
          show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
      rw [hcons, hlen]
      cases k with
      | zero =>
          obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp ih
          rw [← hyz, mul_add]
          refine Submodule.add_mem _ (Submodule.mem_sup_left (sfBottom_mul_closed a hy))
            (Submodule.mem_sup_right ?_)
          have h := sfCre_zero_mul_sfHighPar a hz
          rwa [zmod_two_shift] at h
      | succ n =>
          exact Submodule.mem_sup_right
            (Submodule.subset_span ⟨n + 1, a, stWordSF rest, by omega,
              stWordSF_mem_evenOdd rest, rfl⟩)

/-- **The even part of `FockSF`, spanned modulo the odd–odd sector.**  Every even state is a
combination of `|0⟩`, `χ⁰₋₁χ¹₋₁|0⟩` (the two even members of the four `SympFermC2` bottom
states) and states `χᵃ₋ₖ₋₁ v` with `k ≥ 1` and `v` **odd**. -/
theorem evSF_le_sfBottom_sup_sfHighPar_one : evSF ≤ sfBottom ⊔ sfHighPar 1 := by
  rw [show (evSF : Submodule ℂ FockSF) = _ from evenPartSF_eq_span, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have h := stWordSF_mem_bottom_sup_highPar l
  rwa [ZMod.natCast_eq_zero_iff_even.mpr hl, zero_add] at h

/-! ## §4  The easy inclusion, and the gap it leaves -/

/-- **The easy inclusion**: `O₂(W(2)) ⊆ O₂(SF)`.  Both `C₂` ideals are spanned by `₍₋₂₎`
products; `W(2)`'s are computed with the ambient vertex operators, restricted, so every
generator of the smaller one is a generator of the bigger one.  ⚠ This runs the **wrong way**
for transferring finiteness: it yields a surjection `A₂(W(2)) ↠ 𝒱₀̄/(O₂(SF) ⊓ 𝒱₀̄)` and so
bounds `A₂(W(2))` only from *below*. -/
theorem O₂W2_le_O₂SF : O₂W2 ≤ O₂SF := by
  have key : ∀ z : ↥evSF, z ∈ O₂ tripletW2 → (z : FockSF) ∈ O₂SF := by
    intro z hz
    have hz' : z ∈ Submodule.span ℂ
        {x : ↥evSF | ∃ u v : ↥evSF, x = tripletW2.smul u (-2) v} := hz
    clear hz
    induction hz' using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨u, v, rfl⟩ := hw
        have h : ((tripletW2.smul u (-2) v : ↥evSF) : FockSF)
            = YSF (u : FockSF) 1 (v : FockSF) := by
          rw [tripletW2_smul_coe, mode_apply]; norm_num
        rw [h]
        have h2 := smul_neg_two_mem_O₂SF (u : FockSF) (v : FockSF)
        rwa [smul_neg_two_eq] at h2
    | zero => rw [ZeroMemClass.coe_zero]; exact Submodule.zero_mem _
    | add p q _ _ hp hq => rw [Submodule.coe_add]; exact Submodule.add_mem _ hp hq
    | smul c p _ hp => rw [SetLike.val_smul]; exact Submodule.smul_mem _ _ hp
  rintro x ⟨y, hy, rfl⟩
  exact key y hy

/-- **The one remaining gap, isolated.**

`OddCreationBounded M` says: every state `χᵃ₋ₖ₋₁ v` with level `k ≥ 1` and `v` **odd** lies in
`O₂(W(2))` modulo the fixed finite-dimensional space `M`.

Three remarks on why this is *exactly* the orbifold step and nothing more.

* These states are precisely the even states that the ambient `C₂` kills for a reason invisible
  to `W(2)`: by `SympFermC2.sfCre_one_mul_mem_O₂SF`, `χᵃ₋ₖ₋₁ v = (χᵃ₋₁|0⟩)₍₋₂₎(…)` is a
  `₍₋₂₎`-product of two **odd** states (`sfHighPar_le_O₂SF`), and `O₂(W(2))` is spanned by the
  `₍₋₂₎`-products of two **even** states.
* By `evSF_le_sfBottom_sup_sfHighPar_one` they are, together with `|0⟩` and `χ⁰₋₁χ¹₋₁|0⟩`, all
  of the even part.  So this hypothesis is the *whole* residual content.
* It is not vacuous and `M` cannot be taken to be `0`: `ω²` is a nonzero class of `A₂(W(2))`
  (see the module docstring), so some finite `M` is genuinely needed. -/
def OddCreationBounded (M : Submodule ℂ FockSF) : Prop :=
  ∀ (k : ℕ) (a : Fin 2) (v : FockSF), 1 ≤ k → v ∈ oddSF → sfCre k a * v ∈ M ⊔ O₂W2

/-- **The reduction.**  `C₂`-cofiniteness of the triplet `W(2)` follows from
`OddCreationBounded M` for a single finite-dimensional `M` — i.e. from control of the odd–odd
sector alone.  Everything else (the exterior-algebra spanning, the descent from the subtype
`↥𝒱₀̄` to `FockSF`, the passage to `A₂`) is proved. -/
theorem c2Cofinite_tripletW2_of_oddCreationBounded (M : Submodule ℂ FockSF)
    [FiniteDimensional ℂ M] (h : OddCreationBounded M) : C2Cofinite tripletW2 := by
  haveI hb : FiniteDimensional ℂ ↥sfBottom := by
    rw [sfBottom_def]
    exact FiniteDimensional.span_of_finite ℂ sfBottomSet_finite
  haveI : FiniteDimensional ℂ ↥(M ⊔ sfBottom) := Submodule.finiteDimensional_sup M sfBottom
  refine c2Cofinite_tripletW2_of_evSF_le_sup (M ⊔ sfBottom)
    (le_trans evSF_le_sfBottom_sup_sfHighPar_one (sup_le ?_ ?_))
  · exact le_trans le_sup_right le_sup_left
  · rw [sfHighPar_def, Submodule.span_le]
    rintro _ ⟨k, a, v, hk, hv, rfl⟩
    exact sup_le_sup_right (le_sup_left : M ≤ M ⊔ sfBottom) O₂W2 (h k a v hk hv)

/-! ## §5  The gap descends to level one -/

/-- **Only the level-one members of the gap family matter.**

For `v` odd, `T` trades one level for a translate:
`(k+2)·χᵃ₋ₖ₋₂ v = T(χᵃ₋ₖ₋₁ v) − χᵃ₋ₖ₋₁ (T v)`.
The first term lies in `O₂(W(2))` because `χᵃ₋ₖ₋₁ v` is **even** (`T_mem_O₂W2`), and `T v` is
again odd (`T_mem_evenOdd`), so the second is handled by the inductive hypothesis.  Note this is
the *only* place where the recursion terminates: the level of the single leading operator is a
genuine induction variable, exactly as in `SympFermC2`. -/
theorem oddCreationBounded_of_level_one (M : Submodule ℂ FockSF)
    (h : ∀ (a : Fin 2) (v : FockSF), v ∈ oddSF → sfCre 1 a * v ∈ M ⊔ O₂W2) :
    OddCreationBounded M := by
  intro k a v hk hv
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction n generalizing v with
  | zero => exact h a v hv
  | succ m ih =>
      have hc : ((m : ℂ) + 1 + 1) ≠ 0 := by
        have he : ((m : ℂ) + 1 + 1) = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
        rw [he]
        exact_mod_cast Nat.succ_ne_zero (m + 1)
      have hrec : ((m : ℂ) + 1 + 1) • (sfCre (m + 1 + 1) a * v)
          = T (sfCre (m + 1) a * v) - sfCre (m + 1) a * T v := by
        rw [T_mul, T_sfCre, smul_mul_assoc, add_sub_cancel_left]
        congr 1
        push_cast
        ring
      have hmem : ((m : ℂ) + 1 + 1) • (sfCre (m + 1 + 1) a * v) ∈ M ⊔ O₂W2 := by
        rw [hrec]
        exact Submodule.sub_mem _
          (Submodule.mem_sup_right (T_mem_O₂W2 (sfCre_mul_odd_mem_evSF (m + 1) a hv)))
          (ih (T v) (T_mem_evenOdd hv))
      have h2 := Submodule.smul_mem (M ⊔ O₂W2) ((m : ℂ) + 1 + 1)⁻¹ hmem
      rwa [inv_smul_smul₀ hc] at h2

/-- **The sharpest reduction proved here.**

`C₂`-cofiniteness of the triplet `W(2)` follows from a single statement about the two
weight-one symplectic-fermion generators:

> `χᵃ₋₂ v ∈ O₂(W(2)) + M` for `a ∈ {0,1}`, every **odd** `v`, and one fixed
> finite-dimensional `M`.

Equivalently: the `₍₋₂₎`-products `(χᵃ₋₁|0⟩)₍₋₂₎v` of two **odd** states are, up to finitely
many classes, already `₍₋₂₎`-products of two **even** states.  That is Abe's orbifold step, and
nothing else is missing. -/
theorem c2Cofinite_tripletW2_of_levelOne (M : Submodule ℂ FockSF) [FiniteDimensional ℂ M]
    (h : ∀ (a : Fin 2) (v : FockSF), v ∈ oddSF → sfCre 1 a * v ∈ M ⊔ O₂W2) :
    C2Cofinite tripletW2 :=
  c2Cofinite_tripletW2_of_oddCreationBounded M (oddCreationBounded_of_level_one M h)

/-- The same, with the finite-dimensional space presented as the span of an explicit finite set
of states — the shape in which a completion of this file would supply it. -/
theorem c2Cofinite_tripletW2_of_levelOne_span (S : Set FockSF) (hS : S.Finite)
    (h : ∀ (a : Fin 2) (v : FockSF), v ∈ oddSF →
      sfCre 1 a * v ∈ Submodule.span ℂ S ⊔ O₂W2) :
    C2Cofinite tripletW2 := by
  haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ S) := FiniteDimensional.span_of_finite ℂ hS
  exact c2Cofinite_tripletW2_of_levelOne (Submodule.span ℂ S) h

/-! ## §6  `W(2)` has one-dimensional grade zero -/

/-- **`𝒱₀ = ℂ|0⟩` for `W(2)`** — definitionally `VacuumGradeZero tripletW2`
(`Modularity.BlockZeroMode`), stated here without importing that file. -/
theorem tripletW2_vacuumGradeZero :
    tripletW2.grading 0 ≤ Submodule.span ℂ ({tripletW2.vacuum} : Set ↥evSF) :=
  le_of_eq tripletW2.vacuum_grade

end VOA.TripletDirect

