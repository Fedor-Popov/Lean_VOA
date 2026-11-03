/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.TripletWpAmbient
import VOA.Modules.PairClosure

/-!
# The triplet `W(p)`: strong generation reduced to the finite generator OPE table

`Examples.TripletWpAmbient` reduced the strong-generation hypothesis of the triplet
`C₂`-cofiniteness theorem to a single closure clause, `SmulClosedWp p hp` — but that clause still
quantifies over **all pairs of members** of the iterated-product span and **all** modes `n ∈ ℤ`.
This file applies the general reduction `Modules.PairClosure.iterProdSpan_smul_closed` to collapse
it to the **finite generator OPE table**:

  `smulClosedWp_of_genPairClosed` — `SmulClosedWp p hp` follows from
  `GenPairClosedWp p hp : g₍ⱼ₎h ∈ iterProdSpan (tripGens p)` for the 16 ordered pairs
  `g, h ∈ {ω_λ, E, H, F}` and the non-negative modes `j ≥ 0`.

  `genPairClosedWp_of_bdd` — and the table is **finite**: `j < 4p + 2` suffices, because
  `g₍ⱼ₎h` vanishes for `j ≥ wt g + wt h` (positivity of the deformed grading), and every
  generator has weight `≤ 2p + 1`.  (Per pair the sharp bound is `wt g + wt h`; `4p + 2` is the
  uniform envelope `2·(2p+1)`.)

The chain, fully assembled:

  `GenPairClosedWp p hp` ⟹ `SmulClosedWp` ⟹ `StrongGenWp` ⟹ `AdjoinGenWp`, and with
  `AMOmegaIdentity p hp (3p−1)` this gives `C2Cofinite (tripletWVOA p hp)` and
  `dim A₂ ≤ 48p − 16`  (`c2Cofinite_tripletWVOA_of_genPairs`).

## Nine of the sixteen pairs discharged — including the whole `ω`-block

* **`E, H, F` are Virasoro primary, at every `p`** (`screenGens_primary`,
  `omegaTailWp_all`) — the primarity prerequisite.  Route (§5):
  charged vacua are primary for the background-charge stress tensor (`LBg_latChargeGen_pos`,
  a Fock-vacuum computation), so `F = e^{−α}` and `e^α` are primary; skew symmetry then gives
  `Q ω_λ = 0` (`Qwp_omegaTrip` — `Q` commutes with the deformed Virasoro action), and applying
  the derivation `Q` to `ω₍ⱼ₎F = 0` walks the vanishing up to `H = QF` and `E = QH`.  This
  closes the entire `(ω, ·)` row (`omega_row_of_tail`) and, by skew transport, the `(·, ω)`
  column — 7 pairs.
* `pair_omegaTrip_omegaTrip` — `ω₍ⱼ₎ω ∈ T` for all `j ≥ 0` (free in any VOA:
  `Modules.PairClosure.conformal_smul_conformal_mem_iterProdSpan`).
* `pair_Etrip_Etrip`, `pair_Ftrip_Ftrip` — `E₍ⱼ₎E = F₍ⱼ₎F = 0` for `j ≥ 0` (the lattice
  vanishing `smul_Etrip_Etrip` / `smul_Ftrip_Ftrip`, valid from `j ≥ −2p`).

## What is not proved in this file

The former seven mixed `{E,H,F}` pairs are formally reduced by the exact `Q`-relations,
charge truncation, ordinary skew-symmetry, and the one-dimensional degree-zero Fock space.
At `p = 2`, only three coordinate products remain: `F₍₀₎H`, `F₍₁₎E`, and `F₍₃₎E`
(`loweringPairsWp_two_of_three`).  The other residual is `AMOmegaIdentity 2 hp 5`, the
weight-10 charge-zero identity.  These are not proved in this file; they are proved downstream
at `p = 2`: the three coordinates by `WpC2.threeCoordinateIdentitiesWp_two`
(`Examples.TripletWpTwoMixedClose`), the AM identity by `WpTwoAMFinal.amOmegaIdentity_two`
(`Examples.TripletWpTwoAMFinal`), and strong generation by `Wp.strongGenWp_two`
(`Examples.TripletWpTwoIrrational`).

## Status

Every declaration is proved: `sorry`-free, `admit`-free, `native_decide`-free, and
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).  The theorem
`VOA.pbw` is not used.  `GenPairClosedWp` and `AMOmegaIdentity`
are `def … : Prop`, never proved and never assumed: they appear only as explicit arguments.

## References

* D. Adamović and A. Milas, *On the triplet vertex algebra `W(p)`*, Adv. Math. **217** (2008)
  2664–2699 (arXiv:0707.1857), Prop. 2.3(ii).
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpC2

open scoped BigOperators
open VOA VOA.IntegralLattice
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp

/-! ## §1  The generators are homogeneous of positive, bounded weight -/

/-- Every triplet generator is homogeneous of weight `d` with `1 ≤ d ≤ 2p + 1`
(`ω_λ` has weight `2`, and `E, H, F` have weight `2p − 1`). -/
theorem tripGens_grading_bounded (p : ℕ) (hp : 1 ≤ p) :
    ∀ s ∈ tripGens p, ∃ d : ℤ, 1 ≤ d ∧ d ≤ 2 * (p : ℤ) + 1
      ∧ s ∈ (tripletLatticeVOA p hp).grading d := by
  have hp' : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  intro s hs
  rcases hs with rfl | hs
  · exact ⟨2, by norm_num, by omega, omegaTrip_mem_grading p hp⟩
  rcases hs with rfl | hs
  · exact ⟨2 * (p : ℤ) - 1, by omega, by omega, Etrip_mem_grading p hp⟩
  rcases hs with rfl | hs
  · exact ⟨2 * (p : ℤ) - 1, by omega, by omega, Htrip_mem_grading p hp⟩
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨2 * (p : ℤ) - 1, by omega, by omega, Ftrip_mem_grading p hp⟩

/-- The positive-homogeneity input of `Modules.PairClosure`. -/
theorem tripGens_posHomog (p : ℕ) (hp : 1 ≤ p) :
    ∀ s ∈ tripGens p, ∃ d : ℤ, 1 ≤ d ∧ s ∈ (tripletLatticeVOA p hp).grading d := by
  intro s hs
  obtain ⟨d, hd1, _, hdm⟩ := tripGens_grading_bounded p hp s hs
  exact ⟨d, hd1, hdm⟩

/-! ## §2  The finite-table hypothesis, and the reduction -/

/-- **The generator OPE table** — the residual of Adamović–Milas Proposition 2.3(ii) in its
smallest form: each non-negative product `g₍ⱼ₎h` of two of the four generators `{ω_λ, E, H, F}`
lies in the span of the iterated strictly-negative-mode words.  By `genPairClosedWp_of_bdd` only
`0 ≤ j < 4p + 2` matters, so this is a finite table of Fock-space computations. -/
def GenPairClosedWp (p : ℕ) (hp : 1 ≤ p) : Prop :=
  ∀ g ∈ tripGens p, ∀ h ∈ tripGens p, ∀ j : ℤ, 0 ≤ j →
    (tripletLatticeVOA p hp).smul g j h ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)

/-- **The table is finite**: modes `j ≥ 4p + 2 ≥ wt g + wt h` annihilate, so only
`0 ≤ j < 4p + 2` needs to be computed. -/
theorem genPairClosedWp_of_bdd (p : ℕ) (hp : 1 ≤ p)
    (h : ∀ g ∈ tripGens p, ∀ h' ∈ tripGens p, ∀ j : ℤ, 0 ≤ j → j < 4 * (p : ℤ) + 2 →
      (tripletLatticeVOA p hp).smul g j h'
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) :
    GenPairClosedWp p hp := by
  intro g hg h' hh' j hj
  by_cases hlt : j < 4 * (p : ℤ) + 2
  · exact h g hg h' hh' j hj hlt
  · push_neg at hlt
    obtain ⟨dg, _, hdg2, hdgm⟩ := tripGens_grading_bounded p hp g hg
    obtain ⟨dh, _, hdh2, hdhm⟩ := tripGens_grading_bounded p hp h' hh'
    rw [smul_grading_neg_eq_zero (tripletLatticeVOA p hp) hdgm hdhm (by omega)]
    exact zero_mem _

/-- **The reduction**: the finite generator OPE table implies the full closure clause
`SmulClosedWp p hp` — the residual of `Examples.TripletWpAmbient` §4.  This is
`Modules.PairClosure.iterProdSpan_smul_closed` at `S = tripGens p`. -/
theorem smulClosedWp_of_genPairClosed (p : ℕ) (hp : 1 ≤ p) (h : GenPairClosedWp p hp) :
    SmulClosedWp p hp := by
  intro u hu n v hv
  exact iterProdSpan_smul_closed (tripletLatticeVOA p hp) (tripGens p)
    (tripGens_posHomog p hp) h hu n hv

/-- The table implies strong generation (Adamović–Milas Prop. 2.3(ii)). -/
theorem strongGenWp_of_genPairClosed (p : ℕ) (hp : 1 ≤ p) (h : GenPairClosedWp p hp) :
    StrongGenWp p hp :=
  strongGenWp_of_smulClosed p hp (smulClosedWp_of_genPairClosed p hp h)

/-- The table implies algebra generation of `A₂(W(p))`. -/
theorem adjoinGenWp_of_genPairClosed (p : ℕ) (hp : 1 ≤ p) (h : GenPairClosedWp p hp) :
    AdjoinGenWp p hp :=
  adjoinGenWp_of_strongGenWp p hp (strongGenWp_of_genPairClosed p hp h)

/-- **`C₂`-cofiniteness of `W(p)` from the two finite residuals**: the generator OPE table
`GenPairClosedWp p hp` and the single lattice identity `AMOmegaIdentity p hp (3p−1)`
(Adamović–Milas Corollary 4.6).  Both are finite Fock-space computations at each fixed `p`.
The dimension bound is `dim_ℂ A₂(W(p)) ≤ 16(3p−1) = 48p − 16`.

⚠ Both inputs are hypotheses; neither is proved anywhere in this repository. -/
theorem c2Cofinite_tripletWVOA_of_genPairs (p : ℕ) (hp : 1 ≤ p)
    (hpairs : GenPairClosedWp p hp) (hAM : AMOmegaIdentity p hp (3 * p - 1)) :
    C2Cofinite (tripletWVOA p hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA p hp)) ≤ 16 * (3 * p - 1) :=
  c2Cofinite_tripletWVOA_of_amCor44 p hp (3 * p - 1)
    (adjoinGenWp_of_genPairClosed p hp hpairs) hAM

/-- The `p = 2` instance: the table (`0 ≤ j < 10`) plus `AMOmegaIdentity 2 hp 5` give
`C2Cofinite (tripletWVOA 2 hp)` and `dim A₂ ≤ 80`.

⚠ This is `W(2)` as built inside the deformed lattice VOA `V_{L_2}`; no isomorphism with the
symplectic-fermion `SympFerm.tripletW2` is proved or claimed anywhere in this repository. -/
theorem c2Cofinite_tripletWVOA_two_of_genPairs (hp : 1 ≤ 2)
    (hpairs : GenPairClosedWp 2 hp) (hAM : AMOmegaIdentity 2 hp 5) :
    C2Cofinite (tripletWVOA 2 hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA 2 hp)) ≤ 80 := by
  have h := c2Cofinite_tripletWVOA_of_genPairs 2 hp hpairs
    (by simpa using hAM)
  simpa using h

/-! ## §3  Three of the sixteen pairs, discharged -/

/-- **The `(ω, ω)` pair is free**: `ω₍ⱼ₎ω ∈ T` for every `j ≥ 0` — general VOA fact
(`conformal_smul_conformal_mem_iterProdSpan`), since `ω_λ` is the conformal vector of
`tripletLatticeVOA p hp` and a member of `tripGens p`. -/
theorem pair_omegaTrip_omegaTrip (p : ℕ) (hp : 1 ≤ p) (j : ℤ) (hj : 0 ≤ j) :
    (tripletLatticeVOA p hp).smul (omegaTrip p) j (omegaTrip p)
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) :=
  conformal_smul_conformal_mem_iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
    (omegaTrip_mem_tripGens p) j hj

/-- **The `(E, E)` pair vanishes**: `E₍ⱼ₎E = 0` for `j ≥ 0` (`smul_Etrip_Etrip`). -/
theorem pair_Etrip_Etrip (p : ℕ) (hp : 1 ≤ p) (j : ℤ) (hj : 0 ≤ j) :
    (tripletLatticeVOA p hp).smul (Etrip p) j (Etrip p)
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  have hp' : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  rw [smul_Etrip_Etrip p hp (by omega : -(2 * (p : ℤ)) ≤ j)]
  exact zero_mem _

/-- **The `(F, F)` pair vanishes**: `F₍ⱼ₎F = 0` for `j ≥ 0` (`smul_Ftrip_Ftrip`). -/
theorem pair_Ftrip_Ftrip (p : ℕ) (hp : 1 ≤ p) (j : ℤ) (hj : 0 ≤ j) :
    (tripletLatticeVOA p hp).smul (Ftrip p) j (Ftrip p)
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  have hp' : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  rw [smul_Ftrip_Ftrip p hp (by omega : -(2 * (p : ℤ)) ≤ j)]
  exact zero_mem _

/-! ## §4  The sharp residual: primarity tails + mixed screening pairs

The `ω`-modes `ω₍₀₎ = L₋₁` and `ω₍₁₎ = L₀` preserve the span for free
(`conformal_smul_zero_mem_iterProdSpan` / `conformal_smul_one_mem_iterProdSpan`), and the whole
`(g, ω)` column follows from the `(ω, g)` row by skew transport
(`smul_mem_iterProdSpan_of_skew`).  So the table collapses to **two** finite families of genuine
lattice computations. -/

/-- The three screening generators `{E, H, F}` (the non-conformal generators). -/
noncomputable def screenGens (p : ℕ) : Set (LatModuleGen (latP p)) :=
  {Etrip p, Htrip p, Ftrip p}

theorem screenGens_subset_tripGens (p : ℕ) : screenGens p ⊆ tripGens p := by
  intro s hs
  rcases hs with rfl | hs
  · exact Etrip_mem_tripGens p
  rcases hs with rfl | hs
  · exact Htrip_mem_tripGens p
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    exact Ftrip_mem_tripGens p

/-- Every triplet generator is `ω_λ` or a screening generator. -/
theorem tripGens_cases (p : ℕ) {s : LatModuleGen (latP p)} (hs : s ∈ tripGens p) :
    s = omegaTrip p ∨ s ∈ screenGens p := by
  rcases hs with rfl | hs
  · exact Or.inl rfl
  · exact Or.inr hs

/-- Every screening generator has deformed weight `2p − 1`. -/
theorem screenGens_mem_grading (p : ℕ) (hp : 1 ≤ p) :
    ∀ g ∈ screenGens p, g ∈ (tripletLatticeVOA p hp).grading (2 * (p : ℤ) - 1) := by
  intro g hg
  rcases hg with rfl | hg
  · exact Etrip_mem_grading p hp
  rcases hg with rfl | hg
  · exact Htrip_mem_grading p hp
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact Ftrip_mem_grading p hp

/-- **The primarity tails**: the higher conformal modes `ω₍ⱼ₎g`, `j ≥ 2`, of the three
screening generators land in the span.  Adamović–Milas assert more — `E, H, F` are Virasoro
**primary**, so these products all *vanish* — and §5 below **proves** exactly that
(`omegaTailWp_all`), so this `Prop` is a theorem; it is kept named because the intermediate
reductions (`omega_row_of_tail`, `genPairClosedWp_of_tail_mixed`) consume it modularly. -/
def OmegaTailWp (p : ℕ) (hp : 1 ≤ p) : Prop :=
  ∀ g ∈ screenGens p, ∀ j : ℤ, 2 ≤ j →
    (tripletLatticeVOA p hp).smul (omegaTrip p) j g
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)

/-- **(Residual 2) The mixed screening pairs**: `g₍ⱼ₎h ∈ T` for `g, h ∈ {E, H, F}`, `j ≥ 0`.
By `mixedPairsWp_of_bdd` only `0 ≤ j < 4p − 2` matters, and the `(E,E)` and `(F,F)` pairs are
already zero (`pair_Etrip_Etrip`, `pair_Ftrip_Ftrip`). -/
def MixedPairsWp (p : ℕ) (hp : 1 ≤ p) : Prop :=
  ∀ g ∈ screenGens p, ∀ h ∈ screenGens p, ∀ j : ℤ, 0 ≤ j →
    (tripletLatticeVOA p hp).smul g j h
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)

/-- The genuinely computational part of the mixed table can be taken to be just the two
`F`-rows `F₍ⱼ₎H` and `F₍ⱼ₎E`.  The long screening `Q` and the exact relations obtained by applying
it to `F₍ⱼ₎F = 0` recover the other five ordered pairs; see
`mixedPairsWp_of_loweringPairs` below. -/
def LoweringPairsWp (p : ℕ) (hp : 1 ≤ p) : Prop :=
  (∀ j : ℤ, 0 ≤ j →
      (tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p)
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p))
    ∧
  (∀ j : ℤ, 0 ≤ j →
      (tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p)
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p))

/-- The tail hypothesis is finite: `ω₍ⱼ₎g = 0` for `j ≥ 2p + 1 = wt ω + wt g`. -/
theorem omegaTailWp_of_bdd (p : ℕ) (hp : 1 ≤ p)
    (h : ∀ g ∈ screenGens p, ∀ j : ℤ, 2 ≤ j → j < 2 * (p : ℤ) + 1 →
      (tripletLatticeVOA p hp).smul (omegaTrip p) j g
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) :
    OmegaTailWp p hp := by
  intro g hg j hj
  by_cases hlt : j < 2 * (p : ℤ) + 1
  · exact h g hg j hj hlt
  · push_neg at hlt
    rw [smul_grading_neg_eq_zero (tripletLatticeVOA p hp) (omegaTrip_mem_grading p hp)
      (screenGens_mem_grading p hp g hg) (by omega)]
    exact zero_mem _

/-- The mixed hypothesis is finite: `g₍ⱼ₎h = 0` for `j ≥ 4p − 2 = wt g + wt h`. -/
theorem mixedPairsWp_of_bdd (p : ℕ) (hp : 1 ≤ p)
    (h : ∀ g ∈ screenGens p, ∀ h' ∈ screenGens p, ∀ j : ℤ, 0 ≤ j → j < 4 * (p : ℤ) - 2 →
      (tripletLatticeVOA p hp).smul g j h'
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) :
    MixedPairsWp p hp := by
  intro g hg h' hh' j hj
  by_cases hlt : j < 4 * (p : ℤ) - 2
  · exact h g hg h' hh' j hj hlt
  · push_neg at hlt
    rw [smul_grading_neg_eq_zero (tripletLatticeVOA p hp)
      (screenGens_mem_grading p hp g hg) (screenGens_mem_grading p hp h' hh') (by omega)]
    exact zero_mem _

/-- The two lowering rows are finite: both products vanish by grading for
`j ≥ 4p - 2`.  At `p = 2` the only inputs are the twelve products with `0 ≤ j ≤ 5`. -/
theorem loweringPairsWp_of_bdd (p : ℕ) (hp : 1 ≤ p)
    (hFH : ∀ j : ℤ, 0 ≤ j → j < 4 * (p : ℤ) - 2 →
      (tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p)
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p))
    (hFE : ∀ j : ℤ, 0 ≤ j → j < 4 * (p : ℤ) - 2 →
      (tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p)
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) :
    LoweringPairsWp p hp := by
  constructor
  · intro j hj
    by_cases hlt : j < 4 * (p : ℤ) - 2
    · exact hFH j hj hlt
    · push_neg at hlt
      rw [smul_grading_neg_eq_zero (tripletLatticeVOA p hp)
        (Ftrip_mem_grading p hp) (Htrip_mem_grading p hp) (by omega)]
      exact zero_mem _
  · intro j hj
    by_cases hlt : j < 4 * (p : ℤ) - 2
    · exact hFE j hj hlt
    · push_neg at hlt
      rw [smul_grading_neg_eq_zero (tripletLatticeVOA p hp)
        (Ftrip_mem_grading p hp) (Etrip_mem_grading p hp) (by omega)]
      exact zero_mem _

/-- The `F₍ⱼ₎H` row truncates earlier than the generic weight bound.  Its charge is `-α`, and its
oscillator degree is `2p - 2 - j`; hence it vanishes already for `j ≥ 2p - 1`.  At `p = 2` only
`j = 0,1,2` remain. -/
theorem smul_Ftrip_Htrip_eq_zero_of_ge (p : ℕ) (hp : 1 ≤ p) {j : ℤ}
    (hj : 2 * (p : ℤ) - 1 ≤ j) :
    (tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p) = 0 := by
  rw [PreVertexAlgebra.smul_def, Ftrip, Screen.Fscr, Y_latChargeGen, Htrip,
    Screen.Hscr_eq (latP p) (alphaP p) p hp (latP_form_alpha p), mode_apply,
    map_smul, Yeαvec_tmul]
  have hS := vSchur_mem_gradingZN_alphaP p
  have hE := Screen.EEVec_mem_gradingZN (latP p) (-alphaP p) (-j - 1) hS
  have hneg : ((2 * p - 1 : ℕ) : ℤ) + (-j - 1) < 0 := by omega
  rw [HeisenbergN.gradingZN_of_neg hneg, Submodule.mem_bot] at hE
  simp only [map_zero, sub_zero, add_zero]
  rw [hE, latStateGen, TensorProduct.zero_tmul, smul_zero, smul_zero]

/-- Exact Fock-coordinate formula for the first residual row.  At `p = 2`, the two modes left by
the sharp charge cutoff are obtained by substituting `j = 0,2`; the degree-zero argument below
then discharges `j = 2`, leaving only `j = 0` as a coordinate residual. -/
theorem chargeOsc_vSchur (L : IntegralLattice) (hPos : L.PosDef)
    (alpha beta : L.carrier) (m N : ℕ) (hm : 1 ≤ m) :
    chargeOsc L beta (m : ℤ) (vSchur L alpha N) =
      if m ≤ N then ((L.form alpha beta : ℤ) : ℂ) • vSchur L alpha (N - m) else 0 := by
  have h := congrArg (fun f : Module.End ℂ (HeisenbergN.FockN (rank L)) =>
      f (HeisenbergN.vacuumN (rank L)))
    (chargeOsc_comp_EminusVec L hPos alpha beta m N hm)
  dsimp only at h
  simp only [LinearMap.comp_apply, LinearMap.add_apply, EminusVec_vacuum,
    chargeOsc_vacuum L beta (m : ℤ) (by positivity : (0 : ℤ) ≤ (m : ℤ)), map_zero,
    zero_add] at h
  split_ifs at h ⊢ <;>
    simpa [LinearMap.smul_apply, LinearMap.zero_apply, EminusVec_vacuum] using h

theorem smul_Ftrip_Htrip_eq_fock (p : ℕ) (hp : 1 ≤ p) (j : ℤ) :
    (tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p) =
      latticeCocycle (latP p) (alphaP p) (-alphaP p) •
        latStateGen (latP p)
          (EEVec (latP p) (-alphaP p) (-j - 1)
            (vSchur (latP p) (alphaP p) (2 * p - 1))) (-alphaP p) := by
  rw [PreVertexAlgebra.smul_def, Ftrip, Screen.Fscr, Y_latChargeGen, Htrip,
    Screen.Hscr_eq (latP p) (alphaP p) p hp (latP_form_alpha p), mode_apply,
    map_smul, Yeαvec_tmul, map_zero, sub_zero, add_zero,
    latticeCocycle_zero_right, one_smul]

/-- Exact Fock-coordinate formula for the second residual row.  At `p = 2` its dressing index is
`3-j`; after the skew/Q reduction the odd modes are `j = 1,3,5`, and the degree-zero argument
below discharges `j = 5`. -/
theorem smul_Ftrip_Etrip_eq_fock (p : ℕ) (hp : 1 ≤ p) (j : ℤ) :
    (tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p) =
      latticeCocycle (latP p) (alphaP p) (-alphaP p) •
        latticeCocycle (latP p) (-alphaP p) (alphaP p) •
          latStateGen (latP p)
            (EEVec (latP p) (-alphaP p) (2 * (p : ℤ) - 1 - j)
              (EEVec (latP p) (alphaP p) (-1)
                (vSchur (latP p) (alphaP p) (2 * p - 1)))) 0 := by
  have hform : (latP p).form (-alphaP p) (alphaP p) = -(2 * (p : ℤ)) := by
    rw [map_neg, LinearMap.neg_apply, latP_form_alpha]
  rw [PreVertexAlgebra.smul_def, Ftrip, Screen.Fscr, Y_latChargeGen, Etrip,
    Screen.Escr_eq (latP p) (alphaP p) p hp (latP_form_alpha p), mode_apply,
    map_smul, Yeαvec_tmul, hform, neg_add_cancel]
  congr 4 <;> ring

/-- The top `FH` residual at `p = 2` is automatic: its Fock factor has degree zero, hence is a
scalar vacuum, so the product is a scalar multiple of the generator `F`. -/
theorem smul_Ftrip_Htrip_two_mem (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).smul (Ftrip 2) 2 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2) := by
  let W := tripletLatticeVOA 2 hp
  let T := iterProdSpan W (tripGens 2)
  have hS : vSchur (latP 2) (alphaP 2) 3 ∈ HeisenbergN.gradingZN (rank (latP 2)) 3 :=
    HeisenbergN.mem_gradingZN_of_gradingWN
      (Screen.vSchur_mem_gradingWN (latP 2) (alphaP 2) 3)
  have hE := Screen.EEVec_mem_gradingZN (latP 2) (-alphaP 2) (-3) hS
  rw [show (3 : ℤ) + (-3) = 0 by norm_num,
    HeisenbergN.gradingZN_zero_eq_span_vacuum,
    Submodule.mem_span_singleton] at hE
  obtain ⟨c, hc⟩ := hE
  rw [smul_Ftrip_Htrip_eq_fock 2 hp 2, show (-(2 : ℤ) - 1) = -3 by norm_num, ← hc,
    latStateGen, TensorProduct.smul_tmul']
  exact Submodule.smul_mem T _ (Submodule.smul_mem T _
    (subset_iterProdSpan W (tripGens 2) (Ftrip_mem_tripGens 2)))

/-- The highest `FE` residual at `p = 2` is likewise automatic: after the two dressings its
charge-zero Fock factor has degree zero, so it is a scalar multiple of the VOA vacuum. -/
theorem smul_Ftrip_Etrip_five_mem (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).smul (Ftrip 2) 5 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2) := by
  let W := tripletLatticeVOA 2 hp
  let T := iterProdSpan W (tripGens 2)
  have hS : vSchur (latP 2) (alphaP 2) 3 ∈ HeisenbergN.gradingZN (rank (latP 2)) 3 :=
    HeisenbergN.mem_gradingZN_of_gradingWN
      (Screen.vSchur_mem_gradingWN (latP 2) (alphaP 2) 3)
  have hinner := Screen.EEVec_mem_gradingZN (latP 2) (alphaP 2) (-1) hS
  have houter := Screen.EEVec_mem_gradingZN (latP 2) (-alphaP 2) (-2) hinner
  rw [show (3 : ℤ) + (-1) + (-2) = 0 by norm_num,
    HeisenbergN.gradingZN_zero_eq_span_vacuum,
    Submodule.mem_span_singleton] at houter
  obtain ⟨c, hc⟩ := houter
  rw [smul_Ftrip_Etrip_eq_fock 2 hp 5]
  norm_num only at ⊢
  rw [← hc, latStateGen, TensorProduct.smul_tmul']
  exact Submodule.smul_mem T _ (Submodule.smul_mem T _ (Submodule.smul_mem T _
    (vacuum_mem_iterProdSpan W (tripGens 2))))

/-- At `p = 2`, ordinary skew-symmetry and `H₍ₙ₎F = -F₍ₙ₎H` remove the odd mode from the
computational ledger: membership of `F₍₂₎H` implies membership of `F₍₁₎H`.  All skew terms above
`j = 1` vanish because the corresponding mode is at least `3`, where the charge-sector bound
`smul_Ftrip_Htrip_eq_zero_of_ge` applies. -/
theorem smul_Ftrip_Htrip_one_mem_of_two (hp : 1 ≤ 2)
    (h2 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 2 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2)) :
    (tripletLatticeVOA 2 hp).smul (Ftrip 2) 1 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2) := by
  let W := tripletLatticeVOA 2 hp
  let T := iterProdSpan W (tripGens 2)
  have hmode : ∀ j : ℕ,
      (W.Y (Htrip 2)) (-(1 : ℤ) - 1 - (j : ℤ)) (Ftrip 2)
        = W.smul (Htrip 2) (1 + (j : ℤ)) (Ftrip 2) := by
    intro j
    rw [PreVertexAlgebra.smul_def, mode_apply,
      show (-(1 + (j : ℤ)) - 1 : ℤ) = -(1 : ℤ) - 1 - (j : ℤ) from by ring]
  have hsupport : Function.support (fun j : ℕ =>
      ((j.factorial : ℂ)⁻¹) • (sgn (-(1 : ℤ) - 1 - (j : ℤ))) •
        ((W.toPreVertexAlgebra.T ^ j)
          ((W.Y (Htrip 2)) (-(1 : ℤ) - 1 - (j : ℤ)) (Ftrip 2))))
      ⊆ (Finset.range 2 : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hj
    change ((j.factorial : ℂ)⁻¹) • (sgn (-(1 : ℤ) - 1 - (j : ℤ))) •
      ((W.toPreVertexAlgebra.T ^ j)
        ((W.Y (Htrip 2)) (-(1 : ℤ) - 1 - (j : ℤ)) (Ftrip 2))) = 0
    rw [hmode j]
    have hrel := HF_add_FH 2 hp (n := 1 + (j : ℤ)) (by omega)
    have hHF : W.smul (Htrip 2) (1 + (j : ℤ)) (Ftrip 2)
        = -W.smul (Ftrip 2) (1 + (j : ℤ)) (Htrip 2) := by
      rw [add_eq_zero_iff_eq_neg] at hrel
      exact hrel
    rw [hHF, smul_Ftrip_Htrip_eq_zero_of_ge 2 hp (by omega), neg_zero, map_zero,
      smul_zero, smul_zero]
  have hsk := VertexOperatorAlgebra.skew_mode W (Ftrip 2) (Htrip 2) 1
  rw [finsum_eq_finsetSum_of_support_subset _ hsupport, Finset.sum_range_succ,
    Finset.sum_range_one] at hsk
  have hrel1 := HF_add_FH 2 hp (n := 1) (by norm_num)
  have hrel2 := HF_add_FH 2 hp (n := 2) (by norm_num)
  have hHF1 : W.smul (Htrip 2) 1 (Ftrip 2) = -W.smul (Ftrip 2) 1 (Htrip 2) := by
    rw [add_eq_zero_iff_eq_neg] at hrel1
    exact hrel1
  have hHF2 : W.smul (Htrip 2) 2 (Ftrip 2) = -W.smul (Ftrip 2) 2 (Htrip 2) := by
    rw [add_eq_zero_iff_eq_neg] at hrel2
    exact hrel2
  rw [hmode 0, hmode 1] at hsk
  norm_num only at hsk
  rw [hHF1, hHF2] at hsk
  rw [show (sgn (-2 : ℤ)) = 1 by rw [sgn, if_pos (by decide)],
    show (sgn (-3 : ℤ)) = -1 by rw [sgn, if_neg (by decide)],
    pow_zero, pow_one, Module.End.one_apply, map_neg] at hsk
  simp only [one_smul] at hsk
  have hsign : (-1 : ℂ) •
      (-W.toPreVertexAlgebra.T (W.smul (Ftrip 2) 2 (Htrip 2))) =
      W.toPreVertexAlgebra.T (W.smul (Ftrip 2) 2 (Htrip 2)) := by
    simp
  rw [hsign] at hsk
  have hT2 : W.toPreVertexAlgebra.T (W.smul (Ftrip 2) 2 (Htrip 2)) ∈ T :=
    T_pow_mem_iterProdSpan W (tripGens 2) 1 h2
  have hdouble : W.smul (Ftrip 2) 1 (Htrip 2) +
      W.smul (Ftrip 2) 1 (Htrip 2) =
      W.toPreVertexAlgebra.T (W.smul (Ftrip 2) 2 (Htrip 2)) := by
    calc
      _ = (-W.smul (Ftrip 2) 1 (Htrip 2) +
          W.toPreVertexAlgebra.T (W.smul (Ftrip 2) 2 (Htrip 2))) +
          W.smul (Ftrip 2) 1 (Htrip 2) :=
        congrArg (fun z => z + W.smul (Ftrip 2) 1 (Htrip 2)) hsk
      _ = _ := by abel
  have hdouble_mem : W.smul (Ftrip 2) 1 (Htrip 2) +
      W.smul (Ftrip 2) 1 (Htrip 2) ∈ T := by
    rw [hdouble]
    exact hT2
  have hscaled := Submodule.smul_mem T (2 : ℂ)⁻¹ hdouble_mem
  have hhalf : (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1 := by norm_num
  simpa only [smul_add, ← add_smul, hhalf, one_smul] using hscaled

/-- The sharp finite form of the two-row residual.  Only `F₍ⱼ₎H` with
`j < 2p - 1` and `F₍ⱼ₎E` with `j < 4p - 2` need computation. -/
theorem loweringPairsWp_of_sharp_bdd (p : ℕ) (hp : 1 ≤ p)
    (hFH : ∀ j : ℤ, 0 ≤ j → j < 2 * (p : ℤ) - 1 →
      (tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p)
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p))
    (hFE : ∀ j : ℤ, 0 ≤ j → j < 4 * (p : ℤ) - 2 →
      (tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p)
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) :
    LoweringPairsWp p hp := by
  apply loweringPairsWp_of_bdd p hp
  · intro j hj _
    by_cases hlt : j < 2 * (p : ℤ) - 1
    · exact hFH j hj hlt
    · push_neg at hlt
      rw [smul_Ftrip_Htrip_eq_zero_of_ge p hp hlt]
      exact zero_mem _
  · exact hFE

/-- At `p = 2`, exactly nine explicit products suffice: `F₍ⱼ₎H` for `j = 0,1,2` and
`F₍ⱼ₎E` for `j = 0,…,5`. -/
theorem loweringPairsWp_two_of_nine (hp : 1 ≤ 2)
    (hFH : ∀ j : ℤ, 0 ≤ j → j < 3 →
      (tripletLatticeVOA 2 hp).smul (Ftrip 2) j (Htrip 2)
        ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE : ∀ j : ℤ, 0 ≤ j → j < 6 →
      (tripletLatticeVOA 2 hp).smul (Ftrip 2) j (Etrip 2)
        ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2)) :
    LoweringPairsWp 2 hp := by
  apply loweringPairsWp_of_sharp_bdd 2 hp
  · simpa using hFH
  · simpa using hFE

/-- At `p = 2`, skew-symmetry removes `F₍₁₎H`: only `F₍₀₎H`, `F₍₂₎H`, and the
six products `F₍ⱼ₎E` for `0 ≤ j ≤ 5` need be supplied. -/
theorem loweringPairsWp_two_of_eight (hp : 1 ≤ 2)
    (hFH0 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 0 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFH2 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 2 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE : ∀ j : ℤ, 0 ≤ j → j < 6 →
      (tripletLatticeVOA 2 hp).smul (Ftrip 2) j (Etrip 2)
        ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2)) :
    LoweringPairsWp 2 hp := by
  apply loweringPairsWp_two_of_nine hp
  · intro j hj0 hj3
    interval_cases j
    · exact hFH0
    · exact smul_Ftrip_Htrip_one_mem_of_two hp hFH2
    · exact hFH2
  · exact hFE

/-- The `(ω, g)` row, assembled: `ω₍ⱼ₎g ∈ T` for every `j ≥ 0` and `g ∈ tripGens p`, from the
tail hypothesis alone.  (`j = 0, 1` are the free `L₋₁`/`L₀` cases; `j ≥ 2` is the tail for
screening `g` and `pair_omegaTrip_omegaTrip` for `g = ω`.) -/
theorem omega_row_of_tail (p : ℕ) (hp : 1 ≤ p) (htail : OmegaTailWp p hp) :
    ∀ g ∈ tripGens p, ∀ j : ℤ, 0 ≤ j →
      (tripletLatticeVOA p hp).smul (omegaTrip p) j g
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  intro g hg j hj
  rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j from by omega) with rfl | rfl | h2
  · exact conformal_smul_zero_mem_iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
      (subset_iterProdSpan (tripletLatticeVOA p hp) (tripGens p) hg)
  · exact conformal_smul_one_mem_iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
      (tripGens_posHomog p hp)
      (subset_iterProdSpan (tripletLatticeVOA p hp) (tripGens p) hg)
  · rcases tripGens_cases p hg with rfl | hscr
    · exact pair_omegaTrip_omegaTrip p hp j hj
    · exact htail g hscr j h2

/-- **The two finite residuals close the whole table**: `GenPairClosedWp p hp` follows from
the primarity tails and the mixed screening pairs.  The `(ω, ·)` row is `omega_row_of_tail`, the
`(·, ω)` column is its skew transport, and `(ω, ω)` is free. -/
theorem genPairClosedWp_of_tail_mixed (p : ℕ) (hp : 1 ≤ p)
    (htail : OmegaTailWp p hp) (hmixed : MixedPairsWp p hp) :
    GenPairClosedWp p hp := by
  intro g hg h hh j hj
  rcases tripGens_cases p hg with rfl | hgscr
  · exact omega_row_of_tail p hp htail h hh j hj
  rcases tripGens_cases p hh with rfl | hhscr
  · -- the (g, ω) column, by skew transport from the (ω, g) row
    exact smul_mem_iterProdSpan_of_skew (tripletLatticeVOA p hp) (tripGens p) g (omegaTrip p) j
      (fun k hk => omega_row_of_tail p hp htail g (screenGens_subset_tripGens p hgscr)
        k (le_trans hj hk))
  · exact hmixed g hgscr h hhscr j hj

/-- **`C₂`-cofiniteness of `W(p)` from three finite lattice residuals**: the primarity
tails (`L₁g, …, L_{2p−1}g` for `g ∈ {E,H,F}`), the mixed screening pairs (`g₍ⱼ₎h`,
`0 ≤ j < 4p − 2`), and the Adamović–Milas `ω̄`-identity in weight `6p − 2`.  Each is a finite
Fock-space computation at fixed `p`.

(The tail hypothesis is in fact a theorem — `omegaTailWp_all` in §5 below — so the sharp form is
`c2Cofinite_tripletWVOA_of_mixed_AM` in §6, with **two** residuals.  This three-hypothesis form
is kept as the modular intermediate.) -/
theorem c2Cofinite_tripletWVOA_of_tail_mixed (p : ℕ) (hp : 1 ≤ p)
    (htail : OmegaTailWp p hp) (hmixed : MixedPairsWp p hp)
    (hAM : AMOmegaIdentity p hp (3 * p - 1)) :
    C2Cofinite (tripletWVOA p hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA p hp)) ≤ 16 * (3 * p - 1) :=
  c2Cofinite_tripletWVOA_of_genPairs p hp (genPairClosedWp_of_tail_mixed p hp htail hmixed) hAM

/-- The `p = 2` instance: `C2Cofinite (tripletWVOA 2 hp)` and `dim A₂ ≤ 80` from
`OmegaTailWp 2` (nine products `L₁g, L₂g, L₃g`, `g ∈ {E,H,F}`), `MixedPairsWp 2`
(`g₍ⱼ₎h`, `0 ≤ j ≤ 5`), and `AMOmegaIdentity 2 hp 5` (the weight-`10` identity in `V_{L_2}`). -/
theorem c2Cofinite_tripletWVOA_two_of_tail_mixed (hp : 1 ≤ 2)
    (htail : OmegaTailWp 2 hp) (hmixed : MixedPairsWp 2 hp)
    (hAM : AMOmegaIdentity 2 hp 5) :
    C2Cofinite (tripletWVOA 2 hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA 2 hp)) ≤ 80 :=
  c2Cofinite_tripletWVOA_two_of_genPairs hp
    (genPairClosedWp_of_tail_mixed 2 hp htail hmixed) hAM

/-! ## §5  Residual 1 DISCHARGED: `E, H, F` are Virasoro primary, at every `p`

The route is free-field plus formal, no Schur-state computation anywhere:

1. **Charged vacua are primary** (`LBg_latChargeGen_pos`): on the Fock vacuum of the charge-`β`
   sector every component of `L_n^λ = Lₙ + charge oscillator + weight shift − (n+1)λ(n)`
   annihilates for `n ≥ 1` (`LvirN_vacuum`, `chargeOsc_vacuum`, `bgOsc_vacuum`, and the `δ_{n,0}`
   scalars).  In particular `F = e^{−α}` is primary — and so is `e^α`.
2. **`Q ω_λ = 0`** (`Qwp_omegaTrip`): skew symmetry
   `(e^α)₍₀₎ω = ∑ⱼ ±(1/j!)Tʲ(ω₍ⱼ₎e^α)` collapses to `−Te^α + T(L₀e^α) = −Te^α + Te^α = 0`,
   using that `e^α` is primary of deformed weight `1` — the defining property of the long
   screening.  This is the statement that `Q` commutes with the whole deformed Virasoro action.
3. **Leibniz descent** (`omegaTrip_smul_Htrip_tail`, `omegaTrip_smul_Etrip_tail`): applying the
   derivation `Q` to `ω₍ⱼ₎F = 0` gives `(Qω)₍ⱼ₎F + ω₍ⱼ₎H = 0`, hence `ω₍ⱼ₎H = 0`; once more for
   `E = QH`. -/

/-- The background oscillator kills the Fock vacuum at non-negative modes. -/
theorem bgOsc_vacuum (L : IntegralLattice) (lam : Fin (rank L) → ℂ) {m : ℤ} (hm : 0 ≤ m) :
    BgA.bgOsc L lam m (HeisenbergN.vacuumN (rank L)) = 0 := by
  rw [BgA.bgOsc_apply]
  exact Finset.sum_eq_zero fun a _ => by
    rw [HeisenbergN.oscN_vacuum (rank L) 1 a m hm, smul_zero]

/-- The sector Virasoro mode kills the Fock vacuum at strictly positive modes: every summand of
`Lₙ^λ = Lₙ + γ(n) + δ_{n,0}·½⟨γ,γ⟩ − (n+1)(λ(n) + δ_{n,0}⟨λ,γ⟩)` vanishes for `n ≥ 1`. -/
theorem LSecBg_vacuum_pos (L : IntegralLattice) (lam : Fin (rank L) → ℂ) (γ : L.carrier)
    {n : ℤ} (hn : 1 ≤ n) :
    BgA.LSecBg L lam γ n (HeisenbergN.vacuumN (rank L)) = 0 := by
  rw [BgA.LSecBg, LinearMap.sub_apply, LinearMap.smul_apply, BgA.OpSec_apply,
    BgA.BetaSec_apply, BgA.scMom,
    HeisenbergN.LvirN_vacuum (rank L) 1 (by omega : (-1 : ℤ) ≤ n),
    chargeOsc_vacuum L γ n (by omega), bgOsc_vacuum L lam (by omega : (0 : ℤ) ≤ n),
    if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ n = 0)]
  simp

/-- **Every charged vacuum is Virasoro primary for the background-charge stress tensor**:
`Lₙ^λ e^β = 0` for all `n ≥ 1` and every `β ∈ L`, at every slope `λ`. -/
theorem LBg_latChargeGen_pos (L : IntegralLattice) (hPos : L.PosDef)
    (lam : Fin (rank L) → ℂ) {n : ℤ} (hn : 1 ≤ n) (β : L.carrier) :
    BgA.LBg L lam n (latChargeGen L β) = 0 := by
  have h : latChargeGen L β = mkEα L β (HeisenbergN.vacuumN (rank L)) := rfl
  rw [h, BgA.LBg_mkEα L hPos, LSecBg_vacuum_pos L lam β hn, map_zero]

/-- Charged vacua of `V_{L_p}` are primary for the deformed Virasoro action. -/
theorem L_latChargeGen_pos (p : ℕ) (hp : 1 ≤ p) {n : ℤ} (hn : 1 ≤ n) (β : (latP p).carrier) :
    (tripletLatticeVOA p hp).L n (latChargeGen (latP p) β) = 0 := by
  rw [tripletLatticeVOA_L]
  exact LBg_latChargeGen_pos (latP p) (latP_posDef p hp) (lamP p) hn β

/-- `ω₍ⱼ₎x = L_{j−1}x`: the conformal modes in `smul` form. -/
theorem smul_omegaTrip_eq_L (p : ℕ) (hp : 1 ≤ p) (j : ℤ) (x : LatModuleGen (latP p)) :
    (tripletLatticeVOA p hp).smul (omegaTrip p) j x = (tripletLatticeVOA p hp).L (j - 1) x := by
  have h : (tripletLatticeVOA p hp).L (j - 1) x
      = (tripletLatticeVOA p hp).smul (omegaTrip p) (j - 1 + 1) x := rfl
  rw [h, show j - 1 + 1 = j from by ring]

/-- **The `F`-tail vanishes**: `ω₍ⱼ₎F = L_{j−1}F = 0` for `j ≥ 2`. -/
theorem omegaTrip_smul_Ftrip_tail (p : ℕ) (hp : 1 ≤ p) {j : ℤ} (hj : 2 ≤ j) :
    (tripletLatticeVOA p hp).smul (omegaTrip p) j (Ftrip p) = 0 := by
  rw [smul_omegaTrip_eq_L]
  have hF : Ftrip p = latChargeGen (latP p) (-alphaP p) := rfl
  rw [hF]
  exact L_latChargeGen_pos p hp (by omega) (-alphaP p)

/-- **The long screening annihilates the deformed conformal vector**: `Q ω_λ = 0`.

Skew symmetry gives `(e^α)₍₀₎ω = ∑ⱼ (1/j!)·sgn(−1−j)·Tʲ(ω₍ⱼ₎e^α)`; only `j = 0, 1` survive
(`e^α` is primary by `L_latChargeGen_pos`), and they cancel because `e^α` has deformed weight
exactly `1` — the defining property of the long screening.  Equivalently: `Q` commutes with every
deformed Virasoro mode. -/
theorem Qwp_omegaTrip (p : ℕ) (hp : 1 ≤ p) : Qwp p hp (omegaTrip p) = 0 := by
  have hQ : Qwp p hp (omegaTrip p)
      = (tripletLatticeVOA p hp).smul (latChargeGen (latP p) (alphaP p)) 0 (omegaTrip p) := rfl
  rw [hQ, VertexOperatorAlgebra.skew_mode]
  have hcoef : ∀ j : ℕ,
      ((tripletLatticeVOA p hp).Y (omegaTrip p)) (-(0 : ℤ) - 1 - (j : ℤ))
          (latChargeGen (latP p) (alphaP p))
        = (tripletLatticeVOA p hp).L ((j : ℤ) - 1) (latChargeGen (latP p) (alphaP p)) := by
    intro j
    have h1 : (tripletLatticeVOA p hp).L ((j : ℤ) - 1) (latChargeGen (latP p) (alphaP p))
        = mode ((tripletLatticeVOA p hp).Y (omegaTrip p)) ((j : ℤ) - 1 + 1)
            (latChargeGen (latP p) (alphaP p)) := rfl
    rw [h1, mode_apply, show (-((j : ℤ) - 1 + 1) - 1 : ℤ) = -(0 : ℤ) - 1 - (j : ℤ) from by ring]
  have hbody : ∀ j : ℕ,
      ((j.factorial : ℂ)⁻¹) • (sgn (-(0 : ℤ) - 1 - (j : ℤ))) •
          (((tripletLatticeVOA p hp).toPreVertexAlgebra.T ^ j)
            (((tripletLatticeVOA p hp).Y (omegaTrip p)) (-(0 : ℤ) - 1 - (j : ℤ))
              (latChargeGen (latP p) (alphaP p))))
        = ((j.factorial : ℂ)⁻¹) • (sgn (-(0 : ℤ) - 1 - (j : ℤ))) •
          (((tripletLatticeVOA p hp).toPreVertexAlgebra.T ^ j)
            ((tripletLatticeVOA p hp).L ((j : ℤ) - 1) (latChargeGen (latP p) (alphaP p)))) := by
    intro j
    rw [hcoef j]
  rw [finsum_congr hbody]
  rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range 2) (by
    intro j hj
    rw [Function.mem_support] at hj
    by_contra hc
    rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
    refine hj ?_
    rw [L_latChargeGen_pos p hp (by omega : (1 : ℤ) ≤ (j : ℤ) - 1) (alphaP p), map_zero,
      smul_zero, smul_zero])]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have hL0 : (tripletLatticeVOA p hp).L (((1 : ℕ) : ℤ) - 1) (latChargeGen (latP p) (alphaP p))
      = latChargeGen (latP p) (alphaP p) := by
    rw [show (((1 : ℕ) : ℤ) - 1 : ℤ) = 0 from by norm_num,
      (tripletLatticeVOA p hp).L_zero_grading _ (latChargeGen_alpha_mem_grade_one p hp)]
    norm_num
  rw [hL0]
  have hs0 : sgn (-(0 : ℤ) - 1 - ((0 : ℕ) : ℤ)) = -1 := by
    rw [show (-(0 : ℤ) - 1 - ((0 : ℕ) : ℤ)) = -1 from by norm_num, sgn, if_neg (by decide)]
  have hs1 : sgn (-(0 : ℤ) - 1 - ((1 : ℕ) : ℤ)) = 1 := by
    rw [show (-(0 : ℤ) - 1 - ((1 : ℕ) : ℤ)) = -2 from by norm_num, sgn, if_pos (by decide)]
  rw [hs0, hs1]
  have hT : ((tripletLatticeVOA p hp).toPreVertexAlgebra.T ^ (1 : ℕ))
        (latChargeGen (latP p) (alphaP p))
      = (tripletLatticeVOA p hp).L (-1) (latChargeGen (latP p) (alphaP p)) := by
    rw [pow_one, VertexOperatorAlgebra.T_eq_Lneg1]
  have hT0 : ((tripletLatticeVOA p hp).toPreVertexAlgebra.T ^ (0 : ℕ))
        ((tripletLatticeVOA p hp).L (((0 : ℕ) : ℤ) - 1) (latChargeGen (latP p) (alphaP p)))
      = (tripletLatticeVOA p hp).L (-1) (latChargeGen (latP p) (alphaP p)) := by
    rw [pow_zero, Module.End.one_apply, show ((((0 : ℕ) : ℤ) - 1 : ℤ)) = -1 from by norm_num]
  rw [hT, hT0]
  module

/-- `Q` sends each of the four triplet generators back into their linear span:
`Qω = 0`, `QE = 0`, `QH = E`, and `QF = H`. -/
theorem Qwp_tripGens_mem_span (p : ℕ) (hp : 1 ≤ p) :
    ∀ g ∈ tripGens p, Qwp p hp g ∈ Submodule.span ℂ (tripGens p) := by
  intro g hg
  rcases hg with rfl | hg
  · rw [Qwp_omegaTrip]
    exact Submodule.zero_mem _
  rcases hg with rfl | hg
  · rw [Qwp_Etrip]
    exact Submodule.zero_mem _
  rcases hg with rfl | hg
  · rw [Qwp_Htrip]
    exact Submodule.subset_span (Etrip_mem_tripGens p)
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [Qwp_Ftrip]
    exact Submodule.subset_span (Htrip_mem_tripGens p)

/-- The long screening preserves the negative-mode word span.  This is the exact formal reason
that one computed lowering row propagates through the `Q`-string: use the derivation rule at each
word step and `Q{ω,E,H,F} ⊆ span{ω,E,H,F}`. -/
theorem Qwp_mem_iterProdSpan (p : ℕ) (hp : 1 ≤ p) :
    ∀ {x : LatModuleGen (latP p)},
      x ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) →
      Qwp p hp x ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  intro x hx
  refine Submodule.span_induction
    (p := fun x _ => Qwp p hp x ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) ?_ ?_ ?_ ?_ hx
  · intro x hx
    induction hx with
    | vacuum =>
        rw [Qwp, Screening.screening_vacuum]
        exact zero_mem _
    | step s hs m hm x hx ih =>
        rw [Qwp_leibniz]
        exact add_mem
          (spanS_left_mem _ _ hm (Qwp_tripGens_mem_span p hp s hs)
            (Submodule.subset_span hx))
          (smul_mem_iterProdSpan _ _ hs hm ih)
  · simpa only [map_zero] using
      (zero_mem (iterProdSpan (tripletLatticeVOA p hp) (tripGens p)))
  · intro x y _ _ hx hy
    simpa only [map_add] using add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using
      (Submodule.smul_mem (iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) c hx)

/-- Ordinary skew-symmetry recursively determines an even self-product from its higher modes.
The explicit sign hypothesis says that the `j = 0` skew term is `-u₍ₙ₎u`; all remaining
terms lie in the negative-word span by translation stability.  `K + 1` is any support cutoff. -/
theorem smul_self_mem_iterProdSpan_of_higher (p : ℕ) (hp : 1 ≤ p)
    (u : LatModuleGen (latP p)) (n : ℤ) (K : ℕ)
    (hsgn : sgn (-n - 1) = (-1 : ℂ))
    (hzero : ∀ j : ℕ, K + 1 ≤ j →
      (tripletLatticeVOA p hp).smul u (n + (j : ℤ)) u = 0)
    (hhigher : ∀ j : ℕ, 1 ≤ j → j < K + 1 →
      (tripletLatticeVOA p hp).smul u (n + (j : ℤ)) u
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) :
    (tripletLatticeVOA p hp).smul u n u
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  let W := tripletLatticeVOA p hp
  let T := iterProdSpan W (tripGens p)
  let f : ℕ → LatModuleGen (latP p) := fun j =>
    ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - (j : ℤ))) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y u) (-n - 1 - (j : ℤ)) u))
  have hmode : ∀ j : ℕ,
      (W.Y u) (-n - 1 - (j : ℤ)) u = W.smul u (n + (j : ℤ)) u := by
    intro j
    rw [PreVertexAlgebra.smul_def, mode_apply,
      show (-(n + (j : ℤ)) - 1 : ℤ) = -n - 1 - (j : ℤ) from by ring]
  have hsupport : Function.support f ⊆ (Finset.range (K + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hj
    change ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - (j : ℤ))) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y u) (-n - 1 - (j : ℤ)) u)) = 0
    rw [hmode j, hzero j (by omega), map_zero, smul_zero, smul_zero]
  have hsk := VertexOperatorAlgebra.skew_mode W u u n
  change W.smul u n u = ∑ᶠ j : ℕ, f j at hsk
  rw [finsum_eq_finsetSum_of_support_subset _ hsupport, Finset.sum_range_succ'] at hsk
  have hf0 : f 0 = -W.smul u n u := by
    change (((Nat.factorial 0 : ℕ) : ℂ)⁻¹) • (sgn (-n - 1 - ((0 : ℕ) : ℤ))) •
      ((W.toPreVertexAlgebra.T ^ (0 : ℕ)) ((W.Y u) (-n - 1 - ((0 : ℕ) : ℤ)) u)) =
        -W.smul u n u
    rw [hmode 0, show n + ((0 : ℕ) : ℤ) = n by ring, Nat.factorial_zero,
      Nat.cast_one, inv_one, one_smul, show -n - 1 - ((0 : ℕ) : ℤ) = -n - 1 by ring,
      hsgn, pow_zero, Module.End.one_apply]
    exact neg_one_smul (R := ℂ) (W.smul u n u)
  rw [hf0] at hsk
  have hrest : (∑ j ∈ Finset.range K, f (j + 1)) ∈ T := by
    refine Submodule.sum_mem T (fun j hj => ?_)
    have hjlt : j < K := Finset.mem_range.mp hj
    have hm := hhigher (j + 1) (by omega) (by omega)
    have hTm := T_pow_mem_iterProdSpan W (tripGens p) (j + 1) hm
    unfold f
    rw [hmode (j + 1)]
    exact Submodule.smul_mem T _ (Submodule.smul_mem T _ hTm)
  have hdouble : W.smul u n u + W.smul u n u = ∑ j ∈ Finset.range K, f (j + 1) := by
    calc
      _ = ((∑ j ∈ Finset.range K, f (j + 1)) + -W.smul u n u) + W.smul u n u :=
        congrArg (fun z => z + W.smul u n u) hsk
      _ = _ := by abel
  have hdouble_mem : W.smul u n u + W.smul u n u ∈ T := by
    rw [hdouble]
    exact hrest
  have hscaled := Submodule.smul_mem T (2 : ℂ)⁻¹ hdouble_mem
  have hhalf : (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1 := by norm_num
  simpa only [smul_add, ← add_smul, hhalf, one_smul] using hscaled

/-- The charge-zero self-row has the generic weight cutoff: `H₍ⱼ₎H = 0` for
`j ≥ 4p - 2`.  In particular it vanishes from mode `6` onward at `p = 2`. -/
theorem smul_Htrip_Htrip_eq_zero_of_ge (p : ℕ) (hp : 1 ≤ p) {j : ℤ}
    (hj : 4 * (p : ℤ) - 2 ≤ j) :
    (tripletLatticeVOA p hp).smul (Htrip p) j (Htrip p) = 0 := by
  rw [smul_grading_neg_eq_zero (tripletLatticeVOA p hp)
    (Htrip_mem_grading p hp) (Htrip_mem_grading p hp) (by omega)]

/-- The derivation identity `Q(F₍ⱼ₎H) = H₍ⱼ₎H + F₍ⱼ₎E`, in membership form. -/
theorem smul_HH_mem_of_FH_FE (p : ℕ) (hp : 1 ≤ p) (j : ℤ)
    (hFH : (tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p)
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p))
    (hFE : (tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p)
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) :
    (tripletLatticeVOA p hp).smul (Htrip p) j (Htrip p)
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  let T := iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
  have hQ := Qwp_mem_iterProdSpan p hp hFH
  have heq : (tripletLatticeVOA p hp).smul (Htrip p) j (Htrip p) =
      Qwp p hp ((tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p)) -
        (tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p) := by
    rw [Qwp_leibniz, Qwp_Ftrip, Qwp_Htrip]
    abel
  rw [heq]
  exact sub_mem hQ hFE

/-- The same derivation identity solved for `F₍ⱼ₎E`. -/
theorem smul_FE_mem_of_FH_HH (p : ℕ) (hp : 1 ≤ p) (j : ℤ)
    (hFH : (tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p)
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p))
    (hHH : (tripletLatticeVOA p hp).smul (Htrip p) j (Htrip p)
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) :
    (tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p)
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  let T := iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
  have hQ := Qwp_mem_iterProdSpan p hp hFH
  have heq : (tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p) =
      Qwp p hp ((tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p)) -
        (tripletLatticeVOA p hp).smul (Htrip p) j (Htrip p) := by
    rw [Qwp_leibniz, Qwp_Ftrip, Qwp_Htrip]
    abel
  rw [heq]
  exact sub_mem hQ hHH

/-- At `p = 2`, the entire mixed-pair table follows from just five coordinate products:
`F₍₀₎H`, `F₍₂₎H`, and the odd modes `F₍₁₎E`, `F₍₃₎E`, `F₍₅₎E`.

The even `F₍ⱼ₎E` modes are recovered downward from ordinary self-skew-symmetry of `H`
and `Q(F₍ⱼ₎H) = H₍ⱼ₎H + F₍ⱼ₎E`; `F₍₁₎H` is the earlier skew recurrence.
This is the terminal formal reduction: odd self-skew has leading coefficient `+1`, so it gives
no equation for the remaining three odd `F₍ⱼ₎E` modes. -/
theorem loweringPairsWp_two_of_five (hp : 1 ≤ 2)
    (hFH0 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 0 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFH2 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 2 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE1 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 1 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE3 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 3 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE5 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 5 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2)) :
    LoweringPairsWp 2 hp := by
  let W := tripletLatticeVOA 2 hp
  let T := iterProdSpan W (tripGens 2)
  have hFH1 : W.smul (Ftrip 2) 1 (Htrip 2) ∈ T :=
    smul_Ftrip_Htrip_one_mem_of_two hp hFH2
  have hFHge : ∀ j : ℤ, 3 ≤ j → W.smul (Ftrip 2) j (Htrip 2) ∈ T := by
    intro j hj
    rw [smul_Ftrip_Htrip_eq_zero_of_ge 2 hp (by omega)]
    exact zero_mem T
  have hHH5 : W.smul (Htrip 2) 5 (Htrip 2) ∈ T :=
    smul_HH_mem_of_FH_FE 2 hp 5 (hFHge 5 (by norm_num)) hFE5
  have hsgn4 : sgn (-(4 : ℤ) - 1) = (-1 : ℂ) := by
    rw [show (-(4 : ℤ) - 1) = -5 by norm_num, sgn, if_neg (by decide)]
  have hHH4 : W.smul (Htrip 2) 4 (Htrip 2) ∈ T := by
    apply smul_self_mem_iterProdSpan_of_higher 2 hp (Htrip 2) 4 1 hsgn4
    · intro j hj
      rw [smul_Htrip_Htrip_eq_zero_of_ge 2 hp (by omega)]
    · intro j hj1 hj2
      have : j = 1 := by omega
      subst j
      norm_num
      exact hHH5
  have hFE4 : W.smul (Ftrip 2) 4 (Etrip 2) ∈ T :=
    smul_FE_mem_of_FH_HH 2 hp 4 (hFHge 4 (by norm_num)) hHH4
  have hHH3 : W.smul (Htrip 2) 3 (Htrip 2) ∈ T :=
    smul_HH_mem_of_FH_FE 2 hp 3 (hFHge 3 (by norm_num)) hFE3
  have hsgn2 : sgn (-(2 : ℤ) - 1) = (-1 : ℂ) := by
    rw [show (-(2 : ℤ) - 1) = -3 by norm_num, sgn, if_neg (by decide)]
  have hHH2 : W.smul (Htrip 2) 2 (Htrip 2) ∈ T := by
    apply smul_self_mem_iterProdSpan_of_higher 2 hp (Htrip 2) 2 3 hsgn2
    · intro j hj
      rw [smul_Htrip_Htrip_eq_zero_of_ge 2 hp (by omega)]
    · intro j hj1 hj4
      interval_cases j
      · norm_num
        exact hHH3
      · norm_num
        exact hHH4
      · norm_num
        exact hHH5
  have hFE2 : W.smul (Ftrip 2) 2 (Etrip 2) ∈ T :=
    smul_FE_mem_of_FH_HH 2 hp 2 hFH2 hHH2
  have hHH1 : W.smul (Htrip 2) 1 (Htrip 2) ∈ T :=
    smul_HH_mem_of_FH_FE 2 hp 1 hFH1 hFE1
  have hsgn0 : sgn (-(0 : ℤ) - 1) = (-1 : ℂ) := by
    rw [show (-(0 : ℤ) - 1) = -1 by norm_num, sgn, if_neg (by decide)]
  have hHH0 : W.smul (Htrip 2) 0 (Htrip 2) ∈ T := by
    apply smul_self_mem_iterProdSpan_of_higher 2 hp (Htrip 2) 0 5 hsgn0
    · intro j hj
      rw [smul_Htrip_Htrip_eq_zero_of_ge 2 hp (by omega)]
    · intro j hj1 hj6
      interval_cases j
      · norm_num
        exact hHH1
      · norm_num
        exact hHH2
      · norm_num
        exact hHH3
      · norm_num
        exact hHH4
      · norm_num
        exact hHH5
  have hFE0 : W.smul (Ftrip 2) 0 (Etrip 2) ∈ T :=
    smul_FE_mem_of_FH_HH 2 hp 0 hFH0 hHH0
  apply loweringPairsWp_two_of_nine hp
  · intro j hj0 hj3
    interval_cases j
    · exact hFH0
    · exact hFH1
    · exact hFH2
  · intro j hj0 hj6
    interval_cases j
    · exact hFE0
    · exact hFE1
    · exact hFE2
    · exact hFE3
    · exact hFE4
    · exact hFE5

/-- The degree-zero Fock lemma closes `F₍₂₎H` and `F₍₅₎E` automatically.  Thus the
genuine coordinate residual consists of only three products: `F₍₀₎H`, `F₍₁₎E`, and `F₍₃₎E`. -/
theorem loweringPairsWp_two_of_three (hp : 1 ≤ 2)
    (hFH0 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 0 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE1 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 1 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE3 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 3 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2)) :
    LoweringPairsWp 2 hp :=
  loweringPairsWp_two_of_five hp hFH0 (smul_Ftrip_Htrip_two_mem hp)
    hFE1 hFE3 (smul_Ftrip_Etrip_five_mem hp)

/-- A coordinate evaluator need not know about `iterProdSpan`.  These five finite-dimensional
identities are a sufficient target: the displayed right-hand sides are manifest negative-mode
words in `{omega, E, H, F}`.  The coefficients are existential because only membership, not their
normalization, is used downstream. -/
def FiveCoordinateIdentitiesWp (hp : 1 ≤ 2) : Prop :=
  let W := tripletLatticeVOA 2 hp
  ∃ aFH0 bFH0 aFH2 aFE1 bFE1 cFE1 aFE3 aFE5 : ℂ,
    W.smul (Ftrip 2) 0 (Htrip 2) =
        aFH0 • W.smul (omegaTrip 2) (-1) (Ftrip 2) +
          bFH0 • (W.toPreVertexAlgebra.T ^ 2) (Ftrip 2) ∧
    W.smul (Ftrip 2) 2 (Htrip 2) = aFH2 • Ftrip 2 ∧
    W.smul (Ftrip 2) 1 (Etrip 2) =
        aFE1 • W.smul (omegaTrip 2) (-1) (omegaTrip 2) +
          bFE1 • (W.toPreVertexAlgebra.T ^ 2) (omegaTrip 2) +
            cFE1 • W.toPreVertexAlgebra.T (Htrip 2) ∧
    W.smul (Ftrip 2) 3 (Etrip 2) = aFE3 • omegaTrip 2 ∧
    W.smul (Ftrip 2) 5 (Etrip 2) = aFE5 • W.vacuum

/-- The minimal coordinate target after the degree-zero endpoints have been discharged.  In raw
Fock coordinates the three left sides are, respectively,

* `ε(α,-α) · EE(-α,-1) S₃(α) ⊗ e^{-α}`;
* `ε(α,-α)ε(-α,α) · EE(-α,2)(EE(α,-1)S₃(α)) ⊗ e⁰`;
* `ε(α,-α)ε(-α,α) · EE(-α,0)(EE(α,-1)S₃(α)) ⊗ e⁰`,

by `smul_Ftrip_Htrip_eq_fock` and `smul_Ftrip_Etrip_eq_fock`. -/
def ThreeCoordinateIdentitiesWp (hp : 1 ≤ 2) : Prop :=
  let W := tripletLatticeVOA 2 hp
  ∃ aFH0 bFH0 aFE1 bFE1 cFE1 aFE3 : ℂ,
    W.smul (Ftrip 2) 0 (Htrip 2) =
        aFH0 • W.smul (omegaTrip 2) (-1) (Ftrip 2) +
          bFH0 • (W.toPreVertexAlgebra.T ^ 2) (Ftrip 2) ∧
    W.smul (Ftrip 2) 1 (Etrip 2) =
        aFE1 • W.smul (omegaTrip 2) (-1) (omegaTrip 2) +
          bFE1 • (W.toPreVertexAlgebra.T ^ 2) (omegaTrip 2) +
            cFE1 • W.toPreVertexAlgebra.T (Htrip 2) ∧
    W.smul (Ftrip 2) 3 (Etrip 2) = aFE3 • omegaTrip 2

/-- The bridge from the minimal three coordinate identities to all mixed pairs. -/
theorem loweringPairsWp_two_of_three_coordinate_identities (hp : 1 ≤ 2)
    (hcoord : ThreeCoordinateIdentitiesWp hp) : LoweringPairsWp 2 hp := by
  let W := tripletLatticeVOA 2 hp
  let T := iterProdSpan W (tripGens 2)
  rcases hcoord with ⟨aFH0, bFH0, aFE1, bFE1, cFE1, aFE3, hFH0eq, hFE1eq, hFE3eq⟩
  have hF : Ftrip 2 ∈ T := subset_iterProdSpan W (tripGens 2) (Ftrip_mem_tripGens 2)
  have hH : Htrip 2 ∈ T := subset_iterProdSpan W (tripGens 2) (Htrip_mem_tripGens 2)
  have homega : omegaTrip 2 ∈ T :=
    subset_iterProdSpan W (tripGens 2) (omegaTrip_mem_tripGens 2)
  have homegaF : W.smul (omegaTrip 2) (-1) (Ftrip 2) ∈ T :=
    smul_mem_iterProdSpan W (tripGens 2) (omegaTrip_mem_tripGens 2) (by norm_num) hF
  have homegaomega : W.smul (omegaTrip 2) (-1) (omegaTrip 2) ∈ T :=
    smul_mem_iterProdSpan W (tripGens 2) (omegaTrip_mem_tripGens 2) (by norm_num) homega
  have hT2F : (W.toPreVertexAlgebra.T ^ 2) (Ftrip 2) ∈ T :=
    T_pow_mem_iterProdSpan W (tripGens 2) 2 hF
  have hT2omega : (W.toPreVertexAlgebra.T ^ 2) (omegaTrip 2) ∈ T :=
    T_pow_mem_iterProdSpan W (tripGens 2) 2 homega
  have hTH : W.toPreVertexAlgebra.T (Htrip 2) ∈ T :=
    T_pow_mem_iterProdSpan W (tripGens 2) 1 hH
  apply loweringPairsWp_two_of_three hp
  · rw [hFH0eq]
    exact add_mem (Submodule.smul_mem T _ homegaF) (Submodule.smul_mem T _ hT2F)
  · rw [hFE1eq]
    exact add_mem
      (add_mem (Submodule.smul_mem T _ homegaomega) (Submodule.smul_mem T _ hT2omega))
      (Submodule.smul_mem T _ hTH)
  · rw [hFE3eq]
    exact Submodule.smul_mem T _ homega

/-- The exact bridge from the five coordinate identities to the mixed-pair residual. -/
theorem loweringPairsWp_two_of_coordinate_identities (hp : 1 ≤ 2)
    (hcoord : FiveCoordinateIdentitiesWp hp) : LoweringPairsWp 2 hp := by
  let W := tripletLatticeVOA 2 hp
  let T := iterProdSpan W (tripGens 2)
  rcases hcoord with ⟨aFH0, bFH0, aFH2, aFE1, bFE1, cFE1, aFE3, aFE5,
    hFH0eq, hFH2eq, hFE1eq, hFE3eq, hFE5eq⟩
  have hF : Ftrip 2 ∈ T := subset_iterProdSpan W (tripGens 2) (Ftrip_mem_tripGens 2)
  have hH : Htrip 2 ∈ T := subset_iterProdSpan W (tripGens 2) (Htrip_mem_tripGens 2)
  have homega : omegaTrip 2 ∈ T :=
    subset_iterProdSpan W (tripGens 2) (omegaTrip_mem_tripGens 2)
  have homegaF : W.smul (omegaTrip 2) (-1) (Ftrip 2) ∈ T :=
    smul_mem_iterProdSpan W (tripGens 2) (omegaTrip_mem_tripGens 2) (by norm_num) hF
  have homegaomega : W.smul (omegaTrip 2) (-1) (omegaTrip 2) ∈ T :=
    smul_mem_iterProdSpan W (tripGens 2) (omegaTrip_mem_tripGens 2) (by norm_num) homega
  have hT2F : (W.toPreVertexAlgebra.T ^ 2) (Ftrip 2) ∈ T :=
    T_pow_mem_iterProdSpan W (tripGens 2) 2 hF
  have hT2omega : (W.toPreVertexAlgebra.T ^ 2) (omegaTrip 2) ∈ T :=
    T_pow_mem_iterProdSpan W (tripGens 2) 2 homega
  have hTH : W.toPreVertexAlgebra.T (Htrip 2) ∈ T :=
    T_pow_mem_iterProdSpan W (tripGens 2) 1 hH
  apply loweringPairsWp_two_of_five hp
  · rw [hFH0eq]
    exact add_mem (Submodule.smul_mem T _ homegaF) (Submodule.smul_mem T _ hT2F)
  · rw [hFH2eq]
    exact Submodule.smul_mem T _ hF
  · rw [hFE1eq]
    exact add_mem
      (add_mem (Submodule.smul_mem T _ homegaomega) (Submodule.smul_mem T _ hT2omega))
      (Submodule.smul_mem T _ hTH)
  · rw [hFE3eq]
    exact Submodule.smul_mem T _ homega
  · rw [hFE5eq]
    exact Submodule.smul_mem T _ (vacuum_mem_iterProdSpan W (tripGens 2))

/-- The seven ordered mixed screening pairs reduce to the two lowering rows.

Starting with `F₍ⱼ₎H` and `F₍ⱼ₎E`, screening stability gives
`Q(F₍ⱼ₎H) = H₍ⱼ₎H + F₍ⱼ₎E` and `Q(F₍ⱼ₎E) = H₍ⱼ₎E`.  The exact identities
`H₍ⱼ₎F + F₍ⱼ₎H = 0`, `E₍ⱼ₎H + H₍ⱼ₎E = 0`, and
`E₍ⱼ₎F + F₍ⱼ₎E + 2H₍ⱼ₎H = 0` then recover the remaining orientations.  No division and no
parity-sensitive skew argument occurs here. -/
theorem mixedPairsWp_of_loweringPairs (p : ℕ) (hp : 1 ≤ p)
    (hlo : LoweringPairsWp p hp) : MixedPairsWp p hp := by
  rcases hlo with ⟨hFH, hFE⟩
  intro g hg h hh j hj
  have hp' : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hn : -(2 * (p : ℤ)) ≤ j := by omega
  let T := iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
  have hFHj : (tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p) ∈ T := hFH j hj
  have hFEj : (tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p) ∈ T := hFE j hj
  have hHHj : (tripletLatticeVOA p hp).smul (Htrip p) j (Htrip p) ∈ T := by
    have hQ := Qwp_mem_iterProdSpan p hp hFHj
    have heq : (tripletLatticeVOA p hp).smul (Htrip p) j (Htrip p)
        = Qwp p hp ((tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p))
          - (tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p) := by
      rw [Qwp_leibniz, Qwp_Ftrip, Qwp_Htrip]
      abel
    rw [heq]
    exact sub_mem hQ hFEj
  have hHEj : (tripletLatticeVOA p hp).smul (Htrip p) j (Etrip p) ∈ T := by
    have hQ := Qwp_mem_iterProdSpan p hp hFEj
    rw [Qwp_leibniz, Qwp_Ftrip, Qwp_Etrip,
      PreVertexAlgebra.smul_zero_right, add_zero] at hQ
    exact hQ
  have hHFj : (tripletLatticeVOA p hp).smul (Htrip p) j (Ftrip p) ∈ T := by
    have heq : (tripletLatticeVOA p hp).smul (Htrip p) j (Ftrip p)
        = -(tripletLatticeVOA p hp).smul (Ftrip p) j (Htrip p) := by
      have h := HF_add_FH p hp hn
      rw [add_eq_zero_iff_eq_neg] at h
      exact h
    rw [heq]
    exact neg_mem hFHj
  have hEHj : (tripletLatticeVOA p hp).smul (Etrip p) j (Htrip p) ∈ T := by
    have heq : (tripletLatticeVOA p hp).smul (Etrip p) j (Htrip p)
        = -(tripletLatticeVOA p hp).smul (Htrip p) j (Etrip p) := by
      have h := EH_add_HE p hp hn
      rw [add_eq_zero_iff_eq_neg] at h
      exact h
    rw [heq]
    exact neg_mem hHEj
  have hEFj : (tripletLatticeVOA p hp).smul (Etrip p) j (Ftrip p) ∈ T := by
    have h := EF_add_FE_add_two_HH p hp hn
    have h' : (tripletLatticeVOA p hp).smul (Etrip p) j (Ftrip p)
        + ((tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p)
          + (2 : ℂ) • (tripletLatticeVOA p hp).smul (Htrip p) j (Htrip p)) = 0 := by
      simpa only [add_assoc] using h
    have heq : (tripletLatticeVOA p hp).smul (Etrip p) j (Ftrip p)
        = -((tripletLatticeVOA p hp).smul (Ftrip p) j (Etrip p)
          + (2 : ℂ) • (tripletLatticeVOA p hp).smul (Htrip p) j (Htrip p)) :=
      eq_neg_of_add_eq_zero_left h'
    rw [heq]
    exact neg_mem (add_mem hFEj (Submodule.smul_mem _ _ hHHj))
  simp only [screenGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
  rcases hg with rfl | rfl | rfl
  · rcases hh with rfl | rfl | rfl
    · exact pair_Etrip_Etrip p hp j hj
    · exact hEHj
    · exact hEFj
  · rcases hh with rfl | rfl | rfl
    · exact hHEj
    · exact hHHj
    · exact hHFj
  · rcases hh with rfl | rfl | rfl
    · exact hFEj
    · exact hFHj
    · exact pair_Ftrip_Ftrip p hp j hj

/-- **The `H`-tail vanishes**: `ω₍ⱼ₎H = 0` for `j ≥ 2`, by applying the derivation `Q` to
`ω₍ⱼ₎F = 0` and using `Qω = 0`. -/
theorem omegaTrip_smul_Htrip_tail (p : ℕ) (hp : 1 ≤ p) {j : ℤ} (hj : 2 ≤ j) :
    (tripletLatticeVOA p hp).smul (omegaTrip p) j (Htrip p) = 0 := by
  have h := Qwp_leibniz p hp (omegaTrip p) j (Ftrip p)
  rw [omegaTrip_smul_Ftrip_tail p hp hj, map_zero, Qwp_omegaTrip p hp,
    PreVertexAlgebra.smul_zero_left, Qwp_Ftrip, zero_add] at h
  exact h.symm

/-- **The `E`-tail vanishes**: `ω₍ⱼ₎E = 0` for `j ≥ 2` (`Q` applied once more). -/
theorem omegaTrip_smul_Etrip_tail (p : ℕ) (hp : 1 ≤ p) {j : ℤ} (hj : 2 ≤ j) :
    (tripletLatticeVOA p hp).smul (omegaTrip p) j (Etrip p) = 0 := by
  have h := Qwp_leibniz p hp (omegaTrip p) j (Htrip p)
  rw [omegaTrip_smul_Htrip_tail p hp hj, map_zero, Qwp_omegaTrip p hp,
    PreVertexAlgebra.smul_zero_left, Qwp_Htrip, zero_add] at h
  exact h.symm

/-- **`E`, `H`, `F` are Virasoro primary** (of deformed weight `2p − 1`):
`Lₙ g = 0` for every `n ≥ 1`, at every `p`. -/
theorem screenGens_primary (p : ℕ) (hp : 1 ≤ p) :
    ∀ g ∈ screenGens p, ∀ n : ℤ, 1 ≤ n → (tripletLatticeVOA p hp).L n g = 0 := by
  intro g hg n hn
  have hLs : (tripletLatticeVOA p hp).L n g
      = (tripletLatticeVOA p hp).smul (omegaTrip p) (n + 1) g := by
    rw [smul_omegaTrip_eq_L, show n + 1 - 1 = n from by ring]
  rcases hg with rfl | hg
  · rw [hLs]; exact omegaTrip_smul_Etrip_tail p hp (by omega)
  rcases hg with rfl | hg
  · rw [hLs]; exact omegaTrip_smul_Htrip_tail p hp (by omega)
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [hLs]; exact omegaTrip_smul_Ftrip_tail p hp (by omega)

/-- **Residual 1 holds** (unconditionally, at every `p`): the primarity tails are zero,
so in particular they lie in the span. -/
theorem omegaTailWp_all (p : ℕ) (hp : 1 ≤ p) : OmegaTailWp p hp := by
  intro g hg j hj
  rcases hg with rfl | hg
  · rw [omegaTrip_smul_Etrip_tail p hp hj]; exact zero_mem _
  rcases hg with rfl | hg
  · rw [omegaTrip_smul_Htrip_tail p hp hj]; exact zero_mem _
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [omegaTrip_smul_Ftrip_tail p hp hj]; exact zero_mem _

/-! ## §6  The sharpened end state: TWO residuals -/

/-- **`C₂`-cofiniteness of `W(p)` from TWO finite lattice residuals**: the mixed
screening pairs `g₍ⱼ₎h` (`g, h ∈ {E,H,F}`, `0 ≤ j < 4p − 2`) and the Adamović–Milas
`ω̄`-identity in weight `6p − 2`.  The primarity tails are theorems
(`omegaTailWp_all`), so they do not appear.

⚠ The two remaining inputs are hypotheses; neither is proved anywhere in this repository. -/
theorem c2Cofinite_tripletWVOA_of_mixed_AM (p : ℕ) (hp : 1 ≤ p)
    (hmixed : MixedPairsWp p hp) (hAM : AMOmegaIdentity p hp (3 * p - 1)) :
    C2Cofinite (tripletWVOA p hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA p hp)) ≤ 16 * (3 * p - 1) :=
  c2Cofinite_tripletWVOA_of_tail_mixed p hp (omegaTailWp_all p hp) hmixed hAM

/-- The `p = 2` instance: `C2Cofinite (tripletWVOA 2 hp)` and `dim A₂ ≤ 80` from
`MixedPairsWp 2 hp` (the products `g₍ⱼ₎h`, `g, h ∈ {E,H,F}`, `0 ≤ j ≤ 5`; the `(E,E)` and
`(F,F)` pairs are already zero) and `AMOmegaIdentity 2 hp 5` (the weight-`10` identity in
`V_{L_2}`). -/
theorem c2Cofinite_tripletWVOA_two_of_mixed_AM (hp : 1 ≤ 2)
    (hmixed : MixedPairsWp 2 hp) (hAM : AMOmegaIdentity 2 hp 5) :
    C2Cofinite (tripletWVOA 2 hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA 2 hp)) ≤ 80 :=
  c2Cofinite_tripletWVOA_two_of_tail_mixed hp (omegaTailWp_all 2 hp) hmixed hAM

/-- The sharpened general-`p` endpoint: only the two lowering rows and the AM identity remain. -/
theorem c2Cofinite_tripletWVOA_of_lowering_AM (p : ℕ) (hp : 1 ≤ p)
    (hlower : LoweringPairsWp p hp) (hAM : AMOmegaIdentity p hp (3 * p - 1)) :
    C2Cofinite (tripletWVOA p hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA p hp)) ≤ 16 * (3 * p - 1) :=
  c2Cofinite_tripletWVOA_of_mixed_AM p hp (mixedPairsWp_of_loweringPairs p hp hlower) hAM

/-- At `p = 2`, `LoweringPairsWp` can be supplied by nine bounded products
(`loweringPairsWp_two_of_nine`), sharpened by skew recursion to the five products in
`loweringPairsWp_two_of_five`; the other input is the weight-10 AM identity. -/
theorem c2Cofinite_tripletWVOA_two_of_lowering_AM (hp : 1 ≤ 2)
    (hlower : LoweringPairsWp 2 hp) (hAM : AMOmegaIdentity 2 hp 5) :
    C2Cofinite (tripletWVOA 2 hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA 2 hp)) ≤ 80 :=
  c2Cofinite_tripletWVOA_two_of_mixed_AM hp (mixedPairsWp_of_loweringPairs 2 hp hlower) hAM

/-- The final `p = 2` formal endpoint.  Five explicit lattice products and the weight-10
Adamović–Milas identity imply `C₂`-cofiniteness and the bound `dim A₂ ≤ 80`. -/
theorem c2Cofinite_tripletWVOA_two_of_five_AM (hp : 1 ≤ 2)
    (hFH0 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 0 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFH2 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 2 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE1 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 1 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE3 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 3 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE5 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 5 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hAM : AMOmegaIdentity 2 hp 5) :
    C2Cofinite (tripletWVOA 2 hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA 2 hp)) ≤ 80 :=
  c2Cofinite_tripletWVOA_two_of_lowering_AM hp
    (loweringPairsWp_two_of_five hp hFH0 hFH2 hFE1 hFE3 hFE5) hAM

/-- The minimal product-facing endpoint: only `F₍₀₎H`, `F₍₁₎E`, `F₍₃₎E` and the
weight-10 Adamović–Milas identity remain. -/
theorem c2Cofinite_tripletWVOA_two_of_three_AM (hp : 1 ≤ 2)
    (hFH0 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 0 (Htrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE1 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 1 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hFE3 : (tripletLatticeVOA 2 hp).smul (Ftrip 2) 3 (Etrip 2)
      ∈ iterProdSpan (tripletLatticeVOA 2 hp) (tripGens 2))
    (hAM : AMOmegaIdentity 2 hp 5) :
    C2Cofinite (tripletWVOA 2 hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA 2 hp)) ≤ 80 :=
  c2Cofinite_tripletWVOA_two_of_lowering_AM hp
    (loweringPairsWp_two_of_three hp hFH0 hFE1 hFE3) hAM

/-- Coordinate-facing version of the final endpoint. -/
theorem c2Cofinite_tripletWVOA_two_of_coordinates_AM (hp : 1 ≤ 2)
    (hcoord : FiveCoordinateIdentitiesWp hp) (hAM : AMOmegaIdentity 2 hp 5) :
    C2Cofinite (tripletWVOA 2 hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA 2 hp)) ≤ 80 :=
  c2Cofinite_tripletWVOA_two_of_lowering_AM hp
    (loweringPairsWp_two_of_coordinate_identities hp hcoord) hAM

/-- Minimal coordinate-facing endpoint. -/
theorem c2Cofinite_tripletWVOA_two_of_three_coordinates_AM (hp : 1 ≤ 2)
    (hcoord : ThreeCoordinateIdentitiesWp hp) (hAM : AMOmegaIdentity 2 hp 5) :
    C2Cofinite (tripletWVOA 2 hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA 2 hp)) ≤ 80 :=
  c2Cofinite_tripletWVOA_two_of_lowering_AM hp
    (loweringPairsWp_two_of_three_coordinate_identities hp hcoord) hAM

end VOA.LatGen.WpC2
