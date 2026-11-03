/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov

⚠ **Citation.** This result is Adamović–Milas **Corollary 4.6** in the published paper
(Adv. Math. 217 (2008) 2664–2699), equivalently **Corollary 3.6, eq. (3.15)** of arXiv v2 — *not*
Corollary 4.4. Its own cited inputs are **Lemma 4.3 and
Theorem 4.5**, not "Lemmas 4.1–4.2 and Theorem 4.3". Recorded because a wrong theorem number is
exactly the kind of thing that gets inherited rather than re-checked.
-/
import VOA.Examples.TripletWpC2

/-!
# The two residual hypotheses of `W(p)`, pushed down into the free-field Fock space `V_{L_p}`

`Examples.TripletWpC2` proves `C2Cofinite (tripletWVOA p hp)` from two carried hypotheses,
`AdjoinGenWp` (algebra generation of `A₂(W(p))`) and `OmegaNilpotentWp` (nilpotency of `ω̄`).
Both are statements *about a quotient of a subalgebra*.  This file rewrites each of them as a
statement **inside the ambient deformed lattice VOA `V_{L_p}`**, where they become free-field
computations: no quotient, no subalgebra, only vectors of `Fock ⊗ ℂ[L_p]` and the ambient modes.

The mechanism is uniform.  `smul_coe` (`Examples.TripletWpC2`) says products in `W(p)` *are* the
ambient products, so the inclusion `ι : W(p) ↪ V_{L_p}` is injective and intertwines everything;
every submodule of `W(p)` therefore has a faithful image under `ι`, and a membership statement in
`W(p)` is *equivalent* to the corresponding membership of the image.

## Main results

### §1  One new lattice product, the first one below the vanishing range

* `smul_latChargeGen_bottom` — `(e^α)₍−⟨α,β⟩−1₎ e^β = ε(α,β)·e^{α+β}`.  Companion of
  `smul_latChargeGen_eq_zero` (which kills every mode `n ≥ −⟨α,β⟩`): at the *next* mode down the
  same computation returns the charged vacuum instead of `0`, because `EEVec` is evaluated at
  index `0` and `vSchur α 0 = 1`.
* `smul_Ftrip_Ftrip_bottom` — its specialization `F₍−2p−1₎F = ε(−α,−α)·e^{−2α}`.

### §2–§3  The transport dictionary

* `O₂amb`, `mem_O₂amb_iff`, `smul_mem_O₂amb` — the ambient image of `C₂(W(p))`, the faithfulness
  of that image, and the fact that *every* ambient product `u₍ₙ₎v` with `u, v ∈ W(p)` and
  `n ≤ −2` lies in it.
* `L_coe`, `L_neg_one_mem_O₂amb` — Virasoro modes transport, and `L₋₁(W(p)) ⊆ C₂(W(p))`.

### §4  Target 1: `StrongGenWp`, made ambient

* `map_iterProdSpan_genWp` — `ι(iterProdSpan_{W(p)}{ω,E,H,F}) = iterProdSpan_{V_{L_p}}(tripGens p)`.
* `iterProdSpan_amb_le_carrier` — the free inclusion `⊆ W(p)`.
* `strongGenWp_iff` — **`StrongGenWp p hp ↔ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
  = (tripletW p hp).carrier`**, i.e. *strong generation is exactly the statement that the span of
  the iterated strictly-negative modes of `{ω_λ, E, H, F}` on `|0⟩` is already closed under all
  the remaining vertex-algebra operations* (all non-negative modes, and the homogeneous
  projections).  `strongGenWp_iff_carrier_le` is the one-sided form, `≥` being free.

  This is the honest content of Adamović–Milas Proposition 2.3(ii): the residual is that the
  `W`-algebra OPE closes on the strong generators.  Nothing here proves it — the file only
  relocates it from a statement about a subquotient to a statement about explicit vectors of the
  Fock space.
* `SmulClosedWp`, `strongGenWp_iff_smulClosed` — **the reduction to a single clause.**  Three
  of the four `VOASubalgebra` fields for the ambient span are discharged here: `vacuum_mem` and
  `conformal_mem` (`ω_λ` is one of the four generators) and `graded` (`isIterProd_homog` +
  `piHom_mem_iterProdSpan`: an iterated product of homogeneous generators is homogeneous, so each
  `piHom` fixes it or kills it).  What survives is exactly
  `SmulClosedWp p hp : ∀ u v in the span, ∀ n ∈ ℤ, u₍ₙ₎v is in the span` — and it is *equivalent*
  to `StrongGenWp p hp`, so the reduction loses nothing.

### §5–§6  Target 2: `OmegaNilpotentWp`, made ambient, and two unconditional consequences

* `omegaPowAmb` — the ambient vector `L₋₂^m|0⟩ ∈ V_{L_p}` (`omegaPowAmb_succ_L`), and
  `omegaPowMem_iff` — **`OmegaPowMem p hp m ↔ L₋₂^m|0⟩ ∈ ι(C₂(W(p)))`**.  This is strictly
  sharper than `Examples.TripletWpC2` §7, which still spoke about the subalgebra's own quotient.
* `VirDeep`, `virDeep_le_O₂amb` — **every Virasoro lowering mode except `L₋₂` lands in
  `C₂(W(p))`**: `L₋ₙ(W(p)) ⊆ ι(C₂(W(p)))` for `n ≥ 1`, `n ≠ 2` (`n = 1` is `T(V) ⊆ C₂`,
  `n ≥ 3` is `ω₍₋ₙ₊₁₎` with `−n+1 ≤ −2`).  `L₋₂` is the sole exception, and is exactly `ω̄`.
* `Qwp_sq_smul_Ftrip` — the `Q²`-Leibniz expansion `Q²(F₍ₙ₎F) = E₍ₙ₎F + 2H₍ₙ₎H + F₍ₙ₎E` at
  **every** `n` (the `Examples.TripletWpC2` §3 versions all carry `n ≥ −2p`, where the left side
  vanishes; here the left side is the interesting one).
* `smul_Htrip_Htrip_bottom_mem_O₂amb` and `Qwp_sq_latChargeGen_mem_O₂amb` —
  **unconditional**: `H₍−2p−1₎H ∈ ι(C₂(W(p)))` and `Q²e^{−2α} ∈ ι(C₂(W(p)))`.  The second needs
  §1: `Q²e^{−2α} = ε⁻¹·Q²(F₍−2p−1₎F) = ε⁻¹(E₍−2p−1₎F + 2H₍−2p−1₎H + F₍−2p−1₎E)`, and every
  summand has mode index `−2p−1 ≤ −2`.  These are the two inputs Adamović–Milas Corollary 4.6
  consumes, and they are theorems, not hypotheses.
* **Weight bookkeeping, verified against the deformed grading** `q_p(m) = p m² − (p−1)m`:
  `latChargeGen_neg_two_alpha_mem_grading` (`wt e^{−2α} = q_p(−2) = 6p − 2`),
  `Qwp_mem_grading` (`Q = (e^α)₍₀₎` preserves weight, since `wt e^α = 1`),
  `smul_Htrip_Htrip_bottom_mem_grading` (`wt H₍−2p−1₎H = (2p−1)+(2p−1)+(2p+1)−1 = 6p − 2`),
  `omegaPowAmb_mem_grading` (`wt L₋₂^m|0⟩ = 2m`), and `amCor44_exponent`
  (`2(3p−1) = 6p − 2`).  So all four terms of the `AMOmegaIdentity` identity live in the single graded
  piece `𝒱_{6p−2}`, and `m = 3p − 1` is **forced**, not guessed: the Adamović–Milas exponent is
  pure weight arithmetic.

### §7  The residual, as a single named identity in `V_{L_p}`

* `AMOmegaIdentity p hp m` — **Adamović–Milas Corollary 4.6**, verbatim, as a `Prop` about vectors of
  `V_{L_p}`:
  `Q²e^{−2α} = A·H₍−2p−1₎H + B·L₋₂^m|0⟩ + w`, with `B ≠ 0` and `w ∈ VirDeep p hp`.
* `omegaPowMem_of_amOmegaIdentity` — `AMOmegaIdentity p hp m ⟹ OmegaPowMem p hp m`, hence
  `c2Cofinite_tripletWVOA_of_amCor44`: with `m = 3p − 1`,
  `AdjoinGenWp p hp` and `AMOmegaIdentity p hp (3p−1)` give `C2Cofinite (tripletWVOA p hp)` and
  `dim_ℂ W(p)/C₂(W(p)) ≤ 48p − 16`.

## ⚠ Honest accounting of what `AMOmegaIdentity` is and is not

`AMOmegaIdentity` is a **hypothesis**, named, cited, and visible in the signature of every statement that
uses it.  Three points, so that nobody mistakes its status.

1. **It is not circular and not vacuous.**  Its force is the clause `w ∈ VirDeep p hp`, which is a
   *strictly smaller* submodule than `O₂amb p hp`: `VirDeep` allows only `ω` in the left slot of
   the product, `O₂amb` allows every element of `W(p)`.  Replacing `VirDeep` by `O₂amb` would turn
   `AMOmegaIdentity` into a restatement of the conclusion; with `VirDeep` it does not follow from the
   conclusion, and `virDeep_le_O₂amb` is the (one-way) implication that makes it usable.

2. **It is slightly stronger than the sentence printed in Adamović–Milas.**  Their `w` is a
   combination of Virasoro monomials *each containing some* `L(−n)`, `n ≥ 3`, anywhere in the
   word; `VirDeep` asks for the `L(−n)`, `n ≥ 3` (or `n = 1`) to be **leftmost**.  The two agree
   after Virasoro PBW reordering, which this repository does not have in any form, so the stronger
   form is what is stated.  Recorded as a real, if narrow, gap between the hypothesis and the
   citation.

3. **The mathematics that is missing is the constant `B ≠ 0`.**  Adamović–Milas obtain it from
   `A(M(1)‾_p) ≅ ℂ[x]` (Adamović 2003) read off the polynomial `Φ_p` — an import, not a
   computation.  Reproducing it in Lean needs a Virasoro-vacuum-module (PBW/partition) structure
   *inside* the Feigin–Fuchs Fock space `F₀`, and a closed form for `Q²` on a charged vacuum.
   Neither exists in this repository; building them is a substantial separate project.

⚠ Nothing in this file weakens, strengthens or repairs the analysis in the `Examples.TripletWpC2`
module docstring of why Adamović–Milas Theorem 3.1 step 5 is a non-sequitur.  That route is not
attempted here either.

## Status

Every declaration in this file is proved, `sorry`-free, `admit`-free, `native_decide`-free and
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`); the theorem
`VOA.pbw` is not used.  `AMOmegaIdentity` is a `def … : Prop`,
never proved and never assumed: it appears only as an explicit argument.

## References
* D. Adamović and A. Milas, *On the triplet vertex algebra `W(p)`*, Adv. Math. **217** (2008)
  2664–2699 (arXiv:0707.1857): Prop. 2.3(ii), eq. (2.2), eq. (2.4), Lem. 4.1–4.2, Thm 4.3,
  Cor. 4.4.
* D. Adamović, *Classification of irreducible modules of certain subalgebras of free boson vertex
  algebra*, J. Algebra **270** (2003) 115–132.
* T. Abe, *A ℤ₂-orbifold model of the symplectic fermionic VOA*, Math. Z. **255** (2007) 755–792,
  Prop. 2.2.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpC2

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp

/-! ## §1  The bottom lattice product: `(e^α)₍−⟨α,β⟩−1₎ e^β = ε(α,β)·e^{α+β}`

`smul_latChargeGen_eq_zero` (`Examples.TripletWpC2` §1) reads off the vanishing of every mode
`n ≥ −⟨α,β⟩` from the fact that `Yeαvec_tmul` puts `EEVec α (−n−1−⟨α,β⟩)` in front of the vacuum
and `EEVec_vacuum` kills it at negative index.  At `n = −⟨α,β⟩−1` that index is exactly `0`, where
`EEVec_vacuum` returns `vSchur α 0 = 1` instead — so the *same* computation, one mode lower,
delivers the charged vacuum with the FLM cocycle in front.  No new input. -/

/-- **The first non-vanishing mode.**  `(e^α)₍−⟨α,β⟩−1₎ e^β = ε(α,β)·e^{α+β}`. -/
theorem smul_latChargeGen_bottom (L : IntegralLattice) (α β : L.carrier) :
    mode (Yeαvec L α) (-L.form α β - 1) (latChargeGen L β)
      = latticeCocycle L α β • latChargeGen L (α + β) := by
  simp only [mode_apply, latChargeGen]
  rw [Yeαvec_tmul, show -(-L.form α β - 1) - 1 - L.form α β = (0 : ℤ) from by ring,
    EEVec_vacuum, if_pos (le_refl (0 : ℤ)), Int.toNat_zero, vSchur_zero]
  rfl

/-- **`F₍−2p−1₎F = ε(−α,−α)·e^{−2α}`** — the first mode below the vanishing range
`smul_Ftrip_Ftrip`, and the only new lattice input this file needs. -/
theorem smul_Ftrip_Ftrip_bottom (p : ℕ) (hp : 1 ≤ p) :
    (tripletLatticeVOA p hp).smul (Ftrip p) (-(2 * (p : ℤ)) - 1) (Ftrip p)
      = latticeCocycle (latP p) (-alphaP p) (-alphaP p)
          • latChargeGen (latP p) (-alphaP p + -alphaP p) := by
  have hF : Ftrip p = latChargeGen (latP p) (-alphaP p) := rfl
  have hform : (latP p).form (-alphaP p) (-alphaP p) = 2 * (p : ℤ) := by
    rw [Screen.form_neg_self, latP_form_alpha]
  rw [PreVertexAlgebra.smul_def, hF, Y_latChargeGen,
    show -(2 * (p : ℤ)) - 1 = -(latP p).form (-alphaP p) (-alphaP p) - 1 from by rw [hform]]
  exact smul_latChargeGen_bottom (latP p) (-alphaP p) (-alphaP p)

/-! ## §2  The ambient image of `C₂(W(p))`

`smul_coe` makes the inclusion `ι : W(p) ↪ V_{L_p}` intertwine every product, and `ι` is
injective, so `ι(C₂(W(p)))` is a faithful copy: a membership in `C₂(W(p))` is *equivalent* to the
corresponding ambient membership.  ⚠ `O₂amb` is **not** `O₂ (tripletLatticeVOA p hp) ⊓ W(p)` —
that would be the ambient `C₂`-space, which is strictly larger. -/

/-- The image of `C₂(W(p))` inside `V_{L_p}` under the inclusion. -/
noncomputable def O₂amb (p : ℕ) (hp : 1 ≤ p) : Submodule ℂ (LatModuleGen (latP p)) :=
  Submodule.map (tripletW p hp).carrier.subtype (O₂ (tripletWVOA p hp))

/-- **Faithfulness**: for a state of `W(p)`, the ambient membership and the intrinsic one agree. -/
theorem mem_O₂amb_iff (p : ℕ) (hp : 1 ≤ p) (x : (tripletW p hp).carrier) :
    ((x : LatModuleGen (latP p)) ∈ O₂amb p hp) ↔ x ∈ O₂ (tripletWVOA p hp) := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (Subtype.ext hxy : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **Every deep ambient product of two states of `W(p)` lies in `ι(C₂(W(p)))`**, for every
mode index `n ≤ −2`.  (`Modules.PoissonDescent.smul_le_neg_two_mem_O₂`, transported.) -/
theorem smul_mem_O₂amb (p : ℕ) (hp : 1 ≤ p) {u v : LatModuleGen (latP p)}
    (hu : u ∈ (tripletW p hp).carrier) (hv : v ∈ (tripletW p hp).carrier) {n : ℤ} (hn : n ≤ -2) :
    (tripletLatticeVOA p hp).smul u n v ∈ O₂amb p hp := by
  have h : (tripletWVOA p hp).smul ⟨u, hu⟩ n ⟨v, hv⟩ ∈ O₂ (tripletWVOA p hp) :=
    smul_le_neg_two_mem_O₂ (tripletWVOA p hp) ⟨u, hu⟩ ⟨v, hv⟩ hn
  have hc := smul_coe p hp ⟨u, hu⟩ ⟨v, hv⟩ n
  rw [← hc]
  exact (mem_O₂amb_iff p hp _).2 h

/-- Virasoro modes of `W(p)` are the ambient Virasoro modes. -/
theorem L_coe (p : ℕ) (hp : 1 ≤ p) (k : ℤ) (z : (tripletW p hp).carrier) :
    (((tripletWVOA p hp).L k z : (tripletW p hp).carrier) : LatModuleGen (latP p))
      = (tripletLatticeVOA p hp).L k (z : LatModuleGen (latP p)) := by
  have h1 : (tripletWVOA p hp).L k z
      = (tripletWVOA p hp).smul (tripletWVOA p hp).conformalVector (k + 1) z := rfl
  have h2 : (tripletLatticeVOA p hp).L k (z : LatModuleGen (latP p))
      = (tripletLatticeVOA p hp).smul (omegaTrip p) (k + 1) (z : LatModuleGen (latP p)) := rfl
  rw [h1, h2, smul_coe]
  rfl

/-- **`L₋₁(W(p)) ⊆ ι(C₂(W(p)))`** — the translation image is always in `C₂`. -/
theorem L_neg_one_mem_O₂amb (p : ℕ) (hp : 1 ≤ p) {y : LatModuleGen (latP p)}
    (hy : y ∈ (tripletW p hp).carrier) :
    (tripletLatticeVOA p hp).L (-1) y ∈ O₂amb p hp := by
  have h : (tripletWVOA p hp).L (-1) ⟨y, hy⟩ ∈ O₂ (tripletWVOA p hp) :=
    L_neg_one_mem_O₂ (tripletWVOA p hp) ⟨y, hy⟩
  have hc := L_coe p hp (-1) ⟨y, hy⟩
  rw [← hc]
  exact (mem_O₂amb_iff p hp _).2 h

/-! ## §3  The iterated-product span, transported

The two inclusions between `ι(iterProdSpan_{W(p)})` and `iterProdSpan_{V_{L_p}}` are proved by
induction on `IsIterProd`, using `val_range_genWp` (the two generating sets match) in both
directions. -/

/-- Every iterated product of `W(p)`-generators is, as an ambient vector, an iterated product of
`tripGens p`. -/
theorem coe_mem_iterProdSpan_amb (p : ℕ) (hp : 1 ≤ p) {y : (tripletW p hp).carrier}
    (hy : IsIterProd (tripletWVOA p hp) (Set.range (genWp p hp)) y) :
    (y : LatModuleGen (latP p)) ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  induction hy with
  | vacuum =>
      show (((tripletWVOA p hp).vacuum : (tripletW p hp).carrier) : LatModuleGen (latP p))
        ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
      rw [tripletWVOA_vacuum_coe]
      exact vacuum_mem_iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
  | step s hs m hm x _ ih =>
      rw [smul_coe]
      refine smul_mem_iterProdSpan (tripletLatticeVOA p hp) (tripGens p) ?_ hm ih
      rw [← val_range_genWp p hp]
      exact ⟨s, hs, rfl⟩

/-- Every ambient iterated product of `tripGens p` lifts to `W(p)`, into the intrinsic span. -/
theorem exists_lift_isIterProd (p : ℕ) (hp : 1 ≤ p) {x : LatModuleGen (latP p)}
    (hx : IsIterProd (tripletLatticeVOA p hp) (tripGens p) x) :
    ∃ y : (tripletW p hp).carrier,
      y ∈ iterProdSpan (tripletWVOA p hp) (Set.range (genWp p hp))
        ∧ (y : LatModuleGen (latP p)) = x := by
  induction hx with
  | vacuum =>
      exact ⟨(tripletWVOA p hp).vacuum,
        vacuum_mem_iterProdSpan (tripletWVOA p hp) (Set.range (genWp p hp)), rfl⟩
  | step s hs m hm x _ ih =>
      obtain ⟨y, hy, rfl⟩ := ih
      have hs' : s ∈ Subtype.val '' (Set.range (genWp p hp)) := by
        rw [val_range_genWp p hp]; exact hs
      obtain ⟨t, ht, rfl⟩ := hs'
      exact ⟨(tripletWVOA p hp).smul t (-m) y,
        smul_mem_iterProdSpan (tripletWVOA p hp) (Set.range (genWp p hp)) ht hm hy,
        smul_coe p hp t y (-m)⟩

/-- **The transport identity**: the image of the intrinsic iterated-product span is the ambient
iterated-product span. -/
theorem map_iterProdSpan_genWp (p : ℕ) (hp : 1 ≤ p) :
    Submodule.map (tripletW p hp).carrier.subtype
        (iterProdSpan (tripletWVOA p hp) (Set.range (genWp p hp)))
      = iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  refine le_antisymm ?_ ?_
  · rw [iterProdSpan, Submodule.map_span, Submodule.span_le]
    rintro x ⟨y, hy, rfl⟩
    exact coe_mem_iterProdSpan_amb p hp hy
  · rw [iterProdSpan, Submodule.span_le]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := exists_lift_isIterProd p hp hx
    exact ⟨y, hy, rfl⟩

/-! ## §4  Target 1: strong generation, as a statement about `V_{L_p}` -/

/-- The **free** half: the ambient iterated-product span of `{ω_λ, E, H, F}` already sits inside
`W(p)`, since `W(p)` contains the four generators and is closed under all products. -/
theorem iterProdSpan_amb_le_carrier (p : ℕ) (hp : 1 ≤ p) :
    iterProdSpan (tripletLatticeVOA p hp) (tripGens p) ≤ (tripletW p hp).carrier := by
  rw [iterProdSpan, Submodule.span_le]
  intro x hx
  induction hx with
  | vacuum => exact (tripletW p hp).vacuum_mem
  | step s hs m _ y _ ih =>
      exact (tripletW p hp).smul_mem s
        (VOASubalgebra.subset_generated (tripletLatticeVOA p hp) (tripGens p) hs) (-m) y ih

/-- **Strong generation, one-sided ambient form.** -/
theorem strongGenWp_iff_carrier_le (p : ℕ) (hp : 1 ≤ p) :
    StrongGenWp p hp ↔
      (tripletW p hp).carrier ≤ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  constructor
  · intro h x hx
    have hmem : (⟨x, hx⟩ : (tripletW p hp).carrier)
        ∈ iterProdSpan (tripletWVOA p hp) (Set.range (genWp p hp)) := by rw [h]; trivial
    rw [← map_iterProdSpan_genWp p hp]
    exact ⟨⟨x, hx⟩, hmem, rfl⟩
  · intro h
    refine le_antisymm le_top fun z _ => ?_
    have hz : (z : LatModuleGen (latP p))
        ∈ Submodule.map (tripletW p hp).carrier.subtype
            (iterProdSpan (tripletWVOA p hp) (Set.range (genWp p hp))) := by
      rw [map_iterProdSpan_genWp p hp]
      exact h z.2
    obtain ⟨y, hy, hyz⟩ := hz
    exact (Subtype.ext hyz : y = z) ▸ hy

/-- **Target 1, in its final ambient form.**  `W(p)` is strongly generated by
`{ω_λ, E, H, F}` **iff** the span of the iterated strictly-negative modes of those four states on
`|0⟩` is already the whole subalgebra they generate — i.e. iff that span is closed under the
non-negative modes and the homogeneous projections as well.

This is Adamović–Milas Proposition 2.3(ii).  It is *not* proved here: the statement is only moved
out of the subalgebra's own quotient and into `V_{L_p}`, where both sides are explicit subspaces
of the Fock space `Fock ⊗ ℂ[L_p]` and the residual is the closure of the `W`-algebra OPE on the
four generators. -/
theorem strongGenWp_iff (p : ℕ) (hp : 1 ≤ p) :
    StrongGenWp p hp ↔
      iterProdSpan (tripletLatticeVOA p hp) (tripGens p) = (tripletW p hp).carrier := by
  rw [strongGenWp_iff_carrier_le]
  constructor
  · intro h; exact le_antisymm (iterProdSpan_amb_le_carrier p hp) h
  · intro h; exact le_of_eq h.symm

/-! ### Three of the four subalgebra clauses, discharged

By `strongGenWp_iff` and `VOASubalgebra.generated_le`, `StrongGenWp p hp` follows as soon as the
ambient span `iterProdSpan (tripletLatticeVOA p hp) (tripGens p)` is exhibited as a
`VOASubalgebra`.  Three of its four fields cost nothing: `vacuum_mem` and `conformal_mem` are
`vacuum_mem_iterProdSpan` / `subset_iterProdSpan` (`ω_λ` is one of the four generators), and
`graded` follows because every iterated product of *homogeneous* generators is homogeneous
(`tripGens_homogeneous` + `step_mem_grading`), so each `piHom` either fixes it or kills it.

What is left is exactly one closure statement, `SmulClosedWp`. -/

/-- Every iterated product of the four (homogeneous) generators is homogeneous. -/
theorem isIterProd_homog (p : ℕ) (hp : 1 ≤ p) {x : LatModuleGen (latP p)}
    (hx : IsIterProd (tripletLatticeVOA p hp) (tripGens p) x) :
    ∃ k : ℤ, x ∈ (tripletLatticeVOA p hp).grading k := by
  induction hx with
  | vacuum => exact ⟨0, (tripletLatticeVOA p hp).vacuum_mem⟩
  | step s hs m _ y _ ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨j, hj⟩ := tripGens_homogeneous p hp s hs
      exact ⟨j + k + m - 1, step_mem_grading (tripletLatticeVOA p hp) hj hk⟩

/-- The ambient iterated-product span is a **graded** submodule. -/
theorem piHom_mem_iterProdSpan (p : ℕ) (hp : 1 ≤ p) (n : ℤ) {v : LatModuleGen (latP p)}
    (hv : v ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) :
    piHom (tripletLatticeVOA p hp) n v
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p) := by
  refine Submodule.span_induction
    (p := fun v _ => piHom (tripletLatticeVOA p hp) n v
      ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)) ?_ ?_ ?_ ?_ hv
  · intro x hx
    obtain ⟨k, hk⟩ := isIterProd_homog p hp hx
    by_cases hnk : n = k
    · subst hnk
      rw [piHom_of_mem _ hk]
      exact Submodule.subset_span hx
    · rw [piHom_of_mem_ne _ (fun h => hnk h.symm) hk]
      exact zero_mem _
  · simp only [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
  · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ _ ha

/-- **(★) The single residual closure property.**  The span of the iterated strictly-negative
modes of `{ω_λ, E, H, F}` on `|0⟩` is closed under *all* vertex products of its own members —
equivalently (by `mode_iterate` and `mode_commutator`, neither used here) the `W`-algebra OPE
closes on the four strong generators.

This is the honest residual of Adamović–Milas Proposition 2.3(ii). -/
def SmulClosedWp (p : ℕ) (hp : 1 ≤ p) : Prop :=
  ∀ u ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p), ∀ n : ℤ,
    ∀ v ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p),
      (tripletLatticeVOA p hp).smul u n v ∈ iterProdSpan (tripletLatticeVOA p hp) (tripGens p)

/-- The ambient span, as a `VOASubalgebra`, granted `(★)`. -/
noncomputable def iterProdSubalg (p : ℕ) (hp : 1 ≤ p) (hsmul : SmulClosedWp p hp) :
    VOASubalgebra (tripletLatticeVOA p hp) where
  carrier := iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
  vacuum_mem := vacuum_mem_iterProdSpan (tripletLatticeVOA p hp) (tripGens p)
  conformal_mem :=
    subset_iterProdSpan (tripletLatticeVOA p hp) (tripGens p) (omegaTrip_mem_tripGens p)
  smul_mem := hsmul
  graded := fun n _ hv => piHom_mem_iterProdSpan p hp n hv

/-- **Target 1, reduced to one clause.**  `(★)` alone implies strong generation: the vacuum,
conformal and gradedness clauses of `VOASubalgebra` are discharged above, so `generated_le`
applies and `W(p)` collapses onto the iterated-product span. -/
theorem strongGenWp_of_smulClosed (p : ℕ) (hp : 1 ≤ p) (hsmul : SmulClosedWp p hp) :
    StrongGenWp p hp := by
  rw [strongGenWp_iff_carrier_le]
  exact VOASubalgebra.generated_le (iterProdSubalg p hp hsmul)
    (fun x hx => subset_iterProdSpan (tripletLatticeVOA p hp) (tripGens p) hx)

/-- The converse: strong generation makes the span a subalgebra, so `(★)` is *equivalent* to
strong generation — the reduction loses nothing. -/
theorem smulClosedWp_of_strongGenWp (p : ℕ) (hp : 1 ≤ p) (h : StrongGenWp p hp) :
    SmulClosedWp p hp := by
  rw [strongGenWp_iff p hp] at h
  intro u hu n v hv
  rw [h] at hu hv ⊢
  exact (tripletW p hp).smul_mem u hu n v hv

/-- `(★) ↔ StrongGenWp`. -/
theorem strongGenWp_iff_smulClosed (p : ℕ) (hp : 1 ≤ p) :
    StrongGenWp p hp ↔ SmulClosedWp p hp :=
  ⟨smulClosedWp_of_strongGenWp p hp, strongGenWp_of_smulClosed p hp⟩

/-! ## §5  Target 2: `ω̄`-nilpotency as the membership of `L₋₂^m|0⟩` in `ι(C₂(W(p)))` -/

/-- The ambient vector `L₋₂^m|0⟩ ∈ V_{L_p}`. -/
noncomputable def omegaPowAmb (p : ℕ) (hp : 1 ≤ p) : ℕ → LatModuleGen (latP p)
  | 0 => latVacuumGen (latP p)
  | (m + 1) => (tripletLatticeVOA p hp).smul (omegaTrip p) (-1) (omegaPowAmb p hp m)

@[simp] theorem omegaPowAmb_zero (p : ℕ) (hp : 1 ≤ p) :
    omegaPowAmb p hp 0 = latVacuumGen (latP p) := rfl

/-- `omegaPowAmb` really is the iterated `L₋₂`. -/
theorem omegaPowAmb_succ_L (p : ℕ) (hp : 1 ≤ p) (m : ℕ) :
    omegaPowAmb p hp (m + 1) = (tripletLatticeVOA p hp).L (-2) (omegaPowAmb p hp m) :=
  TripletNilp.smul_conformal_neg_one (tripletLatticeVOA p hp) (omegaPowAmb p hp m)

/-- The Poisson powers of `ω` in `W(p)`, seen inside `V_{L_p}`. -/
theorem coe_pMulPow_genOmega (p : ℕ) (hp : 1 ≤ p) (m : ℕ) :
    ((TripletNilp.pMulPow (tripletWVOA p hp) (genOmega p hp) m : (tripletW p hp).carrier)
      : LatModuleGen (latP p)) = omegaPowAmb p hp m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [TripletNilp.pMulPow_succ, smul_coe, genOmega_coe, ih]
      rfl

theorem omegaPowAmb_mem_carrier (p : ℕ) (hp : 1 ≤ p) (m : ℕ) :
    omegaPowAmb p hp m ∈ (tripletW p hp).carrier := by
  rw [← coe_pMulPow_genOmega p hp m]
  exact (TripletNilp.pMulPow (tripletWVOA p hp) (genOmega p hp) m).2

/-- **Target 2, in ambient form.**  `ω̄^m = 0` in `A₂(W(p))` is exactly the membership of the
explicit Fock-space vector `L₋₂^m|0⟩` in the image of `C₂(W(p))`. -/
theorem omegaPowMem_iff (p : ℕ) (hp : 1 ≤ p) (m : ℕ) :
    OmegaPowMem p hp m ↔ omegaPowAmb p hp m ∈ O₂amb p hp := by
  rw [← coe_pMulPow_genOmega p hp m]
  exact (mem_O₂amb_iff p hp _).symm

/-! ### Weight bookkeeping: everything sits in `𝒱_{6p−2}`, and `m = 3p − 1` is forced

The exponent `3p − 1` of Adamović–Milas Corollary 4.6 is not a guess and not a deep fact: it is
the unique `m` for which the two sides of the `AMOmegaIdentity` identity can live in the same graded
piece.  Every ingredient is checked here against the deformed grading
`q_p(m) = p m² − (p−1)m` of `tripletLatticeVOA`. -/

/-- `wt(L₋₂^m|0⟩) = 2m`. -/
theorem omegaPowAmb_mem_grading (p : ℕ) (hp : 1 ≤ p) (m : ℕ) :
    omegaPowAmb p hp m ∈ (tripletLatticeVOA p hp).grading (2 * (m : ℤ)) := by
  induction m with
  | zero => simpa using (tripletLatticeVOA p hp).vacuum_mem
  | succ m ih =>
      have h := (tripletLatticeVOA p hp).smul_mem_grading (omegaTrip_mem_grading p hp) ih (-1)
      rwa [show (2 : ℤ) + 2 * (m : ℤ) - (-1) - 1 = 2 * ((m : ℤ) + 1) from by ring,
        ← Nat.cast_succ] at h

theorem neg_alpha_add_neg_alpha (p : ℕ) :
    (-alphaP p + -alphaP p : (latP p).carrier) = ((-2 : ℤ) : (latP p).carrier) := rfl

/-- `q_p(−2) = 6p − 2` — the deformed weight of `e^{−2α}`. -/
theorem qZP_neg_two (p : ℕ) : qZP p (-2) = 6 * (p : ℤ) - 2 := by
  simp only [qZP]; ring

/-- `wt(e^{−2α}) = 6p − 2`. -/
theorem latChargeGen_neg_two_alpha_mem_grading (p : ℕ) (hp : 1 ≤ p) :
    latChargeGen (latP p) (-alphaP p + -alphaP p)
      ∈ (tripletLatticeVOA p hp).grading (6 * (p : ℤ) - 2) := by
  rw [neg_alpha_add_neg_alpha p, ← qZP_neg_two p]
  exact latChargeGen_mem_gradTrip p (-2)

/-- `wt(H₍−2p−1₎H) = (2p−1) + (2p−1) + (2p+1) − 1 = 6p − 2`. -/
theorem smul_Htrip_Htrip_bottom_mem_grading (p : ℕ) (hp : 1 ≤ p) :
    (tripletLatticeVOA p hp).smul (Htrip p) (-(2 * (p : ℤ)) - 1) (Htrip p)
      ∈ (tripletLatticeVOA p hp).grading (6 * (p : ℤ) - 2) := by
  have h := (tripletLatticeVOA p hp).smul_mem_grading (Htrip_mem_grading p hp)
    (Htrip_mem_grading p hp) (-(2 * (p : ℤ)) - 1)
  rwa [show (2 * (p : ℤ) - 1) + (2 * (p : ℤ) - 1) - (-(2 * (p : ℤ)) - 1) - 1
      = 6 * (p : ℤ) - 2 from by ring] at h

/-- **The long screening preserves the deformed weight**: `Q = (e^α)₍₀₎` and `wt(e^α) = 1`. -/
theorem Qwp_mem_grading (p : ℕ) (hp : 1 ≤ p) {k : ℤ} {x : LatModuleGen (latP p)}
    (hx : x ∈ (tripletLatticeVOA p hp).grading k) :
    Qwp p hp x ∈ (tripletLatticeVOA p hp).grading k := by
  have hQ : Qwp p hp x
      = (tripletLatticeVOA p hp).smul (latChargeGen (latP p) (alphaP p)) 0 x := rfl
  have h := (tripletLatticeVOA p hp).smul_mem_grading
    (latChargeGen_alpha_mem_grade_one p hp) hx 0
  rw [hQ]
  rwa [show (1 : ℤ) + k - 0 - 1 = k from by ring] at h

/-- `wt(Q²e^{−2α}) = 6p − 2`. -/
theorem Qwp_sq_latChargeGen_mem_grading (p : ℕ) (hp : 1 ≤ p) :
    Qwp p hp (Qwp p hp (latChargeGen (latP p) (-alphaP p + -alphaP p)))
      ∈ (tripletLatticeVOA p hp).grading (6 * (p : ℤ) - 2) :=
  Qwp_mem_grading p hp (Qwp_mem_grading p hp (latChargeGen_neg_two_alpha_mem_grading p hp))

/-- **The exponent is forced.**  `wt(L₋₂^m|0⟩) = 2m` must equal `6p − 2`, so `m = 3p − 1`. -/
theorem amCor44_exponent (p : ℕ) (hp : 1 ≤ p) :
    2 * ((3 * p - 1 : ℕ) : ℤ) = 6 * (p : ℤ) - 2 := by omega

/-- `wt(L₋₂^{3p−1}|0⟩) = 6p − 2`: the last of the four weights, matching the other three. -/
theorem omegaPowAmb_exponent_mem_grading (p : ℕ) (hp : 1 ≤ p) :
    omegaPowAmb p hp (3 * p - 1) ∈ (tripletLatticeVOA p hp).grading (6 * (p : ℤ) - 2) := by
  have h := omegaPowAmb_mem_grading p hp (3 * p - 1)
  rwa [amCor44_exponent p hp] at h

/-! ### `VirDeep`: every Virasoro lowering mode except `L₋₂` lands in `C₂(W(p))` -/

/-- The span of `L₋ₙ(W(p))` for `n ≥ 1`, `n ≠ 2` — Adamović–Milas' `w`-space, in the "leftmost
mode is deep" form that avoids any Virasoro PBW reordering. -/
noncomputable def VirDeep (p : ℕ) (hp : 1 ≤ p) : Submodule ℂ (LatModuleGen (latP p)) :=
  Submodule.span ℂ {x | ∃ n : ℤ, 1 ≤ n ∧ n ≠ 2 ∧ ∃ y ∈ (tripletW p hp).carrier,
    x = (tripletLatticeVOA p hp).L (-n) y}

/-- **`L₋ₙ(W(p)) ⊆ ι(C₂(W(p)))` for every `n ≥ 1` with `n ≠ 2`.**  `n = 1` is `T(V) ⊆ C₂`;
`n ≥ 3` is `ω₍₋ₙ₊₁₎` with `−n+1 ≤ −2`.  `L₋₂` is the sole exception — it is `ω̄` itself. -/
theorem virDeep_le_O₂amb (p : ℕ) (hp : 1 ≤ p) : VirDeep p hp ≤ O₂amb p hp := by
  rw [VirDeep, Submodule.span_le]
  rintro x ⟨n, hn1, hn2, y, hy, rfl⟩
  rcases eq_or_lt_of_le hn1 with h1 | h3
  · rw [show (-n : ℤ) = -1 from by omega]
    exact L_neg_one_mem_O₂amb p hp hy
  · have hL : (tripletLatticeVOA p hp).L (-n) y
        = (tripletLatticeVOA p hp).smul (omegaTrip p) (-n + 1) y := rfl
    rw [hL]
    exact smul_mem_O₂amb p hp (omegaTrip_mem_tripletW p hp) hy (by omega)

/-! ## §6  Two unconditional memberships: the inputs of Adamović–Milas Corollary 4.6 -/

/-- **The `Q²`-Leibniz expansion at an arbitrary mode index**:
`Q²(F₍ₙ₎F) = E₍ₙ₎F + 2·H₍ₙ₎H + F₍ₙ₎E`.  The `Examples.TripletWpC2` §3 statements are this one
combined with `F₍ₙ₎F = 0`, which needs `n ≥ −2p`; here `n` is unrestricted, and the interesting
case is `n = −2p−1`, where the left side is *not* zero. -/
theorem Qwp_sq_smul_Ftrip (p : ℕ) (hp : 1 ≤ p) (n : ℤ) :
    Qwp p hp (Qwp p hp ((tripletLatticeVOA p hp).smul (Ftrip p) n (Ftrip p)))
      = (tripletLatticeVOA p hp).smul (Etrip p) n (Ftrip p)
        + (2 : ℂ) • (tripletLatticeVOA p hp).smul (Htrip p) n (Htrip p)
        + (tripletLatticeVOA p hp).smul (Ftrip p) n (Etrip p) := by
  simp only [Qwp_leibniz, map_add, Qwp_Ftrip, Qwp_Htrip]
  rw [two_smul]
  abel

theorem neg_two_p_sub_one_le (p : ℕ) (hp : 1 ≤ p) : -(2 * (p : ℤ)) - 1 ≤ -2 := by
  have : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  omega

/-- **Unconditional**: `H₍−2p−1₎H ∈ ι(C₂(W(p)))`.  Adamović–Milas need this to discard the
`A·H₍−2p−1₎H` term of Corollary 4.4; it is free, because `−2p−1 ≤ −2`. -/
theorem smul_Htrip_Htrip_bottom_mem_O₂amb (p : ℕ) (hp : 1 ≤ p) :
    (tripletLatticeVOA p hp).smul (Htrip p) (-(2 * (p : ℤ)) - 1) (Htrip p) ∈ O₂amb p hp :=
  smul_mem_O₂amb p hp (Htrip_mem_tripletW p hp) (Htrip_mem_tripletW p hp)
    (neg_two_p_sub_one_le p hp)

/-- **Unconditional**: `Q²e^{−2α} ∈ ι(C₂(W(p)))`.

`F₍−2p−1₎F = ε·e^{−2α}` (§1) and `Q` is a derivation, so
`ε·Q²e^{−2α} = E₍−2p−1₎F + 2·H₍−2p−1₎H + F₍−2p−1₎E`; every summand has mode index `−2p−1 ≤ −2`
and both factors in `W(p)`, hence lies in `ι(C₂(W(p)))`.  The cocycle `ε` is invertible
(`Screen.latticeCocycle_ne_zero`).

This is the second input of Adamović–Milas Corollary 4.6, and it is a theorem here. -/
theorem Qwp_sq_latChargeGen_mem_O₂amb (p : ℕ) (hp : 1 ≤ p) :
    Qwp p hp (Qwp p hp (latChargeGen (latP p) (-alphaP p + -alphaP p))) ∈ O₂amb p hp := by
  have hε : latticeCocycle (latP p) (-alphaP p) (-alphaP p) ≠ 0 :=
    Screen.latticeCocycle_ne_zero (latP p) (-alphaP p) (-alphaP p)
  have h2 := Qwp_sq_smul_Ftrip p hp (-(2 * (p : ℤ)) - 1)
  rw [smul_Ftrip_Ftrip_bottom p hp, map_smul, map_smul] at h2
  have hsum : latticeCocycle (latP p) (-alphaP p) (-alphaP p)
      • Qwp p hp (Qwp p hp (latChargeGen (latP p) (-alphaP p + -alphaP p))) ∈ O₂amb p hp := by
    rw [h2]
    refine add_mem (add_mem ?_ ?_) ?_
    · exact smul_mem_O₂amb p hp (Etrip_mem_tripletW p hp) (Ftrip_mem_tripletW p hp)
        (neg_two_p_sub_one_le p hp)
    · exact Submodule.smul_mem _ _ (smul_Htrip_Htrip_bottom_mem_O₂amb p hp)
    · exact smul_mem_O₂amb p hp (Ftrip_mem_tripletW p hp) (Etrip_mem_tripletW p hp)
        (neg_two_p_sub_one_le p hp)
  have := Submodule.smul_mem (O₂amb p hp)
    (latticeCocycle (latP p) (-alphaP p) (-alphaP p))⁻¹ hsum
  rwa [smul_smul, inv_mul_cancel₀ hε, one_smul] at this

/-! ## §7  The residual: Adamović–Milas Corollary 4.6, as one identity in `V_{L_p}` -/

/-- **(AM-Cor 4.4)** — the single remaining input for `ω̄`-nilpotency, stated entirely
inside the free-field Fock space `V_{L_p}`:

  `Q²e^{−2α} = A·H₍−2p−1₎H + B·L₋₂^m|0⟩ + w`,  `B ≠ 0`,  `w ∈ VirDeep p hp`.

Adamović–Milas prove it at `m = 3p − 1`; the weight bookkeeping that produces that exponent is
`wt(e^{−2α}) = q_p(−2) = 4p + 2(p−1) = 6p − 2 = 2(3p−1) = wt(L₋₂^{3p−1}|0⟩)`.

See the ⚠ section of the module docstring for exactly how this differs from the printed
statement, and for what is still missing mathematically (the constant `B ≠ 0`). -/
def AMOmegaIdentity (p : ℕ) (hp : 1 ≤ p) (m : ℕ) : Prop :=
  ∃ A B : ℂ, B ≠ 0 ∧ ∃ w ∈ VirDeep p hp,
    Qwp p hp (Qwp p hp (latChargeGen (latP p) (-alphaP p + -alphaP p)))
      = A • (tripletLatticeVOA p hp).smul (Htrip p) (-(2 * (p : ℤ)) - 1) (Htrip p)
        + B • omegaPowAmb p hp m + w

/-- **The reduction.**  `AMOmegaIdentity p hp m` gives `ω̄ ^ m = 0` in `A₂(W(p))`.

Everything on the right of the identity except `B·L₋₂^m|0⟩` is visibly in `ι(C₂(W(p)))` — the
`H`-term by `smul_Htrip_Htrip_bottom_mem_O₂amb`, the `w`-term by `virDeep_le_O₂amb` — and the
left-hand side is too, by `Qwp_sq_latChargeGen_mem_O₂amb`.  Invertibility of `B` finishes. -/
theorem omegaPowMem_of_amOmegaIdentity (p : ℕ) (hp : 1 ≤ p) (m : ℕ) (h : AMOmegaIdentity p hp m) :
    OmegaPowMem p hp m := by
  obtain ⟨A, B, hB, w, hw, heq⟩ := h
  rw [omegaPowMem_iff p hp m]
  have hL := Qwp_sq_latChargeGen_mem_O₂amb p hp
  rw [heq] at hL
  have hA : A • (tripletLatticeVOA p hp).smul (Htrip p) (-(2 * (p : ℤ)) - 1) (Htrip p)
      ∈ O₂amb p hp :=
    Submodule.smul_mem _ _ (smul_Htrip_Htrip_bottom_mem_O₂amb p hp)
  have hwO : w ∈ O₂amb p hp := virDeep_le_O₂amb p hp hw
  have hBmem : B • omegaPowAmb p hp m ∈ O₂amb p hp := by
    have hrw : B • omegaPowAmb p hp m
        = (A • (tripletLatticeVOA p hp).smul (Htrip p) (-(2 * (p : ℤ)) - 1) (Htrip p)
            + B • omegaPowAmb p hp m + w)
          - A • (tripletLatticeVOA p hp).smul (Htrip p) (-(2 * (p : ℤ)) - 1) (Htrip p) - w := by
      abel
    rw [hrw]
    exact sub_mem (sub_mem hL hA) hwO
  have hfin := Submodule.smul_mem (O₂amb p hp) B⁻¹ hBmem
  rwa [smul_smul, inv_mul_cancel₀ hB, one_smul] at hfin

/-- **`C₂`-cofiniteness of `W(p)` from `AdjoinGenWp` and the single lattice identity
`AMOmegaIdentity`**, with the dimension bound.  At Adamović–Milas' exponent `m = 3p − 1` this reads
`dim_ℂ W(p)/C₂(W(p)) ≤ 48p − 16`.

⚠ Both inputs are hypotheses; neither is proved anywhere in this repository. -/
theorem c2Cofinite_tripletWVOA_of_amCor44 (p : ℕ) (hp : 1 ≤ p) (m : ℕ)
    (hgen : AdjoinGenWp p hp) (h : AMOmegaIdentity p hp m) :
    C2Cofinite (tripletWVOA p hp)
      ∧ Module.finrank ℂ (A₂ (tripletWVOA p hp)) ≤ 16 * m :=
  c2Cofinite_tripletWVOA_of_omegaPowMem p hp m hgen (omegaPowMem_of_amOmegaIdentity p hp m h)

end VOA.LatGen.WpC2
