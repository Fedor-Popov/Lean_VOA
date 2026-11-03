/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.DoubletHalfLattice
import VOA.Examples.LatticeSuperAmbientB

/-!
# The doublet algebra `A(p)` at a concrete half lattice — closing the loop

`Examples.DoubletAp` states everything about `A(p) = ⟨ω, a⁻, a⁺⟩` for an *abstract*
`DeformedAmbient`, and lists as its **gap 1** the absence of any concrete instance.
`Examples.DoubletHalfLattice` supplies the concrete half lattice `½ℤγ` as an
`IntegralLattice` together with its ℚ-valued quadratic refinement, and
`Examples.LatticeSuperAmbientB` supplies a `SuperNearVOA` on `LatModuleGen L` for *any* even,
positive-definite `L` carrying a `QFinite` refinement compatible with a background charge.

This file screws the two together.  Everything below is stated for a natural number `p` with

  `h4 : 4 ∣ p`  and  `hp : 0 < p`,

so `p ∈ {4, 8, 12, …}`.  That range is **not** a convenience: it is exactly the range in which
the half lattice is an *even* lattice (`HalfLat.hlatP_even_iff`), hence exactly the range the
bosonic vertex map `YfullGen` — on which both candidate ambients are built — applies to.  See
§7 for the complementary branch and why it is out of reach here.

## Which ambient, and why

`Examples.LatticeSuperAmbientB` (`SAmbB.latSNVOA` / `SAmbB.deformedAmbient`).  Both candidate
ambients compile and both are usable; `SAmbB` was chosen because

* it is phrased throughout in **`BgB`**, which is the convention of
  `Examples.DoubletGenerators` and of `DoubletAp.DeformedAmbient` (`W.L 0 = BgB.LBG L lam 0`),
  so no `BgA`/`BgB` bridge is needed anywhere in this file;
* it derives `BoundedBelow` from `QFinite` **alone** (`SAmbB.qFinite_bddBelow`), so the single
  arithmetic input `HalfLat.qFinite_qrH` discharges both the finite-dimensionality of the
  weight spaces and the lower bound on the grading;
* it exposes `SAmbB.deformedAmbient` directly as a `DoubletAp.DeformedAmbient`, which is the
  interface `DoubletAp` asks for.

(`Examples.LatticeSuperAmbientA` performs its own instantiation at `Triplet.latP r` with
`p = 4r`.  This file instantiates instead at `HalfLat.hlatP p` — the lattice built for the
purpose in `Examples.DoubletHalfLattice`, indexed by `p` rather than `r` — so the central
charge, the weights and the mod-4 fork are all stated directly in `p`.)

## Main definitions

* `latD p` — the half lattice `½ℤγ = HalfLat.hlatP p`, and `gD p` its generator `g = γ/2`.
* `cD p = (p−1)/p`, `lamD p = cD p · g` — the **background charge** of the half lattice.
  This is the object no previous file constructed for `hlatP`.
* `ambientC p h4 hp` — the `ℂ`-graded `SuperNearVOA` on `LatModuleGen (hlatP p)`.
* `deformedAmbientC p h4 hp` — it as a `DoubletAp.DeformedAmbient`, closing `DoubletAp` gap 1
  at a concrete lattice.
* `doubletApC p h4 hp` — **`A(p)` itself**, a `SuperVOASubalgebra` of `ambientC`.

## Main results

* `hlamD` — `⟨λ, g⟩ = (p−1)/2`, and `hggD` — `2⟨g,g⟩ = p`.  These are *literally* the two
  hypotheses `Examples.DoubletGenerators` is quantified over, so every one of its weight
  theorems applies to this lattice by feeding it these two terms.
* `bgCompatD` — `⟨λ,β⟩ = ½⟨β,β⟩ − q β`, the one condition tying the background charge to the
  refinement.  This is what makes `L₀^λ` grade `gradingLatGenQ`.
* `doubletApC_boundedBelow` — **target (d)**: `A(p)` is bounded below.
* `ambientC_not_positivity` — the ambient is genuinely **not** positive: `e^{+g}` is a non-zero
  state of weight `(2−p)/4 < 0`.  So `BoundedBelow` is forced, not chosen.
* `ambientC_centralCharge` — **target (e)**: `c = 1 − 6(p−1)²/p`, computed from
  `BgA.bgForm_latBg`, and `doubletApC_centralCharge_eq_tripletW`: the same value the triplet
  algebra `W(p)` carries.
* `doubletApC_parity_zero` and `hint_false_of_four_dvd` — **target (f)**, the structural
  fork, proved rather than asserted: in this ambient the parity is trivial, so
  `A(p)₀̄ = A(p)`, and its weight `(3p−2)/4` is a genuine half-integer.  Hence the integrality
  hypothesis `hint` of `DoubletAp.doubletAEvenVOA` is **false** here and the even part cannot
  be formed as a bosonic VOA at `4 ∣ p`.  §7 records what would be needed for `p ≡ 2 mod 4`.

## What is *not* here

* **`p ≡ 2 mod 4`.**  There the half lattice is odd (`HalfLat.hlatP_not_even_of_not_four_dvd`)
  and the bosonic `YfullGen` does not apply; a genuinely super lattice vertex map with
  Koszul-signed cocycle would be needed, and none exists in this repository.  Nothing here
  pretends otherwise: `4 ∣ p` is a hypothesis of every statement.
* **`A(p)₀̄ ≅ W(p)`.**  Not attempted — it is a research problem.  Matching central charges
  (`doubletApC_centralCharge_eq_tripletW`) is the honest check, and that is all that is
  claimed.
* **Positivity of `A(p)`, and `e^{+g} ∉ A(p)`.**  Both remain reduced-not-proved in
  `DoubletAp` (its gaps 3 and 4); this file changes nothing about them.
-/

set_option linter.style.longLine false

namespace VOA.DoubletC

open scoped BigOperators
open VOA VOA.IntegralLattice
open VOA.LatGen VOA.LatGen.HalfLat

/-! ## §1  The concrete lattice data

`p = 4j` throughout.  The two natural numbers that actually appear are `k = p/2` (the Gram
coefficient, `⟨m,n⟩ = k·m·n`) and `j = p/4` (the half-norm coefficient, `½⟨m,m⟩ = j·m²`);
both are recovered from `h4 : 4 ∣ p` by `omega`, so no separate index variable is carried. -/

/-- The **doublet half lattice** `½ℤγ` at level `p`, from `Examples.DoubletHalfLattice`. -/
noncomputable abbrev latD (p : ℕ) : IntegralLattice := hlatP p

/-- The **doublet generator** `g = γ/2`. -/
noncomputable abbrev gD (p : ℕ) : (latD p).carrier := gHalf p

/-- `p` is even, in the division-free form `Examples.DoubletHalfLattice` wants. -/
theorem hp2D (p : ℕ) (h4 : 4 ∣ p) : 2 * (p / 2) = p := by omega

/-- `p = 4·(p/4)`. -/
theorem hp4D (p : ℕ) (h4 : 4 ∣ p) : 4 * (p / 4) = p := by omega

/-- `4 ∣ p` and `0 < p` force `p ≥ 4`. -/
theorem four_le (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) : 4 ≤ p := by omega

/-- **The half lattice is an even lattice** — this is what makes the *bosonic* vertex map
`YfullGen` applicable, and it is exactly where `4 ∣ p` is used. -/
theorem evenD (p : ℕ) (h4 : 4 ∣ p) : (latD p).Even :=
  hlatP_even_of_four_dvd p h4

/-- The half lattice is positive definite. -/
theorem posDefD (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) : (latD p).PosDef :=
  hlatP_posDef p (by omega)

/-! ### Casting the two natural divisions

`(p/2 : ℕ)` and `(p/4 : ℕ)` are *natural* divisions, so `push_cast` is not allowed to touch
them (it would produce integer division).  These two lemmas convert them once and for all, and
after that every cast in this file is division-free. -/

/-- `(p/2 : ℕ) = p/2` in `ℂ`. -/
theorem cast_half (p : ℕ) (h4 : 4 ∣ p) : (((p / 2 : ℕ)) : ℂ) = (p : ℂ) / 2 := by
  obtain ⟨j, rfl⟩ := h4
  have h : 4 * j / 2 = 2 * j := by omega
  rw [h]
  push_cast
  ring

/-- `(p/4 : ℕ) = p/4` in `ℂ`. -/
theorem cast_quarter (p : ℕ) (h4 : 4 ∣ p) : (((p / 4 : ℕ)) : ℂ) = (p : ℂ) / 4 := by
  obtain ⟨j, rfl⟩ := h4
  have h : 4 * j / 4 = j := by omega
  rw [h]
  push_cast
  ring

/-- `⟨g, m⟩ = (p/2)·m`. -/
theorem form_gD (p : ℕ) (h4 : 4 ∣ p) (m : ℤ) :
    (latD p).form (gD p) m = ((p / 2 : ℕ) : ℤ) * m := by
  have h : (latD p).form (gD p) m = ((p / 2 : ℕ) : ℤ) * (1 : ℤ) * m :=
    hlatP_form_k p (p / 2) (hp2D p h4) (gHalf p) m
  rw [h]; ring

/-- `⟨g, m⟩ = (p/2)·m` in `ℂ`, division-free. -/
theorem cast_form_gD (p : ℕ) (h4 : 4 ∣ p) (m : ℤ) :
    (((latD p).form (gD p) m : ℤ) : ℂ) = (p : ℂ) / 2 * (m : ℂ) := by
  rw [form_gD p h4, Int.cast_mul, Int.cast_natCast, cast_half p h4]

/-- **`2⟨g,g⟩ = p`** — literally the hypothesis `hgg` of `Examples.DoubletGenerators`. -/
theorem hggD (p : ℕ) (h4 : 4 ∣ p) : 2 * (latD p).form (gD p) (gD p) = (p : ℤ) :=
  hgg_hlatP p (p / 2) (hp2D p h4)

/-- The **half-norm** on the half lattice: `½⟨m,m⟩ = (p/4)·m²`.  (Integral precisely because
`4 ∣ p` — this is `evenD` in numerical form.) -/
theorem halfNormD (p : ℕ) (h4 : 4 ∣ p) (m : ℤ) :
    halfNorm (latD p) m = ((p / 4 : ℕ) : ℤ) * m ^ 2 := by
  rw [halfNorm, hlatP_form_k p (p / 2) (hp2D p h4)]
  have hk : ((p / 2 : ℕ) : ℤ) = 2 * ((p / 4 : ℕ) : ℤ) := by
    have hd : p / 2 = 2 * (p / 4) := by omega
    rw [hd]; push_cast; ring
  rw [hk, show (2 * ((p / 4 : ℕ) : ℤ)) * m * m = 2 * (((p / 4 : ℕ) : ℤ) * m ^ 2) from by ring,
    Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]

/-- The half-norm in `ℂ`, division-free. -/
theorem cast_halfNormD (p : ℕ) (h4 : 4 ∣ p) (m : ℤ) :
    ((halfNorm (latD p) m : ℤ) : ℂ) = (p : ℂ) / 4 * (m : ℂ) ^ 2 := by
  rw [halfNormD p h4, Int.cast_mul, Int.cast_natCast, Int.cast_pow, cast_quarter p h4]

/-! ### The quadratic refinement -/

/-- **The ℚ-valued quadratic refinement** `q(m) = p m²/4 − (p−1)m/2` of the half lattice. -/
noncomputable def qrD (p : ℕ) (h4 : 4 ∣ p) : QuadRefine (latD p) :=
  qrH p (p / 2) (hp2D p h4)

@[simp] theorem qrD_q (p : ℕ) (h4 : 4 ∣ p) (m : ℤ) : (qrD p h4).q m = qH p m := rfl

/-- **`QFinite`**: only finitely many charges lie below any given refined weight.  This single
input gives both the finite-dimensionality of the weight spaces and (via
`SAmbB.qFinite_bddBelow`) the lower bound on the grading. -/
theorem qFiniteD (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) : QFinite (latD p) (qrD p h4) :=
  qFinite_qrH p (p / 2) (hp2D p h4) (by omega)

/-! ## §2  The background charge `λ = ((p−1)/p)·g`

Nothing before this file constructed a background charge on `hlatP p`.  It is the
lattice-direction charge `BgA.latBg` in the direction of `g` with coefficient `(p−1)/p`; the
coefficient is fixed by demanding `⟨λ,g⟩ = (p−1)/2`, since `⟨g,g⟩ = p/2`. -/

/-- The background-charge coefficient `c = (p−1)/p`. -/
noncomputable def cD (p : ℕ) : ℂ := ((p : ℂ) - 1) / (p : ℂ)

/-- **The background charge** `λ = ((p−1)/p)·g` of the doublet half lattice. -/
noncomputable def lamD (p : ℕ) : Fin (rank (latD p)) → ℂ :=
  BgA.latBg (latD p) (cD p) (gD p)

/-- **`⟨λ, m g⟩ = (p−1)m/2`** for every point of the half lattice. -/
theorem bgPairD (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) (m : ℤ) :
    BgA.bgPair (latD p) (lamD p) m = ((p : ℂ) - 1) / 2 * (m : ℂ) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [lamD, BgA.bgPair_latBg (latD p) (posDefD p h4 hp), cast_form_gD p h4, cD]
  field_simp

/-- **`⟨λ, g⟩ = (p−1)/2`** — literally the hypothesis `hlam` of
`Examples.DoubletGenerators`, in its `BgB` phrasing. -/
theorem hlamD (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    BgB.bgPair (latD p) (lamD p) (gD p) = ((p : ℂ) - 1) / 2 := by
  have h : BgB.bgPair (latD p) (lamD p) (gD p) = ((p : ℂ) - 1) / 2 * ((1 : ℤ) : ℂ) := by
    rw [SAmbB.bgPair_B_eq_A]
    exact bgPairD p h4 hp (gD p)
  rw [h]
  push_cast
  ring

/-! ## §3  Compatibility of the background charge with the refinement

`⟨λ,β⟩ = ½⟨β,β⟩ − q β`.  With `⟨λ,mg⟩ = (p−1)m/2`, `½⟨mg,mg⟩ = (p/4)m²` and
`q(m) = p m²/4 − (p−1)m/2` this is an identity, and it is the *only* place the two halves of
the construction have to agree. -/

/-- **The background charge and the refinement are compatible.** -/
theorem bgCompatD (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    SAmbB.BgCompat (latD p) (qrD p h4) (lamD p) := by
  intro m
  rw [SAmbB.bgPair_B_eq_A, bgPairD p h4 hp, qrD_q, cast_halfNormD p h4]
  simp only [qH]
  push_cast
  ring

/-! ## §4  The ambient: the `ℂ`-graded super near-VOA on the half lattice -/

/-- **The deformed half-lattice super near-VOA**, `p = 4j`.

Weights live in `½ℤ`: `wt(e^{mg}) = p m²/4 − (p−1)m/2`, a genuine half-integer for odd `m`.  In
particular `wt(e^{−g}) = (3p−2)/4` (the doublet weight) and `wt(e^{+g}) = (2−p)/4 < 0` — which
is why this is a `SuperNearVOA` (no `positivity`, no `vacuum_grade`) and not a
`SuperVertexOperatorAlgebra`. -/
noncomputable def ambientC (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    SuperNearVOA (LatModuleGen (latD p)) :=
  SAmbB.latSNVOA (latD p) (evenD p h4) (posDefD p h4 hp) (qrD p h4) (qFiniteD p h4 hp)
    (lamD p) (bgCompatD p h4 hp)

/-- Its weight grading is the refined one. -/
@[simp] theorem ambientC_grading (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).grading = gradingLatGenQ (latD p) (qrD p h4) := rfl

/-- Its vacuum is the lattice vacuum. -/
@[simp] theorem ambientC_vacuum (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).vacuum = latVacuumGen (latD p) := rfl

/-- Its conformal vector is the deformed one `ω_λ = ω_L + λ(−2)|0⟩`. -/
@[simp] theorem ambientC_conformalVector (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).conformalVector = BgB.omegaBG (latD p) (lamD p) := rfl

/-- **Its Virasoro modes are the background-charge deformed ones** `Lₙ = L^λ_n`, on the
nose. -/
theorem ambientC_L (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) (n : ℤ) :
    (ambientC p h4 hp).L n = BgB.LBG (latD p) (lamD p) n :=
  SAmbB.latSNVOA_L _ _ _ _ _ _ _ n

/-- **The ambient is bounded below** — from `QFinite` alone. -/
theorem ambientC_boundedBelow (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).BoundedBelow :=
  SAmbB.latSNVOA_boundedBelow _ _ _ _ _ _ _

/-- **`DoubletAp` gap 1, closed at a concrete lattice**: the half-lattice ambient meets the
`DeformedAmbient` interface. -/
noncomputable def deformedAmbientC (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    DoubletAp.DeformedAmbient (latD p) (lamD p) :=
  SAmbB.deformedAmbient (latD p) (evenD p h4) (posDefD p h4 hp) (qrD p h4) (qFiniteD p h4 hp)
    (lamD p) (bgCompatD p h4 hp)

@[simp] theorem deformedAmbientC_W (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (deformedAmbientC p h4 hp).W = ambientC p h4 hp := rfl

/-! ## §5  Targets (c) and (d): the doublet algebra `A(p)` and its `BoundedBelow`

Everything `Examples.DoubletAp` proves for an abstract `DeformedAmbient` applies to a
constructed object.  The two generators are the half-lattice states

  `a⁻ = e^{−g}`,  `a⁺ = Q a⁻`  with  `Q = (e^{2g})₍₀₎`,

both of deformed weight `(3p−2)/4`. -/

/-- The lower doublet generator `a⁻ = e^{−g}`. -/
noncomputable abbrev aMinusC (p : ℕ) : LatModuleGen (latD p) := Doublet.aMinus (latD p) (gD p)

/-- The upper doublet generator `a⁺ = Q a⁻`. -/
noncomputable abbrev aPlusC (p : ℕ) : LatModuleGen (latD p) := Doublet.aPlus (latD p) (gD p)

/-- **The doublet algebra `A(p) = ⟨ω, a⁻, a⁺⟩`**, as a super vertex operator subalgebra of
the concrete deformed half-lattice ambient.  This is `DoubletAp.doubletA` at `am := a⁻`,
`ap := a⁺`, i.e. the *smallest* subalgebra of `ambientC` containing the three generators. -/
noncomputable def doubletApC (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    SuperVOASubalgebra (ambientC p h4 hp) :=
  DoubletAp.doubletAp (deformedAmbientC p h4 hp) (gD p)

theorem doubletApC_def (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    doubletApC p h4 hp
      = DoubletAp.doubletA (ambientC p h4 hp) (aMinusC p) (aPlusC p) := rfl

/-! ### Membership -/

/-- `a⁻ ∈ A(p)`. -/
theorem aMinusC_mem (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    aMinusC p ∈ (doubletApC p h4 hp).carrier :=
  DoubletAp.aMinus_mem_doubletAp (deformedAmbientC p h4 hp) (gD p)

/-- `a⁺ ∈ A(p)`. -/
theorem aPlusC_mem (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    aPlusC p ∈ (doubletApC p h4 hp).carrier :=
  DoubletAp.aPlus_mem_doubletAp (deformedAmbientC p h4 hp) (gD p)

/-- `ω ∈ A(p)`. -/
theorem conformalVectorC_mem (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).conformalVector ∈ (doubletApC p h4 hp).carrier :=
  DoubletAp.conformalVector_mem_doubletAp (deformedAmbientC p h4 hp) (gD p)

/-- `𝟙 ∈ A(p)`. -/
theorem vacuumC_mem (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).vacuum ∈ (doubletApC p h4 hp).carrier :=
  DoubletAp.vacuum_mem_doubletAp (deformedAmbientC p h4 hp) (gD p)

/-! ### The weights, as memberships in the ambient weight spaces

These are the `Examples.DoubletGenerators` computations, transported by
`SuperNearVOA.mem_grading_of_L0_eq` through `ambientC_L`, and they are exactly where `hggD` and
`hlamD` are consumed. -/

/-- **`a⁻` sits at deformed weight `(3p−2)/4`.** -/
theorem aMinusC_mem_grading (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    aMinusC p ∈ (ambientC p h4 hp).grading ((3 * (p : ℂ) - 2) / 4) :=
  DoubletAp.aMinus_mem_grading (deformedAmbientC p h4 hp) (posDefD p h4 hp) (gD p) p
    (hggD p h4) (hlamD p h4 hp)

/-- **`a⁺` sits at the same weight `(3p−2)/4`** (`Q` has weight `0`). -/
theorem aPlusC_mem_grading (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    aPlusC p ∈ (ambientC p h4 hp).grading ((3 * (p : ℂ) - 2) / 4) :=
  DoubletAp.aPlus_mem_grading (deformedAmbientC p h4 hp) (posDefD p h4 hp) (gD p) p
    (hggD p h4) (hlamD p h4 hp)

/-- **`e^{+g}` sits at weight `(2−p)/4 < 0`.** -/
theorem eGC_mem_grading (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    latChargeGen (latD p) (gD p) ∈ (ambientC p h4 hp).grading ((2 - (p : ℂ)) / 4) :=
  DoubletAp.eG_mem_grading (deformedAmbientC p h4 hp) (posDefD p h4 hp) (gD p) p
    (hggD p h4) (hlamD p h4 hp)

/-! ### Non-degeneracy -/

/-- `a⁻ ≠ 0`. -/
theorem aMinusC_ne_zero (p : ℕ) : aMinusC p ≠ 0 := Doublet.aMinus_ne_zero (latD p) (gD p)

/-- `a⁺ ≠ 0` — through `Screen.vSchur_ne_zero`, the Schur-polynomial computation of
`Examples.DoubletGenerators`. -/
theorem aPlusC_ne_zero (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) : aPlusC p ≠ 0 :=
  Doublet.aPlus_ne_zero (latD p) (posDefD p h4 hp) (gD p) p (by omega) (hggD p h4)

/-- `𝟙 ≠ 0`. -/
theorem vacuumC_ne_zero (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) : (ambientC p h4 hp).vacuum ≠ 0 :=
  DoubletAp.vacuum_ne_zero (ambientC p h4 hp) (aMinusC_ne_zero p)

/-- `A(p)` is a **non-trivial** subalgebra. -/
theorem doubletApC_carrier_ne_bot (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (doubletApC p h4 hp).carrier ≠ ⊥ :=
  DoubletAp.doubletAp_carrier_ne_bot (deformedAmbientC p h4 hp) (gD p)

/-! ### Target (d): `BoundedBelow` -/

/-- **Target (d): `A(p)` is bounded below.**

The ambient is bounded below (`ambientC_boundedBelow`, from `QFinite` alone), and
`DoubletAp.subalgebra_boundedBelow` transports that to any subalgebra.  `positivity` could not
have been transported — it is *false* in the ambient (`ambientC_not_positivity` below). -/
theorem doubletApC_boundedBelow (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (doubletApC p h4 hp).toSuperNearVOA.BoundedBelow :=
  DoubletAp.doubletAp_boundedBelow (deformedAmbientC p h4 hp) (gD p)
    (ambientC_boundedBelow p h4 hp)

/-- **The ambient genuinely fails positivity**: `e^{+g}` is a non-zero state of weight
`(2−p)/4 ≤ −1/2 < 0`.  So the passage through `BoundedBelow` is forced, not stylistic. -/
theorem ambientC_not_positivity (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    ¬ (∀ h : ℂ, h.re < 0 → (ambientC p h4 hp).grading h = ⊥) :=
  DoubletAp.ambient_not_positivity (deformedAmbientC p h4 hp) (posDefD p h4 hp) (gD p) p
    (by omega) (hggD p h4) (hlamD p h4 hp)

/-- The weight-`(2−p)/4` space of the ambient is non-zero. -/
theorem ambientC_grading_ne_bot (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).grading ((2 - (p : ℂ)) / 4) ≠ ⊥ :=
  DoubletAp.ambient_grading_ne_bot (deformedAmbientC p h4 hp) (posDefD p h4 hp) (gD p) p
    (hggD p h4) (hlamD p h4 hp)

/-! ## §6  Target (e): the central charge `c = 1 − 6(p−1)²/p`

`c = rank L − 12⟨λ,λ⟩` with `rank = 1` and `⟨λ,λ⟩ = c²⟨g,g⟩ = ((p−1)/p)²·(p/2) = (p−1)²/(2p)`,
computed from `BgA.bgForm_latBg`.  This is the *same* value the triplet algebra `W(p)` carries
— unsurprisingly, since `A(p)` and `W(p)` share the background charge and differ only in which
lattice the charge sits on. -/

/-- `⟨g,g⟩ = p/2` in `ℂ`. -/
theorem cast_form_gD_self (p : ℕ) (h4 : 4 ∣ p) :
    (((latD p).form (gD p) (gD p) : ℤ) : ℂ) = (p : ℂ) / 2 := by
  have h : (((latD p).form (gD p) (gD p) : ℤ) : ℂ) = (p : ℂ) / 2 * ((1 : ℤ) : ℂ) :=
    cast_form_gD p h4 (gD p)
  rw [h]
  push_cast
  ring

/-- **`⟨λ,λ⟩ = (p−1)²/(2p)`.** -/
theorem bgForm_lamD (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    BgA.bgForm (latD p) (lamD p) (lamD p) = ((p : ℂ) - 1) ^ 2 / (2 * (p : ℂ)) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [lamD, BgA.bgForm_latBg (latD p) (posDefD p h4 hp), cast_form_gD_self p h4, cD]
  field_simp

/-- **Target (e): the ambient — hence `A(p)` — has central charge `1 − 6(p−1)²/p`.** -/
theorem ambientC_centralCharge (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).centralCharge = 1 - 6 * ((p : ℂ) - 1) ^ 2 / (p : ℂ) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc : (ambientC p h4 hp).centralCharge
      = ((rank (latD p) : ℂ)) - 12 * BgA.bgForm (latD p) (lamD p) (lamD p) := rfl
  rw [hc, bgForm_lamD p h4 hp, rank_hlatP]
  push_cast
  field_simp
  ring

/-- …i.e. `DoubletAp.centralChargeAp p`, the `(1,p)` value. -/
theorem ambientC_centralCharge_eq_ap (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).centralCharge = DoubletAp.centralChargeAp p :=
  ambientC_centralCharge p h4 hp

/-- `A(p)` inherits it. -/
theorem doubletApC_centralCharge (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (doubletApC p h4 hp).toSuperNearVOA.centralCharge = DoubletAp.centralChargeAp p :=
  ambientC_centralCharge_eq_ap p h4 hp

/-- **Target (g), the honest half.** `A(p)` and the triplet algebra `W(p)` carry the **same
central charge** `1 − 6(p−1)²/p`.

This is a *check*, not an isomorphism.  `A(p)₀̄ ≅ W(p)` is the expected statement and it is a
research problem; nothing in this file, and nothing in this repository, proves it.  What is
recorded here is the one numerical invariant that must match if it is true, and does. -/
theorem doubletApC_centralCharge_eq_tripletW (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (doubletApC p h4 hp).toSuperNearVOA.centralCharge = (Wp.tripletWVOA p hp).centralCharge := by
  rw [doubletApC_centralCharge]
  exact DoubletAp.centralChargeAp_eq_tripletW p hp

/-- The central charge is non-zero for every `p ≥ 4` (indeed `6p² − 13p + 6 = 0` has no natural
root), which is what makes `ω ≠ 0` available. -/
theorem centralChargeAp_ne_zero (p : ℕ) (hp4 : 4 ≤ p) :
    (1 : ℂ) - 6 * ((p : ℂ) - 1) ^ 2 / (p : ℂ) ≠ 0 := by
  intro h
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hz : ((1 : ℂ) - 6 * ((p : ℂ) - 1) ^ 2 / (p : ℂ)) * (p : ℂ)
      = (p : ℂ) - 6 * ((p : ℂ) - 1) ^ 2 := by
    field_simp
  rw [h, zero_mul] at hz
  have hZ : (((p : ℤ) - 6 * ((p : ℤ) - 1) ^ 2 : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination -hz
  have hZ' : (p : ℤ) - 6 * ((p : ℤ) - 1) ^ 2 = 0 := by exact_mod_cast hZ
  have hpZ : (4 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp4
  nlinarith

/-- `ω ≠ 0` in the concrete ambient. -/
theorem conformalVectorC_ne_zero (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).conformalVector ≠ 0 := by
  refine DoubletAp.conformalVector_ne_zero (ambientC p h4 hp) (aMinusC_ne_zero p) ?_
  rw [ambientC_centralCharge p h4 hp]
  exact centralChargeAp_ne_zero p (by omega)

/-! ## §7  Target (f): the even part, and the mod-4 fork

`DoubletAp.doubletAEvenVOA` produces a **bosonic** `VertexOperatorAlgebra` on `A(p)₀̄` from three
hypotheses, the first being integrality: every even state of non-integer weight vanishes.  At
`4 ∣ p` that hypothesis is **false**, and this section proves it rather than asserting it.

The reason is structural and is worth stating plainly.

* This ambient is built on the *bosonic* vertex map `YfullGen`, which needs an **even** lattice.
  The half lattice is even exactly when `4 ∣ p` (`HalfLat.hlatP_even_iff`), so this route is
  confined to `4 ∣ p`, and its `parity` is honestly trivial — every state is even
  (`ambientC_parity_zero`).  Hence `A(p)₀̄ = A(p)` (`doubletApC_parity_zero`).
* But at `4 ∣ p` the doublet weight `(3p−2)/4` is a genuine **half**-integer
  (`doubletWt_not_int`), and `a⁻` is a non-zero state of that weight inside `A(p)`.  So the
  integrality hypothesis fails.

These are not two independent obstructions but one: by `HalfLat.hlatP_even_iff_halfInt` the half
lattice is even **iff** the doublet weight is a half-integer.  Evenness (what the bosonic vertex
map needs) and integrality (what the bosonic even part needs) are *complementary*.  The even part
is expected to exist in the other branch, `p ≡ 2 mod 4`, where `(3p−2)/4` **is** an integer
(`doubletWt_int_of_two_mod_four`) — and there the lattice is odd
(`HalfLat.hlatP_not_even_of_not_four_dvd`), so a genuinely *super* lattice vertex map with a
Koszul-signed cocycle is required.  No such map exists in this repository, so `p ≡ 2 mod 4` is
not reachable here at all, and this file makes no statement about it. -/

/-- The ambient is **purely even**: the trivial parity of `SAmbB.latSVA`. -/
theorem ambientC_parity_zero (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (ambientC p h4 hp).parity 0 = ⊤ :=
  SAmbB.latSVA_parity_zero (latD p) (evenD p h4) (posDefD p h4 hp) (qrD p h4) (qFiniteD p h4 hp)

/-- **`A(p)₀̄ = A(p)`**: since the ambient parity is trivial, so is the induced parity on the
subalgebra.  There is therefore no "even part" to pass to — the even part *is* `A(p)`. -/
theorem doubletApC_parity_zero (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (doubletApC p h4 hp).toSuperNearVOA.parity 0 = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  change x ∈ (doubletApC p h4 hp).parityS 0
  rw [SuperVOASubalgebra.mem_parityS, ambientC_parity_zero p h4 hp]
  exact Submodule.mem_top

/-- At `4 ∣ p` the doublet weight `(3p−2)/4` is **not** an integer: with `p = 4j` it is
`(6j−1)/2`, and `6j−1` is odd. -/
theorem doubletWt_not_int (p : ℕ) (h4 : 4 ∣ p) :
    ¬ ∃ n : ℤ, (n : ℂ) = (3 * (p : ℂ) - 2) / 4 := by
  rintro ⟨n, hn⟩
  obtain ⟨j, rfl⟩ := h4
  have h2 : (2 : ℂ) * (n : ℂ) = 6 * (j : ℂ) - 1 := by
    rw [hn]
    push_cast
    ring
  have hZ : ((2 * n - 6 * (j : ℤ) + 1 : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination h2
  have hZ' : 2 * n - 6 * (j : ℤ) + 1 = 0 := by exact_mod_cast hZ
  omega

/-- The complementary arithmetic fact, for the record: at `p = 4j+2` the doublet weight
`(3p−2)/4 = 3j+1` **is** an integer.  That is the branch in which a bosonic even part could
exist — and the branch this ambient cannot reach, the half lattice there being odd. -/
theorem doubletWt_int_of_two_mod_four (j : ℕ) :
    ((3 * (j : ℤ) + 1 : ℤ) : ℂ) = (3 * ((4 * j + 2 : ℕ) : ℂ) - 2) / 4 := by
  push_cast
  ring

/-- **Target (f), proved as a negative.**  The integrality hypothesis `hint` of
`DoubletAp.doubletAEvenVOA` is **false** for this ambient whenever `4 ∣ p`: `a⁻` is a non-zero
even state of `A(p)` of non-integer weight `(3p−2)/4`.

So `A(p)₀̄` cannot be formed as a bosonic `VertexOperatorAlgebra` by this route at `4 ∣ p`.
This is the expected structural fork, not a failure of the construction: see the section
docstring. -/
theorem hint_false_of_four_dvd (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    ¬ (∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) →
        ∀ x ∈ (doubletApC p h4 hp).toSuperNearVOA.parity 0,
          x ∈ (doubletApC p h4 hp).toSuperNearVOA.grading h → x = 0) := by
  intro hcon
  have hmem : aMinusC p ∈ (doubletApC p h4 hp).carrier := aMinusC_mem p h4 hp
  have hx0 : (⟨aMinusC p, hmem⟩ : (doubletApC p h4 hp).carrier) ≠ 0 := by
    intro hzero
    exact aMinusC_ne_zero p (congrArg Subtype.val hzero)
  refine hx0 (hcon ((3 * (p : ℂ) - 2) / 4) (doubletWt_not_int p h4) _ ?_ ?_)
  · rw [doubletApC_parity_zero p h4 hp]
    exact Submodule.mem_top
  · change (⟨aMinusC p, hmem⟩ : (doubletApC p h4 hp).carrier)
      ∈ (doubletApC p h4 hp).gradingS ((3 * (p : ℂ) - 2) / 4)
    rw [SuperVOASubalgebra.mem_gradingS]
    exact aMinusC_mem_grading p h4 hp

/-- The same statement in positive form: the weight-`(3p−2)/4` space of `A(p)` is non-zero and
sits at a **half-integer** weight. -/
theorem doubletApC_gradingS_ne_bot (p : ℕ) (h4 : 4 ∣ p) (hp : 0 < p) :
    (doubletApC p h4 hp).gradingS ((3 * (p : ℂ) - 2) / 4) ≠ ⊥ := by
  intro hbot
  have hmem : aMinusC p ∈ (doubletApC p h4 hp).carrier := aMinusC_mem p h4 hp
  have hx : (⟨aMinusC p, hmem⟩ : (doubletApC p h4 hp).carrier)
      ∈ (doubletApC p h4 hp).gradingS ((3 * (p : ℂ) - 2) / 4) := by
    rw [SuperVOASubalgebra.mem_gradingS]
    exact aMinusC_mem_grading p h4 hp
  rw [hbot, Submodule.mem_bot] at hx
  exact aMinusC_ne_zero p (congrArg Subtype.val hx)

/-! ## §8  The smallest case, `p = 4` -/

/-- At `p = 4`: `4 ∣ 4` and `0 < 4`, so everything above instantiates. -/
theorem four_dvd_four : (4 : ℕ) ∣ 4 := ⟨1, rfl⟩

/-- The doublet weight at `p = 4` is `5/2`. -/
theorem doubletWt_four : (3 * ((4 : ℕ) : ℂ) - 2) / 4 = 5 / 2 := by norm_num

/-- The weight of `e^{+g}` at `p = 4` is `−1/2`. -/
theorem eGWt_four : (2 - ((4 : ℕ) : ℂ)) / 4 = -(1 / 2) := by norm_num

/-- The central charge at `p = 4` is `−25/2`. -/
theorem centralCharge_four :
    (ambientC 4 four_dvd_four (by norm_num)).centralCharge = -(25 / 2) := by
  rw [ambientC_centralCharge]
  norm_num

end VOA.DoubletC
