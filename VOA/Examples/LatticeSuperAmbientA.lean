/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperNearVOA
import VOA.Examples.TripletLattice
import VOA.Examples.LatticeBackgroundChargeB
import VOA.Examples.DoubletAp

/-!
# Route A — the `ℂ`-graded super near-VOA on a lattice, by transport

The doublet algebra `A(p)` of `Examples.DoubletAp` needs an ambient object that a `ℤ`-graded
bosonic VOA cannot be: its generators have conformal weight `(3p−2)/4`, which is a **half-integer**
exactly when `4 ∣ p`.  This file builds that ambient by **transport**: the vertex map, vacuum,
creation, locality and regularity are taken *unchanged* from the bosonic even-lattice VOA
`LatGen.latticeVOAGen`, only the grading and the conformal vector are replaced.

## The two replacements

* **Grading.**  `LatticeQuadRefine.gradingLatGenQ L qr` — the `ℂ`-indexed regrading of `V_L` by a
  `ℚ`-valued quadratic refinement `q` of the lattice form.  It is `gradeCollapse` of the
  charge/oscillator bigrading `bigradα`, so internality is free (`gradingLatGenQ_isInternal`).
* **Conformal vector.**  `BgA.omegaBg L lam = ω_L + λ(−2)|0⟩`, whose modes are the deformed
  `L^λ_n = L_n − (n+1)λ(n)` and whose central charge is `rank L − 12⟨λ,λ⟩` (`BgA.LBg_virasoro`).

The two are tied together by one hypothesis, `BgCompat L lam qr`:

  `⟨λ, β⟩ = ½⟨β,β⟩ − q β`   for every `β ∈ L`,

i.e. the refined weight of `e^β` *is* its deformed conformal weight.  Since `⟨λ,·⟩` is linear and
`½⟨·,·⟩` polarizes to the form, this is a single linear condition; its content is that `⟨λ,·⟩` takes
**rational** values on `L`, which is what a `ℚ`-valued `QuadRefine` can record.

## Main definitions

* `parTriv` — the purely even parity axis, with `parTriv_isInternal`, `parTriv_mode` (VA1′) and
  `parTriv_locality` (VA4: at trivial parity `koszul = 1`, so `Localε 1 = Local`).
* `BgCompat L lam qr` — the compatibility hypothesis above.
* `latticeSuperNearVOA L hEven hPos lam qr hc hqf : SuperNearVOA (LatModuleGen L)` — **the
  general transport theorem**, all 22 fields, for an arbitrary even positive-definite lattice, an
  arbitrary background charge and an arbitrary compatible refinement.
* `BoundedQuad` and `latticeSuperNearVOA_boundedBelow` — the property that survives where
  `positivity` cannot.
* `Half.halfSuperNearVOA r hr` — the instance on the **half lattice** `½ℤγ` at `p = 4r`.
* `Half.halfDeformedAmbient r hr : DoubletAp.DeformedAmbient (latP r) (lamHalf r)`.

## Main results

* `gradingLatGenQ_grading_mode` — **VA1 for the refined `ℂ`-grading.**  The heart of the file.
  The refined weight differs from the undeformed one by `−⟨λ, charge⟩`, an additive function of the
  charge; charge is additive under the `n`-th products (`YfullGen_shiftsCharge`), so the correction
  cancels and the axiom reduces to the undeformed `YfullGen_grading_mode` plus the
  `(weight, charge)` intersection lemma `Triplet.mem_bigradα_of_grading_of_charge`.
* `LBg_zero_gradingLatGenQ` — VOA2: the deformed `L₀` acts on the refined weight-`k` space by `k`.
* `latChargeGen_mem_gradingLatGenQ` — `e^β` sits at refined weight `q β`; for the half lattice
  this is a genuine **half-integer**, the statement a `ℤ`-graded VOA cannot make.
* `LBg_eq_LBG`, `omegaBg_eq_omegaBG` — the `BgA`/`BgB` bridge (`Examples.TripletLattice` speaks
  `BgA`, `Examples.DoubletGenerators`/`Examples.DoubletAp` speak `BgB`; they are the same objects).
* `latticeSuperNearVOA_L_eq_LBG` — the instance's `L₀` is `BgB.LBG L lam 0`, exactly the shape
  `DoubletAp.DeformedAmbient` demands.
* `Half.halfDeformedAmbient` — **gap 1 of `Examples.DoubletAp` is closed for every `p = 4r`.**
  Consequences instantiated in §10: `Half.doubletHalf` (the algebra `A(4r)`),
  `Half.doubletHalf_boundedBelow`, `Half.aMinus_mem_grading_half` and `Half.aPlus_mem_grading_half`
  (both generators at weight `(6r−1)/2`), `Half.eG_mem_grading_half` (weight `(1−2r)/2`) and
  `Half.half_ambient_not_positivity` (the ambient really does have a non-zero state of negative
  weight).

## Scope, and what is deliberately **not** here

* **Parity is trivial.**  This route produces a *purely even* `SuperNearVOA` with `ℂ`-valued
  (here: half-integral) weights.  That is the `4 ∣ p` half of the doublet.  The complementary case
  `p ≡ 2 mod 4` is genuinely **super** — the half lattice is odd, `YfullGen` does not apply, and the
  vertex map needs Koszul signs.  Nothing here covers it; `LatGen.Doublet.form_gg_even_iff` is the
  precise dichotomy.
* **No positivity, no `𝒱₀ = ℂ𝟙`.**  Both are false for a genuine background charge
  (`Half.half_ambient_not_positivity` *proves* the first failure), which is exactly why the target
  is `SuperNearVOA` and not `SuperVertexOperatorAlgebra`.  `BoundedBelow` is what is proved instead.
* **`A(p)₀̄ ≅ W(p)` is not attempted** — that is gap 5 of `Examples.DoubletAp` and is untouched.

All `sorry`-free, `admit`-free, `native_decide`-free, and axiom-clean (`propext`,
`Classical.choice`, `Quot.sound` only).
-/

set_option linter.style.longLine false

namespace VOA.LatGen.SAmbA

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen

universe u

/-! ## §0  A `biSup` induction principle -/

/-- Induction over a supremum restricted to a set of indices. -/
theorem biSupInduction {ι : Type*} {M : Type u} [AddCommGroup M] [Module ℂ M]
    (t : ι → Submodule ℂ M) (S : Set ι) {motive : M → Prop} {x : M}
    (hx : x ∈ ⨆ i ∈ S, t i)
    (mem : ∀ i ∈ S, ∀ y ∈ t i, motive y) (zero : motive 0)
    (add : ∀ y z, motive y → motive z → motive (y + z)) : motive x := by
  classical
  rw [iSup_subtype'] at hx
  refine Submodule.iSup_induction (fun i : S => t i) (motive := motive) hx ?_ zero add
  rintro ⟨i, hi⟩ y hy
  exact mem i hi y hy

/-! ## §1  The trivial (purely even) parity axis -/

variable (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The **purely even** parity grading, as the parity axis of a `SuperVertexAlgebra`. -/
def parTriv : ZMod 2 → Submodule ℂ 𝒱 := fun p => if p = 0 then ⊤ else ⊥

@[simp] theorem parTriv_zero : parTriv 𝒱 0 = ⊤ := by rw [parTriv, if_pos rfl]

theorem parTriv_of_ne {p : ZMod 2} (hp : p ≠ 0) : parTriv 𝒱 p = ⊥ := by
  rw [parTriv, if_neg hp]

variable {𝒱}

theorem eq_zero_of_mem_parTriv {p : ZMod 2} (hp : p ≠ 0) {u : 𝒱} (hu : u ∈ parTriv 𝒱 p) :
    u = 0 := by
  rw [parTriv_of_ne 𝒱 hp] at hu
  simpa using hu

theorem mem_parTriv_zero (u : 𝒱) : u ∈ parTriv 𝒱 0 := by
  rw [parTriv_zero]; trivial

variable (𝒱)

/-- The purely even parity grading is an internal direct sum. -/
theorem parTriv_isInternal : DirectSum.IsInternal (parTriv 𝒱) :=
  (ParityGrading.even 𝒱).isInternal

/-! ## §2  A background charge compatible with a quadratic refinement -/

variable (L : IntegralLattice)

/-- **The compatibility of a background charge with a quadratic refinement.**

`q α = ½⟨α,α⟩ − ⟨λ,α⟩`, i.e. the refined weight of the charged vacuum `e^α` is exactly the
`λ`-deformed conformal weight `L^λ₀ e^α`.  Note both sides are additive-up-to-polarization in
`α`, so this is one linear condition, not a family of independent ones; the content is that
`⟨λ,α⟩` is *rational* on the lattice, which is what allows the `ℚ`-valued `QuadRefine` to
record it. -/
def BgCompat (lam : Fin (rank L) → ℂ) (qr : QuadRefine L) : Prop :=
  ∀ β : L.carrier, BgA.bgPair L lam β = ((halfNorm L β : ℤ) : ℂ) - ((qr.q β : ℚ) : ℂ)

variable {L}

/-! ### Membership in the refined grading -/

/-- A bigraded piece sits inside the refined weight space labelled by its refined weight. -/
theorem mem_gradingLatGenQ_of_bigradα (qr : QuadRefine L) (k : ℂ) (p : ℤ × L.carrier)
    (hp : wtQ L qr p = k) {x : LatModuleGen L} (hx : x ∈ bigradα L p) :
    x ∈ gradingLatGenQ L qr k := by
  rw [gradingLatGenQ_def]
  exact le_biSup (bigradα L) (show p ∈ (wtQ L qr) ⁻¹' {k} from hp) hx

/-- The refined weight of the pair `(w, β)`, unfolded. -/
theorem wtQ_pair (qr : QuadRefine L) (w : ℤ) (β : L.carrier) :
    wtQ L qr (w, β) = ((w : ℂ)) + ((qr.q β : ℚ) : ℂ) := by
  rw [wtQ_eq]
  change ((((w : ℤ) : ℚ) + qr.q β : ℚ) : ℂ) = _
  push_cast
  ring

/-! ### The deformed `L₀` acts by the refined weight -/

/-- **The deformed `L₀` acts on the bigraded piece `(w,β)` by the refined weight `w + q β`.** -/
theorem LBg_zero_bigradαQ (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ)
    (qr : QuadRefine L) (hc : BgCompat L lam qr) (w : ℤ) (β : L.carrier)
    {x : LatModuleGen L} (hx : x ∈ bigradα L (w, β)) :
    BgA.LBg L lam 0 x = wtQ L qr (w, β) • x := by
  obtain ⟨q, hq, rfl⟩ := hx
  by_cases hw : 0 ≤ w
  · obtain ⟨m, hmz⟩ : ∃ m : ℕ, w = (m : ℤ) := ⟨w.toNat, by omega⟩
    have hqW : q ∈ HeisenbergN.gradingWN (rank L) m := by
      rw [hmz, HeisenbergN.gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hq
      exact hq
    have hLL : LLGen L 0 = sugFieldGen L (-2) := by rw [LLGen]; norm_num
    have h1 : LLGen L 0 (mkEα L β q) = (((m : ℤ) + halfNorm L β : ℤ) : ℂ) • mkEα L β q := by
      rw [hLL]
      exact sugFieldGen_neg_two_bigradα L hEven hPos hqW
    have h2 : BgA.bgCur L lam 0 (mkEα L β q) = BgA.bgPair L lam β • mkEα L β q := by
      rw [show mkEα L β q = latStateGen L q β from rfl,
        BgA.bgCur_latStateGen, BgA.BetaSec_apply, BgA.bgOsc_zero, LinearMap.zero_apply,
        zero_add, BgA.scMom_zero, latStateGen_smul_boson]
    rw [show BgA.LBg L lam 0 = LLGen L 0 - (((0 : ℤ) : ℂ) + 1) • BgA.bgCur L lam 0 from rfl,
      LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, hc β, smul_smul, ← sub_smul,
      wtQ_pair, hmz]
    congr 1
    push_cast
    ring
  · have hq0 : q = 0 := by
      rw [HeisenbergN.gradingZN_of_neg (by omega : w < 0)] at hq
      simpa using hq
    rw [hq0, map_zero, map_zero, smul_zero]

/-- **The deformed `L₀` acts on the whole refined weight-`k` space by `k`.** -/
theorem LBg_zero_gradingLatGenQ (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ)
    (qr : QuadRefine L) (hc : BgCompat L lam qr) (k : ℂ)
    {x : LatModuleGen L} (hx : x ∈ gradingLatGenQ L qr k) :
    BgA.LBg L lam 0 x = k • x := by
  rw [gradingLatGenQ_def] at hx
  refine biSupInduction (bigradα L) ((wtQ L qr) ⁻¹' {k})
    (motive := fun y => BgA.LBg L lam 0 y = k • y) hx ?_ ?_ ?_
  · intro p hp y hy
    change BgA.LBg L lam 0 y = k • y
    have hpk : wtQ L qr p = k := hp
    have := LBg_zero_bigradαQ hEven hPos lam qr hc p.1 p.2 (by simpa using hy)
    rwa [show (p.1, p.2) = p from rfl, hpk] at this
  · change BgA.LBg L lam 0 0 = k • (0 : LatModuleGen L)
    rw [map_zero, smul_zero]
  · intro y z hy hz
    change BgA.LBg L lam 0 (y + z) = k • (y + z)
    rw [map_add, hy, hz, smul_add]

/-! ## §3  VA1 for the refined `ℂ`-grading -/

/-- The refined weight is additive under polarization: the `(w,β)`-piece and the `(w',β')`-piece
produce, at mode `n`, a piece of refined weight `wtQ(w,β) + wtQ(w',β') − n − 1`. -/
theorem wtQ_mode (qr : QuadRefine L) (w w' : ℤ) (β β' : L.carrier) (n : ℤ) :
    wtQ L qr (w + w' - n - 1 - L.form β β', β + β')
      = wtQ L qr (w, β) + wtQ L qr (w', β') - (n : ℂ) - 1 := by
  have hpol := qr.polarization β β'
  have hq : ((qr.q (β + β') : ℚ) : ℂ)
      = ((qr.q β : ℚ) : ℂ) + ((qr.q β' : ℚ) : ℂ) + ((L.form β β' : ℤ) : ℂ) := by
    have h : qr.q (β + β') = qr.q β + qr.q β' + ((L.form β β' : ℤ) : ℚ) := by linarith
    rw [h]
    push_cast
    ring
  rw [wtQ_pair, wtQ_pair, wtQ_pair, hq]
  push_cast
  ring

/-- **VA1 (`grading_mode`) for the `ℂ`-valued refined grading.**

The refined weight differs from the undeformed lattice weight by `−⟨λ, charge⟩`, an *additive*
function of the charge; since charge is additive under the `n`-th products
(`YfullGen_shiftsCharge`) the correction cancels, and the axiom follows from the undeformed
`YfullGen_grading_mode` together with the `(weight, charge)` intersection lemma. -/
theorem gradingLatGenQ_grading_mode (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    {k l : ℂ} (u : LatModuleGen L) (hu : u ∈ gradingLatGenQ L qr k)
    (v : LatModuleGen L) (hv : v ∈ gradingLatGenQ L qr l) (n : ℤ) :
    mode (YfullGen L hEven hPos u) n v ∈ gradingLatGenQ L qr (k + l - n - 1) := by
  have key : ∀ pu ∈ (wtQ L qr) ⁻¹' {k}, ∀ u' ∈ bigradα L pu,
      ∀ pv ∈ (wtQ L qr) ⁻¹' {l}, ∀ v' ∈ bigradα L pv,
      mode (YfullGen L hEven hPos u') n v' ∈ gradingLatGenQ L qr (k + l - n - 1) := by
    rintro ⟨w, β⟩ hpu u' hu' ⟨w', β'⟩ hpv v' hv'
    have hk : wtQ L qr (w, β) = k := hpu
    have hl : wtQ L qr (w', β') = l := hpv
    have hug := bigradα_le_gradingLatGen L w β hu'
    have hvg := bigradα_le_gradingLatGen L w' β' hv'
    have huc := bigradα_le_chargeSec L w β hu'
    have hvc := bigradα_le_chargeSec L w' β' hv'
    have hmg := YfullGen_grading_mode L hEven hPos u' hug v' hvg n
    have hmc : mode (YfullGen L hEven hPos u') n v' ∈ chargeSec L (β + β') := by
      rw [mode_apply]
      exact YfullGen_shiftsCharge L hEven hPos β huc β' (-n - 1) v' hvc
    have hbig := Triplet.mem_bigradα_of_grading_of_charge L
      ((w + halfNorm L β) + (w' + halfNorm L β') - n - 1) (β + β') hmg hmc
    have hH := halfNorm_add L hEven β β'
    rw [show (w + halfNorm L β) + (w' + halfNorm L β') - n - 1 - halfNorm L (β + β')
        = w + w' - n - 1 - L.form β β' from by omega] at hbig
    refine mem_gradingLatGenQ_of_bigradα qr _ _ ?_ hbig
    rw [wtQ_mode, hk, hl]
  rw [gradingLatGenQ_def] at hu hv
  refine biSupInduction (bigradα L) ((wtQ L qr) ⁻¹' {k})
    (motive := fun y => mode (YfullGen L hEven hPos y) n v
      ∈ gradingLatGenQ L qr (k + l - n - 1)) hu ?_ ?_ ?_
  · intro pu hpu u' hu'
    refine biSupInduction (bigradα L) ((wtQ L qr) ⁻¹' {l})
      (motive := fun y => mode (YfullGen L hEven hPos u') n y
        ∈ gradingLatGenQ L qr (k + l - n - 1)) hv ?_ ?_ ?_
    · intro pv hpv v' hv'
      exact key pu hpu u' hu' pv hpv v' hv'
    · simp only [map_zero]
      exact Submodule.zero_mem _
    · intro y z hy hz
      simp only [map_add]
      exact Submodule.add_mem _ hy hz
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    simp only [map_add, mode_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hy hz

/-! ## §4  The parity axioms at trivial parity

At trivial parity every Koszul sign that can occur with a non-zero state is `1`, so super-VA1′
and super-VA4 collapse to "the mode of the zero state is zero" plus ordinary locality
(`localε_one_iff`). -/

variable {𝒱}

/-- **VA1′ (`parity_mode`) at trivial parity.** -/
theorem parTriv_mode (Y : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧) {p q : ZMod 2} (u : 𝒱)
    (hu : u ∈ parTriv 𝒱 p) (v : 𝒱) (hv : v ∈ parTriv 𝒱 q) (n : ℤ) :
    mode (Y u) n v ∈ parTriv 𝒱 (p + q) := by
  by_cases hpq : p + q = 0
  · rw [hpq, parTriv_zero]
    trivial
  · have hzero : mode (Y u) n v = 0 := by
      by_cases hp : p = 0
      · have hq : q ≠ 0 := by
          intro h
          exact hpq (by rw [hp, h, add_zero])
        rw [eq_zero_of_mem_parTriv hq hv]
        exact map_zero _
      · rw [eq_zero_of_mem_parTriv hp hu, map_zero]
        change (0 : End ℂ 𝒱) v = 0
        rw [LinearMap.zero_apply]
    rw [hzero]
    exact Submodule.zero_mem _

/-- **VA4 (super-locality) at trivial parity** is ordinary locality. -/
theorem parTriv_locality (Y : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧)
    (hloc : ∀ u v : 𝒱, Local (Y u) (Y v)) {p q : ZMod 2} (u : 𝒱) (hu : u ∈ parTriv 𝒱 p)
    (v : 𝒱) (_hv : v ∈ parTriv 𝒱 q) : Localε (koszul p q) (Y u) (Y v) := by
  by_cases hp : p = 0
  · rw [hp, koszul_zero_left]
    exact (localε_one_iff _ _).mpr (hloc u v)
  · rw [eq_zero_of_mem_parTriv hp hu, map_zero]
    exact localε_zero_left _ _

/-! ## §5  The remaining conformal-layer axioms -/

/-- The vacuum sits in refined weight `0` — **no positivity hypothesis**. -/
theorem latVacuumGen_mem_gradingLatGenQ_zero (qr : QuadRefine L) :
    latVacuumGen L ∈ gradingLatGenQ L qr 0 := by
  refine mem_gradingLatGenQ_of_bigradα qr 0 (0, 0) ?_ ?_
  · rw [wtQ_pair, qr.q_zero]
    push_cast
    ring
  · rw [bigradα_zero_zero]
    exact Submodule.mem_span_singleton_self (latVacuumGen L)

/-- The deformed conformal vector sits in refined weight `2` — **for any background charge**. -/
theorem omegaBg_mem_gradingLatGenQ_two (lam : Fin (rank L) → ℂ) (qr : QuadRefine L) :
    BgA.omegaBg L lam ∈ gradingLatGenQ L qr 2 := by
  refine mem_gradingLatGenQ_of_bigradα qr 2 (2, 0) ?_ (Triplet.omegaBg_mem_bigradα L lam)
  rw [wtQ_pair, qr.q_zero]
  push_cast
  ring

/-- The charged vacuum `e^β` sits in bidegree `(0, β)`. -/
theorem latChargeGen_mem_bigradα (β : L.carrier) : latChargeGen L β ∈ bigradα L (0, β) := by
  refine ⟨HeisenbergN.vacuumN (rank L), ?_, rfl⟩
  have h := HeisenbergN.mem_gradingZN_of_gradingWN (HeisenbergN.vacuumN_mem_gradingWN (rank L))
  simpa using h

/-- **`e^β` sits at refined weight `q β`.**  For a refinement with non-integral values this is
a state of *fractional* conformal weight — the statement a `ℤ`-graded VOA cannot make. -/
theorem latChargeGen_mem_gradingLatGenQ (qr : QuadRefine L) (β : L.carrier) :
    latChargeGen L β ∈ gradingLatGenQ L qr (((qr.q β : ℚ) : ℂ)) :=
  mem_gradingLatGenQ_of_bigradα qr _ (0, β)
    (by rw [wtQ_pair]; push_cast; ring) (latChargeGen_mem_bigradα β)

/-- **`L₋₁` is undeformed**: the correction `−(n+1)λ(n)` vanishes at `n = −1`. -/
theorem mode_omegaBg_zero_eq (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) :
    mode (YfullGen L hEven hPos (BgA.omegaBg L lam)) 0
      = mode (YfullGen L hEven hPos (omegaLatGen L)) 0 := by
  have h1 := BgA.mode_YfullGen_omegaBg L hEven hPos lam (-1)
  have h2 := mode_YfullGen_omega_eq_LLGen L hEven hPos (-1)
  rw [show (-1 : ℤ) + 1 = 0 from by ring] at h1 h2
  rw [h1, h2, show BgA.LBg L lam (-1)
      = LLGen L (-1) - ((((-1 : ℤ)) : ℂ) + 1) • BgA.bgCur L lam (-1) from rfl]
  norm_num

/-- **VOA3 for the deformed conformal vector** — inherited verbatim from the undeformed one. -/
theorem translation_bg (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ)
    (v : LatModuleGen L) :
    YfullGen L hEven hPos (mode (YfullGen L hEven hPos (BgA.omegaBg L lam)) 0 v)
      = deriv (YfullGen L hEven hPos v) := by
  rw [mode_omegaBg_zero_eq hEven hPos lam]
  exact YfullGen_translation_omega L hEven hPos v

/-- **VOA1 for the deformed conformal vector**, central charge `rank L − 12⟨λ,λ⟩`. -/
theorem virasoro_bg (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (m n : ℤ) :
    ⁅mode (YfullGen L hEven hPos (BgA.omegaBg L lam)) (m + 1),
      mode (YfullGen L hEven hPos (BgA.omegaBg L lam)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (YfullGen L hEven hPos (BgA.omegaBg L lam)) (m + n + 1)
        + (if m + n = 0
           then (((m : ℂ) ^ 3 - m) / 12 * ((rank L : ℂ) - 12 * BgA.bgForm L lam lam))
                  • (1 : End ℂ (LatModuleGen L))
           else 0) := by
  rw [BgA.mode_YfullGen_omegaBg, BgA.mode_YfullGen_omegaBg,
    show m + n + 1 = (m + n) + 1 from by ring, BgA.mode_YfullGen_omegaBg,
    LieRing.of_associative_ring_bracket]
  exact BgA.LBg_virasoro L hPos lam m n

/-- **VOA2 for the deformed conformal vector**: `L^λ₀` acts on the refined weight-`h` space
by `h`. -/
theorem L0_grading_bg (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ)
    (qr : QuadRefine L) (hc : BgCompat L lam qr) {h : ℂ} (v : LatModuleGen L)
    (hv : v ∈ gradingLatGenQ L qr h) :
    mode (YfullGen L hEven hPos (BgA.omegaBg L lam)) 1 v = h • v := by
  have hm := BgA.mode_YfullGen_omegaBg L hEven hPos lam 0
  rw [show (0 : ℤ) + 1 = 1 from by ring] at hm
  rw [hm]
  exact LBg_zero_gradingLatGenQ hEven hPos lam qr hc h hv

/-! ## §6  The `ℂ`-graded super near-VOA -/

variable (L)

/-- **The background-charge-deformed lattice algebra as a `ℂ`-graded `SuperNearVOA`.**

Data: the *undeformed* vertex map `YfullGen` of the even positive-definite lattice `L`, regraded
by the `ℚ`-valued quadratic refinement `qr` (hence `ℂ`-indexed, and in general **not**
`ℤ`-indexed — this is the point), with the deformed conformal vector `ω_λ = ω_L + λ(−2)|0⟩` and
the **trivial** (purely even) parity axis.

Everything except the conformal layer and the grading is transported unchanged from
`latticeVOAGen`; the grading axioms are §2–§3 and the parity axioms are §4.  No positivity and no
`𝒱₀ = ℂ𝟙` is claimed — for a genuine background charge both are false, which is exactly why the
target is `SuperNearVOA` and not `SuperVertexOperatorAlgebra`. -/
noncomputable def latticeSuperNearVOA (hEven : L.Even) (hPos : L.PosDef)
    (lam : Fin (rank L) → ℂ) (qr : QuadRefine L) (hc : BgCompat L lam qr) (hqf : QFinite L qr) :
    SuperNearVOA (LatModuleGen L) where
  grading := gradingLatGenQ L qr
  isInternal := gradingLatGenQ_isInternal L qr
  finrank := fun h => gradingLatGenQ_finrank L hqf h
  parity := parTriv (LatModuleGen L)
  parity_isInternal := parTriv_isInternal (LatModuleGen L)
  Y := YfullGen L hEven hPos
  vacuum := latVacuumGen L
  vacuum_mem := latVacuumGen_mem_gradingLatGenQ_zero qr
  vacuum_parity := mem_parTriv_zero _
  grading_mode := fun u hu v hv n => gradingLatGenQ_grading_mode hEven hPos qr u hu v hv n
  parity_mode := fun u hu v hv n => parTriv_mode (YfullGen L hEven hPos) u hu v hv n
  vacuum_Y := YfullGen_vacuum L hEven hPos
  creation := YfullGen_creation L hEven hPos
  locality := fun u hu v hv =>
    parTriv_locality (YfullGen L hEven hPos) (YfullGen_local L hEven hPos) u hu v hv
  regularity := YfullGen_regularity L hEven hPos
  conformalVector := BgA.omegaBg L lam
  conformal_mem := omegaBg_mem_gradingLatGenQ_two lam qr
  conformal_parity := mem_parTriv_zero _
  centralCharge := (rank L : ℂ) - 12 * BgA.bgForm L lam lam
  virasoro := virasoro_bg hEven hPos lam
  L0_grading := fun v hv => L0_grading_bg hEven hPos lam qr hc v hv
  translation := translation_bg hEven hPos lam

variable {L}

section Accessors

variable (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (qr : QuadRefine L)
  (hc : BgCompat L lam qr) (hqf : QFinite L qr)

@[simp] theorem latticeSuperNearVOA_grading :
    (latticeSuperNearVOA L hEven hPos lam qr hc hqf).grading = gradingLatGenQ L qr := rfl

@[simp] theorem latticeSuperNearVOA_Y :
    (latticeSuperNearVOA L hEven hPos lam qr hc hqf).Y = YfullGen L hEven hPos := rfl

@[simp] theorem latticeSuperNearVOA_vacuum :
    (latticeSuperNearVOA L hEven hPos lam qr hc hqf).vacuum = latVacuumGen L := rfl

@[simp] theorem latticeSuperNearVOA_conformalVector :
    (latticeSuperNearVOA L hEven hPos lam qr hc hqf).conformalVector = BgA.omegaBg L lam := rfl

@[simp] theorem latticeSuperNearVOA_centralCharge :
    (latticeSuperNearVOA L hEven hPos lam qr hc hqf).centralCharge
      = (rank L : ℂ) - 12 * BgA.bgForm L lam lam := rfl

@[simp] theorem latticeSuperNearVOA_parity :
    (latticeSuperNearVOA L hEven hPos lam qr hc hqf).parity = parTriv (LatModuleGen L) := rfl

/-- The whole algebra is purely even (`Core.SuperEvenPart.PurelyEven` unfolded). -/
theorem latticeSuperNearVOA_parity_zero :
    (latticeSuperNearVOA L hEven hPos lam qr hc hqf).parity 0 = (⊤ : Submodule ℂ (LatModuleGen L)) :=
  parTriv_zero (LatModuleGen L)

/-- **The Virasoro modes of the instance are the background-charge modes** `L^λ_n`. -/
theorem latticeSuperNearVOA_L (n : ℤ) :
    (latticeSuperNearVOA L hEven hPos lam qr hc hqf).L n = BgA.LBg L lam n :=
  BgA.mode_YfullGen_omegaBg L hEven hPos lam n

end Accessors

/-! ## §7  The `BgA` / `BgB` bridge

`Examples.DoubletGenerators` and `Examples.DoubletAp` speak `BgB`; `Examples.TripletLattice`
speaks `BgA`.  The two background-charge layers are the same objects. -/

/-- The two background currents agree. -/
theorem bgCur_eq_bgMode (lam : Fin (rank L) → ℂ) (n : ℤ) :
    BgA.bgCur L lam n = BgB.bgMode L lam n :=
  (BgB.bgMode_eq_sum L lam n).symm

/-- **The two deformed Virasoro mode families agree**: `BgA.LBg = BgB.LBG`. -/
theorem LBg_eq_LBG (lam : Fin (rank L) → ℂ) (n : ℤ) :
    BgA.LBg L lam n = BgB.LBG L lam n := by
  change LLGen L n - ((n : ℂ) + 1) • BgA.bgCur L lam n
      = LLGen L n - ((n : ℂ) + 1) • BgB.bgMode L lam n
  rw [bgCur_eq_bgMode]

/-- **The two deformed conformal vectors agree**: `BgA.omegaBg = BgB.omegaBG`. -/
theorem omegaBg_eq_omegaBG (lam : Fin (rank L) → ℂ) :
    BgA.omegaBg L lam = BgB.omegaBG L lam := by
  change omegaLatGen L + mkEα L 0 (BgA.bgOsc L lam (-2) (HeisenbergN.vacuumN (rank L)))
      = omegaLatGen L + BgB.bgState L lam
  rw [BgB.bgState_eq_mkEα]
  rfl

/-- The two central charges agree. -/
theorem bgForm_eq_bgInner (lam mu : Fin (rank L) → ℂ) :
    BgA.bgForm L lam mu = BgB.bgInner L lam mu := rfl

/-- The two pairings agree. -/
theorem bgPair_eq_bgPair (lam : Fin (rank L) → ℂ) (β : L.carrier) :
    BgA.bgPair L lam β = BgB.bgPair L lam β := rfl

/-- **The instance's `L₀` is the `BgB` deformed `L₀`** — the shape the doublet's
`DoubletAp.DeformedAmbient` interface demands. -/
theorem latticeSuperNearVOA_L_eq_LBG (hEven : L.Even) (hPos : L.PosDef)
    (lam : Fin (rank L) → ℂ) (qr : QuadRefine L) (hc : BgCompat L lam qr) (hqf : QFinite L qr)
    (n : ℤ) :
    (latticeSuperNearVOA L hEven hPos lam qr hc hqf).L n = BgB.LBG L lam n := by
  rw [latticeSuperNearVOA_L, LBg_eq_LBG]

/-! ## §8  Bounded below -/

/-- **`BoundedQuad`** — the refined weight of the charged vacua is bounded below.  This is much
weaker than `PosQuad`, and unlike `PosQuad` it *does* hold for the doublet's half lattice, whose
`e^{+γ/2}` has strictly negative weight. -/
def BoundedQuad (qr : QuadRefine L) : Prop := ∃ B : ℚ, ∀ α : L.carrier, B ≤ qr.q α

/-- Below the bound the refined weight spaces vanish. -/
theorem gradingLatGenQ_eq_bot_of_re_lt {qr : QuadRefine L} {B : ℚ}
    (hb : ∀ α : L.carrier, B ≤ qr.q α) (k : ℂ) (hk : k.re < ((B : ℚ) : ℝ)) :
    gradingLatGenQ L qr k = ⊥ := by
  rw [gradingLatGenQ_def]
  refine le_antisymm (iSup_le fun p => iSup_le fun hp => ?_) bot_le
  obtain ⟨w, β⟩ := p
  have hpk : wtQ L qr (w, β) = k := hp
  have hre : (w : ℝ) + ((qr.q β : ℚ) : ℝ) = k.re := by
    rw [← hpk, wtQ_re]
  have hneg : w < 0 := by
    by_contra hcon
    have hcon' : (0 : ℤ) ≤ w := by omega
    have h1 : (0 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hcon'
    have h2 : ((B : ℚ) : ℝ) ≤ ((qr.q β : ℚ) : ℝ) := by exact_mod_cast hb β
    linarith
  rw [bigradα_eq_bot_of_neg L β hneg]

/-- **The instance is bounded below** whenever the refinement is. -/
theorem latticeSuperNearVOA_boundedBelow (hEven : L.Even) (hPos : L.PosDef)
    (lam : Fin (rank L) → ℂ) (qr : QuadRefine L) (hc : BgCompat L lam qr) (hqf : QFinite L qr)
    (hb : BoundedQuad qr) :
    (latticeSuperNearVOA L hEven hPos lam qr hc hqf).BoundedBelow := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨((B : ℚ) : ℝ), fun k hk => gradingLatGenQ_eq_bot_of_re_lt hB k hk⟩

/-! ## §9  The concrete half lattice `½ℤγ` at `p = 4r`

The doublet's ambient is the **half** lattice `L = ℤg`, `⟨g,g⟩ = p/2`.  For `L` to be an
`IntegralLattice` we need `2 ∣ p`; for `L` to be **even** — which the bosonic `YfullGen` requires —
we need `4 ∣ p` (`LatGen.Doublet.form_gg_even_iff`).  Writing `p = 4r` the half lattice *is*
`Triplet.latP r`: carrier `ℤ`, form `⟨m,n⟩ = 2r·mn`, so `⟨g,g⟩ = 2r = p/2`.

This is exactly the range in which the doublet weight `(3p−2)/4 = (6r−1)/2` is a genuine
**half-integer**, i.e. the range a `ℤ`-graded VOA cannot express and a `ℂ`-graded
`SuperNearVOA` can. -/

namespace Half

open VOA.LatGen.Triplet

variable (r : ℕ)

/-- The **half lattice** `½ℤγ` at `p = 4r`. -/
noncomputable abbrev halfLat : IntegralLattice := latP r

/-- The doublet generator `g = γ/2`, i.e. the generator `1 ∈ ℤ` of the half lattice. -/
def gHalf : (latP r).carrier := (1 : ℤ)

/-- `⟨g,g⟩ = 2r`, i.e. `2⟨g,g⟩ = 4r = p`. -/
theorem two_form_gHalf : 2 * (latP r).form (gHalf r) (gHalf r) = ((4 * r : ℕ) : ℤ) := by
  rw [gHalf, latP_form]
  push_cast
  ring

/-- The background-charge coefficient `c = (4r−1)/(4r) = (p−1)/(2·(p/2))`. -/
noncomputable def cHalf : ℂ := (4 * (r : ℂ) - 1) / (4 * (r : ℂ))

/-- The **background charge** `λ = c·g` of the half lattice. -/
noncomputable def lamHalf : Fin (rank (latP r)) → ℂ := BgA.latBg (latP r) (cHalf r) (gHalf r)

/-- **`⟨λ, g⟩ = (p−1)/2`** with `p = 4r` — the doublet's normalization of the background
charge. -/
theorem bgPair_lamHalf (hr : 1 ≤ r) :
    BgB.bgPair (latP r) (lamHalf r) (gHalf r) = (((4 * r : ℕ) : ℂ) - 1) / 2 := by
  have hr' : ((r : ℂ)) ≠ 0 := by
    have : (0 : ℕ) < r := hr
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega : r ≠ 0)
  rw [← bgPair_eq_bgPair, lamHalf, BgA.bgPair_latBg (latP r) (latP_posDef r hr),
    gHalf, latP_form, cHalf]
  push_cast
  field_simp
  ring

/-- **`⟨λ, mg⟩ = (4r−1)m/2`** for every lattice point. -/
theorem bgPair_lamHalf_apply (hr : 1 ≤ r) (m : ℤ) :
    BgA.bgPair (latP r) (lamHalf r) m = (4 * (r : ℂ) - 1) / 2 * (m : ℂ) := by
  have hr' : ((r : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : r ≠ 0)
  rw [lamHalf, BgA.bgPair_latBg (latP r) (latP_posDef r hr), gHalf, latP_form, cHalf]
  push_cast
  field_simp
  ring

/-! ### The quadratic refinement -/

/-- The **integral doublet weight function** `Q(m) = 2r m² − (4r−1)m = 2·q(m)`. -/
def qZH (m : ℤ) : ℤ := 2 * (r : ℤ) * m ^ 2 - (4 * (r : ℤ) - 1) * m

/-- The **refined weight** `q(m) = ½⟨mg,mg⟩ − ⟨λ,mg⟩ = r m² − (4r−1)m/2`.  It is a
**half-integer**, never an integer for odd `m`: this is the whole point. -/
def qHalfFun (m : ℤ) : ℚ := ((qZH r m : ℤ) : ℚ) / 2

theorem qHalfFun_eq (m : ℤ) :
    qHalfFun r m = (r : ℚ) * (m : ℚ) ^ 2 - (4 * (r : ℚ) - 1) / 2 * (m : ℚ) := by
  rw [qHalfFun, qZH]
  push_cast
  ring

/-- The polarization identity for `q`, over `ℤ`-indexed arguments. -/
theorem qHalfFun_polarization (a b : ℤ) :
    qHalfFun r (a + b) - qHalfFun r a - qHalfFun r b = (((latP r).form a b : ℤ) : ℚ) := by
  rw [latP_form, qHalfFun_eq, qHalfFun_eq, qHalfFun_eq]
  push_cast
  ring

/-- **The quadratic refinement of the half lattice.** -/
noncomputable def qrHalf : QuadRefine (latP r) where
  q := qHalfFun r
  polarization := qHalfFun_polarization r

@[simp] theorem qrHalf_q (m : ℤ) : (qrHalf r).q m = qHalfFun r m := rfl

/-- **The background charge and the refinement are compatible**, pointwise. -/
theorem bgCompat_half_apply (hr : 1 ≤ r) (m : ℤ) :
    BgA.bgPair (latP r) (lamHalf r) m
      = ((halfNorm (latP r) m : ℤ) : ℂ) - ((qHalfFun r m : ℚ) : ℂ) := by
  rw [bgPair_lamHalf_apply r hr, qHalfFun_eq, halfNorm_latP]
  push_cast
  ring

/-- **The background charge and the refinement are compatible.** -/
theorem bgCompat_half (hr : 1 ≤ r) : BgCompat (latP r) (lamHalf r) (qrHalf r) :=
  fun m => bgCompat_half_apply r hr m

/-! ### Properness of the refinement -/

/-- **`2|m| ≤ Q(m) + 2r + 2`** — the deformed weight dominates the charge up to a constant.
(Unlike the triplet's `abs_le_qZP` there is a genuine additive constant: the half lattice has
states of *negative* weight.) -/
theorem two_abs_le_qZH (hr : 1 ≤ r) (m : ℤ) : 2 * |m| ≤ qZH r m + 2 * (r : ℤ) + 2 := by
  have hr' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  rw [qZH]
  by_cases h : 0 ≤ m
  · rw [abs_of_nonneg h]
    have key : 2 * (r : ℤ) * (m - 1) ^ 2 ≥ 2 * (m - 1) ^ 2 := by
      nlinarith [sq_nonneg (m - 1)]
    nlinarith [sq_nonneg (4 * m - 5)]
  · have h' : m < 0 := by omega
    rw [abs_of_neg h']
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ 4 * (r : ℤ) - 3) (by omega : (0 : ℤ) ≤ -m),
      mul_nonneg (by omega : (0 : ℤ) ≤ 2 * (r : ℤ)) (sq_nonneg m)]

/-- **`QFinite`**: only finitely many charges lie below any given refined weight. -/
theorem qFinite_qrHalf (hr : 1 ≤ r) : QFinite (latP r) (qrHalf r) := by
  have h : ∀ N : ℚ, {m : ℤ | qHalfFun r m ≤ N}.Finite := by
    intro N
    refine Set.Finite.subset
      (Set.finite_Icc (-(⌈2 * N⌉ + 2 * (r : ℤ) + 2)) (⌈2 * N⌉ + 2 * (r : ℤ) + 2)) ?_
    intro m hm
    have hmq : qHalfFun r m ≤ N := hm
    have h1 : ((qZH r m : ℤ) : ℚ) ≤ 2 * N := by
      rw [qHalfFun] at hmq
      linarith
    have h2 : ((qZH r m : ℤ) : ℚ) ≤ ((⌈2 * N⌉ : ℤ) : ℚ) := le_trans h1 (Int.le_ceil (2 * N))
    have h3 : qZH r m ≤ ⌈2 * N⌉ := by exact_mod_cast h2
    have h4 := two_abs_le_qZH r hr m
    have habs : (0 : ℤ) ≤ |m| := abs_nonneg m
    have h5 : |m| ≤ ⌈2 * N⌉ + 2 * (r : ℤ) + 2 := by omega
    exact Set.mem_Icc.mpr (abs_le.mp h5)
  exact h

/-- The refined weights are bounded below by `−(r+1)`, pointwise. -/
theorem qHalfFun_lower_bound (hr : 1 ≤ r) (m : ℤ) : -((r : ℚ) + 1) ≤ qHalfFun r m := by
  have h4 := two_abs_le_qZH r hr m
  have habs : (0 : ℤ) ≤ |m| := abs_nonneg m
  have h5 : -(2 * (r : ℤ) + 2) ≤ qZH r m := by omega
  have h6 : ((-(2 * (r : ℤ) + 2) : ℤ) : ℚ) ≤ ((qZH r m : ℤ) : ℚ) := by exact_mod_cast h5
  rw [qHalfFun]
  push_cast at h6 ⊢
  linarith

/-- **`BoundedQuad`**: the refined weights are bounded below by `−(r+1)`.  (`PosQuad` is *false*
here — `q(1) = (1−2r)/2 < 0` for `r ≥ 1`.) -/
theorem boundedQuad_qrHalf (hr : 1 ≤ r) : BoundedQuad (qrHalf r) :=
  ⟨-((r : ℚ) + 1), fun m => qHalfFun_lower_bound r hr m⟩

/-! ### The doublet ambient -/

/-- **The `ℂ`-graded super near-VOA on the half lattice `½ℤγ`, `p = 4r`.**

Weights live in `½ℤ`: `wt(e^{mg}) = r m² − (4r−1)m/2`, which is a half-integer for odd `m`.  In
particular `wt(e^{−g}) = (6r−1)/2 = (3p−2)/4` — the doublet weight — and
`wt(e^{+g}) = (1−2r)/2 = (2−p)/4 < 0`. -/
noncomputable def halfSuperNearVOA (hr : 1 ≤ r) : SuperNearVOA (LatModuleGen (latP r)) :=
  latticeSuperNearVOA (latP r) (latP_even r) (latP_posDef r hr) (lamHalf r) (qrHalf r)
    (bgCompat_half r hr) (qFinite_qrHalf r hr)

/-- The half-lattice ambient is **bounded below** — the property the doublet transports. -/
theorem halfSuperNearVOA_boundedBelow (hr : 1 ≤ r) : (halfSuperNearVOA r hr).BoundedBelow :=
  latticeSuperNearVOA_boundedBelow _ _ _ _ _ _ (boundedQuad_qrHalf r hr)

/-- Its central charge, `c = 1 − 12·⟨λ,λ⟩`. -/
theorem halfSuperNearVOA_centralCharge (hr : 1 ≤ r) :
    (halfSuperNearVOA r hr).centralCharge
      = (rank (latP r) : ℂ) - 12 * BgA.bgForm (latP r) (lamHalf r) (lamHalf r) := rfl

/-- Its Virasoro modes are the deformed ones `L^λ_n`. -/
theorem halfSuperNearVOA_L (hr : 1 ≤ r) (n : ℤ) :
    (halfSuperNearVOA r hr).L n = BgB.LBG (latP r) (lamHalf r) n :=
  latticeSuperNearVOA_L_eq_LBG _ _ _ _ _ _ n

/-- **The half-lattice ambient meets the doublet's `DeformedAmbient` interface.**

This closes gap 1 of `Examples.DoubletAp` for every `p = 4r`, `r ≥ 1`: the doublet algebra
`A(p)`, its `BoundedBelow`, the failure of ambient positivity, and the weight statements of
`Examples.DoubletGenerators` are all instantiated at a concrete lattice. -/
noncomputable def halfDeformedAmbient (hr : 1 ≤ r) :
    VOA.DoubletAp.DeformedAmbient (latP r) (lamHalf r) where
  W := halfSuperNearVOA r hr
  L0_eq := halfSuperNearVOA_L r hr 0

/-! ### §10  The doublet `A(p)` at `p = 4r`, instantiated

Everything `Examples.DoubletAp` states for an abstract `DeformedAmbient` is available at a
concrete lattice.  `p = 4r ≥ 4 > 2`, so the negative-weight state `e^{+g}` is genuinely there. -/

/-- **The doublet algebra `A(4r)`** as a super subalgebra of the half-lattice ambient. -/
noncomputable def doubletHalf (hr : 1 ≤ r) :
    SuperVOASubalgebra (halfSuperNearVOA r hr) :=
  VOA.DoubletAp.doubletAp (halfDeformedAmbient r hr) (gHalf r)

/-- **`A(4r)` is bounded below**, transported from the ambient. -/
theorem doubletHalf_boundedBelow (hr : 1 ≤ r) :
    (doubletHalf r hr).toSuperNearVOA.BoundedBelow :=
  VOA.DoubletAp.doubletAp_boundedBelow (halfDeformedAmbient r hr) (gHalf r)
    (halfSuperNearVOA_boundedBelow r hr)

/-- `A(4r)` is non-trivial. -/
theorem doubletHalf_carrier_ne_bot (hr : 1 ≤ r) : (doubletHalf r hr).carrier ≠ ⊥ :=
  VOA.DoubletAp.doubletAp_carrier_ne_bot (halfDeformedAmbient r hr) (gHalf r)

/-- **`a⁻ = e^{−g}` sits at the doublet weight `(3p−2)/4 = (6r−1)/2`** — a half-integer. -/
theorem aMinus_mem_grading_half (hr : 1 ≤ r) :
    Doublet.aMinus (latP r) (gHalf r)
      ∈ (halfSuperNearVOA r hr).grading ((3 * ((4 * r : ℕ) : ℂ) - 2) / 4) :=
  VOA.DoubletAp.aMinus_mem_grading (halfDeformedAmbient r hr) (latP_posDef r hr)
    (gHalf r) (4 * r) (two_form_gHalf r) (bgPair_lamHalf r hr)

/-- **`a⁺ = Q a⁻` sits at the same weight `(3p−2)/4`.** -/
theorem aPlus_mem_grading_half (hr : 1 ≤ r) :
    Doublet.aPlus (latP r) (gHalf r)
      ∈ (halfSuperNearVOA r hr).grading ((3 * ((4 * r : ℕ) : ℂ) - 2) / 4) :=
  VOA.DoubletAp.aPlus_mem_grading (halfDeformedAmbient r hr) (latP_posDef r hr)
    (gHalf r) (4 * r) (two_form_gHalf r) (bgPair_lamHalf r hr)

/-- The doublet weight in closed form: `(3·4r − 2)/4 = (6r − 1)/2`, a genuine half-integer. -/
theorem doubletWt_half :
    (3 * ((4 * r : ℕ) : ℂ) - 2) / 4 = (6 * (r : ℂ) - 1) / 2 := by
  push_cast
  ring

/-- **`e^{+g}` sits at weight `(2−p)/4 = (1−2r)/2 < 0`.** -/
theorem eG_mem_grading_half (hr : 1 ≤ r) :
    latChargeGen (latP r) (gHalf r)
      ∈ (halfSuperNearVOA r hr).grading ((2 - ((4 * r : ℕ) : ℂ)) / 4) :=
  VOA.DoubletAp.eG_mem_grading (halfDeformedAmbient r hr) (latP_posDef r hr)
    (gHalf r) (4 * r) (two_form_gHalf r) (bgPair_lamHalf r hr)

/-- **The half-lattice ambient genuinely fails positivity**: it carries a non-zero state of
strictly negative conformal weight.  This is what forces `SuperNearVOA` (no `positivity` field)
rather than `SuperVertexOperatorAlgebra`, and `BoundedBelow` as the transported property. -/
theorem half_ambient_not_positivity (hr : 1 ≤ r) :
    ¬ (∀ h : ℂ, h.re < 0 → (halfSuperNearVOA r hr).grading h = ⊥) :=
  VOA.DoubletAp.ambient_not_positivity (halfDeformedAmbient r hr) (latP_posDef r hr)
    (gHalf r) (4 * r) (by omega) (two_form_gHalf r) (bgPair_lamHalf r hr)

/-! ### The smallest case `r = 1`, i.e. `p = 4` -/

/-- At `p = 4` the doublet generators have weight `5/2`. -/
theorem doubletWt_p_four : (3 * ((4 * 1 : ℕ) : ℂ) - 2) / 4 = 5 / 2 := by norm_num

/-- At `p = 4` the ambient state `e^{+g}` has weight `−1/2`. -/
theorem eGWt_p_four : (2 - ((4 * 1 : ℕ) : ℂ)) / 4 = -(1 / 2) := by norm_num

end Half

end VOA.LatGen.SAmbA

