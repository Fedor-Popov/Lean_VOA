/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperNearVOA
import VOA.Examples.LatticeQuadRefine
import VOA.Examples.LatticeBackgroundChargeB
import VOA.Examples.TripletLattice
import VOA.Examples.DoubletAp

/-!
# The `ℂ`-graded lattice super near-VOA — route **B** (axioms first)

A `SuperNearVOA` on the lattice module `V_L = FockN(rank L) ⊗ ℂ{L}` whose weight grading is
the **`ℂ`-indexed** refined grading `gradingLatGenQ L qr` of `Examples.LatticeQuadRefine` and
whose conformal vector is the background-charge deformed `BgB.omegaBG L lam`.

This is the object `Examples.DoubletAp` calls for in its gap list: the ambient of the doublet
algebra `A(p)` is a super near-VOA on a lattice module, `ℂ`-graded (so that half-integer — and
in general rational — conformal weights are admissible), with a *deformed* `L₀`, and **bounded
below but not positive**.

## The route

Rather than transporting a bosonic `VertexOperatorAlgebra` along `PreVertexAlgebra.toSuper`, this
file goes through the `SuperVertexAlgebra` axioms **directly**, field by field:

* the parity is trivial (`ParityGrading.even`), so VA4 collapses to ordinary locality by
  `localε_one_iff` and VA1′ is vacuous;
* `Y := YfullGen L hEven hPos`, so VA2/VA3/VA5 (`vacuum_Y`, `creation`, `regularity`) are the
  bosonic proofs **verbatim** — they never mention the grading;
* `isInternal` and `finrank` come from `LatticeQuadRefine` unchanged;
* **VA1 (`grading_mode`) is the one genuinely new obligation** and is proved here for an
  *arbitrary* even positive-definite `L` and an *arbitrary* `QuadRefine` (`YfullGen_gradingQ_mode`).

Nothing is specialized to a rank-one lattice, to a background charge in a lattice direction, or
to a particular `p`.

## Main definitions

* `mem_gradingLatGenQ_of_bigradα` — the membership gate: a bigraded piece of refined weight `k`
  sits in `gradingLatGenQ … k`.
* `YfullGen_gradingQ_mode` — **VA1 for the refined `ℂ`-grading**, for every even
  positive-definite `L` and every `QuadRefine`.
* `latSVA L hEven hPos qr hqf` — the `SuperVertexAlgebra (LatModuleGen L)`.
* `BgCompat L qr lam` — the one-line compatibility `⟨λ,β⟩ = ½⟨β,β⟩ − q β` between the background
  charge and the quadratic refinement.  It is exactly what makes `ω_λ` grade the refinement.
* `latSNVOA L hEven hPos qr hqf lam hcompat` — the `SuperNearVOA (LatModuleGen L)`.
* `bgCompat_of` — the canonical way to produce a `BgCompat`: define `q` *from* `λ`.

## Main results

* `LBG_zero_bigradα`, `LBG_zero_gradingLatGenQ` — the deformed `L₀` acts on the refined weight-`h`
  space by `h`; this is VOA2, and it is where `BgCompat` is used (and the *only* place).
* `omegaBG_mem_bigradα` — `ω_λ ∈ bigradα (2,0)` for any `λ`, hence `ω_λ` has refined weight `2`
  for any refinement (`omegaBG_mem_gradingQ`), because its charge is `0` and `q 0 = 0`.
* `mode_omegaBG_zero_eq` — `L₋₁` is undeformed, so VOA3 is inherited verbatim.
* `qFinite_bddBelow` — `QFinite` alone forces `q` to be **bounded below** (take the finite set
  `{α | q α ≤ 0}`, which is nonempty since `q 0 = 0`, and minimize over it).
* `latSNVOA_boundedBelow` — **the ambient is bounded below**, with the explicit bound coming
  from `qFinite_bddBelow`.  This is the target of `DoubletAp.subalgebra_boundedBelow`.

## What is *not* here

`positivity` is deliberately not attempted: `DoubletAp.ambient_not_positivity` proves it is
**false** for the intended half-lattice at `p > 2`.  `BoundedBelow` is the correct property and
is proved.

All `sorry`-free, axiom-clean.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.SAmbB

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen

variable (L : IntegralLattice)

/-! ## §1  The membership gate for the refined `ℂ`-grading

`gradingLatGenQ L qr k` is the supremum of the bigraded pieces of refined weight `k`.  Two
shapes of that fact are needed: one to *enter* a weight space from a bigraded piece, and one to
run an induction *out* of a weight space. -/

/-- **Entering a refined weight space.**  A bigraded piece `bigradα L P` whose refined weight
`wtQ L qr P` is `k` sits inside `gradingLatGenQ L qr k`. -/
theorem mem_gradingLatGenQ_of_bigradα (qr : QuadRefine L) {k : ℂ} (P : ℤ × L.carrier)
    (hP : wtQ L qr P = k) {x : LatModuleGen L} (hx : x ∈ bigradα L P) :
    x ∈ gradingLatGenQ L qr k := by
  rw [gradingLatGenQ_def]
  exact le_biSup (bigradα L) (show P ∈ (wtQ L qr) ⁻¹' {k} from hP) hx

/-- **Leaving a refined weight space.**  The refined weight-`k` space is the supremum of the
bigraded pieces indexed by the *subtype* of the fibre; this is the shape
`Submodule.iSup_induction` consumes. -/
theorem gradingLatGenQ_eq_iSup_fiber (qr : QuadRefine L) (k : ℂ) :
    gradingLatGenQ L qr k
      = ⨆ P : ((wtQ L qr) ⁻¹' {k} : Set (ℤ × L.carrier)), bigradα L (P : ℤ × L.carrier) := by
  rw [gradingLatGenQ_def, ← iSup_subtype'']

/-! ## §2  VA1 for the refined grading

The refined weight is `w + q β` on the bigraded piece `(w, β)`; the undeformed one is
`w + ½⟨β,β⟩`.  They differ by the **additive** function `β ↦ ½⟨β,β⟩ − q β`
(`QuadRefine.bgCharge_add`), and the `n`-th products add charges
(`YfullGen_shiftsCharge`), so the difference cancels in `h + k − n − 1`.  This is the same
mechanism as `Triplet.gradTrip_grading_mode`, with the integer weight replaced by a rational one
and the `ℤ`-index by the `ℂ`-index. -/

/-- The bigraded arithmetic behind VA1: the refined weight of the bigraded piece produced by an
`n`-th product is the sum of the refined weights, minus `n + 1`. -/
theorem wtQrat_prod (hEven : L.Even) (qr : QuadRefine L) (w w' n : ℤ) (β β' : L.carrier) :
    wtQrat L qr ((w + halfNorm L β) + (w' + halfNorm L β') - n - 1 - halfNorm L (β + β'), β + β')
      = wtQrat L qr (w, β) + wtQrat L qr (w', β') - (n : ℚ) - 1 := by
  have hnadd : halfNorm L (β + β') = halfNorm L β + halfNorm L β' + L.form β β' :=
    halfNorm_add L hEven β β'
  have hpol : qr.q (β + β') - qr.q β - qr.q β' = ((L.form β β' : ℤ) : ℚ) := qr.polarization β β'
  simp only [wtQrat, hnadd]
  push_cast
  linarith

set_option maxHeartbeats 1000000 in
-- the nested `Submodule.iSup_induction` over two `ℂ`-fibres is heavy to elaborate
/-- **VA1 for the refined `ℂ`-grading.**  For every even positive-definite lattice `L` and
every `ℚ`-valued quadratic refinement `q`, the reconstructed lattice vertex map satisfies
`u₍ₙ₎v ∈ 𝒱_{h+k−n−1}` for the refined weight spaces.

No hypothesis on `q` beyond the polarization axiom: no positivity, no finiteness, no
integrality. -/
theorem YfullGen_gradingQ_mode (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    {h k : ℂ} (u : LatModuleGen L) (hu : u ∈ gradingLatGenQ L qr h)
    (v : LatModuleGen L) (hv : v ∈ gradingLatGenQ L qr k) (n : ℤ) :
    mode (YfullGen L hEven hPos u) n v ∈ gradingLatGenQ L qr (h + k - n - 1) := by
  -- the single-piece computation
  have key : ∀ P : ((wtQ L qr) ⁻¹' {h} : Set (ℤ × L.carrier)),
      ∀ u' ∈ bigradα L (P : ℤ × L.carrier),
      ∀ P' : ((wtQ L qr) ⁻¹' {k} : Set (ℤ × L.carrier)),
      ∀ v' ∈ bigradα L (P' : ℤ × L.carrier),
      mode (YfullGen L hEven hPos u') n v' ∈ gradingLatGenQ L qr (h + k - n - 1) := by
    rintro ⟨⟨w, β⟩, hP⟩ u' hu' ⟨⟨w', β'⟩, hP'⟩ v' hv'
    have hPh : wtQ L qr (w, β) = h := hP
    have hPk : wtQ L qr (w', β') = k := hP'
    have hug : u' ∈ gradingLatGen L (w + halfNorm L β) := bigradα_le_gradingLatGen L w β hu'
    have hvg : v' ∈ gradingLatGen L (w' + halfNorm L β') := bigradα_le_gradingLatGen L w' β' hv'
    have huc : u' ∈ chargeSec L β := bigradα_le_chargeSec L w β hu'
    have hvc : v' ∈ chargeSec L β' := bigradα_le_chargeSec L w' β' hv'
    have hmg := YfullGen_grading_mode L hEven hPos u' hug v' hvg n
    have hmc : mode (YfullGen L hEven hPos u') n v' ∈ chargeSec L (β + β') := by
      rw [mode_apply]
      exact YfullGen_shiftsCharge L hEven hPos β huc β' (-n - 1) v' hvc
    have hbig := Triplet.mem_bigradα_of_grading_of_charge L
      ((w + halfNorm L β) + (w' + halfNorm L β') - n - 1) (β + β') hmg hmc
    refine mem_gradingLatGenQ_of_bigradα L qr _ ?_ hbig
    show wtQ L qr ((w + halfNorm L β) + (w' + halfNorm L β') - n - 1 - halfNorm L (β + β'),
      β + β') = h + k - n - 1
    rw [← hPh, ← hPk, wtQ_eq, wtQ_eq, wtQ_eq, wtQrat_prod L hEven qr w w' n β β']
    push_cast
    ring
  rw [gradingLatGenQ_eq_iSup_fiber] at hu hv
  refine Submodule.iSup_induction
    (fun P : ((wtQ L qr) ⁻¹' {h} : Set (ℤ × L.carrier)) => bigradα L (P : ℤ × L.carrier))
    (motive := fun u' => mode (YfullGen L hEven hPos u') n v
      ∈ gradingLatGenQ L qr (h + k - n - 1)) hu ?_ ?_ ?_
  · intro P u' hu'
    refine Submodule.iSup_induction
      (fun P' : ((wtQ L qr) ⁻¹' {k} : Set (ℤ × L.carrier)) => bigradα L (P' : ℤ × L.carrier))
      (motive := fun v' => mode (YfullGen L hEven hPos u') n v'
        ∈ gradingLatGenQ L qr (h + k - n - 1)) hv ?_ ?_ ?_
    · intro P' v' hv'; exact key P u' hu' P' v' hv'
    · simp only [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy; simp only [map_add]; exact Submodule.add_mem _ hx hy
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    simp only [map_add, mode_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy

/-! ## §3  The vacuum sits at refined weight `0`

Hypothesis-free: the vacuum is the bigraded piece `(0,0)` and `q 0 = 0` is a *theorem* about
`QuadRefine` (`QuadRefine.q_zero`), not an assumption.  (`LatticeQuadRefine` states this only
under `PosQuad`, which the doublet ambient does not satisfy.) -/

theorem wtQ_zero_zero (qr : QuadRefine L) : wtQ L qr ((0 : ℤ), (0 : L.carrier)) = 0 := by
  rw [wtQ_eq, wtQrat, qr.q_zero]
  norm_num

/-- **The vacuum has refined weight `0`** — with no hypothesis on `q` whatsoever. -/
theorem latVacuumGen_mem_gradingQ (qr : QuadRefine L) :
    latVacuumGen L ∈ gradingLatGenQ L qr 0 := by
  refine mem_gradingLatGenQ_of_bigradα L qr ((0 : ℤ), (0 : L.carrier)) (wtQ_zero_zero L qr) ?_
  rw [bigradα_zero_zero]
  exact Submodule.mem_span_singleton_self _

/-! ## §4  The `SuperVertexAlgebra`

Parity is trivial (`ParityGrading.even`), so VA1′ (`parity_mode`) is vacuous and VA4
(`locality`) collapses to the bosonic `YfullGen_local` through `localε_one_iff`.  VA2, VA3 and
VA5 are the bosonic proofs verbatim: they do not mention the grading. -/

/-- **The `ℂ`-graded lattice super vertex algebra.**

All five axioms VA1–VA5 on `V_L`, with the weight grading `gradingLatGenQ L qr` — indexed by
`ℂ`, so rational (in particular half-integer) conformal weights are admissible — and trivial
parity.  `hqf : QFinite L qr` is used **only** for the finite-dimensionality of the weight
spaces. -/
noncomputable def latSVA (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) : SuperVertexAlgebra (LatModuleGen L) where
  grading := gradingLatGenQ L qr
  isInternal := gradingLatGenQ_isInternal L qr
  finrank := gradingLatGenQ_finrank L hqf
  parity := (ParityGrading.even (LatModuleGen L)).parity
  parity_isInternal := (ParityGrading.even (LatModuleGen L)).isInternal
  Y := YfullGen L hEven hPos
  vacuum := latVacuumGen L
  vacuum_mem := latVacuumGen_mem_gradingQ L qr
  vacuum_parity := by simp [ParityGrading.even]
  grading_mode := fun u hu v hv n => YfullGen_gradingQ_mode L hEven hPos qr u hu v hv n
  parity_mode := by
    classical
    intro p q u hu v hv n
    by_cases hp : p = 0
    · by_cases hq : q = 0
      · subst hp; subst hq
        simp [ParityGrading.even]
      · rw [ParityGrading.eq_zero_of_mem_even_of_ne hq hv]
        simp only [map_zero]
        exact Submodule.zero_mem _
    · rw [ParityGrading.eq_zero_of_mem_even_of_ne hp hu]
      simp only [map_zero]
      exact Submodule.zero_mem _
  vacuum_Y := YfullGen_vacuum L hEven hPos
  creation := YfullGen_creation L hEven hPos
  locality := by
    classical
    intro p q u hu v hv
    by_cases hp : p = 0
    · by_cases hq : q = 0
      · subst hp; subst hq
        rw [show koszul (0 : ZMod 2) 0 = 1 by simp, localε_one_iff]
        exact YfullGen_local L hEven hPos u v
      · rw [ParityGrading.eq_zero_of_mem_even_of_ne hq hv, map_zero]
        exact localε_zero_right _ _
    · rw [ParityGrading.eq_zero_of_mem_even_of_ne hp hu, map_zero]
      exact localε_zero_left _ _
  regularity := YfullGen_regularity L hEven hPos

@[simp] theorem latSVA_grading (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) : (latSVA L hEven hPos qr hqf).grading = gradingLatGenQ L qr := rfl

@[simp] theorem latSVA_Y (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) : (latSVA L hEven hPos qr hqf).Y = YfullGen L hEven hPos := rfl

@[simp] theorem latSVA_vacuum (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) : (latSVA L hEven hPos qr hqf).vacuum = latVacuumGen L := rfl

/-- The super vertex algebra is **purely even**: every state lies in the even part. -/
theorem latSVA_parity_zero (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) : (latSVA L hEven hPos qr hqf).parity 0 = ⊤ := by
  simp [latSVA, ParityGrading.even]

/-! ## §5  The deformed conformal vector `ω_λ = ω_L + λ(−2)|0⟩`

`ω_λ` is charge-`0` and boson-level-`2`, hence it lies in the bigraded piece `(2,0)` — for
*every* background charge `λ`.  Since `q 0 = 0`, its **refined** weight is `2` for *every*
refinement, with no compatibility hypothesis at all. -/

/-- `ω_λ` written as a single charge-`0` state. -/
theorem omegaBG_eq_mkEα (lam : Fin (rank L) → ℂ) :
    BgB.omegaBG L lam
      = mkEα L 0 (HeisenbergN.ωN (rank L) 1
          + BgB.bgOsc L lam (-2) (HeisenbergN.vacuumN (rank L))) := by
  rw [BgB.omegaBG, BgB.bgState_eq_mkEα, omegaLatGen, map_add]

/-- **`ω_λ ∈ bigradα (2,0)`** for any background charge: both summands are charge-`0` of boson
level `2`. -/
theorem omegaBG_mem_bigradα (lam : Fin (rank L) → ℂ) :
    BgB.omegaBG L lam ∈ bigradα L ((2 : ℤ), (0 : L.carrier)) := by
  have h1 : HeisenbergN.ωN (rank L) 1 ∈ HeisenbergN.gradingZN (rank L) 2 :=
    HeisenbergN.ωN_mem_gradingZN_two (rank L) 1
  have h2 : BgB.bgOsc L lam (-2) (HeisenbergN.vacuumN (rank L))
      ∈ HeisenbergN.gradingZN (rank L) 2 := by
    rw [BgB.bgOsc_apply]
    refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ?_)
    have h := HeisenbergN.oscN_mem_gradingZN (rank L) 1 a (-2)
      (HeisenbergN.vacuumN_mem_gradingWN (rank L))
    rwa [show ((0 : ℕ) : ℤ) - (-2) = 2 from by norm_num] at h
  rw [omegaBG_eq_mkEα, bigradα]
  exact Submodule.mem_map_of_mem (Submodule.add_mem _ h1 h2)

theorem wtQ_two_zero (qr : QuadRefine L) : wtQ L qr ((2 : ℤ), (0 : L.carrier)) = 2 := by
  rw [wtQ_eq, wtQrat, qr.q_zero]
  norm_num

/-- **`ω_λ` has refined weight `2`** — for any refinement and any background charge. -/
theorem omegaBG_mem_gradingQ (qr : QuadRefine L) (lam : Fin (rank L) → ℂ) :
    BgB.omegaBG L lam ∈ gradingLatGenQ L qr 2 :=
  mem_gradingLatGenQ_of_bigradα L qr _ (wtQ_two_zero L qr) (omegaBG_mem_bigradα L lam)

/-! ## §6  The deformed `L₀` grades the refinement — VOA2

This is the **only** place a hypothesis relating the background charge `λ` to the refinement `q`
is used, and it is the obvious one: `⟨λ,β⟩ = ½⟨β,β⟩ − q β`. -/

/-- **The compatibility of a background charge with a quadratic refinement**:
`⟨λ,β⟩ = ½⟨β,β⟩ − q β`, i.e. `q` is the weight assignment that `ω_λ` measures.

Equivalently `q = QuadRefine.bgCharge`-shifted `halfNorm`; `QuadRefine.bgCharge_add` says every
refinement arises this way from *some* additive functional, and `BgCompat` pins that functional
to be `⟨λ,·⟩`. -/
def BgCompat (qr : QuadRefine L) (lam : Fin (rank L) → ℂ) : Prop :=
  ∀ β : L.carrier, BgB.bgPair L lam β = ((halfNorm L β : ℤ) : ℂ) - ((qr.q β : ℚ) : ℂ)

/-- **The deformed `L₀` on a bigraded piece**: `L₀^λ = w + ½⟨β,β⟩ − ⟨λ,β⟩` on `bigradα (w,β)`.

No compatibility hypothesis yet — this is the raw computation, `LLGen` giving `w + ½⟨β,β⟩`
(`sugFieldGen_neg_two_bigradα`) and `λ(0)` giving the momentum `⟨λ,β⟩` (`BgB.bgMode_mkEα`). -/
theorem LBG_zero_bigradα (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ)
    (w : ℤ) (β : L.carrier) {x : LatModuleGen L} (hx : x ∈ bigradα L (w, β)) :
    BgB.LBG L lam 0 x
      = ((w : ℂ) + ((halfNorm L β : ℤ) : ℂ) - BgB.bgPair L lam β) • x := by
  obtain ⟨q, hq, rfl⟩ := hx
  by_cases hw : 0 ≤ w
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, w = (m : ℤ) := ⟨w.toNat, by omega⟩
    subst hm
    have hqW : q ∈ HeisenbergN.gradingWN (rank L) m := by
      rw [HeisenbergN.gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hq
      exact hq
    have hLL : LLGen L 0 = sugFieldGen L (-2) := by rw [LLGen]; norm_num
    have h1 : LLGen L 0 (mkEα L β q) = (((m : ℤ) + halfNorm L β : ℤ) : ℂ) • mkEα L β q := by
      rw [hLL]
      exact sugFieldGen_neg_two_bigradα L hEven hPos hqW
    have h2 : BgB.bgMode L lam 0 (mkEα L β q) = BgB.bgPair L lam β • mkEα L β q := by
      rw [BgB.bgMode_mkEα, BgB.bgFock]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, BgB.bgOsc_zero_mode, zero_add,
        map_smul]
      simp
    rw [BgB.LBG, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2]
    push_cast
    module
  · have hq0 : q = 0 := by
      rw [HeisenbergN.gradingZN_of_neg (by omega : w < 0)] at hq
      simpa using hq
    rw [hq0, map_zero, map_zero, smul_zero]

/-- **VOA2 for the deformed conformal vector**: `L₀^λ` acts on the refined weight-`h` space by
the scalar `h`.  This is where — and the only place where — `BgCompat` enters. -/
theorem LBG_zero_gradingLatGenQ (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) {h : ℂ} {x : LatModuleGen L}
    (hx : x ∈ gradingLatGenQ L qr h) : BgB.LBG L lam 0 x = h • x := by
  rw [gradingLatGenQ_eq_iSup_fiber] at hx
  refine Submodule.iSup_induction
    (fun P : ((wtQ L qr) ⁻¹' {h} : Set (ℤ × L.carrier)) => bigradα L (P : ℤ × L.carrier))
    (motive := fun y => BgB.LBG L lam 0 y = h • y) hx ?_ ?_ ?_
  · rintro ⟨⟨w, β⟩, hP⟩ y hy
    rw [LBG_zero_bigradα L hEven hPos lam w β hy]
    congr 1
    have hPh : wtQ L qr (w, β) = h := hP
    rw [← hPh, wtQ_eq, wtQrat, hcompat β]
    push_cast
    ring
  · simp only [map_zero, smul_zero]
  · intro y z hy hz
    simp only [map_add]
    rw [hy, hz, smul_add]

/-- VOA2 in the shape the structure field wants. -/
theorem L0_gradingQ (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) {h : ℂ} (v : LatModuleGen L)
    (hv : v ∈ gradingLatGenQ L qr h) :
    mode (YfullGen L hEven hPos (BgB.omegaBG L lam)) 1 v = h • v := by
  have hm := BgB.mode_YfullGen_omegaBG L hEven hPos lam 0
  rw [show (0 : ℤ) + 1 = 1 from by ring] at hm
  rw [hm]
  exact LBG_zero_gradingLatGenQ L hEven hPos qr lam hcompat hv

/-! ## §7  VOA1 and VOA3

VOA1 is `BgB.YfullGen_omegaBG_virasoro` with the `if` pushed through the scalar action.  VOA3 is
inherited **verbatim** from the undeformed lattice VOA, because the deformation
`Lₙ ↦ Lₙ − (n+1)λ(n)` vanishes at `n = −1`. -/

/-- **VOA1 for `ω_λ`**, central charge `rank L − 12⟨λ,λ⟩`. -/
theorem virasoroQ (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) (m n : ℤ) :
    ⁅mode (YfullGen L hEven hPos (BgB.omegaBG L lam)) (m + 1),
      mode (YfullGen L hEven hPos (BgB.omegaBG L lam)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (YfullGen L hEven hPos (BgB.omegaBG L lam)) (m + n + 1)
        + (if m + n = 0
           then (((m : ℂ) ^ 3 - m) / 12 * BgB.bgCentralCharge L lam)
                  • (1 : End ℂ (LatModuleGen L))
           else 0) := by
  rw [BgB.YfullGen_omegaBG_virasoro L hEven hPos lam m n]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
  · rw [if_neg hmn, if_neg hmn, zero_smul]

/-- **`L₋₁` is undeformed**: the correction `−(n+1)λ(n)` vanishes at `n = −1`. -/
theorem mode_omegaBG_zero_eq (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ) :
    mode (YfullGen L hEven hPos (BgB.omegaBG L lam)) 0
      = mode (YfullGen L hEven hPos (omegaLatGen L)) 0 := by
  have h1 := BgB.mode_YfullGen_omegaBG L hEven hPos lam (-1)
  have h2 := mode_YfullGen_omega_eq_LLGen L hEven hPos (-1)
  rw [show (-1 : ℤ) + 1 = 0 from by ring] at h1 h2
  rw [h1, h2, BgB.LBG, show (((-1 : ℤ) : ℂ) + 1) = 0 from by norm_num, zero_smul, sub_zero]

/-- **VOA3 for `ω_λ`** — the undeformed translation axiom, verbatim. -/
theorem translationQ (hEven : L.Even) (hPos : L.PosDef) (lam : Fin (rank L) → ℂ)
    (v : LatModuleGen L) :
    YfullGen L hEven hPos (mode (YfullGen L hEven hPos (BgB.omegaBG L lam)) 0 v)
      = VOA.deriv (YfullGen L hEven hPos v) := by
  rw [mode_omegaBG_zero_eq]
  exact YfullGen_translation_omega L hEven hPos v

/-! ## §8  The `SuperNearVOA` -/

/-- **The `ℂ`-graded lattice super near-VOA with background charge.**

The full conformal layer VOA1–VOA3 on top of `latSVA`: conformal vector
`ω_λ = ω_L + λ(−2)|0⟩`, central charge `rank L − 12⟨λ,λ⟩`, and the weight grading
`gradingLatGenQ L qr` — *provided* `λ` and `q` are compatible, `⟨λ,β⟩ = ½⟨β,β⟩ − q β`.

The two CFT-type conditions are **deliberately absent**: `vacuum_grade` and `positivity` are
false in general here (`DoubletAp.ambient_not_positivity`), which is precisely why
`Core.SuperNearVOA` exists.  What *is* available is `latSNVOA_boundedBelow`. -/
noncomputable def latSNVOA (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) :
    SuperNearVOA (LatModuleGen L) where
  __ := latSVA L hEven hPos qr hqf
  conformalVector := BgB.omegaBG L lam
  conformal_mem := omegaBG_mem_gradingQ L qr lam
  conformal_parity := by simp [latSVA, ParityGrading.even]
  centralCharge := BgB.bgCentralCharge L lam
  virasoro := virasoroQ L hEven hPos lam
  L0_grading := fun v hv => L0_gradingQ L hEven hPos qr lam hcompat v hv
  translation := translationQ L hEven hPos lam

@[simp] theorem latSNVOA_grading (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) :
    (latSNVOA L hEven hPos qr hqf lam hcompat).grading = gradingLatGenQ L qr := rfl

@[simp] theorem latSNVOA_centralCharge (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) :
    (latSNVOA L hEven hPos qr hqf lam hcompat).centralCharge = BgB.bgCentralCharge L lam := rfl

@[simp] theorem latSNVOA_conformalVector (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) :
    (latSNVOA L hEven hPos qr hqf lam hcompat).conformalVector = BgB.omegaBG L lam := rfl

@[simp] theorem latSNVOA_vacuum (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) :
    (latSNVOA L hEven hPos qr hqf lam hcompat).vacuum = latVacuumGen L := rfl

/-- **The Virasoro modes of the instance are the deformed ones**, `Lₙ = L^λ_n`.  This is the
identification `DoubletAp.DeformedAmbient` asks for at `n = 0`. -/
theorem latSNVOA_L (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) (n : ℤ) :
    (latSNVOA L hEven hPos qr hqf lam hcompat).L n = BgB.LBG L lam n :=
  BgB.mode_YfullGen_omegaBG L hEven hPos lam n

/-! ## §9  Bounded below

`QFinite` alone forces the refined weights to be bounded below: the set `{α | q α ≤ 0}` is
finite and contains `0` (because `q 0 = 0`), so `q` attains a minimum over it, and off it `q` is
positive.  Combined with the vanishing of `bigradα (w,β)` for `w < 0`, this bounds the whole
refined grading.

**`positivity` is not claimed** — for the doublet ambient it is false.  This is the property that
survives, and `DoubletAp.subalgebra_boundedBelow` transports it to `A(p)`. -/

/-- **`QFinite` implies `q` is bounded below.**  (`{α | q α ≤ 0}` is finite and nonempty.) -/
theorem qFinite_bddBelow {qr : QuadRefine L} (hqf : QFinite L qr) :
    ∃ B : ℚ, ∀ α : L.carrier, B ≤ qr.q α := by
  classical
  obtain ⟨B, hB⟩ := (Set.Finite.image qr.q (hqf 0)).bddBelow
  refine ⟨min B 0, fun α => ?_⟩
  by_cases hα : qr.q α ≤ 0
  · exact le_trans (min_le_left _ _) (hB ⟨α, hα, rfl⟩)
  · exact le_trans (min_le_right _ _) (le_of_lt (not_le.mp hα))

/-- **The refined grading is bounded below**, given `QFinite`.  The bound is the lower bound
of `q` from `qFinite_bddBelow`; no positivity is needed, and none is claimed. -/
theorem gradingLatGenQ_boundedBelow {qr : QuadRefine L} (hqf : QFinite L qr) :
    ∃ B : ℝ, ∀ h : ℂ, h.re < B → gradingLatGenQ L qr h = ⊥ := by
  obtain ⟨Bq, hBq⟩ := qFinite_bddBelow L hqf
  refine ⟨((Bq : ℚ) : ℝ), fun h hh => ?_⟩
  rw [gradingLatGenQ_def]
  refine le_bot_iff.mp (iSup_le fun P => iSup_le fun hP => ?_)
  obtain ⟨w, β⟩ := P
  have hw : wtQ L qr (w, β) = h := hP
  have hre : (w : ℝ) + ((qr.q β : ℚ) : ℝ) = h.re := by rw [← hw, wtQ_re]
  have hb : ((Bq : ℚ) : ℝ) ≤ ((qr.q β : ℚ) : ℝ) := by exact_mod_cast hBq β
  have hwR : (w : ℝ) < 0 := by linarith
  have hwZ : w < 0 := by exact_mod_cast hwR
  rw [bigradα_eq_bot_of_neg L β hwZ]

/-- **The ambient super near-VOA is bounded below.**  This is the hypothesis of
`DoubletAp.subalgebra_boundedBelow`, and hence the property `A(p)` inherits. -/
theorem latSNVOA_boundedBelow (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) :
    (latSNVOA L hEven hPos qr hqf lam hcompat).BoundedBelow :=
  gradingLatGenQ_boundedBelow L hqf

/-! ## §10  Producing a `BgCompat`

The compatibility is not a constraint on `λ` so much as a *definition* of `q` from `λ`: given
any background charge whose pairing `½⟨β,β⟩ − ⟨λ,β⟩` happens to be rational, that formula **is**
a quadratic refinement, and it is compatible by construction. -/

/-- **The refinement defined by a background charge.**  Given a `ℚ`-valued `q` that computes
`½⟨β,β⟩ − ⟨λ,β⟩` in `ℂ`, the polarization axiom is automatic (`halfNorm` polarizes to the form
and `⟨λ,·⟩` is additive), and the result is compatible with `λ` by construction. -/
theorem bgCompat_of (qr : QuadRefine L) (lam : Fin (rank L) → ℂ)
    (h : ∀ β : L.carrier, ((qr.q β : ℚ) : ℂ)
      = ((halfNorm L β : ℤ) : ℂ) - BgB.bgPair L lam β) : BgCompat L qr lam := by
  intro β
  rw [h β]
  ring

/-! ## §11  The `DoubletAp` interface is met

`Examples.DoubletAp` lists as its **gap 1** the absence of any `DeformedAmbient L lam` — "a
`SuperNearVOA` structure on `LatModuleGen L` whose `L₀` is `BgB.LBG L lam 0`".  `latSNVOA` is
exactly that, and its `L₀` is `BgB.LBG L lam 0` on the nose (`latSNVOA_L`).  Gap 2 — the
`BoundedBelow` hypothesis of `DoubletAp.subalgebra_boundedBelow` — is `latSNVOA_boundedBelow`.

What is still missing for the doublet is *arithmetic*, not structure: a concrete `L` (the half
lattice `½ℤγ` as an `IntegralLattice`), a `QuadRefine` on it, and the verification of `QFinite`
and `BgCompat` at that lattice.  Everything below is universally quantified over those data. -/

/-- **The interface of `DoubletAp` is met**: `latSNVOA` is a `DeformedAmbient L lam`.

This closes `DoubletAp`'s gap 1 at the level of *structure*: every theorem of `DoubletAp` §4
(weight memberships, non-degeneracy, `ambient_not_positivity`, the sandwich reductions,
`doubletAp_boundedBelow`) applies to a constructed object rather than to a hypothetical
one. -/
noncomputable def deformedAmbient (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) :
    DoubletAp.DeformedAmbient L lam where
  W := latSNVOA L hEven hPos qr hqf lam hcompat
  L0_eq := latSNVOA_L L hEven hPos qr hqf lam hcompat 0

@[simp] theorem deformedAmbient_W (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) :
    (deformedAmbient L hEven hPos qr hqf lam hcompat).W
      = latSNVOA L hEven hPos qr hqf lam hcompat := rfl

/-- **`DoubletAp`'s gap 2 is closed**: the constructed ambient is bounded below. -/
theorem deformedAmbient_boundedBelow (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam) :
    (deformedAmbient L hEven hPos qr hqf lam hcompat).W.BoundedBelow :=
  latSNVOA_boundedBelow L hEven hPos qr hqf lam hcompat

/-- **The doublet algebra `A(p)` inside this ambient is bounded below** — the target of
`DoubletAp.subalgebra_boundedBelow`, with the ambient actually constructed. -/
theorem doubletAp_boundedBelow_of_qFinite (hEven : L.Even) (hPos : L.PosDef)
    (qr : QuadRefine L) (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ)
    (hcompat : BgCompat L qr lam) (g : L.carrier) :
    SuperNearVOA.BoundedBelow
      (DoubletAp.doubletAp (deformedAmbient L hEven hPos qr hqf lam hcompat) g).toSuperNearVOA :=
  DoubletAp.doubletAp_boundedBelow _ g (deformedAmbient_boundedBelow L hEven hPos qr hqf lam hcompat)

/-- **The constructed ambient really does fail positivity** for `p > 2`, so the passage through
`BoundedBelow` was forced.  (`DoubletAp.ambient_not_positivity`, applied to `latSNVOA`.) -/
theorem deformedAmbient_not_positivity (hEven : L.Even) (hPos : L.PosDef) (qr : QuadRefine L)
    (hqf : QFinite L qr) (lam : Fin (rank L) → ℂ) (hcompat : BgCompat L qr lam)
    (g : L.carrier) (p : ℕ) (hp : 2 < p) (hgg : 2 * L.form g g = (p : ℤ))
    (hlam : BgB.bgPair L lam g = ((p : ℂ) - 1) / 2) :
    ¬ (∀ h : ℂ, h.re < 0 →
        (deformedAmbient L hEven hPos qr hqf lam hcompat).W.grading h = ⊥) :=
  DoubletAp.ambient_not_positivity _ hPos g p hp hgg hlam

/-! ## §12  Non-vacuity: the construction at the triplet lattice

`latSNVOA` and `deformedAmbient` are universally quantified, so it must be checked that their
hypotheses are jointly satisfiable at all.  They are: the rank-one triplet lattice
`L_p = ℤα`, `⟨α,α⟩ = 2p`, with the Feigin–Fuchs background charge `λ_p` and its refinement
`q_p` (`Examples.TripletLattice`) satisfies `Even`, `PosDef`, `QFinite` and `BgCompat`.

This is **not** the doublet half-lattice — that is `½ℤγ`, and for `p ≡ 2 mod 4` it is not even
(`LatGen.Doublet.form_gg_even_iff`), so the *bosonic* `YfullGen` this file is built on does not
apply to it.  What is checked here is that the interface has models; the doublet instantiation
needs the genuinely super lattice vertex map, which is beyond this file. -/

/-- The two background pairings of `BgA` and `BgB` are the same function. -/
theorem bgPair_B_eq_A (lam : Fin (rank L) → ℂ) (β : L.carrier) :
    BgB.bgPair L lam β = BgA.bgPair L lam β := rfl

/-- The Feigin–Fuchs background charge `λ_p` is compatible with the refinement `q_p`. -/
theorem bgCompat_latP (p : ℕ) (hp : 1 ≤ p) :
    BgCompat (Triplet.latP p) (Triplet.qrP p) (Triplet.lamP p) := by
  intro m
  rw [bgPair_B_eq_A, Triplet.bgPair_lamP_eq p hp m]
  simp only [Triplet.qrP_q]
  push_cast
  ring

/-- **The construction is non-vacuous**: the deformed rank-one lattice algebra `V_{L_p}^{λ_p}`
read as a `ℂ`-graded super near-VOA. -/
noncomputable def tripletSNVOA (p : ℕ) (hp : 1 ≤ p) :
    SuperNearVOA (LatModuleGen (Triplet.latP p)) :=
  latSNVOA (Triplet.latP p) (Triplet.latP_even p) (Triplet.latP_posDef p hp)
    (Triplet.qrP p) (Triplet.qFinite_qrP p hp) (Triplet.lamP p) (bgCompat_latP p hp)

/-- Its central charge is the `(1,p)` value `1 − 6(p−1)²/p`. -/
theorem tripletSNVOA_centralCharge (p : ℕ) (hp : 1 ≤ p) :
    (tripletSNVOA p hp).centralCharge = 1 - 6 * ((p : ℂ) - 1) ^ 2 / (p : ℂ) :=
  Triplet.centralCharge_latP p hp

/-- …which is `DoubletAp.centralChargeAp p`, the central charge `A(p)` is expected to carry. -/
theorem tripletSNVOA_centralCharge_eq_ap (p : ℕ) (hp : 1 ≤ p) :
    (tripletSNVOA p hp).centralCharge = DoubletAp.centralChargeAp p :=
  tripletSNVOA_centralCharge p hp

/-- It is bounded below. -/
theorem tripletSNVOA_boundedBelow (p : ℕ) (hp : 1 ≤ p) : (tripletSNVOA p hp).BoundedBelow :=
  latSNVOA_boundedBelow _ _ _ _ _ _ _

/-- And it is a `DoubletAp.DeformedAmbient`, so the whole of `DoubletAp` applies to it. -/
noncomputable def tripletDeformedAmbient (p : ℕ) (hp : 1 ≤ p) :
    DoubletAp.DeformedAmbient (Triplet.latP p) (Triplet.lamP p) :=
  deformedAmbient (Triplet.latP p) (Triplet.latP_even p) (Triplet.latP_posDef p hp)
    (Triplet.qrP p) (Triplet.qFinite_qrP p hp) (Triplet.lamP p) (bgCompat_latP p hp)

end VOA.LatGen.SAmbB
