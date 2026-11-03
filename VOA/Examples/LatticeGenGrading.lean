/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenModule
import VOA.Foundations.LatticeFinite

/-!
# L₀-weight grading of the general lattice VOA `V_L = FockN(rank L) ⊗ ℂ{L}`  (FLM Ch. 8)

Generalizing `Examples.LatticeGrading` (`A₁`) to an arbitrary even positive-definite `L`.  The
conformal weight of `p ⊗ e^α` with `p` of boson weight `w` is `w + ½⟨α,α⟩` (`halfNorm α`, an integer
by evenness).  We build the `(ℤ × L.carrier)`-**bigrading** `bigradα (w,α) = (gradingZN (rank L) w).map
(p ↦ p ⊗ e^α)`, prove it is an internal direct sum (`bigradα_isInternal`, finiteness-free, via the
retraction detector `piWNα`), and define the collapsed `L₀`-grading
`gradingLatGen k = ⨆_α bigradα (k − ½⟨α,α⟩, α)`.

**Proved here (all axiom-clean, `pbw`-free, finiteness-free):** `bigradα_isInternal`; `gradingLatGen`;
`gradingLatGen_iSup_eq_top`; `gradingLatGen_positivity`; `gradingLatGen_zero_eq_span_vacuum`.

`gradingLatGen_isInternal`/`gradingLatGen_finrank` take the finiteness of bounded lattice vectors
`BoundedFinite L` as a hypothesis; it is discharged from `hPos` by
`IntegralLattice.boundedFinite` (`Foundations.LatticeFinite`), giving the hypothesis-free
`gradingLatGen_isInternal_of_posDef` and `gradingLatGen_finrank_of_posDef` at the end of the file.
-/

set_option linter.style.longLine false

open scoped BigOperators TensorProduct DirectSum
open VOA VOA.IntegralLattice
open Classical

namespace VOA.LatGen

variable (L : IntegralLattice)

/-! ## Half-norm `½⟨α,α⟩` (integer by evenness; positive off `0` by pos-definiteness) -/

/-- The conformal weight `½⟨α,α⟩` of the charged vacuum `e^α` (integer since `L` is even). -/
noncomputable def halfNorm (α : L.carrier) : ℤ := L.form α α / 2

theorem two_halfNorm (hEven : L.Even) (α : L.carrier) : 2 * halfNorm L α = L.form α α := by
  have := hEven α; simp only [halfNorm]; omega

theorem halfNorm_zero : halfNorm L 0 = 0 := by simp [halfNorm]

theorem form_self_nonneg (hPos : L.PosDef) (α : L.carrier) : 0 ≤ L.form α α := by
  rcases eq_or_ne α 0 with h | h
  · rw [h]; simp
  · exact le_of_lt (hPos α h)

theorem halfNorm_nonneg (hEven : L.Even) (hPos : L.PosDef) (α : L.carrier) : 0 ≤ halfNorm L α := by
  have h2 := two_halfNorm L hEven α
  have hpos := form_self_nonneg L hPos α
  omega

theorem halfNorm_pos (hEven : L.Even) (hPos : L.PosDef) {α : L.carrier} (hα : α ≠ 0) :
    0 < halfNorm L α := by
  have h2 := two_halfNorm L hEven α
  have hpos := hPos α hα
  omega

/-! ## The `(ℤ × L.carrier)`-bigrading -/

/-- The injection `p ↦ p ⊗ e^α` of the boson Fock space into the charge-`α` sector. -/
noncomputable def mkEα (α : L.carrier) : HeisenbergN.FockN (rank L) →ₗ[ℂ] LatModuleGen L :=
  (TensorProduct.mk ℂ (HeisenbergN.FockN (rank L)) (L.carrier →₀ ℂ)).flip (eGen L α)

@[simp] theorem mkEα_apply (α : L.carrier) (p : HeisenbergN.FockN (rank L)) :
    mkEα L α p = p ⊗ₜ[ℂ] eGen L α := rfl

/-- The product `(ℤ × L.carrier)`-bigrading: boson-weight `w` tensored into charge sector `α`. -/
noncomputable def bigradα (wα : ℤ × L.carrier) : Submodule ℂ (LatModuleGen L) :=
  (HeisenbergN.gradingZN (rank L) wα.1).map (mkEα L wα.2)

/-- Charge-`α` coordinate extraction `V_L → FockN`, `p ⊗ e^{α'} ↦ (if α = α' then p else 0)`. -/
noncomputable def coordEα (α : L.carrier) : LatModuleGen L →ₗ[ℂ] HeisenbergN.FockN (rank L) :=
  (TensorProduct.rid ℂ (HeisenbergN.FockN (rank L))).toLinearMap.comp
    (LinearMap.lTensor (HeisenbergN.FockN (rank L)) (Finsupp.lapply α))

theorem coordEα_apply (α α' : L.carrier) (p : HeisenbergN.FockN (rank L)) :
    coordEα L α (p ⊗ₜ[ℂ] eGen L α') = (if α = α' then p else 0) := by
  rw [coordEα, LinearMap.comp_apply, LinearMap.lTensor_tmul]
  show (TensorProduct.rid ℂ (HeisenbergN.FockN (rank L)))
      (p ⊗ₜ[ℂ] (Finsupp.lapply α) (eGen L α')) = _
  rw [eGen, Finsupp.lapply_apply, Finsupp.single_apply]
  by_cases h : α' = α
  · rw [if_pos h, if_pos h.symm, TensorProduct.rid_tmul, one_smul]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), TensorProduct.tmul_zero, map_zero]

/-! ## The boson weight projection (rank `L`) -/

/-- The boson grading internal-decomposition equivalence `(⨁ w, gradingZN (rank L) w) ≃ FockN`. -/
noncomputable def bEquivα :
    (⨁ w : ℤ, (HeisenbergN.gradingZN (rank L) w : Submodule ℂ (HeisenbergN.FockN (rank L))))
      ≃ₗ[ℂ] HeisenbergN.FockN (rank L) :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (HeisenbergN.gradingZN (rank L)))
    (HeisenbergN.gradingZN_isInternal (rank L))

/-- The boson weight-`w` projection. -/
noncomputable def bprojα (w : ℤ) :
    HeisenbergN.FockN (rank L) →ₗ[ℂ] HeisenbergN.FockN (rank L) :=
  (HeisenbergN.gradingZN (rank L) w).subtype.comp
    ((DirectSum.component ℂ ℤ
      (fun w => (HeisenbergN.gradingZN (rank L) w : Submodule ℂ (HeisenbergN.FockN (rank L)))) w).comp
      (bEquivα L).symm.toLinearMap)

theorem bprojα_same {w : ℤ} {p : HeisenbergN.FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) w) : bprojα L w p = p := by
  rw [bprojα, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← DirectSum.apply_eq_component]
  show (((bEquivα L).symm p) w : HeisenbergN.FockN (rank L)) = p
  rw [bEquivα, DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem _ hp]

theorem bprojα_of_ne {w w' : ℤ} (hww : w ≠ w') {p : HeisenbergN.FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) w') : bprojα L w p = 0 := by
  rw [bprojα, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← DirectSum.apply_eq_component]
  show (((bEquivα L).symm p) w : HeisenbergN.FockN (rank L)) = 0
  rw [bEquivα, DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne _ hww.symm hp]
  rfl

/-! ## The retraction detecting `bigradα (w,α)` -/

/-- The detector `V_L → FockN` for the bigraded piece `(w,α)`: extract sector `α`, project to
boson-weight `w`. -/
noncomputable def piWNα (w : ℤ) (α : L.carrier) :
    LatModuleGen L →ₗ[ℂ] HeisenbergN.FockN (rank L) := (bprojα L w).comp (coordEα L α)

theorem piWNα_mkEα (w : ℤ) (α α' : L.carrier) {p : HeisenbergN.FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) w) :
    piWNα L w α (mkEα L α' p) = (if α = α' then p else 0) := by
  rw [piWNα, LinearMap.comp_apply, mkEα_apply, coordEα_apply]
  by_cases h : α = α'
  · rw [if_pos h, bprojα_same L hp]
  · rw [if_neg h, map_zero]

theorem piWNα_bigradα_of_ne (w : ℤ) (α : L.carrier) (w' : ℤ) (α' : L.carrier)
    (hne : (w', α') ≠ (w, α)) : bigradα L (w', α') ≤ LinearMap.ker (piWNα L w α) := by
  rintro x ⟨p, hp, rfl⟩
  rw [LinearMap.mem_ker, piWNα, LinearMap.comp_apply, mkEα_apply, coordEα_apply]
  by_cases hn : α = α'
  · subst hn
    have hww : w ≠ w' := fun h => hne (by rw [h])
    rw [if_pos rfl, bprojα_of_ne L hww hp]
  · rw [if_neg hn, map_zero]

theorem piWNα_section {w : ℤ} {α : L.carrier} {p : HeisenbergN.FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) w) : piWNα L w α (mkEα L α p) = p := by
  rw [piWNα_mkEα L w α α hp, if_pos rfl]

/-! ## `bigradα` is an internal direct sum (finiteness-free) -/

theorem bigradα_iSupIndep : iSupIndep (bigradα L) := by
  rw [iSupIndep_def]
  rintro ⟨w, α⟩
  rw [Submodule.disjoint_def]
  intro x hx hxsup
  obtain ⟨p, hp, hpx⟩ := hx
  have hker : (⨆ j, ⨆ (_ : j ≠ (w, α)), bigradα L j) ≤ LinearMap.ker (piWNα L w α) := by
    refine iSup_le (fun j => iSup_le (fun hj => ?_))
    exact piWNα_bigradα_of_ne L w α j.1 j.2 (by simpa using hj)
  have hxk : piWNα L w α x = 0 := by rw [← LinearMap.mem_ker]; exact hker hxsup
  have hpp : piWNα L w α x = p := by rw [← hpx]; exact piWNα_section L hp
  rw [hpp] at hxk
  rw [← hpx, hxk, map_zero]

theorem mkEα_mem_iSup_bigradα (α : L.carrier) (p : HeisenbergN.FockN (rank L)) :
    mkEα L α p ∈ iSup (bigradα L) := by
  have hmem : mkEα L α p ∈ (⨆ w : ℤ, bigradα L (w, α)) := by
    have hmap : (⨆ w : ℤ, HeisenbergN.gradingZN (rank L) w).map (mkEα L α)
        = ⨆ w : ℤ, bigradα L (w, α) := by rw [Submodule.map_iSup]; rfl
    have hp : p ∈ (⨆ w : ℤ, HeisenbergN.gradingZN (rank L) w) := by
      rw [HeisenbergN.gradingZN_iSup_eq_top (rank L)]; trivial
    have : mkEα L α p ∈ (⨆ w : ℤ, HeisenbergN.gradingZN (rank L) w).map (mkEα L α) :=
      Submodule.mem_map_of_mem hp
    rwa [hmap] at this
  exact (iSup_le (fun w => le_iSup (bigradα L) (w, α))) hmem

theorem bigradα_iSup_eq_top : iSup (bigradα L) = ⊤ := by
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top ℂ (HeisenbergN.FockN (rank L)) (L.carrier →₀ ℂ),
    Submodule.span_le]
  rintro _ ⟨p, g, rfl⟩
  rw [SetLike.mem_coe]
  induction g using Finsupp.induction_linear with
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add g₁ g₂ h₁ h₂ => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h₁ h₂
  | single α c =>
      rw [show (Finsupp.single α c : L.carrier →₀ ℂ) = c • eGen L α from by
            rw [eGen, Finsupp.smul_single, smul_eq_mul, mul_one], TensorProduct.tmul_smul]
      exact Submodule.smul_mem _ c (mkEα_mem_iSup_bigradα L α p)

/-- **The `(ℤ × L.carrier)`-bigrading is an internal direct sum of `V_L`** (finiteness-free). -/
theorem bigradα_isInternal : DirectSum.IsInternal (bigradα L) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (bigradα_iSupIndep L) (bigradα_iSup_eq_top L)

/-! ## The collapsed `L₀`-grading `gradingLatGen` -/

/-- The **`L₀`-weight grading** of `V_L`: the weight-`k` space is `⨆_α bigradα (k − ½⟨α,α⟩, α)`
(the conformal weight of `p ⊗ e^α` with boson weight `w` is `w + ½⟨α,α⟩`). -/
noncomputable def gradingLatGen (k : ℤ) : Submodule ℂ (LatModuleGen L) :=
  ⨆ α : L.carrier, bigradα L (k - halfNorm L α, α)

theorem bigradα_eq_bot_of_neg {w : ℤ} (α : L.carrier) (hw : w < 0) : bigradα L (w, α) = ⊥ := by
  rw [bigradα, HeisenbergN.gradingZN_of_neg hw, Submodule.map_bot]

theorem bigradα_le_gradingLatGen (w : ℤ) (α : L.carrier) :
    bigradα L (w, α) ≤ gradingLatGen L (w + halfNorm L α) := by
  have : bigradα L (w, α) = bigradα L (w + halfNorm L α - halfNorm L α, α) := by
    rw [add_sub_cancel_right]
  rw [this]
  exact le_iSup (fun β => bigradα L ((w + halfNorm L α) - halfNorm L β, β)) α

/-- **`iSup gradingLatGen = ⊤`.** -/
theorem gradingLatGen_iSup_eq_top : iSup (gradingLatGen L) = ⊤ := by
  rw [eq_top_iff, ← bigradα_iSup_eq_top L]
  refine iSup_le (fun wα => ?_)
  obtain ⟨w, α⟩ := wα
  exact le_trans (bigradα_le_gradingLatGen L w α) (le_iSup (gradingLatGen L) (w + halfNorm L α))

/-- **`gradingLatGen k = ⊥` for `k < 0`** — no state has negative conformal weight (uses evenness +
pos-definiteness: `½⟨α,α⟩ ≥ 0`, so `k − ½⟨α,α⟩ < 0`). -/
theorem gradingLatGen_positivity (hEven : L.Even) (hPos : L.PosDef) (k : ℤ) (hk : k < 0) :
    gradingLatGen L k = ⊥ := by
  rw [gradingLatGen]
  refine le_bot_iff.mp (iSup_le (fun α => ?_))
  have hh := halfNorm_nonneg L hEven hPos α
  rw [bigradα_eq_bot_of_neg L α (by omega : k - halfNorm L α < 0)]

/-! ## `gradingLatGen 0 = ℂ ∙ vacuum` -/

theorem latVacuumGen_eq_mkEα : latVacuumGen L = mkEα L 0 (HeisenbergN.vacuumN (rank L)) := rfl

theorem bigradα_zero_zero : bigradα L (0, 0) = ℂ ∙ latVacuumGen L := by
  rw [bigradα, HeisenbergN.gradingZN_zero_eq_span_vacuum (rank L), latVacuumGen_eq_mkEα,
    Submodule.map_span, Set.image_singleton]

/-- **`gradingLatGen 0 = ℂ ∙ vacuum`** — the vacuum `e^0` is the unique lowest-weight state (uses
pos-definiteness: `½⟨α,α⟩ > 0` for `α ≠ 0`). -/
theorem gradingLatGen_zero_eq_span_vacuum (hEven : L.Even) (hPos : L.PosDef) :
    gradingLatGen L 0 = ℂ ∙ latVacuumGen L := by
  rw [← bigradα_zero_zero, gradingLatGen]
  apply le_antisymm
  · refine iSup_le (fun α => ?_)
    rcases eq_or_ne α 0 with hα | hα
    · subst hα; rw [halfNorm_zero L, sub_zero]
    · rw [bigradα_eq_bot_of_neg L α (by have := halfNorm_pos L hEven hPos hα; omega)]
      exact bot_le
  · have : bigradα L (0, 0) = bigradα L ((0 : ℤ) - halfNorm L 0, 0) := by rw [halfNorm_zero L]; simp
    rw [this]
    exact le_iSup (fun α => bigradα L ((0 : ℤ) - halfNorm L α, α)) 0

/-! ## The collapse: `gradingLatGen` internal + finite-dimensional, GIVEN bounded-vector finiteness

The A₁ collapse (`gradingLat_iSupIndep`/`_finrank`) got the finiteness of the conformal-weight fiber
for free from `n² ≤ k ⇒ |n| ≤ k`.  For a general `L` the analogous input — that a positive-definite
lattice has finitely many vectors of bounded norm — is the ℤ-posdef ⇒ ℝ-posdef discreteness fact,
which we take as the hypothesis `BoundedFinite L` here; it is proved from `hPos` by
`IntegralLattice.boundedFinite` and discharged in the `_of_posDef` corollaries below. -/

/-- The level-`k` reindexing `α ↦ (k − ½⟨α,α⟩, α)`. -/
noncomputable def levelMapGen (k : ℤ) : L.carrier → ℤ × L.carrier := fun α => (k - halfNorm L α, α)

theorem range_levelMapGen (k : ℤ) :
    Set.range (levelMapGen L k) = {p : ℤ × L.carrier | p.1 + halfNorm L p.2 = k} := by
  ext p
  constructor
  · rintro ⟨α, rfl⟩; simp only [levelMapGen, Set.mem_setOf_eq]; ring
  · intro hp
    refine ⟨p.2, ?_⟩
    simp only [levelMapGen, Set.mem_setOf_eq] at hp ⊢
    rw [Prod.ext_iff]; exact ⟨by omega, rfl⟩

theorem gradingLatGen_eq_biSup (k : ℤ) :
    gradingLatGen L k = ⨆ p ∈ {p : ℤ × L.carrier | p.1 + halfNorm L p.2 = k}, bigradα L p := by
  rw [gradingLatGen, ← range_levelMapGen L k, iSup_range]; rfl

/-- The non-negative-boson-weight part of the conformal-weight-`k` fiber. -/
def fiberPosGen (k : ℤ) : Set (ℤ × L.carrier) :=
  {p : ℤ × L.carrier | p.1 + halfNorm L p.2 = k ∧ 0 ≤ p.1}

/-- The non-negative fiber is finite — from `BoundedFinite L` (only `α` with `⟨α,α⟩ ≤ 2k` contribute). -/
theorem fiberPosGen_finite (hbf : BoundedFinite L) (hEven : L.Even) (k : ℤ) :
    (fiberPosGen L k).Finite := by
  apply Set.Finite.subset (Set.Finite.image (levelMapGen L k) (hbf (2 * k)))
  rintro ⟨w, α⟩ ⟨hwα, hw⟩
  simp only at hwα hw
  refine ⟨α, ?_, ?_⟩
  · -- ⟨α,α⟩ = 2·halfNorm α ≤ 2k
    have h2 := two_halfNorm L hEven α
    simp only [Set.mem_setOf_eq]; omega
  · simp only [levelMapGen]; rw [Prod.ext_iff]; exact ⟨by omega, rfl⟩

theorem gradingLatGen_eq_biSup_pos (hEven : L.Even) (hPos : L.PosDef) (k : ℤ) :
    gradingLatGen L k = ⨆ p ∈ fiberPosGen L k, bigradα L p := by
  rw [gradingLatGen_eq_biSup L k]
  apply le_antisymm
  · refine iSup_le (fun p => iSup_le (fun hp => ?_))
    by_cases hpw : 0 ≤ p.1
    · exact le_biSup (bigradα L) ⟨hp, hpw⟩
    · rw [show bigradα L p = ⊥ from bigradα_eq_bot_of_neg L p.2 (by omega : p.1 < 0)]; exact bot_le
  · exact iSup_le (fun p => iSup_le (fun hp => le_biSup (bigradα L) hp.1))

theorem iSup_ne_gradingLatGen_eq_biSup (k : ℤ) :
    (⨆ (k' : ℤ) (_ : k' ≠ k), gradingLatGen L k')
      = ⨆ p ∈ {p : ℤ × L.carrier | p.1 + halfNorm L p.2 ≠ k}, bigradα L p := by
  apply le_antisymm
  · refine iSup_le (fun k' => iSup_le (fun hk' => ?_))
    rw [gradingLatGen_eq_biSup L k']
    refine iSup_le (fun p => iSup_le (fun hp => ?_))
    have hpk : p.1 + halfNorm L p.2 ≠ k := by
      simp only [Set.mem_setOf_eq] at hp; rw [hp]; exact hk'
    exact le_biSup (bigradα L) (Set.mem_setOf_eq ▸ hpk)
  · refine iSup_le (fun p => iSup_le (fun hp => ?_))
    simp only [Set.mem_setOf_eq] at hp
    refine le_trans (bigradα_le_gradingLatGen L p.1 p.2) ?_
    calc gradingLatGen L (p.1 + halfNorm L p.2)
        ≤ ⨆ (_ : p.1 + halfNorm L p.2 ≠ k), gradingLatGen L (p.1 + halfNorm L p.2) :=
          le_iSup (fun _ : p.1 + halfNorm L p.2 ≠ k => gradingLatGen L (p.1 + halfNorm L p.2)) hp
      _ ≤ _ := le_iSup (fun k' => ⨆ (_ : k' ≠ k), gradingLatGen L k') (p.1 + halfNorm L p.2)

/-- **`iSupIndep gradingLatGen`** — given bounded-vector finiteness. -/
theorem gradingLatGen_iSupIndep (hbf : BoundedFinite L) (hEven : L.Even) (hPos : L.PosDef) :
    iSupIndep (gradingLatGen L) := by
  rw [iSupIndep_def]
  intro k
  rw [gradingLatGen_eq_biSup_pos L hEven hPos k, iSup_ne_gradingLatGen_eq_biSup L k]
  apply iSupIndep.disjoint_biSup_biSup' (bigradα_iSupIndep L)
  · rw [Set.disjoint_left]
    rintro p hp hp'
    simp only [Set.mem_setOf_eq] at hp'
    exact hp' hp.1
  · exact fiberPosGen_finite L hbf hEven k

/-- **The `L₀`-grading is an internal direct-sum decomposition of `V_L`** — given `BoundedFinite L`. -/
theorem gradingLatGen_isInternal (hbf : BoundedFinite L) (hEven : L.Even) (hPos : L.PosDef) :
    DirectSum.IsInternal (gradingLatGen L) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradingLatGen_iSupIndep L hbf hEven hPos) (gradingLatGen_iSup_eq_top L)

instance bigradα_finiteDimensional (p : ℤ × L.carrier) : FiniteDimensional ℂ (bigradα L p) := by
  have : FiniteDimensional ℂ (HeisenbergN.gradingZN (rank L) p.1) :=
    HeisenbergN.gradingZN_finrank (rank L) p.1
  rw [bigradα]; infer_instance

/-- **Each `L₀`-weight space is finite-dimensional** — given `BoundedFinite L`. -/
theorem gradingLatGen_finrank (hbf : BoundedFinite L) (hEven : L.Even) (hPos : L.PosDef) (k : ℤ) :
    FiniteDimensional ℂ (gradingLatGen L k) := by
  rw [gradingLatGen_eq_biSup_pos L hEven hPos k, ← iSup_subtype'']
  have : Finite (fiberPosGen L k) := fiberPosGen_finite L hbf hEven k
  infer_instance

/-! ## Unconditional grading: `BoundedFinite` discharged from `hPos`

`VOA.IntegralLattice.boundedFinite` (`Foundations.LatticeFinite`) proves
`BoundedFinite L` from `L.PosDef` (ℤ-posdef ⇒ ℝ-posdef discreteness: coordinate Gram form is
coercive, so `{α | ⟨α,α⟩ ≤ N}` sits in a finite box).  Feeding it in makes the internal
direct-sum decomposition and the finite-dimensionality of each `L₀`-weight space depend only on
`hEven`/`hPos` — the same hypotheses the A₁ construction had for free. -/

/-- **The `L₀`-grading is an internal direct-sum decomposition of `V_L`** — unconditionally from
`hEven`/`hPos` (`BoundedFinite` discharged via `boundedFinite`). -/
theorem gradingLatGen_isInternal_of_posDef (hEven : L.Even) (hPos : L.PosDef) :
    DirectSum.IsInternal (gradingLatGen L) :=
  gradingLatGen_isInternal L (IntegralLattice.boundedFinite L hPos) hEven hPos

/-- **Each `L₀`-weight space is finite-dimensional** — unconditionally from `hEven`/`hPos`
(`BoundedFinite` discharged via `boundedFinite`). -/
theorem gradingLatGen_finrank_of_posDef (hEven : L.Even) (hPos : L.PosDef) (k : ℤ) :
    FiniteDimensional ℂ (gradingLatGen L k) :=
  gradingLatGen_finrank L (IntegralLattice.boundedFinite L hPos) hEven hPos k

end VOA.LatGen
