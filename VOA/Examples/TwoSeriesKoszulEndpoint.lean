/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulConcreteEndpoint
import VOA.Examples.TwoSeriesKoszulGrading

/-!
# Level-generic port of `KoszulConcreteEndpoint`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval Sl2CosetConcrete
open Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical VOA.GradedUnitaryCohomology
open VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra VOA.LeeYangTransferAssembly VOA.SympFerm
open VOA.Ghost
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `KoszulConcreteEndpoint` -/


/-! ### Blocks on the actual relative weight spaces -/

section Blocks

variable (n : ℤ)

/-- The joint pieces over a set of coarse block indices, at weight `n`. -/
def blkSup (S : (ℤ × ℤ) × ℤ → Prop) : Submodule ℂ (BRSTSpace L) :=
  ⨆ (j : KF × ℤ) (_ : S (bIdx j) ∧ wIdx j = (n : ℂ)), (blockB L) j

/-- **The antighost-count blocks of `(relativeWeight L) n`.** -/
def blkE (b : (ℤ × ℤ) × ℤ) : Submodule ℂ ((relativeWeight L) n) :=
  ((blkSup L) n (· = b)).comap ((relativeWeight L) n).subtype

variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : VOA.ConcreteHodge.Unitary BB RB)
  (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s)

/-- Decomposition of a relative vector along the joint projections. -/
theorem mem_iSup_blkE_of (y : (relativeWeight L) n) (P : (ℤ × ℤ) × ℤ → Prop)
    (h : ∀ j, iproj ((blockB_isInternal L) hA hB w hw) j (y : (BRSTSpace L)) ≠ 0 → P (bIdx j)) :
    y ∈ ⨆ (b : (ℤ × ℤ) × ℤ) (_ : P b), (blkE L) n b := by
  have hI := (blockB_isInternal L) hA hB w hw
  have hS := (relativeWeight_stableB L) hA hB w hw n
  obtain ⟨s, hs⟩ := sum_iproj hI (y : (BRSTSpace L))
  have hy : y = ∑ j ∈ s, (⟨iproj hI j y, hS j y y.2⟩ : (relativeWeight L) n) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hs.symm
  rw [hy]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases h0 : iproj hI j (y : (BRSTSpace L)) = 0
  · have : (⟨iproj hI j y, hS j y y.2⟩ : (relativeWeight L) n) = 0 := Subtype.ext h0
    rw [this]; exact Submodule.zero_mem _
  · have hwt : wIdx j = (n : ℂ) := by
      by_contra hne
      exact h0 (iproj_eq_zero_of_weight hI (brstSVA L).isInternal wIdx ((blockB_le_weight L) w)
        y.2.2 hne)
    refine Submodule.mem_iSup_of_mem (bIdx j) (Submodule.mem_iSup_of_mem (h j h0) ?_)
    change iproj hI j (y : (BRSTSpace L)) ∈ (blkSup L) n (· = bIdx j)
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem ⟨rfl, hwt⟩ (iproj_mem hI j _))

/-- Components of a vector of `(blkSup L) n S` outside `S` vanish. -/
theorem iproj_blkSup_eq_zero {S : (ℤ × ℤ) × ℤ → Prop} {x : (BRSTSpace L)} (hx : x ∈ (blkSup L) n S)
    {j : KF × ℤ} (hj : ¬ S (bIdx j) ∨ wIdx j ≠ (n : ℂ)) :
    iproj ((blockB_isInternal L) hA hB w hw) j x = 0 := by
  have := (mem_iSup_pred_iff ((blockB_isInternal L) hA hB w hw) _ x).mp hx j
  exact this (fun h => by rcases hj with hj | hj; exacts [hj h.1, hj h.2])

include hA hB hw in
theorem blkE_iSupIndep : iSupIndep ((blkE L) n) := by
  have hI := (blockB_isInternal L) hA hB w hw
  intro b
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply Subtype.ext
  rw [Submodule.coe_zero]
  -- the second membership, in the ambient space
  have hx2 : (x : (BRSTSpace L)) ∈ (blkSup L) n (· ≠ b) := by
    have hle : (⨆ (b' : (ℤ × ℤ) × ℤ) (_ : b' ≠ b), (blkE L) n b') ≤
        ((blkSup L) n (· ≠ b)).comap ((relativeWeight L) n).subtype := by
      refine iSup_le fun b' => iSup_le fun hb' => Submodule.comap_mono ?_
      refine iSup_le fun j => iSup_le fun hj => le_iSup_of_le j (le_iSup_of_le ⟨?_, hj.2⟩ le_rfl)
      rw [hj.1]; exact hb'
    exact hle hx'
  obtain ⟨s, hs⟩ := sum_iproj hI (x : (BRSTSpace L))
  rw [← hs]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : bIdx j = b
  · exact (iproj_blkSup_eq_zero L) n hA hB w hw (S := (· ≠ b)) hx2 (Or.inl fun h => h hj)
  · have hx1 : (x : (BRSTSpace L)) ∈ (blkSup L) n (· = b) := hx
    exact (iproj_blkSup_eq_zero L) n hA hB w hw (S := (· = b)) hx1 (Or.inl hj)

include hA hB hw in
theorem blkE_iSup_eq_top : iSup ((blkE L) n) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have h := (mem_iSup_blkE_of L) n hA hB w hw y (fun _ => True) (fun _ _ => trivial)
  exact (iSup_le fun b => iSup_le fun _ => le_iSup ((blkE L) n) b) h

theorem blkE_le_brstDeg (b : (ℤ × ℤ) × ℤ) :
    (blkE L) n b ≤ ((brstDeg L) (ghostRGrading w) (b.1, (n : ℂ))).comap ((relativeWeight L) n).subtype := by
  refine Submodule.comap_mono (iSup_le fun j => iSup_le fun hj => ?_)
  refine ((blockB_le_brstDegF L) j).trans (((brstDegF_le_brstDeg L) w j.1).trans ?_)
  have : fstF j.1 = (b.1, (n : ℂ)) := by
    obtain ⟨h1, h2⟩ := hj
    rw [← h1]; exact Prod.ext rfl h2
  rw [this]

theorem blkE_eq_bot {b : (ℤ × ℤ) × ℤ} (hb : b.2 < 0 ∨ b.1.2 + b.2 < 0) : (blkE L) n b = ⊥ := by
  have : (blkSup L) n (· = b) = ⊥ := by
    refine le_bot_iff.mp (iSup_le fun j => iSup_le fun hj => ?_)
    rw [blockB_eq_bot]
    have h1 := hj.1
    simp only [bIdx] at h1
    subst h1
    simpa using hb
  rw [blkE, this, Submodule.comap_bot, Submodule.ker_subtype]

include hA hB hw in
/-- **Shape of the actual differential**: on `(blkE L) n (a, q)` it lands in antighost numbers
`q` and `q - 1`. -/
theorem relativeDifferential_shape (b : (ℤ × ℤ) × ℤ) (x : (relativeWeight L) n)
    (hx : x ∈ (blkE L) n b) :
    (relativeDifferential L) n x ∈
      ⨆ (b' : (ℤ × ℤ) × ℤ) (_ : b'.2 = b.2 ∨ b'.2 + 1 = b.2), (blkE L) n b' := by
  have hI := (blockB_isInternal L) hA hB w hw
  -- `Q x` in the ambient joint grading
  have hQ : ((relativeDifferential L) n x : (BRSTSpace L)) ∈
      ⨆ (j : KF × ℤ) (_ : j.2 = b.2 ∨ j.2 + 1 = b.2), (blockB L) j := by
    rw [relativeDifferential_coe, brstComplex_Q]
    have hx' : (x : (BRSTSpace L)) ∈ (blkSup L) n (· = b) := hx
    refine Submodule.iSup_induction _
      (motive := fun z => semiInfiniteQ (matterAction L).toAffineSl2Action z ∈
        ⨆ (j : KF × ℤ) (_ : j.2 = b.2 ∨ j.2 + 1 = b.2), (blockB L) j) hx' ?_ (by simp)
      (fun z z' hz hz' => by
        beta_reduce at hz hz' ⊢; rw [map_add]; exact Submodule.add_mem _ hz hz')
    intro j z hz
    refine Submodule.iSup_induction _
      (motive := fun z => semiInfiniteQ (matterAction L).toAffineSl2Action z ∈
        ⨆ (j : KF × ℤ) (_ : j.2 = b.2 ∨ j.2 + 1 = b.2), (blockB L) j) hz ?_ (by simp)
      (fun z z' hz hz' => by
        beta_reduce at hz hz' ⊢; rw [map_add]; exact Submodule.add_mem _ hz hz')
    intro hj z hz
    have h := (semiInfiniteQ_shiftsB L) hA j z hz
    refine (iSup_le fun δ => iSup_le fun hδ => ?_ : shiftTarget (blockB L) GoodB j ≤ _) h
    refine le_iSup_of_le (j + δ) (le_iSup_of_le ?_ le_rfl)
    have hjb : j.2 = b.2 := by
      have := hj.1; simp only [bIdx] at this; rw [← this]
    rcases hδ.2 with e | e
    · left; simp [hjb, e]
    · right; simp [hjb, e]
  refine (mem_iSup_blkE_of L) n hA hB w hw _ _ (fun j hj => ?_)
  by_contra hP
  exact hj ((mem_iSup_pred_iff hI _ _).mp hQ j hP)

/-- **Antighost-count blocks of any Kähler complex on the actual relative complex** whose
bigrading is the interpreted one and whose total differential is the actual one. -/
def koszulBlocksOf (C : KahlerComplex ((relativeWeight L) n))
    (hdeg : ∀ a, C.deg a = ((brstDeg L) (ghostRGrading w) (a, (n : ℂ))).comap
      ((relativeWeight L) n).subtype)
    (hD : C.D = (relativeDifferential L) n) : KoszulBlocks C where
  blk := (blkE L) n
  indep := (blkE_iSupIndep L) n hA hB w hw
  span := (blkE_iSup_eq_top L) n hA hB w hw
  le_deg a q := by rw [hdeg]; exact (blkE_le_brstDeg L) n w (a, q)
  neg a q hq := (blkE_eq_bot L) n (Or.inl hq)
  cneg a q hq := (blkE_eq_bot L) n (Or.inr hq)
  shape i x hx := by rw [hD]; exact (relativeDifferential_shape L) n hA hB w hw i x hx

end Blocks

/-! ### The endpoint geometry -/

section Endpoint

variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

theorem endpoint_deg (n : ℤ) (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (a : ℤ × ℤ) :
    (((endpointKahler L) hA).model n hp).deg a =
      ((brstDeg L) (ghostRGrading unitWeight) (a, (n : ℂ))).comap ((relativeWeight L) n).subtype := by
  rw [← (brstDeg_std L) bgGh_isStd]
  rfl

/-- **The antighost-count blocks of the endpoint geometry** (proved). -/
def endpointBlocks (n : ℤ) (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) :
    KoszulBlocks (((endpointKahler L) hA).model n hp) :=
  (koszulBlocksOf L) n hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos _
    ((endpoint_deg L) hA n hp) (((endpointKahler L) hA).model_D n hp)

/-- **OPEN (reduced leading Koszul input) at weight `n`, degree `r`.** On the actual
antighost-count blocks of the endpoint geometry:

* (first component) Koszul exactness of the actual `d_K` (the antighost-lowering block
  component of the actual `Q⁻`) in positive antighost number, at ghost numbers `0` and `1`
  above `(2r, 0)`;
* (second component) the symbol maps: `π₀` on the antighost-free block at `(2r, 0)` into
  `gr_r A ⊗ L_1` with kernel exactly the `d_K`-boundaries; `π₁` on the antighost-free block at
  `(2r + 1, 1)` into `Π_{(a, m)} gr_r A ⊗ L_1` with kernel exactly the `d_K`-boundaries;
  `π₁ ∘ d_CE` equal to the diagonal action `J^a_m ⊗ 1 + 1 ⊗ J^a_m` after `π₀`;
* (third component) `π₀` lands in total conformal weight `n`.

Mathematically (coset note, §"Explicit leading contraction"): the first component is the
Koszul regularity of `U_n^a = x_n^a + a_n^a` (needs the PBW identification `gr U ≅ ℂ[x]` of
the auxiliary factor and the equivariant contracting homotopy on `g`-invariants); `π₀` is
"evaluate the auxiliary PBW symbol at `x = -a`". -/
def KoszulResidual (n : ℤ) (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (r : ℕ) :
    Type :=
  PProd (((endpointBlocks L) hA n hp).KExact (2 * (r : ℤ), 0))
    (Σ' S : ((endpointBlocks L) hA n hp).KoszulSymbolMaps (2 * (r : ℤ), 0) ((GrA L) r ⊗[ℂ] BSpace)
      ((grDiag L) r), ∀ x, S.π0 x ∈ tensorWeight ((grDeg L) r) bWeight n)

/-- OPEN: the reduced leading Koszul input at every weight and degree. -/
abbrev EndpointKoszulResidual : Type :=
  ∀ n (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (r : ℕ), (KoszulResidual L) hA n hp r

/-- **`(EndpointGrLeadKoszul L)` from the reduced residual.** -/
def endpointGrLeadKoszul_of_residual (R : (EndpointKoszulResidual L) hA) :
    (EndpointGrLeadKoszul L) hA :=
  fun n hp r => (grLeadKoszulData_of_blocks L) n r ((endpointBlocks L) hA n hp) (R n hp r).1
    (R n hp r).2.1 (R n hp r).2.2

end Endpoint


end

end VOA.TwoSeries
