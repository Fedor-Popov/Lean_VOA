/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.VirasoroCOne

/-!
# I1a: local composition series for positive-energy Virasoro modules

This file proves `virLocalCompositionSeries : VirLocalCompositionSeries`, the Jordan–Hölder
multiplicity statement of Deodhar–Gabber–Kac (Prop. 3.2) specialised to the Virasoro algebra:
for any `ℤ`-graded module `M` with finite-dimensional weight spaces, `M_n = 0` for `n < 0`,
`L₀ = n` on `M_n`, and Virasoro modes of central charge `c`, there are `A : ℕ → ℕ` with
`dim M_N = Σ_{h ≤ N} A h · dim L(c,h)_{N-h}`.

## Proof

Everything happens inside the lattice of mode-stable submodules of `M`; no new module types are
built except quotients `M ⧸ S`.

* `stable_proj_mem`: a mode-stable submodule is graded (`L₀` separates degrees).
* `exists_simple_layer`: if `v ∈ T ∩ M_h`, `v ∉ S`, and `L_m v ∈ S` for `m > 0`, the universal
  map `M(c,h) → M ⧸ S` gives stable `S ≤ K ≤ U ≤ T` with
  `dim U_n - dim K_n = dim L(c,h)_{n-h}`: its kernel is a proper submodule, hence inside the
  contravariant radical (`verma_proper_submodule_le_radical`), so `U ⧸ K ≅ L(c,h)` degreewise.
* `local_multiplicities`: strong induction on `Σ_{n ≤ N} (dim T_n - dim S_n)`, peeling off the
  lowest degree where `S` and `T` differ.
* `virLocalCompositionSeries`: the local multiplicities are unique (`dim L(c,h)_0 = 1`), so they
  glue to a single `A`.

No hypothesis beyond those of `VirLocalCompositionSeries` is used.
-/

open Finset

noncomputable section

namespace VOA.Classification.COne.VirComposition

open VOA.InverseDS.VirasoroVerma VOA.InverseDS.LeeYangWardClosure VirModule VirDeformModes

universe u

variable {c : ℂ} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The hypotheses of `VirLocalCompositionSeries`, bundled. -/
structure Hyp (c : ℂ) (G : ℤ → Submodule ℂ M) (Lm : ℤ → Module.End ℂ M) : Prop where
  internal : DirectSum.IsInternal G
  fd : ∀ n, FiniteDimensional ℂ (G n)
  neg : ∀ n : ℤ, n < 0 → G n = ⊥
  zero : ∀ (n : ℤ) (v : M), v ∈ G n → Lm 0 v = (n : ℂ) • v
  deg : ∀ (m n : ℤ) (v : M), v ∈ G n → Lm m v ∈ G (n - m)
  comm : ∀ m n : ℤ, ⁅Lm m, Lm n⁆ = ((m : ℂ) - n) • Lm (m + n)
      + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * c) • (1 : Module.End ℂ M) else 0)

variable {G : ℤ → Submodule ℂ M} {Lm : ℤ → Module.End ℂ M}

/-- A submodule preserved by every mode. -/
def Stable (Lm : ℤ → Module.End ℂ M) (P : Submodule ℂ M) : Prop :=
  ∀ m : ℤ, ∀ x ∈ P, Lm m x ∈ P

/-! ## Degree projections and gradedness of stable submodules -/

/-- The projection onto the degree-`n` summand. -/
def proj (hint : DirectSum.IsInternal G) (n : ℤ) : M →ₗ[ℂ] M :=
  letI := hint.chooseDecomposition
  (G n).subtype ∘ₗ (DirectSum.component ℂ ℤ (fun i => G i) n) ∘ₗ
    (DirectSum.decomposeLinearEquiv G).toLinearMap

theorem proj_apply (hint : DirectSum.IsInternal G) (n : ℤ) (x : M) :
    letI := hint.chooseDecomposition
    proj hint n x = (DirectSum.decompose G x n : M) := rfl

theorem proj_of_mem_same (hint : DirectSum.IsInternal G) {n : ℤ} {x : M} (hx : x ∈ G n) :
    proj hint n x = x := by
  letI := hint.chooseDecomposition
  rw [proj_apply]
  exact DirectSum.decompose_of_mem_same G hx

theorem proj_of_mem_ne (hint : DirectSum.IsInternal G) {i n : ℤ} {x : M} (hx : x ∈ G i)
    (hin : i ≠ n) : proj hint n x = 0 := by
  letI := hint.chooseDecomposition
  rw [proj_apply]
  exact DirectSum.decompose_of_mem_ne G hx hin

theorem proj_mem (hint : DirectSum.IsInternal G) (n : ℤ) (x : M) : proj hint n x ∈ G n := by
  letI := hint.chooseDecomposition
  rw [proj_apply]
  exact (DirectSum.decompose G x n).2

theorem exists_sum_proj (hint : DirectSum.IsInternal G) (x : M) :
    ∃ F : Finset ℤ, x = ∑ i ∈ F, proj hint i x := by
  classical
  letI := hint.chooseDecomposition
  refine ⟨(DirectSum.decompose G x).support, ?_⟩
  simp only [proj_apply]
  exact (DirectSum.sum_support_decompose G x).symm

/-- A finite sum of homogeneous vectors of distinct degrees lying in an `L₀`-stable subspace has
every summand in that subspace. -/
theorem mem_of_sum_mem (H : Hyp c G Lm) {S : Submodule ℂ M} (hS : Stable Lm S) :
    ∀ (F : Finset ℤ) (f : ℤ → M), (∀ i, f i ∈ G i) → ∑ i ∈ F, f i ∈ S →
      ∀ i ∈ F, f i ∈ S := by
  intro F
  induction F using Finset.induction_on with
  | empty => intro f _ _ i hi; simp at hi
  | insert a F haF ih =>
    intro f hf hsum
    rw [Finset.sum_insert haF] at hsum
    have hshift : ∑ i ∈ F, ((i : ℂ) - a) • f i ∈ S := by
      have h1 := S.sub_mem (hS 0 _ hsum) (S.smul_mem (a : ℂ) hsum)
      convert h1 using 1
      rw [map_add, map_sum, H.zero a _ (hf a), smul_add, Finset.smul_sum]
      simp only [sub_smul]
      rw [Finset.sum_sub_distrib]
      have : ∀ i ∈ F, Lm 0 (f i) = (i : ℂ) • f i := fun i _ => H.zero i _ (hf i)
      rw [Finset.sum_congr rfl this]
      abel
    have hrest := ih (fun i => ((i : ℂ) - a) • f i)
      (fun i => (G i).smul_mem _ (hf i)) hshift
    have hF : ∀ i ∈ F, f i ∈ S := by
      intro i hi
      have hne : ((i : ℂ) - a) ≠ 0 := by
        rw [sub_ne_zero]; intro he
        have hia : i = a := by exact_mod_cast he
        exact haF (hia ▸ hi)
      have := S.smul_mem ((i : ℂ) - a)⁻¹ (hrest i hi)
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have := S.sub_mem hsum (S.sum_mem hF)
      rwa [add_sub_cancel_right] at this
    · exact hF i hi

/-- **Stable submodules are graded.** -/
theorem stable_proj_mem (H : Hyp c G Lm) {S : Submodule ℂ M} (hS : Stable Lm S) (n : ℤ)
    {x : M} (hx : x ∈ S) : proj H.internal n x ∈ S := by
  obtain ⟨F, hF⟩ := exists_sum_proj H.internal x
  by_cases hn : n ∈ F
  · exact mem_of_sum_mem H hS F (fun i => proj H.internal i x) (fun i => proj_mem H.internal i x)
      (hF ▸ hx) n hn
  · -- `proj n x = Σ_{i ∈ F} proj n (proj i x) = 0`.
    have : proj H.internal n x = 0 := by
      conv_lhs => rw [hF]
      rw [map_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact proj_of_mem_ne H.internal (proj_mem H.internal i x) (fun he => hn (he ▸ hi))
    rw [this]; exact S.zero_mem


/-! ## The quotient representation `M ⧸ S` -/

/-- The mode `L_m` on `M ⧸ S`. -/
def qMode {S : Submodule ℂ M} (hS : Stable Lm S) (m : ℤ) : Module.End ℂ (M ⧸ S) :=
  S.mapQ S (Lm m) (fun x hx => hS m x hx)

theorem qMode_mkQ {S : Submodule ℂ M} (hS : Stable Lm S) (m : ℤ) (x : M) :
    qMode hS m (S.mkQ x) = S.mkQ (Lm m x) := rfl

theorem qMode_comm (H : Hyp c G Lm) {S : Submodule ℂ M} (hS : Stable Lm S) (m n : ℤ) :
    ⁅qMode hS m, qMode hS n⁆ = ((m : ℂ) - n) • qMode hS (m + n) +
      if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12) • (c • (1 : Module.End ℂ (M ⧸ S))) else 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := S.mkQ_surjective x
  have he := congrArg S.mkQ (LinearMap.congr_fun (H.comm m n) y)
  rw [LieRing.of_associative_ring_bracket] at he ⊢
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, qMode_mkQ, map_sub, map_add, map_smul] at he ⊢
  rw [he]
  split_ifs
  · simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_smul]
  · simp

/-- The quotient modes as Virasoro mode data with scalar centre `c`. -/
def qData (H : Hyp c G Lm) {S : Submodule ℂ M} (hS : Stable Lm S) :
    CentralVirasoroData (M ⧸ S) where
  L := qMode hS
  central := c • 1
  comm := qMode_comm H hS
  central_comm n := by
    change (c • (1 : Module.End ℂ (M ⧸ S))) * qMode hS n = qMode hS n * (c • 1)
    simp

/-- `M ⧸ S` as a Virasoro representation of central charge `c`. -/
def qRep (H : Hyp c G Lm) {S : Submodule ℂ M} (hS : Stable Lm S) : VirRep (M ⧸ S) where
  ρ := fixedRho (qData H hS) rfl
  centralCharge := c
  acts_central := fixedRho_C _ _

theorem qRep_mode (H : Hyp c G Lm) {S : Submodule ℂ M} (hS : Stable Lm S) (m : ℤ) :
    (qRep H hS).ρ (L m) = qMode hS m :=
  fixedRho_L (qData H hS) rfl m

/-! ## Creation words in `M` -/

/-- `L_{-i₁-1} ⋯ L_{-iₖ-1} v` in `M`. -/
def wordAct (Lm : ℤ → Module.End ℂ M) : List ℕ → M → M
  | [], v => v
  | i :: w, v => Lm (-(i : ℤ) - 1) (wordAct Lm w v)

theorem wordAct_mem_grading (H : Hyp c G Lm) {h : ℕ} {v : M} (hv : v ∈ G (h : ℤ)) :
    ∀ w : List ℕ, wordAct Lm w v ∈ G ((h + energyHW w : ℕ) : ℤ)
  | [] => by simpa [wordAct] using hv
  | i :: w => by
    have := H.deg (-(i : ℤ) - 1) _ _ (wordAct_mem_grading H hv w)
    rw [wordAct]
    convert this using 2
    rw [energyHW_cons]; push_cast; ring

theorem wordAct_mem_stable {T : Submodule ℂ M} (hT : Stable Lm T) {v : M} (hv : v ∈ T) :
    ∀ w : List ℕ, wordAct Lm w v ∈ T
  | [] => hv
  | _ :: w => hT _ _ (wordAct_mem_stable hT hv w)

theorem representationNegWord_qRep (H : Hyp c G Lm) {S : Submodule ℂ M} (hS : Stable Lm S)
    (v : M) : ∀ w : List ℕ,
    representationNegWord (qRep H hS) (S.mkQ v) w = S.mkQ (wordAct Lm w v)
  | [] => rfl
  | i :: w => by
    rw [representationNegWord, representationNegWord_qRep H hS v w, virMode, qRep_mode,
      qMode_mkQ]
    rfl

/-! ## One simple layer -/

/-- All sorted creation words on `v`. -/
def wordSpan (Lm : ℤ → Module.End ℂ M) (v : M) : Submodule ℂ M :=
  Submodule.span ℂ (Set.range fun w : {w : List ℕ // SortedWord w} => wordAct Lm w.val v)

/-- Sorted creation words on `v` landing in degree `n`. -/
def wordSpanDeg (Lm : ℤ → Module.End ℂ M) (v : M) (h n : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ w : List ℕ, SortedWord w ∧ h + energyHW w = n ∧ wordAct Lm w v = x}


section Layer

variable (H : Hyp c G Lm) {S : Submodule ℂ M} (hS : Stable Lm S) {h : ℕ} {v : M}
  (hlow : ∀ m : ℤ, 0 < m → Lm m v ∈ S) (hvG : v ∈ G (h : ℤ))
include hlow hvG

theorem isHighest : IsHighestWeightVector (qRep H hS) (S.mkQ v) c (h : ℂ) where
  centralCharge := rfl
  pos_annihilate m hm := by
    rw [virMode, qRep_mode, qMode_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hlow m hm
  zero_acts := by
    rw [virMode, qRep_mode, qMode_mkQ, H.zero _ _ hvG, map_smul]
    push_cast; rfl

/-- The universal map `M(c,h) → M ⧸ S`, `|h⟩ ↦ [v]`. -/
def phi : Verma c (h : ℂ) →ₗ[ℂ] M ⧸ S :=
  universalMap (qRep H hS) (S.mkQ v) (isHighest H hS hlow hvG)

theorem phi_negWord (w : List ℕ) :
    phi H hS hlow hvG (negWord c (h : ℂ) w) = S.mkQ (wordAct Lm w v) := by
  rw [phi, universalMap_negWord, representationNegWord_qRep]

theorem phi_mode (m : ℤ) (x : Verma c (h : ℂ)) :
    phi H hS hlow hvG (vermaMode c (h : ℂ) m x) = qMode hS m (phi H hS hlow hvG x) := by
  rw [phi, vermaMode, universalMap_intertwines, qRep_mode]

theorem ker_phi_le_radical (hvS : v ∉ S) :
    LinearMap.ker (phi H hS hlow hvG) ≤ vermaRadical c (h : ℂ) := by
  refine verma_proper_submodule_le_radical c _ _ (fun m x hx => ?_) (fun htop => hvS ?_)
  · rw [LinearMap.mem_ker] at hx ⊢
    rw [phi_mode, hx, map_zero]
  · have hmem : highestVector c (h : ℂ) ∈ LinearMap.ker (phi H hS hlow hvG) :=
      htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, phi, universalMap_highestVector, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hmem
    exact hmem

/-- The lower end `K` of the layer: preimage of `φ(rad)`. -/
def layerK : Submodule ℂ M :=
  (Submodule.map (phi H hS hlow hvG) (vermaRadical c (h : ℂ))).comap S.mkQ

/-- The upper end `U` of the layer: preimage of `range φ`. -/
def layerU : Submodule ℂ M :=
  (LinearMap.range (phi H hS hlow hvG)).comap S.mkQ

theorem layerK_stable : Stable Lm (layerK H hS hlow hvG) := by
  intro m y hy
  obtain ⟨r, hr, hry⟩ := hy
  refine ⟨vermaMode c (h : ℂ) m r, vermaRadical_stable c _ m r hr, ?_⟩
  rw [phi_mode, hry]
  rfl

theorem layerU_stable : Stable Lm (layerU H hS hlow hvG) := by
  intro m y hy
  obtain ⟨r, hry⟩ := hy
  refine ⟨vermaMode c (h : ℂ) m r, ?_⟩
  rw [phi_mode, hry]
  rfl

theorem le_layerK : S ≤ layerK H hS hlow hvG := by
  intro y hy
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [map_zero, eq_comm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hy

theorem layerK_le_layerU : layerK H hS hlow hvG ≤ layerU H hS hlow hvG := by
  intro y hy
  obtain ⟨r, -, hry⟩ := hy
  exact ⟨r, hry⟩

theorem range_phi_le : LinearMap.range (phi H hS hlow hvG) ≤ (wordSpan Lm v).map S.mkQ := by
  rw [LinearMap.range_eq_map]
  refine (Submodule.map_mono (verma_sortedWord_span_top c (h : ℂ))).trans ?_
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  exact ⟨wordAct Lm w.val v, Submodule.subset_span ⟨w, rfl⟩, (phi_negWord H hS hlow hvG _).symm⟩

theorem layerU_le {T : Submodule ℂ M} (hT : Stable Lm T) (hST : S ≤ T) (hvT : v ∈ T) :
    layerU H hS hlow hvG ≤ T := by
  intro y hy
  obtain ⟨z, hz, hzy⟩ := range_phi_le H hS hlow hvG hy
  have hzT : z ∈ T := by
    refine (Submodule.span_le.mpr ?_) hz
    rintro _ ⟨w, rfl⟩
    exact wordAct_mem_stable hT hvT w.val
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hzy
  have := T.sub_mem hzT (hST hzy)
  rwa [sub_sub_cancel] at this

omit hlow in
theorem proj_wordSpan_mem (n : ℕ) {z : M} (hz : z ∈ wordSpan Lm v) :
    proj H.internal (n : ℤ) z ∈ wordSpanDeg Lm v h n := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    by_cases he : h + energyHW w.val = n
    · rw [proj_of_mem_same H.internal (he ▸ wordAct_mem_grading H hvG w.val)]
      exact Submodule.subset_span ⟨w.val, w.property, he, rfl⟩
    · rw [proj_of_mem_ne H.internal (wordAct_mem_grading H hvG w.val)
        (fun h' => he (by exact_mod_cast h'))]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- `φ` followed by `M ⧸ S → M ⧸ K`. -/
def phiK : Verma c (h : ℂ) →ₗ[ℂ] M ⧸ layerK H hS hlow hvG :=
  S.mapQ (layerK H hS hlow hvG) LinearMap.id (le_layerK H hS hlow hvG) ∘ₗ phi H hS hlow hvG

theorem phiK_negWord (w : List ℕ) :
    phiK H hS hlow hvG (negWord c (h : ℂ) w) = (layerK H hS hlow hvG).mkQ (wordAct Lm w v) := by
  rw [phiK, LinearMap.comp_apply, phi_negWord]
  rfl

theorem ker_phiK (hvS : v ∉ S) :
    LinearMap.ker (phiK H hS hlow hvG) = vermaRadical c (h : ℂ) := by
  ext x
  obtain ⟨y, hy⟩ := S.mkQ_surjective (phi H hS hlow hvG x)
  have hK : phiK H hS hlow hvG x = (layerK H hS hlow hvG).mkQ y := by
    rw [phiK, LinearMap.comp_apply, ← hy]; rfl
  rw [LinearMap.mem_ker, hK, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨r, hr, hry⟩
    have hd : x - r ∈ LinearMap.ker (phi H hS hlow hvG) := by
      rw [LinearMap.mem_ker, map_sub, hry, hy, sub_self]
    have := Submodule.add_mem _ (ker_phi_le_radical H hS hlow hvG hvS hd) hr
    rwa [sub_add_cancel] at this
  · intro hx
    exact ⟨x, hx, hy.symm⟩

theorem wordSpanDeg_le (n : ℕ) :
    wordSpanDeg Lm v h n ≤ layerU H hS hlow hvG ⊓ G (n : ℤ) := by
  rw [wordSpanDeg, Submodule.span_le]
  rintro _ ⟨w, -, he, rfl⟩
  refine ⟨⟨negWord c (h : ℂ) w, phi_negWord H hS hlow hvG w⟩, ?_⟩
  have := wordAct_mem_grading H hvG w
  rwa [he] at this

/-- Degree `n` of `U ⧸ K` is spanned by the creation words of degree `n` (uses that `S` is
graded). -/
theorem map_layerU_inf (n : ℕ) :
    (layerU H hS hlow hvG ⊓ G (n : ℤ)).map (layerK H hS hlow hvG).mkQ =
      (wordSpanDeg Lm v h n).map (layerK H hS hlow hvG).mkQ := by
  refine le_antisymm ?_ (Submodule.map_mono (wordSpanDeg_le H hS hlow hvG n))
  rintro _ ⟨y, ⟨hyU, hyG⟩, rfl⟩
  obtain ⟨z, hz, hzy⟩ := range_phi_le H hS hlow hvG hyU
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hzy
  have hp := stable_proj_mem H hS (n : ℤ) hzy
  rw [map_sub, proj_of_mem_same H.internal hyG] at hp
  refine ⟨proj H.internal n z, proj_wordSpan_mem H hvG n hz, ?_⟩
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact le_layerK H hS hlow hvG hp

theorem map_wordSpanDeg_of_le {n : ℕ} (hn : h ≤ n) :
    (wordSpanDeg Lm v h n).map (layerK H hS hlow hvG).mkQ =
      (sortedSpan c (h : ℂ) (n - h)).map (phiK H hS hlow hvG) := by
  rw [wordSpanDeg, sortedSpan, Submodule.map_span, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨w, hw, he, rfl⟩, rfl⟩
    exact ⟨_, ⟨w, hw, by omega, rfl⟩, phiK_negWord H hS hlow hvG w⟩
  · rintro ⟨_, ⟨w, hw, he, rfl⟩, rfl⟩
    exact ⟨_, ⟨w, hw, by omega, rfl⟩, (phiK_negWord H hS hlow hvG w).symm⟩

/-- `φ_K` induces an injection of `L(c,h)`, so it preserves level dimensions. -/
theorem finrank_map_phiK (hvS : v ∉ S) (k : ℕ) :
    Module.finrank ℂ ((sortedSpan c (h : ℂ) k).map (phiK H hS hlow hvG)) =
      Module.finrank ℂ (vermaSimpleLevel c (h : ℂ) k) := by
  have hle : vermaRadical c (h : ℂ) ≤ LinearMap.ker (phiK H hS hlow hvG) :=
    (ker_phiK H hS hlow hvG hvS).ge
  set f := (vermaRadical c (h : ℂ)).liftQ (phiK H hS hlow hvG) hle
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_phiK H hS hlow hvG hvS).le
  have hcomp : phiK H hS hlow hvG = f ∘ₗ (vermaRadical c (h : ℂ)).mkQ :=
    (Submodule.liftQ_mkQ _ _ _).symm
  rw [hcomp, Submodule.map_comp, vermaSimpleLevel]
  exact (Submodule.equivMapOfInjective f hinj _).finrank_eq.symm

end Layer

theorem wordSpanDeg_of_lt {v : M} {h n : ℕ} (hn : n < h) : wordSpanDeg Lm v h n = ⊥ := by
  rw [wordSpanDeg, Submodule.span_eq_bot]
  rintro _ ⟨w, -, he, rfl⟩
  omega

/-- `dim (P ∩ M_n)`. -/
def dimG (G : ℤ → Submodule ℂ M) (P : Submodule ℂ M) (n : ℕ) : ℕ :=
  Module.finrank ℂ ↥(P ⊓ G (n : ℤ))

/-- **One simple layer.** A vector `v ∈ T ∩ M_h`, `v ∉ S`, singular modulo `S`, produces stable
`S ≤ K ≤ U ≤ T` with `U ⧸ K` having the graded dimension of `L(c,h)`. -/
theorem exists_simple_layer (H : Hyp c G Lm) {S T : Submodule ℂ M} (hS : Stable Lm S)
    (hT : Stable Lm T) (hST : S ≤ T) {h : ℕ} {v : M} (hvT : v ∈ T) (hvG : v ∈ G (h : ℤ))
    (hvS : v ∉ S) (hlow : ∀ m : ℤ, 0 < m → Lm m v ∈ S) :
    ∃ K U : Submodule ℂ M, Stable Lm K ∧ Stable Lm U ∧ S ≤ K ∧ K ≤ U ∧ U ≤ T ∧
      ∀ n : ℕ, dimG G U n = dimG G K n +
        if h ≤ n then Module.finrank ℂ (vermaSimpleLevel c (h : ℂ) (n - h)) else 0 := by
  refine ⟨layerK H hS hlow hvG, layerU H hS hlow hvG, layerK_stable H hS hlow hvG,
    layerU_stable H hS hlow hvG, le_layerK H hS hlow hvG, layerK_le_layerU H hS hlow hvG,
    layerU_le H hS hlow hvG hT hST hvT, fun n => ?_⟩
  haveI := H.fd (n : ℤ)
  set P := layerU H hS hlow hvG ⊓ G (n : ℤ) with hP
  set K := layerK H hS hlow hvG with hKdef
  have hf := LinearMap.finrank_range_add_finrank_ker (K.mkQ.domRestrict P)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at hf
  have hPK : P ⊓ K = K ⊓ G (n : ℤ) := by
    ext x
    simp only [hP, Submodule.mem_inf]
    constructor
    · rintro ⟨⟨-, hx⟩, hK⟩; exact ⟨hK, hx⟩
    · rintro ⟨hK, hx⟩; exact ⟨⟨layerK_le_layerU H hS hlow hvG hK, hx⟩, hK⟩
  have hker : Module.finrank ℂ (K.comap P.subtype) = dimG G K n := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, hPK]
    rfl
  rw [dimG, dimG, ← hP, ← hf, hker, map_layerU_inf, add_comm]
  congr 1
  split_ifs with hn
  · rw [map_wordSpanDeg_of_le H hS hlow hvG hn, finrank_map_phiK H hS hlow hvG hvS]
  · rw [wordSpanDeg_of_lt (by omega), Submodule.map_bot, finrank_bot]


/-! ## Induction on the truncated dimension gap -/

theorem dimG_mono (H : Hyp c G Lm) {P Q : Submodule ℂ M} (hPQ : P ≤ Q) (n : ℕ) :
    dimG G P n ≤ dimG G Q n := by
  haveI := H.fd (n : ℤ)
  exact Submodule.finrank_mono (inf_le_inf_right _ hPQ)

/-- **Local multiplicities.** For stable `S ≤ T`, the graded dimension of `T ⧸ S` in degrees
`≤ N` is a nonnegative combination of irreducible characters. -/
theorem local_multiplicities (H : Hyp c G Lm) (N : ℕ) :
    ∀ (D : ℕ) (S T : Submodule ℂ M), Stable Lm S → Stable Lm T → S ≤ T →
      ∑ n ∈ range (N + 1), (dimG G T n - dimG G S n) = D →
      ∃ A : ℕ → ℕ, ∀ n ≤ N, dimG G T n = dimG G S n +
        ∑ k ∈ range (n + 1), A k * Module.finrank ℂ (vermaSimpleLevel c (k : ℂ) (n - k)) := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro S T hS hT hST hD
  by_cases hex : ∃ n, n ≤ N ∧ dimG G S n < dimG G T n
  swap
  · refine ⟨0, fun n hn => ?_⟩
    push Not at hex
    simp only [Pi.zero_apply, zero_mul, sum_const_zero, add_zero]
    exact le_antisymm (hex n hn) (dimG_mono H hST n)
  set h := Nat.find hex with hhdef
  obtain ⟨hhN, hlt⟩ := Nat.find_spec hex
  have hmin : ∀ n < h, S ⊓ G (n : ℤ) = T ⊓ G (n : ℤ) := by
    intro n hn
    have hnot := Nat.find_min hex hn
    push Not at hnot
    haveI := H.fd (n : ℤ)
    exact Submodule.eq_of_le_of_finrank_eq (inf_le_inf_right _ hST)
      (le_antisymm (dimG_mono H hST n) (hnot (by omega)))
  have hlt' : S ⊓ G (h : ℤ) < T ⊓ G (h : ℤ) := by
    refine lt_of_le_of_ne (inf_le_inf_right _ hST) fun he => ?_
    rw [dimG, dimG, he] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨v, hvT, hvS'⟩ := SetLike.exists_of_lt hlt'
  have hvS : v ∉ S := fun hv => hvS' ⟨hv, hvT.2⟩
  have hlow : ∀ m : ℤ, 0 < m → Lm m v ∈ S := by
    intro m hm
    have hd := H.deg m _ v hvT.2
    by_cases hneg : (h : ℤ) - m < 0
    · rw [H.neg _ hneg, Submodule.mem_bot] at hd
      rw [hd]; exact S.zero_mem
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (h : ℤ) - m := ⟨((h : ℤ) - m).toNat, by omega⟩
      rw [← hk] at hd
      have hmem : Lm m v ∈ T ⊓ G (k : ℤ) := ⟨hT m v hvT.1, hd⟩
      rw [← hmin k (by omega)] at hmem
      exact hmem.1
  obtain ⟨K, U, hK, hU, hSK, hKU, hUT, hdim⟩ :=
    exists_simple_layer H hS hT hST hvT.1 hvT.2 hvS hlow
  have hKUh : dimG G K h + 1 = dimG G U h := by
    rw [hdim h, if_pos le_rfl, Nat.sub_self, vermaSimpleLevel_zero_finrank]
  have hsplit : ∀ {P Q R : Submodule ℂ M}, P ≤ Q → Q ≤ R →
      ∑ n ∈ range (N + 1), (dimG G R n - dimG G P n) =
        ∑ n ∈ range (N + 1), (dimG G R n - dimG G Q n) +
          ∑ n ∈ range (N + 1), (dimG G Q n - dimG G P n) := by
    intro P Q R hPQ hQR
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    have := dimG_mono H hPQ n
    have := dimG_mono H hQR n
    omega
  have hpos : ∀ {P Q : Submodule ℂ M}, dimG G P h < dimG G Q h →
      0 < ∑ n ∈ range (N + 1), (dimG G Q n - dimG G P n) := by
    intro P Q hPQ
    have hs := single_le_sum (f := fun n => dimG G Q n - dimG G P n)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega : h < N + 1))
    exact lt_of_lt_of_le (Nat.sub_pos_of_lt hPQ) hs
  have hTU := dimG_mono H hUT h
  have hSK' := dimG_mono H hSK h
  obtain ⟨A1, hA1⟩ := ih _ (by
      rw [← hD, hsplit hSK (hKU.trans hUT)]
      have := hpos (P := K) (Q := T) (by omega)
      omega) S K hS hK hSK rfl
  obtain ⟨A2, hA2⟩ := ih _ (by
      rw [← hD, hsplit (hSK.trans hKU) hUT]
      have := hpos (P := S) (Q := U) (by omega)
      omega) U T hU hT hUT rfl
  refine ⟨fun k => A1 k + A2 k + if k = h then 1 else 0, fun n hn => ?_⟩
  rw [hA2 n hn, hdim n, hA1 n hn]
  simp only [add_mul, sum_add_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
  split_ifs <;> omega

/-- `⊥` is stable. -/
theorem stable_bot : Stable Lm (⊥ : Submodule ℂ M) := by
  intro m x hx
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

/-- `⊤` is stable. -/
theorem stable_top : Stable Lm (⊤ : Submodule ℂ M) := fun _ _ _ => Submodule.mem_top

/-- The multiplicities are determined by the dimensions (`dim L(c,h)_0 = 1`). -/
theorem multiplicities_unique (A B : ℕ → ℕ) (N : ℕ)
    (hAB : ∀ n ≤ N,
      ∑ k ∈ range (n + 1), A k * Module.finrank ℂ (vermaSimpleLevel c (k : ℂ) (n - k)) =
      ∑ k ∈ range (n + 1), B k * Module.finrank ℂ (vermaSimpleLevel c (k : ℂ) (n - k))) :
    ∀ k ≤ N, A k = B k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro hk
  have hk' := hAB k hk
  rw [sum_range_succ, sum_range_succ, Nat.sub_self, vermaSimpleLevel_zero_finrank, mul_one,
    mul_one] at hk'
  have hs : ∑ j ∈ range k, A j * Module.finrank ℂ (vermaSimpleLevel c (j : ℂ) (k - j)) =
      ∑ j ∈ range k, B j * Module.finrank ℂ (vermaSimpleLevel c (j : ℂ) (k - j)) :=
    sum_congr rfl fun j hj => by rw [ihk j (mem_range.mp hj) (by have := mem_range.mp hj; omega)]
  omega

end VOA.Classification.COne.VirComposition

namespace VOA.Classification.COne

open VirComposition Finset

/-- **I1a, proved.** Local composition series / Jordan–Hölder multiplicities for positive-energy
Virasoro modules with finite-dimensional integer weight spaces, at every central charge
(Deodhar–Gabber–Kac 1982, Prop. 3.2, specialised to Virasoro). -/
theorem virLocalCompositionSeries : VirLocalCompositionSeries.{u} := by
  intro c M _ _ G Lm hint hfd hneg hzero hdeg hcomm
  have H : Hyp c G Lm := ⟨hint, hfd, hneg, hzero, hdeg, hcomm⟩
  have hloc : ∀ N : ℕ, ∃ A : ℕ → ℕ, ∀ n ≤ N, Module.finrank ℂ (G n) =
      ∑ k ∈ range (n + 1), A k *
        Module.finrank ℂ (InverseDS.VirasoroVerma.vermaSimpleLevel c (k : ℂ) (n - k)) := by
    intro N
    obtain ⟨A, hA⟩ := local_multiplicities H N _ ⊥ ⊤ stable_bot stable_top bot_le rfl
    refine ⟨A, fun n hn => ?_⟩
    have := hA n hn
    rwa [dimG, dimG, bot_inf_eq, finrank_bot, zero_add, top_inf_eq] at this
  choose A hA using hloc
  refine ⟨fun k => A k k, fun N => ?_⟩
  rw [hA N N le_rfl]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  rw [multiplicities_unique (A N) (A k) k
    (fun n hn => (hA N n (by omega)).symm.trans (hA k n hn)) k le_rfl]

end VOA.Classification.COne
