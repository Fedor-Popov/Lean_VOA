import VOA.Examples.LatticeFields

/-!
# L₀-weight grading of the A₁ lattice VOA state space (`LatModule = FockN 1 ⊗ ℂ{ℤ}`)

The conformal weight of `p ⊗ e^{nα}` with `p` of boson weight `w` is `w + n²`
(since `wt(e^{nα}) = ½⟨nα,nα⟩ = n²`, as `⟨α,α⟩ = 2`).  We build the `L₀`-grading via
a `(ℤ × ℤ)`-bigrading `bigrad (w,n) = (gradingZN 1 w).map (p ↦ p ⊗ e^{nα})`, prove it is an
internal direct sum (`bigrad_isInternal`), then **collapse** along the fiber map
`(w,n) ↦ w + n²` to obtain `gradingLat k = ⨆ₙ bigrad (k - n², n)`.

This is the `VA1`/`VOA2`-grading datum the `VertexOperatorAlgebra (LatModule)` instance needs,
built purely from the already-proved `FockN` grading (`HeisenbergN.gradingZN_isInternal` etc.)
and `Mathlib`'s tensor/`DirectSum` API — `pbw`-free.

Deliverables (all axiom-clean: `[propext, Classical.choice, Quot.sound]`):
1. `gradingLat`            — the `L₀`-weight grading
2. `gradingLat_isInternal` — internal direct-sum decomposition
3. `gradingLat_finrank`    — each weight space is finite-dimensional
4. `gradingLat_positivity` — `gradingLat k = ⊥` for `k < 0`
5. `gradingLat_zero_eq_span_vacuum` — `gradingLat 0 = ℂ ∙ latVacuum`
-/

open scoped BigOperators TensorProduct DirectSum
open Module (End)

namespace VOA
namespace LatExp

open HeisenbergN (FockN vacuumN gradingZN)
open LatticeVOA (LatModule LatGrp eVec latState latVacuum)

/-- The injection `p ↦ p ⊗ eVec n` of the boson Fock space into a single lattice sector. -/
noncomputable def mkE (n : ℤ) : B →ₗ[ℂ] LatModule :=
  (TensorProduct.mk ℂ B LatGrp).flip (eVec n)

@[simp] theorem mkE_apply (n : ℤ) (p : B) : mkE n p = p ⊗ₜ[ℂ] eVec n := rfl

/-- The product `(ℤ × ℤ)`-bigrading: weight `w` boson part tensored into lattice sector `n`. -/
noncomputable def bigrad (wn : ℤ × ℤ) : Submodule ℂ LatModule :=
  (gradingZN 1 wn.1).map (mkE wn.2)

/-- The `eVec n`-coordinate extraction `LatModule = B ⊗ ℂ{ℤ} → B`, sending
`p ⊗ eVec n' ↦ (if n = n' then p else 0)`. Built as `rid ∘ rTensor (lapply n)`. -/
noncomputable def coordE (n : ℤ) : LatModule →ₗ[ℂ] B :=
  (TensorProduct.rid ℂ B).toLinearMap.comp (LinearMap.lTensor B (Finsupp.lapply n))

theorem coordE_apply (n n' : ℤ) (p : B) :
    coordE n (p ⊗ₜ[ℂ] eVec n') = (if n = n' then p else 0) := by
  rw [coordE, LinearMap.comp_apply, LinearMap.lTensor_tmul]
  show (TensorProduct.rid ℂ B) (p ⊗ₜ[ℂ] (Finsupp.lapply n) (eVec n')) = _
  show (TensorProduct.rid ℂ B) (p ⊗ₜ[ℂ] (Finsupp.single n' (1:ℂ) n)) = _
  rw [Finsupp.single_apply]
  by_cases h : n' = n
  · rw [if_pos h, if_pos h.symm, TensorProduct.rid_tmul, one_smul]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), TensorProduct.tmul_zero, map_zero]

/-- The boson grading internal-decomposition linear equivalence `(⨁ w, gradingZN 1 w) ≃ B`. -/
noncomputable def bEquiv : (⨁ w : ℤ, (gradingZN 1 w : Submodule ℂ B)) ≃ₗ[ℂ] B :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (gradingZN 1))
    (HeisenbergN.gradingZN_isInternal 1)

/-- The boson weight-`w` projection `B →ₗ B` (image lands in `gradingZN 1 w`). -/
noncomputable def bproj (w : ℤ) : B →ₗ[ℂ] B :=
  (gradingZN 1 w).subtype.comp
    ((DirectSum.component ℂ ℤ (fun w => (gradingZN 1 w : Submodule ℂ B)) w).comp
      bEquiv.symm.toLinearMap)

theorem bproj_same {w : ℤ} {p : B} (hp : p ∈ gradingZN 1 w) : bproj w p = p := by
  rw [bproj, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← DirectSum.apply_eq_component]
  show ((bEquiv.symm p) w : B) = p
  rw [bEquiv, DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem _ hp]

theorem bproj_of_ne {w w' : ℤ} (hww : w ≠ w') {p : B} (hp : p ∈ gradingZN 1 w') :
    bproj w p = 0 := by
  rw [bproj, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← DirectSum.apply_eq_component]
  show ((bEquiv.symm p) w : B) = 0
  rw [bEquiv, DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne _ hww.symm hp]
  rfl

/-! ## The retraction detecting `bigrad (w,n)` -/

/-- The detector `LatModule →ₗ B` for the bigraded piece `(w,n)`: extract sector `n`, then
project to boson-weight `w`. -/
noncomputable def piWN (w n : ℤ) : LatModule →ₗ[ℂ] B := (bproj w).comp (coordE n)

theorem piWN_mkE (w n n' : ℤ) {p : B} (hp : p ∈ gradingZN 1 w) :
    piWN w n (mkE n' p) = (if n = n' then p else 0) := by
  rw [piWN, LinearMap.comp_apply, mkE_apply, coordE_apply]
  by_cases h : n = n'
  · rw [if_pos h, bproj_same hp]
  · rw [if_neg h, map_zero]

/-- `piWN w n` annihilates `bigrad (w', n')` whenever `(w',n') ≠ (w,n)`. -/
theorem piWN_bigrad_of_ne (w n w' n' : ℤ) (hne : (w', n') ≠ (w, n)) :
    bigrad (w', n') ≤ LinearMap.ker (piWN w n) := by
  rintro x ⟨p, hp, rfl⟩
  rw [LinearMap.mem_ker, piWN, LinearMap.comp_apply, mkE_apply, coordE_apply]
  by_cases hn : n = n'
  · subst hn
    have hww : w ≠ w' := fun h => hne (by rw [h])
    rw [if_pos rfl, bproj_of_ne hww hp]
  · rw [if_neg hn, map_zero]

/-- `piWN w n` is a left inverse of `mkE n` on `gradingZN 1 w` (it is faithful on `bigrad (w,n)`). -/
theorem piWN_section {w n : ℤ} {p : B} (hp : p ∈ gradingZN 1 w) :
    piWN w n (mkE n p) = p := by rw [piWN_mkE w n n hp, if_pos rfl]

/-! ## `iSupIndep bigrad` -/

theorem bigrad_iSupIndep : iSupIndep bigrad := by
  rw [iSupIndep_def]
  rintro ⟨w, n⟩
  rw [Submodule.disjoint_def]
  intro x hx hxsup
  -- `x ∈ bigrad (w,n)`: get its preimage `p`
  obtain ⟨p, hp, hpx⟩ := hx
  -- the detector kills the `⨆ j ≠ (w,n)` part
  have hker : (⨆ j, ⨆ (_ : j ≠ (w, n)), bigrad j) ≤ LinearMap.ker (piWN w n) := by
    refine iSup_le (fun j => iSup_le (fun hj => ?_))
    exact piWN_bigrad_of_ne w n j.1 j.2 (by simpa using hj)
  have hxk : piWN w n x = 0 := by
    rw [← LinearMap.mem_ker]; exact hker hxsup
  -- but `piWN w n x = p` since `x = mkE n p`
  have : piWN w n x = p := by rw [← hpx]; exact piWN_section hp
  rw [this] at hxk
  rw [← hpx, hxk, map_zero]

/-! ## `iSup bigrad = ⊤` -/

theorem mkE_mem_iSup_bigrad (n : ℤ) (p : B) : mkE n p ∈ iSup bigrad := by
  have hmem : mkE n p ∈ (⨆ w : ℤ, bigrad (w, n)) := by
    have hmap : (⨆ w : ℤ, gradingZN 1 w).map (mkE n) = ⨆ w : ℤ, bigrad (w, n) := by
      rw [Submodule.map_iSup]; rfl
    have hp : p ∈ (⨆ w : ℤ, gradingZN 1 w) := by
      rw [HeisenbergN.gradingZN_iSup_eq_top 1]; trivial
    have : mkE n p ∈ (⨆ w : ℤ, gradingZN 1 w).map (mkE n) :=
      Submodule.mem_map_of_mem hp
    rwa [hmap] at this
  have hle : (⨆ w : ℤ, bigrad (w, n)) ≤ iSup bigrad :=
    iSup_le (fun w => le_iSup bigrad (w, n))
  exact hle hmem

theorem bigrad_iSup_eq_top : iSup bigrad = ⊤ := by
  rw [eq_top_iff]
  rw [← TensorProduct.span_tmul_eq_top ℂ B LatGrp]
  rw [Submodule.span_le]
  rintro _ ⟨p, g, rfl⟩
  -- `p ⊗ₜ g = ∑_{n ∈ g.support} (p ⊗ₜ single n (g n))`, each in `iSup bigrad`
  have hg : g = ∑ n ∈ g.support, (g n) • eVec n := by
    conv_lhs => rw [← Finsupp.sum_single g]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [eVec, show ((g n) • AddMonoidAlgebra.single n (1:ℂ) : LatGrp)
        = AddMonoidAlgebra.single n (g n) from by
      rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]]
  rw [SetLike.mem_coe, hg, TensorProduct.tmul_sum]
  refine Submodule.sum_mem _ (fun n _ => ?_)
  rw [TensorProduct.tmul_smul]
  exact Submodule.smul_mem _ _ (mkE_mem_iSup_bigrad n p)

/-- **The product `(ℤ×ℤ)`-bigrading is an internal direct sum.** -/
theorem bigrad_isInternal : DirectSum.IsInternal bigrad :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    bigrad_iSupIndep bigrad_iSup_eq_top

/-! ## The collapsed `L₀`-grading `gradingLat` -/

/-- The **`L₀`-weight grading** of `LatModule`: the conformal weight of `p ⊗ eVec n` with `p` of
boson weight `w` is `w + n²` (since `wt(e^{nα}) = ½⟨nα,nα⟩ = n²`).  So the weight-`k` space is
`⨆ₙ bigrad (k - n², n)`. -/
noncomputable def gradingLat (k : ℤ) : Submodule ℂ LatModule :=
  ⨆ n : ℤ, bigrad (k - n ^ 2, n)

/-- A bigraded piece with negative boson weight is trivial. -/
theorem bigrad_eq_bot_of_neg {w n : ℤ} (hw : w < 0) : bigrad (w, n) = ⊥ := by
  rw [bigrad, HeisenbergN.gradingZN_of_neg hw, Submodule.map_bot]

/-- `bigrad (w, n) ≤ gradingLat (w + n²)`: each bigraded piece sits at its conformal weight. -/
theorem bigrad_le_gradingLat (w n : ℤ) : bigrad (w, n) ≤ gradingLat (w + n ^ 2) := by
  have : bigrad (w, n) = bigrad (w + n ^ 2 - n ^ 2, n) := by rw [add_sub_cancel_right]
  rw [this]
  exact le_iSup (fun m => bigrad ((w + n ^ 2) - m ^ 2, m)) n

/-- **`iSup gradingLat = ⊤`.** -/
theorem gradingLat_iSup_eq_top : iSup gradingLat = ⊤ := by
  rw [eq_top_iff, ← bigrad_iSup_eq_top]
  refine iSup_le (fun wn => ?_)
  obtain ⟨w, n⟩ := wn
  exact le_trans (bigrad_le_gradingLat w n) (le_iSup gradingLat (w + n ^ 2))

/-! ## `iSupIndep gradingLat` — the collapse -/

/-- The level-`k` reindexing map `n ↦ (k - n², n) : ℤ → ℤ × ℤ`. -/
def levelMap (k : ℤ) : ℤ → ℤ × ℤ := fun n => (k - n ^ 2, n)

/-- The range of `levelMap k` is exactly the fiber `{p | p.1 + p.2² = k}`. -/
theorem range_levelMap (k : ℤ) : Set.range (levelMap k) = {p : ℤ × ℤ | p.1 + p.2 ^ 2 = k} := by
  ext p
  constructor
  · rintro ⟨n, rfl⟩; simp only [levelMap, Set.mem_setOf_eq]; ring
  · intro hp
    refine ⟨p.2, ?_⟩
    simp only [levelMap, Set.mem_setOf_eq] at hp ⊢
    rw [Prod.ext_iff]
    exact ⟨by omega, rfl⟩

/-- `gradingLat k` as a `biSup` of `bigrad` over its conformal-weight fiber. -/
theorem gradingLat_eq_biSup (k : ℤ) :
    gradingLat k = ⨆ p ∈ {p : ℤ × ℤ | p.1 + p.2 ^ 2 = k}, bigrad p := by
  rw [gradingLat, ← range_levelMap k, iSup_range]
  rfl

/-- The non-negative-weight part of the conformal-weight-`k` fiber. -/
def fiberPos (k : ℤ) : Set (ℤ × ℤ) := {p : ℤ × ℤ | p.1 + p.2 ^ 2 = k ∧ 0 ≤ p.1}

/-- The non-negative-weight fiber is finite (only `n` with `n² ≤ k` contribute). -/
theorem fiberPos_finite (k : ℤ) : (fiberPos k).Finite := by
  apply Set.Finite.subset (Set.Finite.image (levelMap k) (Set.finite_Icc (-k) k))
  rintro ⟨w, n⟩ ⟨hwn, hw⟩
  simp only at hwn hw
  -- `n² ≤ k`, so `|n| ≤ k` (when `k ≥ 0`); hence `n ∈ [-k, k]` and `(w,n) = levelMap k n`
  have hn2 : n ^ 2 ≤ k := by nlinarith [sq_nonneg n]
  have hnk : -k ≤ n ∧ n ≤ k := by constructor <;> nlinarith [sq_nonneg (n - 1), sq_nonneg (n + 1)]
  refine ⟨n, ⟨hnk.1, hnk.2⟩, ?_⟩
  simp only [levelMap]
  rw [Prod.ext_iff]
  exact ⟨by omega, rfl⟩

/-- `gradingLat k` restricted to its finite (non-negative-weight) fiber. -/
theorem gradingLat_eq_biSup_pos (k : ℤ) :
    gradingLat k = ⨆ p ∈ fiberPos k, bigrad p := by
  rw [gradingLat_eq_biSup k]
  apply le_antisymm
  · refine iSup_le (fun p => iSup_le (fun hp => ?_))
    by_cases hpw : 0 ≤ p.1
    · exact le_biSup bigrad ⟨hp, hpw⟩
    · rw [show bigrad p = ⊥ from bigrad_eq_bot_of_neg (by omega : p.1 < 0)]
      exact bot_le
  · refine iSup_le (fun p => iSup_le (fun hp => ?_))
    exact le_biSup bigrad hp.1

/-- The complementary join `⨆_{k'≠k} gradingLat k'` as a `biSup` of `bigrad` over the complement
of the conformal-weight-`k` fiber. -/
theorem iSup_ne_gradingLat_eq_biSup (k : ℤ) :
    (⨆ (k' : ℤ) (_ : k' ≠ k), gradingLat k')
      = ⨆ p ∈ {p : ℤ × ℤ | p.1 + p.2 ^ 2 ≠ k}, bigrad p := by
  apply le_antisymm
  · refine iSup_le (fun k' => iSup_le (fun hk' => ?_))
    rw [gradingLat_eq_biSup k']
    refine iSup_le (fun p => iSup_le (fun hp => ?_))
    have hpk : p.1 + p.2 ^ 2 ≠ k := by
      simp only [Set.mem_setOf_eq] at hp; rw [hp]; exact hk'
    exact le_biSup bigrad (Set.mem_setOf_eq ▸ hpk)
  · refine iSup_le (fun p => iSup_le (fun hp => ?_))
    simp only [Set.mem_setOf_eq] at hp
    -- `p` sits in `gradingLat (p.1 + p.2²)`, and `p.1 + p.2² ≠ k`
    refine le_trans (bigrad_le_gradingLat p.1 p.2) ?_
    calc gradingLat (p.1 + p.2 ^ 2)
        ≤ ⨆ (_ : p.1 + p.2 ^ 2 ≠ k), gradingLat (p.1 + p.2 ^ 2) :=
          le_iSup (fun _ : p.1 + p.2 ^ 2 ≠ k => gradingLat (p.1 + p.2 ^ 2)) hp
      _ ≤ _ := le_iSup (fun k' => ⨆ (_ : k' ≠ k), gradingLat k') (p.1 + p.2 ^ 2)

/-- **`iSupIndep gradingLat`.** -/
theorem gradingLat_iSupIndep : iSupIndep gradingLat := by
  rw [iSupIndep_def]
  intro k
  rw [gradingLat_eq_biSup_pos k, iSup_ne_gradingLat_eq_biSup k]
  apply iSupIndep.disjoint_biSup_biSup' bigrad_iSupIndep
  · -- `Disjoint (fiberPos k) {p | p.1+p.2² ≠ k}`
    rw [Set.disjoint_left]
    rintro p hp hp'
    simp only [Set.mem_setOf_eq] at hp'
    exact hp' hp.1
  · exact fiberPos_finite k

/-- **The `L₀`-weight grading is an internal direct-sum decomposition of `LatModule`.** -/
theorem gradingLat_isInternal : DirectSum.IsInternal gradingLat :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    gradingLat_iSupIndep gradingLat_iSup_eq_top

/-! ## finrank -/

instance bigrad_finiteDimensional (p : ℤ × ℤ) : FiniteDimensional ℂ (bigrad p) := by
  have : FiniteDimensional ℂ (gradingZN 1 p.1) := HeisenbergN.gradingZN_finrank 1 p.1
  rw [bigrad]
  infer_instance

/-- **Each `L₀`-weight space `gradingLat k` is finite-dimensional.** -/
theorem gradingLat_finrank (k : ℤ) : FiniteDimensional ℂ (gradingLat k) := by
  rw [gradingLat_eq_biSup_pos k, ← iSup_subtype'']
  have : Finite (fiberPos k) := (fiberPos_finite k)
  infer_instance

/-! ## positivity -/

/-- **`gradingLat k = ⊥` for `k < 0`** (no state has negative conformal weight). -/
theorem gradingLat_positivity (k : ℤ) (hk : k < 0) : gradingLat k = ⊥ := by
  rw [gradingLat]
  refine le_bot_iff.mp (iSup_le (fun n => ?_))
  rw [bigrad_eq_bot_of_neg (by nlinarith [sq_nonneg n] : k - n ^ 2 < 0)]

/-! ## `gradingLat 0 = ℂ ∙ latVacuum` -/

/-- `latVacuum = mkE 0 (vacuumN 1)` (i.e. `1 ⊗ e^0`). -/
theorem latVacuum_eq_mkE : latVacuum = mkE 0 (vacuumN 1) := by
  rw [mkE_apply, HeisenbergN.vacuumN]; rfl

/-- The bottom bigraded piece is the vacuum line. -/
theorem bigrad_zero_zero : bigrad (0, 0) = ℂ ∙ latVacuum := by
  rw [bigrad, HeisenbergN.gradingZN_zero_eq_span_vacuum 1, latVacuum_eq_mkE,
    Submodule.map_span, Set.image_singleton]

/-- **`gradingLat 0 = ℂ ∙ latVacuum`** — the vacuum is the unique lowest conformal-weight state. -/
theorem gradingLat_zero_eq_span_vacuum : gradingLat 0 = ℂ ∙ latVacuum := by
  rw [← bigrad_zero_zero, gradingLat]
  apply le_antisymm
  · refine iSup_le (fun n => ?_)
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, le_refl]
    · have hn2 : 0 < n ^ 2 := by positivity
      rw [bigrad_eq_bot_of_neg (by omega : (0 : ℤ) - n ^ 2 < 0)]
      exact bot_le
  · have : bigrad (0, 0) = bigrad ((0 : ℤ) - (0 : ℤ) ^ 2, 0) := by norm_num
    rw [this]; exact le_iSup (fun n => bigrad ((0 : ℤ) - n ^ 2, n)) 0

end LatExp
end VOA
