/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesArakawaIntertwine
import VOA.Examples.VirasoroSingularGram

/-!
# The slice image of the bottom of a singular vector is a Virasoro singular vector

Let `s ∈ V^k(sl₂)` be positive-current-singular and horizontal-highest of `sl₂`-weight `2`, and
`t₀ = f₀² s` the bottom of its horizontal triplet.  The lifts `Q₀, Q₁, Q₂`
(`TwoSeriesArakawaPositive`, `TwoSeriesArakawaIntertwine`) act on `t₀` by

  `Q₀ t₀ = (2/(k+2) - 1) t₀`,   `Q₁ t₀ = 0`,   `Q₂ t₀ = 0`

(every term ends in a positive current mode, in `f₀` acting on `t₀`, or in the horizontal
Casimir).  Transporting through `W₁ ∘ Q_i = L_i ∘ W₁`, the vector `v = W₁(t₀)` satisfies
`L₀ v = (2/(k+2) - 1) v`, `L₁ v = L₂ v = 0` in `Vir^{c_DS(k)}`, so for `k ≠ 0` it is a Virasoro
singular vector of nonzero weight and lies in the maximal ideal.  This is exactly the bottom
input of `TwoSeriesArakawaEndpoint`, **proved for every level**.

## Results

* `Lm_pos_singP`, `Lm_zero_singP` — Sugawara annihilation modes on singular vectors;
* `singular_mem_maxIdealVir_of_L0` — `L₀ v = μ v` (`μ ≠ 0`), `L₁ v = L₂ v = 0` ⇒ maximal ideal;
* `Wslice_eq_single_of_h0` — a charge eigenvector has a single graded slice component;
* `bottom_mem_maxIdealVir` — `W(f₀² s) ∈ maxIdeal(Vir^{c_DS(k)})`;
* `sliceArakawa_of_maximalGeneration` — **`SliceArakawa` from Adamović–Milas generation
  alone**;
* `twoSeries_gradedUnitary_of_maximalGeneration` — **Affine GU ⇒ GU of `M(2, 2m+5)`**,
  `#print axioms`-clean, conditional on `hA`, the Adamović–Milas generation of the maximal ideal
  of `V^{k}(sl₂)` (`k = -2 + 2/(2m+3)`) by a horizontal-highest positive-singular vector, and
  `JetPoincareCoreT0 (m+1)`.

Everything here is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA VOA.AffineVOA.SugawaraCov VOA.AffineVOA.Strong MvPolynomial
open VOA.VirModule VOA.TwoSeries.DSSlice VOA.VirSimple VOA.LeeYangCharacter
open VOA.TwoSeries.StrictModel VOA.SymbolModel VOA.AffineVOA.Inst
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete
open VOA.AffineSl2BoundaryMaximalIdeal
open scoped BigOperators

noncomputable section

variable (c k : ℂ) (hk : k + 2 ≠ 0)

/-! ## §1  Sugawara annihilation modes on singular vectors -/

theorem Lm_apply_nprod (n : ℤ) (t : WakModule k) :
    Lm k hk n t = (2 * (k + dualCoxeter))⁻¹ • ∑ a : Fin 3, ∑ b : Fin 3, kappaInv a b •
      VOA.nprod (Jfield_isField k a) (Jfield_isField k b) (-n - 2) t := by
  rw [Lm, YA_omega_eq, mode_apply, show -(n + 1) - 1 = -n - 2 by ring]
  unfold AffineVOA.sugawaraField
  show ((2 * (k + dualCoxeter))⁻¹ • (Reconstruction.evalAt (-n - 2) t
      (∑ a : Fin 3, ∑ b : Fin 3,
        kappaInv a b • VOA.nprod (Jfield_isField k a) (Jfield_isField k b)))) = _
  rw [map_sum]
  refine congrArg ((2 * (k + dualCoxeter))⁻¹ • ·) ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, Reconstruction.evalAt_apply]

/-- Positive Sugawara modes kill positive-singular vectors. -/
theorem Lm_pos_singP (t : WakModule k) (ht : SingP k t) {n : ℤ} (hn : 1 ≤ n) :
    Lm k hk n t = 0 := by
  rw [Lm_apply_nprod]
  refine (smul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero fun a _ =>
    Finset.sum_eq_zero fun b _ => ?_)))
  rw [nprod_coeff_apply, finsum_eq_zero_of_forall_eq_zero, smul_zero]
  intro p
  split_ifs with hp
  · rw [ht b _ (by omega), map_zero]
  · by_cases hp1 : p = -1
    · subst hp1
      rw [show -(-1 : ℤ) - 1 = 0 by norm_num, (ht.zeroMode a) b _ (by omega)]
    · rw [ht a _ (by omega), map_zero]

/-- `L₀` on a positive-singular vector is the horizontal Casimir. -/
theorem Lm_zero_singP (t : WakModule k) (ht : SingP k t) :
    Lm k hk 0 t = (2 * (k + dualCoxeter))⁻¹ • ∑ a : Fin 3, ∑ b : Fin 3,
      kappaInv a b • J k b 0 (J k a 0 t) := by
  rw [Lm_apply_nprod]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [nprod_coeff_apply, finsum_eq_single _ (-1)]
  · norm_num
  · intro p hp
    split_ifs with h0
    · rw [ht b _ (by omega), map_zero]
    · rw [ht a _ (by omega), map_zero]

/-! ## §2  A Virasoro singular vector of nonzero weight is in the maximal ideal -/

theorem singular_mem_maxIdealVir_of_L0 (v : VirUniv c) (μ : ℂ) (hμ : μ ≠ 0)
    (h0 : Lop c 0 v = μ • v) (h1 : Lop c 1 v = 0) (h2 : Lop c 2 v = 0) :
    v ∈ maxIdealVir c := by
  have hpos := VirDeformModes.NormalOrdering.Lop_positive_eq_zero_of_one_two c v h1 h2
  have hrow : ∀ x : VirUniv c, (VirGram4.canB c).form x v = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℂ (Set.range (negWordVir c)) := by
      have := negSpanVir_eq_top c
      rw [negSpanVir] at this
      rw [this]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨w, rfl⟩ := hx
        cases w with
        | nil =>
            have h := VirFormSym.adjLop (VirGram4.canB c) 0 (vacVec c) v
            rw [Lop_vacuum c (by norm_num), map_zero, LinearMap.zero_apply, neg_zero, h0,
              map_smul] at h
            rw [negWordVir_nil]
            exact (smul_eq_zero.mp h.symm).resolve_left hμ
        | cons i w =>
            rw [VirFormSym.negWord_cons_left, hpos _ (by omega), map_zero]
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul a x _ hx => simp [map_smul, hx]
  have hr : v ∈ SingVec.rightRadical (VirGram4.canB c) := SingVec.mem_rightRadical.mpr hrow
  rw [LiRadical.rightRadical_eq_maxGradedIdeal (VirGram4.canB_isFullyInvariant c)
    (VirGram4.canB_normalized c)] at hr
  exact hr

/-! ## §3  Charge eigenvectors have a single graded component -/

theorem h0_J_letter (r : Fin 3) (μ : ℤ) (y : WakModule k) (lam : ℂ)
    (hy : J k 2 0 y = lam • y) :
    J k 2 0 (J k (rankColor r) μ y) =
      (lam - 2 * (1 - ((r : ℕ) : ℂ))) • J k (rankColor r) μ y := by
  rcases fin3_cases r with rfl | rfl | rfl
  · show J k 2 0 (J k 1 μ y) = (lam - 2 * (1 - (((0 : Fin 3) : ℕ) : ℂ))) • J k 1 μ y
    rw [h_f_comm, hy, map_smul, zero_add]
    norm_num; module
  · show J k 2 0 (J k 2 μ y) = (lam - 2 * (1 - (((1 : Fin 3) : ℕ) : ℂ))) • J k 2 μ y
    rw [h0_h_comm, hy, map_smul]
    norm_num
  · show J k 2 0 (J k 0 μ y) = (lam - 2 * (1 - (((2 : Fin 3) : ℕ) : ℂ))) • J k 0 μ y
    rw [h0_e_comm, hy, map_smul]
    norm_num; module

theorem h0_rword (l : List RLetter) :
    J k 2 0 (rword k l) = (-2 * (chl l : ℂ)) • rword k l := by
  induction l with
  | nil => simp [J_vacuum_nonneg k 2 le_rfl]
  | cons q l ih =>
      rw [rword_cons, chl_cons]
      change J k 2 0 (J k (rankColor (ofLex q).1) _ _) = _
      rw [h0_J_letter k _ _ _ _ ih]
      change _ = _ • J k (rankColor (ofLex q).1) _ _
      congr 1
      simp only [rk]
      push_cast
      ring

theorem Wslice_h0 (y : WakModule k) (a : ℤ) :
    Wslice c k hk (J k 2 0 y) a = (-2 * (a : ℂ)) • Wslice c k hk y a := by
  have h : (Finsupp.lapply a).comp ((Wslice c k hk).comp (J k 2 0)) =
      (-2 * (a : ℂ)) • (Finsupp.lapply a).comp (Wslice c k hk) := by
    apply LinearMap.ext_on_range (rword_span_eq_top k)
    intro l
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply]
    rw [h0_rword, map_smul, Wslice, chargeLift_rword, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with he
    · rw [he]
    · simp
  exact LinearMap.congr_fun h y

theorem Wslice_sum (y : WakModule k) :
    (Wslice c k hk y).sum (fun _ v => v) = W1 c k hk y := by
  have h : (Finsupp.lsum ℕ fun _ : ℤ => (LinearMap.id : VirUniv c →ₗ[ℂ] VirUniv c)).comp
      (Wslice c k hk) = W1 c k hk := by
    apply LinearMap.ext_on_range (rword_span_eq_top k)
    intro l
    rw [LinearMap.comp_apply, Wslice, chargeLift_rword]
    simp
  have := LinearMap.congr_fun h y
  simpa using this

/-- A charge eigenvector has a single graded slice component. -/
theorem Wslice_eq_single_of_h0 (y : WakModule k) (q : ℤ)
    (hy : J k 2 0 y = (-2 * (q : ℂ)) • y) :
    Wslice c k hk y = Finsupp.single q (W1 c k hk y) := by
  have hz : ∀ a, a ≠ q → Wslice c k hk y a = 0 := by
    intro a ha
    have h := Wslice_h0 c k hk y a
    rw [hy, map_smul, Finsupp.smul_apply] at h
    have h2 : ((-2 * (q : ℂ)) - (-2 * (a : ℂ))) • Wslice c k hk y a = 0 := by
      rw [sub_smul, h, sub_self]
    have hne : (-2 * (q : ℂ)) - (-2 * (a : ℂ)) ≠ 0 := by
      intro h0
      apply ha
      have : (a : ℂ) = q := by linear_combination h0 / 2
      exact_mod_cast this
    exact (smul_eq_zero.mp h2).resolve_left hne
  have hs : Wslice c k hk y = Finsupp.single q (Wslice c k hk y q) := by
    ext a
    by_cases ha : a = q
    · subst ha; simp
    · rw [hz a ha, Finsupp.single_apply, if_neg (Ne.symm ha)]
  have hsum := Wslice_sum c k hk y
  rw [hs, Finsupp.sum_single_index rfl] at hsum
  rw [hs, hsum]

/-! ## §4  The bottom of the triplet -/

section Bottom

variable (s : WakModule k) (hS : SingP k s) (he : J k 0 0 s = 0) (hh : J k 2 0 s = (2 : ℂ) • s)

include hS he hh

omit hS in
theorem triplet_relations :
    J k 0 0 (J k 1 0 (J k 1 0 s)) = (2 : ℂ) • J k 1 0 s ∧
      J k 2 0 (J k 1 0 (J k 1 0 s)) = (-2 : ℂ) • J k 1 0 (J k 1 0 s) ∧
      J k 1 0 (J k 1 0 (J k 1 0 s)) = 0 := by
  have he₁ : J k 0 0 (J k 1 0 s) = (2 : ℂ) • s := by
    rw [e0_f0_comm, he, map_zero, zero_add, hh]
  have hh₁ : J k 2 0 (J k 1 0 s) = 0 := by
    rw [h_f_comm, hh, map_smul, add_zero]; module
  refine ⟨?_, ?_, f0_cube_eq_zero s he hh⟩
  · rw [e0_f0_comm, he₁, hh₁, add_zero, map_smul]
  · rw [h_f_comm, hh₁, map_zero, zero_add, add_zero]

theorem Q0_bottom :
    Q0 k hk (J k 1 0 (J k 1 0 s)) = (2 / (k + 2) - 1) • J k 1 0 (J k 1 0 s) := by
  obtain ⟨he₀, hh₀, hf₀⟩ := triplet_relations k s he hh
  have hS₀ : SingP k (J k 1 0 (J k 1 0 s)) := (hS.zeroMode 1).zeroMode 1
  simp only [Q0]
  rw [Lm_zero_singP k hk _ hS₀]
  simp only [Fin.sum_univ_three, kappaInv]
  simp only [zero_smul, add_zero, zero_add, one_smul]
  rw [he₀, hf₀, hh₀, map_zero, map_smul, map_smul, hh₀, dualCoxeter]
  simp only [smul_add, smul_smul, add_zero]
  rw [← add_smul, ← add_smul]
  congr 1
  field_simp
  ring

theorem Q1_bottom : Q1 k hk (J k 1 0 (J k 1 0 s)) = 0 := by
  obtain ⟨_, hh₀, hf₀⟩ := triplet_relations k s he hh
  have hS₀ : SingP k (J k 1 0 (J k 1 0 s)) := (hS.zeroMode 1).zeroMode 1
  simp only [Q1]
  rw [Lm_pos_singP k hk _ hS₀ le_rfl, hS₀ 2 1 le_rfl, hf₀, hh₀, map_smul, hf₀]
  simp

theorem Q2_bottom : Q2 k hk (J k 1 0 (J k 1 0 s)) = 0 := by
  obtain ⟨_, hh₀, hf₀⟩ := triplet_relations k s he hh
  have hS₀ : SingP k (J k 1 0 (J k 1 0 s)) := (hS.zeroMode 1).zeroMode 1
  simp only [Q2]
  rw [Lm_pos_singP k hk _ hS₀ (by norm_num), hS₀ 2 2 (by norm_num), hS₀ 1 1 le_rfl, hf₀,
    hS₀ 2 1 le_rfl, hh₀, map_smul, hS₀ 1 1 le_rfl, map_smul, hf₀]
  simp

/-- **The slice image of the bottom vector is in the maximal ideal** of `Vir^{c_DS(k)}`,
for every level `k ≠ 0, -2`. -/
theorem bottom_mem_maxIdealVir (hk0 : k ≠ 0) :
    ∀ a, Wslice (cDS k) k hk (J k 1 0 (J k 1 0 s)) a ∈ maxIdealVir (cDS k) := by
  obtain ⟨_, hh₀, _⟩ := triplet_relations k s he hh
  set t₀ := J k 1 0 (J k 1 0 s)
  set v := W1 (cDS k) k hk t₀
  have hμ : (2 / (k + 2) - 1 : ℂ) ≠ 0 := by
    intro h
    apply hk0
    have : (2 : ℂ) / (k + 2) = 1 := by linear_combination h
    rw [div_eq_one_iff_eq hk] at this
    linear_combination -this
  have h0 : Lop (cDS k) 0 v = (2 / (k + 2) - 1 : ℂ) • v := by
    rw [← W1_Q0, Q0_bottom k hk s hS he hh, map_smul]
  have h1 : Lop (cDS k) 1 v = 0 := by
    rw [← W1_Q1, Q1_bottom k hk s hS he hh, map_zero]
  have h2 : Lop (cDS k) 2 v = 0 := by
    rw [← W1_Q2, Q2_bottom k hk s hS he hh, map_zero]
  have hv := singular_mem_maxIdealVir_of_L0 (cDS k) v _ hμ h0 h1 h2
  have hsingle := Wslice_eq_single_of_h0 (cDS k) k hk t₀ 1 (by rw [hh₀]; norm_num)
  intro a
  rw [hsingle, Finsupp.single_apply]
  split_ifs
  · exact hv
  · exact Submodule.zero_mem _

end Bottom

/-! ## §5  The slice Arakawa property -/

/-- **The slice Arakawa property from maximal generation alone.**  At any level `k ≠ 0`
whose maximal ideal is generated by a horizontal-highest positive-singular vector of `sl₂`-weight
`2`, the slice map sends the maximal ideal of `V^k(sl₂)` into that of `Vir^{c_DS(k)}`. -/
theorem sliceArakawa_of_maximalGeneration (L : CosetLevels) (hk0 : L.kA ≠ 0)
    (s : WakModule L.kA)
    (hgen : AffineVacuumMaximalSubmoduleGenerated L.kA L.aNoncritical s)
    (hS : SingP L.kA s) (he : J L.kA 0 0 s = 0) (hh : J L.kA 2 0 s = (2 : ℂ) • s) :
    SliceArakawa (dsSliceMap (cDS L.kA) L) :=
  sliceArakawa_of_singularBottom _ L s hgen hS he hh
    (bottom_mem_maxIdealVir L.kA L.aNoncritical s hS he hh hk0)

/-- The two-series central charge is the Drinfeld–Sokolov charge of the next boundary level. -/
theorem twoSeries_c_eq_cDS (m : ℕ) :
    (twoSeriesLevels m).c = cDS (twoSeriesLevels (m + 1)).kA := by
  rw [twoSeriesLevels_c, twoSeriesLevels_kA, boundaryCharge, cDS, level_eq]
  unfold boundaryMinimalCentralCharge
  have h1 : ((2 * (m + 1) + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * (m + 1))
  push_cast at h1 ⊢
  have h2 : (-2 + 2 / (2 * ((m : ℂ) + 1) + 1) + 2) ≠ 0 := by
    rw [show (-2 : ℂ) + 2 / (2 * ((m : ℂ) + 1) + 1) + 2 = 2 / (2 * ((m : ℂ) + 1) + 1) by ring]
    exact div_ne_zero two_ne_zero h1
  field_simp
  ring

theorem twoSeries_kA_ne_zero (m : ℕ) : (twoSeriesLevels (m + 1)).kA ≠ 0 := by
  rw [twoSeriesLevels_kA, level_eq]
  intro h
  have h1 : ((2 * (m + 1) + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * (m + 1))
  have : (2 : ℂ) = 2 * ((2 * (m + 1) + 1 : ℕ) : ℂ) := by
    field_simp at h
    linear_combination h
  have h3 : ((2 * (m + 1) + 1 : ℕ) : ℂ) = 1 := by linear_combination -this / 2
  have h4 : (2 * (m + 1) + 1 : ℕ) = 1 := by exact_mod_cast h3
  omega

/-- **`SliceArakawa` for the two series**, from maximal generation alone. -/
theorem twoSeries_sliceArakawa_of_maximalGeneration (m : ℕ)
    (s : WakModule (twoSeriesLevels (m + 1)).kA)
    (hgen : AffineVacuumMaximalSubmoduleGenerated (twoSeriesLevels (m + 1)).kA
      (twoSeriesLevels (m + 1)).aNoncritical s)
    (hS : SingP (twoSeriesLevels (m + 1)).kA s)
    (he : J (twoSeriesLevels (m + 1)).kA 0 0 s = 0)
    (hh : J (twoSeriesLevels (m + 1)).kA 2 0 s = (2 : ℂ) • s) :
    SliceArakawa (dsSliceMap (twoSeriesLevels m).c (twoSeriesLevels (m + 1))) := by
  rw [twoSeries_c_eq_cDS]
  exact sliceArakawa_of_maximalGeneration _ (twoSeries_kA_ne_zero m) s hgen hS he hh

/-- **Affine GU ⇒ GU of `M(2, 2m+5)`**, `#print axioms`-clean, conditional on `hA`,
Adamović–Milas generation of the maximal ideal of `V^{k}(sl₂)`, `k = -2 + 2/(2m+3)`, by a
horizontal-highest positive-singular vector `s` of `sl₂`-weight `2`, and `JetPoincareCoreT0`. -/
theorem twoSeries_gradedUnitary_of_maximalGeneration (m : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels (m + 1)))
      (affineRealStructure (twoSeriesLevels (m + 1))) (affineFlag (twoSeriesLevels (m + 1))))
    (s : WakModule (twoSeriesLevels (m + 1)).kA)
    (hgen : AffineVacuumMaximalSubmoduleGenerated (twoSeriesLevels (m + 1)).kA
      (twoSeriesLevels (m + 1)).aNoncritical s)
    (hS : SingP (twoSeriesLevels (m + 1)).kA s)
    (he : J (twoSeriesLevels (m + 1)).kA 0 0 s = 0)
    (hh : J (twoSeriesLevels (m + 1)).kA 2 0 s = (2 : ℂ) • s)
    (h : PoincareZero.JetPoincareCoreT0 (m + 1)) :
    VirGradedUnitary (twoSeriesLevels (m + 1)).c (targetRealStructure (twoSeriesLevels (m + 1))) :=
  twoSeries_gradedUnitary_of_sliceArakawa m hA
    (twoSeries_sliceArakawa_of_maximalGeneration m s hgen hS he hh) h

/-- The same, from the repository's Adamović–Milas package. -/
theorem twoSeries_gradedUnitary_of_adamovicMilas (m : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels (m + 1)))
      (affineRealStructure (twoSeriesLevels (m + 1))) (affineFlag (twoSeriesLevels (m + 1))))
    (D : AffineSl2BoundarySingularFamily.AdamovicMilasData (twoSeriesLevels (m + 1)).kA (m + 1))
    (h : PoincareZero.JetPoincareCoreT0 (m + 1)) :
    VirGradedUnitary (twoSeriesLevels (m + 1)).c (targetRealStructure (twoSeriesLevels (m + 1))) :=
  twoSeries_gradedUnitary_of_maximalGeneration m hA D.vector D.maximalSubmodule
    D.positiveSingular D.horizontalRaising D.horizontalCharge h

end

end VOA.TwoSeries.SliceMap
