/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSliceMapVir
import VOA.Examples.TwoSeriesDSSlice

/-!
# The Drinfeld–Sokolov slice map, constructed

This file discharges the `DSSliceMap` input of `TwoSeriesDSSlice`: for **every** central charge
`c` and every level datum `L` (non-critical level `k = L.kA`) we construct

`dsSliceMap c L : DSSliceMap c L`.

## The construction

1. `W₀ : V^k(sl₂) → E = ℂ[X₀, X₁, …]` (`TwoSeriesSliceMapWhittaker`) is the Whittaker
   coinvariant map: on the `(f, h, e)`-ordered PBW basis, `f^λ h^ν e^μ|0⟩ ↦ χ(f^λ)[ν = 0] X^μ`.
   It satisfies the exact Whittaker relations and kills the Whittaker ideal `Σ (x - χ(x)) V`.
2. The creation Sugawara modes normalise that ideal, so `W₀ ∘ L_n = Lt n ∘ W₀`
   (`TwoSeriesSliceMapSugawara.W0_Lm`); the descended `Lt (-j-2)` is triangular with leading term
   `cL · X_j`, `cL = -1/(k+2)` (`Lt_tri`).
3. `φ : Vir^c → E` (Virasoro creation words ↦ `Lt`-words on `1`) is a linear isomorphism
   intertwining `L_{-n-2}` with `Lt(-n-2)`; `ψ = φ⁻¹` maps total degree `≤ d` into Virasoro
   length `≤ d` (`TwoSeriesSliceMapVir`).
4. `W₁ = ψ ∘ W₀ : V^k → Vir^c`, and `W = chargeLift W₁` places the image of a word of charge
   `#f - #e = a` in degree `a` (the Rees grading).

## The fields

* `vacuum`, `f_one`, `f_high` — exact (Whittaker relations of `W₀`);
* `sugawara` — **exact** (the difference is `0`): `W ∘ L_{-m-2} = L_{-m-2} ∘ W`;
* `filtered`, `current_lower` — from the Kazhdan filtration lemma: a corrected word with
  `#e, #h, #T` letters has `W₀`-degree `≤ #e + #T + ⌊#h/2⌋`, and `h`-led words go to `0`.

## Updated endpoint

`twoSeries_gradedUnitary_of_sliceArakawa` — **Affine GU ⇒ GU of `M(2, 2n+3)`**, conditional only on
`hA`, `SliceArakawa (dsSliceMap …)` and the jet-ideal Poincaré input `JetPoincareCoreT0`.

Everything is proved; no new axiom.  The only universal-object inputs used are the library's
proved PBW results (`affineSl2PBWBasis`'s Wakimoto independence, re-run here for the new letter
order) and the Virasoro partition basis.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA VOA.AffineVOA.CorrectedR VOA.AdamovicSymbol MvPolynomial VOA.VirModule
open VOA.TwoSeries.DSSlice
open VOA.SymbolModel VOA.AffineVOA.Inst VOA.TwoSeries.StrictModel
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

variable (c k : ℂ) (hk : k + 2 ≠ 0)

/-- The ungraded slice map `W₁ = ψ ∘ W₀`. -/
def W1 : WakModule k →ₗ[ℂ] VirUniv c := (psi c k hk).toLinearMap.comp (W0 k hk)

/-- The graded slice map. -/
def Wslice : WakModule k →ₗ[ℂ] (ℤ →₀ VirUniv c) := chargeLift k hk (W1 c k hk)

theorem rword_span_eq_top : Submodule.span ℂ (Set.range (rword k)) = ⊤ := by
  rw [eq_top_iff, ← Fvec_span_eq_top k]
  exact Submodule.span_mono (by rintro _ ⟨μ, rfl⟩; exact ⟨_, rfl⟩)

theorem W1_rword_mem (l : List RLetter) : W1 c k hk (rword k l) ∈ vLen c (Kl l / 2) :=
  psi_Dg c k hk (W0_rword_mem k hk l)

theorem W1_KC {p : ℕ} {q : ℤ} {y : WakModule k} (hy : y ∈ KC k p q) :
    W1 c k hk y ∈ vLen c (p / 2) :=
  psi_Dg c k hk (W0_KC k hk hy)

theorem Wslice_vacuum : Wslice c k hk (vacuumA k) = Finsupp.single 0 (vacVec c) := by
  rw [← rword_nil k, Wslice, chargeLift_rword, chl_nil, W1, LinearMap.comp_apply, rword_nil,
    W0_vacuum]
  simp [psi_one]

theorem J_fOne_rword (l : List RLetter) : J k 1 (-1) (rword k l) = rword k (toLex (0, 0) :: l) := by
  rw [rword_cons]
  simp [rankColor]

theorem Wslice_f_one (y : WakModule k) (a : ℤ) :
    Wslice c k hk (J k 1 (-1) y) a = -(Wslice c k hk y (a - 1)) := by
  have h : (Finsupp.lapply a).comp ((Wslice c k hk).comp (J k 1 (-1))) =
      -((Finsupp.lapply (a - 1)).comp (Wslice c k hk)) := by
    apply LinearMap.ext_on_range (rword_span_eq_top k)
    intro l
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, Finsupp.lapply_apply]
    rw [J_fOne_rword, Wslice, chargeLift_rword, chargeLift_rword, chl_cons, W1,
      LinearMap.comp_apply, LinearMap.comp_apply, rword_cons]
    simp only [col_toLex, dep_toLex, rk_toLex, rankColor]
    rw [show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num, W0_J_fOne, map_neg]
    simp only [Finsupp.single_apply, Fin.val_zero, Nat.cast_zero, sub_zero]
    by_cases h1 : 1 + chl l = a
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega), neg_zero]
  exact LinearMap.congr_fun h y

theorem Wslice_f_high (j : ℕ) (y : WakModule k) :
    Wslice c k hk (J k 1 (-(j : ℤ) - 2) y) = 0 := by
  have h : (Wslice c k hk).comp (J k 1 (-(j : ℤ) - 2)) = 0 := by
    apply LinearMap.ext_on_range (rword_span_eq_top k)
    intro l
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    have hw : J k 1 (-(j : ℤ) - 2) (rword k l) = rword k (toLex (0, j + 1) :: l) := by
      rw [rword_cons]
      simp only [col_toLex, dep_toLex, rankColor]
      congr 2
      push_cast; ring
    rw [hw, Wslice, chargeLift_rword]
    simp only [W1, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hw, W0_J_fHigh, map_zero, Finsupp.single_zero]
  exact LinearMap.congr_fun h y

/-! ## Corrected words -/

/-- Kazhdan weight of a corrected letter (`e = 2`, `h = 1`, `f = 0`, `T = 2`). -/
def kazL : Generator × ℕ → ℕ
  | (.current b, _) => ((colorRank b : Fin 3) : ℕ)
  | (.sugawara, _) => 2

/-- Charge of a corrected letter (`f = 1`, `h = 0`, `e = -1`, `T = 0`). -/
def chL : Generator × ℕ → ℤ
  | (.current b, _) => 1 - ((colorRank b : Fin 3) : ℕ)
  | (.sugawara, _) => 0

/-- Corrected words lie in their Kazhdan–charge span. -/
theorem correctedWordState_mem_KC :
    ∀ w : List (Generator × ℕ),
      correctedWordState k hk w ∈ KC k (w.map kazL).sum (w.map chL).sum
  | [] => rword_mem_KC k (l := []) le_rfl rfl
  | (g, m) :: w => by
      have ih := correctedWordState_mem_KC w
      rw [correctedWordState_cons']
      cases g with
      | current b =>
          rw [letterOp_current]
          have h := J_letter_KC k (toLex (colorRank b, m)) ih
          simp only [col_toLex, rankColor_colorRank, dep_toLex, rk_toLex] at h
          simp only [List.map_cons, List.sum_cons, kazL, chL]
          convert h using 2 <;> ring
      | sugawara =>
          rw [letterOp_sugawara]
          have h := Lm_KC k hk m ih
          simp only [List.map_cons, List.sum_cons, kazL, chL]
          convert h using 2 <;> ring

theorem kazL_le (l : Generator × ℕ) : kazL l ≤ 2 * ((1 : ℤ) - chL l).toNat := by
  obtain ⟨g, m⟩ := l
  cases g with
  | current b => fin_cases b <;> simp [kazL, chL, colorRank]
  | sugawara => simp [kazL, chL]

theorem one_sub_chL_nonneg (l : Generator × ℕ) : 0 ≤ (1 : ℤ) - chL l := by
  obtain ⟨g, m⟩ := l
  cases g with
  | current b =>
      simp only [chL]
      have : ((colorRank b : Fin 3) : ℕ) < 3 := (colorRank b).isLt
      omega
  | sugawara => simp [chL]

theorem length_sub_charge (w : List (Generator × ℕ)) :
    (w.length : ℤ) - (w.map chL).sum = (w.map fun l => (1 : ℤ) - chL l).sum := by
  induction w with
  | nil => simp
  | cons l w ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; push_cast; linarith

theorem kaz_half_le (w : List (Generator × ℕ)) :
    (w.map kazL).sum / 2 ≤ ((w.length : ℤ) - (w.map chL).sum).toNat := by
  rw [length_sub_charge]
  have h1 : ∀ w : List (Generator × ℕ), (w.map kazL).sum ≤
      2 * ((w.map fun l => (1 : ℤ) - chL l).sum).toNat := by
    intro w
    induction w with
    | nil => simp
    | cons l w ih =>
        simp only [List.map_cons, List.sum_cons]
        have hl := kazL_le l
        have hn := one_sub_chL_nonneg l
        have hs : 0 ≤ (w.map fun l => (1 : ℤ) - chL l).sum :=
          List.sum_nonneg fun x hx => by
            obtain ⟨l', _, rfl⟩ := List.mem_map.mp hx
            exact one_sub_chL_nonneg l'
        omega
  have := h1 w
  omega

/-! ## The slice map -/

theorem Wslice_KC {p : ℕ} {q : ℤ} {y : WakModule k} (hy : y ∈ KC k p q) :
    Wslice c k hk y = Finsupp.single q (W1 c k hk y) :=
  chargeLift_KC k hk _ hy

theorem single_mem_vLenZ {q a : ℤ} {v : VirUniv c} {b : ℤ} (hv : a = q → v ∈ vLenZ c b) :
    Finsupp.single q v a ∈ vLenZ c b := by
  rw [Finsupp.single_apply]
  split_ifs with h
  · exact hv h.symm
  · exact Submodule.zero_mem _

theorem vLen_le_vLenZ {d : ℕ} {b : ℤ} (h : (d : ℤ) ≤ b) : vLen c d ≤ vLenZ c b := by
  rw [vLenZ, if_pos (by omega)]
  exact vLen_mono c (by omega)

theorem Wslice_filtered (w : List (Generator × ℕ)) (a : ℤ) :
    Wslice c k hk (correctedWordState k hk w) a ∈ vLenZ c ((w.length : ℤ) - a) := by
  rw [Wslice_KC c k hk (correctedWordState_mem_KC k hk w)]
  refine single_mem_vLenZ c fun ha => ?_
  subst ha
  refine vLen_le_vLenZ c ?_ (W1_KC c k hk (correctedWordState_mem_KC k hk w))
  have h1 := kaz_half_le w
  have h2 : 0 ≤ (w.length : ℤ) - (w.map chL).sum := by
    rw [length_sub_charge]
    exact List.sum_nonneg fun x hx => by
      obtain ⟨l', _, rfl⟩ := List.mem_map.mp hx
      exact one_sub_chL_nonneg l'
  omega

theorem Wslice_current_lower (b : Fin 3) (hb : b ≠ 1) (m : ℕ) (w : List (Generator × ℕ))
    (a : ℤ) :
    Wslice c k hk (correctedWordState k hk ((Generator.current b, m) :: w)) a ∈
      vLenZ c ((w.length : ℤ) - a) := by
  have hmem := correctedWordState_mem_KC k hk ((Generator.current b, m) :: w)
  rw [Wslice_KC c k hk hmem]
  refine single_mem_vLenZ c fun ha => ?_
  subst ha
  rw [correctedWordState_cons', letterOp_current]
  fin_cases b
  · -- `e`: one Kazhdan step costs one Virasoro length
    have hw := correctedWordState_mem_KC k hk w
    have hJ := J_letter_KC k (toLex (2, m)) hw
    simp only [col_toLex, dep_toLex, rk_toLex, rankColor] at hJ
    refine vLen_le_vLenZ c ?_ (W1_KC c k hk hJ)
    have h1 := kaz_half_le w
    have h2 : 0 ≤ (w.length : ℤ) - (w.map chL).sum := by
      rw [length_sub_charge]
      exact List.sum_nonneg fun x hx => by
        obtain ⟨l', _, rfl⟩ := List.mem_map.mp hx
        exact one_sub_chL_nonneg l'
    simp only [List.map_cons, List.sum_cons, chL]
    change ((((w.map kazL).sum + 2) / 2 : ℕ) : ℤ) ≤ (w.length : ℤ) - (1 - 2 + (w.map chL).sum)
    generalize (w.map kazL).sum = K at *
    generalize (w.map chL).sum = Q at *
    omega
  · exact absurd rfl hb
  · -- `h`: killed by the Whittaker relation
    simp only [W1, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h0 := W0_J_h k hk m (correctedWordState k hk w)
    rw [show (-(m : ℤ) - 1) = -(m : ℤ) - 1 from rfl] at h0
    convert Submodule.zero_mem (vLenZ c _)
    convert congrArg (psi c k hk) h0 using 1
    simp

theorem Wslice_sugawara (m : ℕ) (w : List (Generator × ℕ)) (a : ℤ) :
    Wslice c k hk (correctedWordState k hk ((Generator.sugawara, m) :: w)) a -
      Lop c (-(m : ℤ) - 2) (Wslice c k hk (correctedWordState k hk w) a) = 0 := by
  have hw := correctedWordState_mem_KC k hk w
  have hT := Lm_KC k hk m hw
  rw [correctedWordState_cons', letterOp_sugawara]
  change Wslice c k hk (Lm k hk (-(m : ℤ) - 2) _) a - _ = 0
  rw [Wslice_KC c k hk hT, Wslice_KC c k hk hw]
  simp only [W1, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [W0_Lm k hk (by omega), psi_Lt]
  simp only [Finsupp.single_apply]
  split_ifs <;> simp

/-- **The Drinfeld–Sokolov slice map**, for every central charge and every non-critical
level datum. -/
def dsSliceMap (L : CosetLevels) : DSSliceMap c L where
  W := Wslice c L.kA L.aNoncritical
  vacuum := Wslice_vacuum c L.kA L.aNoncritical
  f_one := Wslice_f_one c L.kA L.aNoncritical
  f_high := Wslice_f_high c L.kA L.aNoncritical
  filtered := Wslice_filtered c L.kA L.aNoncritical
  current_lower := Wslice_current_lower c L.kA L.aNoncritical
  sugawara := fun m w a => by
    rw [Wslice_sugawara c L.kA L.aNoncritical m w a]
    exact Submodule.zero_mem _

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, with the slice map constructed:
`#print axioms`-clean, conditional only on `hA`, the Arakawa property of the constructed slice
map, and the jet-ideal Poincaré input `JetPoincareCoreT0 (m+1)`. -/
theorem twoSeries_gradedUnitary_of_sliceArakawa (m : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels (m + 1)))
      (affineRealStructure (twoSeriesLevels (m + 1))) (affineFlag (twoSeriesLevels (m + 1))))
    (hS : SliceArakawa (dsSliceMap (twoSeriesLevels m).c (twoSeriesLevels (m + 1))))
    (h : PoincareZero.JetPoincareCoreT0 (m + 1)) :
    VirGradedUnitary (twoSeriesLevels (m + 1)).c (targetRealStructure (twoSeriesLevels (m + 1))) :=
  twoSeries_gradedUnitary_of_dsSlice m hA _ hS h

end

end VOA.TwoSeries.SliceMap
