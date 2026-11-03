/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieCocycle
import VOA.DeligneAudit.E7LieFacts

/-!
# The cert `E₇` basis inside the lattice Lie algebra `e7Lie = (V_{E₇})₁`

`xs : Fin 133 → e7Lie` realizes the basis of `casimir_cert/cert_E7.json`: `xs i = α_i(-1)𝟙` (`i < 7`),
`xs a = u_a f(wt a) e^{wt a}` for the 126 roots (`f` the coboundary sign of `E7LieCocycle`).
`bracket_of_pairOK`: whenever the kernel check `pairOK a b` holds, `⁅xs a, xs b⁆ = spL (sL a b)`, the
cert structure constants (as a sparse sum).
-/

namespace VOA.DeligneAudit.E7Lie

open VOA VOA.LatGen VOA.LatGen.Screen VOA.IntegralLattice HeisenbergN VOA.CartanLattices
  VOA.AffineGeneral.LatticeLie VOA.AffineGeneral.CartanSimple

noncomputable section

/-! ## Root vectors and coroots for arbitrary lattice vectors -/

theorem mem_one_of_norm (v : Lat) (hv : formZ v v = 2) :
    latChargeGen e7 v ∈ (latticeVOAGen e7 e7_even e7_posDef).grading 1 :=
  latChargeGen_mem_grading_one e7 e7_even e7_posDef (by rw [e7_form_eq]; exact hv)

/-- `e^v` for a norm-two `v`. -/
def ev (v : Lat) (hv : formZ v v = 2) : e7Lie := ⟨latChargeGen e7 v, mem_one_of_norm v hv⟩

/-- `v(-1)𝟙`. -/
def hst (v : Lat) : e7Lie := ⟨hSt e7 v, hSt_mem_gradingLatGen e7 v⟩

theorem ev_congr {v w : Lat} (h : v = w) (hv : formZ v v = 2) (hw : formZ w w = 2) :
    ev v hv = ev w hw := by
  subst h; rfl

theorem hst_ev (v w : Lat) (hw : formZ w w = 2) :
    ⁅hst v, ev w hw⁆ = (formZ v w : ℂ) • ev w hw := by
  apply Subtype.ext
  show (latticeVOAGen e7 e7_even e7_posDef).smul (hSt e7 v) 0
      (latStateGen e7 (vacuumN (rank e7)) w) = _
  rw [smul_hSt_zero_latStateGen, e7_form_eq]
  rfl

theorem hst_hst (v w : Lat) : ⁅hst v, hst w⁆ = 0 := by
  apply Subtype.ext
  show (latticeVOAGen e7 e7_even e7_posDef).smul (hSt e7 v) 0 (latStateGen e7 (vSchur e7 w 1) 0) = 0
  rw [smul_hSt_zero_latStateGen, map_zero, Int.cast_zero, zero_smul]

theorem ev_ev_of_nonneg (v w : Lat) (hv : formZ v v = 2) (hw : formZ w w = 2)
    (h : 0 ≤ formZ v w) : ⁅ev v hv, ev w hw⁆ = 0 := by
  apply Subtype.ext
  show mode (YfullGen e7 e7_even e7_posDef (latChargeGen e7 v)) 0 (latChargeGen e7 w) = 0
  rw [← Qscr_eq_mode_YfullGen e7 e7_even e7_posDef,
    Qscr_latChargeGen_of_nonneg e7 (by rw [e7_form_eq]; exact h)]

theorem ev_ev_of_neg_one (v w : Lat) (hv : formZ v v = 2) (hw : formZ w w = 2)
    (hvw : formZ (v + w) (v + w) = 2) (h : formZ v w = -1) :
    ⁅ev v hv, ev w hw⁆ = latticeCocycle e7 v w • ev (v + w) hvw := by
  apply Subtype.ext
  show mode (YfullGen e7 e7_even e7_posDef (latChargeGen e7 v)) 0 (latChargeGen e7 w) =
    latticeCocycle e7 v w • latChargeGen e7 (v + w)
  rw [← Qscr_eq_mode_YfullGen e7 e7_even e7_posDef, Qscr_latChargeGen, EEVec_vacuum, e7_form_eq,
    h, if_pos (by norm_num)]
  norm_num [vSchur_zero]
  rfl

theorem ev_ev_neg (v : Lat) (hv : formZ v v = 2) (hv' : formZ (-v) (-v) = 2) :
    ⁅ev v hv, ev (-v) hv'⁆ = latticeCocycle e7 v (-v) • hst v := by
  apply Subtype.ext
  show mode (YfullGen e7 e7_even e7_posDef (latChargeGen e7 v)) 0 (latChargeGen e7 (-v)) = _
  rw [← Qscr_eq_mode_YfullGen e7 e7_even e7_posDef]
  exact Qscr_latChargeGen_neg e7 (by rw [e7_form_eq]; exact hv)

/-- `v ↦ v(-1)𝟙` is additive. -/
def hstHom : Lat →+ e7Lie where
  toFun := hst
  map_zero' := Subtype.ext (hSt_zero e7)
  map_add' v w := Subtype.ext (hSt_add e7 v w)

theorem hst_decomp (v : Lat) : hst v = ∑ i : Fin 7, (v i : ℂ) • hst (Pi.single i 1) := by
  have h := congrArg hstHom (lat_decomp v)
  rw [map_sum] at h
  simp only [map_zsmul] at h
  change hst v = _ at h
  rw [h]
  simp only [← Int.cast_smul_eq_zsmul ℂ]
  rfl

/-! ## The cert basis -/

/-- The Cartan index of `i : Fin 7`. -/
def cI (i : Fin 7) : Fin 133 := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by decide)⟩

theorem hvec_cI (i : Fin 7) : hvec (cI i) = Pi.single i 1 := by
  ext j
  simp only [hvec, cI, Pi.single_apply]
  split_ifs <;> simp_all [Fin.ext_iff]

/-- The root vector attached to an index (`e^{wt 7}` on the Cartan indices, unused there). -/
def evR (a : Fin 133) : e7Lie := ev (wtR a) (wtR_norm a)

/-- **The cert basis of `e7Lie`.** -/
def xs (a : Fin 133) : e7Lie :=
  if a.val < 7 then hst (hvec a) else ((u a : ℂ) * f (wt a)) • evR a

theorem xs_cartan (a : Fin 133) (h : a.val < 7) : xs a = hst (hvec a) := by
  rw [xs, if_pos h]

theorem xs_cI (i : Fin 7) : xs (cI i) = hst (Pi.single i 1) := by
  rw [xs_cartan _ (by simp [cI]), hvec_cI]

theorem xs_root (a : Fin 133) (h : 7 ≤ a.val) :
    xs a = ((u a : ℂ) * f (wt a)) • ev (wt a) (wt_norm a h) := by
  rw [xs, if_neg (by omega), evR, ev_congr (wtR_root a h) (wtR_norm a) (wt_norm a h)]

theorem sgn_eq (n : ℤ) : ((sgn n : ℤ) : ℂ) = (-1 : ℂ) ^ n := by
  unfold sgn
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [if_pos (by omega), hk, ← two_mul, zpow_mul]; norm_num
  · rw [if_neg (by omega), hk, zpow_add₀ (by norm_num), zpow_mul]; norm_num

theorem u_sq (a : Fin 133) : (u a : ℂ) * (u a : ℂ) = 1 := by
  exact_mod_cast u_mul_self a

/-! ## Sparse sums -/

/-- `∑ k • x_c` over a sparse list. -/
def spL (l : List (Fin 133 × ℤ)) : e7Lie := (l.map fun t => (t.2 : ℂ) • xs t.1).sum

theorem spL_nil : spL [] = 0 := rfl

theorem spL_single1 (c : Fin 133) (k : ℤ) : spL (single1 c k) = (k : ℂ) • xs c := by
  unfold single1 spL
  split_ifs with h
  · simp [h]
  · simp

theorem spL_filterMap (co : ℤ) (v : Lat) (L : List (Fin 7)) :
    ((L.filterMap fun i => if co * v i = 0 then none else
        some (cI i, co * v i)).map fun t => (t.2 : ℂ) • xs t.1).sum =
      (L.map fun i => ((co * v i : ℤ) : ℂ) • xs (cI i)).sum := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      rw [List.filterMap_cons, List.map_cons, List.sum_cons]
      split_ifs with h
      · simp only [ih, h, Int.cast_zero, zero_smul, zero_add]
      · simp only [List.map_cons, List.sum_cons, ih]

theorem spL_cartanList (co : ℤ) (v : Lat) :
    spL (cartanList co v) = ∑ i : Fin 7, ((co * v i : ℤ) : ℂ) • xs (cI i) := by
  unfold spL cartanList
  exact (spL_filterMap co v (List.finRange 7)).trans (by rw [← List.ofFn_eq_map, List.sum_ofFn])

/-! ## The brackets -/

theorem cartan_xs (i : Fin 7) (b : Fin 133) :
    ⁅xs (cI i), xs b⁆ = (formZ (hvec (cI i)) (wt b) : ℂ) • xs b := by
  by_cases hb : b.val < 7
  · rw [xs_cartan _ (by simp [cI]), xs_cartan b hb, hst_hst, wt_cartan b hb]
    simp [formZ]
  · rw [xs_cartan _ (by simp [cI]), xs_root b (by omega), lie_smul, hst_ev, smul_comm]

/-- **The lattice-model bracket table**, given the kernel check `pairOK a b`. -/
theorem bracket_of_pairOK (a b : Fin 133) (hab : pairOK a b = true) :
    ⁅xs a, xs b⁆ = spL (sL a b) := by
  unfold pairOK at hab
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
  obtain ⟨hmodel, hroot⟩ := hab
  rw [hmodel]
  by_cases ha : a.val < 7
  · by_cases hb : b.val < 7
    · rw [xs_cartan a ha, xs_cartan b hb, hst_hst, modelL, if_pos ha, if_pos hb, spL_nil]
    · rw [modelL, if_pos ha, if_neg hb, spL_single1, xs_cartan a ha, xs_root b (by omega),
        lie_smul, hst_ev, smul_comm]
  · have ha' : 7 ≤ a.val := by omega
    by_cases hb : b.val < 7
    · rw [modelL, if_neg ha, if_pos hb, spL_single1, xs_cartan b hb, xs_root a ha', smul_lie,
        ← lie_skew, hst_ev, smul_neg, smul_comm, Int.cast_neg, neg_smul]
    · have hb' : 7 ≤ b.val := by omega
      rw [if_pos ⟨ha', hb'⟩] at hroot
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hroot
      obtain ⟨⟨hge, hopp⟩, htgt⟩ := hroot
      rw [modelL, if_neg ha, if_neg hb, xs_root a ha', xs_root b hb', smul_lie, lie_smul, smul_smul]
      by_cases h2 : formZ (wt a) (wt b) = -2
      · rw [if_pos h2] at hopp ⊢
        simp only [decide_eq_true_eq] at hopp
        rw [spL_cartanList, ev_congr hopp (wt_norm b hb') (by rw [← hopp]; exact wt_norm b hb'),
          ev_ev_neg, smul_smul, hst_decomp, Finset.smul_sum]
        have hcob := cocycle_coboundary (wt a) (-wt a)
        rw [add_neg_cancel, f_zero, mul_one, ← hopp] at hcob
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [xs_cI, smul_smul, ← hopp]
        congr 1
        rw [Int.cast_mul, Int.cast_mul, Int.cast_mul, sgn_eq, ← hcob]
        ring
      · rw [if_neg h2]
        by_cases h1 : formZ (wt a) (wt b) = -1
        · rw [if_pos h1] at htgt ⊢
          simp only [decide_eq_true_eq] at htgt
          obtain ⟨hc4, hcw⟩ := htgt
          have hn : formZ (wt a + wt b) (wt a + wt b) = 2 := by rw [← hcw]; exact wt_norm _ hc4
          rw [spL_single1, ev_ev_of_neg_one _ _ _ _ hn h1, smul_smul, xs_root _ hc4, smul_smul,
            ev_congr hcw (wt_norm _ hc4) hn]
          congr 1
          have hcob := cocycle_coboundary (wt a) (wt b)
          rw [hcw, Int.cast_mul, Int.cast_mul, Int.cast_mul, sgn_eq]
          have hu := u_sq (tgt a b)
          linear_combination (↑(u a) * ↑(u b)) * hcob -
            ((u a : ℂ) * u b * (-1 : ℂ) ^ ep (wt a) (wt b) * f (wt a + wt b)) * hu
        · rw [if_neg h1]
          have h0 : 0 ≤ formZ (wt a) (wt b) := by omega
          rw [ev_ev_of_nonneg _ _ _ _ h0, smul_zero, spL_nil]

end

end VOA.DeligneAudit.E7Lie
