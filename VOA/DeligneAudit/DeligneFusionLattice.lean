import VOA.AffineGeneral.CartanLatticeSimple
import VOA.Moonshine.TrialitySl2
import VOA.Moonshine.TrialityTheta
import VOA.Moonshine.LatticeMorphRigid
import VOA.Examples.LatticeCharge
import VOA.Core.DeformationLiftedModes
import VOA.DeligneAudit.DeligneFusionRel

/-!
# The `sl₃[t]`-current module on the lattice VOA `V_{A₂}` (Frenkel–Kac, by hand)

Eight weight-one states of `V_{A₂}` whose `0`-products reproduce `AffineSl3.bracketTable`:
root vectors `e^{±α}` rescaled by FLM cocycle signs, and the coroots `hSt α = α(-1)𝟙`.  Their
non-negative modes give a `CurrentModule (bracketTable)` on `LatModuleGen a2`.
-/

namespace VOA.DeligneAudit.FusionLattice

open VOA VOA.LatGen VOA.LatGen.Screen VOA.IntegralLattice VOA.CartanLattices HeisenbergN

noncomputable section

/-- The lattice VOA `V_{A₂}`. -/
abbrev WA : VertexOperatorAlgebra (LatModuleGen a2) := latticeVOAGen a2 a2_even a2_posDef

/-- Coordinates: `a2.carrier = Fin 2 → ℤ`. -/
def lv (a b : ℤ) : a2.carrier := ![a, b]

theorem form_lv (a b c d : ℤ) : a2.form (lv a b) (lv c d) = 2 * a * c - a * d - b * c + 2 * b * d := by
  change (ofCartan (CartanMatrix.A 2) (CartanMatrix.A_isSymm 2)).form (lv a b) (lv c d) = _
  rw [ofCartan_form, Matrix.toBilin'_apply']
  simp [lv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, CartanMatrix.A]
  ring

/-! ## Cocycle signs -/

theorem eps_sq (α β : a2.carrier) : latticeCocycle a2 α β = 1 ∨ latticeCocycle a2 α β = -1 :=
  mul_self_eq_one_iff.mp (latticeCocycle_sq a2 α β)

theorem eps_add_left (α α' β : a2.carrier) :
    latticeCocycle a2 (α + α') β = latticeCocycle a2 α β * latticeCocycle a2 α' β :=
  latticeCocycle_add_left a2 α α' β

theorem eps_add_right (α β β' : a2.carrier) :
    latticeCocycle a2 α (β + β') = latticeCocycle a2 α β * latticeCocycle a2 α β' :=
  latticeCocycle_add_right a2 α β β'

theorem eps_neg_left (α β : a2.carrier) : latticeCocycle a2 (-α) β = latticeCocycle a2 α β := by
  have h := eps_add_left α (-α) β
  rw [add_neg_cancel, latticeCocycle_zero_left] at h
  rcases eps_sq α β with h1 | h1 <;> rw [h1] at h ⊢ <;> first | linear_combination h | linear_combination -h

theorem eps_neg_right (α β : a2.carrier) : latticeCocycle a2 α (-β) = latticeCocycle a2 α β := by
  have h := eps_add_right α β (-β)
  rw [add_neg_cancel, latticeCocycle_zero_right] at h
  rcases eps_sq α β with h1 | h1 <;> rw [h1] at h ⊢ <;> first | linear_combination h | linear_combination -h

def r1 : a2.carrier := lv 1 0
def r2 : a2.carrier := lv 0 1

/-- The four basic signs. -/
abbrev s11 : ℂ := latticeCocycle a2 r1 r1
abbrev s12 : ℂ := latticeCocycle a2 r1 r2
abbrev s21 : ℂ := latticeCocycle a2 r2 r1
abbrev s22 : ℂ := latticeCocycle a2 r2 r2

theorem s12_s21 : s12 * s21 = -1 := by
  have h := latticeCocycle_comm a2 a2_even r1 r2
  rw [show a2.form r1 r2 = -1 by rw [r1, r2, form_lv]; norm_num] at h
  simpa using h

theorem lv_eq (a b : ℤ) : lv a b = a • r1 + b • r2 := by
  change (![a, b] : Fin 2 → ℤ) = a • (![1, 0] : Fin 2 → ℤ) + b • (![0, 1] : Fin 2 → ℤ)
  funext i; fin_cases i <;> simp

theorem lv_add (a b c d : ℤ) : lv a b + lv c d = lv (a + c) (b + d) := by
  change (![a, b] : Fin 2 → ℤ) + (![c, d] : Fin 2 → ℤ) = ![a + c, b + d]
  funext i; fin_cases i <;> simp

theorem lv_zero : lv 0 0 = 0 := by
  change (![0, 0] : Fin 2 → ℤ) = 0
  funext i; fin_cases i <;> simp

theorem eps_zsmul_left (x y : a2.carrier) (n : ℤ) :
    latticeCocycle a2 (n • x) y = latticeCocycle a2 x y ^ n := by
  induction n using Int.induction_on with
  | zero => simp [latticeCocycle_zero_left]
  | succ k ih => rw [add_smul, one_smul, eps_add_left, ih, zpow_add_one₀ (by
      rcases eps_sq x y with h | h <;> rw [h] <;> norm_num)]
  | pred k ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg, eps_add_left, ih, eps_neg_left,
        zpow_sub_one₀ (by rcases eps_sq x y with h | h <;> rw [h] <;> norm_num)]
      rcases eps_sq x y with h | h <;> rw [h] <;> simp

theorem eps_zsmul_right (x y : a2.carrier) (n : ℤ) :
    latticeCocycle a2 x (n • y) = latticeCocycle a2 x y ^ n := by
  induction n using Int.induction_on with
  | zero => simp [latticeCocycle_zero_right]
  | succ k ih => rw [add_smul, one_smul, eps_add_right, ih, zpow_add_one₀ (by
      rcases eps_sq x y with h | h <;> rw [h] <;> norm_num)]
  | pred k ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg, eps_add_right, ih, eps_neg_right,
        zpow_sub_one₀ (by rcases eps_sq x y with h | h <;> rw [h] <;> norm_num)]
      rcases eps_sq x y with h | h <;> rw [h] <;> simp

/-- The cocycle in coordinates. -/
theorem eps_lv (a b c d : ℤ) :
    latticeCocycle a2 (lv a b) (lv c d) = s11 ^ (a * c) * s12 ^ (a * d) * s21 ^ (b * c) * s22 ^ (b * d) := by
  rw [lv_eq a b, lv_eq c d, eps_add_left, eps_add_right, eps_add_right, eps_zsmul_left,
    eps_zsmul_left, eps_zsmul_left, eps_zsmul_left, eps_zsmul_right, eps_zsmul_right,
    eps_zsmul_right, eps_zsmul_right, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  ring

/-! ## Weight-one states and their `0`-products -/

/-- The charged vacuum `e^{(a,b)}`. -/
abbrev ch (a b : ℤ) : LatModuleGen a2 := latChargeGen a2 (lv a b)

abbrev h1 : LatModuleGen a2 := hSt a2 r1
abbrev h2 : LatModuleGen a2 := hSt a2 r2

theorem hSt_zsmul (x : a2.carrier) (n : ℤ) : hSt a2 (n • x) = (n : ℂ) • hSt a2 x := by
  induction n using Int.induction_on with
  | zero => simp [hSt, vSchur_zero_charge, latStateGen]
  | succ k ih => rw [add_smul, one_smul, hSt_add, ih]; push_cast; rw [add_smul, one_smul]
  | pred k ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg, hSt_add, ih, hSt_neg]; push_cast
      rw [sub_smul, one_smul, sub_eq_add_neg]

theorem hSt_lv (a b : ℤ) : hSt a2 (lv a b) = (a : ℂ) • h1 + (b : ℂ) • h2 := by
  rw [lv_eq, hSt_add, hSt_zsmul, hSt_zsmul]

theorem smul_ch_eq_Qscr (x : a2.carrier) (v : LatModuleGen a2) :
    WA.smul (latChargeGen a2 x) 0 v = Qscr a2 x v := by
  rw [Qscr_eq_mode_YfullGen a2 a2_even a2_posDef]; rfl

/-- Master formula for two root vectors. -/
theorem smul_ch_ch (a b c d : ℤ) (hab : a2.form (lv a b) (lv a b) = 2)
    (hcd : a2.form (lv c d) (lv c d) = 2) :
    WA.smul (ch a b) 0 (ch c d) =
      if 2 * a * c - a * d - b * c + 2 * b * d = -1 then
        latticeCocycle a2 (lv a b) (lv c d) • ch (a + c) (b + d)
      else if a + c = 0 ∧ b + d = 0 then
        latticeCocycle a2 (lv a b) (lv c d) • hSt a2 (lv a b)
      else 0 := by
  rw [smul_ch_eq_Qscr, Qscr_latChargeGen, EEVec_vacuum, form_lv, lv_add]
  rw [form_lv] at hab hcd
  by_cases hm1 : 2 * a * c - a * d - b * c + 2 * b * d = -1
  · rw [if_pos hm1, if_pos (by omega), hm1, show (-1 : ℤ) - -1 = 0 by norm_num]
    simp [vSchur_zero, ch, latChargeGen, latStateGen, vacuumN]
  · rw [if_neg hm1]
    by_cases hopp : a + c = 0 ∧ b + d = 0
    · rw [if_pos hopp]
      obtain ⟨hc, hd⟩ := hopp
      obtain rfl : c = -a := by omega
      obtain rfl : d = -b := by omega
      rw [if_pos (by nlinarith), show -1 - (2 * a * -a - a * -b - b * -a + 2 * b * -b) = 1 by nlinarith,
        show a + -a = 0 by ring, show b + -b = 0 by ring, lv_zero]
      simp [hSt]
    · rw [if_neg hopp, if_neg ?_]
      · simp [latStateGen]
      · intro hk
        apply hopp
        have hk2 : 2 * a * c - a * d - b * c + 2 * b * d ≤ -2 := by omega
        have hQ : (a + c) * (a + c) + (b + d) * (b + d) + ((a + c) - (b + d)) * ((a + c) - (b + d)) ≤ 0 := by
          nlinarith [hk2, hab, hcd]
        constructor <;> nlinarith [mul_self_nonneg (a + c), mul_self_nonneg (b + d),
          mul_self_nonneg ((a + c) - (b + d))]

theorem smul_h_ch (x : a2.carrier) (c d : ℤ) :
    WA.smul (hSt a2 x) 0 (ch c d) = ((a2.form x (lv c d) : ℤ) : ℂ) • ch c d :=
  smul_hSt_zero_latStateGen a2 a2_even a2_posDef x (vacuumN _) (lv c d)

theorem smul_ch_h (a b : ℤ) (x : a2.carrier) :
    WA.smul (ch a b) 0 (hSt a2 x) = -((a2.form x (lv a b) : ℤ) : ℂ) • ch a b := by
  rw [smul_ch_eq_Qscr, Qscr_hSt a2 a2_posDef]

theorem smul_h_h (x y : a2.carrier) : WA.smul (hSt a2 x) 0 (hSt a2 y) = 0 := by
  rw [show hSt a2 y = latStateGen a2 (vSchur a2 y 1) 0 from rfl,
    smul_hSt_zero_latStateGen a2 a2_even a2_posDef, map_zero, Int.cast_zero, zero_smul]

theorem form_r1 (c d : ℤ) : a2.form r1 (lv c d) = 2 * c - d := by rw [r1, form_lv]; ring
theorem form_r2 (c d : ℤ) : a2.form r2 (lv c d) = -c + 2 * d := by rw [r2, form_lv]; ring

/-- The `θ`-coroot and the negative coroots in terms of `h₁, h₂`. -/
theorem hSt_lv' (a b : ℤ) : hSt a2 (lv a b) = (a : ℂ) • h1 + (b : ℂ) • h2 := hSt_lv a b

/-- The eight states, in `bracketTable` order `e₁, e₂, e_θ, f₁, f₂, f_θ, h₁, h₂`. -/
def Xs : Fin 8 → LatModuleGen a2 :=
  ![ch 1 0, ch 0 1, s12 • ch 1 1, s11 • ch (-1) 0, s22 • ch 0 (-1),
    (s11 * s21 * s22) • ch (-1) (-1), h1, h2]

theorem s21_eq : s21 = -s12 := by
  have h := s12_s21
  rcases eps_sq r1 r2 with h1 | h1
  · rw [show s12 = 1 from h1] at h ⊢; linear_combination h
  · rw [show s12 = -1 from h1] at h ⊢; linear_combination -h


set_option maxHeartbeats 1000000 in
theorem Xs_bracket_0 (d : Fin 8) :
    WA.smul (Xs 0) 0 (Xs d) = ∑ e, AffineSl3.bracketTable 0 d e • Xs e := by
  have hs21 := s21_eq
  have q11 := eps_sq r1 r1
  have q12 := eps_sq r1 r2
  have q22 := eps_sq r2 r2
  fin_cases d <;>
    simp [Xs, Fin.sum_univ_eight, AffineSl3.bracketTable, smul_ch_ch, smul_h_ch, smul_ch_h,
      smul_h_h, form_lv, form_r1, form_r2, eps_lv, hSt_lv'] <;>
    rcases q11 with e11 | e11 <;> rcases q12 with e12 | e12 <;> rcases q22 with e22 | e22 <;>
    simp [hs21, e11, e12, e22] <;> module

set_option maxHeartbeats 1000000 in
theorem Xs_bracket_1 (d : Fin 8) :
    WA.smul (Xs 1) 0 (Xs d) = ∑ e, AffineSl3.bracketTable 1 d e • Xs e := by
  have hs21 := s21_eq
  have q11 := eps_sq r1 r1
  have q12 := eps_sq r1 r2
  have q22 := eps_sq r2 r2
  fin_cases d <;>
    simp [Xs, Fin.sum_univ_eight, AffineSl3.bracketTable, smul_ch_ch, smul_h_ch, smul_ch_h,
      smul_h_h, form_lv, form_r1, form_r2, eps_lv, hSt_lv'] <;>
    rcases q11 with e11 | e11 <;> rcases q12 with e12 | e12 <;> rcases q22 with e22 | e22 <;>
    simp [hs21, e11, e12, e22] <;> module

set_option maxHeartbeats 1000000 in
theorem Xs_bracket_2 (d : Fin 8) :
    WA.smul (Xs 2) 0 (Xs d) = ∑ e, AffineSl3.bracketTable 2 d e • Xs e := by
  have hs21 := s21_eq
  have q11 := eps_sq r1 r1
  have q12 := eps_sq r1 r2
  have q22 := eps_sq r2 r2
  fin_cases d <;>
    simp [Xs, Fin.sum_univ_eight, AffineSl3.bracketTable, smul_ch_ch, smul_h_ch, smul_ch_h,
      smul_h_h, form_lv, form_r1, form_r2, eps_lv, hSt_lv'] <;>
    rcases q11 with e11 | e11 <;> rcases q12 with e12 | e12 <;> rcases q22 with e22 | e22 <;>
    simp [hs21, e11, e12, e22] <;> module

set_option maxHeartbeats 1000000 in
theorem Xs_bracket_3 (d : Fin 8) :
    WA.smul (Xs 3) 0 (Xs d) = ∑ e, AffineSl3.bracketTable 3 d e • Xs e := by
  have hs21 := s21_eq
  have q11 := eps_sq r1 r1
  have q12 := eps_sq r1 r2
  have q22 := eps_sq r2 r2
  fin_cases d <;>
    simp [Xs, Fin.sum_univ_eight, AffineSl3.bracketTable, smul_ch_ch, smul_h_ch, smul_ch_h,
      smul_h_h, form_lv, form_r1, form_r2, eps_lv, hSt_lv'] <;>
    rcases q11 with e11 | e11 <;> rcases q12 with e12 | e12 <;> rcases q22 with e22 | e22 <;>
    simp [hs21, e11, e12, e22] <;> module

set_option maxHeartbeats 1000000 in
theorem Xs_bracket_4 (d : Fin 8) :
    WA.smul (Xs 4) 0 (Xs d) = ∑ e, AffineSl3.bracketTable 4 d e • Xs e := by
  have hs21 := s21_eq
  have q11 := eps_sq r1 r1
  have q12 := eps_sq r1 r2
  have q22 := eps_sq r2 r2
  fin_cases d <;>
    simp [Xs, Fin.sum_univ_eight, AffineSl3.bracketTable, smul_ch_ch, smul_h_ch, smul_ch_h,
      smul_h_h, form_lv, form_r1, form_r2, eps_lv, hSt_lv'] <;>
    rcases q11 with e11 | e11 <;> rcases q12 with e12 | e12 <;> rcases q22 with e22 | e22 <;>
    simp [hs21, e11, e12, e22] <;> module

set_option maxHeartbeats 1000000 in
theorem Xs_bracket_5 (d : Fin 8) :
    WA.smul (Xs 5) 0 (Xs d) = ∑ e, AffineSl3.bracketTable 5 d e • Xs e := by
  have hs21 := s21_eq
  have q11 := eps_sq r1 r1
  have q12 := eps_sq r1 r2
  have q22 := eps_sq r2 r2
  fin_cases d <;>
    simp [Xs, Fin.sum_univ_eight, AffineSl3.bracketTable, smul_ch_ch, smul_h_ch, smul_ch_h,
      smul_h_h, form_lv, form_r1, form_r2, eps_lv, hSt_lv'] <;>
    rcases q11 with e11 | e11 <;> rcases q12 with e12 | e12 <;> rcases q22 with e22 | e22 <;>
    simp [hs21, e11, e12, e22] <;> module

set_option maxHeartbeats 1000000 in
theorem Xs_bracket_6 (d : Fin 8) :
    WA.smul (Xs 6) 0 (Xs d) = ∑ e, AffineSl3.bracketTable 6 d e • Xs e := by
  have hs21 := s21_eq
  have q11 := eps_sq r1 r1
  have q12 := eps_sq r1 r2
  have q22 := eps_sq r2 r2
  fin_cases d <;>
    simp [Xs, Fin.sum_univ_eight, AffineSl3.bracketTable, smul_ch_ch, smul_h_ch, smul_ch_h,
      smul_h_h, form_lv, form_r1, form_r2, eps_lv, hSt_lv'] <;>
    rcases q11 with e11 | e11 <;> rcases q12 with e12 | e12 <;> rcases q22 with e22 | e22 <;>
    simp [hs21, e11, e12, e22] <;> module

set_option maxHeartbeats 1000000 in
theorem Xs_bracket_7 (d : Fin 8) :
    WA.smul (Xs 7) 0 (Xs d) = ∑ e, AffineSl3.bracketTable 7 d e • Xs e := by
  have hs21 := s21_eq
  have q11 := eps_sq r1 r1
  have q12 := eps_sq r1 r2
  have q22 := eps_sq r2 r2
  fin_cases d <;>
    simp [Xs, Fin.sum_univ_eight, AffineSl3.bracketTable, smul_ch_ch, smul_h_ch, smul_ch_h,
      smul_h_h, form_lv, form_r1, form_r2, eps_lv, hSt_lv'] <;>
    rcases q11 with e11 | e11 <;> rcases q12 with e12 | e12 <;> rcases q22 with e22 | e22 <;>
    simp [hs21, e11, e12, e22] <;> module

/-- **Frenkel–Kac for `sl₃`, in the `bracketTable` basis.** -/
theorem Xs_bracket (c d : Fin 8) :
    WA.smul (Xs c) 0 (Xs d) = ∑ e, AffineSl3.bracketTable c d e • Xs e := by
  fin_cases c
  exacts [Xs_bracket_0 d, Xs_bracket_1 d, Xs_bracket_2 d, Xs_bracket_3 d, Xs_bracket_4 d,
    Xs_bracket_5 d, Xs_bracket_6 d, Xs_bracket_7 d]

/-! ## The current module -/

theorem ch_mem (a b : ℤ) (h : a2.form (lv a b) (lv a b) = 2) : ch a b ∈ WA.grading 1 :=
  latChargeGen_mem_grading_one a2 a2_even a2_posDef h

theorem Xs_mem (c : Fin 8) : Xs c ∈ WA.grading 1 := by
  have hh : ∀ x : a2.carrier, hSt a2 x ∈ WA.grading 1 :=
    fun x => VOA.AffineGeneral.LatticeLie.hSt_mem_gradingLatGen a2 x
  fin_cases c <;> simp only [Xs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals first
    | exact hh _
    | exact ch_mem _ _ (by rw [form_lv]; norm_num)
    | exact Submodule.smul_mem _ _ (ch_mem _ _ (by rw [form_lv]; norm_num))

theorem smul_one_vac (c d : Fin 8) : ∃ β : ℂ, WA.smul (Xs c) 1 (Xs d) = β • WA.vacuum := by
  have h := WA.grading_mode (Xs c) (Xs_mem c) (Xs d) (Xs_mem d) 1
  rw [show (1 : ℤ) + 1 - 1 - 1 = 0 by norm_num] at h
  change _ ∈ gradingLatGen a2 0 at h
  rw [gradingLatGen_zero_eq_span_vacuum a2 a2_even a2_posDef, Submodule.mem_span_singleton] at h
  obtain ⟨β, hβ⟩ := h
  exact ⟨β, hβ.symm⟩

/-- **The `sl₃[t]`-current module on `V_{A₂}`**: `op c n = (X_c)₍ₙ₎`. -/
def latRep : SectorWeyl.CurrentModule (AffineSl3.bracketTable) (LatModuleGen a2) where
  op c n := mode (WA.Y (Xs c)) (n : ℤ)
  comm c d r s v := by
    obtain ⟨β, hβ⟩ := smul_one_vac c d
    have h := VOA.Deform.current_mode_commutator (W := WA) (Xs_mem c) (Xs_mem d) β hβ v r s
    change WA.smul (Xs c) r (WA.smul (Xs d) s v) - WA.smul (Xs d) s (WA.smul (Xs c) r v) = _
    rw [h, Xs_bracket, smul_sum_left]
    have hz : (if ((r : ℤ) + (s : ℤ)) = 0 then (((r : ℤ) : ℂ) * β) • v else 0) = 0 := by
      split_ifs with h0
      · have : (r : ℤ) = 0 := by omega
        rw [this]; simp
      · rfl
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [PreVertexAlgebra.smul_smul_left]
    push_cast; rfl

/-! ## Vanishing tools -/

/-- Below the charge-`β` threshold the `β`-coordinate vanishes (as in `InvFormTP`). -/
theorem gradingLatGen_le_ker_coordEα' {β : a2.carrier} {k : ℤ} (hk : k < halfNorm a2 β) :
    gradingLatGen a2 k ≤ LinearMap.ker (coordEα a2 β) := by
  refine iSup_le fun α => ?_
  by_cases hα : α = β
  · subst hα
    rw [bigradα_eq_bot_of_neg a2 α (by omega)]
    exact bot_le
  · rintro x ⟨p, -, rfl⟩
    rw [LinearMap.mem_ker, mkEα_apply, coordEα_apply, if_neg (Ne.symm hα)]

theorem eq_zero_of_charge_grading {β : a2.carrier} {k : ℤ} (hk : k < halfNorm a2 β)
    {x : LatModuleGen a2} (hx : x ∈ chargeSec a2 β) (hg : x ∈ gradingLatGen a2 k) : x = 0 := by
  obtain ⟨p, rfl⟩ := hx
  have h := gradingLatGen_le_ker_coordEα' hk hg
  rw [LinearMap.mem_ker, mkEα_apply, coordEα_apply, if_pos rfl] at h
  rw [h, map_zero]

theorem halfNorm_lv (a b : ℤ) : halfNorm a2 (lv a b) = a * a - a * b + b * b := by
  rw [halfNorm, form_lv, show 2 * a * a - a * b - b * a + 2 * b * b = 2 * (a * a - a * b + b * b) by
    ring, Int.mul_ediv_cancel_left _ two_ne_zero]

/-- Modes of a charged vacuum on a charged vacuum vanish beyond the pole order. -/
theorem mode_ch_ch_zero (x y : a2.carrier) (n : ℕ) (h : 0 ≤ a2.form x y + n) :
    mode (WA.Y (latChargeGen a2 x)) n (latChargeGen a2 y) = 0 := by
  have hY : WA.Y (latChargeGen a2 x) = Yeαvec a2 x := by
    have hw := YfullGen_word a2 a2_even a2_posDef [] x
    rwa [wordStateLatGen_nil, YwordLatGen_nil] at hw
  rw [hY, mode_apply, latChargeGen, Yeαvec_tmul, EEVec_vacuum, if_neg (by omega)]
  simp [latStateGen]

/-- Positive Cartan modes kill charged vacua. -/
theorem mode_hSt_pos (x y : a2.carrier) (n : ℕ) (hn : 1 ≤ n) :
    mode (WA.Y (hSt a2 x)) n (latChargeGen a2 y) = 0 := by
  change WA.smul (hSt a2 x) n (latChargeGen a2 y) = 0
  rw [hSt_eq_sum, smul_sum_left]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [PreVertexAlgebra.smul_smul_left]
  change _ • mode (WA.Y (wordStateLatGen a2 [(0, a)] 0)) n (latChargeGen a2 y) = 0
  have hw : WA.Y (wordStateLatGen a2 [(0, a)] 0) = alphaLatGen a2 a := by
    change YfullGen a2 a2_even a2_posDef _ = _
    rw [YfullGen_word, BgA.YwordLatGen_singleton, genFieldLatGen_zero]
  rw [hw, mode_apply, alphaLatGen_apply, if_neg (by omega),
    add_zero, currentN_apply, latChargeGen, latStateGen, LinearMap.rTensor_tmul,
    oscN_vacuum _ _ _ _ (by omega), TensorProduct.zero_tmul, smul_zero]

/-! ## The realization `v_N = e^{Nθ}` of `M_{N,0}` -/

open SectorWeyl in
theorem Xs_chargeSec_shift {c : Fin 8} {δ : a2.carrier} (hc : Xs c ∈ chargeSec a2 δ)
    {β : a2.carrier} {x : LatModuleGen a2} (hx : x ∈ chargeSec a2 β) (n : ℕ) :
    latRep.op c n x ∈ chargeSec a2 (δ + β) :=
  YfullGen_shiftsCharge a2 a2_even a2_posDef δ hc β (-(n : ℤ) - 1) x hx

theorem latRep_grading {c : Fin 8} {k : ℤ} {x : LatModuleGen a2} (hx : x ∈ WA.grading k) :
    latRep.op c 0 x ∈ WA.grading k := by
  have h := WA.grading_mode (Xs c) (Xs_mem c) x hx 0
  rwa [show (1 : ℤ) + k - 0 - 1 = k by ring] at h

theorem ch_chargeSec (a b : ℤ) : ch a b ∈ chargeSec a2 (lv a b) := mem_chargeSec a2 _ _

/-- The lowering iterate argument: after `N+1` steps the charge leaves the weight-`N²` shell. -/
theorem lowering_vanish (N : ℕ) (c : Fin 8) (δa δb : ℤ) (s : ℂ) (hXc : Xs c = s • ch δa δb)
    (hnorm : (N : ℤ) * N < halfNorm a2 (lv (N + (N + 1) * δa) (N + (N + 1) * δb))) :
    (latRep.op c 0)^[N + 1] (ch N N) = 0 := by
  have hc : Xs c ∈ chargeSec a2 (lv δa δb) := hXc ▸ Submodule.smul_mem _ _ (ch_chargeSec _ _)
  have key : ∀ k : ℕ, (latRep.op c 0)^[k] (ch N N) ∈ chargeSec a2 (lv (N + k * δa) (N + k * δb)) ∧
      (latRep.op c 0)^[k] (ch N N) ∈ WA.grading ((N : ℤ) * N) := by
    intro k
    induction k with
    | zero =>
        refine ⟨by simpa using ch_chargeSec N N, ?_⟩
        have := latChargeGen_mem_grading a2 (lv (N : ℤ) N)
        rw [halfNorm_lv] at this
        simpa using this
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        refine ⟨?_, latRep_grading ih.2⟩
        have := Xs_chargeSec_shift hc ih.1 0
        rwa [lv_add, show δa + (N + k * δa) = N + (k + 1 : ℕ) * δa by push_cast; ring,
          show δb + (N + k * δb) = N + (k + 1 : ℕ) * δb by push_cast; ring] at this
  obtain ⟨h1, h2⟩ := key (N + 1)
  exact eq_zero_of_charge_grading hnorm (by exact_mod_cast h1) h2

open SectorWeyl in
/-- **`e^{Nθ}` satisfies the relations of `M_{N,0}`** (unconditional). -/
theorem latRep_mabRel (N : ℕ) : MabRel latRep (ch N N) N 0 where
  raising e he r := by
    have : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact mode_ch_ch_zero _ _ r (by rw [form_lv]; push_cast; nlinarith)
    · exact mode_ch_ch_zero _ _ r (by rw [form_lv]; push_cast; nlinarith)
    · change mode (WA.Y (s12 • ch 1 1)) r (ch N N) = 0
      rw [map_smul, mode_smul, LinearMap.smul_apply,
        mode_ch_ch_zero _ _ r (by rw [form_lv]; push_cast; nlinarith), smul_zero]
  cartan_pos h h6 r hr := by
    have : h = 6 ∨ h = 7 := by omega
    rcases this with rfl | rfl
    · exact mode_hSt_pos _ _ r hr
    · exact mode_hSt_pos _ _ r hr
  cartan_zero h h6 := by
    have : h = 6 ∨ h = 7 := by omega
    rcases this with rfl | rfl
    · change WA.smul (hSt a2 r1) 0 (ch N N) = _
      rw [smul_h_ch, form_r1]; push_cast; ring_nf
    · change WA.smul (hSt a2 r2) 0 (ch N N) = _
      rw [smul_h_ch, form_r2]; push_cast; ring_nf
  lowering_f1 := lowering_vanish N 3 (-1) 0 s11 rfl (by rw [halfNorm_lv]; push_cast; nlinarith)
  lowering_f2 := lowering_vanish N 4 0 (-1) s22 rfl (by rw [halfNorm_lv]; push_cast; nlinarith)
  trunc_f1 := by
    change mode (WA.Y (s11 • ch (-1) 0)) ((N + 0 : ℕ) : ℤ) (ch N N) = 0
    rw [map_smul, mode_smul, LinearMap.smul_apply,
      mode_ch_ch_zero _ _ (N + 0) (by rw [form_lv]; push_cast; nlinarith), smul_zero]
  trunc_f2 := by
    change mode (WA.Y (s22 • ch 0 (-1))) ((N + 0 : ℕ) : ℤ) (ch N N) = 0
    rw [map_smul, mode_smul, LinearMap.smul_apply,
      mode_ch_ch_zero _ _ (N + 0) (by rw [form_lv]; push_cast; nlinarith), smul_zero]
  trunc_theta := by
    change mode (WA.Y ((s11 * s21 * s22) • ch (-1) (-1))) ((2 * N + 0 : ℕ) : ℤ) (ch N N) = 0
    rw [map_smul, mode_smul, LinearMap.smul_apply,
      mode_ch_ch_zero _ _ (2 * N + 0) (by rw [form_lv]; push_cast; nlinarith), smul_zero]

end

end VOA.DeligneAudit.FusionLattice

section AxiomAudit
#print axioms VOA.DeligneAudit.FusionLattice.Xs_bracket
#print axioms VOA.DeligneAudit.FusionLattice.latRep
#print axioms VOA.DeligneAudit.FusionLattice.latRep_mabRel
end AxiomAudit
