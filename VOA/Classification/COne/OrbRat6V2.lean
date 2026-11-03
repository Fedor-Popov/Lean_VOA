import VOA.Classification.COne.OrbRat6Phi

/-! # The tetrahedral weight-nine vector of `V₂` and its zero mode on the spin-`3/2` quartet

In `V₂` let `e₀, f₀` be the zero modes of `e^{±β}` (`Qscr`), and `v_k = f₀^k e^{3β}`
(`vv k`, `k = 0..6`, the spin-`3` primary multiplet of weight `9`; `vv 7 = 0`).

* `aT = −120 v₁ + v₅` is fixed by `rotC`, `charU (−1)` and `thetaM`, hence lies in the
  tetrahedral orbifold `cubicModel` (`aW`).
* On the module, `o(v_k) = ad(F)^k o(e^{3β})` and `o(e^{3β}) q₃ = κ q₀` with `κ ≠ 0`; hence
  `o(aT) q₁ = 10 κ q₃`, `o(aT) q₃ = −120 κ q₁` (`oa_q1`, `oa_q3`).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex
  MvPolynomial VOA.LatGen.Screen

theorem Ipow8 : I ^ 8 = 1 := by rw [pow_succ, I_pow_seven]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow9 : I ^ 9 = I := by rw [pow_succ, Ipow8]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow10 : I ^ 10 = -1 := by rw [pow_succ, Ipow9]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow11 : I ^ 11 = -I := by rw [pow_succ, Ipow10]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow12 : I ^ 12 = 1 := by rw [pow_succ, Ipow11]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow13 : I ^ 13 = I := by rw [pow_succ, Ipow12]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow14 : I ^ 14 = -1 := by rw [pow_succ, Ipow13]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow15 : I ^ 15 = -I := by rw [pow_succ, Ipow14]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow16 : I ^ 16 = 1 := by rw [pow_succ, Ipow15]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow17 : I ^ 17 = I := by rw [pow_succ, Ipow16]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow18 : I ^ 18 = -1 := by rw [pow_succ, Ipow17]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow19 : I ^ 19 = -I := by rw [pow_succ, Ipow18]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow20 : I ^ 20 = 1 := by rw [pow_succ, Ipow19]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow21 : I ^ 21 = I := by rw [pow_succ, Ipow20]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow22 : I ^ 22 = -1 := by rw [pow_succ, Ipow21]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow23 : I ^ 23 = -I := by rw [pow_succ, Ipow22]; ring_nf; try simp only [I_sq, neg_neg]
theorem Ipow24 : I ^ 24 = 1 := by rw [pow_succ, Ipow23]; ring_nf; try simp only [I_sq, neg_neg]

/-! ## §1 `sl₂` in `V₂` -/

/-- `e₀` on `V₂`. -/
abbrev eo : Module.End ℂ Sp := Qscr (latP 1) (a1 1)
/-- `f₀` on `V₂`. -/
abbrev fo : Module.End ℂ Sp := Qscr (latP 1) (-a1 1)
/-- `h₀` on `V₂`. -/
abbrev ho : Module.End ℂ Sp := V1.zeroMode (hSt (latP 1) (a1 1)) 1

theorem eo_eq (x : Sp) : eo x = V1.smul (latChargeGen (latP 1) (a1 1)) 0 x := by
  show Qscr (latP 1) (a1 1) x = _
  rw [← zeroMode_latChargeGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)]; rfl

theorem fo_eq (x : Sp) : fo x = V1.smul (latChargeGen (latP 1) (-a1 1)) 0 x := by
  show Qscr (latP 1) (-a1 1) x = _
  rw [← zeroMode_latChargeGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)]; rfl

theorem V_EF (x : Sp) : eo (fo x) - fo (eo x) = eps1 • ho x := by
  rw [eo_eq, fo_eq, eo_eq, fo_eq, VertexOperatorAlgebra.zeroMode_leibniz, smul_e_f,
    PreVertexAlgebra.smul_smul_left, add_sub_cancel_right]
  rfl

theorem V_HF (x : Sp) : ho (fo x) - fo (ho x) = (-2 : ℂ) • fo x := by
  rw [VertexOperatorAlgebra.zeroMode_apply, VertexOperatorAlgebra.zeroMode_apply, fo_eq, fo_eq,
    show (1 : ℤ) - 1 = 0 by norm_num, VertexOperatorAlgebra.zeroMode_leibniz, smul_h_charge,
    PreVertexAlgebra.smul_smul_left, add_sub_cancel_right]
  congr 1
  show (((2 : ℤ) * (-1 : ℤ) : ℤ) : ℂ) = -2
  norm_num

/-- `e^{3β}`. -/
abbrev v0 : Sp := latChargeGen (latP 1) (3 : ℤ)

theorem eo_v0 : eo v0 = 0 :=
  Qscr_latChargeGen_of_nonneg (latP 1) (β := a1 1) (γ := (3 : ℤ)) (by rw [latP_form]; norm_num [a1])

theorem ho_v0 : ho v0 = (6 : ℂ) • v0 := by
  rw [VertexOperatorAlgebra.zeroMode_apply, show (1 : ℤ) - 1 = 0 by norm_num,
    show v0 = latStateGen (latP 1) (vacuumN _) (3 : ℤ) from rfl, smul_hSt_zero_latStateGen,
    latP_form]
  norm_num [a1]

/-- `v_k = f₀^k e^{3β}`. -/
abbrev vv (k : ℕ) : Sp := (fo ^ k) v0

theorem eo_vv (k : ℕ) : eo (vv (k + 1)) = (eps1 * (k + 1) * (6 - k)) • vv k :=
  E_Fpow V_EF V_HF eo_v0 ho_v0 k

theorem v0_bigrad : v0 ∈ bigradα (latP 1) (0, (3 : ℤ)) := ⟨_, one_mem_Z0, rfl⟩

theorem vv_bigrad (k : ℕ) : vv k ∈ bigradα (latP 1) ((k : ℤ) * (6 - k), (3 - k : ℤ)) := by
  induction k with
  | zero => simpa using v0_bigrad
  | succ k ih =>
    rw [vv, pow_succ', Module.End.mul_apply]
    have h := Qscr_mem_bigradα (latP 1) (-a1 1) ih
    convert h using 3
    · rw [latP_form]; simp [a1]; push_cast; ring
    · change (3 - ((k + 1 : ℕ) : ℤ)) = (3 - (k : ℤ)) + -1
      push_cast; ring

theorem vv_seven : vv 7 = 0 := by
  have h := vv_bigrad 7
  rw [bigradα_eq_bot_of_neg _ _ (by norm_num), Submodule.mem_bot] at h
  exact h

theorem fo_vv (k : ℕ) : fo (vv k) = vv (k + 1) := by
  rw [vv, vv, pow_succ', Module.End.mul_apply]

/-- The seven-term vector `∑ c_k v_k`. -/
def R7 (a b c d e f g : ℂ) : Sp :=
  a • vv 0 + b • vv 1 + c • vv 2 + d • vv 3 + e • vv 4 + f • vv 5 + g • vv 6

theorem R7_add (a b c d e f g a' b' c' d' e' f' g' : ℂ) :
    R7 a b c d e f g + R7 a' b' c' d' e' f' g' =
      R7 (a + a') (b + b') (c + c') (d + d') (e + e') (f + f') (g + g') := by
  simp only [R7, add_smul]; abel

theorem R7_smul (t a b c d e f g : ℂ) :
    t • R7 a b c d e f g = R7 (t * a) (t * b) (t * c) (t * d) (t * e) (t * f) (t * g) := by
  simp only [R7, smul_add, smul_smul]

theorem R7_congr {a b c d e f g a' b' c' d' e' f' g' : ℂ} (h1 : a = a') (h2 : b = b')
    (h3 : c = c') (h4 : d = d') (h5 : e = e') (h6 : f = f') (h7 : g = g') :
    R7 a b c d e f g = R7 a' b' c' d' e' f' g' := by
  rw [h1, h2, h3, h4, h5, h6, h7]

theorem vv_zero : vv 0 = v0 := by simp [vv]

theorem eo_R7 (a b c d e f g : ℂ) :
    eo (R7 a b c d e f g) =
      R7 (6 * eps1 * b) (10 * eps1 * c) (12 * eps1 * d) (12 * eps1 * e) (10 * eps1 * f)
        (6 * eps1 * g) 0 := by
  have e1 := eo_vv 0; have e2 := eo_vv 1; have e3 := eo_vv 2
  have e4 := eo_vv 3; have e5 := eo_vv 4; have e6 := eo_vv 5
  simp only [R7, map_add, map_smul, vv_zero, eo_v0, e1, e2, e3, e4, e5, e6, smul_zero, zero_add,
    smul_smul, zero_smul, add_zero]
  push_cast
  module

theorem fo_R7 (a b c d e f g : ℂ) : fo (R7 a b c d e f g) = R7 0 a b c d e f := by
  simp only [R7, map_add, map_smul, fo_vv, Nat.reduceAdd]
  rw [vv_seven]
  simp only [smul_zero, add_zero, zero_smul, zero_add]

theorem expSum_seven {M : Type*} [AddCommGroup M] [Module ℂ M] (D : Module.End ℂ M) (v : M) :
    expSum D 7 v = v + D v + (2⁻¹ : ℂ) • D (D v) + (6⁻¹ : ℂ) • D (D (D v)) +
      (24⁻¹ : ℂ) • D (D (D (D v))) + (120⁻¹ : ℂ) • D (D (D (D (D v)))) +
      (720⁻¹ : ℂ) • D (D (D (D (D (D v))))) := by
  simp only [expSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_succ, pow_zero,
    one_mul, Module.End.mul_apply, Module.End.one_apply]
  norm_num [Nat.factorial]

theorem eo_pow_R7 (a b c d e f g : ℂ) : (eo ^ 7) (R7 a b c d e f g) = 0 := by
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, eo_R7]
  simp [R7]

theorem fo_pow_R7 (a b c d e f g : ℂ) : (fo ^ 7) (R7 a b c d e f g) = 0 := by
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, fo_R7]
  simp [R7]

theorem expE_R7 (t a b c d e f g : ℂ) :
    expE t (R7 a b c d e f g) = expSum (t • eo) 7 (R7 a b c d e f g) := by
  rw [rootExp_apply]
  have hD : V1.zeroMode (t • latChargeGen (latP 1) (a1 1)) 1 = t • eo :=
    zeroMode_smul_latChargeGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) _ t
  rw [expFun_eq_expSum _ (N := 7) (by rw [hD, smul_pow, LinearMap.smul_apply, eo_pow_R7,
    smul_zero]), hD]

theorem expF_R7 (t a b c d e f g : ℂ) :
    expF t (R7 a b c d e f g) = expSum (t • fo) 7 (R7 a b c d e f g) := by
  rw [rootExp_apply]
  have hD : V1.zeroMode (t • latChargeGen (latP 1) (-a1 1)) 1 = t • fo :=
    zeroMode_smul_latChargeGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) _ t
  rw [expFun_eq_expSum _ (N := 7) (by rw [hD, smul_pow, LinearMap.smul_apply, fo_pow_R7,
    smul_zero]), hD]

theorem charU_bigrad (u : ℂˣ) {d : ℤ} {γ : (latP 1).carrier} {x : Sp}
    (hx : x ∈ bigradα (latP 1) (d, γ)) : charU 1 le_rfl u x = ((u ^ ci 1 γ : ℂˣ) : ℂ) • x := by
  obtain ⟨p, _, rfl⟩ := hx
  exact charU_latStateGen 1 le_rfl u p γ

theorem charU_R7 (u : ℂˣ) (a b c d e f g : ℂ) :
    charU 1 le_rfl u (R7 a b c d e f g) =
      R7 (((u ^ (3 : ℤ) : ℂˣ) : ℂ) * a) (((u ^ (2 : ℤ) : ℂˣ) : ℂ) * b)
        (((u ^ (1 : ℤ) : ℂˣ) : ℂ) * c) (((u ^ (0 : ℤ) : ℂˣ) : ℂ) * d)
        (((u ^ (-1 : ℤ) : ℂˣ) : ℂ) * e) (((u ^ (-2 : ℤ) : ℂˣ) : ℂ) * f)
        (((u ^ (-3 : ℤ) : ℂˣ) : ℂ) * g) := by
  simp only [R7, map_add, Aut.map_smul_c, Aut.coe_toLinearEquiv]
  rw [charU_bigrad u (vv_bigrad 0), charU_bigrad u (vv_bigrad 1), charU_bigrad u (vv_bigrad 2),
    charU_bigrad u (vv_bigrad 3), charU_bigrad u (vv_bigrad 4), charU_bigrad u (vv_bigrad 5),
    charU_bigrad u (vv_bigrad 6)]
  simp only [smul_smul, ci]
  norm_num [mul_comm]

/-! ## §2 The tetrahedral vector -/

/-- `aT = −120 v₁ + v₅`. -/
def aT : Sp := R7 0 (-120) 0 0 0 1 0

theorem expE_R7' (t a b c d e f g : ℂ) :
    expE t (R7 a b c d e f g) =
      R7 (a + t * (6 * eps1 * b) + t ^ 2 / 2 * (60 * eps1 ^ 2 * c) +
            t ^ 3 / 6 * (720 * eps1 ^ 3 * d) + t ^ 4 / 24 * (8640 * eps1 ^ 4 * e) +
            t ^ 5 / 120 * (86400 * eps1 ^ 5 * f) + t ^ 6 / 720 * (518400 * eps1 ^ 6 * g))
        (b + t * (10 * eps1 * c) + t ^ 2 / 2 * (120 * eps1 ^ 2 * d) +
            t ^ 3 / 6 * (1440 * eps1 ^ 3 * e) + t ^ 4 / 24 * (14400 * eps1 ^ 4 * f) +
            t ^ 5 / 120 * (86400 * eps1 ^ 5 * g))
        (c + t * (12 * eps1 * d) + t ^ 2 / 2 * (144 * eps1 ^ 2 * e) +
            t ^ 3 / 6 * (1440 * eps1 ^ 3 * f) + t ^ 4 / 24 * (8640 * eps1 ^ 4 * g))
        (d + t * (12 * eps1 * e) + t ^ 2 / 2 * (120 * eps1 ^ 2 * f) +
            t ^ 3 / 6 * (720 * eps1 ^ 3 * g))
        (e + t * (10 * eps1 * f) + t ^ 2 / 2 * (60 * eps1 ^ 2 * g))
        (f + t * (6 * eps1 * g)) g := by
  rw [expE_R7, expSum_seven]
  simp only [LinearMap.smul_apply, map_smul, eo_R7, R7_smul, R7_add]
  apply R7_congr <;> ring

theorem expF_R7' (t a b c d e f g : ℂ) :
    expF t (R7 a b c d e f g) =
      R7 a (b + t * a) (c + t * b + t ^ 2 / 2 * a) (d + t * c + t ^ 2 / 2 * b + t ^ 3 / 6 * a)
        (e + t * d + t ^ 2 / 2 * c + t ^ 3 / 6 * b + t ^ 4 / 24 * a)
        (f + t * e + t ^ 2 / 2 * d + t ^ 3 / 6 * c + t ^ 4 / 24 * b + t ^ 5 / 120 * a)
        (g + t * f + t ^ 2 / 2 * e + t ^ 3 / 6 * d + t ^ 4 / 24 * c + t ^ 5 / 120 * b +
          t ^ 6 / 720 * a) := by
  rw [expF_R7, expSum_seven]
  simp only [LinearMap.smul_apply, map_smul, fo_R7, R7_smul, R7_add]
  apply R7_congr <;> ring

theorem rotC_aT : rotC aT = aT := by
  simp only [aT, rotC, rot2, rot4, Aut.mul_apply]
  rw [charU_R7, charU_R7, expE_R7', expF_R7', expE_R7']
  simp only [unitI_val, unitHalf_val]
  have hI3 : I ^ (3 : ℤ) = -I := by rw [zpow_ofNat, I_pow_three]
  have hI2 : I ^ (2 : ℤ) = -1 := by rw [zpow_ofNat, I_sq]
  have hIm1 : I ^ (-1 : ℤ) = -I := by rw [zpow_neg_one, inv_I]
  have hIm2 : I ^ (-2 : ℤ) = -1 := by rw [zpow_neg, hI2]; norm_num
  have hIm3 : I ^ (-3 : ℤ) = I := by rw [zpow_neg, hI3, inv_neg, inv_I, neg_neg]
  rw [hI3, hI2, hIm1, hIm2, hIm3]
  norm_num
  rcases eps1_cases with h | h <;> rw [h] <;> apply R7_congr <;>
    (ring_nf
     try simp only [I_sq, I_pow_three, I_pow_four, I_pow_five, I_pow_six, I_pow_seven, Ipow8,
       Ipow9, Ipow10, Ipow11, Ipow12, Ipow13, Ipow14, Ipow15, Ipow16, Ipow17, Ipow18, Ipow19,
       Ipow20, Ipow21, Ipow22, Ipow23, Ipow24]
     try ring_nf)

theorem charU_neg_aT : charU 1 le_rfl (-1) aT = aT := by
  rw [aT, charU_R7]
  apply R7_congr <;> simp [Units.val_zpow_eq_zpow_val] <;> norm_num

end VOA.Classification.COne.OrbRat6
