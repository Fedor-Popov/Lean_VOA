/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharEval

/-!
# Blocks of every colour

For every colour `c ≥ 0` the series

  `T^c X`, `T^c Y`, `T^c Z`  and  `P_c = T^c J - T^{c+1}/(c+1)`

lie in the model `S` with `c + 1` letters (`tpow_gS_inS`, `pc_inS`).  The first family follows
from `T^{c+1} G = W · T^c G + T^c (J G)` with `W = T - J` the Sugawara letter and the Wronskian
identities for `J G`.  For the second, `Q_c = -(c+1) P_c = (c+1) K T^c + T^{c+1}` (`K = -J`)
satisfies the recursion `Q_{c+1} = W Q_c - (c+1) B_c` with the *conic pairing*

  `B_c = Y' (T^c Y)' - ½ X' (T^c Z)' - ½ Z' (T^c X)' = T^c J²`

(`conic_pairing`, using `Y² = XZ` and `J² = Y'² - X'Z'`).

Over `ℂ[T_j]` each block coefficient is its lowest part `Σ_{b+d=a} [T^c]_b G_d` plus `T`-degree
`≥ c + 1` (`blkG_coeff_sub_lowM`), and `Φ_{ψ_F}` of a product of block coefficients is computed
from the lowest parts (`Φ_pblkG`).

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.SymbolModel VOA.TwoSeries.StrictModel VOA.JetProduct
open scoped BigOperators

noncomputable section

section General

variable (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R)

theorem gS_one_sq : gS R 1 * gS R 1 = gS R 0 * gS R 2 := by
  have h : ySer * ySer = xSer * zSer := by simp only [xSer, ySer, zSer]; ring
  have := congrArg (PowerSeries.map (ι R).toRingHom) h
  simpa only [map_mul] using this

theorem gS_one_sq_deriv :
    (2 : PowerSeries (MPoly R)) * (gS R 1 * dG R 1) = dG R 0 * gS R 2 + gS R 0 * dG R 2 := by
  have h := congrArg (PowerSeries.derivative (MPoly R)) (gS_one_sq R)
  simp only [Derivation.leibniz, smul_eq_mul] at h
  rw [dG, dG, dG]
  linear_combination h

/-- **The conic pairing** `Y'(T^c Y)' - ½ X'(T^c Z)' - ½ Z'(T^c X)' = T^c J²`. -/
theorem conic_pairing (c : ℕ) :
    dG R 1 * PowerSeries.derivative (MPoly R) (tS R t ^ c * gS R 1) - (1 / 2 : ℂ) • (dG R 0 * PowerSeries.derivative (MPoly R) (tS R t ^ c * gS R 2)) -
        (1 / 2 : ℂ) • (dG R 2 * PowerSeries.derivative (MPoly R) (tS R t ^ c * gS R 0)) =
      tS R t ^ c * (gS R 3 * gS R 3) := by
  rw [gS_three_mul_gS_three]
  simp only [Derivation.leibniz, smul_eq_mul, Algebra.smul_def]
  have hc : algebraMap ℂ (PowerSeries (MPoly R)) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℂ (PowerSeries (MPoly R))) 2, ← map_mul]; norm_num
  have h2 := gS_one_sq_deriv R
  rw [dG, dG, dG] at h2 ⊢
  linear_combination (-(tS R t ^ c * PowerSeries.derivative (MPoly R) (gS R 0) *
      PowerSeries.derivative (MPoly R) (gS R 2) + PowerSeries.derivative (MPoly R) (tS R t ^ c) *
        gS R 1 * PowerSeries.derivative (MPoly R) (gS R 1))) * hc +
    (algebraMap ℂ (PowerSeries (MPoly R)) (1 / 2) *
      PowerSeries.derivative (MPoly R) (tS R t ^ c)) * h2

theorem InS.mul' {r r' rr : ℕ} {w w' ww : ℤ} {F G : PowerSeries (MPoly R)}
    (hF : InS R t r w F) (hG : InS R t r' w' G) (hr : r + r' = rr) (hw : w + w' = ww) :
    InS R t rr ww (F * G) := by
  subst hr hw; exact hF.mul hG

/-- The non-`J` blocks of every colour: `T^c X, T^c Y, T^c Z ∈ S` with `c + 1` letters. -/
theorem tpow_gS_inS_all : ∀ c : ℕ,
    InS R t (c + 1) (1 + 2 * (c : ℤ)) (tS R t ^ c * gS R 0) ∧
      InS R t (c + 1) (1 + 2 * (c : ℤ)) (tS R t ^ c * gS R 1) ∧
        InS R t (c + 1) (1 + 2 * (c : ℤ)) (tS R t ^ c * gS R 2)
  | 0 => by
    refine ⟨(gS_inS R t (g := 0) (by decide)).congr (by simp) (by simp),
      (gS_inS R t (g := 1) (by decide)).congr (by simp) (by simp),
      (gS_inS R t (g := 2) (by decide)).congr (by simp) (by simp)⟩
  | c + 1 => by
    obtain ⟨ih0, ih1, ih2⟩ := tpow_gS_inS_all c
    have hW := sug_inS R t
    have d0 := dG_inS R t (g := 0) (by decide)
    have d1 := dG_inS R t (g := 1) (by decide)
    have d2 := dG_inS R t (g := 2) (by decide)
    have hwW : (2 : ℤ) + (1 + 2 * (c : ℤ)) = 3 + 2 * (c : ℤ) := by ring
    have hwD : (1 + 2 * (c : ℤ)) + 2 = 3 + 2 * (c : ℤ) := by ring
    have hrW : 1 + (c + 1) = c + 1 + 1 := by ring
    have hwT : (3 + 2 * (c : ℤ)) = 1 + 2 * ((c + 1 : ℕ) : ℤ) := by push_cast; ring
    refine ⟨?_, ?_, ?_⟩
    · have A : InS R t (c + 1 + 1) (3 + 2 * (c : ℤ)) ((tS R t - gS R 3) * (tS R t ^ c * gS R 0)) :=
        hW.mul' R t ih0 hrW hwW
      have B : InS R t (c + 1 + 1) (3 + 2 * (c : ℤ)) ((tS R t ^ c * gS R 1) * dG R 0) :=
        ih1.mul' R t d0 rfl hwD
      have C : InS R t (c + 1 + 1) (3 + 2 * (c : ℤ)) ((tS R t ^ c * gS R 0) * dG R 1) :=
        ih0.mul' R t d1 rfl hwD
      refine (A.add (B.sub C)).congr ?_ hwT
      have := gS_three_mul_gS_zero R
      linear_combination (-(tS R t ^ c)) * this
    · have A : InS R t (c + 1 + 1) (3 + 2 * (c : ℤ)) ((tS R t - gS R 3) * (tS R t ^ c * gS R 1)) :=
        hW.mul' R t ih1 hrW hwW
      have B : InS R t (c + 1 + 1) (3 + 2 * (c : ℤ)) ((tS R t ^ c * gS R 2) * dG R 0) :=
        ih2.mul' R t d0 rfl hwD
      have C : InS R t (c + 1 + 1) (3 + 2 * (c : ℤ)) ((tS R t ^ c * gS R 0) * dG R 2) :=
        ih0.mul' R t d2 rfl hwD
      refine (A.add ((B.sub C).smul (1 / 2 : ℂ))).congr ?_ hwT
      have := gS_three_mul_gS_one R
      simp only [Algebra.smul_def] at this ⊢
      linear_combination (-(tS R t ^ c)) * this
    · have A : InS R t (c + 1 + 1) (3 + 2 * (c : ℤ)) ((tS R t - gS R 3) * (tS R t ^ c * gS R 2)) :=
        hW.mul' R t ih2 hrW hwW
      have B : InS R t (c + 1 + 1) (3 + 2 * (c : ℤ)) ((tS R t ^ c * gS R 2) * dG R 1) :=
        ih2.mul' R t d1 rfl hwD
      have C : InS R t (c + 1 + 1) (3 + 2 * (c : ℤ)) ((tS R t ^ c * gS R 1) * dG R 2) :=
        ih1.mul' R t d2 rfl hwD
      refine (A.add (B.sub C)).congr ?_ hwT
      have := gS_three_mul_gS_two R
      linear_combination (-(tS R t ^ c)) * this

/-- `Q_c = T^{c+1} - (c+1) T^c J`. -/
def qS (c : ℕ) : PowerSeries (MPoly R) :=
  tS R t ^ (c + 1) - ((c + 1 : ℕ) : ℂ) • (tS R t ^ c * gS R 3)

theorem qS_succ (c : ℕ) : qS R t (c + 1) = (tS R t - gS R 3) * qS R t c -
    ((c + 1 : ℕ) : ℂ) • (dG R 1 * PowerSeries.derivative (MPoly R) (tS R t ^ c * gS R 1) -
      (1 / 2 : ℂ) • (dG R 0 * PowerSeries.derivative (MPoly R) (tS R t ^ c * gS R 2)) -
        (1 / 2 : ℂ) • (dG R 2 * PowerSeries.derivative (MPoly R) (tS R t ^ c * gS R 0))) := by
  rw [conic_pairing, qS, qS]
  simp only [Algebra.smul_def]
  push_cast
  ring

/-- `Q_c ∈ S` with `c + 1` letters. -/
theorem qS_inS : ∀ c : ℕ, InS R t (c + 1) (2 + 2 * (c : ℤ)) (qS R t c)
  | 0 => (sug_inS R t).congr (by simp [qS]) (by simp)
  | c + 1 => by
    have ih := qS_inS c
    obtain ⟨h0, h1, h2⟩ := tpow_gS_inS_all R t c
    have hW := sug_inS R t
    have d0 := dG_inS R t (g := 0) (by decide)
    have d1 := dG_inS R t (g := 1) (by decide)
    have d2 := dG_inS R t (g := 2) (by decide)
    have hw : (2 : ℤ) + (1 + 2 * (c : ℤ) + 1) = 4 + 2 * (c : ℤ) := by ring
    have A : InS R t (c + 1 + 1) (4 + 2 * (c : ℤ)) ((tS R t - gS R 3) * qS R t c) :=
      hW.mul' R t ih (by ring) (by ring)
    have B1 : InS R t (c + 1 + 1) (4 + 2 * (c : ℤ))
        (dG R 1 * PowerSeries.derivative (MPoly R) (tS R t ^ c * gS R 1)) :=
      d1.mul' R t h1.deriv (by ring) hw
    have B2 : InS R t (c + 1 + 1) (4 + 2 * (c : ℤ))
        (dG R 0 * PowerSeries.derivative (MPoly R) (tS R t ^ c * gS R 2)) :=
      d0.mul' R t h2.deriv (by ring) hw
    have B3 : InS R t (c + 1 + 1) (4 + 2 * (c : ℤ))
        (dG R 2 * PowerSeries.derivative (MPoly R) (tS R t ^ c * gS R 0)) :=
      d2.mul' R t h0.deriv (by ring) hw
    refine (A.sub (((B1.sub (B2.smul _)).sub (B3.smul _)).smul _)).congr (qS_succ R t c).symm ?_
    push_cast; ring

/-- The blocks of colour `c`: `T^c X, T^c Y, T^c Z`, and `T^c J - T^{c+1}/(c+1)`. -/
def blkG (c : ℕ) (g : Fin 4) : PowerSeries (MPoly R) :=
  if g = 3 then tS R t ^ c * gS R 3 - (1 / ((c + 1 : ℕ) : ℂ)) • tS R t ^ (c + 1)
  else tS R t ^ c * gS R g

/-- The weight offset of a block of colour `c`. -/
def bwtG (c : ℕ) (g : Fin 4) : ℤ := 1 + 2 * (c : ℤ) + (if g = 3 then 1 else 0)

/-- **The blocks of every colour lie in the model.** -/
theorem blkG_inS (c : ℕ) (g : Fin 4) : InS R t (c + 1) (bwtG c g) (blkG R t c g) := by
  obtain ⟨h0, h1, h2⟩ := tpow_gS_inS_all R t c
  unfold blkG bwtG
  split_ifs with hg
  · have h := (qS_inS R t c).smul (-(1 / ((c + 1 : ℕ) : ℂ)))
    refine h.congr ?_ (by ring)
    rw [qS, smul_sub, smul_smul]
    have hc : ((c + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero c
    rw [show -(1 / ((c + 1 : ℕ) : ℂ)) * ((c + 1 : ℕ) : ℂ) = -1 by field_simp]
    simp only [neg_smul, one_smul, sub_neg_eq_add]
    abel
  · have hg' : g = 0 ∨ g = 1 ∨ g = 2 := by
      rcases g with ⟨g, hlt⟩
      interval_cases g
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd rfl hg
    rcases hg' with rfl | rfl | rfl
    · exact h0.congr rfl (by ring)
    · exact h1.congr rfl (by ring)
    · exact h2.congr rfl (by ring)

/-- The product `Π_b [s^{a_b}] blkG (c_b, g_b)`. -/
def pblkG {K : ℕ} (c : Fin K → ℕ) (g : Fin K → Fin 4) (a : Fin K → ℕ) : MPoly R :=
  ∏ i, PowerSeries.coeff (a i) (blkG R t (c i) (g i))

/-- Products of block coefficients of every colour lie in the model. -/
theorem pblkG_mem : ∀ {K : ℕ} (c : Fin K → ℕ) (g : Fin K → Fin 4) (a : Fin K → ℕ),
    pblkG R t c g a ∈ modelDeg R t (∑ i, (c i + 1)) (∑ i, ((a i : ℤ) + bwtG (c i) (g i)))
  | 0, c, g, a => by simpa [pblkG] using one_mem_modelDeg R t
  | K + 1, c, g, a => by
    rw [pblkG, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact mul_mem_modelDeg R t (blkG_inS R t (c 0) (g 0) (a 0))
      (pblkG_mem (fun i => c i.succ) (fun i => g i.succ) (fun i => a i.succ))

end General

/-! ### Lowest parts over `ℂ[T_j]` -/

theorem tSer_pow_lowDeg : ∀ (c b : ℕ), lowDeg c (PowerSeries.coeff b (tSer ^ c))
  | 0, b => lowDeg_zero_left _
  | c + 1, b => by
    rw [pow_succ, PowerSeries.coeff_mul]
    refine lowDeg_sum _ _ fun p _ => lowDeg_mul (tSer_pow_lowDeg c p.1) ?_
    simp only [tSer, PowerSeries.coeff_mk]
    exact lowDeg_X _

theorem tS_T_eq : tS TPoly X = PowerSeries.map (MvPolynomial.C : TPoly →+* MPoly TPoly) tSer := by
  refine PowerSeries.ext fun a => ?_
  rw [tS, PowerSeries.coeff_mk, PowerSeries.coeff_map, tSer, PowerSeries.coeff_mk]

theorem coeff_tS_pow (c b : ℕ) :
    PowerSeries.coeff b (tS TPoly X ^ c) = MvPolynomial.C (PowerSeries.coeff b (tSer ^ c)) := by
  rw [tS_T_eq, ← map_pow, PowerSeries.coeff_map]

/-- The lowest part `Σ_{b+d=a} [T^c]_b · G_{g,d}`. -/
def lowG (c : ℕ) (g : Fin 4) (a : ℕ) : MPoly TPoly :=
  ∑ p ∈ Finset.antidiagonal a,
    MvPolynomial.C (PowerSeries.coeff p.1 (tSer ^ c)) * ι TPoly (genCoeff g p.2)

theorem lowG_lowM (c : ℕ) (g : Fin 4) (a : ℕ) : LowM c (lowG c g a) :=
  LowM.sum _ _ fun p _ => LowM.C_mul_ι (tSer_pow_lowDeg c p.1) _

theorem coeff_tpow_gS (c : ℕ) (g : Fin 4) (a : ℕ) :
    PowerSeries.coeff a (tS TPoly X ^ c * gS TPoly g) = lowG c g a := by
  rw [PowerSeries.coeff_mul, lowG]
  apply Finset.sum_congr rfl
  intro p _
  rw [coeff_tS_pow, coeff_gS]

/-- Each block coefficient of colour `c` is its lowest part plus `T`-degree `≥ c + 1`. -/
theorem blkG_coeff_sub_lowM (c : ℕ) (g : Fin 4) (a : ℕ) :
    LowM (c + 1) (PowerSeries.coeff a (blkG TPoly X c g) - lowG c g a) := by
  unfold blkG
  split_ifs with hg
  · subst hg
    rw [map_sub, coeff_tpow_gS, sub_sub_cancel_left, PowerSeries.coeff_smul, coeff_tS_pow]
    exact LowM.neg' (LowM.smul _ (LowM.C (tSer_pow_lowDeg _ _)))
  · rw [coeff_tpow_gS, sub_self]; exact LowM.zero _

theorem prod_lowG {K : ℕ} (c : Fin K → ℕ) (g : Fin K → Fin 4) (a : Fin K → ℕ) :
    ∏ i, lowG (c i) (g i) (a i) = ∑ p ∈ Fintype.piFinset (fun i => Finset.antidiagonal (a i)),
      MvPolynomial.C (∏ i, PowerSeries.coeff (p i).1 (tSer ^ c i)) *
        ι TPoly (Pga g (toF fun i => (p i).2)) := by
  simp only [lowG]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod]
  simp [Pga]

theorem pblkG_lowM {K : ℕ} (c : Fin K → ℕ) (g : Fin K → Fin 4) (a : Fin K → ℕ) :
    LowM (∑ i, c i) (pblkG TPoly X c g a) :=
  (prod_sub_lowM c (fun i => lowG (c i) (g i) (a i))
    (fun i => PowerSeries.coeff (a i) (blkG TPoly X (c i) (g i)))
    (fun _ => lowG_lowM _ _ _) (fun _ => blkG_coeff_sub_lowM _ _ _)).2

/-- `Φ_{ψ_F}` of a product of block coefficients, from the lowest parts. -/
theorem Φ_pblkG {K S : ℕ} (F : MvPolynomial (Fin S) ℂ) (c : Fin K → ℕ) (hc : ∑ i, c i = S)
    (g : Fin K → Fin 4) (a : Fin K → ℕ) :
    VOA.TwoSeries.StrictModel.Φ TPoly (ψF F) (pblkG TPoly X c g a) =
      ∑ p ∈ Fintype.piFinset (fun i => Finset.antidiagonal (a i)),
        ψF F (∏ i, PowerSeries.coeff (p i).1 (tSer ^ c i)) • Pga g (toF fun i => (p i).2) := by
  have hlow := (prod_sub_lowM c (fun i => lowG (c i) (g i) (a i))
    (fun i => PowerSeries.coeff (a i) (blkG TPoly X (c i) (g i)))
    (fun i => lowG_lowM _ _ _) (fun i => blkG_coeff_sub_lowM _ _ _)).1
  rw [hc] at hlow
  have h0 := Φ_ψF_eq_zero F hlow
  rw [map_sub, sub_eq_zero] at h0
  rw [pblkG, h0, prod_lowG, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact VOA.TwoSeries.StrictModel.Φ_C_mul_ι TPoly _ _ _

end

end VOA.TwoSeries.ModelChar
