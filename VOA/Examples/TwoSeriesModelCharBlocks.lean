/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesStrictLevelOne
import VOA.Examples.JetProductRank

/-!
# Colour-one blocks of the model `S_{n,r}`

Over any coefficient algebra `R` with a sequence `t : ℕ → R` (the images of the jets `T_j`),
the model `S = ⊕_r S_r` (`modelDeg R t r d`) is closed under products
(`modelDeg_mul_le`), and a power series is *in `S` with `r` letters and weight offset `w`*
(`InS R t r w F`) when its `s^a` coefficient lies in `modelDeg R t r (a + w)`.  This class is
closed under products, sums, scalars and `d/ds`.

With `X = u², Y = uv, Z = v², J = u'v - uv'` (the generator series, mapped into `R[u_j, v_j]`)
and `T(s) = Σ t_j s^j`, the Wronskian identities

  `J X = Y X' - X Y'`,  `2 J Y = Z X' - X Z'`,  `J Z = Z Y' - Y Z'`,  `J² = Y'² - X' Z'`

(`jx_wronskian` …) show that the **colour-one blocks**

  `T X`, `T Y`, `T Z`, `T J - T²/2`

are in `S` with two letters (`blk_inS`), as are the colour-zero blocks `X, Y, Z, J - T`
with one letter.  The `s^a` coefficient of each block is its *lowest part*
`Σ_{b+d=a} T_b^{[c]} G_d` plus a part of higher `T`-degree (`blkCoeff_eq`), and products of
block coefficients lie in `S` (`pblk_mem`).

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.SymbolModel VOA.TwoSeries.StrictModel VOA.AdamovicSymbol
open VOA.AffineVOA.CorrectedR (Generator)
open scoped BigOperators

noncomputable section

section General

variable (R : Type) [CommRing R] [Algebra ℂ R] (t : ℕ → R)

/-! ### Products in the model -/

theorem mword_append (w w' : List (Generator × ℕ)) :
    mword R t (w ++ w') = mword R t w * mword R t w' := by
  simp [mword, List.map_append, List.prod_append]

theorem wordWt_append (w w' : List (Generator × ℕ)) :
    wordWt (w ++ w') = wordWt w + wordWt w' := by
  simp [wordWt, List.map_append, List.sum_append]

/-- **The model is closed under products.** -/
theorem modelDeg_mul_le (r r' : ℕ) (d d' : ℤ) :
    modelDeg R t r d * modelDeg R t r' d' ≤ modelDeg R t (r + r') (d + d') := by
  rw [modelDeg, modelDeg, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨w, hw, hwt, rfl⟩, _, ⟨w', hw', hwt', rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨w ++ w', by simp [hw, hw'], by rw [wordWt_append, hwt, hwt'],
    mword_append R t w w'⟩

theorem mul_mem_modelDeg {r r' : ℕ} {d d' : ℤ} {x y : MPoly R}
    (hx : x ∈ modelDeg R t r d) (hy : y ∈ modelDeg R t r' d') :
    x * y ∈ modelDeg R t (r + r') (d + d') :=
  modelDeg_mul_le R t r r' d d' (Submodule.mul_mem_mul hx hy)

theorem one_mem_modelDeg : (1 : MPoly R) ∈ modelDeg R t 0 0 :=
  Submodule.subset_span ⟨[], rfl, rfl, rfl⟩

/-! ### Series in the model -/

/-- A series whose `s^a` coefficient lies in `modelDeg R t r (a + w)`. -/
def InS (r : ℕ) (w : ℤ) (F : PowerSeries (MPoly R)) : Prop :=
  ∀ a : ℕ, PowerSeries.coeff a F ∈ modelDeg R t r ((a : ℤ) + w)

variable {R t}

theorem InS.mul {r r' : ℕ} {w w' : ℤ} {F G : PowerSeries (MPoly R)}
    (hF : InS R t r w F) (hG : InS R t r' w' G) : InS R t (r + r') (w + w') (F * G) := by
  intro a
  rw [PowerSeries.coeff_mul]
  refine Submodule.sum_mem _ fun p hp => ?_
  have h := mul_mem_modelDeg R t (hF p.1) (hG p.2)
  have hsum : ((p.1 : ℤ) + w) + ((p.2 : ℤ) + w') = (a : ℤ) + (w + w') := by
    have := Finset.mem_antidiagonal.mp hp
    rw [← this]; push_cast; ring
  rwa [hsum] at h

theorem InS.add {r : ℕ} {w : ℤ} {F G : PowerSeries (MPoly R)}
    (hF : InS R t r w F) (hG : InS R t r w G) : InS R t r w (F + G) := fun a => by
  rw [map_add]; exact Submodule.add_mem _ (hF a) (hG a)

theorem InS.sub {r : ℕ} {w : ℤ} {F G : PowerSeries (MPoly R)}
    (hF : InS R t r w F) (hG : InS R t r w G) : InS R t r w (F - G) := fun a => by
  rw [map_sub]; exact Submodule.sub_mem _ (hF a) (hG a)

theorem InS.smul {r : ℕ} {w : ℤ} {F : PowerSeries (MPoly R)} (c : ℂ)
    (hF : InS R t r w F) : InS R t r w (c • F) := fun a => by
  rw [PowerSeries.coeff_smul]; exact Submodule.smul_mem _ c (hF a)

theorem InS.neg {r : ℕ} {w : ℤ} {F : PowerSeries (MPoly R)}
    (hF : InS R t r w F) : InS R t r w (-F) := fun a => by
  rw [map_neg]; exact Submodule.neg_mem _ (hF a)

theorem InS.congr {r : ℕ} {w w' : ℤ} {F G : PowerSeries (MPoly R)} (hF : InS R t r w F)
    (hFG : F = G) (hw : w = w') : InS R t r w' G := by
  subst hFG hw; exact hF

theorem InS.deriv {r : ℕ} {w : ℤ} {F : PowerSeries (MPoly R)} (hF : InS R t r w F) :
    InS R t r (w + 1) (PowerSeries.derivative (MPoly R) F) := fun a => by
  rw [PowerSeries.coeff_derivative]
  have h := hF (a + 1)
  have he : ((a + 1 : ℕ) : ℤ) + w = (a : ℤ) + (w + 1) := by push_cast; ring
  rw [he] at h
  have : PowerSeries.coeff (a + 1) F * ((a : MPoly R) + 1) =
      ((a + 1 : ℕ) : ℂ) • PowerSeries.coeff (a + 1) F := by
    rw [Algebra.smul_def, mul_comm]; push_cast; rfl
  rw [this]
  exact Submodule.smul_mem _ _ h

/-! ### The letter series and the generator series -/

variable (R t)

/-- The series of a letter. -/
def letSer (l : Generator) : PowerSeries (MPoly R) := PowerSeries.mk fun a => mletter R t (l, a)

theorem letSer_inS (l : Generator) :
    InS R t 1 (match l with | .current _ => 1 | .sugawara => 2) (letSer R t l) := by
  intro a
  rw [letSer, PowerSeries.coeff_mk]
  have h := mword_mem_modelDeg R t [(l, a)]
  simp only [mword_cons, mword_nil, mul_one, List.length_cons, List.length_nil, zero_add] at h
  convert h using 2
  cases l <;> simp [wordWt, letterWt]

/-- The generator series `X, Y, Z, J`, mapped into `R[u_j, v_j]`. -/
def gS (g : Fin 4) : PowerSeries (MPoly R) := PowerSeries.map (ι R).toRingHom (genSer g)

theorem coeff_gS (g : Fin 4) (a : ℕ) : PowerSeries.coeff a (gS R g) = ι R (genCoeff g a) := by
  rw [gS, PowerSeries.coeff_map]; rfl

/-- The series `T(s) = Σ t_j s^j`. -/
def tS : PowerSeries (MPoly R) := PowerSeries.mk fun a => MvPolynomial.C (t a)

theorem letSer_current_zero : letSer R t (.current 0) = gS R 0 := by
  refine PowerSeries.ext fun a => ?_; rw [letSer, PowerSeries.coeff_mk, coeff_gS]; rfl

theorem letSer_current_one : letSer R t (.current 1) = -gS R 2 := by
  refine PowerSeries.ext fun a => ?_
  rw [letSer, PowerSeries.coeff_mk, map_neg, coeff_gS]
  change ι R (PowerSeries.coeff a (curSer 1)) = _
  simp [curSer, genCoeff, genSer, zSer]

theorem letSer_current_two : letSer R t (.current 2) = (-2 : ℂ) • gS R 1 := by
  refine PowerSeries.ext fun a => ?_
  rw [letSer, PowerSeries.coeff_mk, PowerSeries.coeff_smul, coeff_gS]
  change ι R (PowerSeries.coeff a (curSer 2)) = _
  simp only [curSer, genCoeff, genSer, map_neg, map_add]
  rw [← map_smul]
  simp [ySer]
  module

theorem letSer_sugawara : letSer R t .sugawara = tS R t - gS R 3 := by
  refine PowerSeries.ext fun a => ?_
  rw [letSer, PowerSeries.coeff_mk, map_sub, coeff_gS, tS, PowerSeries.coeff_mk]
  change ι R (PowerSeries.coeff a (-jSer)) + MvPolynomial.C (t a) = _
  rw [map_neg, map_neg]
  simp only [genCoeff, genSer]
  rw [neg_add_eq_sub]
  rfl

theorem gS_inS_cur (g : Fin 3) : InS R t 1 1 (gS R g.castSucc) := by
  match g with
  | 0 => exact (letSer_inS R t (.current 0)).congr (letSer_current_zero R t) rfl
  | 1 =>
    have h := (letSer_inS R t (.current 2)).smul (-(1 / 2 : ℂ))
    refine h.congr ?_ rfl
    rw [letSer_current_two, smul_smul]; norm_num
  | 2 =>
    have h := (letSer_inS R t (.current 1)).neg
    refine h.congr ?_ rfl
    rw [letSer_current_one, neg_neg]; rfl

/-- The colour-zero `J`-block `J - T`. -/
theorem jt_inS : InS R t 1 2 (gS R 3 - tS R t) :=
  (letSer_inS R t .sugawara).neg.congr (by rw [letSer_sugawara]; ring) rfl

/-! ### The Wronskian identities -/

theorem map_derivative {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (F : PowerSeries A) :
    PowerSeries.map f (PowerSeries.derivative A F) =
      PowerSeries.derivative B (PowerSeries.map f F) := by
  ext n
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map, map_mul, map_add, map_natCast]

theorem jx_jet : jSer * xSer = ySer * dS xSer - xSer * dS ySer := by
  simp only [jSer, xSer, ySer, Derivation.leibniz, smul_eq_mul]; ring

theorem jy_jet : (2 : JetSer) * (jSer * ySer) = zSer * dS xSer - xSer * dS zSer := by
  simp only [jSer, xSer, ySer, zSer, Derivation.leibniz, smul_eq_mul]; ring

theorem jz_jet : jSer * zSer = zSer * dS ySer - ySer * dS zSer := by
  simp only [jSer, zSer, ySer, Derivation.leibniz, smul_eq_mul]; ring

theorem jj_jet : jSer * jSer = dS ySer * dS ySer - dS xSer * dS zSer := by
  simp only [jSer, xSer, ySer, zSer, Derivation.leibniz, smul_eq_mul]; ring

/-- `d/ds` of a mapped generator series. -/
def dG (g : Fin 4) : PowerSeries (MPoly R) := PowerSeries.derivative (MPoly R) (gS R g)

theorem map_dS (g : Fin 4) :
    PowerSeries.map (ι R).toRingHom (dS (genSer g)) = dG R g := by
  rw [dG, gS, ← map_derivative]

theorem gS_three_mul_gS_zero : gS R 3 * gS R 0 = gS R 1 * dG R 0 - gS R 0 * dG R 1 := by
  have h := congrArg (PowerSeries.map (ι R).toRingHom) jx_jet
  simp only [map_mul, map_sub] at h
  rw [show (dS xSer) = dS (genSer 0) from rfl, show (dS ySer) = dS (genSer 1) from rfl,
    map_dS, map_dS] at h
  exact h

theorem gS_three_mul_gS_one :
    gS R 3 * gS R 1 = (1 / 2 : ℂ) • (gS R 2 * dG R 0 - gS R 0 * dG R 2) := by
  have h := congrArg (PowerSeries.map (ι R).toRingHom) jy_jet
  simp only [map_mul, map_sub, map_ofNat] at h
  rw [show (dS xSer) = dS (genSer 0) from rfl, show (dS zSer) = dS (genSer 2) from rfl,
    map_dS, map_dS] at h
  change (2 : PowerSeries (MPoly R)) * (gS R 3 * gS R 1) = gS R 2 * dG R 0 - gS R 0 * dG R 2 at h
  rw [← h, two_mul, ← two_smul ℂ, smul_smul]
  norm_num


theorem gS_three_mul_gS_two : gS R 3 * gS R 2 = gS R 2 * dG R 1 - gS R 1 * dG R 2 := by
  have h := congrArg (PowerSeries.map (ι R).toRingHom) jz_jet
  simp only [map_mul, map_sub] at h
  rw [show (dS ySer) = dS (genSer 1) from rfl, show (dS zSer) = dS (genSer 2) from rfl,
    map_dS, map_dS] at h
  exact h

theorem gS_three_mul_gS_three : gS R 3 * gS R 3 = dG R 1 * dG R 1 - dG R 0 * dG R 2 := by
  have h := congrArg (PowerSeries.map (ι R).toRingHom) jj_jet
  simp only [map_mul, map_sub] at h
  rw [show (dS xSer) = dS (genSer 0) from rfl, show (dS ySer) = dS (genSer 1) from rfl,
    show (dS zSer) = dS (genSer 2) from rfl, map_dS, map_dS, map_dS] at h
  exact h

/-! ### The blocks -/

/-- The blocks of colour `c ∈ {0, 1}` and type `g`: `X, Y, Z, J - T` and
`T X, T Y, T Z, T J - T²/2`. -/
def blk (c : Fin 2) (g : Fin 4) : PowerSeries (MPoly R) :=
  if c = 0 then (if g = 3 then gS R 3 - tS R t else gS R g)
  else (if g = 3 then tS R t * gS R 3 - (1 / 2 : ℂ) • (tS R t * tS R t) else tS R t * gS R g)

/-- The weight offset of a block. -/
def bwt (c : Fin 2) (g : Fin 4) : ℤ := 1 + 2 * (c : ℤ) + (if g = 3 then 1 else 0)

theorem gS_inS {g : Fin 4} (hg : g ≠ 3) : InS R t 1 1 (gS R g) := by
  match g, hg with
  | 0, _ => exact gS_inS_cur R t 0
  | 1, _ => exact gS_inS_cur R t 1
  | 2, _ => exact gS_inS_cur R t 2
  | 3, hg => exact absurd rfl hg

theorem dG_inS {g : Fin 4} (hg : g ≠ 3) : InS R t 1 2 (dG R g) :=
  (gS_inS R t hg).deriv.congr rfl (by norm_num)

theorem sug_inS : InS R t 1 2 (tS R t - gS R 3) :=
  (letSer_inS R t .sugawara).congr (letSer_sugawara R t) rfl

/-- **The blocks lie in the model**: `c + 1` letters, weight offset `bwt c g`. -/
theorem blk_inS (c : Fin 2) (g : Fin 4) :
    InS R t ((c : ℕ) + 1) (bwt c g) (blk R t c g) := by
  have h0 : (0 : Fin 4) ≠ 3 := by decide
  have h1 : (1 : Fin 4) ≠ 3 := by decide
  have h2 : (2 : Fin 4) ≠ 3 := by decide
  match c, g with
  | 0, 0 => exact (gS_inS R t h0).congr (by simp [blk]) (by simp [bwt])
  | 0, 1 => exact (gS_inS R t h1).congr (by simp [blk]) (by simp [bwt])
  | 0, 2 => exact (gS_inS R t h2).congr (by simp [blk]) (by simp [bwt])
  | 0, 3 => exact (jt_inS R t).congr (by simp [blk]) (by simp [bwt])
  | 1, 0 =>
    have h := ((sug_inS R t).mul (gS_inS R t h0)).add ((gS_inS R t h1).mul (dG_inS R t h0) |>.sub
      ((gS_inS R t h0).mul (dG_inS R t h1)) |>.congr rfl (by norm_num))
    refine h.congr ?_ (by norm_num [bwt, h0, h1, h2])
    rw [← gS_three_mul_gS_zero]; simp [blk]; ring
  | 1, 1 =>
    have h := ((sug_inS R t).mul (gS_inS R t h1)).add
      ((((gS_inS R t h2).mul (dG_inS R t h0)).sub ((gS_inS R t h0).mul (dG_inS R t h2))).smul
        (1 / 2 : ℂ) |>.congr rfl (by norm_num))
    refine h.congr ?_ (by norm_num [bwt, h0, h1, h2])
    rw [← gS_three_mul_gS_one]; simp [blk]; ring
  | 1, 2 =>
    have h := ((sug_inS R t).mul (gS_inS R t h2)).add ((gS_inS R t h2).mul (dG_inS R t h1) |>.sub
      ((gS_inS R t h1).mul (dG_inS R t h2)) |>.congr rfl (by norm_num))
    refine h.congr ?_ (by norm_num [bwt, h0, h1, h2])
    rw [← gS_three_mul_gS_two]; simp [blk]; ring
  | 1, 3 =>
    have h := ((((dG_inS R t h1).mul (dG_inS R t h1)).sub
      ((dG_inS R t h0).mul (dG_inS R t h2))).sub ((sug_inS R t).mul (sug_inS R t))).smul
        (1 / 2 : ℂ)
    refine h.congr ?_ (by norm_num [bwt, h0, h1, h2])
    rw [← gS_three_mul_gS_three]
    simp only [blk, show (1 : Fin 2) ≠ 0 by decide, if_false, if_true]
    simp only [Algebra.smul_def]
    have hc : algebraMap ℂ (PowerSeries (MPoly R)) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap ℂ (PowerSeries (MPoly R))) 2, ← map_mul]; norm_num
    linear_combination (tS R t * gS R 3) * hc

/-! ### Products of block coefficients -/

/-- The product `Π_i [s^{a_i}] blk (c_i, g_i)` of block coefficients. -/
def pblk {K : ℕ} (c : Fin K → Fin 2) (g : Fin K → Fin 4) (a : Fin K → ℕ) : MPoly R :=
  ∏ i, PowerSeries.coeff (a i) (blk R t (c i) (g i))

/-- **Products of block coefficients lie in the model.** -/
theorem pblk_mem : ∀ {K : ℕ} (c : Fin K → Fin 2) (g : Fin K → Fin 4) (a : Fin K → ℕ),
    pblk R t c g a ∈ modelDeg R t (∑ i, ((c i : ℕ) + 1)) (∑ i, ((a i : ℤ) + bwt (c i) (g i)))
  | 0, c, g, a => by simpa [pblk] using one_mem_modelDeg R t
  | K + 1, c, g, a => by
    rw [pblk, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact mul_mem_modelDeg R t (blk_inS R t (c 0) (g 0) (a 0))
      (pblk_mem (fun i => c i.succ) (fun i => g i.succ) (fun i => a i.succ))

end General

end

end VOA.TwoSeries.ModelChar
