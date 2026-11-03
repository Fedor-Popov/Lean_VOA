/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpSpan2Separate

/-!
# The cusp-localized Cramer frame and `QExpPrinciple24Away 2`

Rows `R_{(O,t)} = Π_{O' ≠ O} f_{O,O'}^N · τ_{1,O}^t τ_{2,O}^t` (products of weight-one
Eisenstein binomials). The jets of length `N` of the rows at all cusps form a triangular matrix
with good diagonal; the trace identity of `QExpSpan2Trace` and Cramer's rule
(`frame_cramer_awaySat`) then bound the coefficients of every full-level form of even weight.
-/

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace VOA.Classification.COne.SSHecke

variable {N : ℕ}

/-! ## Cusps are separated by the first column -/

theorem cuspStab_neg_one : (-1 : SL(2, ℤ)) ∈ cuspStab :=
  Subgroup.subset_closure (by simp)

theorem cuspStab_T_zpow (c : ℤ) : ModularGroup.T ^ c ∈ cuspStab := by
  have h : ModularGroup.T⁻¹ ∈ cuspStab := Subgroup.subset_closure (by simp)
  have := cuspStab.zpow_mem h (-c)
  rwa [inv_zpow', neg_neg] at this

/-- If `γ'⁻¹ γ` has first column `±e₁ (mod N)`, the two cosets lie in the same cusp orbit. -/
theorem cuspOrb_eq_of_firstColumn [NeZero N] (q q' : CosetQ N)
    (hcol : ((((cosetRep q')⁻¹ * cosetRep q : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = 1 ∨
        ((((cosetRep q')⁻¹ * cosetRep q : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = -1)
    (hcol' : ((((cosetRep q')⁻¹ * cosetRep q : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0) :
    (⟦q⟧ : CuspOrb N) = ⟦q'⟧ := by
  set g : SL(2, ℤ) := (cosetRep q')⁻¹ * cosetRep q with hg
  have hdet : (g 0 0 : ℤ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe; rwa [Matrix.det_fin_two] at this
  have hdetN : ((g 0 0 : ℤ) : ZMod N) * ((g 1 1 : ℤ) : ZMod N) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hcol', mul_zero, sub_zero] at this
    exact this
  -- `y g ∈ Γ(N)` for a suitable `y ∈ ⟨T, -1⟩`
  obtain ⟨y, hy, hδ⟩ : ∃ y ∈ cuspStab, y * g ∈ CongruenceSubgroup.Gamma N := by
    rcases hcol with h1 | h1
    · have h11 : ((g 1 1 : ℤ) : ZMod N) = 1 := by rw [h1, one_mul] at hdetN; exact hdetN
      refine ⟨ModularGroup.T ^ (-(g 0 1)), cuspStab_T_zpow _, ?_⟩
      rw [CongruenceSubgroup.Gamma_mem]
      simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      push_cast
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h1, h11, hcol']
    · have h11 : ((g 1 1 : ℤ) : ZMod N) = -1 := by
        rw [h1] at hdetN
        have := congrArg (fun z => -z) hdetN
        simpa using this
      refine ⟨-ModularGroup.T ^ (g 0 1), cuspStab.mul_mem cuspStab_neg_one
        (cuspStab_T_zpow _) |> fun h => by simpa using h, ?_⟩
      rw [CongruenceSubgroup.Gamma_mem]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
        ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      push_cast
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h1, h11, hcol']
  -- transport to the cosets
  refine Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
    ⟨⟨slHom y, Subgroup.mem_map_of_mem _ hy⟩, ?_⟩))
  change slHom y • q' = q
  conv_lhs => rw [← Quotient.out_eq q']
  conv_rhs => rw [← Quotient.out_eq q]
  change slHom y • (QuotientGroup.mk q'.out : CosetQ N) = QuotientGroup.mk q.out
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hq : ((q.out : ↥𝒮ℒ) : GL (Fin 2) ℝ) = mapGL ℝ (cosetRep q)⁻¹ := by
    rw [map_inv, mapGL_cosetRep, inv_inv]
  have hq' : ((q'.out : ↥𝒮ℒ) : GL (Fin 2) ℝ) = mapGL ℝ (cosetRep q')⁻¹ := by
    rw [map_inv, mapGL_cosetRep, inv_inv]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, smul_eq_mul, coe_slHom, hq, hq']
  rw [← map_mul, ← map_inv, ← map_mul]
  refine mem_GammaGL_iff.mpr ⟨_, ?_, rfl⟩
  have hσ : cosetRep q = cosetRep q' * (y⁻¹ * (y * g)) := by
    rw [hg]; group
  have := (CongruenceSubgroup.Gamma_normal N).conj_mem _ (inv_mem hδ) (cosetRep q' * y⁻¹)
  convert this using 1
  rw [hσ]; group

/-! ## Cusp representatives -/

section Frame

variable [NeZero N]

open scoped Classical in
/-- Cusp representatives, the identity coset representing its own cusp. -/
def cuspRep (O : CuspOrb N) : CosetQ N :=
  if O = ⟦cosetOne N⟧ then cosetOne N else O.out

omit [NeZero N] in
theorem cuspRep_spec (O : CuspOrb N) : (⟦cuspRep O⟧ : CuspOrb N) = O := by
  unfold cuspRep
  split_ifs with h
  · exact h.symm
  · exact Quotient.out_eq O

omit [NeZero N] in
theorem cuspRep_one : cuspRep (⟦cosetOne N⟧ : CuspOrb N) = cosetOne N := by
  simp [cuspRep]

/-- The matrix of the cusp `O`. -/
def cuspSigma (O : CuspOrb N) : SL(2, ℤ) := cosetRep (cuspRep O)

theorem firstColumn_of_ne {O O' : CuspOrb N} (h : O ≠ O') :
    ¬ ((((((cuspSigma O')⁻¹ * cuspSigma O : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = 1 ∨
        ((((cuspSigma O')⁻¹ * cuspSigma O : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = -1) ∧
      ((((cuspSigma O')⁻¹ * cuspSigma O : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0) := by
  rintro ⟨h1, h2⟩
  apply h
  rw [← cuspRep_spec O, ← cuspRep_spec O']
  exact cuspOrb_eq_of_firstColumn _ _ h1 h2

/-! ## Integral series -/

/-- Series with all coefficients in a subalgebra `A`. -/
def IntegralIn {M : ℕ} (A : Subalgebra (zInv M) ℂ) (f : PowerSeries ℂ) : Prop :=
  ∀ n, PowerSeries.coeff n f ∈ A

theorem IntegralIn.mul {M : ℕ} {A : Subalgebra (zInv M) ℂ} {f g : PowerSeries ℂ}
    (hf : IntegralIn A f) (hg : IntegralIn A g) : IntegralIn A (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact A.sum_mem fun x _ => A.mul_mem (hf _) (hg _)

theorem IntegralIn.one {M : ℕ} {A : Subalgebra (zInv M) ℂ} : IntegralIn A 1 := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact A.one_mem
  · exact A.zero_mem

theorem IntegralIn.list_prod {M : ℕ} {A : Subalgebra (zInv M) ℂ} (l : List (PowerSeries ℂ))
    (hl : ∀ f ∈ l, IntegralIn A f) : IntegralIn A l.prod := by
  induction l with
  | nil => exact IntegralIn.one
  | cons f l ih =>
    rw [List.prod_cons]
    exact (hl f (by simp)).mul (ih fun g hg => hl g (by simp [hg]))

/-- The lift of an integral series to `PowerSeries A`. -/
def liftA {M : ℕ} (A : Subalgebra (zInv M) ℂ) (f : PowerSeries ℂ) (hf : IntegralIn A f) :
    PowerSeries A :=
  PowerSeries.mk fun n => ⟨PowerSeries.coeff n f, hf n⟩

theorem map_liftA {M : ℕ} (A : Subalgebra (zInv M) ℂ) (f : PowerSeries ℂ)
    (hf : IntegralIn A f) : PowerSeries.map (algebraMap A ℂ) (liftA A f hf) = f := by
  ext n
  simp [liftA]

theorem binSeries_integral {M : ℕ} (hM : M ≠ 0) (h2N : 2 * N ∣ M) (b : Bin N)
    (h1 : b.c1 ∈ frameRing M (weightOneStandardRoot N))
    (h2 : b.c2 ∈ frameRing M (weightOneStandardRoot N)) :
    IntegralIn (frameRing M (weightOneStandardRoot N)) (binSeries b) := by
  intro n
  simp only [binSeries, map_sub, PowerSeries.coeff_smul, smul_eq_mul, eisSeries,
    PowerSeries.coeff_mk]
  exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ h1 (eisCoeff_mem_frameRing hM h2N _ _))
    (Subalgebra.mul_mem _ h2 (eisCoeff_mem_frameRing hM h2N _ _))

/-! ## The separating and tangent binomials, for a fixed prime `p ∤ N` -/

variable {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (h24 : 24 ∣ N)

open scoped Classical in
/-- The separating binomial at `∞` for the pair `(O, O')`. -/
def sepBin0 (O O' : CuspOrb N) : Bin N :=
  if h : O = O' then ⟨0, 0, 0, 0⟩ else
    (exists_sep_bin hp hpN h24 _ (firstColumn_of_ne h)).choose

/-- The binomial vanishing at `O'` with good value at `O`. -/
def sepBin (O O' : CuspOrb N) : Bin N := (sepBin0 hp hpN h24 O O').act (cuspSigma O')⁻¹

theorem sepBin_coeffs (O O' : CuspOrb N) :
    (sepBin hp hpN h24 O O').c1 ∈ frameRing (sepModulus N p) (weightOneStandardRoot N) ∧
    (sepBin hp hpN h24 O O').c2 ∈ frameRing (sepModulus N p) (weightOneStandardRoot N) := by
  unfold sepBin sepBin0
  split_ifs with h
  · exact ⟨Subalgebra.zero_mem _, Subalgebra.zero_mem _⟩
  · obtain ⟨h1, h2, -⟩ := (exists_sep_bin hp hpN h24 _ (firstColumn_of_ne h)).choose_spec
    exact ⟨h1, h2⟩

theorem sepBin_vanish {O O' : CuspOrb N} (h : O ≠ O') :
    PowerSeries.constantCoeff (binSeries ((sepBin hp hpN h24 O O').act (cuspSigma O'))) = 0 := by
  unfold sepBin sepBin0
  rw [dif_neg h, ← Bin.act_mul, inv_mul_cancel, Bin.act_one, constantCoeff_binSeries]
  exact (exists_sep_bin hp hpN h24 _ (firstColumn_of_ne h)).choose_spec.2.2.1

theorem sepBin_good {O O' : CuspOrb N} (h : O ≠ O') :
    GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N))
      (PowerSeries.constantCoeff (binSeries ((sepBin hp hpN h24 O O').act (cuspSigma O)))) := by
  unfold sepBin sepBin0
  rw [dif_neg h, ← Bin.act_mul, constantCoeff_binSeries]
  exact (exists_sep_bin hp hpN h24 _ (firstColumn_of_ne h)).choose_spec.2.2.2

/-! ## Tangent binomials -/

/-- `τ₁ = cot(1) E_{(1,0)} - C(1,0) E_{(0,1)}`: vanishes at `∞` with good `q^{1/N}` term. -/
def tau1 : Bin N :=
  ⟨Cval ![(0 : ZMod N), 1], ![1, 0], Cval ![(1 : ZMod N), 0], ![0, 1]⟩

/-- `τ₂ = E_{(0,1)}`, good at `∞`. -/
def tau2 : Bin N := ⟨1, ![(0 : ZMod N), 1], 0, 0⟩

theorem const_tau1 : PowerSeries.constantCoeff (binSeries (tau1 (N := N))) = 0 := by
  rw [constantCoeff_binSeries]; simp only [tau1]; ring

theorem coeff1_tau1 (hN3 : 3 ≤ N) :
    PowerSeries.coeff 1 (binSeries (tau1 (N := N))) = Cval ![(0 : ZMod N), 1] := by
  simp only [binSeries, tau1, map_sub, PowerSeries.coeff_smul, smul_eq_mul, eisSeries,
    PowerSeries.coeff_mk, eisCoeff_one_e1 hN3, eisCoeff_one_e2 hN3]
  ring

theorem const_tau2 :
    PowerSeries.constantCoeff (binSeries (tau2 (N := N))) = Cval ![(0 : ZMod N), 1] := by
  rw [constantCoeff_binSeries]; simp [tau2]

theorem goodVal_cot1 {p : ℕ} (hN3 : 3 ≤ N) :
    GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N)) (Cval ![(0 : ZMod N), 1]) := by
  refine goodVal_Cval_cot _ rfl ?_
  change (2 : ZMod N) * 1 ≠ 0
  rw [mul_one]
  intro h
  have h2 : ((2 : ℕ) : ZMod N).val = 2 := ZMod.val_natCast_of_lt (by omega)
  rw [Nat.cast_ofNat, h, ZMod.val_zero] at h2
  omega

theorem GoodVal.finset_prod {M : ℕ} {A : Subalgebra (zInv M) ℂ} {ι : Type*} (s : Finset ι)
    (f : ι → ℂ) (hf : ∀ i ∈ s, GoodVal A (f i)) : GoodVal A (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨A.one_mem, by simp [A.one_mem], one_ne_zero⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-! ## Rows and their jets -/

section Rows

noncomputable instance cuspOrbDecEq : DecidableEq (CuspOrb N) := Classical.decEq _

variable {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (h24 : 24 ∣ N)

def tanBin1 (O : CuspOrb N) : Bin N := tau1.act (cuspSigma O)⁻¹
def tanBin2 (O : CuspOrb N) : Bin N := tau2.act (cuspSigma O)⁻¹

/-- The binomial list of the row `(O, t)`. -/
def rowList (i : CuspOrb N × Fin N) : List (Bin N) :=
  ((Finset.univ.erase i.1).toList.flatMap fun O' => List.replicate N (sepBin hp hpN h24 i.1 O')) ++
    (List.replicate i.2.val (tanBin1 i.1) ++ List.replicate i.2.val (tanBin2 i.1))

/-- A binomial's expansion at the cusp `O`. -/
def phiS (O : CuspOrb N) (b : Bin N) : PowerSeries ℂ := binSeries (b.act (cuspSigma O))

/-- The expansion of the row `i` at the cusp `O`. -/
def rowSeries (i : CuspOrb N × Fin N) (O : CuspOrb N) : PowerSeries ℂ :=
  ((rowList hp hpN h24 i).map (phiS O)).prod

theorem prod_map_flatMap_replicate {α γ β : Type*} [CommMonoid β] (L : List α) (n : ℕ)
    (f : α → γ) (φ : γ → β) :
    ((L.flatMap fun a => List.replicate n (f a)).map φ).prod =
      (L.map fun a => φ (f a) ^ n).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_replicate,
      List.prod_replicate, List.map_cons, List.prod_cons]

theorem rowSeries_eq (i : CuspOrb N × Fin N) (O : CuspOrb N) :
    rowSeries hp hpN h24 i O =
      (∏ O' ∈ Finset.univ.erase i.1, phiS O (sepBin hp hpN h24 i.1 O') ^ N) *
        (phiS O (tanBin1 i.1) ^ i.2.val * phiS O (tanBin2 i.1) ^ i.2.val) := by
  rw [rowSeries, rowList, List.map_append, List.prod_append, prod_map_flatMap_replicate,
    Finset.prod_map_toList, List.map_append, List.prod_append, List.map_replicate,
    List.prod_replicate, List.map_replicate, List.prod_replicate]

theorem phiS_own_tan1 (O : CuspOrb N) : phiS O (tanBin1 O) = binSeries (tau1 (N := N)) := by
  rw [phiS, tanBin1, ← Bin.act_mul, inv_mul_cancel, Bin.act_one]

theorem phiS_own_tan2 (O : CuspOrb N) : phiS O (tanBin2 O) = binSeries (tau2 (N := N)) := by
  rw [phiS, tanBin2, ← Bin.act_mul, inv_mul_cancel, Bin.act_one]

/-- Jets of a row vanish at the other cusps. -/
theorem rowSeries_coeff_other {i : CuspOrb N × Fin N} {O : CuspOrb N} (hO : O ≠ i.1)
    {s : ℕ} (hs : s < N) : PowerSeries.coeff s (rowSeries hp hpN h24 i O) = 0 := by
  have hX : (PowerSeries.X : PowerSeries ℂ) ∣ phiS O (sepBin hp hpN h24 i.1 O) :=
    PowerSeries.X_dvd_iff.mpr (sepBin_vanish hp hpN h24 (Ne.symm hO))
  have hXN : (PowerSeries.X : PowerSeries ℂ) ^ N ∣ rowSeries hp hpN h24 i O := by
    rw [rowSeries_eq]
    refine dvd_mul_of_dvd_left ((pow_dvd_pow_of_dvd hX N).trans
      (Finset.dvd_prod_of_mem (fun O' => phiS O (sepBin hp hpN h24 i.1 O') ^ N)
        (Finset.mem_erase.mpr ⟨hO, Finset.mem_univ _⟩))) _
  exact PowerSeries.X_pow_dvd_iff.mp hXN s hs

/-- At its own cusp the row is `q^{t/N}` times a good unit. -/
theorem rowSeries_own (hN3 : 3 ≤ N) (i : CuspOrb N × Fin N) :
    ∃ W : PowerSeries ℂ, rowSeries hp hpN h24 i i.1 = PowerSeries.X ^ i.2.val * W ∧
      GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N))
        (PowerSeries.constantCoeff W) := by
  obtain ⟨w, hw⟩ := PowerSeries.X_dvd_iff.mpr (const_tau1 (N := N))
  have hw0 : PowerSeries.constantCoeff w = Cval ![(0 : ZMod N), 1] := by
    rw [← coeff1_tau1 hN3, hw, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_succ_X_mul]
  refine ⟨(∏ O' ∈ Finset.univ.erase i.1, phiS i.1 (sepBin hp hpN h24 i.1 O') ^ N) *
    (w ^ i.2.val * binSeries (tau2 (N := N)) ^ i.2.val), ?_, ?_⟩
  · rw [rowSeries_eq, phiS_own_tan1, phiS_own_tan2, hw]
    ring
  · rw [map_mul, map_mul, map_pow, map_pow, map_prod, hw0, const_tau2]
    refine (GoodVal.finset_prod _ _ fun O' hO' => ?_).mul
      (((goodVal_cot1 hN3).pow _).mul ((goodVal_cot1 hN3).pow _))
    rw [map_pow]
    exact (sepBin_good hp hpN h24 (Ne.symm (Finset.mem_erase.mp hO').1)).pow N

theorem rowSeries_integral (i : CuspOrb N × Fin N) (O : CuspOrb N) :
    IntegralIn (frameRing (sepModulus N p) (weightOneStandardRoot N))
      (rowSeries hp hpN h24 i O) := by
  have hM := sepModulus_ne_zero (p := p) (NeZero.pos N)
  have h2N := two_mul_dvd_sepModulus N p
  refine IntegralIn.list_prod _ fun f hf => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
  have hc : b.c1 ∈ frameRing (sepModulus N p) (weightOneStandardRoot N) ∧
      b.c2 ∈ frameRing (sepModulus N p) (weightOneStandardRoot N) := by
    simp only [rowList, List.mem_append, List.mem_flatMap, List.mem_replicate] at hb
    rcases hb with ⟨O', -, -, rfl⟩ | (⟨-, rfl⟩ | ⟨-, rfl⟩)
    · exact sepBin_coeffs hp hpN h24 _ _
    · exact ⟨Cval_mem_frameRing hM h2N _, Cval_mem_frameRing hM h2N _⟩
    · exact ⟨Subalgebra.one_mem _, Subalgebra.zero_mem _⟩
  exact binSeries_integral hM h2N _ hc.1 hc.2

theorem rowList_length_even (i : CuspOrb N × Fin N) :
    Even ((rowList hp hpN h24 i).length : ℤ) := by
  have h2 : 2 ∣ N := dvd_trans (by norm_num) h24
  rw [Int.even_coe_nat]
  simp only [rowList, List.length_append, List.length_replicate, List.length_flatMap,
    List.map_const', List.sum_replicate, smul_eq_mul]
  exact (Even.mul_left (even_iff_two_dvd.mpr h2) _).add ⟨_, rfl⟩

end Rows

/-! ## Assembly -/

theorem awaySat_mul_left {M : ℕ} {L : Submodule ℤ ℂ} (c : ℂ) {z : ℂ} (hz : z ∈ awaySat M L) :
    c * z ∈ awaySat M (L.map (LinearMap.mulLeft ℤ c)) := by
  obtain ⟨e, he⟩ := hz
  refine ⟨e, ?_⟩
  have : (M : ℂ) ^ e * (c * z) = LinearMap.mulLeft ℤ c ((M : ℂ) ^ e * z) := by
    simp only [LinearMap.mulLeft_apply]; ring
  rw [this]
  exact Submodule.mem_map_of_mem he

theorem rank_injective (N : ℕ) {α : Type*} [Fintype α] :
    Function.Injective fun j : α × Fin N => N * (Fintype.equivFin α j.1).val + j.2.val := by
  rintro ⟨a, s⟩ ⟨a', s'⟩ h
  simp only at h
  have hs : s.val = s'.val := by
    have h1 := congrArg (· % N) h
    simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt s'.isLt] at h1
    exact h1
  have ha : (Fintype.equivFin α a).val = (Fintype.equivFin α a').val := by
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) s.isLt
    have h1 := congrArg (· / N) h
    simp only [Nat.mul_add_div hN, Nat.div_eq_of_lt s.isLt, Nat.div_eq_of_lt s'.isLt] at h1
    simpa using h1
  have ha' : a = a' := (Fintype.equivFin α).injective (Fin.ext ha)
  rw [ha', Fin.ext hs]

open scoped Classical in
/-- **Bounded denominators away from `p` for every full-level form of even weight.**
For `24 ∣ N`, a prime `p ∤ N`, and `F ∈ M_k(Γ(N))` with `k` even, all width-`N` coefficients
of `F` lie in `awaySat (sepModulus N p) L` for a finitely generated `L ⊂ ℂ`. -/
theorem fullLevel_coeff_awaySat {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (h24 : 24 ∣ N) {k : ℤ} (hk : Even k) (F : ModularForm (GammaGL N) k) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧
      ∀ n, PowerSeries.coeff n (qExpansion (N : ℝ) F) ∈ awaySat (sepModulus N p) L := by
  have hN := NeZero.pos N
  have hN3 : 3 ≤ N := by have := Nat.le_of_dvd hN h24; omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hP := nat_mem_strictPeriods_Gamma N
  set M := sepModulus N p with hMdef
  have hM : M ≠ 0 := sepModulus_ne_zero hN
  set A := frameRing M (weightOneStandardRoot N) with hAdef
  have hA : A.toSubmodule.FG := frameRing_fg hN (stdRoot_isPrimitiveRoot N).pow_eq_one
  -- data
  let ι := CuspOrb N × Fin N
  let fO : CuspOrb N → PowerSeries ℂ := fun O => qExpansion (N : ℝ) (gammaSlash F (cuspSigma O))
  let card : CuspOrb N → ℂ := fun O =>
    ((Finset.univ.filter fun q : CosetQ N => (⟦q⟧ : CuspOrb N) = O).card : ℂ)
  let Y : ι → PowerSeries ℂ := fun j => card j.1 • resPart N ((N - j.2.val) % N) (fO j.1)
  let B' : Matrix ι ι (PowerSeries A) := fun i j =>
    resShift N j.2.val (liftA A (rowSeries hp hpN h24 i j.1) (rowSeries_integral hp hpN h24 i j.1))
  let e : ι → ℕ := fun j => j.2.val
  let G : ι → PowerSeries ℂ := fun i =>
    qExpansion (N : ℝ) (ModularForm.trace 𝒮ℒ (F.mul (binProd (rowList hp hpN h24 i))))
  have hG : ∀ i, ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, PowerSeries.coeff n (G i) ∈ L :=
    fun i => levelOne_nat_hasFiniteCoeffLattice hN _
  -- the trace identities
  have hcusp : ∀ i O, cuspPsi (F.mul (binProd (rowList hp hpN h24 i))) (cuspRep O) =
      ∑ s ∈ Finset.range N, resPart N ((N - s) % N) (fO O) *
        resPart N s (rowSeries hp hpN h24 i O) := by
    intro i O
    rw [cuspPsi, ← resPart_zero_mul hN]
    congr 1
    change qExpansion (N : ℝ) (gammaSlash (F.mul _) (cuspSigma O)) = _
    rw [gammaSlash_mul_apply, ModularForm.qExpansion_mul hNR hP,
      qExpansion_gammaSlash_binProd]
    rfl
  have heq : ∀ i, ∑ j, PowerSeries.map (algebraMap A ℂ) (PowerSeries.X ^ e j * B' i j) * Y j =
      G i := by
    intro i
    have hk' : Even (k + ((rowList hp hpN h24 i).length : ℤ)) :=
      hk.add (rowList_length_even hp hpN h24 i)
    simp only [G]
    rw [qExpansion_trace_eq_orbits hk' _ cuspRep cuspRep_spec, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun O _ => ?_
    rw [hcusp, Finset.smul_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [B', e, Y, ← resPart_eq_X_pow_mul s.isLt]
    rw [mul_smul_comm, mul_comm, resPart_map, map_liftA]
    simp only [card]
    congr 3
    ext q
    simp only [Finset.mem_filter]
  -- the determinant
  have hentry : ∀ i j, ((PowerSeries.constantCoeff (B' i j) : A) : ℂ) =
      PowerSeries.coeff j.2.val (rowSeries hp hpN h24 i j.1) := by
    intro i j
    simp only [B', constantCoeff_resShift j.2.isLt, liftA, PowerSeries.coeff_mk]
  have hdet : IsUnit (Matrix.det fun i j => PowerSeries.constantCoeff (B' i j)) := by
    refine isUnit_det_of_triangular _ _ (rank_injective N) ?_ ?_
    · rintro ⟨O₀, t⟩ ⟨O, s⟩ hlt
      apply Subtype.ext
      rw [hentry, ZeroMemClass.coe_zero]
      by_cases hO : O = O₀
      · subst hO
        obtain ⟨W, hW, -⟩ := rowSeries_own hp hpN h24 hN3 (O, t)
        simp only at hlt ⊢
        have hst : s.val < t.val := by omega
        rw [hW, PowerSeries.coeff_X_pow_mul',
          if_neg (show ¬ ((O, t).2.val ≤ (O, s).2.val) from Nat.not_le.mpr hst)]
      · exact rowSeries_coeff_other hp hpN h24 hO s.isLt
    · rintro ⟨O, t⟩
      obtain ⟨W, hW, hgood⟩ := rowSeries_own hp hpN h24 hN3 (O, t)
      have hval : ((PowerSeries.constantCoeff (B' (O, t) (O, t)) : A) : ℂ) =
          PowerSeries.constantCoeff W := by
        rw [hentry]; simp only
        rw [hW, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
          PowerSeries.coeff_zero_eq_constantCoeff_apply]
      have hu := hgood.isUnit
      convert hu using 1
      exact Subtype.ext hval
  -- Cramer at the identity cusp
  set O₁ : CuspOrb N := ⟦cosetOne N⟧
  have hcr : ∀ s : Fin N, ∃ L : Submodule ℤ ℂ, L.FG ∧
      ∀ n, PowerSeries.coeff n (Y (O₁, s)) ∈ awaySat M L :=
    fun s => frame_cramer_awaySat hM A hA B' e hdet Y G hG heq (O₁, s)
  choose Ls hLs hYs using hcr
  set c := card O₁
  have hc : c ≠ 0 := by
    simp only [c, card, ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
    intro h
    have : cosetOne N ∈ (Finset.univ.filter fun q : CosetQ N => (⟦q⟧ : CuspOrb N) = O₁) := by
      simp [O₁]
    rw [h] at this
    simp at this
  have hfO : fO O₁ = qExpansion (N : ℝ) F := by
    simp only [fO, cuspSigma, O₁, cuspRep_one]
    rw [← quotientFunc_eq_gammaSlash, quotientFunc_cosetOne]
  refine ⟨(⨆ s, Ls s).map (LinearMap.mulLeft ℤ c⁻¹),
    (Submodule.fg_iSup _ hLs).map _, fun n => ?_⟩
  set s₀ : Fin N := ⟨(N - n % N) % N, Nat.mod_lt _ hN⟩
  have hres : n % N = ((N - s₀.val) % N) % N := by
    simp only [s₀, Nat.mod_mod]
    have hlt : n % N < N := Nat.mod_lt _ hN
    rcases Nat.eq_zero_or_pos (n % N) with h0 | hpos
    · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega : N - n % N < N), Nat.sub_sub_self hlt.le,
        Nat.mod_eq_of_lt hlt]
  have hY : PowerSeries.coeff n (Y (O₁, s₀)) = c * PowerSeries.coeff n (qExpansion (N : ℝ) F) := by
    simp only [Y, PowerSeries.coeff_smul, smul_eq_mul, coeff_resPart, if_pos hres, hfO]
    rfl
  have hmem : PowerSeries.coeff n (Y (O₁, s₀)) ∈ awaySat M (⨆ s, Ls s) := by
    obtain ⟨e', he'⟩ := hYs s₀ n
    exact ⟨e', Submodule.mem_iSup_of_mem s₀ he'⟩
  have := awaySat_mul_left c⁻¹ hmem
  rwa [hY, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] at this

/-- **`QExpPrinciple24Away k` for every even weight.** -/
theorem qExpPrinciple24Away_of_even {k : ℤ} (hk : Even k) : QExpPrinciple24Away k := by
  intro N hN h24 F p hp hpN
  letI : NeZero N := ⟨hN.ne'⟩
  have h2 : 2 ∣ N := dvd_trans (by norm_num) h24
  have hpN' : ¬ p ∣ N := (Nat.Prime.coprime_iff_not_dvd hp).mp hpN
  obtain ⟨L, hL, hc⟩ := fullLevel_coeff_awaySat hp hpN' h24 hk (restrictGamma1ToGamma hN F)
  refine ⟨sepModulus N p, not_dvd_sepModulus hp hpN' h2, L, hL, fun n => ?_⟩
  rw [← qExpansion_coeff_nat_mul hN F n]
  exact hc (N * n)

/-- **The target: `QExpPrinciple24Away 2`, unconditionally.** -/
theorem qExpPrinciple24Away_two : QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_of_even ⟨1, rfl⟩

end Frame

end VOA.Classification.COne.SSHecke
