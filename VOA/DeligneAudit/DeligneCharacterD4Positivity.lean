/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp12
import VOA.DeligneAudit.D4FusionF

/-!
# `D4DemazurePositivity` from U5 and U6

* `coeff`: if U6 is stated with the algorithmic integer character `hilbSeriesZ` (no truncation),
  `hilbSeriesZ n = ∑_d q^{nd}[n,d] F_{n-d}`, then nonnegativity follows from U5: the zero module gives
  `F ≥ 0`, and the `q`-binomials are nonnegative (`hilbInt_nonneg_of_fusion`).
* `energy`: every term of `q^{-m²}C_m` has `q`-exponent `≥ -m²`.  This is proved from the D₄ identity
  `[s^{2m}] CT_x Θ M = (2/(q)_m) C_m` (the finite identity): the left side has coefficients in
  `ℚ⟦r⟧`, and `demazureChar` is normalised (`energy_holds`).
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-! ## `F ≥ 0` from U5 -/

open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.SectorWeyl in
theorem F_coeff_nonneg {S : DeligneSectorData} {F : ℕ → PowerSeries ℚ} (hU5 : FusionModuleBoundG S F)
    (m b : ℕ) : 0 ≤ coeff b (F m) := by
  let ρ : CurrentModule S.f PUnit := ⟨fun _ _ => 0, fun _ _ _ _ _ => Subsingleton.elim _ _⟩
  have hw : LocalWeylRelG S ρ (0 : PUnit) m := ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _, fun _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ => Subsingleton.elim _ _⟩
  have h := hU5.le m PUnit ρ 0 hw b
  exact le_trans (by positivity) h

/-! ## Coefficient positivity from U5 + U6 (integer form) -/

/-- The algorithmic integer Hilbert series `∑_N hilbInt n N qᴺ` (no truncation). -/
def hilbSeriesZ (n : ℕ) : PowerSeries ℚ := PowerSeries.mk fun N => (D4K.hilbInt n N : ℚ)

/-- Nonnegative coefficients. -/
def NN (f : PowerSeries ℚ) : Prop := ∀ N, 0 ≤ coeff N f

theorem NN.add {f g : PowerSeries ℚ} (hf : NN f) (hg : NN g) : NN (f + g) := fun N => by
  rw [map_add]; exact add_nonneg (hf N) (hg N)

theorem NN.mul {f g : PowerSeries ℚ} (hf : NN f) (hg : NN g) : NN (f * g) := fun N => by
  rw [coeff_mul]; exact Finset.sum_nonneg fun p _ => mul_nonneg (hf _) (hg _)

theorem NN_X_pow (k : ℕ) : NN (X ^ k : PowerSeries ℚ) := fun N => by
  rw [coeff_X_pow]; split_ifs <;> norm_num

theorem NN_one : NN (1 : PowerSeries ℚ) := by simpa using NN_X_pow 0

theorem NN_qbinom : ∀ n k, NN (VOA.DeligneGaussian.qbinom (X : PowerSeries ℚ) n k)
  | _, 0 => by rw [VOA.DeligneGaussian.qbinom_zero_right]; exact NN_one
  | 0, _ + 1 => fun N => by simp [VOA.DeligneGaussian.qbinom]
  | n + 1, k + 1 => by
      rw [VOA.DeligneGaussian.qbinom_succ_succ]
      exact ((NN_X_pow _).mul (NN_qbinom n k)).add (NN_qbinom n (k + 1))

theorem NN_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (h : ∀ i ∈ s, NN (f i)) :
    NN (∑ i ∈ s, f i) := fun N => by
  rw [map_sum]; exact Finset.sum_nonneg fun i hi => h i hi N

/-! ## Energy from integrality -/

/-- Normalised term lists: distinct monomials, nonzero coefficients. -/
def NF (g : LPoly) : Prop := (g.map Prod.fst).Nodup ∧ ∀ t ∈ g, t.2 ≠ 0

theorem addTerm_keys (t : Term) : ∀ s : LPoly, (addTerm t s).map Prod.fst =
    if t.1 ∈ s.map Prod.fst then s.map Prod.fst else s.map Prod.fst ++ [t.1]
  | [] => by simp [addTerm]
  | u :: rest => by
      by_cases h : t.1 = u.1
      · simp [addTerm, h]
      · have ih := addTerm_keys t rest
        simp only [addTerm, if_neg h, List.map_cons, ih, List.mem_cons]
        split_ifs with h1 h2 h2 <;> simp_all

theorem addTerm_nodup (t : Term) (s : LPoly) (h : (s.map Prod.fst).Nodup) :
    ((addTerm t s).map Prod.fst).Nodup := by
  rw [addTerm_keys]
  split_ifs with h1
  · exact h
  · exact h.append (List.nodup_singleton _) (by simpa using h1)

theorem foldr_addTerm_nodup (f : LPoly) : ((f.foldr addTerm []).map Prod.fst).Nodup := by
  induction f with
  | nil => simp
  | cons t f ih => exact addTerm_nodup t _ ih

theorem normalize_NF (f : LPoly) : NF (normalize f) := by
  refine ⟨?_, fun t ht => (decide_eq_true_iff.mp (List.mem_filter.mp ht).2)⟩
  exact (foldr_addTerm_nodup f).sublist (List.Sublist.map _ List.filter_sublist)

theorem demazureChar_NF (m : ℕ) : NF (demazureChar cartanD4 thetaD4 wordD4 m) := by
  rcases m with _ | m
  · rw [show demazureChar cartanD4 thetaD4 wordD4 0 = [((List.replicate 4 0, 0), 1)] from rfl]
    refine ⟨by simp, fun t ht => ?_⟩
    rw [List.mem_singleton] at ht; subst ht; decide
  · rw [demazureChar, Function.iterate_succ_apply']
    generalize (demazureStep cartanD4 thetaD4 wordD4)^[m] _ = g
    rw [demazureStep, wordD4, List.foldr_cons, demazureFin]
    exact normalize_NF _

/-- Integral elements of `𝕜[x,z]`: no negative powers of `r`. -/
def IntR (g : D4K.R) : Prop := ∀ (v : D4K.V) (e : ℤ), e < 0 → (g v).coeff e = 0

theorem IntR_ιR (f : R') : IntR (ιR f) := by
  intro v e he
  rw [ιR_apply]
  show (HahnSeries.ofPowerSeries ℤ ℚ (f v)).coeff e = 0
  rw [PowerSeries.coeff_coe, if_pos he]

/-- `f ↦ ∑_v f(v) θ(-v₀) z^{v with x killed}`. -/
def ctQ (f : R') : R' := f.sum fun v c => AddMonoidAlgebra.single (D4K.killX v) (c * thP (-(v 0)))

theorem ctTheta_ιR (f : R') : D4K.ctTheta (ιR f) = ιR (ctQ f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero]; exact (map_zero ιR).symm
  | add f g hf hg =>
      rw [map_add, map_add, hf, hg, ← map_add]
      congr 1
      exact (Finsupp.sum_add_index' (fun _ => by rw [zero_mul, AddMonoidAlgebra.single_zero])
        (fun _ _ _ => by rw [add_mul, AddMonoidAlgebra.single_add])).symm
  | single v c =>
      rw [ιR_single, D4K.ctFun_mon, ctQ, Finsupp.sum_single_index (by rw [zero_mul, AddMonoidAlgebra.single_zero]),
        ιR_single, map_mul, coeK_thP]

theorem smul_ιR (c : P) (h : R') : coeK c • ιR h = ιR (c • h) := by
  refine Finsupp.ext fun v => ?_
  show coeK c * (ιR h) v = (ιR (c • h)) v
  rw [ιR_apply, ιR_apply]
  show coeK c * coeK (h v) = coeK (c * h v)
  rw [map_mul]

theorem Cdem_integral (m : ℕ) : IntR (D4K.Cdem m) := by
  have h := D4K.Ikernel_coeff_even D4Finite.d4FiniteIdentity_holds m
  have h2 : (2 : D4K.Kq) ≠ 0 := by
    rw [show (2 : D4K.Kq) = HahnSeries.C (2 : ℚ) from (map_ofNat HahnSeries.C 2).symm]
    exact HahnSeries.C_ne_zero two_ne_zero
  have hC : D4K.Cdem m = ((2 : D4K.Kq)⁻¹ * D4K.qpoch m) • coeff (2 * m) D4K.Ikernel := by
    rw [h, smul_smul]
    rw [show (2 : D4K.Kq)⁻¹ * D4K.qpoch m * (2 * (D4K.qpoch m)⁻¹) = 1 by
      field_simp [D4K.qpoch_ne_zero m]]
    rw [one_smul]
  have hk : coeff (2 * m) D4K.Ikernel = ιR (ctQ (coeff (2 * m) kernelM')) := by
    rw [D4K.Ikernel, D4K.coeff_smap, ← ιS_kernelM', coeff_map, ctTheta_ιR]
  have hs : (2 : D4K.Kq)⁻¹ * D4K.qpoch m = coeK (PowerSeries.C (1 / 2 : ℚ) * qpochP m) := by
    rw [map_mul, coeK_qpochP]
    congr 1
    rw [show coeK (PowerSeries.C (1 / 2 : ℚ)) = HahnSeries.C (1 / 2 : ℚ) from HahnSeries.ofPowerSeries_C _]
    rw [show (2 : D4K.Kq) = HahnSeries.C (2 : ℚ) from (map_ofNat HahnSeries.C 2).symm, ← map_inv₀]
    norm_num
  rw [hC, hk, hs, smul_ιR]
  exact IntR_ιR _

theorem rootToV_inj {μ ν : List ℤ} (hμ : ∃ a b c d : ℤ, μ = [a, b, c, d])
    (hν : ∃ a b c d : ℤ, ν = [a, b, c, d]) (h : D4K.rootToV μ = D4K.rootToV ν) : μ = ν := by
  obtain ⟨a, b, c, d, rfl⟩ := hμ
  obtain ⟨a', b', c', d', rfl⟩ := hν
  rw [D4K.rootToV_four, D4K.rootToV_four] at h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  simp [D4K.rootV, D4K.zv, Pi.single_apply] at h1 h2 h3 h4
  have : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by omega
  obtain ⟨rfl, rfl, rfl, rfl⟩ := this
  rfl

theorem termR_apply_coeff (t : Term) (v : D4K.V) (e : ℤ) :
    ((D4K.termR t) v).coeff (2 * e) =
      if D4K.rootToV t.1.1 = v ∧ t.1.2 = e then (t.2 : ℚ) else 0 := by
  rw [D4K.termR, D4K.mon]
  show ((Finsupp.single (D4K.rootToV t.1.1) (D4K.qq ^ t.1.2 * (t.2 : D4K.Kq))) v).coeff (2 * e) = _
  rw [Finsupp.single_apply]
  by_cases h1 : D4K.rootToV t.1.1 = v
  · rw [if_pos h1]
    rw [D4K.qq_zpow, show ((t.2 : ℤ) : D4K.Kq) = HahnSeries.C (t.2 : ℚ) by rfl, HahnSeries.C_apply,
      HahnSeries.single_mul_single, one_mul, add_zero]
    by_cases h2 : t.1.2 = e
    · rw [if_pos ⟨h1, h2⟩, h2, HahnSeries.coeff_single_same]
    · rw [if_neg (fun h => h2 h.2), HahnSeries.coeff_single_of_ne (by omega)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]; rfl

theorem sum_key (g : LPoly) (hnd : (g.map Prod.fst).Nodup) (t0 : Term) (ht : t0 ∈ g) :
    (g.map fun t => if t.1 = t0.1 then (t.2 : ℚ) else 0).sum = t0.2 := by
  induction g with
  | nil => simp at ht
  | cons u g ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp ht with rfl | ht'
      · rw [if_pos rfl]
        rw [List.sum_eq_zero, add_zero]
        intro x hx
        obtain ⟨t, htg, rfl⟩ := List.mem_map.mp hx
        rw [if_neg]
        intro h; exact hnd.1 (h ▸ List.mem_map_of_mem htg)
      · rw [ih hnd.2 ht', if_neg, zero_add]
        intro h; exact hnd.1 (h ▸ List.mem_map_of_mem ht')

theorem sum_termR_coeff (L : LPoly) (v : D4K.V) (e : ℤ) :
    ((L.map D4K.termR).sum v).coeff (2 * e) =
      (L.map fun t => if D4K.rootToV t.1.1 = v ∧ t.1.2 = e then (t.2 : ℚ) else 0).sum := by
  induction L with
  | nil => rfl
  | cons t L ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ← ih, ← termR_apply_coeff]
      show ((D4K.termR t v) + ((L.map D4K.termR).sum v)).coeff (2 * e) = _
      rw [HahnSeries.coeff_add]

/-- **Energy** from integrality of the D₄ identity. -/
theorem energy_holds (m : ℕ) :
    ∀ t ∈ demazureChar cartanD4 thetaD4 wordD4 m, 0 ≤ t.1.2 + (m : ℤ) * m := by
  intro t0 ht0
  by_contra hneg
  push_neg at hneg
  have hgood := (D4K.toR_demazureChar m).1
  have hnf := demazureChar_NF m
  have hint := Cdem_integral m (D4K.rootToV t0.1.1) (2 * (t0.1.2 + m * m)) (by omega)
  rw [D4K.Cdem, ← (D4K.toR_demazureChar m).2] at hint
  change ((D4K.qq ^ (m * m)) * (D4K.toR (demazureChar cartanD4 thetaD4 wordD4 m))
    (D4K.rootToV t0.1.1)).coeff _ = 0 at hint
  rw [show D4K.qq ^ (m * m) = HahnSeries.single (2 * ((m * m : ℕ) : ℤ)) (1 : ℚ) by
    rw [← zpow_natCast, D4K.qq_zpow], show 2 * (t0.1.2 + (m : ℤ) * m) = 2 * t0.1.2 + 2 * ((m * m : ℕ) : ℤ) by
    push_cast; ring, HahnSeries.coeff_single_mul_add, one_mul] at hint
  rw [D4K.toR, sum_termR_coeff] at hint
  have hkey : (demazureChar cartanD4 thetaD4 wordD4 m).map (fun t =>
      if D4K.rootToV t.1.1 = D4K.rootToV t0.1.1 ∧ t.1.2 = t0.1.2 then (t.2 : ℚ) else 0) =
      (demazureChar cartanD4 thetaD4 wordD4 m).map (fun t => if t.1 = t0.1 then (t.2 : ℚ) else 0) := by
    refine List.map_congr_left fun t ht => ?_
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact Prod.ext (rootToV_inj (hgood t ht) (hgood t0 ht0) h1) h2
    · intro h; rw [h]; exact ⟨rfl, rfl⟩
  rw [hkey, sum_key _ hnf.1 t0 ht0] at hint
  exact hnf.2 t0 ht0 (by exact_mod_cast hint)

/-! ## Coefficient positivity from U5 for the unclamped fusion series -/

/-- The fusion series of the unclamped Demazure series. -/
def d4FusionFZ : ℕ → PowerSeries ℚ := DeligneCarrier.fusionOf hilbSeriesZ

open VOA.DeligneAudit.DeligneSector in
/-- **Coefficient positivity** from U5 for `d4FusionFZ`. -/
theorem hilbInt_nonneg_of_U5Z (hU5 : FusionModuleBoundG DeligneSector.D4.D4sector d4FusionFZ) (m N : ℕ) :
    0 ≤ D4K.hilbInt m N := by
  have hF : ∀ k, NN (d4FusionFZ k) := fun k b => F_coeff_nonneg hU5 k b
  have h := congrArg (coeff N) ((DeligneCarrier.mixedFusionRecursion_fusionOf hilbSeriesZ).eq m)
  rw [hilbSeriesZ, coeff_mk, VOA.DeligneGaussian.mixed_eq] at h
  have hnn : NN (∑ d ∈ Finset.range (m + 1), X ^ (d * (m + 0)) *
      VOA.DeligneGaussian.qbinom (X : PowerSeries ℚ) m d * d4FusionFZ (m + 0 - d)) :=
    NN_sum _ _ fun d _ => ((NN_X_pow _).mul (NN_qbinom _ _)).mul (hF _)
  have := hnn N
  rw [d4FusionFZ] at this
  rw [← h] at this
  exact_mod_cast this

/-- **`D4DemazurePositivity` from U5 (unclamped form).** -/
theorem d4DemazurePositivity_of_U5Z
    (hU5 : DeligneSector.FusionModuleBoundG DeligneSector.D4.D4sector d4FusionFZ) :
    D4K.D4DemazurePositivity :=
  ⟨energy_holds, hilbInt_nonneg_of_U5Z hU5⟩

theorem hilbSeries_eq_Z (hc : ∀ m N : ℕ, 0 ≤ D4K.hilbInt m N) :
    DeligneCarrier.hilbSeries d4DemazureHilb = hilbSeriesZ := by
  funext m
  ext N : 1
  rw [DeligneCarrier.hilbSeries, hilbSeriesZ, coeff_mk, coeff_mk, D4K.d4DemazureHilb_eq_toNat]
  have := hc m N
  rw [show ((D4K.hilbInt m N).toNat : ℚ) = (((D4K.hilbInt m N).toNat : ℤ) : ℚ) by push_cast; rfl,
    Int.toNat_of_nonneg this]

/-- **`d4FusionF = d4FusionFZ`** once the Demazure coefficients are nonnegative. -/
theorem d4FusionF_eq_Z
    (hU5 : DeligneSector.FusionModuleBoundG DeligneSector.D4.D4sector d4FusionFZ) :
    DeligneCarrier.d4FusionF = d4FusionFZ := by
  rw [DeligneCarrier.d4FusionF, hilbSeries_eq_Z (hilbInt_nonneg_of_U5Z hU5), d4FusionFZ]

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp

namespace VOA.DeligneAudit.D4Lie

open VOA.AffineGeneral VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneCarrier
  VOA.DeligneAudit.DeligneCharacter VOA.DeligneAudit.DeligneSector.D4
  VOA.DeligneAudit.DeligneSector

/-- **D₄ Deligne classical freeness from U5 alone** (stated for the unclamped fusion series
`d4FusionFZ = fusionOf (∑ hilbInt)`); Demazure positivity is derived. -/
theorem classicallyFree_of_fusionBoundZ (hU5 : FusionModuleBoundG D4sector D4Wp.d4FusionFZ) :
    CaseClassicallyFree .D4 W4 explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W4 1 ⟨explicitPresentation4.gen i,
          explicitPresentation4.gen_weight_one i⟩).toRingHom = explicitPresentation4.ideal := by
  have h := D4Wp.d4FusionF_eq_Z hU5
  exact classicallyFree_of_fusionBound (h ▸ hU5) (D4Wp.d4DemazurePositivity_of_U5Z hU5)

end VOA.DeligneAudit.D4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4Wp.energy_holds
#print axioms VOA.DeligneAudit.DeligneCharacter.D4Wp.d4DemazurePositivity_of_U5Z
#print axioms VOA.DeligneAudit.D4Lie.classicallyFree_of_fusionBoundZ
end AxiomAudit
