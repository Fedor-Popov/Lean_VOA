/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedGeneralFields
import VOA.Moonshine.LatticeTwistedProduct

/-! # Charge-parametric product for even lattices
Adapted from `LatticeTwistedProduct` using only `TwistedCharge` relations.
The existing generic oscillator and lattice-state results are reused. -/
namespace VOA.Moonshine.LatticeTwistedGeneral
open LatticeTwisted MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

variable (L : IntegralLattice) (hEven : L.Even) (C : TwistedCharge L)
  (hPos : L.PosDef)

theorem smul_hgen_hgen_nonneg (b c : Fin (rank L)) {n : ℤ} (hn : 0 ≤ n) :
    (latticeVOAGen L hEven hPos).smul (hgen L b) n (hgen L c)
      = if n = 1 ∧ b = c then latVacuumGen L else 0 := by
  rw [show hgen L c = (X (0, c) : FockN (rank L)) ⊗ₜ[ℂ] eGen L 0 from rfl, smul_hgen, chargeCoord_zero, zero_smul, ite_self, add_zero]
  rcases eq_or_lt_of_le hn with h0 | hpos
  · subst h0
    rw [oscN_zero, LinearMap.zero_apply, TensorProduct.zero_tmul, if_neg (by omega)]
  · rw [oscN_apply_pos _ _ _ hpos, pderiv_X, Pi.single_apply]
    by_cases h1 : n = 1
    · subst h1
      by_cases hbc : b = c
      · subst hbc
        simp [latVacuumGen, latStateGen, vacuumN]
      · rw [if_neg (show ((0 : ℕ), c) ≠ ((1 - 1 : ℤ).toNat, b) by
          intro h; exact hbc (Prod.ext_iff.mp h).2.symm), if_neg (by tauto)]
        simp
    · rw [if_neg (show ((0 : ℕ), c) ≠ ((n - 1).toNat, b) by
        intro h; have := (Prod.ext_iff.mp h).1; simp at this; omega), if_neg (by tauto)]
      simp

theorem star_FgT_YTLFld (b : Fin (rank L)) (α : L.carrier) (e : ℤ) {ℓ : ℤ} (hℓ : 0 ≤ ℓ) :
    star (1 / 2) (FgT b) ℓ (YTLFld L hEven C α e)
      = if ℓ = 0 then chargeCoord L α b • YTLFld L hEven C α (e + 1) else 0 := by
  rw [star_eq_sum_range _ _ _ _ 1 (fun i hi => by
    rw [← FgenTFld_eq_FgT]; exact prod_FgenTFld_YTLFld_pos L hEven C b α e (by omega)),
    Finset.sum_range_one]
  simp only [Nat.cast_zero, add_zero, cbinom_zero, one_smul, neg_zero, fzmul_zero_shift]
  split_ifs with h0
  · subst h0
    rw [← FgenTFld_eq_FgT]; exact prod_FgenTFld_YTLFld_zero L hEven C b α e
  · rw [← FgenTFld_eq_FgT]; exact prod_FgenTFld_YTLFld_pos L hEven C b α e (by omega)

include hPos in
theorem FL_echg (e : ℤ) (α : L.carrier) :
    FL L hEven C e (echg L α) = YTLFld L hEven C α e := by
  rw [echg_eq, show (1 : FockN (rank L)) = wordStateN [] from rfl,
    FL_wordState L hEven C hPos, Fw_nil]

include hPos in
theorem FL_smul_hgen_neg (e : ℤ) (b : Fin (rank L)) (k : ℕ) (w : LatModuleGen L) :
    FL L hEven C (e + 1) ((latticeVOAGen L hEven hPos).smul (hgen L b) (-(k : ℤ) - 1) w)
      = star (1 / 2) (FgT b) (-(k : ℤ) - 1) (FL L hEven C e w) := by
  rw [smul_hgen_neg, FL_mulLeft L hEven C hPos e (k, b)]

include hPos in
theorem genPF_word (l : List (ℕ × Fin (rank L))) : ∀ (α : L.carrier) (b : Fin (rank L))
    (e' ℓ : ℤ), star (1 / 2) (FgT b) ℓ (FL L hEven C e' (wordStateN l ⊗ₜ[ℂ] eGen L α))
      = FL L hEven C (e' + 1) ((latticeVOAGen L hEven hPos).smul (hgen L b) ℓ
          (wordStateN l ⊗ₜ[ℂ] eGen L α)) := by
  induction l with
  | nil =>
      intro α b e' ℓ
      rcases lt_or_ge ℓ 0 with hℓ | hℓ
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = -(k : ℤ) - 1 := ⟨(-ℓ - 1).toNat, by omega⟩
        exact (FL_smul_hgen_neg L hEven C hPos e' b k _).symm
      rw [show wordStateN ([] : List (ℕ × Fin (rank L))) ⊗ₜ[ℂ] eGen L α = echg L α from rfl,
        smul_hgen_echg_nonneg L hEven hPos b hℓ, FL_echg L hEven C hPos,
        star_FgT_YTLFld L hEven C b α e' hℓ]
      split_ifs
      · rw [map_smul, FL_echg L hEven C hPos]
      · rw [map_zero]
  | cons c l ih =>
      intro α b e' ℓ
      rcases lt_or_ge ℓ 0 with hℓ | hℓ
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = -(k : ℤ) - 1 := ⟨(-ℓ - 1).toNat, by omega⟩
        exact (FL_smul_hgen_neg L hEven C hPos e' b k _).symm
      set w := wordStateN l ⊗ₜ[ℂ] eGen L α with hw
      have hcw : wordStateN (c :: l) ⊗ₜ[ℂ] eGen L α
          = (latticeVOAGen L hEven hPos).smul (hgen L c.2) (-(c.1 : ℤ) - 1) w := by
        rw [smul_hgen_neg, hw, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, wordStateN_cons]
      have hFX : FL L hEven C e' (wordStateN (c :: l) ⊗ₜ[ℂ] eGen L α)
          = star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (FL L hEven C (e' - 1) w) := by
        rw [hcw, show e' = e' - 1 + 1 by ring, FL_smul_hgen_neg L hEven C hPos,
          show e' - 1 + 1 - 1 = e' - 1 by ring]
      rw [hFX]
      have hT := star_comm (latGenSet_local L hEven C hPos) (FgT_mem L hEven C b)
        (FgT_mem L hEven C c.2) (FL_mem L hEven C hPos (e' - 1) w) (1 / 2) (1 / 2) ℓ
        (-(c.1 : ℤ) - 1) 2 (fun s hs => prod_FgT_two_le _ _ (by omega))
      rw [Finset.sum_range_succ, Finset.sum_range_one, star_gT_gen, star_gT_gen,
        if_neg (by norm_num), if_pos rfl, star_zero_left, smul_zero, zero_add,
        star_smul_left (local_fzmul_one_left 1 _),
        show (1 / 2 : ℂ) + 1 / 2 = ((1 : ℤ) : ℂ) by norm_num, star_fzmul_one,
        ih α b (e' - 1) ℓ, sub_add_cancel,
        ← FL_smul_hgen_neg L hEven C hPos e' c.2 c.1] at hT
      rw [eq_add_of_sub_eq hT]
      -- the right side, through the commutator of `V_L`
      have hV := voa_comm (latticeVOAGen L hEven hPos) (hgen L b) (hgen L c.2) w ℓ
        (-(c.1 : ℤ) - 1) 2 (fun k hk => by
          rw [smul_hgen_hgen_nonneg L hEven hPos b c.2 (by omega), if_neg (by omega)])
      rw [Finset.sum_range_succ, Finset.sum_range_one,
        smul_hgen_hgen_nonneg L hEven hPos b c.2 (by norm_num),
        smul_hgen_hgen_nonneg L hEven hPos b c.2 (by norm_num), if_neg (by norm_num)] at hV
      rw [hcw, eq_add_of_sub_eq hV, map_add, map_add, map_smul, map_smul]
      simp only [PreVertexAlgebra.smul_zero_left, map_zero, smul_zero, zero_add]
      rw [← hw]
      congr 1
      have hz : fzmul 1 (FL L hEven C (e' - 1) w) = FL L hEven C (e' + 1) w := by
        rw [← FL_shift, show e' - 1 + 2 * 1 = e' + 1 by ring]
      have hvac : ∀ (n : ℤ) (x : LatModuleGen L),
          (latticeVOAGen L hEven hPos).smul (latVacuumGen L) n x = if n = -1 then x else 0 :=
        fun n x => PreVertexAlgebra.smul_vacuum_left _ n x
      by_cases hbc : b = c.2 <;> by_cases hn : ℓ + (-(c.1 : ℤ) - 1) - 1 = -1 <;>
        simp only [hbc, hn, Nat.cast_one, and_self, and_false, if_true, if_false,
          one_smul, zero_smul, hvac, map_zero, smul_zero,
          PreVertexAlgebra.smul_zero_left, hz]

include hPos in
theorem genPF (b : Fin (rank L)) (e' ℓ : ℤ) (w : LatModuleGen L) :
    star (1 / 2) (FgT b) ℓ (FL L hEven C e' w)
      = FL L hEven C (e' + 1) ((latticeVOAGen L hEven hPos).smul (hgen L b) ℓ w) := by
  have hl : ∀ v, Local (FgT (Tm := Space L hEven C) b).1 (FL L hEven C e' v).1 := fun v =>
    tloc L hEven C hPos (FgT_mem L hEven C b) (FL_mem L hEven C hPos e' v)
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, star_zero_right, PreVertexAlgebra.smul_zero_right, map_zero]
  | add x y hx hy =>
      rw [map_add, star_add_right (hl _) (hl _), hx, hy, PreVertexAlgebra.smul_add_right, map_add]
  | tmul p g =>
      induction p using MvPolynomial.induction_on' with
      | monomial m a =>
          induction g using Finsupp.induction_linear with
          | zero => rw [TensorProduct.tmul_zero, map_zero, star_zero_right,
              PreVertexAlgebra.smul_zero_right, map_zero]
          | add g₁ g₂ h₁ h₂ =>
              rw [TensorProduct.tmul_add, map_add, star_add_right (hl _) (hl _), h₁, h₂,
                PreVertexAlgebra.smul_add_right, map_add]
          | single α d =>
              have hs : (monomial m a : FockN (rank L)) ⊗ₜ[ℂ] Finsupp.single α d
                  = (a * d) • (wordStateN (monoWordN m) ⊗ₜ[ℂ] eGen L α) := by
                rw [wordStateN_monoWordN, eGen, show (monomial m a : FockN (rank L))
                    = a • monomial m 1 by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
                  show (Finsupp.single α d : L.carrier →₀ ℂ) = d • Finsupp.single α 1 by
                    rw [Finsupp.smul_single_one],
                  TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm d a]
              rw [hs, map_smul, star_smul_right (hl _), genPF_word L hEven C hPos,
                PreVertexAlgebra.smul_smul_right, map_smul]
      | add p q hp hq =>
          rw [TensorProduct.add_tmul, map_add, star_add_right (hl _) (hl _), hp, hq,
            PreVertexAlgebra.smul_add_right, map_add]

omit hEven in
theorem latState_induction {P : LatModuleGen L → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : ℂ) x, P x → P (c • x))
    (hw : ∀ (l : List (ℕ × Fin (rank L))) (β : L.carrier), P (wordStateN l ⊗ₜ[ℂ] eGen L β)) :
    ∀ x, P x := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd x y hx hy
  | tmul p g =>
      induction p using MvPolynomial.induction_on' with
      | monomial m a =>
          induction g using Finsupp.induction_linear with
          | zero => rw [TensorProduct.tmul_zero]; exact h0
          | add g₁ g₂ h₁ h₂ => rw [TensorProduct.tmul_add]; exact hadd _ _ h₁ h₂
          | single β d =>
              have hs : (monomial m a : FockN (rank L)) ⊗ₜ[ℂ] Finsupp.single β d
                  = (a * d) • (wordStateN (monoWordN m) ⊗ₜ[ℂ] eGen L β) := by
                rw [wordStateN_monoWordN, eGen, show (monomial m a : FockN (rank L))
                    = a • monomial m 1 by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
                  show (Finsupp.single β d : L.carrier →₀ ℂ) = d • Finsupp.single β 1 by
                    rw [Finsupp.smul_single_one],
                  TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm d a]
              rw [hs]
              exact hsmul _ _ (hw _ _)
      | add p q hp hq => rw [TensorProduct.add_tmul]; exact hadd _ _ hp hq

def PF (u v : LatModuleGen L) : Prop :=
  ∀ e e' ℓ : ℤ, star ((e : ℂ) / 2) (FL L hEven C e u) ℓ (FL L hEven C e' v)
    = FL L hEven C (e + e') ((latticeVOAGen L hEven hPos).smul (piE L e u) ℓ v)

section PFLinear

include hPos

theorem FLloc (e e' : ℤ) (u v : LatModuleGen L) : Local (FL L hEven C e u).1 (FL L hEven C e' v).1 :=
  FL_local L hEven C hPos e e' u v

theorem PF_zero_left (v : LatModuleGen L) : PF L hEven C hPos 0 v := by
  intro e e' ℓ
  rw [map_zero, star_zero_left, show piE L e 0 = 0 by simp [piE], PreVertexAlgebra.smul_zero_left,
    map_zero]

theorem PF_add_left {u u' v : LatModuleGen L} (h : PF L hEven C hPos u v)
    (h' : PF L hEven C hPos u' v) : PF L hEven C hPos (u + u') v := by
  intro e e' ℓ
  rw [map_add, star_add_left (FLloc L hEven C hPos _ _ _ _) (FLloc L hEven C hPos _ _ _ _), h, h',
    piE_add, PreVertexAlgebra.smul_add_left, map_add]

theorem PF_smul_left {u v : LatModuleGen L} (c : ℂ) (h : PF L hEven C hPos u v) :
    PF L hEven C hPos (c • u) v := by
  intro e e' ℓ
  rw [map_smul, star_smul_left (FLloc L hEven C hPos _ _ _ _), h, piE_smul,
    PreVertexAlgebra.smul_smul_left, map_smul]

theorem PF_zero_right (u : LatModuleGen L) : PF L hEven C hPos u 0 := by
  intro e e' ℓ
  rw [map_zero, star_zero_right, PreVertexAlgebra.smul_zero_right, map_zero]

theorem PF_add_right {u v v' : LatModuleGen L} (h : PF L hEven C hPos u v)
    (h' : PF L hEven C hPos u v') : PF L hEven C hPos u (v + v') := by
  intro e e' ℓ
  rw [map_add, star_add_right (FLloc L hEven C hPos _ _ _ _) (FLloc L hEven C hPos _ _ _ _), h, h',
    PreVertexAlgebra.smul_add_right, map_add]

theorem PF_smul_right {u v : LatModuleGen L} (c : ℂ) (h : PF L hEven C hPos u v) :
    PF L hEven C hPos u (c • v) := by
  intro e e' ℓ
  rw [map_smul, star_smul_right (FLloc L hEven C hPos _ _ _ _), h,
    PreVertexAlgebra.smul_smul_right, map_smul]

end PFLinear

include hPos in
theorem PF_word_echg (β : L.carrier)
    (hbase : ∀ α : L.carrier, PF L hEven C hPos (echg L α) (echg L β))
    (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    PF L hEven C hPos (wordStateN l ⊗ₜ[ℂ] eGen L α) (echg L β) := by
  induction l with
  | nil => exact hbase α
  | cons c l ih =>
      set w := wordStateN l ⊗ₜ[ℂ] eGen L α with hw
      set b := c.2
      set n := c.1
      have hcw : wordStateN (c :: l) ⊗ₜ[ℂ] eGen L α
          = (latticeVOAGen L hEven hPos).smul (hgen L b) (-(n : ℤ) - 1) w := by
        rw [smul_hgen_neg, hw, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, wordStateN_cons]
      intro e e' ℓ
      set X := FL L hEven C (e - 1) w with hX
      set Y := FL L hEven C e' (echg L β) with hY
      have hFu : FL L hEven C e (wordStateN (c :: l) ⊗ₜ[ℂ] eGen L α)
          = star (1 / 2) (FgT b) (-(n : ℤ) - 1) X := by
        rw [hcw, show e = e - 1 + 1 by ring, FL_smul_hgen_neg L hEven C hPos]
      -- bounds
      obtain ⟨N1, hN1⟩ := star_eventually_zero (FLloc L hEven C hPos (e - 1) e' w (echg L β))
        (((e - 1 : ℤ) : ℂ) / 2)
      obtain ⟨N2, hN2⟩ := star_eventually_zero (tloc L hEven C hPos (FgT_mem L hEven C b)
        (FL_mem L hEven C hPos e' (echg L β))) (1 / 2)
      obtain ⟨N3, hN3⟩ := PreVertexAlgebra.smul_eventually_zero
        (latticeVOAGen L hEven hPos).toPreVertexAlgebra (piE L (e - 1) w) (echg L β)
      set K : ℕ := (N1 - ℓ).toNat + N2.toNat + (N3 - ℓ).toNat + 1 with hK
      have hYi : ∀ (i : ℕ) (q : ℤ), star (((e - 1 : ℤ) : ℂ) / 2) X q
            (FL L hEven C (e' + 1) ((latticeVOAGen L hEven hPos).smul (hgen L b) i (echg L β)))
          = FL L hEven C (e - 1 + (e' + 1)) ((latticeVOAGen L hEven hPos).smul (piE L (e - 1) w) q
              ((latticeVOAGen L hEven hPos).smul (hgen L b) i (echg L β))) := by
        intro i q
        rw [smul_hgen_echg_nonneg L hEven hPos b (by omega)]
        split_ifs
        · rw [map_smul, star_smul_right (FLloc L hEven C hPos _ _ _ _), ih, PreVertexAlgebra.smul_smul_right,
            map_smul]
        · rw [map_zero, star_zero_right, PreVertexAlgebra.smul_zero_right, map_zero]
      rw [hFu, show (e : ℂ) / 2 = 1 / 2 + (((e - 1 : ℤ) : ℂ) / 2) by push_cast; ring,
        star_iterate_range (latGenSet_local L hEven C hPos) (FgT_mem L hEven C b)
          (FL_mem L hEven C hPos _ _) (FL_mem L hEven C hPos _ _) _ _ _ _ K (fun i hi =>
            ⟨hN1 _ (by omega), hN2 _ (by omega)⟩)]
      -- rewrite each term on the field side
      have hterm : ∀ i ∈ Finset.range K, ((-1 : ℂ) ^ i * gBinom (-(n : ℤ) - 1) i) •
          (star (1 / 2) (FgT b) (-(n : ℤ) - 1 - i) (star (((e - 1 : ℤ) : ℂ) / 2) X (ℓ + i) Y)
            - ((-1 : ℂ) ^ (-(n : ℤ) - 1)) • star (((e - 1 : ℤ) : ℂ) / 2) X
                (-(n : ℤ) - 1 + ℓ - i) (star (1 / 2) (FgT b) i Y))
          = FL L hEven C (e + e') (((-1 : ℂ) ^ i * gBinom (-(n : ℤ) - 1) i) •
              ((latticeVOAGen L hEven hPos).smul (hgen L b) (-(n : ℤ) - 1 - i)
                ((latticeVOAGen L hEven hPos).smul (piE L (e - 1) w) (ℓ + i) (echg L β))
              - ((-1 : ℂ) ^ (-(n : ℤ) - 1)) • (latticeVOAGen L hEven hPos).smul (piE L (e - 1) w)
                  (-(n : ℤ) - 1 + ℓ - i) ((latticeVOAGen L hEven hPos).smul (hgen L b) i
                    (echg L β)))) := by
        intro i _
        rw [ih (e - 1) e' (ℓ + i), genPF L hEven C hPos, hY, genPF L hEven C hPos, hYi,
          map_smul, map_sub, map_smul, show e - 1 + e' + 1 = e + e' by ring,
          show e - 1 + (e' + 1) = e + e' by ring]
      rw [Finset.sum_congr rfl hterm, ← map_sum, hcw, piE_smul_hgen L hEven hPos,
        VertexOperatorAlgebra.mode_iterate]
      congr 1
      symm
      refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
      rw [Function.mem_support] at hi
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hi
      rw [hN3 _ (by omega), PreVertexAlgebra.smul_zero_right,
        smul_hgen_echg_nonneg L hEven hPos b (by omega), if_neg (by omega),
        PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero, smul_zero]

include hPos in
theorem PF_echg_right (β : L.carrier)
    (hbase : ∀ α : L.carrier, PF L hEven C hPos (echg L α) (echg L β)) (u : LatModuleGen L) :
    PF L hEven C hPos u (echg L β) :=
  latState_induction L (P := fun u => PF L hEven C hPos u (echg L β))
    (PF_zero_left L hEven C hPos _) (fun _ _ hx hy => PF_add_left L hEven C hPos hx hy)
    (fun c _ hx => PF_smul_left L hEven C hPos c hx)
    (fun l α => PF_word_echg L hEven C hPos β hbase l α) u

include hPos in
theorem PF_word (hbase : ∀ α β : L.carrier, PF L hEven C hPos (echg L α) (echg L β))
    (l : List (ℕ × Fin (rank L))) (β : L.carrier) :
    ∀ u, PF L hEven C hPos u (wordStateN l ⊗ₜ[ℂ] eGen L β) := by
  induction l with
  | nil => exact PF_echg_right L hEven C hPos β (fun α => hbase α β)
  | cons c l ih =>
      intro u e e' ℓ
      set v := wordStateN l ⊗ₜ[ℂ] eGen L β with hv
      set b := c.2
      set p : ℤ := -(c.1 : ℤ) - 1 with hp
      have hcv : wordStateN (c :: l) ⊗ₜ[ℂ] eGen L β
          = (latticeVOAGen L hEven hPos).smul (hgen L b) p v := by
        rw [hp, smul_hgen_neg, hv, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, wordStateN_cons]
      have hFv : FL L hEven C e' (wordStateN (c :: l) ⊗ₜ[ℂ] eGen L β)
          = star (1 / 2) (FgT b) p (FL L hEven C (e' - 1) v) := by
        rw [hcv, hp, show e' = e' - 1 + 1 by ring, FL_smul_hgen_neg L hEven C hPos,
          show e' - 1 + 1 - 1 = e' - 1 by ring]
      -- a common bound for the generator products against `u`
      obtain ⟨K1, hK1⟩ := exists_prod_offset_zero (tloc L hEven C hPos (FgT_mem L hEven C b)
        (FL_mem L hEven C hPos e u)) 0
      obtain ⟨K2, hK2⟩ := PreVertexAlgebra.smul_eventually_zero
        (latticeVOAGen L hEven hPos).toPreVertexAlgebra (hgen L b) (piE L e u)
      set Lb : ℕ := K1 + K2.toNat with hLb
      have hT := star_comm (latGenSet_local L hEven C hPos) (FgT_mem L hEven C b)
        (FL_mem L hEven C hPos e u) (FL_mem L hEven C hPos (e' - 1) v) (1 / 2) ((e : ℂ) / 2) p ℓ Lb
        (fun s hs => by have := hK1 s (by omega); rwa [zero_add] at this)
      rw [ih u e (e' - 1) ℓ, genPF L hEven C hPos, show e + (e' - 1) + 1 = e + e' by ring] at hT
      have hterm : ∀ s ∈ Finset.range Lb, gBinom p s • star (1 / 2 + (e : ℂ) / 2)
          (star (1 / 2) (FgT b) s (FL L hEven C e u)) (p + ℓ - s) (FL L hEven C (e' - 1) v)
          = gBinom p s • FL L hEven C (e + e') ((latticeVOAGen L hEven hPos).smul
              ((latticeVOAGen L hEven hPos).smul (hgen L b) s (piE L e u)) (p + ℓ - s) v) := by
        intro s _
        rw [genPF L hEven C hPos, show (1 / 2 : ℂ) + (e : ℂ) / 2 = ((e + 1 : ℤ) : ℂ) / 2 by
            push_cast; ring, ih _ (e + 1) (e' - 1), piE_smul_hgen L hEven hPos,
          show e + 1 - 1 = e by ring, show e + 1 + (e' - 1) = e + e' by ring]
      rw [Finset.sum_congr rfl hterm] at hT
      have hV := voa_comm (latticeVOAGen L hEven hPos) (hgen L b) (piE L e u) v p ℓ Lb
        (fun k hk => hK2 _ (by omega))
      rw [hFv, hcv, show (latticeVOAGen L hEven hPos).smul (piE L e u) ℓ
          ((latticeVOAGen L hEven hPos).smul (hgen L b) p v)
          = (latticeVOAGen L hEven hPos).smul (hgen L b) p
              ((latticeVOAGen L hEven hPos).smul (piE L e u) ℓ v)
            - ∑ s ∈ Finset.range Lb, gBinom p s • (latticeVOAGen L hEven hPos).smul
                ((latticeVOAGen L hEven hPos).smul (hgen L b) s (piE L e u)) (p + ℓ - s) v by
          rw [← hV]; abel, map_sub, map_sum]
      simp only [map_smul]
      rw [← hT]
      abel

include hPos in
theorem PF_of_base (hbase : ∀ α β : L.carrier, PF L hEven C hPos (echg L α) (echg L β))
    (u v : LatModuleGen L) : PF L hEven C hPos u v :=
  latState_induction L (P := fun v => PF L hEven C hPos u v)
    (PF_zero_right L hEven C hPos u) (fun _ _ hx hy => PF_add_right L hEven C hPos hx hy)
    (fun c _ hx => PF_smul_right L hEven C hPos c hx)
    (fun l β => PF_word L hEven C hPos hbase l β u) v

end VOA.Moonshine.LatticeTwistedGeneral
