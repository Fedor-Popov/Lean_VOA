/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieCocycle

/-!
# The cert `D₄` basis inside the lattice Lie algebra `d4Lie = (V_{D₄})₁`

`xs : Fin 28 → d4Lie` is the basis of `casimir_cert/cert_D4.json` realized in the lattice VOA:

* `xs i = α_i(-1)𝟙` for the Cartan indices `i < 4` (`α_i` the simple roots, `hvec i`);
* `xs a = u_a f(wt a) e^{wt a}` for the 24 root indices, `u_a = ±1` explicit and `f` the
  (noncomputable) coboundary sign of `D4LieCocycle`.

`bracket_xs`: **`⁅xs a, xs b⁆ = ∑ c, sZ a b c • xs c`**, the cert structure constants.  The proof
evaluates each bracket in the lattice VOA (`e^α₍₀₎e^β`, `α(-1)₍₀₎e^β`) and uses the coboundary
identity to replace `ε` by the explicit `ε'`; the resulting integer table is `model`, which equals
the cert table by `sZ_eq_model`.
-/

namespace VOA.DeligneAudit.D4Lie

open VOA VOA.LatGen VOA.LatGen.Screen VOA.IntegralLattice HeisenbergN VOA.CartanLattices
  VOA.AffineGeneral.LatticeLie VOA.AffineGeneral.CartanSimple

noncomputable section

/-! ## Root vectors and coroots for arbitrary lattice vectors -/

theorem mem_one_of_norm (v : Lat) (hv : formZ v v = 2) :
    latChargeGen d4 v ∈ (latticeVOAGen d4 d4_even d4_posDef).grading 1 :=
  latChargeGen_mem_grading_one d4 d4_even d4_posDef (by rw [d4_form_eq]; exact hv)

/-- `e^v` for a norm-two `v`. -/
def ev (v : Lat) (hv : formZ v v = 2) : d4Lie := ⟨latChargeGen d4 v, mem_one_of_norm v hv⟩

/-- `v(-1)𝟙`. -/
def hst (v : Lat) : d4Lie := ⟨hSt d4 v, hSt_mem_gradingLatGen d4 v⟩

theorem ev_congr {v w : Lat} (h : v = w) (hv : formZ v v = 2) (hw : formZ w w = 2) :
    ev v hv = ev w hw := by
  subst h; rfl

theorem hst_ev (v w : Lat) (hw : formZ w w = 2) :
    ⁅hst v, ev w hw⁆ = (formZ v w : ℂ) • ev w hw := by
  apply Subtype.ext
  show (latticeVOAGen d4 d4_even d4_posDef).smul (hSt d4 v) 0
      (latStateGen d4 (vacuumN (rank d4)) w) = _
  rw [smul_hSt_zero_latStateGen, d4_form_eq]
  rfl

theorem hst_hst (v w : Lat) : ⁅hst v, hst w⁆ = 0 := by
  apply Subtype.ext
  show (latticeVOAGen d4 d4_even d4_posDef).smul (hSt d4 v) 0 (latStateGen d4 (vSchur d4 w 1) 0) = 0
  rw [smul_hSt_zero_latStateGen, map_zero, Int.cast_zero, zero_smul]

theorem ev_ev_of_nonneg (v w : Lat) (hv : formZ v v = 2) (hw : formZ w w = 2)
    (h : 0 ≤ formZ v w) : ⁅ev v hv, ev w hw⁆ = 0 := by
  apply Subtype.ext
  show mode (YfullGen d4 d4_even d4_posDef (latChargeGen d4 v)) 0 (latChargeGen d4 w) = 0
  rw [← Qscr_eq_mode_YfullGen d4 d4_even d4_posDef,
    Qscr_latChargeGen_of_nonneg d4 (by rw [d4_form_eq]; exact h)]

theorem ev_ev_of_neg_one (v w : Lat) (hv : formZ v v = 2) (hw : formZ w w = 2)
    (hvw : formZ (v + w) (v + w) = 2) (h : formZ v w = -1) :
    ⁅ev v hv, ev w hw⁆ = latticeCocycle d4 v w • ev (v + w) hvw := by
  apply Subtype.ext
  show mode (YfullGen d4 d4_even d4_posDef (latChargeGen d4 v)) 0 (latChargeGen d4 w) =
    latticeCocycle d4 v w • latChargeGen d4 (v + w)
  rw [← Qscr_eq_mode_YfullGen d4 d4_even d4_posDef, Qscr_latChargeGen, EEVec_vacuum, d4_form_eq,
    h, if_pos (by norm_num)]
  norm_num [vSchur_zero]
  rfl

theorem ev_ev_neg (v : Lat) (hv : formZ v v = 2) (hv' : formZ (-v) (-v) = 2) :
    ⁅ev v hv, ev (-v) hv'⁆ = latticeCocycle d4 v (-v) • hst v := by
  apply Subtype.ext
  show mode (YfullGen d4 d4_even d4_posDef (latChargeGen d4 v)) 0 (latChargeGen d4 (-v)) = _
  rw [← Qscr_eq_mode_YfullGen d4 d4_even d4_posDef]
  exact Qscr_latChargeGen_neg d4 (by rw [d4_form_eq]; exact hv)

/-- `v ↦ v(-1)𝟙` is additive. -/
def hstHom : Lat →+ d4Lie where
  toFun := hst
  map_zero' := Subtype.ext (hSt_zero d4)
  map_add' v w := Subtype.ext (hSt_add d4 v w)

theorem hst_decomp (v : Lat) :
    hst v = (v 0 : ℂ) • hst (Pi.single 0 1) + (v 1 : ℂ) • hst (Pi.single 1 1) +
      (v 2 : ℂ) • hst (Pi.single 2 1) + (v 3 : ℂ) • hst (Pi.single 3 1) := by
  have h := congrArg hstHom (lat_decomp v)
  rw [map_sum, Fin.sum_univ_four] at h
  simp only [map_zsmul] at h
  change hst v = _ at h
  rw [h]
  simp only [← Int.cast_smul_eq_zsmul ℂ]
  rfl

/-! ## The cert basis -/

theorem hvec_eq (i : Fin 4) : hvec ⟨i.val, by omega⟩ = Pi.single i 1 := by
  ext j
  simp only [hvec, Pi.single_apply, Fin.ext_iff]

/-- The root vector attached to an index (`e^{wt 4}` on the Cartan indices, unused there). -/
def evR (a : Fin 28) : d4Lie := ev (wtR a) (wtR_norm a)

/-- **The cert basis of `d4Lie`.** -/
def xs (a : Fin 28) : d4Lie :=
  if a.val < 4 then hst (hvec a) else ((u a : ℂ) * f (wt a)) • evR a

theorem xs_cartan (a : Fin 28) (h : a.val < 4) : xs a = hst (hvec a) := by
  rw [xs, if_pos h]

theorem xs_root (a : Fin 28) (h : 4 ≤ a.val) :
    xs a = ((u a : ℂ) * f (wt a)) • ev (wt a) (wt_norm a h) := by
  rw [xs, if_neg (by omega), evR, ev_congr (wtR_root a h) (wtR_norm a) (wt_norm a h)]

theorem sgn_eq (n : ℤ) : ((sgn n : ℤ) : ℂ) = (-1 : ℂ) ^ n := by
  unfold sgn
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [if_pos (by omega), hk, ← two_mul, zpow_mul]; norm_num
  · rw [if_neg (by omega), hk, zpow_add₀ (by norm_num), zpow_mul]; norm_num

theorem u_sq (a : Fin 28) : (u a : ℂ) * (u a : ℂ) = 1 := by
  exact_mod_cast u_mul_self a

/-- A sum over `Fin 28` supported on the Cartan indices. -/
theorem sum_cartan {M : Type*} [AddCommMonoid M] (g : Fin 28 → M) (hg : ∀ c : Fin 28, 4 ≤ c.val → g c = 0) :
    ∑ c, g c = g 0 + g 1 + g 2 + g 3 := by
  rw [← Finset.sum_subset (Finset.subset_univ ({0, 1, 2, 3} : Finset (Fin 28)))]
  · simp [Finset.sum_insert, add_assoc]
  · intro c _ hc
    apply hg
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨h0, h1, h2, h3⟩ := hc
    have : c.val ≠ 0 := fun h => h0 (Fin.ext h)
    have : c.val ≠ 1 := fun h => h1 (Fin.ext h)
    have : c.val ≠ 2 := fun h => h2 (Fin.ext h)
    have : c.val ≠ 3 := fun h => h3 (Fin.ext h)
    omega

theorem sum_single {M : Type*} [AddCommMonoid M] [Module ℂ M] (x : Fin 28 → M) (c0 : Fin 28) (k : ℤ) :
    ∑ c, (((if c = c0 then k else 0 : ℤ)) : ℂ) • x c = (k : ℂ) • x c0 := by
  simp only [apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **The lattice-model bracket table.** -/
theorem bracket_model (a b : Fin 28) : ⁅xs a, xs b⁆ = ∑ c, (model a b c : ℂ) • xs c := by
  by_cases ha : a.val < 4
  · by_cases hb : b.val < 4
    · rw [xs_cartan a ha, xs_cartan b hb, hst_hst]
      symm
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [model, ha, hb]
    · have hb' : 4 ≤ b.val := by omega
      have hm : ∀ c, model a b c = if c = b then formZ (hvec a) (wt b) else 0 := fun c => by
        simp [model, ha, hb]
      simp only [hm, sum_single]
      rw [xs_cartan a ha, xs_root b hb', lie_smul, hst_ev, smul_comm]
  · have ha' : 4 ≤ a.val := by omega
    by_cases hb : b.val < 4
    · have hm : ∀ c, model a b c = if c = a then -formZ (hvec b) (wt a) else 0 := fun c => by
        simp [model, ha, hb]
      simp only [hm, sum_single]
      rw [xs_cartan b hb, xs_root a ha', smul_lie, ← lie_skew, hst_ev, smul_neg, smul_comm,
        Int.cast_neg, neg_smul]
    · have hb' : 4 ≤ b.val := by omega
      have hge := form_ge a b ha' hb'
      rw [xs_root a ha', xs_root b hb', smul_lie, lie_smul, smul_smul]
      by_cases h2 : formZ (wt a) (wt b) = -2
      · -- opposite roots
        have hopp := opp_of_form a b ha' hb' h2
        have hm : ∀ c, model a b c = if c.val < 4 then
            u a * u b * sgn (ep (wt a) (wt b)) * wt a ⟨c.val % 4, Nat.mod_lt _ (by norm_num)⟩
            else 0 := fun c => by simp [model, ha, hb, h2]
        rw [sum_cartan _ (fun c hc => by rw [hm c, if_neg (by omega), Int.cast_zero, zero_smul])]
        rw [hm 0, hm 1, hm 2, hm 3, if_pos (by decide), if_pos (by decide), if_pos (by decide),
          if_pos (by decide), xs_cartan 0 (by decide), xs_cartan 1 (by decide),
          xs_cartan 2 (by decide), xs_cartan 3 (by decide)]
        rw [ev_congr hopp (wt_norm b hb') (by rw [← hopp]; exact wt_norm b hb'), ev_ev_neg,
          smul_smul, hst_decomp]
        have hcob := cocycle_coboundary (wt a) (-wt a)
        rw [add_neg_cancel, f_zero, mul_one, ← hopp] at hcob
        have e0 : hvec 0 = Pi.single 0 1 := by ext j; fin_cases j <;> rfl
        have e1 : hvec 1 = Pi.single 1 1 := by ext j; fin_cases j <;> rfl
        have e2 : hvec 2 = Pi.single 2 1 := by ext j; fin_cases j <;> rfl
        have e3 : hvec 3 = Pi.single 3 1 := by ext j; fin_cases j <;> rfl
        rw [e0, e1, e2, e3, ← hopp]
        have hc : (u a : ℂ) * f (wt a) * ((u b : ℂ) * f (wt b)) * latticeCocycle d4 (wt a) (wt b)
            = (u a : ℂ) * u b * (-1 : ℂ) ^ ep (wt a) (wt b) := by
          rw [← hcob]; ring
        have k0 : (⟨(0 : Fin 28).val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = 0 := rfl
        have k1 : (⟨(1 : Fin 28).val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = 1 := rfl
        have k2 : (⟨(2 : Fin 28).val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = 2 := rfl
        have k3 : (⟨(3 : Fin 28).val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = 3 := rfl
        rw [hc, k0, k1, k2, k3]
        simp only [Int.cast_mul, sgn_eq]
        module
      · by_cases h1 : formZ (wt a) (wt b) = -1
        · obtain ⟨hc4, hcw⟩ := tgt_spec a b ha' hb' h1
          have hm : ∀ c, model a b c =
              if c = tgt a b then u a * u b * sgn (ep (wt a) (wt b)) * u (tgt a b) else 0 :=
            fun c => by
              simp only [model, ha, hb, h1, if_false, if_true]
              split_ifs with hct <;> simp_all
          simp only [hm, sum_single]
          have hn : formZ (wt a + wt b) (wt a + wt b) = 2 := by rw [← hcw]; exact wt_norm _ hc4
          rw [ev_ev_of_neg_one _ _ _ _ hn h1, smul_smul, xs_root _ hc4, smul_smul,
            ev_congr hcw (wt_norm _ hc4) hn]
          congr 1
          have hcob := cocycle_coboundary (wt a) (wt b)
          rw [hcw, Int.cast_mul, Int.cast_mul, Int.cast_mul, sgn_eq]
          have hu := u_sq (tgt a b)
          linear_combination (↑(u a) * ↑(u b)) * hcob + 0 * hu +
            ((u a : ℂ) * u b * (-1 : ℂ) ^ ep (wt a) (wt b) * f (wt a + wt b)) * (hu.symm ▸ rfl : (1 : ℂ) = 1) -
            ((u a : ℂ) * u b * (-1 : ℂ) ^ ep (wt a) (wt b) * f (wt a + wt b)) * hu
        · have h0 : 0 ≤ formZ (wt a) (wt b) := by omega
          rw [ev_ev_of_nonneg _ _ _ _ h0, smul_zero]
          symm
          refine Finset.sum_eq_zero fun c _ => ?_
          simp [model, ha, hb, h2, h1]

end

end VOA.DeligneAudit.D4Lie
