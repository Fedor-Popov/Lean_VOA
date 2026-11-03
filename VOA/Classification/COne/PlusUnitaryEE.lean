/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusUnitaryVac
import VOA.Classification.COne.LatticeModulesIrred
import VOA.Modules.ModuleRestrictOrd

/-!
# H3: the eigenvalue of `o(E ∗ E)` on the curve, by interpolation

Let `x` be a lowest-weight vector (weight `h`) of an ordinary `V⁺ = V_{2m}⁺`-module with
`o(W⁴)x = 2h·x` and `o(E)x = 0`.  We show `4mh = j²` for some `0 ≤ j < m`
(`plusEESquare_holds`).

## Proof
* `E ∗ E` has charge `0` (`e^{±α}₍ₙ₎e^{±α} = 0` for `n ≥ −1`), so it lies in `M(1)⁺`; by the strong
  generation of `M(1)⁺` by `ω, W⁴` (`strongGenM1_holds`) and Zhu's propagation
  (`good_of_iterProdSpan_eq_top`), there is a polynomial `Φ(h, w)` of degree `≤ m`, independent of
  the module, with `o(E ∗ E)x = Φ(h, w)x` on every top vector (`exists_Phi`).
* On the curve put `K(t) = Φ(t/4m, t/2m)`, a polynomial of degree `≤ m`.
* The `V_{2m}`-modules `V_{L+λ_j}` (`latticeModule`, restricted to `V⁺`) have top vectors `e^{λ_j}`
  of weight `j²/4m`.  There `o(W⁴) = 2h` because `W⁴ − 2ω ∈ O(V_{2m})` (`wRel_mem_O`, a
  three-term certificate: `A(M(1)) = ℂ[h̄]`).  `o(E)e^{λ_j} = 0` for `|j| < m`, so `K(j²) = 0`
  for `0 ≤ j < m`; and `o(E)²e^{λ_m} = κ·e^{λ_m}` with `κ ≠ 0`, so `K(m²) ≠ 0`.
* Hence `K ≠ 0` has the `m` roots `j²` and at most `m` roots: every root is a `j²`.  Finally on `x`,
  `o(E ∗ E)x = o(E)o(E)x = 0`, so `K(4mh) = Φ(h, 2h) = 0`.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne.PlusUnitary

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## §1  `W⁴ − 2ω ∈ O(V_{2m})` -/

/-- `P ⊗ e⁰` for a neutral raw polynomial. -/
noncomputable abbrev ls (P : RawPoly ℕ) : LatModuleGen (latP m) := latStateGen (latP m) (evR (a0 m) P) 0

theorem ls_append (P Q : RawPoly ℕ) : ls m (P ++ Q) = ls m P + ls m Q := by
  rw [ls, evR_append, latStateGen_add_boson]

theorem ls_scaleR (q : ℚ) (P : RawPoly ℕ) : ls m (scaleR q P) = ((q : ℚ) : ℂ) • ls m P := by
  rw [ls, evR_scaleR, latStateGen_csmul]

theorem ls_nil : ls m [] = 0 := by rw [ls, evR_nil]; simp [latStateGen]

theorem ls_normR (P : RawPoly ℕ) : ls m (normR P) = ls m P := by rw [ls, evR_normR]

theorem ls_flatMap_range (n : ℕ) (F : ℕ → RawPoly ℕ) :
    ls m ((List.range n).flatMap F) = ∑ i ∈ Finset.range n, ls m (F i) := by
  induction n with
  | zero => simp [ls_nil]
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      ls_append, ih]

theorem ls_lc : ∀ L : List (ℚ × RawPoly ℕ), ls m (lc L) = (L.map fun t => ((t.1 : ℚ) : ℂ) • ls m t.2).sum
  | [] => by simp [lc, ls_nil]
  | (c, B) :: rest => by
    rw [lc, ls_append, ls_scaleR, ls_lc rest, List.map_cons, List.sum_cons]

theorem ls_Pres (k : ℕ) (Q P : RawPoly ℕ) (n : ℕ) :
    Pres (V2m m hm) k (ls m Q) (ls m P) n = ls m (presR k Q P n) := by
  rw [Pres, presR, ls_flatMap_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ls_scaleR, ls, ls, V2m_smul_evR_W m hm Q, show -((i : ℤ) - 2 - n) - 1 = (n : ℤ) + 1 - i by ring]
  by_cases hi : i ≤ k + n
  · rw [show ((k : ℤ) + n) = (((k + n : ℕ)) : ℤ) by push_cast; ring, cbz_natCast_eq_choose hi]
    push_cast; rfl
  · rw [show ((k : ℤ) + n) = (((k + n : ℕ)) : ℤ) by push_cast; ring, cbz_nat_eq_zero (by omega),
      Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The certificate `W⁴ − 2ω = 4·Pres(h,h,1) − 5·Pres(h,h,0) − 3·Pres(h,x₁,0)`. -/
def wRelL : List (ℚ × RawPoly ℕ) :=
  [(4, presR 1 [(1, [0])] [(1, [0])] 1), (-5, presR 1 [(1, [0])] [(1, [0])] 0),
   (-3, presR 1 [(1, [0])] [(1, [1])] 0)]

theorem wRel_cert : normR (WR ++ scaleR (-2) omR) = normR (lc wRelL) := by decide +kernel

theorem h_mem_grading : ls m [(1, [0])] ∈ (V2m m hm).grading ((1 : ℕ) : ℤ) :=
  latStateGen_mem_grading m hm (evR_mem_grading (a0 m) [(1, [0])] (by simp [wWt]))

/-- **`W⁴ − 2ω ∈ O(V_{2m})`.** -/
theorem wRel_mem_O : ls m WR - (2 : ℂ) • ls m omR ∈ O (V2m m hm) := by
  have h1 : ls m WR - (2 : ℂ) • ls m omR = ls m (lc wRelL) := by
    have h := congrArg (ls m) wRel_cert
    rw [ls_normR, ls_normR, ls_append, ls_scaleR] at h
    rw [← h]
    push_cast; rw [neg_smul, sub_eq_add_neg]
  rw [h1, ls_lc]
  simp only [wRelL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.add_mem _
    (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)) <;>
  · rw [← ls_Pres m hm]; exact Pres_mem_O _ (h_mem_grading m hm) _ _

theorem omega_V2m : (V2m m hm).conformalVector = ls m omR := hasPoly_omega m hm

/-- On a lowest-weight vector of a `V_{2m}`-module, `o(W⁴)` acts by `2h`. -/
theorem oMod_W_V2m {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2m m hm) M) {h : ℂ}
    (hcw : IsLowestWeight N h) {x : M} (hx : x ∈ N.weight h) :
    oMod N (ls m WR) x = (2 * h) • x := by
  have h0 := oMod_eq_zero_of_mem_O N hcw (wRel_mem_O m hm) hx
  rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, ← omega_V2m m hm,
    oMod_homogeneous N (V2m m hm).conformal_mem, show (2 : ℤ) - 1 = 1 by norm_num,
    N.L0_weight h x hx, smul_smul, sub_eq_zero] at h0
  exact h0

/-! ## §2  Restriction to `V⁺` -/

/-- An ordinary `V_{2m}`-module as a `V_{2m}⁺`-module. -/
noncomputable def resN {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2m m hm) M) :
    OrdVModule (V2mPlus m hm) M :=
  (orbifold (Subgroup.zpowers (thetaV2m m hm))).restrictOrdVModule N

theorem oMod_resN {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2m m hm) M)
    {u : VP m hm} {k : ℤ} (hu : u ∈ (V2mPlus m hm).grading k) (x : M) :
    oMod (resN m hm N) u x = oMod N (u : LatModuleGen (latP m)) x := by
  rw [oMod_homogeneous _ hu, oMod_homogeneous N (show (u : LatModuleGen (latP m)) ∈ (V2m m hm).grading k from hu)]
  rfl

theorem isLowestWeight_resN {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2m m hm) M)
    {h : ℂ} (hcw : IsLowestWeight N h) : IsLowestWeight (resN m hm N) h := hcw

theorem WP_coe : ((WP m hm : VP m hm) : LatModuleGen (latP m)) = ls m WR := hasPoly_W m hm

theorem EP_coe : ((EP m hm : VP m hm) : LatModuleGen (latP m)) =
    latChargeGen (latP m) ((1 : ℤ) : (latP m).carrier) + latChargeGen (latP m) ((-1 : ℤ) : (latP m).carrier) := rfl

/-! ## §3  The lattice modules `V_{L+λ_j}` -/

section LatticeTops

variable (j : ℤ)

theorem latticeModule_isLowestWeight (hj : |j| ≤ m) :
    IsLowestWeight (latticeModule m hm j) ((((j : ℝ) ^ 2 / (4 * m) : ℝ) : ℂ)) := by
  intro α hα
  obtain ⟨r, hr, hle⟩ := latticeModule_lowestWeight m hm j hj hα
  obtain ⟨w, n, hwn⟩ := latticeModule_weight_ne_bot m hm j hα
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- `α − h = w + mn² + nj`
  have hdiff : ((((w : ℝ) + ((2 * m * n + j : ℤ) : ℝ) ^ 2 / (4 * m) : ℝ)) : ℝ) - (j : ℝ) ^ 2 / (4 * m)
      = ((w + m * n ^ 2 + n * j : ℤ) : ℝ) := by
    push_cast; field_simp; ring
  have hk0 : 0 ≤ (w + m * n ^ 2 + n * j : ℤ) := by
    have hreal : r = ((w : ℝ) + ((2 * m * n + j : ℤ) : ℝ) ^ 2 / (4 * m)) := by
      have := hr.symm.trans hwn
      exact_mod_cast this
    have : (0 : ℝ) ≤ ((w + m * n ^ 2 + n * j : ℤ) : ℝ) := by rw [← hdiff, ← hreal]; linarith
    exact_mod_cast this
  refine ⟨(w + m * n ^ 2 + n * j : ℤ).toNat, ?_⟩
  rw [hwn]
  have : ((((w + m * n ^ 2 + n * j : ℤ).toNat : ℕ) : ℝ)) = ((w + m * n ^ 2 + n * j : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk0
  rw [show (((w + m * n ^ 2 + n * j : ℤ).toNat : ℕ) : ℂ) =
      ((((w + m * n ^ 2 + n * j : ℤ).toNat : ℕ) : ℝ) : ℂ) by norm_cast, this, ← Complex.ofReal_add]
  congr 1
  linarith [hdiff]

/-- The cocycle factor of `Y(e^{kα}, z)` on `p ⊗ e^{nα}` in `V_{L+λ_j}`. -/
noncomputable abbrev kap (k n : ℤ) : ℂ :=
  latCob (latP m) (glueLat m j) (glueIota m j) k
    * latticeCocycle (glueLat m j) (glueIota m j k) (glueIota m j n + glueDelta m j)

theorem kap_ne_zero (k n : ℤ) : kap m j k n ≠ 0 :=
  mul_ne_zero (latCob_ne_zero _ _ _ _) (LatGen.latticeCocycle_ne_zero _ _ _)

/-- `Y(e^{kα}, z)_t` on the pure exponential `e^{nα}` of `V_{L+λ_j}`. -/
theorem latE_vac (k n t : ℤ) :
    (latticeModule m hm j).YM (latChargeGen (latP m) k) t (latStateGen (latP m) (vacuumN _) n) =
      if 0 ≤ t - 2 * m * k * n - j * k then
        kap m j k n • latStateGen (latP m) (vSchur (latP m) k (t - 2 * m * k * n - j * k).toNat) (k + n)
      else 0 := by
  rw [latticeModule_latChargeGen, EEVec_vacuum]
  split_ifs
  · rfl
  · simp [latStateGen]

/-- `o(E)` on `V_{L+λ_j}`. -/
theorem oMod_E_lat (y : LatModuleGen (latP m)) :
    oMod (latticeModule m hm j) ((EP m hm : VP m hm) : LatModuleGen (latP m)) y =
      (latticeModule m hm j).YM (latChargeGen (latP m) (1 : ℤ)) (-(m : ℤ)) y +
        (latticeModule m hm j).YM (latChargeGen (latP m) (-1 : ℤ)) (-(m : ℤ)) y := by
  rw [oMod_homogeneous _ (show ((EP m hm : VP m hm) : LatModuleGen (latP m)) ∈ (V2m m hm).grading (m : ℤ)
    from EP_mem_grading m hm), mode_apply, EP_coe, map_add, show -((m : ℤ) - 1) - 1 = -(m : ℤ) by ring]
  rfl

/-- For `|j| < m`, `o(E)` kills the top vector `e^{λ_j}`. -/
theorem oMod_E_lat_vac (hj : |j| < m) :
    oMod (latticeModule m hm j) ((EP m hm : VP m hm) : LatModuleGen (latP m)) (latVacuumGen (latP m)) = 0 := by
  rw [oMod_E_lat, latVacuumGen, show (0 : (latP m).carrier) = ((0 : ℤ) : (latP m).carrier) from rfl,
    latE_vac, latE_vac, if_neg, if_neg, add_zero]
  all_goals (obtain ⟨h1, h2⟩ := abs_lt.mp hj; omega)

/-- At `j = m`: `o(E)e^{λ_m} = κ₁ e^{λ_m − α}`. -/
theorem oMod_E_lat_m_vac :
    oMod (latticeModule m hm m) ((EP m hm : VP m hm) : LatModuleGen (latP m)) (latVacuumGen (latP m)) =
      kap m m (-1) 0 • latStateGen (latP m) (vacuumN _) ((-1 : ℤ) : (latP m).carrier) := by
  rw [oMod_E_lat, latVacuumGen, show (0 : (latP m).carrier) = ((0 : ℤ) : (latP m).carrier) from rfl,
    latE_vac, latE_vac, if_neg, if_pos, zero_add]
  · congr 2
    · rw [show (-(m : ℤ) - 2 * (m : ℤ) * (-1) * 0 - (m : ℤ) * (-1)) = 0 by ring]
      simp [vSchur_zero, vacuumN]
  · ring_nf; rfl
  · have : (1 : ℤ) ≤ m := by exact_mod_cast hm
    nlinarith

/-- At `j = m`: `o(E)e^{λ_m − α} = κ₂ e^{λ_m}`. -/
theorem oMod_E_lat_m_neg :
    oMod (latticeModule m hm m) ((EP m hm : VP m hm) : LatModuleGen (latP m))
        (latStateGen (latP m) (vacuumN _) ((-1 : ℤ) : (latP m).carrier)) =
      kap m m 1 (-1) • latVacuumGen (latP m) := by
  rw [oMod_E_lat, latE_vac, latE_vac, if_pos, if_neg, add_zero]
  · rw [latVacuumGen]
    congr 1
    rw [show (-(m : ℤ) - 2 * (m : ℤ) * 1 * (-1) - (m : ℤ) * 1) = 0 by ring]
    simp [vSchur_zero, vacuumN]
    rfl
  · have : (1 : ℤ) ≤ m := by exact_mod_cast hm
    nlinarith
  · ring_nf; rfl

end LatticeTops

/-! ## §4  `E ∗ E` lies in `M(1)⁺` -/

theorem chargeProd_mem_sec0 (n : ℤ) (hn : -1 ≤ n) (a b : ℤ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    (V2m m hm).smul (latChargeGen (latP m) a) n (latChargeGen (latP m) b) ∈ sec0Sub m := by
  unfold V2m
  rw [show latChargeGen (latP m) b = latStateGen (latP m) (vacuumN _) b from rfl,
    latVOA_smul_latChargeGen_state, latP_form, EEVec_vacuum]
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  by_cases hab : a + b = 0
  · split_ifs
    · refine Submodule.smul_mem _ _ ?_
      refine (show ∀ γ : (latP m).carrier, γ = 0 → ∀ q, latStateGen (latP m) q γ ∈ sec0Sub m from ?_) _ hab _
      rintro γ rfl q
      exact ⟨q, rfl⟩
    · simp [latStateGen]
  · have : a = b := by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
    subst this
    rw [if_neg (by rcases ha with rfl | rfl <;> nlinarith)]
    simp [latStateGen]

theorem EE_smul_mem_sec0 (n : ℤ) (hn : -1 ≤ n) :
    (V2m m hm).smul ((EP m hm : VP m hm) : LatModuleGen (latP m)) n ((EP m hm : VP m hm) : LatModuleGen (latP m))
      ∈ sec0Sub m := by
  rw [EP_coe, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_add_right]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_) <;>
    exact chargeProd_mem_sec0 m hm n hn _ _ (by simp) (by simp)

/-- `E₍ₙ₎E ∈ M(1)⁺` (`n ≥ −1`), with its weight. -/
theorem exists_EE_m1 (i : ℕ) : ∃ u : (m1Sub m hm).carrier,
    incl m hm u = (V2mPlus m hm).smul (EP m hm) ((i : ℤ) - 1) (EP m hm) ∧
      u ∈ (M1P m hm).grading ((m : ℤ) + m - ((i : ℤ) - 1) - 1) := by
  set y := (V2mPlus m hm).smul (EP m hm) ((i : ℤ) - 1) (EP m hm)
  have hsec : (y : LatModuleGen (latP m)) ∈ sec0Sub m := by
    rw [V2mPlus_smul_coe]; exact EE_smul_mem_sec0 m hm _ (by omega)
  refine ⟨⟨(y : LatModuleGen (latP m)), Submodule.mem_inf.mpr ⟨hsec, y.2⟩⟩, rfl, ?_⟩
  rw [M1P_mem_grading_iff]
  exact (V2mPlus m hm).smul_mem_grading (EP_mem_grading m hm) (EP_mem_grading m hm) _

/-- The generators `(ω, W⁴)` of `M(1)⁺`. -/
noncomputable def gM2 : Fin 2 → (m1Sub m hm).carrier := ![ωM m hm, WM m hm]

theorem range_gM2 : Set.range (gM2 m hm) = gensM m hm := by
  ext v
  simp only [Set.mem_range, gensM, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp [gM2]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem good_M1 : ∀ w : ℤ, ∀ a ∈ (M1P m hm).grading w, Good (V := V2mPlus m hm) (incl m hm) (gM2 m hm) w a :=
  good_of_iterProdSpan_eq_top (incl_gradedHom m hm) ![2, 4]
    (fun i => by fin_cases i
                 · exact ωM_mem_grading m hm
                 · exact WM_mem_grading m hm)
    (fun i => by fin_cases i <;> simp)
    (by rw [range_gM2]; exact strongGenM1_holds m hm)

/-- **`o(E ∗ E)` is a fixed polynomial of degree `≤ m` in the eigenvalues of `o(ω), o(W⁴)`.** -/
theorem exists_Phi : ∃ Φ : MvPolynomial (Fin 2) ℂ, Φ.totalDegree ≤ m ∧
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M) (h : ℂ),
      IsLowestWeight N h → ∀ x ∈ N.weight h, ∀ val : Fin 2 → ℂ,
        oMod N (V2mPlus m hm).conformalVector x = val 0 • x → oMod N (WP m hm) x = val 1 • x →
          oMod N (zhuMul (V2mPlus m hm) (EP m hm) (EP m hm)) x = MvPolynomial.eval val Φ • x := by
  choose u hu using exists_EE_m1 m hm
  set U : (m1Sub m hm).carrier := ∑ i ∈ Finset.range (m + 1), cbz (m : ℤ) (i : ℤ) • u i
  have hU : incl m hm U = zhuMul (V2mPlus m hm) (EP m hm) (EP m hm) := by
    rw [zhuMul_homogeneous _ (EP_mem_grading m hm), show ((m : ℤ)).toNat = m by simp, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, (hu i).1]
  have hG : Good (V := V2mPlus m hm) (incl m hm) (gM2 m hm) ((m : ℤ) + m) U := by
    refine (goodSub (V := V2mPlus m hm) (incl m hm) (gM2 m hm) _).sum_mem fun i hi => ?_
    refine Submodule.smul_mem _ _ ?_
    exact (good_M1 m hm _ _ (hu i).2).mono _ _ (by omega)
  obtain ⟨Φ, hdeg, hΦ⟩ := hG
  refine ⟨Φ, by rw [show ((m : ℤ) + m).toNat = m + m by omega] at hdeg; omega, ?_⟩
  intro M _ _ N h hcw x hx val h0 h1
  rw [← hU]
  refine hΦ M N h hcw x hx val fun i => ?_
  fin_cases i
  · exact h0
  · exact h1

/-! ## §5  Interpolation -/

/-- `K(t) = Φ(t/4m, t/2m)`. -/
noncomputable def Kp (Φ : MvPolynomial (Fin 2) ℂ) : Polynomial ℂ :=
  MvPolynomial.aeval ![Polynomial.C (1 / (4 * (m : ℂ))) * Polynomial.X,
    Polynomial.C (1 / (2 * (m : ℂ))) * Polynomial.X] Φ

theorem Kp_eval (Φ : MvPolynomial (Fin 2) ℂ) (t : ℂ) :
    (Kp m Φ).eval t = MvPolynomial.eval ![t / (4 * m), t / (2 * m)] Φ := by
  have hae : ∀ g : Fin 2 → ℂ, MvPolynomial.aeval g Φ = MvPolynomial.eval g Φ := fun g => rfl
  rw [Kp, ← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply, hae]
  congr 2
  funext i
  fin_cases i <;> simp [div_eq_mul_inv, mul_comm]

theorem natDegree_aeval_le (Φ : MvPolynomial (Fin 2) ℂ) (f : Fin 2 → Polynomial ℂ)
    (hf : ∀ i, (f i).natDegree ≤ 1) : (MvPolynomial.aeval f Φ).natDegree ≤ Φ.totalDegree := by
  conv_lhs => rw [MvPolynomial.as_sum Φ]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => ?_
  refine Polynomial.natDegree_pow_le.trans ?_
  calc d i * (f i).natDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = d i := mul_one _

theorem Kp_natDegree (Φ : MvPolynomial (Fin 2) ℂ) : (Kp m Φ).natDegree ≤ Φ.totalDegree := by
  refine natDegree_aeval_le Φ _ fun i => ?_
  fin_cases i
  · change (Polynomial.C _ * Polynomial.X).natDegree ≤ 1
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  · change (Polynomial.C _ * Polynomial.X).natDegree ≤ 1
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

/-- A polynomial of degree `≤ m` vanishing at `j²` (`j < m`) and not at `m²` vanishes only there. -/
theorem roots_of_interp (p : Polynomial ℂ) (hdeg : p.natDegree ≤ m)
    (hz : ∀ j : ℕ, j < m → p.eval ((j : ℂ) ^ 2) = 0) (hnz : p.eval ((m : ℂ) ^ 2) ≠ 0) :
    ∀ t : ℂ, p.eval t = 0 → ∃ j : ℕ, j < m ∧ t = (j : ℂ) ^ 2 := by
  intro t ht
  by_contra hcon
  push Not at hcon
  have hp0 : p ≠ 0 := by rintro rfl; exact hnz (by simp)
  set S : Finset ℂ := insert t ((Finset.range m).image fun j : ℕ => (j : ℂ) ^ 2)
  have hinj : Function.Injective fun j : ℕ => (j : ℂ) ^ 2 := by
    intro a b hab
    have : ((a ^ 2 : ℕ) : ℂ) = ((b ^ 2 : ℕ) : ℂ) := by push_cast; exact hab
    exact Nat.pow_left_injective (n := 2) (by norm_num) (by exact_mod_cast this)
  have hnot : t ∉ (Finset.range m).image fun j : ℕ => (j : ℂ) ^ 2 := by
    intro hmem
    obtain ⟨j, hj, hjt⟩ := Finset.mem_image.mp hmem
    exact hcon j (Finset.mem_range.mp hj) hjt.symm
  have hcard : S.card = m + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hsub : S ⊆ p.roots.toFinset := by
    intro z hz'
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    rcases Finset.mem_insert.mp hz' with rfl | hz'
    · exact ht
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz'
      exact hz j (Finset.mem_range.mp hj)
  have h1 := Finset.card_le_card hsub
  have h2 := Multiset.toFinset_card_le p.roots
  have h3 := Polynomial.card_roots' p
  omega

/-! ## §6  H3 -/

include hm in
theorem latVacuumGen_ne_zero' : latVacuumGen (latP m) ≠ 0 := by
  intro h
  apply (V2mPlus_isSimple m hm).vacuum_ne_zero
  exact Subtype.ext h

theorem oMod_omega_resN {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2m m hm) M)
    {h : ℂ} {x : M} (hx : x ∈ N.weight h) : oMod (resN m hm N) (V2mPlus m hm).conformalVector x = h • x := by
  rw [oMod_resN m hm N (V2mPlus m hm).conformal_mem]
  change oMod N (V2m m hm).conformalVector x = h • x
  rw [oMod_homogeneous N (V2m m hm).conformal_mem, show (2 : ℤ) - 1 = 1 by norm_num]
  exact N.L0_weight h x hx

/-- On the top `e^{λ_j}` (`|j| ≤ m`), `o(E ∗ E)` acts by `K(j²)`. -/
theorem lat_EE (Φ : MvPolynomial (Fin 2) ℂ)
    (hΦ : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M) (h : ℂ),
      IsLowestWeight N h → ∀ x ∈ N.weight h, ∀ val : Fin 2 → ℂ,
        oMod N (V2mPlus m hm).conformalVector x = val 0 • x → oMod N (WP m hm) x = val 1 • x →
          oMod N (zhuMul (V2mPlus m hm) (EP m hm) (EP m hm)) x = MvPolynomial.eval val Φ • x)
    (j : ℤ) (hj : |j| ≤ m) :
    oMod (resN m hm (latticeModule m hm j)) (zhuMul (V2mPlus m hm) (EP m hm) (EP m hm)) (latVacuumGen (latP m)) =
      (Kp m Φ).eval ((j : ℂ) ^ 2) • latVacuumGen (latP m) := by
  set hj' : ℂ := ((((j : ℝ) ^ 2 / (4 * m) : ℝ)) : ℂ)
  have hcw := latticeModule_isLowestWeight m hm j hj
  have hx := latticeModule_vacuum_mem m hm j
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hval : ![hj', 2 * hj'] = ![(j : ℂ) ^ 2 / (4 * m), (j : ℂ) ^ 2 / (2 * m)] := by
    simp only [hj']
    push_cast
    congr 1
    · congr 1; field_simp; ring
  rw [hΦ (LatModuleGen (latP m)) _ hj' (isLowestWeight_resN m hm _ hcw) _ hx ![hj', 2 * hj'] (oMod_omega_resN m hm _ hx) ?_,
    Kp_eval, hval]
  rw [oMod_resN m hm _ (WP_mem_grading m hm), WP_coe]
  exact oMod_W_V2m m hm _ hcw hx

/-- **H3 is a theorem** (every `m ≥ 1`). -/
theorem plusEESquare_holds : PlusEESquare m hm := by
  intro M _ _ N h x hcw hx hx0 hW hE
  obtain ⟨Φ, hdeg, hΦ⟩ := exists_Phi m hm
  have hv0 := latVacuumGen_ne_zero' m hm
  have hz : ∀ k : ℕ, k < m → (Kp m Φ).eval (((k : ℤ) : ℂ) ^ 2) = 0 := by
    intro k hk
    have hk' : |(k : ℤ)| < m := by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hk
    have h1 := lat_EE m hm Φ hΦ k hk'.le
    have hcw := isLowestWeight_resN m hm _ (latticeModule_isLowestWeight m hm k hk'.le)
    rw [oMod_zhuMul_lowest_all _ hcw _ _ (latticeModule_vacuum_mem m hm k),
      oMod_resN m hm _ (EP_mem_grading m hm) (latVacuumGen _), oMod_E_lat_vac m hm k hk', map_zero] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hv0
  have hz' : ∀ k : ℕ, k < m → (Kp m Φ).eval ((k : ℂ) ^ 2) = 0 := fun k hk => by
    simpa using hz k hk
  have hnz : (Kp m Φ).eval ((m : ℂ) ^ 2) ≠ 0 := by
    have hmm : |(m : ℤ)| ≤ m := by rw [abs_of_nonneg (by positivity)]
    have h1 := lat_EE m hm Φ hΦ m hmm
    have hcw := isLowestWeight_resN m hm _ (latticeModule_isLowestWeight m hm m hmm)
    rw [oMod_zhuMul_lowest_all _ hcw _ _ (latticeModule_vacuum_mem m hm m),
      oMod_resN m hm _ (EP_mem_grading m hm) (latVacuumGen _), oMod_E_lat_m_vac, map_smul,
      oMod_resN m hm _ (EP_mem_grading m hm), oMod_E_lat_m_neg, smul_smul] at h1
    have h2 : (kap m m (-1) 0 * kap m m 1 (-1) - (Kp m Φ).eval (((m : ℤ) : ℂ) ^ 2)) • latVacuumGen (latP m) = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right hv0
    have h4 : (Kp m Φ).eval (((m : ℤ) : ℂ) ^ 2) ≠ 0 := by
      rw [← sub_eq_zero.mp h3]
      exact mul_ne_zero (kap_ne_zero m m _ _) (kap_ne_zero m m _ _)
    simpa using h4
  have hroot : (Kp m Φ).eval (4 * m * h) = 0 := by
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 := hΦ M N h hcw x hx ![h, 2 * h] (by
      rw [oMod_homogeneous N (V2mPlus m hm).conformal_mem, show (2 : ℤ) - 1 = 1 by norm_num]
      exact N.L0_weight h x hx) hW
    rw [oMod_zhuMul_lowest_all N hcw _ _ hx, hE, map_zero] at h1
    have h2 := (smul_eq_zero.mp h1.symm).resolve_right hx0
    have hv : (![4 * (m : ℂ) * h / (4 * m), 4 * m * h / (2 * m)] : Fin 2 → ℂ) = ![h, 2 * h] := by
      ext i; fin_cases i <;> simp <;> field_simp; ring
    rw [Kp_eval, hv]; exact h2
  obtain ⟨j, hj, hjt⟩ := roots_of_interp m (Kp m Φ) ((Kp_natDegree m Φ).trans hdeg) hz' hnz _ hroot
  exact ⟨j, hj, hjt⟩

end VOA.Classification.COne.PlusUnitary
