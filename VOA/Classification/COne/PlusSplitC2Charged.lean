import VOA.Classification.COne.PlusSplitZhuMixedCertificate

/-! Direct C₂ certificates on the charged sector. These use negative modes
and translation only, not Zhu residues or conclusions about simple tops. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusC2Charged
open PlusUnitary PlusC2 PlusC2Eval VOA.SparseRational PlusZhuMixed

def gen (t : CEntry) : RawPoly ℕ :=
  normR (if t.2.1 = [] then polyActWC omR (-1) [(1, t.2.2.1)]
    else polyActWC [(1, t.2.1)] ((t.2.2.2 : ℤ) + 1) [(1, t.2.2.1)])

def cert (L : List CEntry) : RawPoly ℕ := L.flatMap fun t => cmulR t.1 (gen t)

theorem gen_mem (m : ℕ) (hm : 1 ≤ m) (t : CEntry) (ht : Even t.2.1.length) :
    ∃ y ∈ O₂ (V2mPlus m hm), HasC m hm y (gen t) := by
  unfold gen
  split_ifs
  · exact ⟨_, L_neg_one_mem_O₂ _ _, hasC_normR m hm
      (hasC_smul_left m hm (omega_coe m hm) (hasC_stP m hm _) 0)⟩
  · refine ⟨(V2mPlus m hm).smul (incl m hm (mkW m hm t.2.1 ht))
      (-((t.2.2.2 : ℤ) + 2)) (stP m hm [(1, t.2.2.1)]),
      smul_le_neg_two_mem_O₂ _ _ _ (show -((t.2.2.2 : ℤ) + 2) ≤ -2 by omega),
      hasC_normR m hm ?_⟩
    have h := hasC_smul_left m hm (incl_mkW_coe m hm _ ht)
      (hasC_stP m hm [(1, t.2.2.1)]) (-((t.2.2.2 : ℤ) + 2))
    rwa [show -(-((t.2.2.2 : ℤ) + 2)) - 1 = (t.2.2.2 : ℤ) + 1 by ring] at h

theorem cert_mem (m : ℕ) (hm : 1 ≤ m) (L : List CEntry)
    (hL : ∀ t ∈ L, Even t.2.1.length) :
    ∃ y ∈ O₂ (V2mPlus m hm), HasC m hm y (cert L) := by
  induction L with
  | nil => exact ⟨0, Submodule.zero_mem _, hasC_zero m hm⟩
  | cons t L ih =>
    obtain ⟨y, hy, hyC⟩ := ih fun t ht => hL t (List.mem_cons_of_mem _ ht)
    obtain ⟨g, hg, hgC⟩ := gen_mem m hm t (hL t List.mem_cons_self)
    obtain ⟨z, hz, hzC⟩ := hasC_cmulR m hm hgC t.1
    exact ⟨z + y, Submodule.add_mem _
      ((Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hg)) hz) hy,
      hasC_add m hm hzC hyC⟩

def omIterC : ℕ → RawPoly ℕ
  | 0 => Y0
  | k + 1 => normR (polyActWC omR 0 (omIterC k))

def mixedCert : List CEntry :=
  [([(-120, 5), (30, 1)], [], [3], 0),
   ([(80, 4), (-120, 2), (45, 0)], [], [2, 1], 0),
   ([(20, 3), (-15, 1)], [], [1, 1, 1], 0),
   ([(68, 6), (-80, 4), (93, 2), (-45, 0)], [0, 0], [], 1)]

def cubicCert : List CEntry :=
  [([(160, 9), (-1136, 7), (-648, 5), (780, 3)], [], [5], 0),
   ([(384, 6), (-768, 4), (-480, 2), (960, 0)], [], [4, 1], 0),
   ([(-400, 8), (1432, 6), (-1644, 4), (-350, 2), (960, 0)], [], [3, 2], 0),
   ([(160, 3), (-320, 1)], [], [3, 1, 1], 0),
   ([(192, 7), (-672, 5), (816, 3), (-480, 1)], [], [2, 2, 1], 0),
   ([(96, 6), (-272, 4), (160, 2)], [], [2, 1, 1, 1], 0),
   ([(16, 5), (-32, 3)], [], [1, 1, 1, 1, 1], 0),
   ([(-176, 10), (2296, 8), (-7308, 6), (6570, 4), (-390, 2), (-1920, 0)],
     [0, 0], [], 3),
   ([(128, 9), (-448, 7), (672, 5), (-816, 3), (480, 1)], [0, 0], [2], 1),
   ([(72, 9), (-460, 7), (1110, 5), (-801, 3), (320, 1)], [0, 0], [3], 0),
   ([(32, 10), (-576, 8), (2352, 6), (-1936, 4), (450, 2)], [2, 0], [], 1)]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- Kernel normalization of the finite rational certificate.
theorem mixedCert_check : normR (cert mixedCert) =
    normR (cpow 2 (cmulR dC (polyActWC WR 0 Y0) ++ cmulR aC (omIterC 2))) := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- Kernel normalization of the finite rational certificate.
theorem cubicCert_check : normR (cert cubicCert) =
    normR (cmulR [(128, 6), (-256, 4)] (omIterC 3)) := by
  decide +kernel

variable (m : ℕ) (hm : 1 ≤ m)

def omegaIter (k : ℕ) : VP m hm :=
  (fun x => (V2mPlus m hm).smul (V2mPlus m hm).conformalVector (-1) x)^[k] (y0 m hm)

theorem hasC_omegaIter (k : ℕ) : HasC m hm (omegaIter m hm k) (omIterC k) := by
  induction k with
  | zero => exact hasC_stP m hm Y0
  | succ k ih =>
    rw [omegaIter, Function.iterate_succ_apply']
    exact hasC_normR m hm (hasC_smul_left m hm (omega_coe m hm) ih (-1))

theorem mk₂_omegaIter (k : ℕ) :
    mk₂ (V2mPlus m hm) (omegaIter m hm k) =
      mk₂ (V2mPlus m hm) (V2mPlus m hm).conformalVector ^ k *
        mk₂ (V2mPlus m hm) (y0 m hm) := by
  induction k with
  | zero => simp [omegaIter]
  | succ k ih =>
    rw [omegaIter, Function.iterate_succ_apply']
    dsimp only [omegaIter] at ih
    rw [VOA.TripletNilp.mk₂_smul_neg_one, ih, pow_succ']; ring

theorem omega_cubed_E (hm2 : 2 ≤ m) :
    mk₂ (V2mPlus m hm) (V2mPlus m hm).conformalVector ^ 3 *
      mk₂ (V2mPlus m hm) (y0 m hm) = 0 := by
  obtain ⟨z, hz, hzC⟩ := cert_mem m hm cubicCert (by decide)
  have ht := hasC_cmulR_exact m hm (hasC_omegaIter m hm 3) [(128, 6), (-256, 4)]
  have he := hasC_of_normR_eq m hm hzC cubicCert_check
  have hy : scalarC (cα m) [(128, 6), (-256, 4)] • omegaIter m hm 3 ∈ O₂ (V2mPlus m hm) :=
    (show z = _ from he.trans ht.symm) ▸ hz
  have hn : scalarC (cα m) [(128, 6), (-256, 4)] ≠ 0 := by
    have hc := cα_poly_ne_zero m hm hm2
    have h0 : cα m ≠ 0 := by intro h; simp [h] at hc
    have heq : scalarC (cα m) [(128, 6), (-256, 4)] =
        (128 : ℂ) * cα m ^ 3 * (cα m ^ 3 - 2 * cα m) := by
      norm_num [scalarC]; ring
    rw [heq]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ h0)) hc
  have hy' := (O₂ (V2mPlus m hm)).smul_mem
    (scalarC (cα m) [(128, 6), (-256, 4)])⁻¹ hy
  rw [smul_smul, inv_mul_cancel₀ hn, one_smul] at hy'
  rw [← mk₂_omegaIter, mk₂_eq_zero_iff]
  exact hy'

theorem W_E_relation :
    scalarC (cα m) dC • (mk₂ (V2mPlus m hm) (WP m hm) *
      mk₂ (V2mPlus m hm) (y0 m hm)) +
    scalarC (cα m) aC • (mk₂ (V2mPlus m hm) (V2mPlus m hm).conformalVector ^ 2 *
      mk₂ (V2mPlus m hm) (y0 m hm)) = 0 := by
  obtain ⟨z, hz, hzC⟩ := cert_mem m hm mixedCert (by decide)
  have ht := hasC_cpow m hm (hasC_add m hm
    (hasC_cmulR_exact m hm
      (hasC_smul_left m hm (w := WP m hm) (hasPoly_W m hm)
        (hasC_stP m hm Y0) (-1)) dC)
    (hasC_cmulR_exact m hm (hasC_omegaIter m hm 2) aC)) 2
  have he := hasC_of_normR_eq m hm hzC mixedCert_check
  have hy := (show z = _ from he.trans ht.symm) ▸ hz
  have hn : cα m ^ 2 ≠ 0 := by
    rw [pow_two, cα_sq m hm]
    exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
  have hy' := (O₂ (V2mPlus m hm)).smul_mem (cα m ^ 2)⁻¹ hy
  rw [smul_smul, inv_mul_cancel₀ hn, one_smul] at hy'
  have hq := (mk₂_eq_zero_iff _).mpr hy'
  simpa only [map_add, map_smul, VOA.TripletNilp.mk₂_smul_neg_one, mk₂_omegaIter] using hq

end VOA.Classification.COne.PlusC2Charged
