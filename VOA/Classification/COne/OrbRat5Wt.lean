import VOA.Classification.COne.OrbRat5Low

/-! # Weight spaces of `V₈⁺` in weights `≤ 4`

* `plus_low_mem_span`: a vector of `V₈⁺` of weight `k ≤ 3` lies in `span {𝟙, ω, ω₍₀₎ω}`.
* `plus_four_decomp`: a weight-four vector of `V₈⁺` is `α ω₍₋₁₎ω + β ω₍₀₎ω₍₀₎ω + γ J + δ E`.

Certificates (`decide +kernel`, cheap): the even Fock monomials of weight `≤ 4` in terms of the
Virasoro descendants `ω, ω₍₀₎ω, ω₍₋₁₎ω, ω₍₀₎ω₍₀₎ω` and `J`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat5

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f LatMod
  OrbRat3

/-! ## §1 The charge analysis of `V₈` in weights `≤ 4` -/

theorem halfNorm_four (α : ℤ) : LatGen.halfNorm (latP 4) α = 4 * (α * α) := by
  simp only [LatGen.halfNorm]
  rw [latP_form]
  have h : (2 : ℤ) * ((4 : ℕ) : ℤ) * α * α = 2 * (4 * (α * α)) := by push_cast; ring
  rw [h]
  omega

theorem V8_grading_low {k : ℕ} (hk : k ≤ 3) {v : LatModuleGen (latP 4)}
    (hv : v ∈ (V2m 4 four_ge_one).grading (k : ℤ)) :
    ∃ q ∈ gradingWN (rank (latP 4)) k, v = latStateGen (latP 4) q 0 := by
  rw [V2m_grading_eq] at hv
  have hle : gradingLatGen (latP 4) (k : ℤ) ≤ bigradα (latP 4) ((k : ℤ), 0) := by
    apply iSup_le
    intro α
    change ℤ at α
    by_cases hα : α = 0
    · subst hα
      rw [halfNorm_four, mul_zero, mul_zero, sub_zero]
      exact le_rfl
    · rw [bigradα_eq_bot_of_neg (latP 4) α]
      · exact bot_le
      · rw [halfNorm_four]
        have hsq : 1 ≤ α * α := by
          rcases lt_or_gt_of_ne hα with h | h <;> nlinarith
        have : (k : ℤ) ≤ 3 := by exact_mod_cast hk
        nlinarith
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp (hle hv)
  refine ⟨q, ?_, by rw [mkEα_apply]; rfl⟩
  rw [gradingZN_of_nonneg (by positivity)] at hq
  simpa using hq

theorem fock_zero_eq {q : FockN (rank (latP 4))} (hq : q ∈ gradingWN (rank (latP 4)) 0) :
    ∃ c : ℂ, q = c • (1 : FockN (rank (latP 4))) := by
  have h : q ∈ Submodule.span ℂ {(1 : FockN (rank (latP 4)))} := by
    apply mem_of_monomials _ hq
    intro d hd
    rw [weight_eq_zero_iff _ d hd, monomial_zero', C_1]
    exact Submodule.subset_span rfl
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  exact ⟨c, hc.symm⟩

theorem V8_grading_four {v : LatModuleGen (latP 4)}
    (hv : v ∈ (V2m 4 four_ge_one).grading 4) :
    ∃ q ∈ gradingWN (rank (latP 4)) 4, ∃ a b : ℂ,
      v = latStateGen (latP 4) q 0 + a • latChargeGen (latP 4) ((1 : ℤ) : (latP 4).carrier) +
        b • latChargeGen (latP 4) ((-1 : ℤ) : (latP 4).carrier) := by
  rw [V2m_grading_eq] at hv
  have hle : gradingLatGen (latP 4) 4 ≤ bigradα (latP 4) (4, 0) ⊔
      bigradα (latP 4) (0, ((1 : ℤ) : (latP 4).carrier)) ⊔
      bigradα (latP 4) (0, ((-1 : ℤ) : (latP 4).carrier)) := by
    apply iSup_le
    intro α
    change ℤ at α
    by_cases h0 : α = 0
    · subst h0
      rw [halfNorm_four]
      exact le_sup_left.trans le_sup_left
    by_cases h1 : α = 1
    · subst h1
      rw [halfNorm_four]
      exact le_sup_right.trans le_sup_left
    by_cases h2 : α = -1
    · subst h2
      rw [halfNorm_four]
      exact le_sup_right
    rw [bigradα_eq_bot_of_neg (latP 4) α]
    · exact bot_le
    · rw [halfNorm_four]
      have hsq : 4 ≤ α * α := by
        rcases lt_or_gt_of_ne h0 with h | h
        · have : α ≤ -2 := by omega
          nlinarith
        · have : 2 ≤ α := by omega
          nlinarith
      nlinarith
  obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp (hle hv)
  obtain ⟨x₀, hx₀, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hx₀
  obtain ⟨q₁, hq₁, rfl⟩ := Submodule.mem_map.mp hy
  obtain ⟨q₂, hq₂, rfl⟩ := Submodule.mem_map.mp hz
  rw [gradingZN_of_nonneg (by norm_num)] at hq hq₁ hq₂
  obtain ⟨a, rfl⟩ := fock_zero_eq (by simpa using hq₁)
  obtain ⟨b, rfl⟩ := fock_zero_eq (by simpa using hq₂)
  refine ⟨q, by simpa using hq, a, b, ?_⟩
  simp only [mkEα_apply]
  rfl

/-! ## §2 Raw-polynomial certificates -/

/-- The neutral sector of `V₈` in the charged raw representation. -/
noncomputable abbrev st (P : RawPoly ℕ) : LatModuleGen (latP 4) := sector 0 (evRc (a0 4) (cα 4) P)

theorem st_liftR (P : RawPoly ℕ) : st (liftR P) = ls 4 P := by
  change latStateGen (latP 4) (evRc (a0 4) (cα 4) (liftR P)) 0 = _
  rw [evRc_liftR]

theorem st_normR (P : RawPoly ℕ) : st (normR P) = st P := by
  rw [st, evRc_normR]

theorem st_eq_of_normR {P Q : RawPoly ℕ} (h : normR P = normR Q) : st P = st Q := by
  rw [← st_normR P, h, st_normR]

theorem st_append (P Q : RawPoly ℕ) : st (P ++ Q) = st P + st Q := by
  rw [st, evRc_append, map_add]

theorem st_scaleR (q : ℚ) (P : RawPoly ℕ) : st (scaleR q P) = (q : ℂ) • st P := by
  rw [st, evRc_scaleR, map_smul]

theorem smul_ls_st (Q P : RawPoly ℕ) (n : ℤ) :
    (V2m 4 four_ge_one).smul (ls 4 Q) n (st P) = st (neutralAction Q n 0 P) :=
  neutralAction_sound Q P n 0

/-- `ω` of `V₈`. -/
noncomputable abbrev ωc : LatModuleGen (latP 4) := (V2m 4 four_ge_one).conformalVector

theorem ωc_eq : ωc = st (liftR omR) := by rw [st_liftR]; exact omega_V2m 4 four_ge_one

/-- `ω₍₀₎ω`. -/
noncomputable abbrev Lω : LatModuleGen (latP 4) := (V2m 4 four_ge_one).smul ωc 0 ωc
/-- `ω₍₋₁₎ω`. -/
noncomputable abbrev Aω : LatModuleGen (latP 4) := (V2m 4 four_ge_one).smul ωc (-1) ωc
/-- `ω₍₀₎ω₍₀₎ω`. -/
noncomputable abbrev Bω : LatModuleGen (latP 4) :=
  (V2m 4 four_ge_one).smul ωc 0 ((V2m 4 four_ge_one).smul ωc 0 ωc)

def NL : RawPoly ℕ := neutralAction omR 0 0 (liftR omR)
def NA : RawPoly ℕ := neutralAction omR (-1) 0 (liftR omR)
def NB : RawPoly ℕ := neutralAction omR 0 0 NL

theorem smul_ω_st (n : ℤ) (P : RawPoly ℕ) :
    (V2m 4 four_ge_one).smul ωc n (st P) = st (neutralAction omR n 0 P) := by
  change (V2m 4 four_ge_one).smul (V2m 4 four_ge_one).conformalVector n (st P) = _
  rw [omega_V2m]; exact smul_ls_st omR P n

theorem Lω_eq : Lω = st NL := by
  have h : Lω = (V2m 4 four_ge_one).smul ωc 0 (st (liftR omR)) := by rw [← ωc_eq]
  rw [h, smul_ω_st]; rfl

theorem Aω_eq : Aω = st NA := by
  have h : Aω = (V2m 4 four_ge_one).smul ωc (-1) (st (liftR omR)) := by rw [← ωc_eq]
  rw [h, smul_ω_st]; rfl

theorem Bω_eq : Bω = st NB := by
  have h : Bω = (V2m 4 four_ge_one).smul ωc 0 Lω := rfl
  rw [h, Lω_eq, smul_ω_st]; rfl

theorem cert_xx00 : normR (liftR [(1, [0, 0])]) = normR (scaleR 2 (liftR omR)) := by
  decide +kernel

theorem cert_xx10 : normR (liftR [(1, [1, 0])]) = normR NL := by decide +kernel

theorem cert_xx20 : normR (liftR [(1, [2, 0])]) =
    normR (scaleR (4/9) NA ++ scaleR (1/6) NB ++ scaleR (-1/9) (liftR JR)) := by
  decide +kernel

theorem cert_xx11 : normR (liftR [(1, [1, 1])]) =
    normR (scaleR (-8/9) NA ++ scaleR (2/3) NB ++ scaleR (2/9) (liftR JR)) := by
  decide +kernel

theorem cert_xx0000 : normR (liftR [(1, [0, 0, 0, 0])]) =
    normR (scaleR (20/9) NA ++ scaleR (-2/3) NB ++ scaleR (4/9) (liftR JR)) := by
  decide +kernel

theorem sector_word2 (i j : ℕ) :
    sector 0 (xx i * xx j) = st (liftR [(1, [i, j])]) := by
  rw [st_liftR]
  change _ = latStateGen (latP 4) (evR (a0 4) [(1, [i, j])]) 0
  simp [evR_cons, evR_nil, evalWord_cons, evalWord_nil, sector]
  rfl

theorem sector_word4 (i j k l : ℕ) :
    sector 0 (xx i * xx j * xx k * xx l) = st (liftR [(1, [i, j, k, l])]) := by
  rw [st_liftR]
  change _ = latStateGen (latP 4) (evR (a0 4) [(1, [i, j, k, l])]) 0
  simp [evR_cons, evR_nil, evalWord_cons, evalWord_nil, sector, mul_assoc]
  rfl

theorem Jc_eq_st : Jc = st (liftR JR) := by rw [st_liftR]

/-! ## §3 The spans -/

theorem low_even_image :
    Submodule.map (sector 0) (Submodule.span ℂ lowEven) ≤
      Submodule.span ℂ {(V2m 4 four_ge_one).vacuum, ωc, Lω} := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [lowEven, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Submodule.subset_span (Set.mem_insert _ _)
  · have h : sector 0 (xx 0 * xx 0) = (2 : ℂ) • ωc := by
      rw [sector_word2, st_eq_of_normR cert_xx00, st_scaleR, ← ωc_eq]; norm_num
    rw [SetLike.mem_coe, h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · have h : sector 0 (xx 1 * xx 0) = Lω := by
      rw [sector_word2, st_eq_of_normR cert_xx10, Lω_eq]
    rw [SetLike.mem_coe, h]
    exact Submodule.subset_span (by simp)

theorem four_even_image :
    Submodule.map (sector 0) (Submodule.span ℂ fourEven) ≤
      Submodule.span ℂ {Aω, Bω, Jc} := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [fourEven, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hA : Aω ∈ Submodule.span ℂ {Aω, Bω, Jc} := Submodule.subset_span (by simp)
  have hB : Bω ∈ Submodule.span ℂ {Aω, Bω, Jc} := Submodule.subset_span (by simp)
  have hJ : Jc ∈ Submodule.span ℂ {Aω, Bω, Jc} := Submodule.subset_span (by simp)
  have key : ∀ (a b c : ℚ), ((a : ℂ) • Aω + (b : ℂ) • Bω) + (c : ℂ) • Jc ∈
      Submodule.span ℂ {Aω, Bω, Jc} := fun a b c =>
    Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hA)
      (Submodule.smul_mem _ _ hB)) (Submodule.smul_mem _ _ hJ)
  rcases hx with rfl | rfl | rfl
  · rw [SetLike.mem_coe, sector_word2, st_eq_of_normR cert_xx20, st_append, st_append,
      st_scaleR, st_scaleR, st_scaleR, ← Aω_eq, ← Bω_eq, ← Jc_eq_st]
    exact key _ _ _
  · rw [SetLike.mem_coe, sector_word2, st_eq_of_normR cert_xx11, st_append, st_append,
      st_scaleR, st_scaleR, st_scaleR, ← Aω_eq, ← Bω_eq, ← Jc_eq_st]
    exact key _ _ _
  · rw [SetLike.mem_coe, sector_word4, st_eq_of_normR cert_xx0000, st_append, st_append,
      st_scaleR, st_scaleR, st_scaleR, ← Aω_eq, ← Bω_eq, ← Jc_eq_st]
    exact key _ _ _

/-- The parity projection of a neutral state. -/
theorem half_theta_neutral (q : FockN (rank (latP 4))) :
    (1 / 2 : ℂ) • (latStateGen (latP 4) q 0 + thetaLat (latP 4) (latStateGen (latP 4) q 0)) =
      sector 0 (evenPart q) := by
  rw [thetaLat_latStateGen, evenPart_apply, map_smul, map_add]
  rfl

theorem theta_fixed_eq {v : LatModuleGen (latP 4)} (hv : thetaLat (latP 4) v = v) :
    v = (1 / 2 : ℂ) • (v + thetaLat (latP 4) v) := by
  rw [hv, ← two_smul ℂ v, smul_smul]; norm_num

/-- `V₈⁺` in weight `k ≤ 3`, inside `V₈`. -/
theorem plus_low_mem_span {k : ℕ} (hk : k ≤ 3) {w : VP 4 four_ge_one}
    (hw : w ∈ (V2mPlus 4 four_ge_one).grading (k : ℤ)) :
    (w : LatModuleGen (latP 4)) ∈ Submodule.span ℂ {(V2m 4 four_ge_one).vacuum, ωc, Lω} := by
  obtain ⟨q, hq, hwq⟩ := V8_grading_low hk (v := (w : LatModuleGen (latP 4))) hw
  have hθ := (mem_VP_iff 4 four_ge_one _).mp w.2
  rw [theta_fixed_eq hθ, hwq, half_theta_neutral]
  exact low_even_image (Submodule.mem_map_of_mem (evenPart_low_mem (fock_low_mem_span hk hq)))

/-- `V₈⁺` in weight four, inside `V₈`. -/
theorem plus_four_mem {w : VP 4 four_ge_one}
    (hw : w ∈ (V2mPlus 4 four_ge_one).grading 4) :
    ∃ α β γ δ : ℂ, (w : LatModuleGen (latP 4)) = α • Aω + β • Bω + γ • Jc + δ • Ec := by
  obtain ⟨q, hq, a, b, hwq⟩ := V8_grading_four (v := (w : LatModuleGen (latP 4))) hw
  have hθ := (mem_VP_iff 4 four_ge_one _).mp w.2
  have hmem := four_even_image (Submodule.mem_map_of_mem (evenPart_four_mem
    (fock_four_mem_span hq)))
  obtain ⟨α, z, hz, hαz⟩ := Submodule.mem_span_insert.mp hmem
  obtain ⟨β, γ, rfl⟩ := Submodule.mem_span_pair.mp hz
  refine ⟨α, β, γ, (a + b) / 2, ?_⟩
  have t1 : thetaLat (latP 4) (latChargeGen (latP 4) ((1 : ℤ) : (latP 4).carrier)) =
      latChargeGen (latP 4) ((-1 : ℤ) : (latP 4).carrier) := thetaLat_latChargeGen _ _
  have t2 : thetaLat (latP 4) (latChargeGen (latP 4) ((-1 : ℤ) : (latP 4).carrier)) =
      latChargeGen (latP 4) ((1 : ℤ) : (latP 4).carrier) := thetaLat_latChargeGen _ _
  rw [theta_fixed_eq hθ, hwq, map_add, map_add, map_smul, map_smul, t1, t2]
  have key : (1 / 2 : ℂ) • (latStateGen (latP 4) q 0 +
      thetaLat (latP 4) (latStateGen (latP 4) q 0)) = α • Aω + β • (Bω) + γ • Jc := by
    rw [half_theta_neutral, hαz]; module
  have hE : Ec = latChargeGen (latP 4) ((1 : ℤ) : (latP 4).carrier) +
      latChargeGen (latP 4) ((-1 : ℤ) : (latP 4).carrier) := rfl
  rw [hE]
  linear_combination (norm := module) key

end VOA.Classification.COne.OrbRat5
