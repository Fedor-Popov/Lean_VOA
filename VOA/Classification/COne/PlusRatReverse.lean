import VOA.Classification.COne.PlusRatVacuumSign
import VOA.Classification.COne.Distinct
import VOA.Moonshine.SigmaExistGeneric

/-! # Vacuum kernel / sign quotient: the reverse orientation

`PairSplitting m hm (.inr 0) (.inr 1)` (kernel bottom zero, quotient bottom one) is proved for
every `m ≥ 2` with only the sign row at weight one, without contragredient modules.

Route.
* Kernel.  A weight-zero top vector `z` of the kernel has the vacuum character, so all
  positive-weight zero modes kill it; the E-telescope of `PlusRatTelescope` then gives
  `ζ · T z = 0`, hence `T z = 0`, and the kernel has no generalized weight one
  (`kernel_weightOne_eq_zero`).
* Lift.  For an `L(0)`-eigenvector `w` of weight one, the dual telescope
  `L(1) ∑_{n<m} (-1)^n C(J,n) E_{J-n} E_n w = 0` holds (`lowering_telescope_core`, using
  `L(1)E = 0`).  In the quotient the same sum is `ζ` acting on the top, and `ζ` is invertible
  modulo `ω - 1`; transporting back, `L(1) w = 0`.  Then `[L(1), a_{α-1}]` gives
  `a_α w = 0` for all `a`, i.e. `w` is a top vector of the whole extension.
* Splitting.  By Li's single-mode spanning, the cyclic module of a top vector of weight one
  has no generalized weight zero, so it avoids the kernel.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRatSign
open VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN VOA.SparseRational
open PlusUnitary PlusC2 PlusC2Eval PlusCharacterTable PlusSplitting PlusRatTelescope LatMod
open PlusZhuSchur PlusZhuNormalForms PlusResonantPairs VOA.Huang.LogRemovalAdmissible
open ABDWeakAdmissible PlusRational

universe u

/-! ## §1  `L(1)` commutator on weak modules -/

section General
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- `[L(1), u_n] = (2 wt u - n - 2) u_{n+1} + (L(1)u)_n` on a weak module. -/
theorem L1_comm (A : WeakModule W M) {wt : ℤ} {u : V} (hu : u ∈ W.grading wt) (n : ℤ)
    (x : M) :
    mode (A.YM W.conformalVector) 2 (mode (A.YM u) n x) -
        mode (A.YM u) n (mode (A.YM W.conformalVector) 2 x)
      = ((2 * wt - n - 2 : ℤ) : ℂ) • mode (A.YM u) (n + 1) x
        + mode (A.YM (W.L 1 u)) n x := by
  rw [mode_commutator A]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (0 : ℤ) 2) (fun i hi => by
    rw [Function.mem_support] at hi
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_apply_neg 2 h, zero_smul]
    · rw [cbz_lt (p := 2) (c := i) (by norm_num) h, zero_smul])]
  rw [show Finset.Icc (0 : ℤ) 2 = {0, 1, 2} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e0 : W.smul W.conformalVector 0 u = W.L (-1) u := by
    rw [VertexOperatorAlgebra.L_def]; rfl
  have e1 : W.smul W.conformalVector 1 u = (wt : ℂ) • u := by
    rw [← VertexOperatorAlgebra.L_zero_grading W u hu, VertexOperatorAlgebra.L_def]; rfl
  have e2 : W.smul W.conformalVector 2 u = W.L 1 u := by
    rw [VertexOperatorAlgebra.L_def]; rfl
  rw [e0, e1, e2]
  have hT := act_T_covariance A u (2 + n - 0) x
  simp only [WeakModule.act_def] at hT
  rw [hT, map_smul, mode_smul, LinearMap.smul_apply]
  have c0 : cbz 2 0 = 1 := cbz_zero 2
  have c1 : cbz 2 1 = 2 := by
    have := cbz_natCast_eq_choose (a := 2) (k := 1) (by norm_num)
    norm_num at this; exact this
  have c2 : cbz 2 2 = 1 := by
    have := cbz_natCast_eq_choose (a := 2) (k := 2) (by norm_num)
    norm_num at this; exact this
  rw [c0, c1, c2, show 2 + n - 0 - 1 = n + 1 by ring, show 2 + n - 1 = n + 1 by ring,
    show 2 + n - 2 = n by ring]
  rw [one_smul, smul_smul, ← add_assoc, ← add_smul]
  congr 2
  · push_cast; ring
  all_goals simp

/-- Zero modes of arbitrary states preserve every generalized `L(0)`-eigenspace. -/
theorem oLevW_mem_maxGen (A : WeakModule W M) (s : V) {μ : ℂ} {w : M}
    (hw : w ∈ (L0 A).maxGenEigenspace μ) : oLevW A 0 s w ∈ (L0 A).maxGenEigenspace μ := by
  have hv : s ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun s => oLevW A 0 s w ∈ _) hv ?_ ?_ ?_
  · intro k a ha
    rw [oLevW_homogeneous A 0 ha]
    have h := mode_mem_maxGenEigenspace A ha (k - 1 + 0) hw
    have hc : μ + ((k - (k - 1 + 0) - 1 : ℤ) : ℂ) = μ := by
      rw [show (k - (k - 1 + 0) - 1 : ℤ) = 0 by ring]; simp
    rwa [hc] at h
  · simp
  · intro a b ha hb
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ ha hb

/-- Weak-module homomorphisms intertwine zero modes of arbitrary states. -/
theorem hom_oLevW {N : Type u} [AddCommGroup N] [Module ℂ N] (A : WeakModule W M)
    (B : WeakModule W N) (q : A.Hom B) (s : V) (w : M) :
    q.toLinearMap (oLevW A 0 s w) = oLevW B 0 s (q.toLinearMap w) := by
  have hv : s ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction _
    (motive := fun s => q.toLinearMap (oLevW A 0 s w) = oLevW B 0 s (q.toLinearMap w)) hv
    ?_ ?_ ?_
  · intro k a ha
    rw [oLevW_homogeneous A 0 ha, oLevW_homogeneous B 0 ha]
    exact q.map_act a _ w
  · simp
  · intro a b ha hb
    rw [map_add, LinearMap.add_apply, map_add, ha, hb, map_add, LinearMap.add_apply]

end General

/-! ## §2  `L(1) E = 0` -/

variable (m : ℕ) (hm : 1 ≤ m)

theorem charge_eq_evRc (δ : (latP m).carrier) (c : ℂ) :
    latChargeGen (latP m) δ = latStateGen (latP m) (evRc (a0 m) c [(1, [])]) δ := by
  rw [evRc_cons, evRc_nil, add_zero]
  simp [latChargeGen, vacuumN, evalWord]

/-- `L(1) e^δ = 0`, by the certified charged evaluator. -/
theorem L1_charge (δ : (latP m).carrier) :
    (V2m m hm).smul (latStateGen (latP m) (evR (a0 m) omR) 0) 2
      (latChargeGen (latP m) δ) = 0 := by
  rw [charge_eq_evRc m δ (chargeCoord (latP m) δ (a0 m)),
    V2m_smul_evRc m hm omR [(1, [])] 2 0 δ (by simp [wWtC]), ← evRc_normR]
  have h : normR (polyActC omR (-2 - 1) 0 [(1, [])]) = [] := by decide +kernel
  rw [h, evRc_nil]
  simp [latStateGen]

/-- `E` is quasi-primary. -/
theorem L1_E : (V2mPlus m hm).L 1 (EP m hm) = 0 := by
  have h : (V2mPlus m hm).L 1 (EP m hm) =
      (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 2 (EP m hm) := by
    rw [VertexOperatorAlgebra.L_def]; rfl
  rw [h]
  apply Subtype.ext
  rw [V2mPlus_smul_coe, omega_coe, EP_coe, PreVertexAlgebra.smul_add_right, L1_charge,
    L1_charge, add_zero]
  rfl

theorem grading_one_eq_bot (hm2 : 2 ≤ m) : (V2mPlus m hm).grading 1 = ⊥ := by
  haveI := (V2mPlus m hm).finrank 1
  exact Submodule.finrank_eq_zero.mp (V2mPlus_finrank_one m hm hm2)

/-! ## §3  The vacuum character -/

@[reducible] local instance zhuRingRR : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuAlgebraRR : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-- The generators determine the top action of a character. -/
theorem topEvaluation_eq_char (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) {y : M} (hy : y ∈ Omega A)
    (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ)
    (hg : ∀ i : Fin 3, topEvaluation A y hy (VOA.mk (V2mPlus m hm) (gP m hm i)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm i)) • y) (r : VOA.A (V2mPlus m hm)) :
    topEvaluation A y hy r = χ r • y := by
  set f := topEvaluation A y hy
  let B : Subalgebra ℂ (VOA.A (V2mPlus m hm)) :=
    { carrier := {r | f r = χ r • y}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨s, rfl⟩ := VOA.mk_surjective (V2mPlus m hm) a
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [topEvaluation_mk_mul, hb, map_smul, ← topEvaluation_mk A y hy s, ha, map_mul,
          smul_smul, mul_comm]
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, map_add, add_smul]
      algebraMap_mem' := by
        intro c
        change f (algebraMap ℂ _ c) = χ (algebraMap ℂ _ c) • y
        rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one (A := VOA.A (V2mPlus m hm)),
          map_smul, topEvaluation_one]
        simp }
  have htop : B = ⊤ := by
    apply top_unique
    rw [← V2mPlus_zhu_adjoin_generators m hm hm2]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact hg i
  have hr : r ∈ B := htop ▸ Algebra.mem_top
  exact hr

/-- The adjoint vacuum is a top vector. -/
theorem vacuum_mem_Omega : (V2mPlus m hm).vacuum ∈ Omega (adjointWeakModule (V2mPlus m hm)) := by
  intro β v hv n hn
  by_cases hβ : β < 0
  · rw [(V2mPlus m hm).positivity β hβ, Submodule.mem_bot] at hv
    subst hv
    simp
  · exact ((V2mPlus m hm).creation v).2 n (by omega)

theorem vacuum_gen_eval {a : VP m hm} {w : ℤ} (ha : a ∈ (V2mPlus m hm).grading w)
    (hw : 1 ≤ w) :
    topEvaluation (adjointWeakModule (V2mPlus m hm)) _ (vacuum_mem_Omega m hm)
      (VOA.mk (V2mPlus m hm) a) = 0 := by
  rw [topEvaluation_mk, oLevW_homogeneous _ 0 ha]
  exact ((V2mPlus m hm).creation a).2 _ (by omega)

/-- The vacuum row vanishes on every positive-weight state. -/
theorem vacuum_char_eval (hm2 : 2 ≤ m) (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ)
    (hχ : HasValues m hm (.inr 0) χ) {a : VP m hm} {α : ℤ}
    (ha : a ∈ (V2mPlus m hm).grading α) (hα : 1 ≤ α) : χ (VOA.mk (V2mPlus m hm) a) = 0 := by
  have h0 : topEvaluation (adjointWeakModule (V2mPlus m hm)) _ (vacuum_mem_Omega m hm)
      (VOA.mk (V2mPlus m hm) (gP m hm 0)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) • (V2mPlus m hm).vacuum := by
    rw [show gP m hm 0 = (V2mPlus m hm).conformalVector from rfl,
      vacuum_gen_eval m hm (V2mPlus m hm).conformal_mem (by norm_num)]
    rw [show (V2mPlus m hm).conformalVector = gP m hm 0 from rfl, hχ.1]
    simp [values, exceptional]
  have h1 : topEvaluation (adjointWeakModule (V2mPlus m hm)) _ (vacuum_mem_Omega m hm)
      (VOA.mk (V2mPlus m hm) (gP m hm 1)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) • (V2mPlus m hm).vacuum := by
    rw [show gP m hm 1 = WP m hm from rfl,
      vacuum_gen_eval m hm (WP_mem_grading m hm) (by norm_num)]
    rw [show WP m hm = gP m hm 1 from rfl, hχ.2.1]
    simp [values, exceptional]
  have h2 : topEvaluation (adjointWeakModule (V2mPlus m hm)) _ (vacuum_mem_Omega m hm)
      (VOA.mk (V2mPlus m hm) (gP m hm 2)) =
      χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) • (V2mPlus m hm).vacuum := by
    rw [show gP m hm 2 = EP m hm from rfl,
      vacuum_gen_eval m hm (EP_mem_grading m hm) (by omega)]
    rw [show EP m hm = gP m hm 2 from rfl, hχ.2.2]
    simp [values, exceptional]
  have hall := topEvaluation_eq_char m hm hm2 _ (vacuum_mem_Omega m hm) χ (by
    intro i; fin_cases i
    exacts [h0, h1, h2]) (VOA.mk (V2mPlus m hm) a)
  rw [vacuum_gen_eval m hm ha hα] at hall
  rcases smul_eq_zero.mp hall.symm with h | h
  · exact h
  · exact absurd h (V2mPlus_isSimple m hm).vacuum_ne_zero

include hm in
/-- Only the vacuum row has weight zero. -/
theorem label_of_weight_zero (i : Label m) (hw : weight m i = 0) : i = .inr 0 := by
  rcases i with r | i
  · exfalso
    simp only [weight] at hw
    have hpos : (0 : ℚ) < ((r.val : ℚ) + 1) ^ 2 / (4 * m) := by
      have : (0 : ℚ) < m := by exact_mod_cast hm
      positivity
    linarith
  · fin_cases i
    · rfl
    all_goals (exfalso; simp [weight] at hw <;> omega)

/-- An element vanishing at the vacuum row is a multiple of `ω`. -/
theorem exists_mul_omega (hm2 : 2 ≤ m) (r : VOA.A (V2mPlus m hm))
    (hr : ∀ (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ), HasValues m hm (.inr 0) χ → χ r = 0) :
    ∃ ξ : VOA.A (V2mPlus m hm), r = ξ * generator m hm 0 := by
  classical
  obtain ⟨χ, hχ, hinj⟩ := exists_characterTable m hm hm2
  letI := finiteDimensional_A_of_C2Cofinite _ (V2mPlus_c2Cofinite m hm)
  have hdim : Module.finrank ℂ (VOA.A (V2mPlus m hm)) ≤ Fintype.card (Label m) := by
    rw [V2mPlus_zhu_finrank m hm hm2, card_label m hm]
  let e := characterAlgEquiv χ hinj hdim
  have he_apply : ∀ r i, e r i = χ i r := fun _ _ => rfl
  refine ⟨e.symm (fun i => if χ i (generator m hm 0) = 0 then 0
    else χ i r / χ i (generator m hm 0)), ?_⟩
  apply e.injective
  funext i
  rw [map_mul, AlgEquiv.apply_symm_apply]
  simp only [Pi.mul_apply, he_apply]
  by_cases h0 : χ i (generator m hm 0) = 0
  · rw [if_pos h0, zero_mul]
    have hw : weight m i = 0 := by
      rw [hasValues_omega m hm (hχ i)] at h0
      exact_mod_cast h0
    have hi := label_of_weight_zero m hm i hw
    subst hi
    exact hr _ (hχ _)
  · rw [if_neg h0, div_mul_cancel₀ _ h0]

/-- Positive-weight zero modes kill every weight-zero top vector. -/
theorem zeroWeight_top_zeroMode (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M) {z : M} (hz : z ∈ Omega A) (hL : L0 A z = 0)
    {a : VP m hm} {α : ℤ} (ha : a ∈ (V2mPlus m hm).grading α) (hα : 1 ≤ α) :
    mode (A.YM a) (α - 1) z = 0 := by
  obtain ⟨ξ, hξ⟩ := exists_mul_omega m hm hm2 (VOA.mk (V2mPlus m hm) a)
    (fun χ hχ => vacuum_char_eval m hm hm2 χ hχ ha hα)
  have h1 : mode (A.YM a) (α - 1) z = topEvaluation A z hz (VOA.mk (V2mPlus m hm) a) := by
    rw [topEvaluation_mk, oLevW_homogeneous A 0 ha, add_zero]
  rw [h1, hξ]
  obtain ⟨s, rfl⟩ := VOA.mk_surjective (V2mPlus m hm) ξ
  rw [topEvaluation_mk_mul, topEvaluation_omega m hm A hz, hL, map_zero]

/-! ## §4  General word and telescoping lemmas -/

section Words
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

theorem homogeneousWord_hom {N : Type u} [AddCommGroup N] [Module ℂ N]
    (A : WeakModule W M) (B : WeakModule W N) (φ : A.Hom B) :
    ∀ (l : List (HomogeneousLetter W)) (x : M),
      homogeneousWord B l (φ.toLinearMap x) = φ.toLinearMap (homogeneousWord A l x)
  | [], x => rfl
  | a :: l, x => by
    simp only [homogeneousWord, LinearMap.comp_apply]
    rw [homogeneousWord_hom A B φ l x]
    exact (φ.map_act _ _ _).symm

theorem homogeneousWord_vacuum_mem :
    ∀ l : List (HomogeneousLetter W),
      homogeneousWord (adjointWeakModule W) l W.vacuum ∈ W.grading (homogeneousDegree l)
  | [] => by
    simp only [homogeneousWord, homogeneousDegree, LinearMap.id_apply]
    exact W.vacuum_mem_grading_zero
  | a :: l => by
    simp only [homogeneousWord, LinearMap.comp_apply, homogeneousDegree]
    have h := W.toPreVertexAlgebra.smul_mem_grading a.homogeneous
      (homogeneousWord_vacuum_mem l) a.modeIndex
    have he : a.weight + homogeneousDegree l - a.modeIndex - 1 =
        a.weight - a.modeIndex - 1 + homogeneousDegree l := by ring
    rw [he] at h
    exact h

/-- **The lowering telescope.** If `a ∈ W_N` is quasi-primary, `L(1)x` is killed by all
non-negative modes of `a` and `a_{N-1} a_N x = 0`, then
`L(1) ∑_{n<N} (-1)^n C(J,n) a_{J-n} a_n x = 0`, `J = 2N - 2`. -/
theorem lowering_telescope_core (A : WeakModule W M) {a : V} (N : ℕ) (hN1 : 1 ≤ N)
    (ha : a ∈ W.grading (N : ℤ)) (hL1a : W.L 1 a = 0) (x : M)
    (h1 : ∀ n : ℕ, mode (A.YM a) n (mode (A.YM W.conformalVector) 2 x) = 0)
    (h2 : mode (A.YM a) ((N : ℤ) - 1) (mode (A.YM a) N x) = 0) :
    mode (A.YM W.conformalVector) 2
      (∑ n ∈ Finset.range N, ((-1 : ℂ) ^ n * ((2 * N - 2).choose n : ℂ)) •
        mode (A.YM a) (((2 * N - 2 : ℕ) : ℤ) - n) (mode (A.YM a) n x)) = 0 := by
  set J := 2 * N - 2 with hJdef
  have hJ : (J : ℤ) = 2 * (N : ℤ) - 2 := by omega
  have hcomm : ∀ (k : ℤ) (y : M), mode (A.YM W.conformalVector) 2 (mode (A.YM a) k y) =
      mode (A.YM a) k (mode (A.YM W.conformalVector) 2 y) +
        ((2 * (N : ℤ) - k - 2 : ℤ) : ℂ) • mode (A.YM a) (k + 1) y := by
    intro k y
    have h := L1_comm A ha k y
    rw [hL1a, map_zero] at h
    have h0 : mode (0 : (Module.End ℂ M)⟦z^±⟧) k y = 0 := rfl
    rw [h0, add_zero] at h
    rw [← h]; abel
  let g : ℕ → M := fun k => mode (A.YM a) ((J : ℤ) - k + 1) (mode (A.YM a) k x)
  let H : ℕ → M := fun k => (-(-1 : ℂ) ^ k * (k : ℂ) * (J.choose k : ℂ)) • g k
  rw [map_sum]
  have hstep : ∀ n ∈ Finset.range N,
      mode (A.YM W.conformalVector) 2 (((-1 : ℂ) ^ n * (J.choose n : ℂ)) •
        mode (A.YM a) ((J : ℤ) - n) (mode (A.YM a) n x)) = H (n + 1) - H n := by
    intro n _
    rw [map_smul, hcomm, hcomm, h1 n, zero_add]
    have hgn1 : mode (A.YM a) ((J : ℤ) - n) (mode (A.YM a) ((n : ℤ) + 1) x) = g (n + 1) := by
      simp only [g]
      congr 1
      · congr 1; push_cast; ring
    have hgn : mode (A.YM a) ((J : ℤ) - n + 1) (mode (A.YM a) (n : ℤ) x) = g n := rfl
    rw [map_smul, hgn1, hgn]
    simp only [H]
    have hc := choose_mul_sub J n
    have hc1 : ((2 * (N : ℤ) - (n : ℤ) - 2 : ℤ) : ℂ) = (J : ℂ) - n := by
      rw [show (2 * (N : ℤ) - (n : ℤ) - 2 : ℤ) = (J : ℤ) - n by omega]; push_cast; ring
    have hc2 : ((2 * (N : ℤ) - ((J : ℤ) - n) - 2 : ℤ) : ℂ) = (n : ℂ) := by
      rw [show (2 * (N : ℤ) - ((J : ℤ) - n) - 2 : ℤ) = n by omega]; push_cast; ring
    rw [hc1, hc2]
    push_cast
    linear_combination (norm := module) (((-1 : ℂ) ^ n) * hc) • g (n + 1)
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub]
  have hgN : g N = 0 := by
    simp only [g]
    rw [show (J : ℤ) - (N : ℕ) + 1 = (N : ℤ) - 1 by omega]
    exact h2
  simp only [H, hgN, smul_zero, Nat.cast_zero, mul_zero, zero_mul, zero_smul, sub_zero]

end Words

/-! ## §5  The kernel has no weight one -/

section Kernel
variable {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus m hm) M)
  (P : Submodule (modeAlg A) M)

theorem mem_P_mode (a : VP m hm) (n : ℤ) {x : M} (hx : x ∈ P) : mode (A.YM a) n x ∈ P :=
  P.smul_mem (⟨mode (A.YM a) n, Algebra.subset_adjoin ⟨a, n, rfl⟩⟩ : modeAlg A) hx

/-- An eigenvector inside a mode submodule. -/
theorem exists_eigen_in (μ : ℂ) {v : M} (hvP : v ∈ P)
    (hv : v ∈ (L0 A).maxGenEigenspace μ) (hv0 : v ≠ 0) :
    ∃ z ∈ P, z ≠ 0 ∧ L0 A z = μ • z := by
  classical
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hv
  set f := L0 A - μ • (1 : Module.End ℂ M)
  have hmem : ∀ j : ℕ, (f ^ j) v ∈ P := by
    intro j
    induction j with
    | zero => simpa using hvP
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      change L0 A ((f ^ j) v) - μ • (f ^ j) v ∈ P
      exact P.sub_mem (mem_P_mode m hm A P _ 1 ih) (P.smul_of_tower_mem μ ih)
  have hex : ∃ j : ℕ, (f ^ (j + 1)) v = 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (by simpa using hk) hv0
    · exact ⟨k - 1, by rwa [Nat.sub_add_cancel hk0]⟩
  let j := Nat.find hex
  have hj : (f ^ (j + 1)) v = 0 := Nat.find_spec hex
  refine ⟨(f ^ j) v, hmem j, ?_, ?_⟩
  · intro h0
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, pow_zero] at h0; exact hv0 h0
    · have := Nat.find_min hex (show j - 1 < j by omega)
      apply this
      rwa [Nat.sub_add_cancel hj0]
  · have h := hj
    rw [pow_succ', Module.End.mul_apply] at h
    change L0 A ((f ^ j) v) - μ • (f ^ j) v = 0 at h
    exact sub_eq_zero.mp h

/-- A weight-zero eigenvector of a bottom-zero kernel is vacuum-like. -/
theorem translation_zero_of_kernel_zero (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m)
    (hbP : FactorBottom A ⊥ P 0) {z : M} (hzP : z ∈ P) (hL : L0 A z = 0) :
    translation A z = 0 := by
  have hzg : z ∈ (L0 A).maxGenEigenspace 0 := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hL
  have hzΩ : z ∈ Omega A := kernel_bottom_mem_Omega A P 0 hbP hzP hzg
  have hyL : L0 A (translation A z) = translation A z := by
    have hc := L0_commutator_weak A (V2mPlus m hm).conformal_mem z 0
    rw [hL, map_zero, add_zero] at hc
    norm_num at hc
    exact hc
  have hyΩ : translation A z ∈ Omega A := by
    intro β v hv n hn
    rw [mode_translation_defect A v n z, Omega_mode_vanish hzΩ hv hn, map_zero, zero_add]
    by_cases hβ : β < 0
    · rw [(V2mPlus m hm).positivity β hβ, Submodule.mem_bot] at hv
      subst hv
      simp
    by_cases hnβ : n = β
    · subst hnβ
      by_cases hn0 : n = 0
      · subst hn0; simp
      · rw [zeroWeight_top_zeroMode m hm hm2 A hzΩ hL hv (by omega), smul_zero]
    · rw [Omega_mode_vanish hzΩ hv (show β ≤ n - 1 by omega), smul_zero]
  apply weightOne_top_eq_zero m hm hm2 hw1 A hyΩ hyL
  rw [← telescopeE_eq m hm A hyΩ]
  apply telescope_core A (EP m hm) (EP m hm) m (2 * m - 2) z
  · exact zeroWeight_top_zeroMode m hm hm2 A hzΩ hL (EP_mem_grading m hm) (by omega)
  · intro n hn
    by_cases hlast : n = m - 1
    · rw [hlast, show (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 by omega,
        zeroWeight_top_zeroMode m hm hm2 A hzΩ hL (EP_mem_grading m hm) (by omega), map_zero]
    · have hJn : ((2 * m - 2 : ℕ) : ℤ) - n = ((2 * m - 2 - n : ℕ) : ℤ) := by omega
      rw [hJn, lowering_composite_eq A (EP_mem_grading m hm) (EP_mem_grading m hm) hzΩ
        (2 * m - 2 - n) n (by omega) (by omega)]
      rw [zstate, map_sum, LinearMap.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i ≤ 2 * m - 2 - n := by have := Finset.mem_range.mp hi; omega
      have hgr := (V2mPlus m hm).toPreVertexAlgebra.smul_mem_grading (EP_mem_grading m hm)
        (EP_mem_grading m hm) (i : ℤ)
      rw [map_smul, LinearMap.smul_apply, oLevW_homogeneous A 0 hgr, add_zero,
        zeroWeight_top_zeroMode m hm hm2 A hzΩ hL hgr (by omega), smul_zero]

/-- **The bottom-zero kernel has no generalized weight one.** -/
theorem kernel_weightOne_eq_zero (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m)
    (hP : IsAtom P) (hbP : FactorBottom A ⊥ P 0) {w : M} (hwP : w ∈ P)
    (hw : w ∈ (L0 A).maxGenEigenspace 1) : w = 0 := by
  obtain ⟨v, hv, hv0⟩ := SetLike.not_le_iff_exists.mp hbP.1
  have hv0' : v ≠ 0 := fun h => hv0 (by rw [h]; exact Submodule.zero_mem _)
  obtain ⟨z, hzP, hz0, hzL⟩ := exists_eigen_in m hm A P 0 hv.1 hv.2 hv0'
  have hzL' : L0 A z = 0 := by simpa using hzL
  have hT := translation_zero_of_kernel_zero m hm A P hm2 hw1 hbP hzP hzL'
  have hcyc : cyclic A z = P := by
    have hle : cyclic A z ≤ P := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hzP)
    rcases hP.le_iff.mp hle with h | h
    · exfalso
      have hz : z ∈ cyclic A z := Submodule.mem_span_singleton_self z
      rw [h] at hz
      exact hz0 ((Submodule.mem_bot _).mp hz)
    · exact h
  have hzg : z ∈ (L0 A).maxGenEigenspace 0 := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hzL'
  have hdeg := cyclic_inf_gen_eq_degreeSpan (V2mPlus_c2Cofinite m hm) A hzg 1
  have hw' : w ∈ homogeneousDegreeSpan A z 1 := by
    rw [← hdeg]
    refine ⟨?_, ?_⟩
    · change w ∈ cyclic A z
      rw [hcyc]; exact hwP
    · simpa using hw
  have hzero : homogeneousDegreeSpan A z 1 = ⊥ := by
    rw [eq_bot_iff]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    change homogeneousDegree l = 1 at hl
    have hmem := homogeneousWord_vacuum_mem (W := V2mPlus m hm) l
    rw [hl, grading_one_eq_bot m hm hm2, Submodule.mem_bot] at hmem
    change homogeneousWord A l z ∈ (⊥ : Submodule ℂ M)
    have h := homogeneousWord_hom _ A (vacuumLiftHom A z hT) l (V2mPlus m hm).vacuum
    rw [vacuumLiftHom_vacuum, hmem, map_zero] at h
    rw [h]
    exact Submodule.zero_mem _
  rw [hzero] at hw'
  exact (Submodule.mem_bot ℂ).mp hw'

/-- Every weight-zero kernel vector is vacuum-like. -/
theorem kernel_zero_vacuumLike (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m)
    (hP : IsAtom P) (hbP : FactorBottom A ⊥ P 0) {z : M} (hzP : z ∈ P)
    (hz : z ∈ (L0 A).maxGenEigenspace 0) : translation A z = 0 := by
  apply kernel_weightOne_eq_zero m hm A P hm2 hw1 hP hbP
    (mem_P_mode m hm A P _ 0 hzP)
  have h := mode_mem_maxGenEigenspace A (V2mPlus m hm).conformal_mem 0 hz
  have hc : (0 : ℂ) + ((2 - 0 - 1 : ℤ) : ℂ) = 1 := by norm_num
  rw [hc] at h
  exact h

end Kernel

/-! ## §6  Top vectors generate no lower weight (Li's spanning) -/

section Li
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

theorem homogeneousWord_mem_modeSpan (A : WeakModule W M) (x : M) :
    ∀ l : List (HomogeneousLetter W),
      homogeneousWord A l x ∈ VOA.Moonshine.SigmaExist.modeSpan A {x}
  | [] => VOA.Moonshine.SigmaExist.subset_modeSpan A {x} rfl
  | a :: l => by
    simp only [homogeneousWord, LinearMap.comp_apply]
    exact VOA.Moonshine.SigmaExist.act_mem_modeSpan A {x} a.state a.modeIndex
      (homogeneousWord_mem_modeSpan A x l)

/-- The single-mode span of a top vector of eigenvalue `k` avoids generalized weight
below `k`... more precisely it lies in generalized weights different from `k - 1`. -/
theorem modeSpan_le_spectral (A : WeakModule W M) {x : M} (hx : x ∈ Omega A) (k : ℂ)
    (hL : L0 A x = k • x) :
    VOA.Moonshine.SigmaExist.modeSpan A {x} ≤ spectralPart A {μ | μ ≠ k - 1} := by
  have hxg : x ∈ (L0 A).maxGenEigenspace k := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    exact Module.End.mem_eigenspace_iff.mpr hL
  apply Submodule.span_le.mpr
  rintro _ ⟨a, q, y, hy, rfl⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hv : a ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun a => A.act a q y ∈ spectralPart A _) hv
    ?_ ?_ ?_
  · intro j b hb
    by_cases hq : j ≤ q
    · rw [WeakModule.act_def, Omega_mode_vanish hx hb hq]
      exact Submodule.zero_mem _
    · have h := mode_mem_maxGenEigenspace A hb q hxg
      apply Submodule.mem_iSup_of_mem (k + ((j - q - 1 : ℤ) : ℂ))
      apply Submodule.mem_iSup_of_mem
      · exact h
      · intro he
        have h2 : ((j - q - 1 : ℤ) : ℂ) = -1 := by linear_combination he
        have h3 : (j - q - 1 : ℤ) = -1 := by exact_mod_cast h2
        omega
  · simp
  · intro a b ha hb
    have he : A.act (a + b) q y = A.act a q y + A.act b q y := by
      simp only [WeakModule.act_def, map_add, mode_add, LinearMap.add_apply]
    rw [he]
    exact Submodule.add_mem _ ha hb

/-- No word of degree `-1` reaches a top vector's lower neighbour. -/
theorem degreeSpan_neg_one_eq_bot (A : WeakModule W M) {x : M} (hx : x ∈ Omega A) (k : ℂ)
    (hL : L0 A x = k • x) : homogeneousDegreeSpan A x (-1) = ⊥ := by
  have hxg : x ∈ (L0 A).maxGenEigenspace k := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    exact Module.End.mem_eigenspace_iff.mpr hL
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  have hg := homogeneousDegreeSpan_gen A hxg (-1) hv
  have hsp : v ∈ spectralPart A {μ | μ ≠ k - 1} := by
    refine Submodule.span_induction (p := fun v _ => v ∈ spectralPart A {μ | μ ≠ k - 1})
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨l, _, rfl⟩
      exact modeSpan_le_spectral A hx k hL (homogeneousWord_mem_modeSpan A x l)
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro c a _ ha; exact Submodule.smul_mem _ c ha
  have hd := spectralPart_disjoint A (s := {k - 1}) (t := {μ | μ ≠ k - 1})
    (Set.disjoint_left.mpr (by intro μ hμ hn; exact hn (Set.mem_singleton_iff.mp hμ)))
  have hg' : v ∈ spectralPart A {k - 1} := by
    apply Submodule.mem_iSup_of_mem (k - 1)
    apply Submodule.mem_iSup_of_mem rfl
    have he : k + ((-1 : ℤ) : ℂ) = k - 1 := by push_cast; ring
    rwa [he] at hg
  exact Submodule.disjoint_def.mp hd v hg' hsp

end Li

/-! ## §7  The extension -/

section Extension
variable {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule (V2mPlus m hm) M)
  (P : Submodule (modeAlg A) M)

/-- Generalized weights below the quotient bottom lie in the kernel. -/
theorem low_mem_P (hbQ : FactorBottom A P ⊤ 1) {v : M} {μ : ℂ}
    (hv : v ∈ (L0 A).maxGenEigenspace μ) (hμ : μ.re < 1) : v ∈ P := by
  by_contra h
  have hw : FactorWeight A P ⊤ μ := fun ht => h (ht ⟨Submodule.mem_top, hv⟩)
  have := hbQ.2 μ hw
  simp only [Complex.one_re] at this
  linarith

/-- The E-telescope sum. -/
def Zop (w : M) : M :=
  ∑ n ∈ Finset.range m, ((-1 : ℂ) ^ n * ((2 * m - 2).choose n : ℂ)) •
    mode (A.YM (EP m hm)) (((2 * m - 2 : ℕ) : ℤ) - n) (mode (A.YM (EP m hm)) n w)

theorem Zop_mem_maxGen {w : M} {μ : ℂ} (hw : w ∈ (L0 A).maxGenEigenspace μ) :
    Zop m hm A w ∈ (L0 A).maxGenEigenspace μ := by
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  have h1 := mode_mem_maxGenEigenspace A (EP_mem_grading m hm) (n : ℤ) hw
  have h2 := mode_mem_maxGenEigenspace A (EP_mem_grading m hm)
    (((2 * m - 2 : ℕ) : ℤ) - n) h1
  have hn' : n < m := Finset.mem_range.mp hn
  have hc : μ + (((m : ℤ) - n - 1 : ℤ) : ℂ) +
      (((m : ℤ) - (((2 * m - 2 : ℕ) : ℤ) - n) - 1 : ℤ) : ℂ) = μ := by
    have : ((m : ℤ) - n - 1) + ((m : ℤ) - (((2 * m - 2 : ℕ) : ℤ) - n) - 1) = 0 := by omega
    have h' : ((((m : ℤ) - n - 1) + ((m : ℤ) - (((2 * m - 2 : ℕ) : ℤ) - n) - 1) : ℤ) : ℂ)
        = 0 := by rw [this]; simp
    push_cast at h' ⊢
    linear_combination h'
  rwa [hc] at h2

/-- `L(1)` kills the E-telescope of every generalized weight-one vector. -/
theorem L1_Zop_eq_zero (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m) (hP : IsAtom P)
    (hbP : FactorBottom A ⊥ P 0) (hbQ : FactorBottom A P ⊤ 1) {w : M}
    (hw : w ∈ (L0 A).maxGenEigenspace 1) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 (Zop m hm A w) = 0 := by
  apply lowering_telescope_core A m hm (EP_mem_grading m hm) (L1_E m hm) w
  · intro n
    have hL1w : mode (A.YM (V2mPlus m hm).conformalVector) 2 w ∈
        (L0 A).maxGenEigenspace 0 := by
      have h := mode_mem_maxGenEigenspace A (V2mPlus m hm).conformal_mem 2 hw
      have hc : (1 : ℂ) + ((2 - 2 - 1 : ℤ) : ℂ) = 0 := by norm_num
      rwa [hc] at h
    have hP' := low_mem_P m hm A P hbQ hL1w (by norm_num)
    have hT := kernel_zero_vacuumLike m hm A P hm2 hw1 hP hbP hP' hL1w
    exact nonnegative_modes_zero_of_translation_zero A hT _ n (by positivity)
  · have hEw : mode (A.YM (EP m hm)) (m : ℤ) w ∈ (L0 A).maxGenEigenspace 0 := by
      have h := mode_mem_maxGenEigenspace A (EP_mem_grading m hm) (m : ℤ) hw
      have hc : (1 : ℂ) + (((m : ℤ) - m - 1 : ℤ) : ℂ) = 0 := by push_cast; ring
      rwa [hc] at h
    have hP' := low_mem_P m hm A P hbQ hEw (by norm_num)
    have hT := kernel_zero_vacuumLike m hm A P hm2 hw1 hP hbP hP' hEw
    exact nonnegative_modes_zero_of_translation_zero A hT _ _ (by omega)

/-- In the quotient, a lift of the quotient bottom is a top vector. -/
theorem quotient_mem_Omega (hbQ : FactorBottom A P ⊤ 1) {w : M}
    (hw : w ∈ (L0 A).maxGenEigenspace 1) :
    (WeakModule.quotientMk A (ofR A P)).toLinearMap w ∈
      Omega (WeakModule.quotient A (ofR A P)) := by
  intro β v hv n hn
  have hq := (WeakModule.quotientMk A (ofR A P)).map_act v n w
  simp only [WeakModule.act_def] at hq
  rw [← hq]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply low_mem_P m hm A P hbQ (mode_mem_maxGenEigenspace A hv n hw)
  simp only [Complex.add_re, Complex.one_re, Complex.intCast_re]
  have : ((β - n - 1 : ℤ) : ℝ) < 0 := by exact_mod_cast (show β - n - 1 < 0 by omega)
  linarith

/-- **`L(1)` kills every weight-one eigenvector of the extension.** -/
theorem L1_kill (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m) (hP : IsAtom P)
    (hbP : FactorBottom A ⊥ P 0) (hbQ : FactorBottom A P ⊤ 1) {w : M} (hL : L0 A w = w) :
    mode (A.YM (V2mPlus m hm).conformalVector) 2 w = 0 := by
  have hwg : w ∈ (L0 A).maxGenEigenspace 1 := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hL
  obtain ⟨ξ₁, ξ₂, hunit⟩ := exists_unit_combination m hm hm2 hw1
  obtain ⟨s₁, hs₁⟩ := VOA.mk_surjective (V2mPlus m hm) ξ₁
  obtain ⟨s₂, hs₂⟩ := VOA.mk_surjective (V2mPlus m hm) ξ₂
  set w' := oLevW A 0 s₁ w with hw'def
  have hw'g : w' ∈ (L0 A).maxGenEigenspace 1 := oLevW_mem_maxGen A s₁ hwg
  set B := WeakModule.quotient A (ofR A P)
  set q : A.Hom B := WeakModule.quotientMk A (ofR A P)
  have hqΩ := quotient_mem_Omega m hm A P hbQ hwg
  have hq'Ω := quotient_mem_Omega m hm A P hbQ hw'g
  have hZq : q.toLinearMap (Zop m hm A w') =
      topEvaluation B (q.toLinearMap w') hq'Ω (zetaE m hm) := by
    rw [← telescopeE_eq m hm B hq'Ω, Zop, map_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [map_smul]
    congr 1
  have hshift : ∀ r, topEvaluation B (q.toLinearMap w') hq'Ω r =
      topEvaluation B (q.toLinearMap w) hqΩ (r * ξ₁) := by
    intro r
    obtain ⟨t, rfl⟩ := VOA.mk_surjective (V2mPlus m hm) r
    rw [topEvaluation_mk, ← hs₁, topEvaluation_mk_mul, topEvaluation_mk, hw'def,
      hom_oLevW A B q s₁ w]
  have hLq : L0 B (q.toLinearMap w) = q.toLinearMap w := by
    have h := q.map_act (V2mPlus m hm).conformalVector 1 w
    simp only [WeakModule.act_def] at h
    change mode (B.YM (V2mPlus m hm).conformalVector) 1 (q.toLinearMap w) = _
    rw [← h]
    change q.toLinearMap (L0 A w) = _
    rw [hL]
  have hqZ : q.toLinearMap (Zop m hm A w') = q.toLinearMap w := by
    rw [hZq, hshift, zhu_mul_comm m hm hm2, eq_sub_of_add_eq hunit, map_sub,
      topEvaluation_one, ← hs₂, topEvaluation_mk_mul]
    have hω : topEvaluation B (q.toLinearMap w) hqΩ
        (generator m hm 0 - algebraMap ℂ _ 1) = 0 := by
      rw [map_sub, topEvaluation_omega m hm B hqΩ, Algebra.algebraMap_eq_smul_one, map_smul,
        topEvaluation_one, one_smul, hLq, sub_self]
    rw [hω, map_zero, sub_zero]
  have hdiff : Zop m hm A w' - w ∈ P := by
    have h0 : q.toLinearMap (Zop m hm A w' - w) = 0 := by rw [map_sub, hqZ, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).mp h0
  have hZ : Zop m hm A w' = w := sub_eq_zero.mp
    (kernel_weightOne_eq_zero m hm A P hm2 hw1 hP hbP hdiff
      (Submodule.sub_mem _ (Zop_mem_maxGen m hm A hw'g) hwg))
  rw [← hZ]
  exact L1_Zop_eq_zero m hm A P hm2 hw1 hP hbP hbQ hw'g

/-- All lowering-by-one modes kill a weight-one eigenvector of the extension. -/
theorem lowering_one_kill (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m) (hP : IsAtom P)
    (hbP : FactorBottom A ⊥ P 0) (hbQ : FactorBottom A P ⊤ 1) {w : M} (hL : L0 A w = w) :
    ∀ (k : ℕ) (a : VP m hm), a ∈ (V2mPlus m hm).grading (k : ℤ) →
      mode (A.YM a) (k : ℤ) w = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro a ha
  have hc := L1_comm A ha ((k : ℤ) - 1) w
  have hzm : L0 A (mode (A.YM a) ((k : ℤ) - 1) w) = mode (A.YM a) ((k : ℤ) - 1) w := by
    have h := L0_commutator_weak A ha w ((k : ℤ) - 1)
    rw [hL] at h
    rw [h]
    simp
  rw [L1_kill m hm A P hm2 hw1 hP hbP hbQ hzm, L1_kill m hm A P hm2 hw1 hP hbP hbQ hL,
    map_zero, sub_zero] at hc
  have hgr : (V2mPlus m hm).L 1 a ∈ (V2mPlus m hm).grading ((k : ℤ) - 1) := by
    have h := (V2mPlus m hm).toPreVertexAlgebra.smul_mem_grading
      (V2mPlus m hm).conformal_mem ha 2
    have he : (V2mPlus m hm).L 1 a = (V2mPlus m hm).smul (V2mPlus m hm).conformalVector 2 a := by
      rw [VertexOperatorAlgebra.L_def]; rfl
    rw [he]
    have hk : (2 : ℤ) + k - 2 - 1 = (k : ℤ) - 1 := by ring
    rwa [hk] at h
  have hlow : mode (A.YM ((V2mPlus m hm).L 1 a)) ((k : ℤ) - 1) w = 0 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have hz : (V2mPlus m hm).L 1 a = 0 := by
        have := hgr
        rw [(V2mPlus m hm).positivity _ (by norm_num), Submodule.mem_bot] at this
        exact this
      rw [hz, map_zero]
      rfl
    · have h := ih (k - 1) (by omega) _ (by rwa [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 by omega])
      rwa [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 by omega] at h
  rw [hlow, add_zero, show (k : ℤ) - 1 + 1 = k by ring] at hc
  by_cases hk1 : k = 1
  · subst hk1
    have hz : a = 0 := by
      have := ha
      rw [show ((1 : ℕ) : ℤ) = 1 by norm_num, grading_one_eq_bot m hm hm2,
        Submodule.mem_bot] at this
      exact this
    rw [hz, map_zero]
    rfl
  · have hne : ((2 * (k : ℤ) - ((k : ℤ) - 1) - 2 : ℤ) : ℂ) ≠ 0 := by
      have : (2 * (k : ℤ) - ((k : ℤ) - 1) - 2 : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    exact (smul_eq_zero.mp hc.symm).resolve_left hne

/-- A weight-one eigenvector of the extension is a top vector. -/
theorem eigen_one_mem_Omega (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m) (hP : IsAtom P)
    (hbP : FactorBottom A ⊥ P 0) (hbQ : FactorBottom A P ⊤ 1) {w : M} (hL : L0 A w = w) :
    w ∈ Omega A := by
  have hwg : w ∈ (L0 A).maxGenEigenspace 1 := by
    apply Module.End.eigenspace_le_maxGenEigenspace
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hL
  intro β v hv n hn
  by_cases hβ : β < 0
  · rw [(V2mPlus m hm).positivity β hβ, Submodule.mem_bot] at hv
    subst hv
    simp
  by_cases hnβ : n = β
  · subst hnβ
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
    exact lowering_one_kill m hm A P hm2 hw1 hP hbP hbQ hL k v hv
  · have hg := mode_mem_maxGenEigenspace A hv n hwg
    have hre : (1 + ((β - n - 1 : ℤ) : ℂ)).re < 0 := by
      simp only [Complex.add_re, Complex.one_re, Complex.intCast_re]
      have : ((β - n - 1 : ℤ) : ℝ) < -1 := by exact_mod_cast (show β - n - 1 < -1 by omega)
      linarith
    have hP' := low_mem_P m hm A P hbQ hg (by linarith)
    exact kernel_generalized_below_bottom_eq_zero A P 0 hbP hP' hg (by simpa using hre)

end Extension

/-- **The vacuum-kernel / sign-quotient ordered pair splits.** -/
theorem pairSplitting_vacuum_sign (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m) :
    PairSplitting m hm (.inr 0) (.inr 1) := by
  intro M _ _ A P hP hQ hb ht
  have hbP : FactorBottom A ⊥ P 0 := by simpa [weight] using hb
  have hbQ : FactorBottom A P ⊤ 1 := by simpa [weight] using ht
  apply (exists_cyclic_lift_iff_complement A P hQ 1 hbQ).mp
  obtain ⟨x, hx, hxP⟩ := exists_generalized_lift_of_factorBottom A P 1 hbQ
  -- an honest eigenvector lift
  classical
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  set f := L0 A - (1 : ℂ) • (1 : Module.End ℂ M)
  have hfmem : ∀ j : ℕ, (f ^ j) x ∈ (L0 A).maxGenEigenspace 1 := by
    intro j
    apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
    refine ⟨k, ?_⟩
    rw [← Module.End.mul_apply, ← pow_add, add_comm, pow_add, Module.End.mul_apply, hk,
      map_zero]
  have hex : ∃ j : ℕ, (f ^ (j + 1)) x ∈ P := ⟨k, by
    rw [show k + 1 = 1 + k by ring, pow_add, Module.End.mul_apply, hk, map_zero]
    exact Submodule.zero_mem _⟩
  let j := Nat.find hex
  have hj : (f ^ (j + 1)) x ∈ P := Nat.find_spec hex
  have hjP : (f ^ j) x ∉ P := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, pow_zero]; exact hxP
    · have := Nat.find_min hex (show j - 1 < j by omega)
      rwa [Nat.sub_add_cancel hj0] at this
  have hfe : f ((f ^ j) x) = (f ^ (j + 1)) x := by
    rw [pow_succ', Module.End.mul_apply]
  have hfz : f ((f ^ j) x) = 0 := by
    apply kernel_weightOne_eq_zero m hm A P hm2 hw1 hP hbP
    · rw [hfe]; exact hj
    · rw [hfe]; exact hfmem (j + 1)
  set x' := (f ^ j) x
  have hL : L0 A x' = x' := by
    have h := hfz
    change L0 A x' - (1 : ℂ) • x' = 0 at h
    rw [one_smul] at h
    exact sub_eq_zero.mp h
  have hx'g : x' ∈ (L0 A).maxGenEigenspace 1 := hfmem j
  have hx'Ω := eigen_one_mem_Omega m hm A P hm2 hw1 hP hbP hbQ hL
  refine ⟨x', hx'g, hjP, ?_⟩
  obtain ⟨y, hy, hy0⟩ := SetLike.not_le_iff_exists.mp hbP.1
  have hy0' : y ≠ 0 := fun h => hy0 (by rw [h]; exact Submodule.zero_mem _)
  rw [disjoint_cyclic_iff_no_mode_word A P hP hy.1 hy0' x',
    no_mode_word_iff_not_mem_degreeSpan (V2mPlus_c2Cofinite m hm) A hx'g (-1)
      (by
        have h2 : (1 : ℂ) + ((-1 : ℤ) : ℂ) = 0 := by norm_num
        rw [h2]; exact hy.2),
    degreeSpan_neg_one_eq_bot A hx'Ω 1 (by rw [one_smul]; exact hL)]
  intro h
  exact hy0' ((Submodule.mem_bot ℂ).mp h)

/-- **Both vacuum/sign orientations split** (only the sign row at weight one). -/
theorem vacuum_sign_both (hm2 : 2 ≤ m) (hw1 : OnlySignWeightOne m) :
    PairSplitting m hm (.inr 0) (.inr 1) ∧ PairSplitting m hm (.inr 1) (.inr 0) :=
  ⟨pairSplitting_vacuum_sign m hm hm2 hw1, pairSplitting_sign_vacuum m hm hm2 hw1⟩

end VOA.Classification.COne.PlusRatSign
