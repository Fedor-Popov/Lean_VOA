/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusC2OneProof
import VOA.Classification.COne.PlusC2Excess
import VOA.Examples.TripletW2Nilpotent

/-!
# The Heisenberg orbifold `M(1)⁺` as a sub-VOA of `V_{2m}`

Notation of `PlusC2Sector.lean`.  `M(1)⁺ ⊂ V_{2m}` is the charge-`0`, `θ`-fixed part:
`m1Carrier = range(q ↦ q ⊗ e⁰) ⊓ V⁺`.  It is closed under all products and gradings, so it is a
`VOASubalgebra` (`m1Sub`) and hence a vertex operator algebra `M1P m hm` in its own right, with its
own `C₂`-space `O₂(M1P)` and Poisson algebra `A₂(M1P)` (a commutative `ℂ`-algebra).

## Main results

* `mem_m1Carrier_iff` — `M(1)⁺ = {q ⊗ e⁰ : σq = q}`.
* `m1Sub`, `M1P` — the sub-VOA and its VOA.
* `phi` (`Φ_w = ` the coefficient of `h(−1)^w ⊗ e⁰`) and `phi_O₂` — `Φ_w` vanishes on `O₂(M1P)`
  (every `u₍ₙ₎v` with `n ≤ −2` has excess `≥ 1`, `PlusC2Excess.lean`).
* `phi_omegaPow` — `Φ_{2k}(ω₍₋₁₎^k 𝟙) = 2^{−k}` (leading term of the normal-ordered product).
* `m1PlusC2Line_of_M1PLine` — the residual `M1PlusC2Line` of `PlusC2Zero.lean` follows from the
  intrinsic statement `M1PLine` about the VOA `M1P` (for large `w`, a weight-`w` vector of `M(1)⁺`
  with `Φ_w = 0` lies in `O₂(M1P)`).
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN VOA.Moonshine LatMod
  MvPolynomial VOA.TripletNilp

namespace PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## §1  The carrier -/

/-- The charge-`0` sector `M(1) ⊗ e⁰`. -/
noncomputable abbrev sec0Sub : Submodule ℂ (LatModuleGen (latP m)) :=
  LinearMap.range (stateMap (latP m) 0)

/-- The carrier of `M(1)⁺`: charge `0` and `θ`-fixed. -/
noncomputable def m1Carrier : Submodule ℂ (LatModuleGen (latP m)) := sec0Sub m ⊓ VP m hm

theorem coordEα_latStateGen_zero (q : FockN (rank (latP m))) :
    coordEα (latP m) 0 (latStateGen (latP m) q 0) = q := by
  rw [latStateGen, coordEα_apply, if_pos rfl]

theorem mem_m1Carrier_iff (v : LatModuleGen (latP m)) :
    v ∈ m1Carrier m hm ↔ ∃ q, sigmaN (rank (latP m)) q = q ∧ v = latStateGen (latP m) q 0 := by
  constructor
  · rintro ⟨⟨q, rfl⟩, hθ⟩
    rw [SetLike.mem_coe, mem_VP_iff, stateMap_apply, thetaLat_latStateGen, neg_zero] at hθ
    refine ⟨(1 / 2 : ℂ) • (q + sigmaN _ q), ?_, ?_⟩
    · rw [map_smul, map_add, sigmaN_sigmaN, add_comm]
    · rw [stateMap_apply, latStateGen_csmul, latStateGen_add_boson, hθ, ← two_smul ℂ, smul_smul]
      norm_num
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨q, rfl⟩, ?_⟩
    rw [SetLike.mem_coe, mem_VP_iff, thetaLat_latStateGen, neg_zero, hq]

theorem V2m_grading_eq : (V2m m hm).grading = gradingLatGen (latP m) := rfl

theorem latStateGen_mem_grading {w : ℕ} {q : FockN (rank (latP m))}
    (hq : q ∈ gradingWN (rank (latP m)) w) : latStateGen (latP m) q 0 ∈ (V2m m hm).grading w := by
  rw [V2m_grading_eq]
  have h := bigradα_le_gradingLatGen (latP m) (w : ℤ) 0
  rw [halfNorm_zero, add_zero] at h
  refine h ⟨q, ?_, rfl⟩
  rw [gradingZN_of_nonneg (Int.natCast_nonneg w), Int.toNat_natCast]
  exact hq

/-- The charge-`0` sector is graded. -/
theorem piHom_sec0 (n : ℤ) (q : FockN (rank (latP m))) :
    piHom (V2m m hm) n (latStateGen (latP m) q 0) ∈ sec0Sub m := by
  have hq : q ∈ (⊤ : Submodule ℂ (FockN (rank (latP m)))) := Submodule.mem_top
  rw [← gradingWN_iSup_eq_top] at hq
  induction hq using Submodule.iSup_induction' with
  | mem w x hx =>
    by_cases hw : (w : ℤ) = n
    · rw [piHom_of_mem _ (hw ▸ latStateGen_mem_grading m hm hx)]
      exact ⟨x, rfl⟩
    · rw [piHom_of_mem_ne _ hw (latStateGen_mem_grading m hm hx)]
      exact Submodule.zero_mem _
  | zero =>
    rw [show latStateGen (latP m) (0 : FockN (rank (latP m))) 0 = 0 by simp [latStateGen], map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [latStateGen_add_boson, map_add]
    exact Submodule.add_mem _ hx hy

/-! ## §2  The sub-VOA -/

/-- **`M(1)⁺` is a sub-VOA of `V_{2m}`.** -/
noncomputable def m1Sub : VOASubalgebra (V2m m hm) where
  carrier := m1Carrier m hm
  vacuum_mem := ⟨⟨vacuumN _, rfl⟩, (orbifold (Subgroup.zpowers (thetaV2m m hm))).vacuum_mem⟩
  conformal_mem := ⟨⟨ωN _ 1, rfl⟩, (orbifold (Subgroup.zpowers (thetaV2m m hm))).conformal_mem⟩
  smul_mem := by
    rintro u ⟨⟨p, rfl⟩, hu⟩ n v ⟨⟨q, rfl⟩, hv⟩
    refine ⟨?_, (orbifold (Subgroup.zpowers (thetaV2m m hm))).smul_mem _ hu n _ hv⟩
    obtain ⟨r, hr⟩ := smul_sector_zero m hm p q n
    exact ⟨r, by rw [stateMap_apply, stateMap_apply, stateMap_apply, hr]⟩
  graded := by
    rintro n v ⟨⟨q, rfl⟩, hv⟩
    exact ⟨piHom_sec0 m hm n q, (orbifold (Subgroup.zpowers (thetaV2m m hm))).graded n _ hv⟩

/-- **The vertex operator algebra `M(1)⁺`.** -/
noncomputable abbrev M1P : VertexOperatorAlgebra (m1Sub m hm).carrier := (m1Sub m hm).toVOA

theorem M1P_smul_coe (u v : (m1Sub m hm).carrier) (n : ℤ) :
    (((M1P m hm).smul u n v : (m1Sub m hm).carrier) : LatModuleGen (latP m)) =
      (V2m m hm).smul u n v := by
  rw [PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def]
  exact VOASubalgebra.mode_YS_coe _ u n v

theorem M1P_mem_grading_iff (v : (m1Sub m hm).carrier) (n : ℤ) :
    v ∈ (M1P m hm).grading n ↔ (v : LatModuleGen (latP m)) ∈ (V2m m hm).grading n := Iff.rfl

theorem exists_fock (v : (m1Sub m hm).carrier) :
    ∃ q, sigmaN (rank (latP m)) q = q ∧ (v : LatModuleGen (latP m)) = latStateGen (latP m) q 0 :=
  (mem_m1Carrier_iff m hm v).mp v.2

/-! ## §3  The functional `Φ_w` and `O₂(M1P)` -/

/-- `Φ_w(x)`: the coefficient of `h(−1)^w ⊗ e⁰` in `x`. -/
noncomputable def phi (w : ℕ) (x : LatModuleGen (latP m)) : ℂ :=
  topCoeff m w (coordEα (latP m) 0 x)

theorem phi_add (w : ℕ) (x y : LatModuleGen (latP m)) : phi m w (x + y) = phi m w x + phi m w y := by
  simp [phi, topCoeff, map_add]

theorem phi_smul (w : ℕ) (c : ℂ) (x : LatModuleGen (latP m)) : phi m w (c • x) = c * phi m w x := by
  simp [phi, topCoeff, map_smul]

theorem phi_sub (w : ℕ) (x y : LatModuleGen (latP m)) : phi m w (x - y) = phi m w x - phi m w y := by
  simp [phi, topCoeff, map_sub]

theorem phi_latStateGen (w : ℕ) (q : FockN (rank (latP m))) :
    phi m w (latStateGen (latP m) q 0) = topCoeff m w q := by
  rw [phi, coordEα_latStateGen_zero]

/-- `Φ_w` vanishes on the excess-`≥ 1` part. -/
theorem topCoeff_ExF_one (w : ℕ) {F : FockN (rank (latP m))} (hF : F ∈ ExF (latP m) 1) :
    topCoeff m w F = 0 := by
  refine Submodule.span_induction (p := fun F _ => topCoeff m w F = 0) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨s, hs, rfl⟩
    rw [topCoeff, coeff_monomial, if_neg]
    rintro rfl
    rw [monoWt_single, monoDeg_single] at hs
    simp at hs
  · simp [topCoeff]
  · intro x y _ _ hx hy; simp only [topCoeff, coeff_add] at hx hy ⊢; rw [hx, hy, add_zero]
  · intro c x _ hx; simp only [topCoeff, coeff_smul, smul_eq_mul] at hx ⊢; rw [hx, mul_zero]

theorem phi_ExFil_one (w : ℕ) {x : LatModuleGen (latP m)} (hx : x ∈ ExFil (latP m) 1 0) :
    phi m w x = 0 := by
  obtain ⟨F, hF, rfl⟩ := hx
  rw [stateMap_apply, phi_latStateGen]
  exact topCoeff_ExF_one m w hF

/-- Every `u₍ₙ₎v` (`n ≤ −2`) of two charge-`0` states has excess `≥ 1`. -/
theorem smul_neg_two_mem_ExFil (p q : FockN (rank (latP m))) {n : ℤ} (hn : n ≤ -2) :
    (V2m m hm).smul (latStateGen (latP m) p 0) n (latStateGen (latP m) q 0) ∈ ExFil (latP m) 1 0 := by
  have hq : latStateGen (latP m) q 0 ∈ ExFil (latP m) 0 0 := ⟨q, by rw [ExF_zero]; trivial, rfl⟩
  set S : Submodule ℂ (FockN (rank (latP m))) :=
    { carrier := {p | (V2m m hm).smul (latStateGen (latP m) p 0) n (latStateGen (latP m) q 0) ∈
        ExFil (latP m) 1 0}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [latStateGen_add_boson, PreVertexAlgebra.smul_add_left]
        exact Submodule.add_mem _ hx hy
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [show latStateGen (latP m) (0 : FockN (rank (latP m))) 0 = 0 by simp [latStateGen],
          PreVertexAlgebra.smul_zero_left]
        exact Submodule.zero_mem _
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [latStateGen_csmul, PreVertexAlgebra.smul_smul_left]
        exact Submodule.smul_mem _ _ hx } with hS
  suffices h : (⊤ : Submodule ℂ (FockN (rank (latP m)))) ≤ S from h Submodule.mem_top
  refine (gradingWN_iSup_eq_top _).ge.trans (iSup_le fun w => ?_)
  refine (gradingWN_le_span_words _ w).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨l, -, rfl⟩
  have h := word_smul_le_neg_two_mem_ExFil (latP m) (latP_even m) (latP_posDef m hm) l hn hq
  rw [wordStateLatGen_eq] at h
  simpa using h

/-- **`Φ_w` vanishes on `O₂(M(1)⁺)`.** -/
theorem phi_O₂ (w : ℕ) {x : (m1Sub m hm).carrier} (hx : x ∈ O₂ (M1P m hm)) :
    phi m w (x : LatModuleGen (latP m)) = 0 := by
  rw [O₂] at hx
  induction hx using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨p, -, hp⟩ := exists_fock m hm u
    obtain ⟨q, -, hq⟩ := exists_fock m hm v
    rw [M1P_smul_coe, hp, hq]
    exact phi_ExFil_one m w (smul_neg_two_mem_ExFil m hm p q le_rfl)
  | zero => simp [phi, topCoeff]
  | add x y _ _ hx hy =>
    rw [Submodule.coe_add, phi_add, hx, hy, add_zero]
  | smul c x _ hx =>
    rw [Submodule.coe_smul, phi_smul, hx, mul_zero]

/-! ## §4  The conformal vector and its powers -/

/-- The conformal vector of `M1P`. -/
noncomputable abbrev ωM : (m1Sub m hm).carrier := (M1P m hm).conformalVector

theorem a0_unique (a : Fin (rank (latP m))) : a = a0 m := a_eq_a0 m a

/-- The rank-one conformal vector: `ω = ½·h(−1)² 𝟙 = ½·(word [(0,a₀),(0,a₀)])`. -/
theorem omegaLatGen_eq :
    ((ωM m hm : (m1Sub m hm).carrier) : LatModuleGen (latP m)) =
      (1 / 2 : ℂ) • wordStateLatGen (latP m) [((0 : ℕ), a0 m), ((0 : ℕ), a0 m)] 0 := by
  change omegaLatGen (latP m) = _
  rw [omegaLatGen, wordStateLatGen_eq, ωN]
  rw [Finset.sum_eq_single (a0 m) (fun b _ hb => absurd (a0_unique m b) hb)
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [ωNa, oscN_neg _ _ _ (by norm_num : (-1 : ℤ) < 0)]
  simp only [mulXN_apply, wordStateN_cons, wordStateN_nil, vacuumN, mkEα_apply, mul_one,
    TensorProduct.smul_tmul']
  norm_num

/-- `ω₍₋₁₎(p ⊗ e⁰) = (½ h(−1)² p + R) ⊗ e⁰` with `R` of lower degree. -/
theorem omega_smul_neg_one (p : FockN (rank (latP m))) {e : ℤ} (hp : p ∈ FilF (latP m) e) :
    ∃ R ∈ FilF (latP m) (e + 1),
      (V2m m hm).smul (ωM m hm : LatModuleGen (latP m)) (-1) (latStateGen (latP m) p 0) =
        latStateGen (latP m) ((1 / 2 : ℂ) • (X ((0 : ℕ), a0 m) * (X ((0 : ℕ), a0 m) * p)) + R) 0 := by
  have h := word_smul_neg_one_sub_mem_Fil (latP m) (latP_even m) (latP_posDef m hm)
    [((0 : ℕ), a0 m), ((0 : ℕ), a0 m)] e 0 p hp
  obtain ⟨R, hR, hR'⟩ := h
  refine ⟨(1 / 2 : ℂ) • R, Submodule.smul_mem _ _ (FilF_mono (latP m) (by simp; omega) hR), ?_⟩
  rw [omegaLatGen_eq, PreVertexAlgebra.smul_smul_left]
  rw [stateMap_apply] at hR'
  have : (V2m m hm).smul (wordStateLatGen (latP m) [((0 : ℕ), a0 m), ((0 : ℕ), a0 m)] 0) (-1)
      (latStateGen (latP m) p 0) = latStateGen (latP m) R 0 +
        latStateGen (latP m) (wordStateN [((0 : ℕ), a0 m), ((0 : ℕ), a0 m)] * p) 0 := by
    rw [hR']; unfold V2m; abel
  rw [this]
  simp only [latStateGen_add_boson, latStateGen_csmul, wordStateN_cons, wordStateN_nil, mul_one,
    mul_assoc]
  module

theorem topCoeff_FilF (w : ℕ) {e : ℤ} (hw : e < w) {F : FockN (rank (latP m))}
    (hF : F ∈ FilF (latP m) e) : topCoeff m w F = 0 := by
  refine Submodule.span_induction (p := fun F _ => topCoeff m w F = 0) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨s, hs, rfl⟩
    rw [topCoeff, coeff_monomial, if_neg]
    rintro rfl
    rw [Finsupp.sum_single_index rfl] at hs
    omega
  · simp [topCoeff]
  · intro x y _ _ hx hy; simp only [topCoeff, coeff_add] at hx hy ⊢; rw [hx, hy, add_zero]
  · intro c x _ hx; simp only [topCoeff, coeff_smul, smul_eq_mul] at hx ⊢; rw [hx, mul_zero]

/-- **The powers of `ω`**: `ω₍₋₁₎^k 𝟙 = P_k ⊗ e⁰` with `deg P_k ≤ 2k` and
`Φ_{2k} = 2^{−k}`. -/
theorem omegaPow_spec (k : ℕ) :
    ∃ P ∈ FilF (latP m) (2 * k),
      ((pMulPow (M1P m hm) (ωM m hm) k : (m1Sub m hm).carrier) : LatModuleGen (latP m)) =
        latStateGen (latP m) P 0 ∧ topCoeff m (2 * k) P = (1 / 2 : ℂ) ^ k := by
  induction k with
  | zero =>
    refine ⟨1, monomial_mem_FilF (latP m) 0 1 (by simp), rfl, ?_⟩
    simp [topCoeff]
  | succ k ih =>
    obtain ⟨P, hP, hPe, hPc⟩ := ih
    obtain ⟨R, hR, hRe⟩ := omega_smul_neg_one m hm P hP
    refine ⟨(1 / 2 : ℂ) • (X ((0 : ℕ), a0 m) * (X ((0 : ℕ), a0 m) * P)) + R, ?_, ?_, ?_⟩
    · refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (FilF_mono (latP m) (by omega) hR)
      have := X_mul_mem_FilF (latP m) ((0 : ℕ), a0 m) (X_mul_mem_FilF (latP m) ((0 : ℕ), a0 m) hP)
      refine FilF_mono (latP m) (by push_cast; omega) this
    · rw [pMulPow_succ, M1P_smul_coe, hPe, hRe]
    · have h1 : topCoeff m (2 * (k + 1)) R = 0 :=
        topCoeff_FilF m _ (by push_cast; omega) hR
      have h2 : topCoeff m (2 * (k + 1)) ((1 / 2 : ℂ) • (X ((0 : ℕ), a0 m) * (X ((0 : ℕ), a0 m) * P)) + R) =
          (1 / 2 : ℂ) * topCoeff m (2 * (k + 1)) (X ((0 : ℕ), a0 m) * (X ((0 : ℕ), a0 m) * P)) +
            topCoeff m (2 * (k + 1)) R := by
        simp [topCoeff]
      rw [h2, h1, add_zero, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, topCoeff_X_mul,
        if_pos rfl, topCoeff_X_mul, if_pos rfl, hPc, pow_succ]
      ring

/-- `Φ_{2k}(ω₍₋₁₎^k 𝟙) = 2^{−k} ≠ 0`. -/
theorem phi_omegaPow (k : ℕ) :
    phi m (2 * k) ((pMulPow (M1P m hm) (ωM m hm) k : (m1Sub m hm).carrier) : LatModuleGen (latP m)) =
      (1 / 2 : ℂ) ^ k := by
  obtain ⟨P, -, hPe, hPc⟩ := omegaPow_spec m hm k
  rw [hPe, phi_latStateGen, hPc]

/-! ## §5  The intrinsic residual and the reduction -/

/-- **The intrinsic line property of `M(1)⁺`** (TRUE; see `M1PlusC2Line`): for all large `w`, a
weight-`w` vector of the VOA `M1P` with `Φ_w = 0` lies in `O₂(M1P)`. -/
def M1PLine : Prop :=
  ∃ N : ℕ, ∀ w : ℕ, N ≤ w → ∀ v : (m1Sub m hm).carrier, v ∈ (M1P m hm).grading w →
    phi m w (v : LatModuleGen (latP m)) = 0 → v ∈ O₂ (M1P m hm)

/-- The inclusion `M(1)⁺ ↪ V⁺`. -/
noncomputable def incl : (m1Sub m hm).carrier →ₗ[ℂ] VP m hm :=
  Submodule.inclusion (show m1Carrier m hm ≤ VP m hm from inf_le_right)

theorem incl_coe (v : (m1Sub m hm).carrier) :
    ((incl m hm v : VP m hm) : LatModuleGen (latP m)) = v := rfl

theorem incl_eq_PP (v : (m1Sub m hm).carrier) {q : FockN (rank (latP m))}
    (hq : (v : LatModuleGen (latP m)) = latStateGen (latP m) q 0) :
    incl m hm v = PP m hm (latStateGen (latP m) q 0) := by
  rw [← hq]
  exact (PP_of_mem m hm (incl m hm v)).symm

/-- `O₂(M(1)⁺)` lands in the internal `C₂(M(1)⁺) ⊆ V⁺`. -/
theorem incl_O₂_le : (O₂ (M1P m hm)).map (incl m hm) ≤ c2M1Plus m hm := by
  rw [O₂, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨u, v, rfl⟩, rfl⟩
  obtain ⟨p, -, hp⟩ := exists_fock m hm u
  obtain ⟨q, -, hq⟩ := exists_fock m hm v
  refine Submodule.subset_span ⟨p, q, ?_⟩
  apply Subtype.ext
  rw [incl_coe, M1P_smul_coe, V2mPlus_smul_coe, ← incl_eq_PP m hm u hp, ← incl_eq_PP m hm v hq,
    incl_coe, incl_coe]

/-- `σ(x^t) = (−1)^{deg t}·x^t`. -/
theorem sigmaN_monomial' (t : (ℕ × Fin (rank (latP m))) →₀ ℕ) (c : ℂ) :
    sigmaN (rank (latP m)) (monomial t c) = ((-1 : ℂ) ^ (t.sum fun _ k => k)) • monomial t c := by
  have hX : ∀ (x : ℕ × Fin (rank (latP m))) (n : ℕ),
      (-(X x : FockN (rank (latP m)))) ^ n = MvPolynomial.C ((-1 : ℂ) ^ n) * X x ^ n := by
    intro x n
    rw [show -(X x : FockN (rank (latP m))) = MvPolynomial.C (-1 : ℂ) * X x by simp, mul_pow, ← C_pow]
  rw [sigmaN_apply, sigmaAlg, aeval_monomial, algebraMap_eq, Finsupp.prod]
  simp_rw [hX]
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, monomial_eq,
    Finsupp.prod, smul_eq_C_mul, Finsupp.sum]
  ring

/-- `σ` acts on the coefficient of a monomial by the sign `(−1)^deg`. -/
theorem coeff_sigmaN (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (q : FockN (rank (latP m))) :
    coeff s (sigmaN (rank (latP m)) q) = (-1 : ℂ) ^ (s.sum fun _ k => k) * coeff s q := by
  induction q using MvPolynomial.induction_on' with
  | monomial t c =>
    rw [sigmaN_monomial', coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem topCoeff_sigmaN (w : ℕ) (q : FockN (rank (latP m))) :
    topCoeff m w (sigmaN (rank (latP m)) q) = (-1 : ℂ) ^ w * topCoeff m w q := by
  rw [topCoeff, coeff_sigmaN, Finsupp.sum_single_index rfl, topCoeff]

/-- **`M1PlusC2Line` from the intrinsic `M1PLine`.** -/
theorem m1PlusC2Line_of_M1PLine (h : M1PLine m hm) : M1PlusC2Line m hm := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun w hw q hq hev => ?_⟩
  set q' : FockN (rank (latP m)) := (1 / 2 : ℂ) • (q + sigmaN _ q) with hq'
  have hσ : sigmaN (rank (latP m)) q' = q' := by
    rw [hq', map_smul, map_add, sigmaN_sigmaN, add_comm]
  set v : (m1Sub m hm).carrier := ⟨latStateGen (latP m) q' 0, (mem_m1Carrier_iff m hm _).mpr ⟨q', hσ, rfl⟩⟩
  have hq'w : q' ∈ gradingWN (rank (latP m)) w :=
    Submodule.smul_mem _ _ (Submodule.add_mem _ hq (sigmaN_mem_gradingWN _ hq))
  have hvw : v ∈ (M1P m hm).grading w := latStateGen_mem_grading m hm hq'w
  have hphi : phi m w (v : LatModuleGen (latP m)) = 0 := by
    change phi m w (latStateGen (latP m) q' 0) = 0
    rw [phi_latStateGen, hq']
    have hlin : topCoeff m w ((1 / 2 : ℂ) • (q + sigmaN _ q)) =
        (1 / 2 : ℂ) * (topCoeff m w q + topCoeff m w (sigmaN _ q)) := by
      simp [topCoeff]; ring
    rw [hlin, topCoeff_sigmaN]
    rcases Nat.even_or_odd w with he | ho
    · rw [hev he, Even.neg_one_pow he]; ring
    · rw [Odd.neg_one_pow ho]; ring
  have hO := hN w hw v hvw hphi
  have hmem := incl_O₂_le m hm ⟨v, hO, rfl⟩
  have heq : incl m hm v = PP m hm (latStateGen (latP m) q 0) := by
    apply Subtype.ext
    rw [incl_coe, PP_coe, thetaLat_latStateGen, neg_zero, ← latStateGen_add_boson,
      ← latStateGen_csmul]
  rwa [heq] at hmem

end PlusC2

end VOA.Classification.COne
