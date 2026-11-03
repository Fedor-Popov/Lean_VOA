import VOA.Classification.COne.OrbZhuBound

/-!
# OrbZhu (4): the even residual `TetraSixteenTruncation`

`ω̄² v̄ ∈ ℂ · ω̄¹⁰ 𝟙̄` in `R(V₂^{A₄})`, where `v = T I₄`.

Ingredients:
* the certified weight-20 Dong–Jiang relation for the explicit weight-16 state
  `X = J₍₋₉₎J + 27 E₍₋₉₎E` (`OrbC2h.cubicFiniteVirasoroCertificates`), transported to
  `V₂^{A₄}` along `plus_cubic_tetra_iso`: `c ω̄¹⁰ 𝟙̄ + b ω̄² X̄ = 0`, `b = djB20 ≠ 0`;
* `W₁₆ ⊆ ℂ v + Σ L(-m) W₁₆₋ₘ` (`grading_sixteen_le`), using `T₂ r² = 0` (a primary that is a
  lower descendant vanishes in the unitary `V₂`);
* `X` is NOT a lower descendant (`fixedSixteen_not_lowerDesc`): its `e^{2β}`-coordinate is `27`
  (`OrbC2e.coord_weightSixteen`), while lower descendants of weight 16 have none (the charge-`2β`
  sector of `V₈` starts in weight 16 and `L(n)` preserves charge sectors).
Hence `X ≡ c v (mod lower descendants)` with `c ≠ 0`, so `v̄ ∈ span{X̄, ω̄⁸𝟙̄}`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbZhu

open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b OrbC2c OrbC2e OrbC2f OrbC2g OrbC2h PlusC2
  VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN

/-- `tetra ≅ A₄` is finite (the same instance as in `OrbZhuGraded`). -/
noncomputable local instance tetraFintypeZ' : Fintype tetra :=
  @Fintype.ofFinite _ (Finite.of_equiv (alternatingGroup (Fin 4)) tetra_group.some.symm.toEquiv)

/-! ## Lower descendants along homomorphisms -/

section Hom
universe u v
variable {𝒱 : Type u} {𝒲 : Type v} [AddCommGroup 𝒱] [Module ℂ 𝒱] [AddCommGroup 𝒲]
  [Module ℂ 𝒲] {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}

theorem map_lowerDesc_le {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (N : ℤ) :
    (lowerDesc V N).map φ ≤ lowerDesc T N := by
  rw [lowerDesc, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨m, y, hy, rfl⟩, rfl⟩
  exact Submodule.subset_span
    ⟨m, φ y, ConverseUniverse.voaHom_map_grading hφ hω hy, ConverseUniverse.voaHom_map_L hφ hω _ _⟩

end Hom

/-! ## Charge sectors of `V₈ = V_{√8ℤ}` -/

local notation "V8" => V2m 4 four_ge_one

theorem coordEα_mkEα_ne {L : IntegralLattice} {α β : L.carrier} (h : α ≠ β)
    (p : FockN (rank L)) : coordEα L β (mkEα L α p) = 0 := by
  rw [mkEα_apply, coordEα_apply, if_neg (Ne.symm h)]

theorem coordEα_mkEα_self {L : IntegralLattice} (β : L.carrier) (p : FockN (rank L)) :
    coordEα L β (mkEα L β p) = p := by
  rw [mkEα_apply, coordEα_apply, if_pos rfl]

/-- The sum of the charge sectors other than `β`. -/
def otherSec (L : IntegralLattice) (β : L.carrier) : Submodule ℂ (LatModuleGen L) :=
  ⨆ (α : L.carrier) (_ : α ≠ β), chargeSec L α

theorem coordEα_otherSec {L : IntegralLattice} (β : L.carrier) {x : LatModuleGen L}
    (hx : x ∈ otherSec L β) : coordEα L β x = 0 := by
  have : otherSec L β ≤ LinearMap.ker (coordEα L β) := by
    refine iSup₂_le fun α hα => ?_
    rintro _ ⟨p, rfl⟩
    exact coordEα_mkEα_ne hα p
  exact this hx

theorem sub_mkEα_coordEα_mem (L : IntegralLattice) (β : L.carrier) (x : LatModuleGen L) :
    x - mkEα L β (coordEα L β x) ∈ otherSec L β := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p f =>
    have hf : f = f.erase β + Finsupp.single β (f β) := (Finsupp.erase_add_single β f).symm
    have hc : coordEα L β (p ⊗ₜ[ℂ] f) = f β • p := by
      simp [coordEα]
    have hmk : mkEα L β (f β • p) = p ⊗ₜ[ℂ] Finsupp.single β (f β) := by
      rw [mkEα_apply, eGen, TensorProduct.smul_tmul, Finsupp.smul_single, smul_eq_mul, mul_one]
    have key : p ⊗ₜ[ℂ] f - p ⊗ₜ[ℂ] Finsupp.single β (f β) = p ⊗ₜ[ℂ] (f.erase β) := by
      rw [← TensorProduct.tmul_sub, sub_eq_of_eq_add hf]
    rw [hc, hmk, key]
    rw [← Finsupp.sum_single (f.erase β), Finsupp.sum, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    have hne : α ≠ β := by
      intro h; subst h; simp at hα
    apply (le_iSup₂ (f := fun (α : L.carrier) (_ : α ≠ β) => chargeSec L α) α hne)
    refine ⟨(f.erase β) α • p, ?_⟩
    rw [mkEα_apply, eGen, TensorProduct.smul_tmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  | add x y hx hy =>
    have e : x + y - mkEα L β (coordEα L β (x + y)) =
        (x - mkEα L β (coordEα L β x)) + (y - mkEα L β (coordEα L β y)) := by
      rw [map_add, map_add]; abel
    rw [e]; exact Submodule.add_mem _ hx hy

theorem V8_L_mem_chargeSec (α : (latP 4).carrier) (n : ℤ) {x : LatModuleGen (latP 4)}
    (hx : x ∈ chargeSec (latP 4) α) : (V8).L n x ∈ chargeSec (latP 4) α := by
  have h := YfullGen_shiftsCharge (latP 4) (latP_even 4) (latP_posDef 4 four_ge_one) 0
    (omegaLatGen_mem_chargeSec (latP 4)) α (-(n + 1) - 1) x hx
  rw [zero_add] at h
  exact h

theorem V8_L_mem_otherSec (β : (latP 4).carrier) (n : ℤ) {x : LatModuleGen (latP 4)}
    (hx : x ∈ otherSec (latP 4) β) : (V8).L n x ∈ otherSec (latP 4) β := by
  have : otherSec (latP 4) β ≤ (otherSec (latP 4) β).comap ((V8).L n) := by
    refine iSup₂_le fun α hα => ?_
    intro y hy
    exact (le_iSup₂ (f := fun (α : (latP 4).carrier) (_ : α ≠ β) => chargeSec (latP 4) α) α hα)
      (V8_L_mem_chargeSec α n hy)
  exact this hx

theorem coordEα_V8_L (β : (latP 4).carrier) (n : ℤ) (x : LatModuleGen (latP 4)) :
    coordEα (latP 4) β ((V8).L n x) =
      coordEα (latP 4) β ((V8).L n (mkEα (latP 4) β (coordEα (latP 4) β x))) := by
  have h := V8_L_mem_otherSec β n (sub_mkEα_coordEα_mem (latP 4) β x)
  have h0 := coordEα_otherSec β h
  rwa [map_sub, map_sub, sub_eq_zero] at h0

theorem halfNorm_two : LatGen.halfNorm (latP 4) ((2 : ℤ) : (latP 4).carrier) = 16 := by
  simp only [LatGen.halfNorm]
  rw [latP_form]
  norm_num

theorem coordEα_two_of_lt {k : ℤ} (hk : k < 16) {x : LatModuleGen (latP 4)}
    (hx : x ∈ (V8).grading k) : coordEα (latP 4) ((2 : ℤ) : (latP 4).carrier) x = 0 := by
  have hle : gradingLatGen (latP 4) k ≤
      LinearMap.ker (coordEα (latP 4) ((2 : ℤ) : (latP 4).carrier)) := by
    refine iSup_le fun α => ?_
    by_cases hα : α = ((2 : ℤ) : (latP 4).carrier)
    · subst hα
      rw [bigradα_eq_bot_of_neg (latP 4) _ (by rw [halfNorm_two]; omega)]
      exact bot_le
    · rintro x ⟨p, -, rfl⟩
      rw [LinearMap.mem_ker, mkEα_apply, coordEα_apply, if_neg (Ne.symm hα)]
  exact hle hx

/-- Weight-16 lower descendants of `V₈` have no `e^{2β}` coordinate. -/
theorem coordEα_two_lowerDesc {y : LatModuleGen (latP 4)} (hy : y ∈ lowerDesc V8 16) :
    coordEα (latP 4) ((2 : ℤ) : (latP 4).carrier) y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, z, hz, rfl⟩ := hy
    rw [coordEα_V8_L, coordEα_two_of_lt (by omega) hz, map_zero, map_zero, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

local notation "PP" => V2mPlus 4 four_ge_one
local notation "FF" => orbifoldVOA (Subgroup.zpowers plusCubic)

theorem weightSixteen_not_lowerDesc :
    (weightSixteen : LatModuleGen (latP 4)) ∉ lowerDesc V8 16 := by
  intro h
  have h1 := coordEα_two_lowerDesc h
  rw [coord_weightSixteen] at h1
  have : (1 : FockN (rank (latP 4))) ≠ 0 := one_ne_zero
  exact this (by simpa using h1)

/-- The certified weight-16 state is not a lower descendant in the cubic model. -/
theorem fixedSixteen_not_lowerDesc : fixedSixteen ∉ lowerDesc FF 16 := by
  intro h
  let f1 := (orbifold (Subgroup.zpowers plusCubic)).carrier.subtype
  have hf1 : IsVOAHom FF PP f1 := ⟨rfl, fun _ _ _ => rfl⟩
  let f2 := (orbifold (Subgroup.zpowers (thetaV2m 4 four_ge_one))).carrier.subtype
  have hf2 : IsVOAHom PP V8 f2 := ⟨rfl, fun _ _ _ => rfl⟩
  have h1 := map_lowerDesc_le hf1 rfl 16 (Submodule.mem_map_of_mem h)
  have h2 := map_lowerDesc_le hf2 rfl 16 (Submodule.mem_map_of_mem h1)
  exact weightSixteen_not_lowerDesc h2

/-! ## The weight-sixteen space of `V₂^{A₄}` -/

theorem V2_prim_lowerDesc_eq_zero {N : ℤ} {p : LatModuleGen (latP 1)}
    (hp : p ∈ prim (V2m 1 le_rfl) N) (hl : p ∈ lowerDesc (V2m 1 le_rfl) N) : p = 0 := by
  let U := v2VirUnitary_holds.some
  have hpL := (mem_prim (V2m 1 le_rfl)).mp hp
  have horth : ∀ x ∈ lowerDesc (V2m 1 le_rfl) N, U.form x p = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, y, -, rfl⟩ := hx
      rw [U.adjoint, show -(-(m : ℤ) - 1) = (m : ℤ) + 1 by ring, hpL.2 m, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  exact U.self_eq_zero (horth p hl)

theorem tetraV2TModel : V2TModel tetra T2 phi := v2TModel_of_T2Residual t2Residual

theorem T2_r2_eq_zero : T2 r2 = 0 := by
  have hp := tetraV2TModel.primVal r2 2 (by norm_num) r2_hom
  have hl := tetraV2TModel.r2
  norm_num at hp
  exact V2_prim_lowerDesc_eq_zero hp hl

theorem tT_r2_sq_mem : tT (r2 * r2) ∈ lowerDesc Wt 16 := by
  obtain ⟨c, hc⟩ := tetraV2TModel.top r2 r2 2 2 r2_hom r2_hom (by norm_num) (by norm_num)
  rw [T2_r2_eq_zero, PreVertexAlgebra.smul_zero_left, smul_zero, sub_zero] at hc
  have hav := average_lowerDesc tetra hc
  norm_num at hav
  exact hav

theorem gdeg_four {t : ℕ × ℕ × ℕ × ℕ} (ht : gdeg t = 4) : t = (2, 0, 0, 0) ∨ t = (0, 0, 1, 0) := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [gdeg] at ht
  have : (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 0) := by omega
  rcases this with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> simp

/-- `W₁₆ ⊆ ℂ v + lower descendants`. -/
theorem grading_sixteen_le :
    Wt.grading 16 ≤ (ℂ ∙ tetraV) ⊔ lowerDesc Wt 16 := by
  have hD : VirPrimaryDecomp Wt := tetraPrimaryDecomp_of_unitary v2VirUnitary_holds
  intro x hx
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp (hD 16 hx)
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right hl)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (tetraPrimModel.span 16 hp)
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right hb)
  refine (Submodule.span_le.mpr ?_) ha
  rintro _ ⟨F, ⟨hF, n, hn, hnN⟩, rfl⟩
  have hn4 : n = 4 := by
    have : (n : ℤ) = 4 := by nlinarith
    exact_mod_cast this
  subst hn4
  have hFs := mem_span_genMon_of_isHomogeneous hF hn
  have hmap : tT F ∈ (Submodule.span ℂ (genMon '' {t | gdeg t = 4})).map tT :=
    Submodule.mem_map_of_mem hFs
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  rcases gdeg_four ht with rfl | rfl
  · have : genMon (2, 0, 0, 0) = r2 * r2 := by simp [genMon, pow_two]
    rw [SetLike.mem_coe, this]
    exact Submodule.mem_sup_right tT_r2_sq_mem
  · have : genMon (0, 0, 1, 0) = I4 := by simp [genMon]
    rw [SetLike.mem_coe, this]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)

/-- `R`-classes of weight-16 lower descendants lie on `ω̄⁸𝟙̄`. -/
theorem mk₂_lowerDesc_sixteen {y : (orbifold tetra).carrier} (hy : y ∈ lowerDesc Wt 16) :
    mk₂ Wt y ∈ ℂ ∙ mk₂ Wt (((Wt.L (-2)) ^ 8) Wt.vacuum) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, z, hz, rfl⟩ := hy
    rcases m with _ | _ | m
    · have h0 : Wt.L (-((0 : ℕ) : ℤ) - 1) z ∈ O₂ Wt := by simpa using L_neg_one_mem_O₂ Wt z
      rw [(mk₂_eq_zero_iff Wt).mpr h0]
      exact Submodule.zero_mem _
    · have hL : Wt.L (-(((0 + 1 : ℕ)) : ℤ) - 1) z = Wt.L (-2) z := by norm_num
      rw [hL, ← exceptionalConformalEnd_mk]
      have hz' : z ∈ Wt.grading 14 := by
        have : (16 : ℤ) - ((0 + 1 : ℕ) : ℤ) - 1 = 14 := by norm_num
        rw [← this]; exact hz
      have h14 := mk₂_mem_gradedSpan 14 z hz'
      have hle : gradedSpan 14 ≤ ℂ ∙ mk₂ Wt (((Wt.L (-2)) ^ 7) Wt.vacuum) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, a, ha, rfl⟩
        fin_cases i
        · have : a = 7 := by simp [gWt] at ha; omega
          subst this
          exact Submodule.mem_span_singleton_self _
        · exfalso; simp [gWt] at ha; omega
        · exfalso; simp [gWt] at ha; omega
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hle h14)
      rw [← hc, map_smul, exceptionalConformalEnd_mk, ← Module.End.mul_apply, ← pow_succ']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · have hO : Wt.L (-((m + 1 + 1 : ℕ) : ℤ) - 1) z ∈ O₂ Wt :=
        smul_le_neg_two_mem_O₂ Wt _ _ (by omega)
      rw [(mk₂_eq_zero_iff Wt).mpr hO]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

/-! ## Assembly -/

/-- The even residual from the weight-20 relation and an identification
`v̄ = p X̄ + q ω̄⁸𝟙̄`. -/
theorem tetraSixteenTruncation_of_combo {X : (orbifold tetra).carrier} {b c : ℂ} (hb : b ≠ 0)
    (h20 : c • (exceptionalConformalEnd Wt ^ 10) (mk₂ Wt Wt.vacuum) +
      b • (exceptionalConformalEnd Wt ^ 2) (mk₂ Wt X) = 0) (p q : ℂ)
    (hv : mk₂ Wt tetraV = p • mk₂ Wt X + q • mk₂ Wt (((Wt.L (-2)) ^ 8) Wt.vacuum)) :
    TetraSixteenTruncation := by
  set D := exceptionalConformalEnd Wt
  have hX2 : (D ^ 2) (mk₂ Wt X) = -(c / b) • (D ^ 10) (mk₂ Wt Wt.vacuum) := by
    have h := congrArg (fun z => b⁻¹ • z) h20
    simp only [smul_add, smul_smul, smul_zero] at h
    rw [inv_mul_cancel₀ hb, one_smul] at h
    rw [eq_neg_of_add_eq_zero_right h, ← neg_smul, div_eq_inv_mul]
  refine ⟨p * -(c / b) + q, ?_⟩
  rw [← exceptionalConformalEnd_pow_mk, ← exceptionalConformalEnd_pow_mk, hv,
    ← exceptionalConformalEnd_pow_mk]
  have h82 : (D ^ 2) ((D ^ 8) (mk₂ Wt Wt.vacuum)) = (D ^ 10) (mk₂ Wt Wt.vacuum) := by
    rw [← Module.End.mul_apply, ← pow_add]
  rw [map_add, map_smul, map_smul, hX2, h82, smul_smul, ← add_smul]

/-- **`TetraSixteenTruncation` holds.** -/
theorem tetraSixteenTruncation_holds : TetraSixteenTruncation := by
  -- the certified weight-20 remainder in `V₈⁺`
  have hmem : modeRemainder PP normalizedNine weightSixteen (-3) 10 2 candidateVacuum20 djB20 ∈
      virError PP (PP).vacuum ⊔ virError PP weightSixteen := by
    rw [cubicFiniteVirasoroCertificates.1]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (wordSum_mem_virError PP _ _ vacErrors20_bad))
      (Submodule.mem_sup_right (wordSum_mem_virError PP _ _ seedErrors20_bad))
  have hF := fixed_remainder_mem fixedNormalizedNine fixedSixteen (-3) 10 2 _ _ hmem
  obtain ⟨e, he, hω⟩ := plus_cubic_tetra_iso
  have hT := hom_remainder_mem he hω _ _ _ _ _ _ _ hF
  -- the R-level relation
  have hR : virError Wt Wt.vacuum ⊔ virError Wt (e fixedSixteen) ≤ O₂ Wt :=
    sup_le (virError_le_c2 _ _) (virError_le_c2 _ _)
  have h20 := (mk₂_eq_zero_iff Wt).mpr (hR hT)
  rw [modeRemainder, map_sub, map_add, map_smul, map_smul,
    (mk₂_eq_zero_iff _).mpr (smul_le_neg_two_mem_O₂ _ _ _ (by norm_num)),
    zero_sub, neg_eq_zero] at h20
  simp only [← exceptionalConformalEnd_pow_mk] at h20
  -- the weight-16 identification
  have hXg : e fixedSixteen ∈ Wt.grading 16 :=
    ConverseUniverse.voaHom_map_grading he hω weightSixteen_mem_grading
  obtain ⟨y, hy, l, hl, hyl⟩ := Submodule.mem_sup.mp (grading_sixteen_le hXg)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hyl
    apply fixedSixteen_not_lowerDesc
    have hs := ConverseUniverse.isVOAHom_symm' e he
    have hωs : e.symm (orbifoldVOA tetra).conformalVector = (FF).conformalVector := by
      rw [← hω, LinearEquiv.symm_apply_apply]
    have := map_lowerDesc_le hs hωs 16 (Submodule.mem_map_of_mem (hyl ▸ hl))
    simpa using this
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (mk₂_lowerDesc_sixteen hl)
  have hv : mk₂ Wt tetraV = a⁻¹ • mk₂ Wt (e fixedSixteen) +
      (-(a⁻¹ * d)) • mk₂ Wt (((Wt.L (-2)) ^ 8) Wt.vacuum) := by
    rw [← hyl, map_add, map_smul, ← hd, smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul,
      smul_smul, neg_smul, add_neg_cancel_right]
  exact tetraSixteenTruncation_of_combo (by norm_num [djB20]) h20 _ _ hv

/-- `CubicZhuDimensionBound` from the odd Zhu relation alone. -/
theorem cubicZhuDimensionBound_of_oddRelation (hO : TetraOddZhuRelation) :
    OrbRat2.CubicZhuDimensionBound :=
  cubicZhuDimensionBound_of_residuals tetraSixteenTruncation_holds hO

/-- B3 (`A₄`) rationality from the odd Zhu relation and the two non-vacuum residuals. -/
theorem cubicModel_admissiblyRational_of_oddRelation (hO : TetraOddZhuRelation)
    (h41 : OrbRat8.TopCyclicFourOneResidual)
    (h94 : OrbRat8.TopCyclicVanishing OrbRat2.cubicModel (1 / 4) (9 / 4)) :
    AdmissiblyRational OrbRat2.cubicModel :=
  cubicModel_admissiblyRational_of_zhuResiduals tetraSixteenTruncation_holds hO h41 h94

end VOA.Classification.COne.OrbZhu
