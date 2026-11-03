import VOA.Classification.COne.OrbZhuGraded
import VOA.Classification.COne.OrbA4Assembly

/-!
# OrbZhu (3): `CubicZhuDimensionBound` reduced to two sharp residuals

Counting in `A(W)`, `W = V₂^{A₄}`, with the tower calculus of `OrbZhuTower` and the graded
three-seed span of `OrbZhuGraded`:

* `𝟙`-tower: `[ω]^a`, `a ≤ 10` (`ω̄¹¹ = 0`, proved): 11;
* `v`-tower: `[ω]^a[v]`, `a ≤ 1`, given `TetraSixteenTruncation` (`ω̄²v̄ ∈ ℂ·ω̄¹⁰`): 2;
* `u`-tower: `[ω]^a[u]`, `a ≤ 7`, given `TetraOddZhuRelation` (a monic relation of degree
  `≤ 8` for `[u]` over `ℂ[[ω]]` IN `A(W)`): 8.

Total `11 + 2 + 8 = 21` (`tetra_finrank_zhu_le`), transported to `cubicModel` along
`tetra_cubic_iso` (`finrank_zhu_le_of_voaHom_surj`).

The odd relation CANNOT come from `R(W)`: the `u`-tower `ω̄^a ū` is nonzero in `R(W)` for
`a ≤ 8`, so `dim R(W) ≥ 22`; the filtration
bound `dim A(W) ≤ dim R(W)` alone can never give `21`.

`tetraSixteenTruncation_of_sixteen`: the even residual follows from the proved weight-20
Dong–Jiang relation for any certified weight-16 state `X` whose class is not a multiple of
`ω̄⁸𝟙̄`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbZhu

open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b OrbC2c OrbRat2

/-! ## The residuals -/

/-- OPEN (true: Dong–Jiang Lemma 4.3 with `u^{(16)} = v`, i.e. the weight-20 relation
`c·ω̄¹⁰ + b·ω̄²X̄ = 0` together with `X̄ = α v̄ + β ω̄⁸𝟙̄`, `α ≠ 0`): the weight-sixteen tower
truncates, `ω̄² v̄ ∈ ℂ · ω̄¹⁰ 𝟙̄` in `R(W) = W/C₂(W)`. -/
def TetraSixteenTruncation : Prop :=
  ∃ γ : ℂ, mk₂ Wt (((Wt.L (-2)) ^ 2) tetraV) = γ • mk₂ Wt (((Wt.L (-2)) ^ 10) Wt.vacuum)

/-- OPEN (true: Dong–Jiang's 21 irreducible modules give `A(W) ≅ ℂ²¹`; the octahedral
involution `τ` has `τ u = -u`, so `[u]` lies in the `τ`-odd part of `A(W)`, on which `[ω]` has
at most the 8 doubled lowest weights `4, 9/4, 1/36, 25/36, 49/36, 1/9, 4/9, 16/9` as
eigenvalues): `[u]` satisfies a monic relation of degree `≤ 8` over `ℂ[[ω]]` in `A(W)`.
This relation is NOT visible in `R(W)`. -/
def TetraOddZhuRelation : Prop :=
  ∃ P : Polynomial ℂ, P.Monic ∧ P.natDegree ≤ 8 ∧
    (Polynomial.aeval (omegaL Wt) P) (mk Wt tetraU) = 0

/-! ## The weight-sixteen class -/

theorem gradedSpan_sixteen_le :
    gradedSpan 16 ≤ Submodule.span ℂ
      {mk₂ Wt (((Wt.L (-2)) ^ 8) Wt.vacuum), mk₂ Wt tetraV} := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, a, ha, rfl⟩
  fin_cases i
  · have : a = 8 := by simp [gWt] at ha; omega
    subst this
    exact Submodule.subset_span (Or.inl rfl)
  · exfalso; simp [gWt] at ha; omega
  · have : a = 0 := by simp [gWt] at ha; omega
    subst this
    exact Submodule.subset_span (Or.inr rfl)

/-- The even residual from the proved weight-20 relation and a nondegenerate weight-16
state: if `X ∈ W₁₆` satisfies `c ω̄¹⁰ + b ω̄² X̄ = 0` with `b ≠ 0` and `X̄ ∉ ℂ ω̄⁸ 𝟙̄`,
then `ω̄² v̄ ∈ ℂ ω̄¹⁰ 𝟙̄`. -/
theorem tetraSixteenTruncation_of_sixteen {X : (orbifold tetra).carrier}
    (hX : X ∈ Wt.grading 16) {b c : ℂ} (hb : b ≠ 0)
    (h20 : c • (exceptionalConformalEnd Wt ^ 10) (mk₂ Wt Wt.vacuum) +
      b • (exceptionalConformalEnd Wt ^ 2) (mk₂ Wt X) = 0)
    (hα : ∀ β : ℂ, mk₂ Wt X ≠ β • mk₂ Wt (((Wt.L (-2)) ^ 8) Wt.vacuum)) :
    TetraSixteenTruncation := by
  have hmem := gradedSpan_sixteen_le (mk₂_mem_gradedSpan 16 X hX)
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hmem
  have hq : q ≠ 0 := by
    rintro rfl
    exact hα p (by rw [← hpq, zero_smul, add_zero])
  set D := exceptionalConformalEnd Wt
  have hv : mk₂ Wt tetraV = q⁻¹ • (mk₂ Wt X - p • mk₂ Wt (((Wt.L (-2)) ^ 8) Wt.vacuum)) := by
    rw [← hpq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hq, one_smul]
  refine ⟨-(q⁻¹ * (c / b + p)), ?_⟩
  rw [← exceptionalConformalEnd_pow_mk, ← exceptionalConformalEnd_pow_mk, hv]
  rw [← exceptionalConformalEnd_pow_mk] at hv ⊢
  have hX2 : (D ^ 2) (mk₂ Wt X) = -(c / b) • (D ^ 10) (mk₂ Wt Wt.vacuum) := by
    have h := congrArg (fun z => b⁻¹ • z) h20
    simp only [smul_add, smul_smul, smul_zero] at h
    rw [inv_mul_cancel₀ hb, one_smul] at h
    rw [eq_neg_of_add_eq_zero_right h, ← neg_smul, div_eq_inv_mul]
  have h82 : (D ^ 2) ((D ^ 8) (mk₂ Wt Wt.vacuum)) = (D ^ 10) (mk₂ Wt Wt.vacuum) := by
    rw [← Module.End.mul_apply, ← pow_add]
  rw [map_smul, map_sub, map_smul, hX2, h82, ← sub_smul, smul_smul]
  congr 1
  ring

/-! ## The count -/

/-- Tower heights in `R(W)`. -/
def nR : Fin 3 → ℕ := ![11, 11, 2]

/-- Tower heights in `A(W)`. -/
def mA : Fin 3 → ℕ := ![11, 8, 2]

theorem towers_span_truncated (hT : TetraSixteenTruncation) :
    Submodule.span ℂ (Set.range fun p : (Σ i, Fin (nR i)) =>
      mk₂ Wt (((Wt.L (-2)) ^ (p.2 : ℕ)) (gSeed p.1))) = ⊤ := by
  obtain ⟨γ, hγ⟩ := hT
  apply top_unique
  rw [← towers_span_eleven]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i, a⟩, rfl⟩
  set S := Submodule.span ℂ (Set.range fun p : (Σ i, Fin (nR i)) =>
      mk₂ Wt (((Wt.L (-2)) ^ (p.2 : ℕ)) (gSeed p.1)))
  have hin : ∀ (j : Fin 3) (b : ℕ) (hb : b < nR j),
      mk₂ Wt (((Wt.L (-2)) ^ b) (gSeed j)) ∈ S :=
    fun j b hb => Submodule.subset_span ⟨⟨j, ⟨b, hb⟩⟩, rfl⟩
  show mk₂ Wt (((Wt.L (-2)) ^ (a : ℕ)) (gSeed i)) ∈ S
  fin_cases i
  · exact hin 0 a (by simp [nR])
  · exact hin 1 a (by simp [nR])
  · by_cases ha : (a : ℕ) < 2
    · exact hin 2 a (by simpa [nR] using ha)
    · obtain ⟨c, hc⟩ : ∃ c, (a : ℕ) = c + 2 := ⟨a - 2, by omega⟩
      have hv : mk₂ Wt (((Wt.L (-2)) ^ (a : ℕ)) (gSeed 2)) =
          γ • mk₂ Wt (((Wt.L (-2)) ^ (c + 10)) Wt.vacuum) := by
        rw [← exceptionalConformalEnd_pow_mk, hc, pow_add, Module.End.mul_apply,
          exceptionalConformalEnd_pow_mk]
        change (exceptionalConformalEnd Wt ^ c) (mk₂ Wt (((Wt.L (-2)) ^ 2) tetraV)) = _
        rw [hγ, map_smul, ← exceptionalConformalEnd_pow_mk, ← exceptionalConformalEnd_pow_mk,
          ← Module.End.mul_apply, ← pow_add]
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [hv]
      apply Submodule.smul_mem
      by_cases hc0 : c = 0
      · subst hc0
        exact hin 0 10 (by simp [nR])
      · have : mk₂ Wt (((Wt.L (-2)) ^ (c + 10)) Wt.vacuum) = 0 := by
          rw [← exceptionalConformalEnd_pow_mk,
            show c + 10 = (c - 1) + 11 by omega, pow_add, tetra_conformal_pow_eleven,
            mul_zero, LinearMap.zero_apply]
        rw [this]; exact Submodule.zero_mem _

/-- **`dim A(V₂^{A₄}) ≤ 21`** from the two residuals. -/
theorem tetra_finrank_zhu_le (hT : TetraSixteenTruncation) (hO : TetraOddZhuRelation) :
    FiniteDimensional ℂ (A Wt) ∧ Module.finrank ℂ (A Wt) ≤ 21 := by
  obtain ⟨P, hPm, hPd, hP⟩ := hO
  have h := finrank_A_le_of_towers Wt gSeed (fun i => (gWt i : ℤ)) gSeed_mem nR mA
    (towers_span_truncated hT) (by
      intro i a ha
      fin_cases i
      · exact pow_mem_towerSub Wt _ (by simpa [nR, mA] using ha)
      · exact towerSub_mono Wt _ (by simpa [mA] using hPd)
          (pow_mem_towerSub_of_monic Wt _ hPm hP a)
      · exact pow_mem_towerSub Wt _ (by simpa [nR, mA] using ha))
  refine ⟨h.1, h.2.trans ?_⟩
  simp [mA, Fin.sum_univ_three]

/-! ## Transport to the cubic model -/

section Transport

universe u v

variable {𝒱 : Type u} {𝒲 : Type v} [AddCommGroup 𝒱] [Module ℂ 𝒱] [AddCommGroup 𝒲]
  [Module ℂ 𝒲] {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}

theorem voaHom_map_zhuMul {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (a b : 𝒱) :
    φ (zhuMul V a b) = zhuMul T (φ a) (φ b) := by
  have ha : a ∈ Submodule.span ℂ {x | IsHomog V x} := by rw [span_homog_eq_top]; trivial
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, hn⟩ := hx
    rw [zhuMul_homogeneous V hn,
      zhuMul_homogeneous T (ConverseUniverse.voaHom_map_grading hφ hω hn), map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hφ.map_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [zhuMul_add_left, map_add, hx, hy, map_add, zhuMul_add_left]
  | smul c x _ hx => rw [zhuMul_smul_left, map_smul, hx, map_smul, zhuMul_smul_left]

theorem voaHom_map_O {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) : (O V).map φ ≤ O T := by
  rw [O, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨φ a, φ b, ?_⟩
  rw [voaHom_map_zhuMul hφ hω, map_add, ConverseUniverse.voaHom_map_L hφ hω,
    ConverseUniverse.voaHom_map_L hφ hω]

/-- A surjective conformal VOA homomorphism does not increase `dim A`. -/
theorem finrank_zhu_le_of_voaHom_surj {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (hs : Function.Surjective φ)
    [FiniteDimensional ℂ (A V)] :
    FiniteDimensional ℂ (A T) ∧ Module.finrank ℂ (A T) ≤ Module.finrank ℂ (A V) := by
  let f : A V →ₗ[ℂ] A T := Submodule.mapQ (O V) (O T) φ
    (Submodule.map_le_iff_le_comap.mp (voaHom_map_O hφ hω))
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (O T) q
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨(O V).mkQ x, rfl⟩
  have hr : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  have h1 := LinearMap.finrank_range_le f
  rw [hr, finrank_top] at h1
  refine ⟨?_, h1⟩
  exact Module.Finite.of_surjective f hf

end Transport

/-- **`CubicZhuDimensionBound` from the two residuals.** -/
theorem cubicZhuDimensionBound_of_residuals (hT : TetraSixteenTruncation)
    (hO : TetraOddZhuRelation) : OrbRat2.CubicZhuDimensionBound := by
  obtain ⟨hfin, hle⟩ := tetra_finrank_zhu_le hT hO
  obtain ⟨e, he, hω⟩ := tetra_cubic_iso
  have hs := ConverseUniverse.isVOAHom_symm' e he
  have hω' : e.symm (orbifoldVOA tetra).conformalVector =
      (orbifoldVOA (Subgroup.zpowers kleinCubic)).conformalVector := by
    rw [← hω, LinearEquiv.symm_apply_apply]
  exact (finrank_zhu_le_of_voaHom_surj hs hω' e.symm.surjective).2.trans hle

/-- B3 (`A₄`): rationality of the cubic model from the two Zhu residuals and the two
non-vacuum residuals. -/
theorem cubicModel_admissiblyRational_of_zhuResiduals (hT : TetraSixteenTruncation)
    (hO : TetraOddZhuRelation) (h41 : OrbRat8.TopCyclicFourOneResidual)
    (h94 : OrbRat8.TopCyclicVanishing cubicModel (1 / 4) (9 / 4)) :
    AdmissiblyRational cubicModel :=
  OrbA4.cubicModel_admissiblyRational_of_residuals
    (cubicZhuDimensionBound_of_residuals hT hO) h41 h94

end VOA.Classification.COne.OrbZhu
