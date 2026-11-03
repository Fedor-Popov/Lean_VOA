import VOA.Classification.COne.OrbPrimEquiv
import VOA.Classification.COne.OrbC2hFinal
import VOA.Classification.COne.OrbZhuTower

/-!
# OrbZhu (2): the GRADED three-seed span of `R(V₂^{A₄}) = W/C₂(W)`

`OrbPrim.tetrahedralVirasoroSpan_holds` spans `R(W)` by conformal towers on the seeds
`𝟙, u, v, u₍ₙ₎u`.  The `u₍ₙ₎u` seeds are not needed, and the span is graded:

`mk₂_mem_gradedSpan`: for `x ∈ W_N`,
`x̄ ∈ span{ ω̄^a s̄ : s ∈ {𝟙, u, v}, wt s + 2a = N }`, where `u = T I₃` (weight 9) and
`v = T I₄` (weight 16) are the averaged polynomial-model primaries of `OrbPrim`.

The proof re-runs the `OrbPrim` primary reduction with the second channel
(`six_of_secondChannel`) giving `T I₆ ∈ C₂ + lower descendants` outright, and tracks weights.
Consequence: `towers_span_top`: `R(W)` is spanned by `ω̄^a 𝟙̄, ω̄^a ū, ω̄^a v̄`, `a ≤ 10`
(using `ω̄¹¹ = 0`, `OrbC2h.tetrahedralDongJiangRelations`).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbZhu

open VOA VertexOperatorAlgebra MvPolynomial OrbSpan OrbPrim OrbC2b OrbC2c

/-- `tetra ≅ A₄` is finite. -/
noncomputable local instance tetraFintypeZ : Fintype tetra :=
  @Fintype.ofFinite _ (Finite.of_equiv (alternatingGroup (Fin 4)) tetra_group.some.symm.toEquiv)

/-- `W = V₂^{A₄}`. -/
abbrev Wt := orbifoldVOA tetra

theorem tetraV2Model : V2Model tetra T2 phi :=
  ((v2TModel_of_T2Residual t2Residual).toSplit primSpectrumBound_V2).toV2Model

/-- The averaged polynomial model `T : ℂ[x,y,z] → W`. -/
def tT : P3 →ₗ[ℂ] (orbifold tetra).carrier := avgT tetra T2

theorem tetraPrimModel : PrimModel Wt tT := primModel_of_v2Model tetraV2Model

/-- The weight-nine seed `u = T I₃`. -/
def tetraU : (orbifold tetra).carrier := tT I3

/-- The weight-sixteen seed `v = T I₄`. -/
def tetraV : (orbifold tetra).carrier := tT I4

theorem tetraU_mem : tetraU ∈ Wt.grading 9 := by
  have h := avgT_grading tetraV2Model isA4Inv_I3 I3_hom
  norm_num at h; exact h

theorem tetraV_mem : tetraV ∈ Wt.grading 16 := by
  have h := avgT_grading tetraV2Model isA4Inv_I4 I4_hom
  norm_num at h; exact h

/-- The second channel puts `T I₆` in `C₂ + lower descendants` (no `u₍ₙ₎u` seed). -/
theorem tetra_six : tT I6 ∈ O₂ Wt ⊔ lowerDesc Wt 36 := by
  have hS : ∃ c d : ℂ, c ≠ 0 ∧ Wt.smul (tT I4) (-12) (tT I3) - c • tT I6 -
      d • tT (I3 * I3) ∈ lowerDesc Wt 36 := by
    obtain ⟨c, d, hc, hδ⟩ := tetraV2Model.six
    refine ⟨c, d, hc, ?_⟩
    have hav := average_lowerDesc tetra hδ
    rwa [map_sub, map_sub, map_smul, map_smul,
      average_smul_T₂ tetraV2Model isA4Inv_I4 isA4Inv_I3,
      average_T₂_inv I6, average_T₂_inv (I3 * I3)] at hav
  exact six_of_secondChannel _ tetraPrimModel.top hS

/-- The three seeds. -/
def gSeed : Fin 3 → (orbifold tetra).carrier := ![Wt.vacuum, tetraU, tetraV]

/-- Their weights. -/
def gWt : Fin 3 → ℕ := ![0, 9, 16]

theorem gSeed_mem (i : Fin 3) : gSeed i ∈ Wt.grading (gWt i) := by
  fin_cases i
  · exact Wt.vacuum_mem
  · exact tetraU_mem
  · exact tetraV_mem

/-- The weight-`N` part of the tower span. -/
def gradedSpan (N : ℤ) : Submodule ℂ (A₂ Wt) :=
  Submodule.span ℂ {y | ∃ (i : Fin 3) (a : ℕ), (gWt i : ℤ) + 2 * a = N ∧
    y = mk₂ Wt (((Wt.L (-2)) ^ a) (gSeed i))}

theorem conformal_mem_gradedSpan {N : ℤ} {y : A₂ Wt} (hy : y ∈ gradedSpan N) :
    exceptionalConformalEnd Wt y ∈ gradedSpan (N + 2) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, a, ha, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨i, a + 1, by push_cast; omega, ?_⟩
    rw [exceptionalConformalEnd_mk, pow_succ', Module.End.mul_apply]
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem gradedSpan_neg {N : ℤ} (hN : N < 0) : ∀ x ∈ Wt.grading N, mk₂ Wt x ∈ gradedSpan N := by
  intro x hx
  rw [Wt.positivity N hN, Submodule.mem_bot] at hx
  rw [hx, map_zero]; exact Submodule.zero_mem _

/-- Lower descendants, given the claim in lower weights. -/
theorem lowerDesc_mem_gradedSpan {N : ℤ}
    (ih : ∀ M : ℤ, M < N → ∀ x ∈ Wt.grading M, mk₂ Wt x ∈ gradedSpan M) :
    ∀ y ∈ lowerDesc Wt N, mk₂ Wt y ∈ gradedSpan N := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, z, hz, rfl⟩ := hy
    rcases m with _ | _ | m
    · rw [(mk₂_eq_zero_iff Wt).mpr (by simpa using L_neg_one_mem_O₂ Wt z)]
      exact Submodule.zero_mem _
    · have h1 : ((((0 : ℕ) + 1 : ℕ) : ℤ)) = 1 := by norm_num
      have hL : Wt.L (-(((0 + 1 : ℕ)) : ℤ) - 1) z = Wt.L (-2) z := by norm_num
      rw [hL, ← exceptionalConformalEnd_mk]
      have hz' := ih (N - 2) (by omega) z (by
        rw [show N - 2 = N - ((0 + 1 : ℕ) : ℤ) - 1 by push_cast; ring]; exact hz)
      have := conformal_mem_gradedSpan hz'
      rwa [show N - 2 + 2 = N by ring] at this
    · have hO : Wt.L (-((m + 1 + 1 : ℕ) : ℤ) - 1) z ∈ O₂ Wt :=
        smul_le_neg_two_mem_O₂ Wt _ _ (by omega)
      rw [(mk₂_eq_zero_iff Wt).mpr hO]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem sup_mem_gradedSpan {N : ℤ}
    (ih : ∀ M : ℤ, M < N → ∀ x ∈ Wt.grading M, mk₂ Wt x ∈ gradedSpan M) {y}
    (hy : y ∈ O₂ Wt ⊔ lowerDesc Wt N) : mk₂ Wt y ∈ gradedSpan N := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, (mk₂_eq_zero_iff Wt).mpr ha, zero_add]
  exact lowerDesc_mem_gradedSpan ih b hb

theorem seed_mem_gradedSpan (i : Fin 3) : mk₂ Wt (gSeed i) ∈ gradedSpan (gWt i) :=
  Submodule.subset_span ⟨i, 0, by simp, rfl⟩

/-- `T` of a generator monomial of degree `n`, `n² = N`. -/
theorem genMon_mem_gradedSpan {N : ℤ}
    (ih : ∀ M : ℤ, M < N → ∀ x ∈ Wt.grading M, mk₂ Wt x ∈ gradedSpan M)
    (t : ℕ × ℕ × ℕ × ℕ) (ht : ((gdeg t : ℕ) : ℤ) ^ 2 = N) :
    mk₂ Wt (tT (genMon t)) ∈ gradedSpan N := by
  rcases genMon_cases t with rfl | rfl | rfl | rfl | rfl | ⟨a, b, ha, hb, hab, he⟩
  · have h1 : genMon (0, 0, 0, 0) = 1 := by simp [genMon]
    have hN : N = 0 := by simp [gdeg] at ht; omega
    subst hN
    rw [h1, tetraPrimModel.vac]
    exact seed_mem_gradedSpan 0
  · have h1 : genMon (1, 0, 0, 0) = r2 := by simp [genMon]
    have hN : N = 4 := by simp [gdeg] at ht; omega
    subst hN
    rw [h1]; exact sup_mem_gradedSpan ih tetraPrimModel.r2
  · have h1 : genMon (0, 1, 0, 0) = I3 := by simp [genMon]
    have hN : N = 9 := by simp [gdeg] at ht; omega
    subst hN
    rw [h1]; exact seed_mem_gradedSpan 1
  · have h1 : genMon (0, 0, 1, 0) = I4 := by simp [genMon]
    have hN : N = 16 := by simp [gdeg] at ht; omega
    subst hN
    rw [h1]; exact seed_mem_gradedSpan 2
  · have h1 : genMon (0, 0, 0, 1) = I6 := by simp [genMon]
    have hN : N = 36 := by simp [gdeg] at ht; omega
    subst hN
    rw [h1]; exact sup_mem_gradedSpan ih tetra_six
  · rw [he]
    have h := tetraPrimModel.top _ _ _ _ (isA4Inv_genMon a) (isA4Inv_genMon b)
      (genMon_hom a) (genMon_hom b) ha hb
    rw [hab, ht] at h
    exact sup_mem_gradedSpan ih h

theorem prim_mem_gradedSpan {N : ℤ}
    (ih : ∀ M : ℤ, M < N → ∀ x ∈ Wt.grading M, mk₂ Wt x ∈ gradedSpan M) :
    ∀ p ∈ prim Wt N, mk₂ Wt p ∈ gradedSpan N := by
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (tetraPrimModel.span N hp)
  rw [map_add]
  refine Submodule.add_mem _ ?_ (lowerDesc_mem_gradedSpan ih b hb)
  have hmap : mk₂ Wt a ∈ (Submodule.span ℂ (tT '' invDeg N)).map (mk₂ Wt) :=
    Submodule.mem_map_of_mem ha
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨_, ⟨F, ⟨hF, n, hn, hnN⟩, rfl⟩, rfl⟩
  have hFs := mem_span_genMon_of_isHomogeneous hF hn
  have hmap2 : mk₂ Wt (tT F) ∈
      (Submodule.span ℂ (genMon '' {t | gdeg t = n})).map ((mk₂ Wt).comp tT) :=
    Submodule.mem_map_of_mem hFs
  rw [Submodule.map_span] at hmap2
  refine (Submodule.span_le.mpr ?_) hmap2
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  simp only [Set.mem_setOf_eq] at ht
  exact genMon_mem_gradedSpan ih t (by rw [ht]; exact hnN)

/-- **The graded three-seed span.** -/
theorem mk₂_mem_gradedSpan : ∀ (N : ℤ), ∀ x ∈ Wt.grading N, mk₂ Wt x ∈ gradedSpan N := by
  have hD : VirPrimaryDecomp Wt := tetraPrimaryDecomp_of_unitary v2VirUnitary_holds
  have key : ∀ n : ℕ, ∀ N : ℤ, N < n → ∀ x ∈ Wt.grading N, mk₂ Wt x ∈ gradedSpan N := by
    intro n
    induction n with
    | zero => intro N hN; exact gradedSpan_neg (by omega)
    | succ n ih =>
      intro N hN x hx
      by_cases hlt : N < n
      · exact ih N hlt x hx
      have ih' : ∀ M : ℤ, M < N → ∀ x ∈ Wt.grading M, mk₂ Wt x ∈ gradedSpan M :=
        fun M hM => ih M (by omega)
      obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp (hD N hx)
      rw [map_add]
      exact Submodule.add_mem _ (prim_mem_gradedSpan ih' p hp)
        (lowerDesc_mem_gradedSpan ih' l hl)
  intro N x hx
  exact key (N.toNat + 1) N (by omega) x hx

/-- All conformal towers on the three seeds span `R(W)`. -/
theorem towers_span_all :
    Submodule.span ℂ (Set.range fun p : Fin 3 × ℕ =>
      mk₂ Wt (((Wt.L (-2)) ^ p.2) (gSeed p.1))) = ⊤ := by
  apply top_unique
  rintro y -
  obtain ⟨x, rfl⟩ := mk₂_surjective Wt y
  have hx : x ∈ Submodule.span ℂ {x | IsHomog Wt x} := by rw [span_homog_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨N, hN⟩ := hx
    refine (Submodule.span_le.mpr ?_) (mk₂_mem_gradedSpan N x hN)
    rintro _ ⟨i, a, -, rfl⟩
    exact Submodule.subset_span ⟨(i, a), rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

/-- `ω̄¹¹ = 0` on `R(W)` (Dong–Jiang, `OrbC2h`). -/
theorem tetra_conformal_pow_eleven : exceptionalConformalEnd Wt ^ 11 = 0 :=
  tetra_conformal_nilpotent_of_relations OrbC2h.tetrahedralDongJiangRelations

/-- Towers of height `11` on `𝟙, u, v` span `R(W)`. -/
theorem towers_span_eleven :
    Submodule.span ℂ (Set.range fun p : Fin 3 × Fin 11 =>
      mk₂ Wt (((Wt.L (-2)) ^ (p.2 : ℕ)) (gSeed p.1))) = ⊤ := by
  apply top_unique
  rw [← towers_span_all]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i, a⟩, rfl⟩
  by_cases ha : a < 11
  · exact Submodule.subset_span ⟨(i, ⟨a, ha⟩), rfl⟩
  · obtain ⟨b, rfl⟩ : ∃ b, a = 11 + b := ⟨a - 11, by omega⟩
    have : mk₂ Wt (((Wt.L (-2)) ^ (11 + b)) (gSeed i)) = 0 := by
      rw [← exceptionalConformalEnd_pow_mk, pow_add, tetra_conformal_pow_eleven, zero_mul,
        LinearMap.zero_apply]
    simp only [this, SetLike.mem_coe]; exact Submodule.zero_mem _

end VOA.Classification.COne.OrbZhu
