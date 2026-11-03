/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteComplex

/-!
# Survival of the semi-infinite vacuum

The ghost Fock space has negative ghost degrees, so their global vanishing cannot
prove non-exactness. At conformal weight zero, however, every ghost has
nonnegative ghost degree: an antighost creation operator costs positive weight.
For matter with nonnegative integral weights, projection first to weight zero
and then to ghost degree minus one proves that a nonzero vacuum is not exact.
-/

namespace VOA.Sl2SemiInfinite

open scoped TensorProduct

universe u v

/-- The nonnegative part of an integer grading. -/
def nonnegativeGhostPart {K : Type*} [AddCommGroup K] [Module ℂ K]
    (G : ℤ → Submodule ℂ K) : Submodule ℂ K := ⨆ n : ℕ, G (n : ℤ)

theorem ghNum_nonneg_of_weight_zero (l : SympFerm.SFWord)
    (hl : Ghost.ghWeight l = 0) : 0 ≤ Ghost.ghNum l := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      have hp : Ghost.ghModeWt p = 0 := by
        rw [Ghost.ghWeight_cons] at hl
        omega
      have hr : Ghost.ghWeight rest = 0 := by
        rw [Ghost.ghWeight_cons] at hl
        omega
      have ha : p.2 = 1 := by
        obtain ⟨k, a⟩ := p
        fin_cases a
        · simp [Ghost.ghModeWt, Ghost.ghWt] at hp
        · rfl
      rw [Ghost.ghNum_cons, ha]
      have := ih hr
      norm_num [Ghost.ghCharge]
      omega

/-- Weight zero in a single ghost pair has no negative ghost-number support. -/
theorem ghost_weight_zero_le_nonnegative :
    Ghost.bcGhostSVA.grading 0 ≤ nonnegativeGhostPart Ghost.ghostGrading := by
  change Ghost.gradingGh 0 ≤ _
  rw [Ghost.gradingGh, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hweight : Ghost.ghWeight l = 0 := by
    exact_mod_cast (show (Ghost.ghWeight l : ℂ) = 0 from hl)
  have hn := ghNum_nonneg_of_weight_zero l hweight
  apply Submodule.mem_iSup_of_mem (Ghost.ghNum l).toNat
  simpa only [Int.toNat_of_nonneg hn] using Ghost.stWordSF_mem_ghostGrading l

/-- Weight zero of two nonnegatively supported algebras is the tensor of their
weight-zero spaces. No choice of bases is needed. -/
theorem tenGrading_zero_eq {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hV : DSMor.NatSupported V.grading) (hW : DSMor.NatSupported W.grading) :
    TensorVA.tenGrading V W 0 = TensorVA.tenSub (V.grading 0) (W.grading 0) := by
  apply le_antisymm
  · unfold TensorVA.tenGrading
    refine iSup_le fun h => ?_
    by_cases hh : ∃ n : ℕ, (n : ℂ) = h
    · obtain ⟨n, rfl⟩ := hh
      by_cases hn : n = 0
      · subst n
        simp
      · rw [hW (0 - (n : ℂ)) (by
          rintro ⟨m, hm⟩
          have hsum : ((m + n : ℕ) : ℂ) = 0 := by
            push_cast
            linear_combination hm
          have hz : m + n = 0 := by exact_mod_cast hsum
          omega), DSMor.tenSub_bot_right]
        exact bot_le
    · rw [hV h hh, DSMor.tenSub_bot_left]
      exact bot_le
  · have h := le_iSup (fun h : ℂ =>
      TensorVA.tenSub (V.grading h) (W.grading (0 - h))) 0
    simpa [TensorVA.tenGrading] using h

/-- Nonnegative ghost-number support is preserved by tensor products. -/
theorem tmul_mem_nonnegativeGhostPart {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (P : ℤ → Submodule ℂ A) (Q : ℤ → Submodule ℂ B)
    {x : A} {y : B} (hx : x ∈ nonnegativeGhostPart P)
    (hy : y ∈ nonnegativeGhostPart Q) :
    x ⊗ₜ[ℂ] y ∈ nonnegativeGhostPart (tensorGhostGrading P Q) := by
  refine Submodule.iSup_induction'
    (motive := fun x _ => x ⊗ₜ[ℂ] y ∈ nonnegativeGhostPart (tensorGhostGrading P Q))
    _ ?_ ?_ ?_ hx
  · intro n x hx
    refine Submodule.iSup_induction'
      (motive := fun y _ => x ⊗ₜ[ℂ] y ∈ nonnegativeGhostPart (tensorGhostGrading P Q))
      _ ?_ ?_ ?_ hy
    · intro m y hy
      apply Submodule.mem_iSup_of_mem (n + m)
      simpa only [Nat.cast_add] using tmul_mem_tensorGhostGrading P Q hx hy
    · dsimp only
      rw [TensorProduct.tmul_zero]
      exact Submodule.zero_mem _
    · intro y z _ _ hy hz
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hy hz
  · dsimp only
    rw [TensorProduct.zero_tmul]
    exact Submodule.zero_mem _
  · intro x z _ _ hx hz
    rw [TensorProduct.add_tmul]
    exact Submodule.add_mem _ hx hz

theorem tenGrading_zero_le_nonnegative {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hV : DSMor.NatSupported V.grading) (hW : DSMor.NatSupported W.grading)
    (P : ℤ → Submodule ℂ A) (Q : ℤ → Submodule ℂ B)
    (hP : V.grading 0 ≤ nonnegativeGhostPart P)
    (hQ : W.grading 0 ≤ nonnegativeGhostPart Q) :
    TensorVA.tenGrading V W 0 ≤ nonnegativeGhostPart (tensorGhostGrading P Q) := by
  rw [tenGrading_zero_eq V W hV hW]
  intro u hu
  exact TensorVA.tenSub_induction (Submodule.zero_mem _)
    (fun _ _ => Submodule.add_mem _) (fun c _ => Submodule.smul_mem _ c)
    (fun x hx y hy => tmul_mem_nonnegativeGhostPart P Q (hP hx) (hQ hy)) hu

/-- The three-pair ghost weight-zero subspace has nonnegative ghost number. -/
theorem sl2Ghost_weight_zero_le_nonnegative :
    sl2GhostSVA.grading 0 ≤ nonnegativeGhostPart sl2GhostGrading := by
  apply tenGrading_zero_le_nonnegative ghostPairSVA Ghost.bcGhostSVA
    natSupported_ghostPairSVA DSMor.natSupported_bcGhostSVA
    ghostPairGrading Ghost.ghostGrading
  · exact tenGrading_zero_le_nonnegative Ghost.bcGhostSVA Ghost.bcGhostSVA
      DSMor.natSupported_bcGhostSVA DSMor.natSupported_bcGhostSVA
      Ghost.ghostGrading Ghost.ghostGrading
      ghost_weight_zero_le_nonnegative ghost_weight_zero_le_nonnegative
  · exact ghost_weight_zero_le_nonnegative

variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M}

/-- Nonnegative matter weights prohibit negative ghost number at total weight zero. -/
theorem matterGhost_weight_zero_le_nonnegative
    (hn : DSMor.NatSupported V.grading) :
    TensorVA.tenGrading V sl2GhostSVA 0 ≤ nonnegativeGhostPart (matterGhostGrading M) := by
  rw [tenGrading_zero_eq V sl2GhostSVA hn natSupported_sl2GhostSVA]
  intro u hu
  refine TensorVA.tenSub_induction (Submodule.zero_mem _)
    (fun _ _ => Submodule.add_mem _) (fun c _ => Submodule.smul_mem _ c) ?_ hu
  intro x _ y hy
  have hy' := sl2Ghost_weight_zero_le_nonnegative hy
  refine Submodule.iSup_induction'
    (motive := fun y _ => x ⊗ₜ[ℂ] y ∈ nonnegativeGhostPart (matterGhostGrading M))
    _ ?_ ?_ ?_ hy'
  · intro n y hy
    exact Submodule.mem_iSup_of_mem n (tmul_mem_matterGhostGrading M x hy)
  · dsimp only
    rw [TensorProduct.tmul_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ hy hz

/-- A negative homogeneous projection kills the nonnegative part. -/
theorem negative_homogProj_eq_zero {K : Type*} [AddCommGroup K] [Module ℂ K]
    (G : ℤ → Submodule ℂ K) [DirectSum.Decomposition G]
    {g : ℤ} (hg : g < 0) {x : K} (hx : x ∈ nonnegativeGhostPart G) :
    homogProj G g x = 0 := by
  classical
  refine Submodule.iSup_induction'
    (motive := fun x _ => homogProj G g x = 0) _ ?_ ?_ ?_ hx
  · intro n x hx
    exact homogProj_of_mem_ne G (by omega) hx
  · dsimp only
    exact map_zero _
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy, add_zero]

/-- The correct degree criterion is needed only at conformal weight zero.
There may be arbitrarily negative ghost degrees elsewhere. -/
theorem vacuum_not_mem_imQ_of_weight_zero_nonnegative
    {K : Type*} [AddCommGroup K] [Module ℂ K] {S : SuperVertexAlgebra K}
    (C : BRST.BRSTComplex S)
    (h0 : S.vacuum ∈ C.ghost 0)
    (hwt : S.grading 0 ≤ nonnegativeGhostPart C.ghost)
    (hne : S.vacuum ≠ 0) : S.vacuum ∉ C.imQ := by
  classical
  haveI : DirectSum.Decomposition S.grading := S.isInternal.chooseDecomposition S.grading
  haveI : DirectSum.Decomposition C.ghost := C.ghost_isInternal.chooseDecomposition C.ghost
  rintro ⟨a, ha⟩
  have hw : C.Q (homogProj S.grading 0 a) = S.vacuum := by
    have h := BRST.homogProj_shift S.grading C.Q (Equiv.refl ℂ)
      (fun h x hx => C.Q_wt h x hx) 0 a
    simpa only [Equiv.refl_apply, ha, homogProj_of_mem S.grading S.vacuum_mem] using h.symm
  have hz : homogProj C.ghost (-1) (homogProj S.grading 0 a) = 0 :=
    negative_homogProj_eq_zero C.ghost (by norm_num)
      (hwt (homogProj_mem S.grading 0 a))
  have hg := BRST.homogProj_shift C.ghost C.Q (BRST.shiftOne ℤ)
    (fun g x hx => C.Q_ghost g x hx) (-1) (homogProj S.grading 0 a)
  have he : (BRST.shiftOne ℤ) (-1) = 0 := by
    rw [BRST.shiftOne_apply]
    norm_num
  rw [he, hw, homogProj_of_mem C.ghost h0, hz, map_zero] at hg
  exact hne hg

/-- The actual semi-infinite vacuum is non-exact for nonnegatively supported
matter with a nonzero vacuum. The ghost-degree gap is proved, not assumed. -/
theorem semiInfinite_vacuum_not_mem_imQ
    (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hn : DSMor.NatSupported V.grading) (hv : V.vacuum ≠ 0) :
    V.vacuum ⊗ₜ[ℂ] sl2GhostSVA.vacuum ∉ (semiInfiniteBRSTComplex A hV hg).imQ := by
  apply vacuum_not_mem_imQ_of_weight_zero_nonnegative (semiInfiniteBRSTComplex A hV hg)
  · exact tmul_mem_matterGhostGrading M V.vacuum sl2GhostSVA_vacuum_ghost
  · exact matterGhost_weight_zero_le_nonnegative hn
  · exact tensorSVA_vacuum_ne_zero V sl2GhostSVA hV parityCompatible_sl2GhostSVA hg
      hv sl2GhostSVA_vacuum_ne_zero

/-- The canonical vacuum class in full semi-infinite cohomology is nonzero. -/
theorem semiInfinite_cohomology_vacuum_ne_zero
    (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hn : DSMor.NatSupported V.grading) (hv : V.vacuum ≠ 0) :
    (semiInfiniteBRSTComplex A hV hg).cohomology.vacuum ≠ 0 := by
  intro hz
  rw [BRST.BRSTComplex.cohomology_vacuum, BRST.BRSTComplex.prj_eq_zero,
    BRST.BRSTComplex.vacK_coe] at hz
  exact semiInfinite_vacuum_not_mem_imQ A hV hg hn hv hz

/-- Non-exactness in the full complex implies non-exactness in the actual
relative subcomplex. -/
theorem relative_vacuum_not_mem_range
    (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hn : DSMor.NatSupported V.grading) (hv : V.vacuum ≠ 0) :
    (⟨V.vacuum ⊗ₜ[ℂ] sl2GhostSVA.vacuum,
      vacuum_mem_relativeCarrier A.toAffineSl2Action⟩ : relativeCarrier A.toAffineSl2Action)
        ∉ LinearMap.range (relativeQ A hV hg) := by
  rintro ⟨x, hx⟩
  apply semiInfinite_vacuum_not_mem_imQ A hV hg hn hv
  exact ⟨x, congrArg Subtype.val hx⟩

/-- Boundaries as a subspace of relative cycles. Square-zero of `relativeQ`
ensures that this is exactly its image, viewed inside its kernel. -/
noncomputable def relativeBoundaries
    (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    Submodule ℂ (LinearMap.ker (relativeQ A hV hg)) :=
  (LinearMap.range (relativeQ A hV hg)).comap (LinearMap.ker (relativeQ A hV hg)).subtype

/-- The actual relative cohomology, cycles modulo boundaries. -/
abbrev RelativeCohomology
    (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :=
  (LinearMap.ker (relativeQ A hV hg)) ⧸ relativeBoundaries A hV hg

/-- The tensor vacuum as a cycle in the relative complex. -/
noncomputable def relativeVacuumCycle
    (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    LinearMap.ker (relativeQ A hV hg) :=
  ⟨⟨V.vacuum ⊗ₜ[ℂ] sl2GhostSVA.vacuum,
    vacuum_mem_relativeCarrier A.toAffineSl2Action⟩,
    by
      apply Subtype.ext
      exact (semiInfiniteBRSTComplex A hV hg).Q_vacuum⟩

/-- The canonical relative vacuum class. -/
noncomputable def relativeVacuumClass
    (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    RelativeCohomology A hV hg :=
  (relativeBoundaries A hV hg).mkQ (relativeVacuumCycle A hV hg)

/-- The vacuum class survives in the relative complex for nonnegative matter
weights and a nonzero matter vacuum. -/
theorem relativeVacuumClass_ne_zero
    (A : TranslatedAffineSl2Action V (-4))
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hn : DSMor.NatSupported V.grading) (hv : V.vacuum ≠ 0) :
    relativeVacuumClass A hV hg ≠ 0 := by
  intro hz
  have hm := (Submodule.Quotient.mk_eq_zero (relativeBoundaries A hV hg)).mp hz
  exact relative_vacuum_not_mem_range A hV hg hn hv hm

end VOA.Sl2SemiInfinite
