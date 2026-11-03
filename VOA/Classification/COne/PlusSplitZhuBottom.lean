import VOA.Classification.COne.PlusSplitZhuCharacters
import VOA.Huang.BottomRecovery
import VOA.Modules.ZhuVermaAnArchZeroModeLaw
import VOA.Modularity.AModBridge

/-!
# Splitting extensions detected at admissible level zero

This proves the bottom-lifting argument for an actual nonnegative admissible
grading. It does not identify an arbitrary `FactorBottom` interval with this
grading. In particular the kernel need not be graded or the extension ordinary.

The level-zero representation generalizes the construction in `LeeYangZhu`.
Bottom recovery is the proved homogeneous-mode word argument, with no PBW input.
Reference: Abe, https://arxiv.org/html/math/0311210, Proposition 7.2.
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.PlusSplitting
open PlusRational VOA.Huang.BottomRecovery
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

def bottomAdmLev (N : AdmissibleModule W M) : AdmLev W N.toWeakModule where
  lev := N.lev
  lev_neg := N.lev_eq_bot_of_neg
  act_lev := N.act_lev

/-- Zero modes restricted to the actual admissible bottom. -/
noncomputable def bottomRhoV (N : AdmissibleModule W M) :
    𝒱 →ₗ[ℂ] Module.End ℂ (N.lev 0) where
  toFun v :=
    { toFun := fun x => ⟨oLevW N.toWeakModule 0 v (x : M), by
          simpa using oLevW_mem_lev (bottomAdmLev N) 0 v x.2⟩
      map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c x; apply Subtype.ext; exact map_smul _ _ _ }
  map_add' := by intro u v; ext x; simp
  map_smul' := by intro c v; ext x; simp

theorem O_le_ker_bottomRhoV (N : AdmissibleModule W M) :
    O W ≤ LinearMap.ker (bottomRhoV N) := by
  intro v hv
  rw [LinearMap.mem_ker]
  ext x
  exact O_annihilates_Omega N.toWeakModule hv (lev_zero_le_Omega (bottomAdmLev N) x.2)

noncomputable def bottomRho (N : AdmissibleModule W M) :
    VOA.A W →ₗ[ℂ] Module.End ℂ (N.lev 0) :=
  (O W).liftQ (bottomRhoV N) (O_le_ker_bottomRhoV N)

@[simp] theorem bottomRho_mk (N : AdmissibleModule W M) (v : 𝒱) :
    bottomRho N (VOA.mk W v) = bottomRhoV N v := by
  rw [bottomRho, VOA.mk, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- An arbitrary admissible bottom is a Zhu module, with no diagonalizability
or finite-dimensionality requirement. -/
noncomputable def bottomAMod (N : AdmissibleModule W M) : AMod W where
  carrier := N.lev 0
  ρ := bottomRho N
  ρ_one := by
    ext x
    change oLevW N.toWeakModule 0 W.vacuum (x : M) = x
    rw [oLevW_homogeneous N.toWeakModule 0 W.vacuum_mem_grading_zero,
      N.toWeakModule.vacuum_YM, mode_one]
    simp
  ρ_mul := by
    intro a b
    ext x
    exact oOmega_zhuMul_mult N.toWeakModule a b
      (lev_zero_le_Omega (bottomAdmLev N) x.2)

/-- Any weak submodule is invariant under the sum defining an arbitrary
zero mode. -/
theorem oLevW_mem_modeSubmodule (A : WeakModule W M)
    (P : Submodule (modeAlg A) M) (v : 𝒱) {x : M} (hx : x ∈ P) :
    oLevW A 0 v x ∈ P := by
  have hv : v ∈ ⨆ w, W.grading w := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction _
    (motive := fun v => oLevW A 0 v x ∈ P) hv ?_ ?_ ?_
  · intro w a ha
    rw [oLevW_homogeneous A 0 ha, add_zero]
    exact (ofR A P).act_mem a (w - 1) hx
  · simp
  · intro a b ha hb
    simpa using P.add_mem ha hb

/-- Zhu semisimplicity supplies a zero-mode-stable complement inside level
zero to its intersection with any weak submodule. -/
theorem exists_bottom_complement
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (N : AdmissibleModule W M) (P : Submodule (modeAlg N.toWeakModule) M) :
    ∃ S : Submodule ℂ M, S ≤ N.lev 0 ∧
      (∀ ⦃a : 𝒱⦄ ⦃w : ℤ⦄, a ∈ W.grading w → ∀ ⦃x : M⦄,
        x ∈ S → N.toWeakModule.act a (w - 1) x ∈ S) ∧
      Disjoint (P.restrictScalars ℂ) S ∧
      (P.restrictScalars ℂ ⊓ N.lev 0) ⊔ S = N.lev 0 := by
  let U := bottomAMod N
  letI := instRingA W
  letI : Module (VOA.A W) (N.lev 0) := U.moduleA
  letI : IsSemisimpleRing (VOA.A W) := hss
  let B : Submodule (VOA.A W) (N.lev 0) :=
    { carrier := {x | (x : M) ∈ P}
      zero_mem' := P.zero_mem
      add_mem' := fun hx hy => P.add_mem hx hy
      smul_mem' := by
        intro a x hx
        obtain ⟨v, rfl⟩ := VOA.mk_surjective W a
        exact oLevW_mem_modeSubmodule N.toWeakModule P v hx }
  obtain ⟨C, hC⟩ := exists_isCompl B
  let T := U.toAModSubmodule C
  let S := T.carrier.map (N.lev 0).subtype
  have hS (x : N.lev 0) : (x : M) ∈ S ↔ x ∈ C := by
    constructor
    · rintro ⟨y, hy, he⟩
      have : y = x := Subtype.ext he
      simpa only [this] using hy
    · intro hx; exact ⟨x, hx, rfl⟩
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, _, rfl⟩; exact y.2
  · intro a w ha x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hm := T.ρ_mem (VOA.mk W a) hy
    refine ⟨U.ρ (VOA.mk W a) y, hm, ?_⟩
    change oLevW N.toWeakModule 0 a (y : M) = _
    rw [oLevW_homogeneous N.toWeakModule 0 ha, add_zero]
    rfl
  · apply Submodule.disjoint_def.mpr
    intro x hx hxS
    obtain ⟨y, hy, rfl⟩ := hxS
    have hz : y = 0 := (Submodule.disjoint_def.mp hC.disjoint) y hx hy
    exact congrArg Subtype.val hz
  · apply le_antisymm
    · exact sup_le inf_le_right (by rintro x ⟨y, _, rfl⟩; exact y.2)
    · intro x hx
      have ht : (⟨x, hx⟩ : N.lev 0) ∈ B ⊔ C := by rw [hC.sup_eq_top]; trivial
      obtain ⟨b, hb, c, hc, he⟩ := Submodule.mem_sup.mp ht
      exact Submodule.mem_sup.mpr
        ⟨b, ⟨hb, b.2⟩, c, (hS c).mpr hc, congrArg Subtype.val he⟩

/-- A bottom complement lifts to a complement of a simple kernel with a
simple quotient, provided both factors are detected at admissible level zero.
This includes self-extensions; the middle module is never assumed ordinary. -/
theorem exists_isCompl_of_semisimpleZhu_levelZero
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (N : AdmissibleModule W M) (P : Submodule (modeAlg N.toWeakModule) M)
    (hP : IsAtom P) (hQ : P ⋖ ⊤)
    (hbottom : ∃ y : M, y ∈ P ∧ y ∈ N.lev 0 ∧ y ≠ 0)
    (htop : ¬ N.lev 0 ≤ P.restrictScalars ℂ) :
    ∃ Q : Submodule (modeAlg N.toWeakModule) M, IsCompl P Q := by
  obtain ⟨S, hS0, hSo, hd, hsum⟩ := exists_bottom_complement hss N P
  let Q := toR N.toWeakModule (genSub (N := N) S)
  have hdis : Disjoint P Q := by
    rw [disjoint_iff]
    by_contra hn
    have he : P ⊓ Q = P := (hP.le_iff_eq hn).mp inf_le_left
    have hPQ : P ≤ Q := he ▸ inf_le_right
    obtain ⟨y, hyP, hy0, hyne⟩ := hbottom
    have hyS := genSub_le_bottom S hS0 hSo (hPQ hyP) hy0
    exact hyne ((Submodule.disjoint_def.mp hd) y hyP hyS)
  have hsup : P ⊔ Q = ⊤ := by
    rcases hQ.wcovBy.eq_or_eq le_sup_left le_top with he | he
    · exfalso
      apply htop
      rw [← hsum]
      refine sup_le inf_le_left ?_
      intro x hx
      have hxQ : x ∈ Q := le_genSub S hx
      have hxS : x ∈ P ⊔ Q := Submodule.mem_sup_right hxQ
      rwa [he] at hxS
    · exact he
  exact ⟨Q, ⟨hdis, codisjoint_iff.mpr hsup⟩⟩

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne
open PlusSplitting

/-- The proved level-zero version of equal-bottom splitting. It retains
arbitrary mode submodules, but requires a common admissible bottom grading. -/
def V2mPlusLevelZeroSplitting : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M]
      (N : AdmissibleModule (V2mPlus m hm) M)
      (P : Submodule (modeAlg N.toWeakModule) M),
      IsAtom P → P ⋖ ⊤ →
      (∃ y : M, y ∈ P ∧ y ∈ N.lev 0 ∧ y ≠ 0) →
      (¬N.lev 0 ≤ P.restrictScalars ℂ) →
      ∃ Q : Submodule (modeAlg N.toWeakModule) M, IsCompl P Q

theorem levelZeroSplitting_of_zhuSemisimple (hzhu : ZhuV2mPlusSemisimple) :
    V2mPlusLevelZeroSplitting := by
  intro m hm hm2 M _ _ N P hP hQ hb ht
  exact exists_isCompl_of_semisimpleZhu_levelZero (hzhu m hm hm2) N P hP hQ hb ht

theorem levelZeroSplitting_of_dimension_characters
    (hdim : V2mPlusZhuDimensionBound) (hchar : V2mPlusZhuDistinctCharacters) :
    V2mPlusLevelZeroSplitting :=
  levelZeroSplitting_of_zhuSemisimple
    (zhuV2mPlusSemisimple_of_dimension_characters hdim hchar)

end VOA.Classification.COne
