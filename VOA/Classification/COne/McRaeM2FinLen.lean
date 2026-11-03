import VOA.Classification.COne.McRaeM2Graded
import VOA.Classification.COne.McRaeM1Main
import VOA.Classification.COne.AdmissibleOrdinaryC2
import VOA.Classification.COne.PlusRat2DualSwap

/-!
# McRae's route: finite-length weak modules of a `C₂`-cofinite VOA are graded

For a `C₂`-cofinite VOA `W` and a weak module `A` of finite length (over its mode algebra), the
generalized `L₀`-eigenspaces are finite-dimensional and give `A` the structure of a graded weak
module (`C2Rigid.GWModule`) with the generalized-eigenspace grading:

* `isSimple_subquotient` — a covering pair `Q ⋖ P` of submodules gives a simple weak module `P/Q`;
* `finiteDimensional_inf_maxGen` — `P ∩ X_[α]` is finite-dimensional for every submodule `P`
  (well-founded induction on `P`; the simple factors are ordinary by ABD, and generalized
  eigenspaces are exact);
* `gwOfFiniteLength hC2 A hA : GWModule W X`, with `toWeakModule = A`, weight spaces the
  generalized eigenspaces, and `isGenGraded_gwOfFiniteLength`.

Consequently every finite-length weak module (in particular every Huang cover) has a contragredient
`contra (gwOfFiniteLength hC2 A hA)` and an annihilator anti-isomorphism `perpIsoGen`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.ABDWeakAdmissible
open VOA.Huang.LogRemovalAdmissible

universe u
variable {V X : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup X] [Module ℂ X] {W : VertexOperatorAlgebra V}

section Subquotient
variable (A : WeakModule W X) (P Q : Submodule (modeAlg A) X)

/-- The submodule `P` as a weak module. -/
abbrev subW : WeakModule W (ofR A P).carrier := WeakModule.submodule A (ofR A P)

/-- `Q ∩ P`, as a weak submodule of `P`. -/
def subInW : WeakModule.Submodule' (subW A P) where
  carrier := (Q.restrictScalars ℂ).comap (ofR A P).carrier.subtype
  act_mem u n x hx := by
    change mode (A.YM u) n (x : X) ∈ Q
    exact (ofR A Q).act_mem u n hx

/-- The subquotient `P / (Q ∩ P)` as a weak module. -/
abbrev quoW : WeakModule W ((ofR A P).carrier ⧸ (subInW A P Q).carrier) :=
  WeakModule.quotient (subW A P) (subInW A P Q)

theorem L0_quoW_mk (y : (ofR A P).carrier) :
    L0 (quoW A P Q) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (⟨L0 A y, (ofR A P).act_mem _ _ y.2⟩ : (ofR A P).carrier) :=
  WeakModule.quotient_act_mk (subW A P) (subInW A P Q) W.conformalVector 1 y

/-- A covering pair of submodules gives a simple weak module. -/
theorem isSimple_subquotient (hQP : Q ⋖ P) :
    Nontrivial ((ofR A P).carrier ⧸ (subInW A P Q).carrier) ∧
      ∀ R : WeakModule.Submodule' (quoW A P Q), R.carrier = ⊥ ∨ R.carrier = ⊤ := by
  classical
  obtain ⟨x, hxP, hxQ⟩ := SetLike.exists_of_lt hQP.lt
  refine ⟨⟨Submodule.Quotient.mk ⟨x, hxP⟩, 0, fun h => hxQ ?_⟩, ?_⟩
  · have := (Submodule.Quotient.mk_eq_zero _).mp h
    exact this
  intro R
  -- the preimage of `R` in `X`
  let Rt : WeakModule.Submodule' A :=
    { carrier :=
        { carrier := {z | ∃ h : z ∈ P, Submodule.Quotient.mk (⟨z, h⟩ : (ofR A P).carrier) ∈
              R.carrier}
          add_mem' := by
            rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
            refine ⟨P.add_mem ha hb, ?_⟩
            have := R.carrier.add_mem ha' hb'
            rwa [← Submodule.Quotient.mk_add] at this
          zero_mem' := ⟨P.zero_mem, by
            have := R.carrier.zero_mem
            rwa [← Submodule.Quotient.mk_zero] at this⟩
          smul_mem' := by
            rintro c a ⟨ha, ha'⟩
            refine ⟨P.smul_of_tower_mem c ha, ?_⟩
            have := R.carrier.smul_mem c ha'
            rwa [← Submodule.Quotient.mk_smul] at this }
      act_mem := by
        rintro u n z ⟨hz, hz'⟩
        refine ⟨(ofR A P).act_mem u n hz, ?_⟩
        have := R.act_mem u n hz'
        rw [WeakModule.quotient_act_mk] at this
        exact this }
  have hQle : Q ≤ toR A Rt := by
    intro z hz
    refine ⟨hQP.le hz, ?_⟩
    rw [(Submodule.Quotient.mk_eq_zero _).mpr (show _ ∈ (subInW A P Q).carrier from hz)]
    exact R.carrier.zero_mem
  have hleP : toR A Rt ≤ P := fun z hz => hz.1
  rcases hQle.lt_or_eq with hlt | heq
  · right
    have hRP : toR A Rt = P := by
      by_contra hne
      exact hQP.2 hlt (lt_of_le_of_ne hleP hne)
    refine eq_top_iff.mpr fun y _ => ?_
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      have hy : (y : X) ∈ toR A Rt := by rw [hRP]; exact y.2
      obtain ⟨_, hy'⟩ := hy
      exact hy'
  · left
    refine eq_bot_iff.mpr fun y hy => ?_
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      have hyR : (y : X) ∈ toR A Rt := ⟨y.2, hy⟩
      rw [← heq] at hyR
      exact (Submodule.mem_bot ℂ).mpr ((Submodule.Quotient.mk_eq_zero _).mpr hyR)

end Subquotient

/-- In a `C₂`-cofinite VOA, every simple weak module has finite-dimensional generalized
eigenspaces (it is ordinary, by ABD). -/
theorem finiteDimensional_maxGen_of_simple (hC2 : C2Cofinite W) {Y : Type u} [AddCommGroup Y]
    [Module ℂ Y] (B : WeakModule W Y)
    (hB : Nontrivial Y ∧ ∀ R : WeakModule.Submodule' B, R.carrier = ⊥ ∨ R.carrier = ⊤) (α : ℂ) :
    FiniteDimensional ℂ ((L0 B).maxGenEigenspace α) := by
  obtain ⟨N, rfl⟩ := AdmissibleOrdinary.abdIrreducibleWeakIsOrdinary_of_weakIsAdmissible
    abdWeakIsAdmissible hC2 B hB
  rw [PlusRat2Dual.maxGen_eq_weight N α]
  exact N.finrank α

/-- **Generalized eigenspaces of finite-length modules are finite-dimensional**, for a
`C₂`-cofinite VOA: `P ∩ X_[α]` is finite-dimensional for every submodule `P`. -/
theorem finiteDimensional_inf_maxGen (hC2 : C2Cofinite W) (A : WeakModule W X)
    (hA : IsFiniteLength (modeAlg A) X) (α : ℂ) (P : Submodule (modeAlg A) X) :
    FiniteDimensional ℂ ↥(P.restrictScalars ℂ ⊓ (L0 A).maxGenEigenspace α) := by
  classical
  obtain ⟨hN, hArt⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hA
  haveI : WellFoundedGT (Submodule (modeAlg A) X) := isNoetherian_iff'.mp hN
  haveI : WellFoundedLT (Submodule (modeAlg A) X) := hArt
  induction P using WellFoundedLT.induction with
  | _ P ih =>
  by_cases hP : P = ⊥
  · subst hP
    have : (⊥ : Submodule (modeAlg A) X).restrictScalars ℂ ⊓ (L0 A).maxGenEigenspace α = ⊥ := by
      rw [Submodule.restrictScalars_bot, bot_inf_eq]
    rw [this]
    infer_instance
  -- a maximal proper submodule `Q ⋖ P`
  obtain ⟨Q, hQlt, hQmax⟩ := (wellFounded_gt (α := Submodule (modeAlg A) X)).has_min
    {Q | Q < P} ⟨⊥, bot_lt_iff_ne_bot.mpr hP⟩
  have hQP : Q ⋖ P := ⟨hQlt, fun c hQc hcP => hQmax c hcP hQc⟩
  haveI hQfd := ih Q hQlt
  -- the map to the simple subquotient
  let U := P.restrictScalars ℂ ⊓ (L0 A).maxGenEigenspace α
  let f : U →ₗ[ℂ] ((ofR A P).carrier ⧸ (subInW A P Q).carrier) :=
    (subInW A P Q).carrier.mkQ ∘ₗ
      { toFun := fun v => (⟨(v : X), v.2.1⟩ : (ofR A P).carrier)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hf : ∀ v : U, f v = Submodule.Quotient.mk (⟨(v : X), v.2.1⟩ : (ofR A P).carrier) :=
    fun _ => rfl
  haveI hS := finiteDimensional_maxGen_of_simple hC2 (quoW A P Q)
    (isSimple_subquotient A P Q hQP) α
  -- the kernel embeds into `Q ∩ X_[α]`
  let g : LinearMap.ker f →ₗ[ℂ] ↥(Q.restrictScalars ℂ ⊓ (L0 A).maxGenEigenspace α) :=
    { toFun := fun v => ⟨((v : U) : X), by
          have h0 : f v = 0 := v.2
          rw [hf] at h0
          exact Submodule.mem_inf.mpr
            ⟨(Submodule.Quotient.mk_eq_zero (subInW A P Q).carrier).mp h0, (v : U).2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun z : ↥(Q.restrictScalars ℂ ⊓ (L0 A).maxGenEigenspace α) => (z : X)) h
  haveI : FiniteDimensional ℂ (LinearMap.ker f) := Module.Finite.of_injective g hg
  -- the image lies in the generalized eigenspace of the subquotient
  have hcomap : (((L0 (quoW A P Q)).maxGenEigenspace α).comap f) = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    change f v ∈ (L0 (quoW A P Q)).maxGenEigenspace α
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp v.2.2
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨k, ?_⟩
    have hpow : ∀ (j : ℕ) (y : (ofR A P).carrier),
        ((L0 (quoW A P Q) - α • 1) ^ j) (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk (⟨((L0 A - α • 1) ^ j) (y : X),
            by
              induction j with
              | zero => exact y.2
              | succ j ihj =>
                rw [pow_succ', Module.End.mul_apply]
                exact Submodule.sub_mem _ ((ofR A P).act_mem _ _ ihj)
                  (Submodule.smul_mem _ _ ihj)⟩ : (ofR A P).carrier) := by
      intro j
      induction j with
      | zero => intro y; rfl
      | succ j ihj =>
        intro y
        rw [pow_succ', Module.End.mul_apply, ihj, LinearMap.sub_apply, L0_quoW_mk,
          LinearMap.smul_apply, Module.End.one_apply, ← Submodule.Quotient.mk_smul,
          ← Submodule.Quotient.mk_sub]
        congr 1
        apply Subtype.ext
        simp only [Submodule.coe_sub, Submodule.coe_smul, pow_succ', Module.End.mul_apply,
          LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hf, hpow]
    simp only [hk]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.zero_mem _)
  haveI : FiniteDimensional ℂ (((L0 (quoW A P Q)).maxGenEigenspace α).comap f) := inferInstance
  rw [hcomap] at this
  exact Module.Finite.equiv (Submodule.topEquiv)

/-- **A finite-length weak module of a `C₂`-cofinite VOA is a graded weak module**, graded by
its generalized `L₀`-eigenspaces. -/
def gwOfFiniteLength (hC2 : C2Cofinite W) (A : WeakModule W X)
    (hA : IsFiniteLength (modeAlg A) X) : GWModule W X where
  toWeakModule := A
  weight α := (L0 A).maxGenEigenspace α
  isInternal := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Module.End.independent_maxGenEigenspace (L0 A))
    have h := eq_iSup_inf_maxGenEigenspace_of_locally_finite (L0 A)
      (McRaeM1.L0_locallyFinite_of_c2 hC2 A) ⊤ (fun _ _ => Submodule.mem_top)
    simp only [top_inf_eq] at h
    exact h.symm
  mode_mem_weight' := by
    intro β v hv α x hx n
    have h := ABDWeakAdmissible.mode_mem_maxGenEigenspace A hv n hx
    have he : α + ((β - n - 1 : ℤ) : ℂ) = α + (β : ℂ) - n - 1 := by push_cast; ring
    rwa [he] at h
  finrank α := by
    have h := finiteDimensional_inf_maxGen hC2 A hA α ⊤
    rw [Submodule.restrictScalars_top, top_inf_eq] at h
    exact h
  boundedBelow := by
    obtain ⟨b, hb⟩ := exists_uniform_weak_spectrum_lower_bound (W := W) hC2
    exact ⟨b, fun α hα => hb A α hα⟩

@[simp] theorem gwOfFiniteLength_toWeakModule (hC2 : C2Cofinite W) (A : WeakModule W X)
    (hA : IsFiniteLength (modeAlg A) X) : (gwOfFiniteLength hC2 A hA).toWeakModule = A := rfl

theorem gwOfFiniteLength_weight (hC2 : C2Cofinite W) (A : WeakModule W X)
    (hA : IsFiniteLength (modeAlg A) X) (α : ℂ) :
    (gwOfFiniteLength hC2 A hA).weight α = (L0 A).maxGenEigenspace α := rfl

theorem isGenGraded_gwOfFiniteLength (hC2 : C2Cofinite W) (A : WeakModule W X)
    (hA : IsFiniteLength (modeAlg A) X) : IsGenGraded (gwOfFiniteLength hC2 A hA) :=
  fun _ => le_rfl

end VOA.C2Rigid
