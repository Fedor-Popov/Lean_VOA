import VOA.Classification.COne.PlusRat2DualPerp
import VOA.Modules.LogVModule

/-! # Contragredient symmetry of two-step splitting

For a `C₂`-cofinite VOA, splitting of every extension with simple kernel of bottom `hj` and simple
quotient of bottom `hi` implies splitting of every extension with kernel bottom `hi` and quotient
bottom `hj` (`pairSplit_swap`, for `hi ≠ hj`).

Proof.  By `exists_ordinary_or_split` the middle module is ordinary (or already split).  The
annihilator `S ↦ S^⊥` is an order anti-isomorphism onto the submodule lattice of the
contragredient (`perpIso`); it exchanges atoms and coatoms, and it exchanges the factor bottoms
(`factorBottom_perp_bot`, `factorBottom_perp_top`).  A complement of `P^⊥` pulls back to a
complement of `P`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat2Dual
open PlusSplitting ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible PlusRational

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- For an ordinary module the generalized `L(0)`-eigenspaces are the weight spaces. -/
theorem maxGen_eq_weight {X : Type u} [AddCommGroup X] [Module ℂ X] (N : OrdVModule W X)
    (μ : ℂ) : (L0 N.toWeakModule).maxGenEigenspace μ = N.weight μ :=
  (N.toLog.weight_eq_maxGenEigenspace μ).symm

section Factor
variable (O : OrdVModule W M)

theorem exists_lofD_of_mem {μ : ℂ} {f : RestrictedDual O} (hf : f ∈ (Dm O).weight μ) :
    ∃ g : Module.Dual ℂ (O.weight μ), lofD O μ g = f := hf

/-- A weight vector outside a submodule is separated by a functional killing the submodule. -/
theorem exists_sep (S : Submodule (modeAlg O.toWeakModule) M) {μ : ℂ} {v : M}
    (hv : v ∈ O.weight μ) (hvS : v ∉ S) :
    ∃ g : Module.Dual ℂ (O.weight μ), g ⟨v, hv⟩ ≠ 0 ∧ lofD O μ g ∈ perpA O S := by
  let U := O.weight μ
  let Sμ : Submodule ℂ U := (S.restrictScalars ℂ).comap U.subtype
  have hc : (⟨v, hv⟩ : U) ∉ Sμ := hvS
  obtain ⟨g, hg, hgS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
  refine ⟨g, hg, ?_⟩
  apply lofD_mem_perpA
  intro w hw
  have : g w ∈ Sμ.map g := ⟨w, hw, rfl⟩
  rw [hgS] at this
  exact (Submodule.mem_bot ℂ).mp this

theorem lofD_eq_zero_iff {μ : ℂ} (g : Module.Dual ℂ (O.weight μ)) :
    lofD O μ g = 0 ↔ g = 0 := by
  constructor
  · intro h
    have := congrArg (fc O μ) h
    rw [fc_lofD] at this
    rw [this]
    exact map_zero _
  · rintro rfl
    exact map_zero (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (O.weight β)) μ)

/-- Factor weights of the annihilator as a submodule. -/
theorem factorWeight_perp_bot (P : Submodule (modeAlg O.toWeakModule) M) (μ : ℂ) :
    FactorWeight (Dm O).toWeakModule ⊥ (perpA O P) μ ↔
      FactorWeight O.toWeakModule P ⊤ μ := by
  unfold FactorWeight
  rw [maxGen_eq_weight, maxGen_eq_weight, not_iff_not]
  constructor
  · intro h v ⟨_, hv⟩
    by_contra hvP
    obtain ⟨g, hg, hgP⟩ := exists_sep O P hv hvP
    have h0 : lofD O μ g ∈ (⊥ : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)) :=
      h ⟨hgP, ⟨g, rfl⟩⟩
    rw [Submodule.mem_bot, lofD_eq_zero_iff] at h0
    exact hg (by rw [h0]; rfl)
  · intro h f ⟨hfP, hf⟩
    obtain ⟨g, rfl⟩ := exists_lofD_of_mem O hf
    change lofD O μ g ∈ (⊥ : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O))
    rw [Submodule.mem_bot, lofD_eq_zero_iff]
    ext v
    have hvP : (v : M) ∈ P := h ⟨Submodule.mem_top, v.2⟩
    have := hfP _ hvP
    rw [pr_of_mem O v.2] at this
    erw [fc_lofD] at this
    exact this

/-- Factor weights of the quotient by the annihilator. -/
theorem factorWeight_perp_top (P : Submodule (modeAlg O.toWeakModule) M) (μ : ℂ) :
    FactorWeight (Dm O).toWeakModule (perpA O P) ⊤ μ ↔
      FactorWeight O.toWeakModule ⊥ P μ := by
  unfold FactorWeight
  rw [maxGen_eq_weight, maxGen_eq_weight, not_iff_not]
  constructor
  · intro h v ⟨hvP, hv⟩
    change v ∈ (⊥ : Submodule (modeAlg O.toWeakModule) M)
    rw [Submodule.mem_bot]
    have hall : ∀ g : Module.Dual ℂ (O.weight μ), g ⟨v, hv⟩ = 0 := by
      intro g
      have hg := h ⟨Submodule.mem_top, ⟨g, rfl⟩⟩
      have := hg v hvP
      rw [pr_of_mem O hv] at this
      erw [fc_lofD] at this
      exact this
    have h0 : (⟨v, hv⟩ : O.weight μ) = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℂ _).mp hall
    exact congrArg Subtype.val h0
  · intro h f ⟨_, hf⟩ x hx
    obtain ⟨g, rfl⟩ := exists_lofD_of_mem O hf
    rw [dualPairing_lof]
    have hc : cmp O μ x ∈ (⊥ : Submodule (modeAlg O.toWeakModule) M) :=
      h ⟨cmp_mem_modeSub O P hx μ, cmp_mem O μ x⟩
    rw [Submodule.mem_bot] at hc
    have he : internalProjTo O.isInternal μ x = 0 := Subtype.ext hc
    rw [he, map_zero]

theorem factorBottom_perp_bot (P : Submodule (modeAlg O.toWeakModule) M) (h : ℂ) :
    FactorBottom (Dm O).toWeakModule ⊥ (perpA O P) h ↔ FactorBottom O.toWeakModule P ⊤ h := by
  unfold FactorBottom
  simp only [factorWeight_perp_bot]

theorem factorBottom_perp_top (P : Submodule (modeAlg O.toWeakModule) M) (h : ℂ) :
    FactorBottom (Dm O).toWeakModule (perpA O P) ⊤ h ↔ FactorBottom O.toWeakModule ⊥ P h := by
  unfold FactorBottom
  simp only [factorWeight_perp_top]

end Factor

/-- Splitting of every two-step extension with the given kernel and quotient bottoms. -/
def PairSplit (W : VertexOperatorAlgebra V) (hi hj : ℂ) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
    (P : Submodule (modeAlg A) M), IsAtom P → P ⋖ ⊤ →
    FactorBottom A ⊥ P hi → FactorBottom A P ⊤ hj → ∃ Q : Submodule (modeAlg A) M, IsCompl P Q

/-- **Contragredient symmetry**: splitting for (kernel `hj`, quotient `hi`) implies splitting
for (kernel `hi`, quotient `hj`). -/
theorem pairSplit_swap (hC2 : C2Cofinite W) {hi hj : ℂ} (hne : hi ≠ hj)
    (h : PairSplit W hj hi) : PairSplit W hi hj := by
  intro M _ _ A P hP hQ hb ht
  rcases exists_ordinary_or_split hC2 A P hP hQ hne hb ht with hs | ⟨O, rfl⟩
  · exact hs
  let φ := perpIso O
  have hP' : IsAtom (perpA O P) := by
    have h1 : φ P ⋖ φ ⊤ := (apply_covBy_apply_iff φ).mpr hQ
    rw [map_top, perpIso_apply] at h1
    change OrderDual.toDual (perpA O P) ⋖ OrderDual.toDual ⊥ at h1
    rw [toDual_covBy_toDual_iff] at h1
    exact bot_covBy_iff.mp h1
  have hQ' : perpA O P ⋖ ⊤ := by
    have h1 : φ ⊥ ⋖ φ P := (apply_covBy_apply_iff φ).mpr (bot_covBy_iff.mpr hP)
    rw [map_bot, perpIso_apply] at h1
    change OrderDual.toDual ⊤ ⋖ OrderDual.toDual (perpA O P) at h1
    rwa [toDual_covBy_toDual_iff] at h1
  obtain ⟨R, hR⟩ := h (Dm O).toWeakModule (perpA O P) hP' hQ'
    ((factorBottom_perp_bot O P hj).mpr ht) ((factorBottom_perp_top O P hi).mpr hb)
  refine ⟨perpD O R, ?_⟩
  rw [OrderIso.isCompl_iff φ, perpIso_apply]
  change IsCompl (OrderDual.toDual (perpA O P)) (OrderDual.toDual (perpA O (perpD O R)))
  rw [perpA_perpD, isCompl_toDual_iff]
  exact hR

end VOA.Classification.COne.PlusRat2Dual
