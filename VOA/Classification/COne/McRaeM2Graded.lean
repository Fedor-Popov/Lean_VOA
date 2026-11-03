import VOA.Classification.COne.McRaeM2Perp

/-!
# McRae's route: the generalized-eigenspace grading and graded submodules

For a graded weak module `N` (`C2Rigid.GWModule`) whose grading refines the generalized
`L₀`-eigenspaces, `N.weight α ≤ (L0 N).maxGenEigenspace α` (`IsGenGraded N`):

* `weight_eq_maxGen` — then `N.weight α` IS the generalized eigenspace;
* `L0_locallyFinite` — `L₀` is locally finite (from the finite-dimensional grading);
* `subsGraded_of_isGenGraded` — every mode submodule is graded (`SubsGraded N`);
* `L0_contra_lof` — on `(M_α)*` the contragredient `L₀` is the transpose of `L₀|_{M_α}`;
* `isGenGraded_contra` — the contragredient again has the generalized-eigenspace grading;
* `perpIsoGen` — for such `N`, `S ↦ S^⊥` is an order anti-isomorphism
  `Sub(N) ≃o Sub(N')ᵒᵈ`, with no further hypothesis.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.PlusRat2Dual (mem_P_mode)
open VOA.Huang.LogRemovalAdmissible

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The grading refines the generalized `L₀`-eigenspaces. -/
def IsGenGraded (N : GWModule W M) : Prop :=
  ∀ α : ℂ, N.weight α ≤ (L0 N.toWeakModule).maxGenEigenspace α

section Basic
variable (N : GWModule W M)

/-- `L₀` preserves each graded piece. -/
theorem L0_mem_weight {α : ℂ} {x : M} (hx : x ∈ N.weight α) : L0 N.toWeakModule x ∈ N.weight α := by
  have h := mode_mem_weight N W.conformal_mem hx 1
  have he : α + ((2 : ℤ) : ℂ) - ((1 : ℤ) : ℂ) - 1 = α := by push_cast; ring
  rw [he] at h
  exact h

/-- `L₀` is locally finite on a graded weak module. -/
theorem L0_locallyFinite (x : M) : ∃ S : Submodule ℂ M,
    FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ y ∈ S, L0 N.toWeakModule y ∈ S := by
  classical
  obtain ⟨s, -, hsum⟩ := exists_sum_cmp N x
  haveI : ∀ α, FiniteDimensional ℂ (N.weight α) := N.finrank
  refine ⟨s.sup N.weight, inferInstance, ?_, ?_⟩
  · rw [← hsum]
    exact Submodule.sum_mem _ fun α hα => Finset.le_sup (f := N.weight) hα (cmp_mem N α x)
  · have hle : s.sup N.weight ≤ (s.sup N.weight).comap (L0 N.toWeakModule) := by
      refine Finset.sup_le fun α hα z hz => ?_
      exact Finset.le_sup (f := N.weight) hα (L0_mem_weight N hz)
    exact fun y hy => hle hy

/-- For a generalized-eigenspace grading, each piece IS the generalized eigenspace. -/
theorem mem_weight_of_mem_maxGen (hN : IsGenGraded N) {α : ℂ} {v : M}
    (hv : v ∈ (L0 N.toWeakModule).maxGenEigenspace α) : v ∈ N.weight α := by
  classical
  obtain ⟨s, hs0, hsum⟩ := exists_sum_cmp N v
  set d := v - cmp N α v with hd
  have hd1 : d ∈ (L0 N.toWeakModule).maxGenEigenspace α :=
    Submodule.sub_mem _ hv (hN α (cmp_mem N α v))
  have hsplit : v = ∑ β ∈ s.filter (· ≠ α), cmp N β v + cmp N α v := by
    conv_lhs => rw [← hsum]
    rw [← Finset.sum_filter_add_sum_filter_not s (· ≠ α)]
    congr 1
    by_cases hα : α ∈ s
    · rw [Finset.sum_eq_single_of_mem α (by simp [hα])]
      intro β hβ hne
      simp only [ne_eq, Decidable.not_not, Finset.mem_filter] at hβ
      exact absurd hβ.2 hne
    · rw [hs0 α hα, Finset.sum_eq_zero]
      intro β hβ
      simp only [ne_eq, Decidable.not_not, Finset.mem_filter] at hβ
      exact absurd (hβ.2 ▸ hβ.1) hα
  have hd2 : d ∈ ⨆ (β : ℂ) (_ : β ≠ α), (L0 N.toWeakModule).maxGenEigenspace β := by
    have : d = ∑ β ∈ s.filter (· ≠ α), cmp N β v := by
      rw [hd]; exact sub_eq_of_eq_add hsplit
    rw [this]
    refine Submodule.sum_mem _ fun β hβ => ?_
    have hne : β ≠ α := (Finset.mem_filter.mp hβ).2
    exact (le_iSup₂ (f := fun (β : ℂ) (_ : β ≠ α) => (L0 N.toWeakModule).maxGenEigenspace β)
      β hne) (hN β (cmp_mem N β v))
  have h0 : d = 0 := by
    have hdisj := (Module.End.independent_maxGenEigenspace (L0 N.toWeakModule)) α
    exact (Submodule.disjoint_def.mp hdisj) d hd1 hd2
  have : v = cmp N α v := sub_eq_zero.mp h0
  rw [this]
  exact cmp_mem N α v

theorem weight_eq_maxGen (hN : IsGenGraded N) (α : ℂ) :
    N.weight α = (L0 N.toWeakModule).maxGenEigenspace α :=
  le_antisymm (hN α) fun _ hv => mem_weight_of_mem_maxGen N hN hv

/-- For a generalized-eigenspace grading, every mode submodule is graded. -/
theorem subsGraded_of_isGenGraded (hN : IsGenGraded N) : SubsGraded N := by
  intro P x hx α
  let P' : Submodule ℂ M := P.restrictScalars ℂ
  have hP' : ∀ y ∈ P', L0 N.toWeakModule y ∈ P' := fun y hy => mem_P_mode _ P _ 1 hy
  have hdec := eq_iSup_inf_maxGenEigenspace_of_locally_finite (L0 N.toWeakModule)
    (L0_locallyFinite N) P' hP'
  have hx' : x ∈ ⨆ μ : ℂ, P' ⊓ (L0 N.toWeakModule).maxGenEigenspace μ := by
    rw [← hdec]; exact hx
  change cmp N α x ∈ P'
  refine Submodule.iSup_induction _ (motive := fun y => cmp N α y ∈ P') hx' ?_ ?_ ?_
  · intro μ y hy
    have hyw : y ∈ N.weight μ := mem_weight_of_mem_maxGen N hN hy.2
    by_cases hμ : μ = α
    · subst hμ; rw [cmp_of_mem N hyw]; exact hy.1
    · rw [cmp_of_mem_ne N hyw hμ]; exact P'.zero_mem
  · have h := cmp_smul N α 0 (0 : M)
    rw [zero_smul, zero_smul] at h
    show cmp N α 0 ∈ P'
    rw [h]; exact P'.zero_mem
  · intro a b ha hb
    show cmp N α (a + b) ∈ P'
    rw [cmp_add]; exact P'.add_mem ha hb

end Basic

section Contra
variable (N : GWModule W M)

/-- `L₀` restricted to a graded piece. -/
def L0w (α : ℂ) : Module.End ℂ (N.weight α) :=
  (L0 N.toWeakModule).restrict (fun _ hx => L0_mem_weight N hx)

@[simp] theorem L0w_apply (α : ℂ) (y : N.weight α) :
    ((L0w N α y : N.weight α) : M) = L0 N.toWeakModule y := rfl

theorem L0w_sub_pow_apply (α : ℂ) (k : ℕ) (y : N.weight α) :
    ((((L0w N α - α • 1) ^ k) y : N.weight α) : M) = ((L0 N.toWeakModule - α • 1) ^ k) y := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
    rfl

/-- **The contragredient `L₀` on `(M_α)*` is the transpose of `L₀|_{M_α}`.** -/
theorem L0_contra_lof (α : ℂ) (g : Module.Dual ℂ (N.weight α)) :
    L0 (contra N).toWeakModule (lofD N α g) = lofD N α (g ∘ₗ L0w N α) := by
  show mode (YMdual N W.conformalVector) 1
      (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α g) = _
  rw [mode_YMdual_homogeneous N W.conformal_mem 1, dualModeEndo_lof,
    show dualOutIdx 2 1 α = α from by simp only [dualOutIdx]; ring]
  congr 1
  refine LinearMap.ext (fun y => ?_)
  show dualCompMap N 2 W.conformalVector 1 α g ((N.weight α).subtype y) = g (L0w N α y)
  rw [dualCompMap_apply, show (2 : ℤ).toNat + 1 = 3 from rfl,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have hkill : ∀ j : ℕ,
      g (internalProjTo N.isInternal α
          (mode (N.YM ((W.L 1 ^ (j + 1)) W.conformalVector)) (2 * 2 - 1 - 2 - ((j + 1 : ℕ) : ℤ))
            ((N.weight α).subtype y))) = 0 := by
    intro j
    rw [L_one_pow_succ_conformalVector, map_zero]
    show g (internalProjTo N.isInternal α (mode (0 : (Module.End ℂ M)⟦z^±⟧)
        (2 * 2 - 1 - 2 - ((j + 1 : ℕ) : ℤ)) ((N.weight α).subtype y))) = 0
    rw [show mode (0 : (Module.End ℂ M)⟦z^±⟧) (2 * 2 - 1 - 2 - ((j + 1 : ℕ) : ℤ)) = 0 from rfl]
    simp
  have h0term : g (internalProjTo N.isInternal α
      (mode (N.YM ((W.L 1 ^ (0:ℕ)) W.conformalVector)) (2 * 2 - 1 - 2 - ((0:ℕ) : ℤ))
        ((N.weight α).subtype y))) = g (L0w N α y) := by
    rw [pow_zero, Module.End.one_apply, show (2 * 2 - 1 - 2 - ((0:ℕ):ℤ) : ℤ) = 1 from by norm_num]
    congr 1
    exact internalProjTo_coe N.isInternal α (L0w N α y)
  rw [show ((1:ℕ)) = 0 + 1 from rfl, show ((2:ℕ)) = 1 + 1 from rfl, hkill 0, hkill 1]
  simp only [smul_zero, add_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  rw [h0term]; norm_num

theorem L0_contra_sub_pow_lof (α : ℂ) (k : ℕ) (g : Module.Dual ℂ (N.weight α)) :
    ((L0 (contra N).toWeakModule - α • 1) ^ k) (lofD N α g)
      = lofD N α (g ∘ₗ (L0w N α - α • 1) ^ k) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LinearMap.sub_apply, L0_contra_lof,
      LinearMap.smul_apply, Module.End.one_apply]
    have h1 : ∀ h : Module.Dual ℂ (N.weight α),
        (α • (lofD N α h : RestrictedDual N) : RestrictedDual N) = lofD N α (α • h) :=
      fun h => ((DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α).map_smul α h).symm
    have h2 : ∀ a b : Module.Dual ℂ (N.weight α),
        ((lofD N α a : RestrictedDual N) - lofD N α b : RestrictedDual N) = lofD N α (a - b) :=
      fun a b => ((DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α).map_sub a b).symm
    rw [h1, h2, pow_succ]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      Module.End.mul_apply, Module.End.one_apply, map_sub, map_smul]

/-- On a generalized-eigenspace-graded module, `L₀ − α` is nilpotent on `M_α`. -/
theorem L0w_sub_pow_finrank (hN : IsGenGraded N) (α : ℂ) :
    (L0w N α - α • 1) ^ Module.finrank ℂ (N.weight α) = 0 := by
  haveI := N.finrank α
  refine LinearMap.ext fun y => ?_
  have hy : y ∈ (L0w N α).maxGenEigenspace α := by
    rw [Module.End.mem_maxGenEigenspace]
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hN α y.2)
    refine ⟨k, Subtype.ext ?_⟩
    rw [L0w_sub_pow_apply]
    exact hk
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.mem_genEigenspace_nat] at hy
  exact hy

/-- **The contragredient of a generalized-eigenspace-graded module is again one.** -/
theorem isGenGraded_contra (hN : IsGenGraded N) : IsGenGraded (contra N) := by
  intro α f hf
  obtain ⟨g, rfl⟩ := hf
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨Module.finrank ℂ (N.weight α), ?_⟩
  have := L0_contra_sub_pow_lof N α (Module.finrank ℂ (N.weight α)) g
  rw [L0w_sub_pow_finrank N hN, LinearMap.comp_zero] at this
  exact this.trans (map_zero _)

/-- **Annihilators are an order anti-isomorphism** between the submodule lattices of a
generalized-eigenspace-graded module and of its contragredient. -/
def perpIsoGen (hN : IsGenGraded N) : Submodule (modeAlg N.toWeakModule) M ≃o
    (Submodule (modeAlg (Dm N).toWeakModule) (RestrictedDual N))ᵒᵈ :=
  perpIso N (subsGraded_of_isGenGraded N hN)
    (subsGraded_of_isGenGraded (contra N) (isGenGraded_contra N hN))

end Contra

end VOA.C2Rigid
