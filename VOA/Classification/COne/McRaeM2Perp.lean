import VOA.Modules.C2RigidContraClose
import VOA.Classification.COne.PlusRat2DualPerp

/-!
# McRae's route: annihilators between a graded weak module and its contragredient

Port of `PlusRat2DualPerp` (ordinary modules) to graded weak modules `GWModule` (generalized,
possibly logarithmic `L₀`), with contragredient `contra O` (`Modules/C2RigidContraClose.lean`).

The ordinary-module file derives gradedness of submodules (`x ∈ P ⟹ x_α ∈ P`) from `L₀` acting by
`α` on `M_α`.  Here that is replaced by the predicate `SubsGraded O`, which is proved in
`McRaeM2Graded.lean` for the generalized-eigenspace grading (`weight α ≤ maxGenEigenspace L₀ α`)
of `O` and of `contra O`.  Given `SubsGraded O` and `SubsGraded (contra O)`:

* `perpA`, `perpD` are mutually inverse (`perpD_perpA`, `perpA_perpD`) and order-reversing;
* `perpIso : Sub(O) ≃o Sub(O')ᵒᵈ`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.PlusRat2Dual (mem_P_mode double_sum_collapse L1_pow_mem_grading)
open VOA.Huang.LogRemovalAdmissible

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-! ## §1  Components -/

section Graded
variable (N : GWModule W M)

/-- The `α`-component of a vector. -/
def cmp (α : ℂ) (x : M) : M :=
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  ((DirectSum.decompose N.weight x α : N.weight α) : M)

theorem cmp_mem (α : ℂ) (x : M) : cmp N α x ∈ N.weight α := by
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  exact (DirectSum.decompose N.weight x α).2

theorem cmp_add (α : ℂ) (x y : M) : cmp N α (x + y) = cmp N α x + cmp N α y := by
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  simp [cmp, DirectSum.decompose_add]

theorem cmp_smul (α : ℂ) (c : ℂ) (x : M) : cmp N α (c • x) = c • cmp N α x := by
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  simp only [cmp, DirectSum.decompose_smul, DirectSum.smul_apply, Submodule.coe_smul]

theorem cmp_of_mem {α : ℂ} {x : M} (hx : x ∈ N.weight α) : cmp N α x = x := by
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  simp [cmp, DirectSum.decompose_of_mem_same N.weight hx]

theorem cmp_of_mem_ne {α β : ℂ} {x : M} (hx : x ∈ N.weight β) (h : β ≠ α) : cmp N α x = 0 := by
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  simp [cmp, DirectSum.decompose_of_mem_ne N.weight hx h]

/-- Every vector is the finite sum of its components. -/
theorem exists_sum_cmp (x : M) :
    ∃ s : Finset ℂ, (∀ α ∉ s, cmp N α x = 0) ∧ ∑ α ∈ s, cmp N α x = x := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  refine ⟨(DirectSum.decompose N.weight x).support, ?_, ?_⟩
  · intro α hα
    have h0 : DirectSum.decompose N.weight x α = 0 := by
      by_contra h
      exact hα (DFinsupp.mem_support_iff.mpr h)
    simp [cmp, h0]
  · exact DirectSum.sum_support_decompose N.weight x


/-- **Graded submodules**: every mode submodule contains the components of its members. -/
def SubsGraded : Prop :=
  ∀ (P : Submodule (modeAlg N.toWeakModule) M) {x : M}, x ∈ P → ∀ α : ℂ, cmp N α x ∈ P

/-- A mode submodule is determined by its homogeneous members. -/
theorem mem_of_cmp_mem (S : Submodule ℂ M) {x : M} (h : ∀ α, cmp N α x ∈ S) : x ∈ S := by
  obtain ⟨s, -, hsum⟩ := exists_sum_cmp N x
  rw [← hsum]
  exact Submodule.sum_mem S (fun α _ => h α)

end Graded

section Inversion
variable (O : GWModule W M)

/-- **Inversion of the transpose.**  A module mode is a combination of the transposes
`dualAdj` of the contragredient modes of `L(1)^j a`. -/
theorem mode_eq_sum_dualAdj {a : V} {w : ℤ} (ha : a ∈ W.grading w) (p : ℤ) {α : ℂ} {x : M}
    (hx : x ∈ O.weight α) :
    mode (O.YM a) p x = (-1 : ℂ) ^ w • ∑ j ∈ Finset.range (w.toNat + 1),
      ((j.factorial : ℂ))⁻¹ • dualAdj O (w - j) ((W.L 1 ^ j) a) (2 * w - p - 2 - j) α x := by
  rcases lt_or_ge w 0 with hw | hw
  · have ha0 : a = 0 := by
      have := ha
      rwa [W.positivity w hw, Submodule.mem_bot] at this
    subst ha0
    simp only [map_zero]
    have : ∀ j : ℕ, dualAdj O (w - j) ((W.L 1 ^ j) (0 : V)) (2 * w - p - 2 - j) α x = 0 := by
      intro j
      rw [map_zero]
      exact dualAdj_zero_state O _ _ hx
    simp [dualAdj_zero_state O _ _ hx]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, w = n := ⟨w.toNat, by omega⟩
  rw [Int.toNat_natCast]
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ((j.factorial : ℂ))⁻¹ • dualAdj O ((n : ℤ) - j) ((W.L 1 ^ j) a)
          (2 * (n : ℤ) - p - 2 - j) α x =
        (-1 : ℂ) ^ (n - j) • ∑ i ∈ Finset.range (n - j + 1),
          (((j.factorial : ℂ))⁻¹ * ((i.factorial : ℂ))⁻¹) •
            mode (O.YM ((W.L 1 ^ (i + j)) a)) (p - ((i + j : ℕ) : ℤ)) x := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [dualAdj_clean O (L1_pow_mem_grading ha j) _ hx]
    have htn : ((n : ℤ) - j).toNat = n - j := by omega
    have hz : ((n : ℤ) - (j : ℤ)) = ((n - j : ℕ) : ℤ) := by omega
    rw [htn, hz, zpow_natCast, smul_comm, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, ← Module.End.mul_apply, ← pow_add]
    congr 3
    push_cast [Nat.cast_sub hjn]
    ring
  rw [Finset.sum_congr rfl hterm, zpow_natCast, Finset.smul_sum]
  have hsign : ∀ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ n • ((-1 : ℂ) ^ (n - j) •
      ∑ i ∈ Finset.range (n - j + 1),
        (((j.factorial : ℂ))⁻¹ * ((i.factorial : ℂ))⁻¹) •
          mode (O.YM ((W.L 1 ^ (i + j)) a)) (p - ((i + j : ℕ) : ℤ)) x) =
      ∑ i ∈ Finset.range (n - j + 1),
        ((-1 : ℂ) ^ j * (((j.factorial : ℂ))⁻¹ * ((i.factorial : ℂ))⁻¹)) •
          mode (O.YM ((W.L 1 ^ (i + j)) a)) (p - ((i + j : ℕ) : ℤ)) x := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [smul_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    have : (-1 : ℂ) ^ n = (-1 : ℂ) ^ j * (-1 : ℂ) ^ (n - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hjn]
    rw [this]
    have h2 : (-1 : ℂ) ^ (n - j) * (-1 : ℂ) ^ (n - j) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination ((-1 : ℂ) ^ j * (((j.factorial : ℂ))⁻¹ * ((i.factorial : ℂ))⁻¹)) * h2
  rw [Finset.sum_congr rfl hsign]
  rw [double_sum_collapse n (fun t => mode (O.YM ((W.L 1 ^ t) a)) (p - (t : ℤ)) x)]
  simp

end Inversion

section Pairing
variable (O : GWModule W M)

/-- The (unconditional) contragredient module. -/
abbrev Dm : GWModule W (RestrictedDual O) := contra O

theorem Dm_YM (u : V) : (Dm O).YM u = YMdual O u := rfl

/-- The graded generator `lof α g`. -/
abbrev lofD (α : ℂ) (g : Module.Dual ℂ (O.weight α)) : RestrictedDual O :=
  DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (O.weight β)) α g

theorem pr_zero_left (f : RestrictedDual O) : dualPairing O 0 f = 0 := by
  have h := dualPairing_smul_left O 0 (0 : M) f
  rw [zero_smul, zero_smul] at h
  exact h

theorem pr_sum_left {ι : Type*} (s : Finset ι) (c : ι → M) (f : RestrictedDual O) :
    dualPairing O (∑ i ∈ s, c i) f = ∑ i ∈ s, dualPairing O (c i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pr_zero_left]
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, dualPairing_add_left, ih]

/-- The `α`-component of an element of the contragredient. -/
abbrev fc (α : ℂ) (f : RestrictedDual O) : Module.Dual ℂ (O.weight α) :=
  DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (O.weight β)) α f

theorem pr_of_mem {α : ℂ} {x : M} (hx : x ∈ O.weight α) (f : RestrictedDual O) :
    dualPairing O x f = (fc O α f) ⟨x, hx⟩ :=
  dualPairing_component O f hx

/-- Pairing a component against `f` is pairing `x` against the `α`-component of `f`. -/
theorem pr_cmp (α : ℂ) (x : M) (f : RestrictedDual O) :
    dualPairing O (cmp O α x) f = dualPairing O x (lofD O α (fc O α f)) := by
  rw [pr_of_mem O (cmp_mem O α x), dualPairing_lof]
  rfl

theorem fc_lofD (α : ℂ) (g : Module.Dual ℂ (O.weight α)) : fc O α (lofD O α g) = g :=
  DirectSum.component.lof_self ℂ (M := fun β => Module.Dual ℂ (O.weight β)) α g

theorem fc_lofD_ne {α β : ℂ} (g : Module.Dual ℂ (O.weight β)) (h : β ≠ α) :
    fc O α (lofD O β g) = 0 := by
  rw [fc, DirectSum.component.of, dif_neg h]

/-- The components of an element of the contragredient. -/
theorem cmpD_eq (α : ℂ) (f : RestrictedDual O) :
    cmp (Dm O) α f = lofD O α (fc O α f) := by
  classical
  let f' : DirectSum ℂ (fun β => Module.Dual ℂ (O.weight β)) := f
  have hsum := DirectSum.sum_support_of f'
  have hlin : ∀ (s : Finset ℂ) (c : ℂ → RestrictedDual O),
      cmp (Dm O) α (∑ i ∈ s, c i) = ∑ i ∈ s, cmp (Dm O) α (c i) := by
    intro s c
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      have h := cmp_smul (Dm O) α 0 (0 : RestrictedDual O)
      rwa [zero_smul, zero_smul] at h
    | insert a s has ih => rw [Finset.sum_insert has, Finset.sum_insert has, cmp_add, ih]
  have hmem : ∀ i, lofD O i (f' i) ∈ (Dm O).weight i := fun i => ⟨f' i, rfl⟩
  have hfc : fc O α f = f' α := (DirectSum.apply_eq_component _ _ _).symm
  rw [hfc]
  change cmp (Dm O) α f' = _
  conv_lhs => rw [← hsum]
  erw [hlin]
  change ∑ i ∈ f'.support, cmp (Dm O) α (lofD O i (f' i)) = _
  by_cases hα : α ∈ f'.support
  · rw [Finset.sum_eq_single α]
    · exact cmp_of_mem (Dm O) (hmem α)
    · intro b _ hb
      exact cmp_of_mem_ne (Dm O) (hmem b) hb
    · intro h; exact absurd hα h
  · rw [Finset.sum_eq_zero]
    · have h0 : f' α = 0 := by
        by_contra h
        exact hα (DFinsupp.mem_support_iff.mpr h)
      rw [h0]
      exact (map_zero (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (O.weight β)) α)).symm
    · intro b hb
      exact cmp_of_mem_ne (Dm O) (hmem b) (fun h => hα (h ▸ hb))

/-- Nondegeneracy on the module side. -/
theorem eq_zero_of_pr {x : M} (h : ∀ f, dualPairing O x f = 0) : x = 0 := by
  have hx : x ∈ (⊥ : Submodule ℂ M) := by
    apply mem_of_cmp_mem O ⊥
    intro α
    rw [Submodule.mem_bot]
    by_contra hne
    have hne' : (⟨cmp O α x, cmp_mem O α x⟩ : O.weight α) ≠ 0 := fun h0 =>
      hne (congrArg Subtype.val h0)
    obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one ℂ hne'
    have h1 := h (lofD O α g)
    rw [dualPairing_lof] at h1
    have he : internalProjTo O.isInternal α x = ⟨cmp O α x, cmp_mem O α x⟩ := Subtype.ext rfl
    rw [he, hg] at h1
    exact one_ne_zero h1
  simpa using hx

end Pairing

section Perp
variable (O : GWModule W M)

theorem cmp_mem_perpD_aux
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    (T : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O))
    {x : M} (hx : ∀ f ∈ T, dualPairing O x f = 0) (α : ℂ) :
    ∀ f ∈ T, dualPairing O (cmp O α x) f = 0 := by
  intro f hf
  rw [pr_cmp, ← cmpD_eq]
  exact hx _ (hD T hf α)

/-- The annihilator in the contragredient of a submodule. -/
def perpASub
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    (S : Submodule (modeAlg O.toWeakModule) M) :
    WeakModule.Submodule' (Dm O).toWeakModule where
  carrier :=
    { carrier := {f | ∀ x ∈ S, dualPairing O x f = 0}
      add_mem' := by
        intro f g hf hg x hx
        rw [map_add, hf x hx, hg x hx, add_zero]
      zero_mem' := by
        intro x _
        exact map_zero _
      smul_mem' := by
        intro c f hf x hx
        rw [map_smul, hf x hx, smul_zero] }
  act_mem := by
    intro a p f hf
    have ha : a ∈ ⨆ w, W.grading w := by
      rw [W.isInternal.submodule_iSup_eq_top]; trivial
    refine Submodule.iSup_induction W.grading
      (motive := fun a => ∀ x ∈ S, dualPairing O x ((Dm O).toWeakModule.act a p f) = 0)
      ha ?_ ?_ ?_
    · intro w a ha x hx
      obtain ⟨s, -, hsum⟩ := exists_sum_cmp O x
      rw [← hsum, pr_sum_left]
      apply Finset.sum_eq_zero
      intro α _
      change dualPairing O (cmp O α x) (mode (YMdual O a) p f) = 0
      rw [dualPairing_mode_dualAdj O ha p f (cmp_mem O α x)]
      apply hf
      rw [dualAdj_clean O ha p (cmp_mem O α x)]
      apply S.smul_of_tower_mem
      apply Submodule.sum_mem
      intro j _
      apply S.smul_of_tower_mem
      exact mem_P_mode _ S _ _ (hO S hx α)
    · intro x _
      change dualPairing O x (mode (YMdual O 0) p f) = 0
      rw [map_zero]
      exact map_zero _
    · intro a b ha hb x hx
      change dualPairing O x (mode (YMdual O (a + b)) p f) = 0
      rw [map_add]
      change dualPairing O x (mode (YMdual O a) p f + mode (YMdual O b) p f) = 0
      rw [map_add]
      exact (congrArg₂ (· + ·) (ha x hx) (hb x hx)).trans (add_zero 0)

/-- The annihilator in the module of a submodule of the contragredient. -/
def perpDSub
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    (T : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)) :
    WeakModule.Submodule' O.toWeakModule where
  carrier :=
    { carrier := {x | ∀ f ∈ T, dualPairing O x f = 0}
      add_mem' := by
        intro x y hx hy f hf
        rw [dualPairing_add_left, hx f hf, hy f hf, add_zero]
      zero_mem' := by
        intro f _
        exact pr_zero_left O f
      smul_mem' := by
        intro c x hx f hf
        rw [dualPairing_smul_left, hx f hf, smul_zero] }
  act_mem := by
    intro a p x hx
    have ha : a ∈ ⨆ w, W.grading w := by
      rw [W.isInternal.submodule_iSup_eq_top]; trivial
    refine Submodule.iSup_induction W.grading
      (motive := fun a => ∀ f ∈ T, dualPairing O (O.toWeakModule.act a p x) f = 0)
      ha ?_ ?_ ?_
    · intro w a ha f hf
      obtain ⟨s, -, hsum⟩ := exists_sum_cmp O x
      rw [WeakModule.act_def, ← hsum, map_sum, pr_sum_left]
      apply Finset.sum_eq_zero
      intro α _
      rw [mode_eq_sum_dualAdj O ha p (cmp_mem O α x), dualPairing_smul_left, pr_sum_left]
      rw [Finset.sum_eq_zero, smul_zero]
      intro j _
      rw [dualPairing_smul_left, ← dualPairing_mode_dualAdj O (L1_pow_mem_grading ha j) _ f
        (cmp_mem O α x)]
      have hm : mode (YMdual O ((W.L 1 ^ j) a)) (2 * w - p - 2 - j) f ∈ T :=
        mem_P_mode _ T ((W.L 1 ^ j) a) _ hf
      rw [cmp_mem_perpD_aux O hO hD T hx α _ hm, smul_zero]
    · intro f _
      rw [WeakModule.act_def, map_zero]
      exact pr_zero_left O f
    · intro a b ha hb f hf
      rw [WeakModule.act_def, map_add]
      change dualPairing O (mode (O.YM a) p x + mode (O.YM b) p x) f = 0
      rw [dualPairing_add_left]
      exact (congrArg₂ (· + ·) (ha f hf) (hb f hf)).trans (add_zero 0)

/-- `S ↦ S^⊥ ⊆ O'`. -/
def perpA
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    (S : Submodule (modeAlg O.toWeakModule) M) :
    Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O) :=
  toR _ (perpASub O hO hD S)

/-- `T ↦ T^⊥ ⊆ O`. -/
def perpD
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    (T : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)) :
    Submodule (modeAlg O.toWeakModule) M :=
  toR _ (perpDSub O hO hD T)

theorem mem_perpA
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    {S : Submodule (modeAlg O.toWeakModule) M} {f : RestrictedDual O} :
    f ∈ perpA O hO hD S ↔ ∀ x ∈ S, dualPairing O x f = 0 := Iff.rfl

theorem mem_perpD
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    {T : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)} {x : M} :
    x ∈ perpD O hO hD T ↔ ∀ f ∈ T, dualPairing O x f = 0 := Iff.rfl

/-- A functional on a weight space extends by zero into the annihilator. -/
theorem lofD_mem_perpA
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    (S : Submodule (modeAlg O.toWeakModule) M) (α : ℂ)
    (g : Module.Dual ℂ (O.weight α))
    (hg : ∀ v : O.weight α, (v : M) ∈ S → g v = 0) : lofD O α g ∈ perpA O hO hD S := by
  intro x hx
  rw [dualPairing_lof]
  apply hg
  exact hO S hx α

/-- `S^⊥⊥ = S`. -/
theorem perpD_perpA
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    (S : Submodule (modeAlg O.toWeakModule) M) : perpD O hO hD (perpA O hO hD S) = S := by
  apply le_antisymm
  · intro x hx
    apply mem_of_cmp_mem O (S.restrictScalars ℂ)
    intro α
    by_contra hn
    let U := O.weight α
    let Sα : Submodule ℂ U := (S.restrictScalars ℂ).comap U.subtype
    have hc : (⟨cmp O α x, cmp_mem O α x⟩ : U) ∉ Sα := hn
    obtain ⟨g, hg, hgS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
    have hf : lofD O α g ∈ perpA O hO hD S := by
      apply lofD_mem_perpA
      intro v hv
      have : g v ∈ Sα.map g := ⟨v, hv, rfl⟩
      rw [hgS] at this
      exact (Submodule.mem_bot ℂ).mp this
    have h0 := hx _ hf
    rw [dualPairing_lof] at h0
    apply hg
    rw [← h0]
    rfl
  · intro x hx f hf
    exact hf x hx

/-- `T^⊥⊥ = T`. -/
theorem perpA_perpD
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    (T : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)) :
    perpA O hO hD (perpD O hO hD T) = T := by
  apply le_antisymm
  · intro f hf
    apply mem_of_cmp_mem (Dm O) (T.restrictScalars ℂ)
    intro α
    rw [cmpD_eq]
    by_contra hn
    let U := O.weight α
    haveI : FiniteDimensional ℂ U := O.finrank α
    let lα : Module.Dual ℂ U →ₗ[ℂ] RestrictedDual O :=
      DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (O.weight β)) α
    let Tα : Submodule ℂ (Module.Dual ℂ U) := (T.restrictScalars ℂ).comap lα
    have hfn : fc O α f ∉ Tα := hn
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Tα)] at hfn
    rw [Submodule.mem_dualAnnihilator] at hfn
    push Not at hfn
    obtain ⟨u, hu, hfu⟩ := hfn
    rw [Submodule.mem_dualCoannihilator] at hu
    have hxT : (u : M) ∈ perpD O hO hD T := by
      intro t ht
      rw [pr_of_mem O u.2]
      apply hu
      change lofD O α (fc O α t) ∈ T
      rw [← cmpD_eq]
      exact hD T ht α
    have h0 := hf _ hxT
    rw [pr_of_mem O u.2] at h0
    exact hfu h0
  · intro f hf x hx
    exact hx f hf

theorem perpA_antitone
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    {S S' : Submodule (modeAlg O.toWeakModule) M} (h : S ≤ S') :
    perpA O hO hD S' ≤ perpA O hO hD S := fun _ hf x hx => hf x (h hx)

theorem perpD_antitone
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    {T T' : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)}
    (h : T ≤ T') : perpD O hO hD T' ≤ perpD O hO hD T := fun _ hx f hf => hx f (h hf)

/-- The annihilator is an order anti-isomorphism of submodule lattices. -/
def perpIso
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    : Submodule (modeAlg O.toWeakModule) M ≃o
    (Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O))ᵒᵈ where
  toFun S := OrderDual.toDual (perpA O hO hD S)
  invFun T := perpD O hO hD (OrderDual.ofDual T)
  left_inv S := perpD_perpA O hO hD S
  right_inv T := perpA_perpD O hO hD (OrderDual.ofDual T)
  map_rel_iff' := by
    intro S S'
    simp only [Equiv.coe_fn_mk, OrderDual.toDual_le_toDual]
    constructor
    · intro h
      have := perpD_antitone O hO hD h
      rwa [perpD_perpA, perpD_perpA] at this
    · exact perpA_antitone O hO hD

theorem perpIso_apply
    (hO : SubsGraded O) (hD : SubsGraded (contra O))
    (S : Submodule (modeAlg O.toWeakModule) M) :
    perpIso O hO hD S = OrderDual.toDual (perpA O hO hD S) := rfl

end Perp

end VOA.C2Rigid
