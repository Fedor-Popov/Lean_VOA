import VOA.Classification.COne.PlusRat2DualLift
import VOA.Modules.ContragredientClose

/-! # Annihilators between an ordinary module and its contragredient

For an ordinary module `O` (an `OrdVModule`) with contragredient `D = O'` (the unconditional
`contragredientModule`), the annihilator maps

* `perpA : Submodule (modeAlg O) M → Submodule (modeAlg D) O'`,
* `perpD : Submodule (modeAlg D) O' → Submodule (modeAlg O) M`

are mutually inverse and order-reversing (`perpD_perpA`, `perpA_perpD`).  Mode closure of
`perpA S` uses the transpose formula `dualPairing_mode_dualAdj`; mode closure of `perpD T` uses its
inversion `mode_eq_sum_dualAdj` (the identity `e^{zL(1)}(-z⁻²)^{L(0)}` is an involution).
Double annihilators use gradedness of submodules and finite-dimensional duality on each weight
space.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat2Dual
open PlusSplitting ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible PlusRational

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-! ## §1  Gradedness of `L(0)`-stable subspaces -/

section Graded
variable (N : OrdVModule W M)

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

/-- In an `L(0)`-stable subspace, homogeneous summands of a member are members. -/
theorem sum_components_mem (S : Submodule ℂ M)
    (hS : ∀ y ∈ S, L0 N.toWeakModule y ∈ S) :
    ∀ (s : Finset ℂ) (c : ℂ → M), (∀ α, c α ∈ N.weight α) →
      ∑ α ∈ s, c α ∈ S → ∀ α ∈ s, c α ∈ S := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro c _ _ α hα; simp at hα
  | insert a s has ih =>
    intro c hc hsum
    have hL : ∀ β, (L0 N.toWeakModule - a • 1) (c β) = (β - a) • c β := by
      intro β
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        show L0 N.toWeakModule (c β) = β • c β from N.L0_weight β _ (hc β), sub_smul]
    have hs' : ∑ β ∈ s, (β - a) • c β ∈ S := by
      have h1 : (L0 N.toWeakModule - a • 1) (∑ β ∈ insert a s, c β) ∈ S := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        exact S.sub_mem (hS _ hsum) (S.smul_mem a hsum)
      rwa [map_sum, Finset.sum_insert has, hL, sub_self, zero_smul, zero_add,
        Finset.sum_congr rfl (fun β _ => hL β)] at h1
    have hih := ih (fun β => (β - a) • c β) (fun β => Submodule.smul_mem _ _ (hc β)) hs'
    have hmem : ∀ β ∈ s, c β ∈ S := by
      intro β hβ
      have hne : β - a ≠ 0 := sub_ne_zero.mpr (fun h => has (h ▸ hβ))
      have := S.smul_mem (β - a)⁻¹ (hih β hβ)
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    intro α hα
    rcases Finset.mem_insert.mp hα with rfl | hα
    · rw [Finset.sum_insert has] at hsum
      have := S.sub_mem hsum (Submodule.sum_mem S hmem)
      rwa [add_sub_cancel_right] at this
    · exact hmem α hα

/-- Components of a member of an `L(0)`-stable subspace are members. -/
theorem cmp_mem_of_stable (S : Submodule ℂ M) (hS : ∀ y ∈ S, L0 N.toWeakModule y ∈ S)
    {x : M} (hx : x ∈ S) (α : ℂ) : cmp N α x ∈ S := by
  classical
  obtain ⟨s, hs0, hsum⟩ := exists_sum_cmp N x
  by_cases hα : α ∈ s
  · have hs : ∑ β ∈ s, cmp N β x ∈ S := by rw [hsum]; exact hx
    exact sum_components_mem N S hS s (fun β => cmp N β x) (fun β => cmp_mem N β x) hs α hα
  · rw [hs0 α hα]; exact S.zero_mem

/-- Mode submodules are `L(0)`-stable. -/
theorem L0_mem_of_modeSub (P : Submodule (modeAlg N.toWeakModule) M) {y : M} (hy : y ∈ P) :
    L0 N.toWeakModule y ∈ P :=
  mem_P_mode N.toWeakModule P _ 1 hy

theorem cmp_mem_modeSub (P : Submodule (modeAlg N.toWeakModule) M) {x : M} (hx : x ∈ P)
    (α : ℂ) : cmp N α x ∈ P :=
  cmp_mem_of_stable N (P.restrictScalars ℂ) (fun _ hy => L0_mem_of_modeSub N P hy) hx α

/-- A mode submodule is determined by its homogeneous members. -/
theorem mem_of_cmp_mem (S : Submodule ℂ M) {x : M} (h : ∀ α, cmp N α x ∈ S) : x ∈ S := by
  obtain ⟨s, -, hsum⟩ := exists_sum_cmp N x
  rw [← hsum]
  exact Submodule.sum_mem S (fun α _ => h α)

end Graded


/-! ## §2  The involution identity -/

section Combinatorics

/-- `∑_{j ≤ m} (-1)^j / (j! (m-j)!) = [m = 0]`. -/
theorem alt_inv_factorial_sum (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
      (-1 : ℂ) ^ j * (((j.factorial : ℂ))⁻¹ * (((m - j).factorial : ℂ))⁻¹) =
      if m = 0 then 1 else 0 := by
  have h := add_pow (-1 : ℂ) 1 m
  rw [neg_add_cancel] at h
  have hmf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (-1 : ℂ) ^ j * (((j.factorial : ℂ))⁻¹ * (((m - j).factorial : ℂ))⁻¹) =
        ((m.factorial : ℂ))⁻¹ * ((-1 : ℂ) ^ j * (1 : ℂ) ^ (m - j) * (m.choose j : ℂ)) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hc := Nat.choose_mul_factorial_mul_factorial hjm
    have hc' : (m.choose j : ℂ) * (j.factorial : ℂ) * ((m - j).factorial : ℂ) =
        (m.factorial : ℂ) := by exact_mod_cast hc
    have hj0 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hmj0 : ((m - j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m - j)
    have hch : (m.choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjm).ne'
    rw [one_pow, mul_one, ← hc']
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← h]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [zero_pow (by omega), mul_zero, if_neg (by omega)]

/-- The double sum of the involution identity collapses to its `0`-th term. -/
theorem double_sum_collapse {X : Type*} [AddCommGroup X] [Module ℂ X] (n : ℕ) (F : ℕ → X) :
    ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n - j + 1),
      ((-1 : ℂ) ^ j * (((j.factorial : ℂ))⁻¹ * ((i.factorial : ℂ))⁻¹)) • F (i + j) = F 0 := by
  let f : ℕ → ℕ → X := fun j i =>
    ((-1 : ℂ) ^ j * (((j.factorial : ℂ))⁻¹ * ((i.factorial : ℂ))⁻¹)) • F (i + j)
  have hflip := Finset.sum_range_diag_flip (n + 1) f
  have hinner : ∀ j ∈ Finset.range (n + 1),
      ∑ i ∈ Finset.range (n - j + 1), f j i = ∑ i ∈ Finset.range (n + 1 - j), f j i := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show n - j + 1 = n + 1 - j by omega]
  change ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n - j + 1), f j i = F 0
  rw [Finset.sum_congr rfl hinner, ← hflip]
  have hcol : ∀ m ∈ Finset.range (n + 1),
      ∑ k ∈ Finset.range (m + 1), f k (m - k) = (if m = 0 then (1 : ℂ) else 0) • F m := by
    intro m _
    have hk : ∀ k ∈ Finset.range (m + 1), f k (m - k) =
        ((-1 : ℂ) ^ k * (((k.factorial : ℂ))⁻¹ * (((m - k).factorial : ℂ))⁻¹)) • F m := by
      intro k hk
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [f]
      rw [Nat.sub_add_cancel hkm]
    rw [Finset.sum_congr rfl hk, ← Finset.sum_smul, alt_inv_factorial_sum]
  rw [Finset.sum_congr rfl hcol, Finset.sum_eq_single 0]
  · simp
  · intro m _ hm; rw [if_neg hm, zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

end Combinatorics

/-- `L(1)^j` lowers the weight by `j`. -/
theorem L1_pow_mem_grading {a : V} {w : ℤ} (ha : a ∈ W.grading w) (j : ℕ) :
    (W.L 1 ^ j) a ∈ W.grading (w - j) := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := W.toPreVertexAlgebra.smul_mem_grading W.conformal_mem ih 2
    have he : W.L 1 ((W.L 1 ^ j) a) = W.smul W.conformalVector 2 ((W.L 1 ^ j) a) := by
      rw [VertexOperatorAlgebra.L_def]; rfl
    rw [he]
    have hk : (2 : ℤ) + (w - j) - 2 - 1 = w - ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [hk] at h

section Inversion
variable (O : OrdVModule W M)

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


/-! ## §3  Pairing -/

section Pairing
variable (O : OrdVModule W M)

/-- The (unconditional) contragredient module. -/
abbrev Dm : OrdVModule W (RestrictedDual O) := contragredientModule O

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


/-! ## §4  Annihilators -/

section Perp
variable (O : OrdVModule W M)

theorem cmp_mem_perpD_aux (T : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O))
    {x : M} (hx : ∀ f ∈ T, dualPairing O x f = 0) (α : ℂ) :
    ∀ f ∈ T, dualPairing O (cmp O α x) f = 0 := by
  intro f hf
  rw [pr_cmp, ← cmpD_eq]
  exact hx _ (cmp_mem_modeSub (Dm O) T hf α)

/-- The annihilator in the contragredient of a submodule. -/
def perpASub (S : Submodule (modeAlg O.toWeakModule) M) :
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
      exact mem_P_mode _ S _ _ (cmp_mem_modeSub O S hx α)
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
def perpDSub (T : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)) :
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
      rw [cmp_mem_perpD_aux O T hx α _ hm, smul_zero]
    · intro f _
      rw [WeakModule.act_def, map_zero]
      exact pr_zero_left O f
    · intro a b ha hb f hf
      rw [WeakModule.act_def, map_add]
      change dualPairing O (mode (O.YM a) p x + mode (O.YM b) p x) f = 0
      rw [dualPairing_add_left]
      exact (congrArg₂ (· + ·) (ha f hf) (hb f hf)).trans (add_zero 0)

/-- `S ↦ S^⊥ ⊆ O'`. -/
def perpA (S : Submodule (modeAlg O.toWeakModule) M) :
    Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O) :=
  toR _ (perpASub O S)

/-- `T ↦ T^⊥ ⊆ O`. -/
def perpD (T : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)) :
    Submodule (modeAlg O.toWeakModule) M :=
  toR _ (perpDSub O T)

theorem mem_perpA {S : Submodule (modeAlg O.toWeakModule) M} {f : RestrictedDual O} :
    f ∈ perpA O S ↔ ∀ x ∈ S, dualPairing O x f = 0 := Iff.rfl

theorem mem_perpD {T : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)} {x : M} :
    x ∈ perpD O T ↔ ∀ f ∈ T, dualPairing O x f = 0 := Iff.rfl

/-- A functional on a weight space extends by zero into the annihilator. -/
theorem lofD_mem_perpA (S : Submodule (modeAlg O.toWeakModule) M) (α : ℂ)
    (g : Module.Dual ℂ (O.weight α))
    (hg : ∀ v : O.weight α, (v : M) ∈ S → g v = 0) : lofD O α g ∈ perpA O S := by
  intro x hx
  rw [dualPairing_lof]
  apply hg
  exact cmp_mem_modeSub O S hx α

/-- `S^⊥⊥ = S`. -/
theorem perpD_perpA (S : Submodule (modeAlg O.toWeakModule) M) : perpD O (perpA O S) = S := by
  apply le_antisymm
  · intro x hx
    apply mem_of_cmp_mem O (S.restrictScalars ℂ)
    intro α
    by_contra hn
    let U := O.weight α
    let Sα : Submodule ℂ U := (S.restrictScalars ℂ).comap U.subtype
    have hc : (⟨cmp O α x, cmp_mem O α x⟩ : U) ∉ Sα := hn
    obtain ⟨g, hg, hgS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
    have hf : lofD O α g ∈ perpA O S := by
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
theorem perpA_perpD (T : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)) :
    perpA O (perpD O T) = T := by
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
    have hxT : (u : M) ∈ perpD O T := by
      intro t ht
      rw [pr_of_mem O u.2]
      apply hu
      change lofD O α (fc O α t) ∈ T
      rw [← cmpD_eq]
      exact cmp_mem_modeSub (Dm O) T ht α
    have h0 := hf _ hxT
    rw [pr_of_mem O u.2] at h0
    exact hfu h0
  · intro f hf x hx
    exact hx f hf

theorem perpA_antitone {S S' : Submodule (modeAlg O.toWeakModule) M} (h : S ≤ S') :
    perpA O S' ≤ perpA O S := fun _ hf x hx => hf x (h hx)

theorem perpD_antitone {T T' : Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O)}
    (h : T ≤ T') : perpD O T' ≤ perpD O T := fun _ hx f hf => hx f (h hf)

/-- The annihilator is an order anti-isomorphism of submodule lattices. -/
def perpIso : Submodule (modeAlg O.toWeakModule) M ≃o
    (Submodule (modeAlg (Dm O).toWeakModule) (RestrictedDual O))ᵒᵈ where
  toFun S := OrderDual.toDual (perpA O S)
  invFun T := perpD O (OrderDual.ofDual T)
  left_inv S := perpD_perpA O S
  right_inv T := perpA_perpD O (OrderDual.ofDual T)
  map_rel_iff' := by
    intro S S'
    simp only [Equiv.coe_fn_mk, OrderDual.toDual_le_toDual]
    constructor
    · intro h
      have := perpD_antitone O h
      rwa [perpD_perpA, perpD_perpA] at this
    · exact perpA_antitone O

theorem perpIso_apply (S : Submodule (modeAlg O.toWeakModule) M) :
    perpIso O S = OrderDual.toDual (perpA O S) := rfl

end Perp

end VOA.Classification.COne.PlusRat2Dual
