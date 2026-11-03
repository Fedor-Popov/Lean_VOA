import VOA.DeligneAudit.D4FusionToroidalGrRank

/-! Exact rank of the finite high-mode associated graded. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl

noncomputable section

private def finiteSinglesStar {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : ℕ) (A : ℕ → Submodule ℂ V) :
    ((i : Fin D) → A i) →ₗ[ℂ] (ℕ →₀ V) where
  toFun x := ∑ i : Fin D, Finsupp.single i.val (x i).val
  map_add' x y := by
    simp only [Pi.add_apply, Submodule.coe_add, Finsupp.single_add,
      Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, Submodule.coe_smul, ← Finsupp.smul_single,
      Finset.smul_sum, RingHom.id_apply]

private theorem finiteSinglesStar_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : ℕ) (A : ℕ → Submodule ℂ V) (x : (i : Fin D) → A i)
    (i : Fin D) : finiteSinglesStar D A x i = (x i).val := by
  change (∑ c : Fin D, Finsupp.single c.val (x c).val) i.val = _
  calc
    _ = (Finsupp.lapply i.val : (ℕ →₀ V) →ₗ[ℂ] V)
        (∑ c : Fin D, Finsupp.single c.val (x c).val) := rfl
    _ = ∑ c : Fin D, (Finsupp.lapply i.val : (ℕ →₀ V) →ₗ[ℂ] V)
        (Finsupp.single c.val (x c).val) := by rw [map_sum]
    _ = _ := by simp [Finsupp.lapply_apply, Finsupp.single_apply, Fin.val_inj]

private theorem finiteSinglesStar_injective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : ℕ) (A : ℕ → Submodule ℂ V) :
    Function.Injective (finiteSinglesStar D A) := by
  intro x y h
  funext i
  apply Subtype.ext
  simpa only [finiteSinglesStar_apply] using congrArg (fun z : ℕ →₀ V => z i) h

private theorem finiteSinglesStar_range {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : ℕ) (A : ℕ → Submodule ℂ V)
    (hvanish : ∀ j, D ≤ j → A j = ⊥) :
    LinearMap.range (finiteSinglesStar D A) =
      Submodule.span ℂ {v | ∃ j x, x ∈ A j ∧ v = Finsupp.single j x} := by
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    change ∑ i : Fin D, Finsupp.single i.val (x i).val ∈ _
    apply Submodule.sum_mem
    intro i _
    exact Submodule.subset_span ⟨i.val, (x i).val, (x i).property, rfl⟩
  · rw [Submodule.span_le]
    rintro v ⟨j, x, hx, rfl⟩
    by_cases hj : j < D
    · let i : Fin D := ⟨j, hj⟩
      let y : (k : Fin D) → A k := Pi.single i ⟨x, hx⟩
      refine ⟨y, ?_⟩
      change (∑ k : Fin D, Finsupp.single k.val (y k).val) = _
      rw [Finset.sum_eq_single i]
      · simp [y, i]
      · intro k _ hk
        simp [y, hk]
      · simp
    · have hx0 : x = 0 := by
        have : x ∈ (⊥ : Submodule ℂ V) := by
          rw [← hvanish j (Nat.le_of_not_gt hj)]
          exact hx
        simpa using this
      subst x
      simp

private theorem finiteSinglesStar_finrank {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (D : ℕ) (A : ℕ → Submodule ℂ V)
    (hvanish : ∀ j, D ≤ j → A j = ⊥) :
    Module.finrank ℂ
      (Submodule.span ℂ {v | ∃ j x, x ∈ A j ∧ v = Finsupp.single j x}) =
      ∑ i : Fin D, Module.finrank ℂ (A i) := by
  rw [← finiteSinglesStar_range D A hvanish,
    LinearMap.finrank_range_of_inj (finiteSinglesStar_injective D A),
    Module.finrank_pi_fintype]

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n)
    (m : ℕ)

private theorem TU_vanish_star [FiniteDimensional ℂ (UModG f R)]
    (hm : 1 ≤ m) : ∃ D, ∀ j, D ≤ j → TU f R m j = ⊥ := by
  obtain ⟨D, hD⟩ := finite_TU f R m hm
  exact ⟨D, fun j hj => le_antisymm
    ((TU_mono f R m hj).trans (le_of_eq hD)) bot_le⟩

/-- G2 finite-dimensionality, for any finite-dimensional universal module. -/
theorem gr_finiteDimensional_star [FiniteDimensional ℂ (UModG f R)]
    (hm : 1 ≤ m) : FiniteDimensional ℂ (Gr f R m) := by
  obtain ⟨D, hD⟩ := TU_vanish_star f R m hm
  have hnum := finiteSinglesStar_range D (fun j => TU f R m j) hD
  haveI : FiniteDimensional ℂ (grNumerator f R m) := by
    rw [grNumerator, ← hnum]
    infer_instance
  infer_instance

/-- The associated graded has exactly the rank of the filtered module. -/
theorem gr_finrank_eq [FiniteDimensional ℂ (UModG f R)]
    (hm : 1 ≤ m) :
    Module.finrank ℂ (Gr f R m) = Module.finrank ℂ (UModG f R) := by
  obtain ⟨D, hD⟩ := TU_vanish_star f R m hm
  have hnum : Module.finrank ℂ (grNumerator f R m) =
      ∑ i : Fin D, Module.finrank ℂ (TU f R m i) := by
    unfold grNumerator
    exact finiteSinglesStar_finrank D (fun j => TU f R m j) hD
  have hden : Module.finrank ℂ (grDenominator f R m) =
      ∑ i : Fin D, Module.finrank ℂ (TU f R m (i + 1)) := by
    unfold grDenominator
    apply finiteSinglesStar_finrank
    intro j hj
    exact hD (j + 1) (by omega)
  haveI : FiniteDimensional ℂ (grNumerator f R m) := by
    rw [grNumerator, ← finiteSinglesStar_range D (fun j => TU f R m j) hD]
    infer_instance
  have hker : Module.finrank ℂ (grKernel f R m) =
      Module.finrank ℂ (grDenominator f R m) := by
    have heq : (grKernel f R m).map (grNumerator f R m).subtype =
        grDenominator f R m := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, grDenominator_le_numerator f R m hx⟩, hx, rfl⟩
    rw [← heq]
    exact (Submodule.finrank_map_subtype_eq
      (grNumerator f R m) (grKernel f R m)).symm
  have htel : (∑ i : Fin D, Module.finrank ℂ (TU f R m (i + 1))) +
      Module.finrank ℂ (UModG f R) =
      ∑ i : Fin D, Module.finrank ℂ (TU f R m i) := by
    let a := fun j => Module.finrank ℂ (TU f R m j)
    have hshift : ∀ k,
        (∑ j ∈ Finset.range k, a (j + 1)) + a 0 =
          (∑ j ∈ Finset.range k, a j) + a k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          simp only [Finset.sum_range_succ]
          omega
    have hzero : a 0 = Module.finrank ℂ (UModG f R) := by
      change Module.finrank ℂ (TU f R m 0) = _
      rw [TU_zero f R m]
      exact finrank_top ℂ (UModG f R)
    have hlast : a D = 0 := by
      change Module.finrank ℂ (TU f R m D) = 0
      rw [hD D le_rfl]
      exact finrank_bot ℂ (UModG f R)
    have hs₁ : (∑ i : Fin D, a (i.val + 1)) =
        ∑ j ∈ Finset.range D, a (j + 1) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]
    have hs₀ : (∑ i : Fin D, a i.val) =
        ∑ j ∈ Finset.range D, a j := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]
    change (∑ i : Fin D, a (i.val + 1)) +
      Module.finrank ℂ (UModG f R) = ∑ i : Fin D, a i.val
    rw [hs₁, hs₀, ← hzero]
    simpa only [hlast, add_zero] using hshift D
  have hq := (grKernel f R m).finrank_quotient_add_finrank
  change Module.finrank ℂ (Gr f R m) +
    Module.finrank ℂ (grKernel f R m) =
      Module.finrank ℂ (grNumerator f R m) at hq
  rw [hnum, hker, hden] at hq
  omega

private def finiteSinglesStar_equiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : ℕ) (A : ℕ → Submodule ℂ V)
    (hvanish : ∀ j, D ≤ j → A j = ⊥) :
    ((i : Fin D) → A i) ≃ₗ[ℂ]
      Submodule.span ℂ {v | ∃ j x, x ∈ A j ∧ v = Finsupp.single j x} := by
  let S : Submodule ℂ (ℕ →₀ V) :=
    Submodule.span ℂ {v | ∃ j x, x ∈ A j ∧ v = Finsupp.single j x}
  let L := (finiteSinglesStar D A).codRestrict S (by
    intro x
    change finiteSinglesStar D A x ∈
      Submodule.span ℂ {v | ∃ j y, y ∈ A j ∧ v = Finsupp.single j y}
    rw [← finiteSinglesStar_range D A hvanish]
    exact ⟨x, rfl⟩)
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · intro x y h
    apply finiteSinglesStar_injective D A
    exact congrArg Subtype.val h
  · intro y
    have hy : y.1 ∈ LinearMap.range (finiteSinglesStar D A) := by
      rw [finiteSinglesStar_range D A hvanish]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

/-- The finite numerator is exactly the product of its filtration terms. -/
def grNumerator_equiv_pi (D : ℕ)
    (hD : ∀ j, D ≤ j → TU f R m j = ⊥) :
    grNumerator f R m ≃ₗ[ℂ] ((i : Fin D) → TU f R m i) := by
  change Submodule.span ℂ
    {v | ∃ j x, x ∈ TU f R m j ∧ v = Finsupp.single j x} ≃ₗ[ℂ] _
  exact (finiteSinglesStar_equiv D (fun j => TU f R m j) hD).symm

/-- The finite kernel is exactly the product of the next filtration terms. -/
def grKernel_equiv_pi (D : ℕ)
    (hD : ∀ j, D ≤ j → TU f R m j = ⊥) :
    grKernel f R m ≃ₗ[ℂ] ((i : Fin D) → TU f R m (i + 1)) := by
  let e : grKernel f R m ≃ₗ[ℂ] grDenominator f R m :=
    Submodule.comapSubtypeEquivOfLe (grDenominator_le_numerator f R m)
  have hshift : ∀ j, D ≤ j → TU f R m (j + 1) = ⊥ := by
    intro j hj
    exact hD (j + 1) (by omega)
  exact e.trans (by
    change Submodule.span ℂ
      {v | ∃ j x, x ∈ TU f R m (j + 1) ∧ v = Finsupp.single j x} ≃ₗ[ℂ] _
    exact (finiteSinglesStar_equiv D (fun j => TU f R m (j + 1)) hshift).symm)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.gr_finrank_eq
#print axioms VOA.DeligneAudit.Toroidal.grNumerator_equiv_pi
#print axioms VOA.DeligneAudit.Toroidal.grKernel_equiv_pi
