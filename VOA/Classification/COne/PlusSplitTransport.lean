import VOA.Classification.COne.PlusSplitEqualBottom

/-! Spectral and submodule transport for weak-module homomorphisms. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible
universe u
variable {V X Y : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  {W : VertexOperatorAlgebra V}

theorem map_mem_maxGenEigenspace (f : Module.End ℂ X) (g : Module.End ℂ Y)
    (π : X →ₗ[ℂ] Y) (hc : ∀ x, π (f x) = g (π x)) (h : ℂ)
    {x : X} (hx : x ∈ f.maxGenEigenspace h) : π x ∈ g.maxGenEigenspace h := by
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace f h x).mp hx
  apply (Module.End.mem_maxGenEigenspace g h (π x)).mpr
  refine ⟨n, ?_⟩
  have hp : ∀ (n : ℕ) (x : X), π (((f - h • 1) ^ n) x) = ((g - h • 1) ^ n) (π x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hc, ih]
  rw [← hp, hn, map_zero]

/-- Local finiteness makes generalized eigenspaces exact under intertwining
maps, including maps with nontrivial kernel and non-surjective maps. -/
theorem map_inf_maxGenEigenspace (f : Module.End ℂ X) (g : Module.End ℂ Y)
    (π : X →ₗ[ℂ] Y) (hc : ∀ x, π (f x) = g (π x))
    (hloc : ∀ x : X, ∃ S : Submodule ℂ X, FiniteDimensional ℂ S ∧ x ∈ S ∧
      ∀ y ∈ S, f y ∈ S)
    (P : Submodule ℂ X) (hP : ∀ x ∈ P, f x ∈ P) (h : ℂ) :
    (P ⊓ f.maxGenEigenspace h).map π = P.map π ⊓ g.maxGenEigenspace h := by
  classical
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, map_mem_maxGenEigenspace f g π hc h hx.2⟩
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    let T : Submodule ℂ X := ⨆ k, ⨆ (_ : k ≠ h), P ⊓ f.maxGenEigenspace k
    have hd : P ≤ (P ⊓ f.maxGenEigenspace h) ⊔ T := by
      calc
        P = ⨆ k, P ⊓ f.maxGenEigenspace k :=
          eq_iSup_inf_maxGenEigenspace_of_locally_finite f hloc P hP
        _ ≤ _ := ?_
      apply iSup_le
      intro k
      by_cases hk : k = h
      · subst k; exact le_sup_left
      · intro z hz
        exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem k
          (Submodule.mem_iSup_of_mem hk hz))
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp (hd hx)
    have hb' : π b ∈ ⨆ k, ⨆ (_ : k ≠ h), g.maxGenEigenspace k := by
      have ht : T ≤ (⨆ k, ⨆ (_ : k ≠ h), g.maxGenEigenspace k).comap π := by
        apply iSup_le; intro k; apply iSup_le; intro hk z hz
        exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk
          (map_mem_maxGenEigenspace f g π hc k hz.2))
      exact ht hb
    have hz : π b = 0 := by
      apply Submodule.disjoint_def.mp ((g.independent_genEigenspace ⊤) h)
      · have eqb : π b = π x - π a := by rw [← he, map_add]; abel
        rw [eqb]
        exact (g.maxGenEigenspace h).sub_mem hy
          (map_mem_maxGenEigenspace f g π hc h ha.2)
      · exact hb'
    exact ⟨a, ha, by rw [← he, map_add, hz, add_zero]⟩

/-- Image using the actual mode algebra of the target. -/
def modeMap {A : WeakModule W X} {B : WeakModule W Y} (π : A.Hom B)
    (P : Submodule (modeAlg A) X) : Submodule (modeAlg B) Y :=
  toR B { carrier := (P.restrictScalars ℂ).map π.toLinearMap
          act_mem := by
            rintro v n y ⟨x, hx, rfl⟩
            exact ⟨A.act v n x, (ofR A P).act_mem v n hx, π.map_act v n x⟩ }

/-- Preimage using the actual mode algebra of the source. -/
def modeComap {A : WeakModule W X} {B : WeakModule W Y} (π : A.Hom B)
    (P : Submodule (modeAlg B) Y) : Submodule (modeAlg A) X :=
  toR A { carrier := (P.restrictScalars ℂ).comap π.toLinearMap
          act_mem := by
            intro v n x hx
            change π.toLinearMap (A.act v n x) ∈ P
            rw [π.map_act]
            exact (ofR B P).act_mem v n hx }

variable {A : WeakModule W X} {B : WeakModule W Y}

theorem modeMap_le_iff (π : A.Hom B) (P : Submodule (modeAlg A) X)
    (Q : Submodule (modeAlg B) Y) : modeMap π P ≤ Q ↔ P ≤ modeComap π Q := by
  change (P.restrictScalars ℂ).map π.toLinearMap ≤ Q.restrictScalars ℂ ↔
    P.restrictScalars ℂ ≤ (Q.restrictScalars ℂ).comap π.toLinearMap
  exact Submodule.map_le_iff_le_comap

theorem modeMap_mono (π : A.Hom B) : Monotone (modeMap π) :=
  fun _ _ h => Submodule.map_mono h

theorem modeComap_mono (π : A.Hom B) : Monotone (modeComap π) :=
  fun _ _ h _ hx => h hx

theorem modeComap_map (π : A.Hom B) (P : Submodule (modeAlg A) X) :
    modeComap π (modeMap π P) = P ⊔ modeComap π ⊥ := by
  apply Submodule.restrictScalars_injective ℂ
  change ((P.restrictScalars ℂ).map π.toLinearMap).comap π.toLinearMap = _
  rw [Submodule.comap_map_eq, Submodule.restrictScalars_sup]
  rfl

theorem modeMap_comap (π : A.Hom B) (Q : Submodule (modeAlg B) Y) :
    modeMap π (modeComap π Q) = Q ⊓ modeMap π ⊤ := by
  apply Submodule.restrictScalars_injective ℂ
  change ((Q.restrictScalars ℂ).comap π.toLinearMap).map π.toLinearMap = _
  rw [Submodule.map_comap_eq]
  change _ = Q.restrictScalars ℂ ⊓ (⊤ : Submodule ℂ X).map π.toLinearMap
  rw [Submodule.map_top, inf_comm]

theorem modeMap_sup (π : A.Hom B) (P Q : Submodule (modeAlg A) X) :
    modeMap π (P ⊔ Q) = modeMap π P ⊔ modeMap π Q := by
  apply Submodule.restrictScalars_injective ℂ
  change ((P ⊔ Q).restrictScalars ℂ).map π.toLinearMap =
    (modeMap π P ⊔ modeMap π Q).restrictScalars ℂ
  rw [Submodule.restrictScalars_sup, Submodule.restrictScalars_sup]
  exact Submodule.map_sup (P.restrictScalars ℂ) (Q.restrictScalars ℂ) π.toLinearMap

theorem modeComap_inf (π : A.Hom B) (P Q : Submodule (modeAlg B) Y) :
    modeComap π (P ⊓ Q) = modeComap π P ⊓ modeComap π Q := rfl

theorem modeMap_inf_comap (π : A.Hom B) (P : Submodule (modeAlg A) X)
    (Q : Submodule (modeAlg B) Y) :
    modeMap π (P ⊓ modeComap π Q) = modeMap π P ⊓ Q := by
  apply Submodule.restrictScalars_injective ℂ
  change ((P.restrictScalars ℂ) ⊓ (Q.restrictScalars ℂ).comap π.toLinearMap).map
    π.toLinearMap = (P.restrictScalars ℂ).map π.toLinearMap ⊓ Q.restrictScalars ℂ
  exact Submodule.map_inf_eq_map_inf_comap.symm

/-- Cover relations survive the image when the kernel is in the lower term. -/
theorem modeMap_covBy (π : A.Hom B) {P Q : Submodule (modeAlg A) X}
    (h : P ⋖ Q) (hk : modeComap π ⊥ ≤ P) : modeMap π P ⋖ modeMap π Q := by
  have hp : modeComap π (modeMap π P) = P := by
    rw [modeComap_map, sup_eq_left.mpr hk]
  have hq : modeComap π (modeMap π Q) = Q := by
    rw [modeComap_map, sup_eq_left.mpr (hk.trans h.le)]
  refine ⟨lt_of_le_of_ne (modeMap_mono π h.le) ?_, ?_⟩
  · intro he
    exact h.ne (by rw [← hp, ← hq, he])
  · intro D hPD hDQ
    have hl : P < modeComap π D := by
      apply lt_of_le_of_ne ((modeMap_le_iff π P D).mp hPD.le)
      intro he
      have hd : D ≤ modeMap π ⊤ := hDQ.le.trans (modeMap_mono π le_top)
      have he' := congrArg (modeMap π) he
      rw [modeMap_comap, inf_eq_left.mpr hd] at he'
      exact hPD.ne he'
    have hu : modeComap π D < Q := by
      apply lt_of_le_of_ne (by rw [← hq]; exact modeComap_mono π hDQ.le)
      intro he
      have hd : D ≤ modeMap π ⊤ := hDQ.le.trans (modeMap_mono π le_top)
      have he' := congrArg (modeMap π) he
      rw [modeMap_comap, inf_eq_left.mpr hd] at he'
      exact hDQ.ne he'
    exact h.2 hl hu

/-- Intrinsic factor weights are preserved by image, with no injectivity
assumption, when the kernel lies in the lower term. -/
theorem factorWeight_modeMap_iff (hC2 : C2Cofinite W) (π : A.Hom B)
    (P Q : Submodule (modeAlg A) X) (hk : modeComap π ⊥ ≤ P) (h : ℂ) :
    FactorWeight B (modeMap π P) (modeMap π Q) h ↔ FactorWeight A P Q h := by
  have hs := map_inf_maxGenEigenspace (L0 A) (L0 B) π.toLinearMap
    (π.map_act W.conformalVector 1) (weakL0LocallyFinite hC2 A)
    (Q.restrictScalars ℂ) (fun x hx => (ofR A Q).act_mem _ _ hx) h
  unfold FactorWeight
  change (¬ ((Q.restrictScalars ℂ).map π.toLinearMap ⊓ (L0 B).maxGenEigenspace h) ≤
      (P.restrictScalars ℂ).map π.toLinearMap) ↔ _
  rw [← hs, Submodule.map_le_iff_le_comap]
  have hp := congrArg (Submodule.restrictScalars ℂ) (modeComap_map π P)
  change ((P.restrictScalars ℂ).map π.toLinearMap).comap π.toLinearMap = _ at hp
  rw [hp, sup_eq_left.mpr hk]

theorem factorBottom_modeMap_iff (hC2 : C2Cofinite W) (π : A.Hom B)
    (P Q : Submodule (modeAlg A) X) (hk : modeComap π ⊥ ≤ P) (h : ℂ) :
    FactorBottom B (modeMap π P) (modeMap π Q) h ↔ FactorBottom A P Q h := by
  simp only [FactorBottom, factorWeight_modeMap_iff hC2 π P Q hk]

theorem modeComap_covBy (π : A.Hom B) {P Q : Submodule (modeAlg B) Y}
    (h : P ⋖ Q) (hr : Q ≤ modeMap π ⊤) : modeComap π P ⋖ modeComap π Q := by
  have hp : modeMap π (modeComap π P) = P := by
    rw [modeMap_comap, inf_eq_left.mpr (h.le.trans hr)]
  have hq : modeMap π (modeComap π Q) = Q := by
    rw [modeMap_comap, inf_eq_left.mpr hr]
  apply covBy_of_eq_or_eq (lt_of_le_of_ne (modeComap_mono π h.le) (fun he =>
    h.ne (by rw [← hp, ← hq, he])))
  intro D hPD hDQ
  have hd : modeComap π (modeMap π D) = D := by
    rw [modeComap_map, sup_eq_left.mpr ((modeComap_mono π bot_le).trans hPD)]
  have hl : P ≤ modeMap π D := by rw [← hp]; exact modeMap_mono π hPD
  have hu : modeMap π D ≤ Q := by rw [← hq]; exact modeMap_mono π hDQ
  rcases h.wcovBy.eq_or_eq hl hu with he | he
  · left; rw [← hd, he]
  · right; rw [← hd, he]

theorem modeMap_eq_iff (π : A.Hom B) {P Q : Submodule (modeAlg A) X}
    (hP : modeComap π ⊥ ≤ P) (hQ : modeComap π ⊥ ≤ Q) :
    modeMap π P = modeMap π Q ↔ P = Q := by
  constructor
  · intro he
    have := congrArg (modeComap π) he
    simpa only [modeComap_map, sup_eq_left.mpr hP, sup_eq_left.mpr hQ] using this
  · exact congrArg _

/-- Relative complements pull back along an arbitrary weak-module map when
the kernel lies in the bottom endpoint. -/
theorem relativeComplement_of_modeMap (π : A.Hom B)
    {a b c : Submodule (modeAlg A) X} (hab : a ≤ b) (hbc : b ≤ c)
    (hk : modeComap π ⊥ ≤ a)
    (hs : ∃ D : Submodule (modeAlg B) Y,
      modeMap π a ≤ D ∧ D ≤ modeMap π c ∧
      modeMap π b ⊓ D = modeMap π a ∧ modeMap π b ⊔ D = modeMap π c) :
    ∃ d : Submodule (modeAlg A) X, a ≤ d ∧ d ≤ c ∧ b ⊓ d = a ∧ b ⊔ d = c := by
  obtain ⟨D, haD, hDc, hi, hu⟩ := hs
  let d := c ⊓ modeComap π D
  have had : a ≤ d := le_inf (hab.trans hbc) ((modeMap_le_iff π a D).mp haD)
  have hd : modeMap π d = D := by
    rw [modeMap_inf_comap, inf_eq_right.mpr hDc]
  refine ⟨d, had, inf_le_left, ?_, ?_⟩
  · apply (modeMap_eq_iff π (le_inf (hk.trans hab) (hk.trans had)) hk).mp
    have he : b ⊓ d = b ⊓ modeComap π D := by
      dsimp [d]; rw [← inf_assoc, inf_eq_left.mpr hbc]
    rw [he, modeMap_inf_comap, hi]
  · apply (modeMap_eq_iff π ((hk.trans hab).trans le_sup_left) (hk.trans (hab.trans hbc))).mp
    rw [modeMap_sup, hd, hu]

end VOA.Classification.COne.PlusSplitting
