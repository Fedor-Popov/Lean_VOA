import VOA.Huang.DLNSmallLayer

/-!
# Inflation through a Schur cover

`MultAtMostTwo Q`: in every central extension of `Q`, the derived subgroup meets the kernel in at
most two elements (homology-free form of `|H₂(Q)| ≤ 2`).

If `ρ : C ↠ A` is a central extension whose kernel contains a nontrivial element of `[C,C]` and
`MultAtMostTwo A`, then `ρ` has trivial inflation. The proof applies the bound to the fibre
product `E ×_A C`, a central extension of `A` in which both `(αx, 1)` and a lift `(z, k₀)` of the
nontrivial kernel element lie in the derived subgroup.

We also generalize the layer reduction from Schur-trivial quotients to trivial inflation.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

/-- Homology-free form of "the Schur multiplier of `Q` has order at most two". -/
def MultAtMostTwo (Q : Type) [Group Q] : Prop :=
  ∀ (E : Type) [Group E] (π : E →* Q), Function.Surjective π → π.ker ≤ Subgroup.center E →
    ∀ x ∈ commutator E, ∀ y ∈ commutator E, π x = 1 → π y = 1 → x = 1 ∨ y = 1 ∨ x = y

theorem inflationTrivial_comp {A B C : Type} [Group A] [Group B] [Group C] (ρ : C →* A)
    (s : B →* C) (h : InflationTrivial ρ) : InflationTrivial (ρ.comp s) := by
  intro E _ π hs hc F _ α β hcomp x hx hβx
  exact h E π hs hc F α (s.comp β) (by rw [hcomp]; rfl) x hx (by simp [hβx])

/-- **Inflation through a Schur cover.** -/
theorem inflationTrivial_of_cover {A C : Type} [Group A] [Group C] (ρ : C →* A)
    (hρ : Function.Surjective ρ) (hcen : ρ.ker ≤ Subgroup.center C) (k₀ : C)
    (hk₀ : k₀ ∈ commutator C) (hρk : ρ k₀ = 1) (hk1 : k₀ ≠ 1) (hA : MultAtMostTwo A) :
    InflationTrivial ρ := by
  intro E _ π hs hc F _ α β hcomp x hx hβx
  -- The fibre product.
  let P : Subgroup (E × C) :=
    MonoidHom.eqLocus (π.comp (MonoidHom.fst E C)) (ρ.comp (MonoidHom.snd E C))
  have hmemP : ∀ p : E × C, p ∈ P ↔ π p.1 = ρ p.2 := fun p => Iff.rfl
  let πP : P →* A := (π.comp (MonoidHom.fst E C)).comp P.subtype
  have hπP : ∀ p : P, πP p = π (p : E × C).1 := fun p => rfl
  have hπPs : Function.Surjective πP := by
    intro a
    obtain ⟨c, hc'⟩ := hρ a
    obtain ⟨e, he⟩ := hs a
    exact ⟨⟨(e, c), by rw [hmemP]; simp [he, hc']⟩, by simp [hπP, he]⟩
  have hπPc : πP.ker ≤ Subgroup.center P := by
    intro p hp
    have h1 : π (p : E × C).1 = 1 := hp
    have h2 : ρ (p : E × C).2 = 1 := by rw [← (hmemP _).mp p.2, h1]
    have hz1 := hc h1
    have hz2 := hcen h2
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.mp hz1 _
    · exact Subgroup.mem_center_iff.mp hz2 _
  -- The image of `x`.
  let φ : F →* P := (α.prod β).codRestrict P (fun f => by
    rw [hmemP]; exact congrArg (fun h : F →* A => h f) hcomp)
  have hφx : φ x ∈ commutator P := by
    have hmap : (commutator F).map φ ≤ commutator P := by
      rw [map_commutator_eq, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hmap ⟨x, hx, rfl⟩
  have hπφx : πP (φ x) = 1 := by
    rw [hπP]
    change π (α x) = 1
    have := congrArg (fun h : F →* A => h x) hcomp
    simp only [MonoidHom.comp_apply] at this
    rw [this, hβx, map_one]
  -- A derived lift of `k₀`.
  let sndP : P →* C := (MonoidHom.snd E C).comp P.subtype
  have hsnd : Function.Surjective sndP := by
    intro c
    obtain ⟨e, he⟩ := hs (ρ c)
    exact ⟨⟨(e, c), by rw [hmemP]; exact he⟩, rfl⟩
  have hk₀' : k₀ ∈ (commutator P).map sndP := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hsnd, ← commutator_def]
    exact hk₀
  obtain ⟨p, hp, hpk⟩ := hk₀'
  have hπp : πP p = 1 := by
    rw [hπP, (hmemP _).mp p.2]
    change ρ (sndP p) = 1
    rw [hpk, hρk]
  rcases hA P πP hπPs hπPc (φ x) hφx p hp hπφx hπp with h | h | h
  · have := congrArg (fun q : P => (q : E × C).1) h
    simpa [φ] using this
  · exfalso; apply hk1
    rw [← hpk, h, map_one]
  · exfalso; apply hk1
    have := congrArg sndP h
    rw [hpk] at this
    rw [← this]
    change β x = 1
    exact hβx

/-- **Layer reduction through trivial inflation.** If `ρ : G ↠ Ḡ` has trivial inflation, every
derived kernel element of a central extension of `G` lies in `⁅E, π⁻¹(ker ρ)⁆`. -/
theorem mem_layer_commutator_of_inflationTrivial {G Gb E : Type} [Group G] [Group Gb]
    [Group E] (ρ : G →* Gb) (hρ : Function.Surjective ρ) (hinf : InflationTrivial ρ)
    (π : E →* G) (hs : Function.Surjective π)
    (x : E) (hx : x ∈ commutator E) (hπx : π x = 1) :
    x ∈ ⁅(⊤ : Subgroup E), ρ.ker.comap π⁆ := by
  set M : Subgroup E := ρ.ker.comap π with hM
  set K : Subgroup E := ⁅(⊤ : Subgroup E), M⁆ with hK
  haveI : M.Normal := by rw [hM]; infer_instance
  haveI : K.Normal := by rw [hK]; exact Subgroup.commutator_normal ⊤ M
  have hKle : K ≤ (ρ.comp π).ker := by
    rw [hK, Subgroup.commutator_le]
    intro e _ m hm
    have hm' : ρ (π m) = 1 := hm
    simp [MonoidHom.mem_ker, map_commutatorElement, hm']
  let ψ : E ⧸ K →* Gb := QuotientGroup.lift K (ρ.comp π) hKle
  have hψs : Function.Surjective ψ := by
    intro g
    obtain ⟨h, rfl⟩ := hρ g
    obtain ⟨e, rfl⟩ := hs h
    exact ⟨QuotientGroup.mk e, rfl⟩
  have hψc : ψ.ker ≤ Subgroup.center (E ⧸ K) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective K y
    have he : e ∈ M := hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective K w
    have hcomm : ⁅d, e⁆ ∈ K := Subgroup.commutator_mem_commutator (Subgroup.mem_top d) he
    have h1 : (QuotientGroup.mk' K) ⁅d, e⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have h1 := hinf (E ⧸ K) ψ hψs hψc E (QuotientGroup.mk' K) π (by ext; rfl) x hx hπx
  exact (QuotientGroup.eq_one_iff x).mp h1

/-- The layer condition with "at most two" in place of "trivial". -/
def LayerAtMostTwo {G Gb : Type} [Group G] [Group Gb] (ρ : G →* Gb) : Prop :=
  ∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π → π.ker ≤ Subgroup.center E →
    ∀ x ∈ ⁅(⊤ : Subgroup E), ρ.ker.comap π⁆, ∀ y ∈ ⁅(⊤ : Subgroup E), ρ.ker.comap π⁆,
      π x = 1 → π y = 1 → x = 1 ∨ y = 1 ∨ x = y

/-- **Inductive step for the multiplier bound.** -/
theorem multAtMostTwo_of_inflation_layer {G Gb : Type} [Group G] [Group Gb] (ρ : G →* Gb)
    (hρ : Function.Surjective ρ) (hinf : InflationTrivial ρ) (hL : LayerAtMostTwo ρ) :
    MultAtMostTwo G := by
  intro E _ π hs hc x hx y hy hπx hπy
  exact hL E π hs hc x (mem_layer_commutator_of_inflationTrivial ρ hρ hinf π hs x hx hπx)
    y (mem_layer_commutator_of_inflationTrivial ρ hρ hinf π hs y hy hπy) hπx hπy

theorem layerAtMostTwo_of_multAtMostTwo {G Gb : Type} [Group G] [Group Gb] (ρ : G →* Gb)
    (hG : MultAtMostTwo G) : LayerAtMostTwo ρ := by
  intro E _ π hs hc x hx y hy hπx hπy
  have hle : ⁅(⊤ : Subgroup E), ρ.ker.comap π⁆ ≤ commutator E := by
    rw [commutator_def]; exact Subgroup.commutator_mono le_rfl le_top
  exact hG E π hs hc x (hle hx) y (hle hy) hπx hπy

theorem multAtMostTwo_of_schurTrivial {Q : Type} [Group Q] (h : SchurTrivial Q) :
    MultAtMostTwo Q := by
  intro E _ π hs hc x hx y _ hπx _
  exact Or.inl ((schurTrivial_iff_centralDerivedInjective Q).mp h E π hs hc x hx hπx)

end VOA.Huang.DLNSchur
