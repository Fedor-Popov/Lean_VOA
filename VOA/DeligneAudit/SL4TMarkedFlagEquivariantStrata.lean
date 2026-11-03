import VOA.DeligneAudit.SL4TMarkedFlagJointStratumCount

/-!
# The marked full-flag strata as representations of the position symmetries

The subject is the `S_U × S_V`-equivariant isomorphism `C/G_j ≅ gr C[X_{<j}]` and the passage to
invariants.

A permutation `π` of the roots that preserves the marked group `V` and the selected set `Y` carries
every marked configuration to another one with the same number of selected doubles: the zero
point(s) move to `π⁻¹` of themselves and the remaining paired configuration is relabelled by the
permutation `deletedPositionPerm` induced on the other positions (`singlyMarkedPoint_relabel`,
`doublyMarkedPoint_relabel`, and the matching statements for the selected doubles). So the finite
point set of the configurations with fewer than `j` selected doubles is stable under every group
`G` acting by such permutations.

For any finite injective point set stable under a group of coordinate permutations,
`stablePointAction` is the induced action on its index set, and the invariants of the leading
relation algebra have dimension the number of orbits (`stablePointQuotient_fixed_finrank`). Since
the marked stratum ideals **equal** these leading-relation ideals
(`SL4TMarkedFlagStratumExactness`), the position representation on each stratum quotient
`ℂ[x]/(flag relations + G_j)` has invariants of dimension the number of `G`-orbits of
configurations with fewer than `j` selected doubles
(`singlyMarkedSelectedStratum_invariant_finrank`,
`doublyMarkedOneSelectedStratum_invariant_finrank`,
`doublyMarkedTwoSelectedStratum_invariant_finrank`).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-! ### Actions on stable point sets -/

section StableAction

variable {ι σ G : Type*} [Group G]

/-- A group permuting coordinates acts on the index set of an injective point set that it
preserves. -/
def stablePointAction (x : ι → σ → ℂ) (hx : Function.Injective x)
    (η : G →* Equiv.Perm σ) (hst : ∀ (g : G) i, ∃ i', x i' = fun s => x i (η g⁻¹ s)) :
    MulAction G ι where
  smul g i := Classical.choose (hst g i)
  one_smul i := by
    show Classical.choose (hst 1 i) = i
    apply hx
    rw [Classical.choose_spec (hst 1 i)]
    funext s
    simp
  mul_smul g h i := by
    show Classical.choose (hst (g * h) i) = Classical.choose (hst g (Classical.choose (hst h i)))
    apply hx
    rw [Classical.choose_spec (hst (g * h) i), Classical.choose_spec (hst g _)]
    funext s
    rw [Classical.choose_spec (hst h i)]
    simp [mul_inv_rev, Equiv.Perm.mul_apply]

theorem stablePointAction_equivariant (x : ι → σ → ℂ) (hx : Function.Injective x)
    (η : G →* Equiv.Perm σ) (hst : ∀ (g : G) i, ∃ i', x i' = fun s => x i (η g⁻¹ s)) :
    letI := stablePointAction x hx η hst
    ∀ (g : G) i s, x (g⁻¹ • i) s = x i (η g s) := by
  intro g i s
  show x (Classical.choose (hst g⁻¹ i)) s = _
  rw [Classical.choose_spec (hst g⁻¹ i), inv_inv]

/-- **Invariants of a stable point set.** The invariants of the leading-relation algebra of a
finite injective point set stable under a finite group of coordinate permutations have dimension
the number of orbits. -/
theorem stablePointQuotient_fixed_finrank [Fintype G] [Fintype ι] (x : ι → σ → ℂ)
    (hx : Function.Injective x) (η : G →* Equiv.Perm σ)
    (hst : ∀ (g : G) i, ∃ i', x i' = fun s => x i (η g⁻¹ s)) :
    letI := stablePointAction x hx η hst
    Module.finrank ℂ (pointInitialRepresentation x η
        (stablePointAction_equivariant x hx η hst)).invariants =
      Nat.card (MulAction.orbitRel.Quotient G ι) := by
  letI := stablePointAction x hx η hst
  exact pointInitialQuotient_fixed_finrank x hx η (stablePointAction_equivariant x hx η hst)

end StableAction

/-! ### Relabelling marked configurations -/

/-- The permutation of the remaining positions induced by a permutation `π`, when the deleted
position `π⁻¹ v` is sent to `v`. -/
def deletedPositionPerm {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1)) :
    Equiv.Perm (Fin n) :=
  Equiv.removeNone (((finSuccEquiv' (π.symm v)).symm.trans π).trans (finSuccEquiv' v))

theorem deletedPositionPerm_spec {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1))
    (j : Fin n) : v.succAbove (deletedPositionPerm π v j) = π ((π.symm v).succAbove j) := by
  have hne : π ((π.symm v).succAbove j) ≠ v := by
    intro h
    have h' := congrArg π.symm h
    rw [Equiv.symm_apply_apply] at h'
    exact Fin.succAbove_ne _ _ h'
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hne
  have hsome : (((finSuccEquiv' (π.symm v)).symm.trans π).trans (finSuccEquiv' v)) (some j) =
      some j' := by
    simp only [Equiv.trans_apply, finSuccEquiv'_symm_some, ← hj', finSuccEquiv'_succAbove]
  have h := Equiv.removeNone_some _ ⟨j', hsome⟩
  rw [hsome] at h
  unfold deletedPositionPerm
  rw [Option.some_injective _ h, hj']

/-- The relabelled singly marked configuration. -/
def singlyMarkedRelabel (B k : ℕ) (V V' : Finset (Fin (B + 1))) (π : Equiv.Perm (Fin (B + 1)))
    (hV : ∀ i, π i ∈ V ↔ i ∈ V') (c : SinglyMarkedConfiguration B k V) :
    SinglyMarkedConfiguration B k V' :=
  ⟨⟨π.symm c.1.val, (hV _).mp (by rw [Equiv.apply_symm_apply]; exact c.1.property)⟩,
    fullFlagConfiguration_relabel B k (deletedPositionPerm π c.1.val).symm c.2⟩

theorem singlyMarkedPoint_relabel (B k : ℕ) (V V' : Finset (Fin (B + 1)))
    (ζ : Fin (B - k) → ℂ) (π : Equiv.Perm (Fin (B + 1))) (hV : ∀ i, π i ∈ V ↔ i ∈ V')
    (c : SinglyMarkedConfiguration B k V) :
    singlyMarkedPoint B k V' ζ (singlyMarkedRelabel B k V V' π hV c) =
      fun s => singlyMarkedPoint B k V ζ c (π s) := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove (π.symm c.1.val) i with h | ⟨j, rfl⟩
  · rw [h]
    simp [singlyMarkedPoint, singlyMarkedRelabel]
  · rw [← deletedPositionPerm_spec]
    simp [singlyMarkedPoint, singlyMarkedRelabel, fullFlagConfiguration_relabel]

theorem deletedGroup_relabel {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1))
    (Y Y' : Finset (Fin (n + 1))) (hY : ∀ i, π i ∈ Y ↔ i ∈ Y') :
    deletedGroup (π.symm v) Y' = (deletedGroup v Y).map (deletedPositionPerm π v).symm.toEmbedding
    := by
  ext j
  rw [Finset.mem_map_equiv, Equiv.symm_symm, mem_deletedGroup, mem_deletedGroup,
    deletedPositionPerm_spec, hY]

theorem singlyMarkedSelectedDoubles_relabel (B k : ℕ) (V V' Y Y' : Finset (Fin (B + 1)))
    (π : Equiv.Perm (Fin (B + 1))) (hV : ∀ i, π i ∈ V ↔ i ∈ V')
    (hY : ∀ i, π i ∈ Y ↔ i ∈ Y')
    (c : SinglyMarkedConfiguration B k V) :
    singlyMarkedSelectedDoubles Y' (singlyMarkedRelabel B k V V' π hV c) =
      singlyMarkedSelectedDoubles Y c := by
  unfold singlyMarkedSelectedDoubles singlyMarkedRelabel
  dsimp only
  rw [deletedGroup_relabel π c.1.val Y Y' hY, fullFlagDoublesIn_relabel]

/-- The relabelled doubly marked configuration. -/
def doublyMarkedRelabel (B k : ℕ) (V : Finset (Fin (B + 2))) (π : Equiv.Perm (Fin (B + 2)))
    (hV : ∀ i, π i ∈ V ↔ i ∈ V) (c : DoublyMarkedConfiguration B k V) :
    DoublyMarkedConfiguration B k V :=
  ⟨⟨π.symm c.1.val, fun h => c.1.property (by
      have := (hV (π.symm c.1.val)).mpr h
      rwa [Equiv.apply_symm_apply] at this)⟩,
    singlyMarkedRelabel B k (deletedGroup c.1.val V) (deletedGroup (π.symm c.1.val) V)
      (deletedPositionPerm π c.1.val)
      (fun i => by rw [mem_deletedGroup, mem_deletedGroup, deletedPositionPerm_spec, hV])
      c.2⟩

theorem doublyMarkedPoint_relabel (B k : ℕ) (V : Finset (Fin (B + 2))) (ζ : Fin (B - k) → ℂ)
    (π : Equiv.Perm (Fin (B + 2))) (hV : ∀ i, π i ∈ V ↔ i ∈ V)
    (c : DoublyMarkedConfiguration B k V) :
    doublyMarkedPoint B k V ζ (doublyMarkedRelabel B k V π hV c) =
      fun s => doublyMarkedPoint B k V ζ c (π s) := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove (π.symm c.1.val) i with h | ⟨j, rfl⟩
  · rw [h]
    simp [doublyMarkedPoint, doublyMarkedRelabel]
  · have hs := congrFun (singlyMarkedPoint_relabel B k (deletedGroup c.1.val V)
      (deletedGroup (π.symm c.1.val) V) ζ (deletedPositionPerm π c.1.val)
      (fun i => by rw [mem_deletedGroup, mem_deletedGroup, deletedPositionPerm_spec, hV])
      c.2) j
    rw [← deletedPositionPerm_spec]
    simp only [doublyMarkedPoint, doublyMarkedRelabel, Fin.insertNth_apply_succAbove]
    exact hs

theorem doublyMarkedSelectedDoubles_relabel (B k : ℕ) (V Y : Finset (Fin (B + 2)))
    (π : Equiv.Perm (Fin (B + 2))) (hV : ∀ i, π i ∈ V ↔ i ∈ V)
    (hY : ∀ i, π i ∈ Y ↔ i ∈ Y)
    (c : DoublyMarkedConfiguration B k V) :
    doublyMarkedSelectedDoubles Y (doublyMarkedRelabel B k V π hV c) =
      doublyMarkedSelectedDoubles Y c := by
  have hY1 : ∀ i, deletedPositionPerm π c.1.val i ∈ deletedGroup c.1.val Y ↔
      i ∈ deletedGroup (π.symm c.1.val) Y := fun i => by
    rw [mem_deletedGroup, mem_deletedGroup, deletedPositionPerm_spec, hY]
  have hsingle := singlyMarkedSelectedDoubles_relabel B k (deletedGroup c.1.val V)
    (deletedGroup (π.symm c.1.val) V) (deletedGroup c.1.val Y) (deletedGroup (π.symm c.1.val) Y)
    (deletedPositionPerm π c.1.val)
    (fun i => by rw [mem_deletedGroup, mem_deletedGroup, deletedPositionPerm_spec, hV]) hY1 c.2
  unfold singlyMarkedSelectedDoubles at hsingle
  unfold doublyMarkedSelectedDoubles
  have hu : (doublyMarkedRelabel B k V π hV c).1.val ∈ Y ↔ c.1.val ∈ Y := by
    show π.symm c.1.val ∈ Y ↔ _
    rw [← hY (π.symm c.1.val), Equiv.apply_symm_apply]
  have hw : (doublyMarkedRelabel B k V π hV c).1.val.succAbove
      (doublyMarkedRelabel B k V π hV c).2.1.val ∈ Y ↔ c.1.val.succAbove c.2.1.val ∈ Y := by
    show (π.symm c.1.val).succAbove ((deletedPositionPerm π c.1.val).symm c.2.1.val) ∈ Y ↔ _
    rw [← hY ((π.symm c.1.val).succAbove ((deletedPositionPerm π c.1.val).symm c.2.1.val)),
      ← deletedPositionPerm_spec, Equiv.apply_symm_apply]
  have hd : fullFlagDoublesIn (deletedGroup (doublyMarkedRelabel B k V π hV c).2.1.val
      (deletedGroup (doublyMarkedRelabel B k V π hV c).1.val Y))
        (doublyMarkedRelabel B k V π hV c).2.2 =
      fullFlagDoublesIn (deletedGroup c.2.1.val (deletedGroup c.1.val Y)) c.2.2 := hsingle
  rw [hd]
  congr 1
  by_cases h1 : c.1.val ∈ Y <;> by_cases h2 : c.1.val.succAbove c.2.1.val ∈ Y <;>
    simp [h1, h2, hu, hw]

/-! ### Stability of the stratum point sets and their invariants -/

theorem singlyMarkedStratumPoint_stable {G : Type*} [Group G] (B k j : ℕ)
    (V Y : Finset (Fin (B + 1))) (ζ : Fin (B - k) → ℂ) (η : G →* Equiv.Perm (Fin (B + 1)))
    (hηV : ∀ g i, η g i ∈ V ↔ i ∈ V) (hηY : ∀ g i, η g i ∈ Y ↔ i ∈ Y) (g : G)
    (c : {c : SinglyMarkedConfiguration B k V // singlyMarkedSelectedDoubles Y c < j}) :
    ∃ c', singlyMarkedStratumPoint B k j V Y ζ c' =
      fun s => singlyMarkedStratumPoint B k j V Y ζ c (η g⁻¹ s) :=
  ⟨⟨singlyMarkedRelabel B k V V (η g⁻¹) (hηV g⁻¹) c.val, by
      rw [singlyMarkedSelectedDoubles_relabel B k V V Y Y (η g⁻¹) (hηV g⁻¹) (hηY g⁻¹)]
      exact c.property⟩,
    singlyMarkedPoint_relabel B k V V ζ (η g⁻¹) (hηV g⁻¹) c.val⟩

theorem doublyMarkedStratumPoint_stable {G : Type*} [Group G] (B k j : ℕ)
    (V Y : Finset (Fin (B + 2))) (ζ : Fin (B - k) → ℂ) (η : G →* Equiv.Perm (Fin (B + 2)))
    (hηV : ∀ g i, η g i ∈ V ↔ i ∈ V) (hηY : ∀ g i, η g i ∈ Y ↔ i ∈ Y) (g : G)
    (c : {c : DoublyMarkedConfiguration B k V // doublyMarkedSelectedDoubles Y c < j}) :
    ∃ c', doublyMarkedStratumPoint B k j V Y ζ c' =
      fun s => doublyMarkedStratumPoint B k j V Y ζ c (η g⁻¹ s) :=
  ⟨⟨doublyMarkedRelabel B k V (η g⁻¹) (hηV g⁻¹) c.val, by
      rw [doublyMarkedSelectedDoubles_relabel B k V Y (η g⁻¹) (hηV g⁻¹) (hηY g⁻¹)]
      exact c.property⟩,
    doublyMarkedPoint_relabel B k V ζ (η g⁻¹) (hηV g⁻¹) c.val⟩

/-- The standard injective nonzero site values `1, 2, …`. -/
def standardSites (h : ℕ) : Fin h → ℂ := fun a => (a.val : ℂ) + 1

theorem standardSites_injective (h : ℕ) : Function.Injective (standardSites h) := by
  intro a b hab
  apply Fin.ext
  have h' : (a.val : ℂ) = b.val := by simpa [standardSites] using hab
  exact_mod_cast h'

theorem standardSites_ne_zero (h : ℕ) (a : Fin h) : standardSites h a ≠ 0 := by
  intro hab
  have h' : ((a.val + 1 : ℕ) : ℂ) = 0 := by simpa [standardSites] using hab
  exact Nat.succ_ne_zero a.val (by exact_mod_cast h')

theorem singlyMarkedStratumPoint_injective (B k j : ℕ) (V Y : Finset (Fin (B + 1))) :
    Function.Injective (singlyMarkedStratumPoint B k j V Y (standardSites (B - k))) :=
  fun a b h => Subtype.ext (singlyMarkedPoint_injective _ _ V _ (standardSites_injective _)
    (standardSites_ne_zero _) h)

theorem doublyMarkedStratumPoint_injective (B k j : ℕ) (V Y : Finset (Fin (B + 2))) :
    Function.Injective (doublyMarkedStratumPoint B k j V Y (standardSites (B - k))) :=
  fun a b h => Subtype.ext (doublyMarkedPoint_injective _ _ V _ (standardSites_injective _)
    (standardSites_ne_zero _) h)

/-- **Equivariant singly marked stratum.** For a finite group of position permutations
preserving `V` and `Y`, the stratum quotient `ℂ[x]/(flag relations + G_1)` is the
leading-relation algebra of the configurations without a selected double, and its invariants
have dimension the number of orbits of those configurations. -/
theorem singlyMarkedSelectedStratum_invariant_finrank {G : Type*} [Group G] [Fintype G]
    (m : ℕ) (hm : 1 ≤ m) (V Y : Finset (Fin (m + 2))) (hV : V.Nonempty) (hY : Y.Nonempty)
    (hZ : Yᶜ.Nonempty) (η : G →* Equiv.Perm (Fin (m + 2)))
    (hηV : ∀ g i, η g i ∈ V ↔ i ∈ V) (hηY : ∀ g i, η g i ∈ Y ↔ i ∈ Y) :
    singlyMarkedSelectedStratumIdeal m V Y =
        pointInitialIdeal (singlyMarkedStratumPoint (m + 1) 1 1 V Y (standardSites (m + 1 - 1)))
      ∧
    (letI := stablePointAction _ (singlyMarkedStratumPoint_injective (m + 1) 1 1 V Y) η
      (singlyMarkedStratumPoint_stable (m + 1) 1 1 V Y _ η hηV hηY)
    Module.finrank ℂ (pointInitialRepresentation _ η (stablePointAction_equivariant _
        (singlyMarkedStratumPoint_injective (m + 1) 1 1 V Y) η
        (singlyMarkedStratumPoint_stable (m + 1) 1 1 V Y _ η hηV hηY))).invariants =
      Nat.card (MulAction.orbitRel.Quotient G
        {c : SinglyMarkedConfiguration (m + 1) 1 V // singlyMarkedSelectedDoubles Y c < 1})) :=
  ⟨singlyMarkedSelectedStratumIdeal_eq m hm V Y hV hY hZ _ (standardSites_injective _)
      (standardSites_ne_zero _),
    stablePointQuotient_fixed_finrank _ _ η _⟩

/-- **Equivariant doubly marked stratum, one selected double.** -/
theorem doublyMarkedOneSelectedStratum_invariant_finrank {G : Type*} [Group G] [Fintype G]
    (m : ℕ) (hm : 1 ≤ m) (V Y : Finset (Fin (m + 3))) (hV : V.Nonempty) (hU : Vᶜ.Nonempty)
    (hY : Y.Nonempty) (hZ : Yᶜ.Nonempty) (η : G →* Equiv.Perm (Fin (m + 3)))
    (hηV : ∀ g i, η g i ∈ V ↔ i ∈ V) (hηY : ∀ g i, η g i ∈ Y ↔ i ∈ Y) :
    doublyMarkedOneSelectedStratumIdeal m V Y =
        pointInitialIdeal (doublyMarkedStratumPoint (m + 1) 1 1 V Y (standardSites (m + 1 - 1)))
      ∧
    (letI := stablePointAction _ (doublyMarkedStratumPoint_injective (m + 1) 1 1 V Y) η
      (doublyMarkedStratumPoint_stable (m + 1) 1 1 V Y _ η hηV hηY)
    Module.finrank ℂ (pointInitialRepresentation _ η (stablePointAction_equivariant _
        (doublyMarkedStratumPoint_injective (m + 1) 1 1 V Y) η
        (doublyMarkedStratumPoint_stable (m + 1) 1 1 V Y _ η hηV hηY))).invariants =
      Nat.card (MulAction.orbitRel.Quotient G
        {c : DoublyMarkedConfiguration (m + 1) 1 V // doublyMarkedSelectedDoubles Y c < 1})) :=
  ⟨doublyMarkedOneSelectedStratumIdeal_eq m hm V Y hV hU hY hZ _ (standardSites_injective _)
      (standardSites_ne_zero _),
    stablePointQuotient_fixed_finrank _ _ η _⟩

/-- **Equivariant doubly marked stratum, two selected doubles.** -/
theorem doublyMarkedTwoSelectedStratum_invariant_finrank {G : Type*} [Group G] [Fintype G]
    (m : ℕ) (hm : 1 ≤ m) (V Y : Finset (Fin (m + 3))) (hV : V.Nonempty) (hU : Vᶜ.Nonempty)
    (hY2 : 2 ≤ Y.card) (hZ : Yᶜ.Nonempty) (η : G →* Equiv.Perm (Fin (m + 3)))
    (hηV : ∀ g i, η g i ∈ V ↔ i ∈ V) (hηY : ∀ g i, η g i ∈ Y ↔ i ∈ Y) :
    doublyMarkedTwoSelectedStratumIdeal m V Y =
        pointInitialIdeal (doublyMarkedStratumPoint (m + 1) 1 2 V Y (standardSites (m + 1 - 1)))
      ∧
    (letI := stablePointAction _ (doublyMarkedStratumPoint_injective (m + 1) 1 2 V Y) η
      (doublyMarkedStratumPoint_stable (m + 1) 1 2 V Y _ η hηV hηY)
    Module.finrank ℂ (pointInitialRepresentation _ η (stablePointAction_equivariant _
        (doublyMarkedStratumPoint_injective (m + 1) 1 2 V Y) η
        (doublyMarkedStratumPoint_stable (m + 1) 1 2 V Y _ η hηV hηY))).invariants =
      Nat.card (MulAction.orbitRel.Quotient G
        {c : DoublyMarkedConfiguration (m + 1) 1 V // doublyMarkedSelectedDoubles Y c < 2})) :=
  ⟨doublyMarkedTwoSelectedStratumIdeal_eq m hm V Y hV hU hY2 hZ _ (standardSites_injective _)
      (standardSites_ne_zero _),
    stablePointQuotient_fixed_finrank _ _ η _⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.stablePointAction
#print axioms VOA.DeligneAudit.SL4T.stablePointAction_equivariant
#print axioms VOA.DeligneAudit.SL4T.stablePointQuotient_fixed_finrank
#print axioms VOA.DeligneAudit.SL4T.deletedPositionPerm
#print axioms VOA.DeligneAudit.SL4T.deletedPositionPerm_spec
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedRelabel
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedPoint_relabel
#print axioms VOA.DeligneAudit.SL4T.deletedGroup_relabel
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedDoubles_relabel
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedRelabel
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedPoint_relabel
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedSelectedDoubles_relabel
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedStratumPoint_stable
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratumPoint_stable
#print axioms VOA.DeligneAudit.SL4T.standardSites
#print axioms VOA.DeligneAudit.SL4T.standardSites_injective
#print axioms VOA.DeligneAudit.SL4T.standardSites_ne_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedStratumPoint_injective
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratumPoint_injective
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedStratum_invariant_finrank
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneSelectedStratum_invariant_finrank
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedTwoSelectedStratum_invariant_finrank
