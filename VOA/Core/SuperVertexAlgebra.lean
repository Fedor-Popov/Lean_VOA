/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.VertexAlgebra
import VOA.Foundations.Parity
import VOA.Core.DongSuper

/-!
# Super vertex algebras: the core axioms with both generalizations

The vertex-algebra axioms of `Core.VertexAlgebra`, generalized along **two independent
axes**:

* **Axis A — the weight grading.**  `grading : ℂ → Submodule ℂ 𝒱` rather than `ℤ → …`,
  so half-integer (indeed arbitrary complex) conformal weights are admissible.  This makes
  the algebra grading agree with the module grading, which is already `ℂ`-valued
  throughout `Modules/`.
* **Axis B — parity.**  A second, independent `ZMod 2` grading, entering VA4 through the
  Koszul sign: locality is `Localε (koszul p q)`, not `Local`.

**The two axes are deliberately not linked.**  There is no spin–statistics field.  A
structure may have half-integer weights and be purely even (symplectic bosons `βγ`), or
integer weights and be odd (the `bc` ghost system), or both (the free fermion).  Where a
theorem genuinely needs the relation it takes `SpinStatistics` as an explicit hypothesis.

## Main definitions

* `SuperVertexAlgebra` — VA1–VA5 with a `ℂ`-valued weight grading and a `ZMod 2` parity.
* `SpinStatistics` — the *predicate* "integer weight ⟺ even parity", never a field.
* `PreVertexAlgebra.toSuper` — every ordinary vertex algebra is a super vertex algebra, with
  its `ℤ`-grading pushed forward along `ℤ ↪ ℂ` and purely even parity.  So this is a
  generalization of `Core.VertexAlgebra`, not a parallel hierarchy.

## Implementation notes

The mode index stays `ℤ`.  Only the *grading* index moves to `ℂ`: `Y(u,z) = ∑_{n∈ℤ} u₍ₙ₎
z^{-n-1}` regardless of conformal weights, which is why the whole Borcherds / locality /
Dong apparatus is untouched by Axis A.

`isInternal_extend` is the general fact that an internal grading pushes forward along an
injective reindexing (with `⊥` off the image).  It is what makes `toSuper` possible and is
stated separately because it is not specific to vertex algebras.

## References
* Gannon §5.1.3 (Def. 5.1.3a) for the bosonic axioms; Kac, *Vertex Algebras for
  Beginners*, §1.3, §4.1 for the super case.
-/

namespace VOA

open Module (End)

universe u

/-! ## Pushing an internal grading forward along an injection -/

section Pushforward

variable {ι κ : Type*} {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Reindex a family of submodules along `f`, taking `⊥` outside the image of `f`. -/
noncomputable def extendGrading (f : ι → κ) (A : ι → Submodule ℂ M) : κ → Submodule ℂ M :=
  Function.extend f A (fun _ => ⊥)

/-- On the image of an injective `f`, the reindexed family is the original one. -/
theorem extendGrading_apply {f : ι → κ} (hf : Function.Injective f) (A : ι → Submodule ℂ M)
    (i : ι) : extendGrading f A (f i) = A i :=
  hf.extend_apply A _ i

/-- Off the image of `f`, the reindexed family is `⊥`. -/
theorem extendGrading_of_notMem_range {f : ι → κ} (A : ι → Submodule ℂ M) {k : κ}
    (hk : ¬∃ i, f i = k) : extendGrading f A k = ⊥ :=
  Function.extend_apply' A _ k hk

/-- **An internal grading pushes forward along an injective reindexing.**

This is what lets an ordinary `ℤ`-graded vertex algebra be read as a `ℂ`-graded one
without changing any of its content. -/
theorem isInternal_extend [DecidableEq ι] [DecidableEq κ] {f : ι → κ}
    (hf : Function.Injective f)
    {A : ι → Submodule ℂ M} (hA : DirectSum.IsInternal A) :
    DirectSum.IsInternal (extendGrading f A) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hA ⊢
  obtain ⟨hindep, htop⟩ := hA
  constructor
  · intro k
    by_cases hk : ∃ i, f i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [extendGrading_apply hf]
      -- the competing supremum collapses onto the original one
      have hsup : (⨆ (k' : κ) (_ : k' ≠ f i), extendGrading f A k')
          = ⨆ (j : ι) (_ : j ≠ i), A j := by
        refine le_antisymm (iSup₂_le fun k' hk' => ?_) (iSup₂_le fun j hj => ?_)
        · by_cases hk'' : ∃ j, f j = k'
          · obtain ⟨j, rfl⟩ := hk''
            have hji : j ≠ i := fun h => hk' (by rw [h])
            rw [extendGrading_apply hf]
            exact le_iSup₂ (f := fun j (_ : j ≠ i) => A j) j hji
          · rw [extendGrading_of_notMem_range A hk'']
            exact bot_le
        · have : f j ≠ f i := fun h => hj (hf h)
          rw [← extendGrading_apply hf A j]
          exact le_iSup₂ (f := fun k' (_ : k' ≠ f i) => extendGrading f A k') (f j) this
      rw [hsup]
      exact iSupIndep_def.1 hindep i
    · rw [extendGrading_of_notMem_range A hk]
      exact disjoint_bot_left
  · refine le_antisymm le_top (htop ▸ iSup_le fun i => ?_)
    rw [← extendGrading_apply hf A i]
    exact le_iSup (extendGrading f A) (f i)

end Pushforward

/-! ## The super vertex-algebra axioms -/

/-- A **super vertex algebra**: the axioms VA1–VA5 of `Core.VertexAlgebra`, with a
`ℂ`-valued conformal-weight grading (Axis A) and an independent `ZMod 2` parity grading
entering locality through the Koszul sign (Axis B).

Setting the parity trivial recovers a `ℂ`-graded ordinary vertex algebra; restricting the
grading to `ℤ` recovers `Core.VertexAlgebra` (`PreVertexAlgebra.toSuper`).

⚠ **Not a vertex superalgebra in the standard sense.**  Like `PreVertexAlgebra`, this structure has
no translation-covariance axiom `Y(Tu,z) = ∂_z Y(u,z)` and no (super-)Jacobi identity: VA1–VA5
with Koszul-signed locality do not imply them (certificate `L17Counter.toSuper_superJacobi_fails` in
`Notes/Textbook/certificates/L17_Checks.lean`). Translation covariance enters only with the
conformal layer, as VOA3 of `SuperNearVOA` (`SuperNearVOA.translation`). -/
structure SuperVertexAlgebra (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] where
  /-- **Axis A.** The conformal-weight grading `𝒱 = ⊕_{h ∈ ℂ} 𝒱_h`. -/
  grading : ℂ → Submodule ℂ 𝒱
  /-- The weight grading is a genuine internal direct-sum decomposition. -/
  isInternal : DirectSum.IsInternal grading
  /-- Each homogeneous weight space is finite-dimensional. -/
  finrank : ∀ h, FiniteDimensional ℂ (grading h)
  /-- **Axis B.** The parity grading `𝒱 = 𝒱₀̄ ⊕ 𝒱₁̄`, independent of the weight grading. -/
  parity : ZMod 2 → Submodule ℂ 𝒱
  /-- The parity grading is a genuine internal direct-sum decomposition. -/
  parity_isInternal : DirectSum.IsInternal parity
  /-- The state–field correspondence `Y(u,z) = ∑_{n ∈ ℤ} u₍ₙ₎ z^{-n-1}`.  The mode index
  is `ℤ` whatever the conformal weights. -/
  Y : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧
  /-- The vacuum vector `𝟙`. -/
  vacuum : 𝒱
  /-- The vacuum has conformal weight `0`. -/
  vacuum_mem : vacuum ∈ grading 0
  /-- The vacuum is even. -/
  vacuum_parity : vacuum ∈ parity 0
  /-- **VA1 (weight).** For `u ∈ 𝒱_h` and `v ∈ 𝒱_k`, `u₍ₙ₎v ∈ 𝒱_{h+k-n-1}`. -/
  grading_mode : ∀ {h k : ℂ} (u : 𝒱), u ∈ grading h → ∀ (v : 𝒱), v ∈ grading k →
    ∀ (n : ℤ), mode (Y u) n v ∈ grading (h + k - n - 1)
  /-- **VA1′ (parity).** Modes add parities: `u₍ₙ₎v` has parity `|u| + |v|`.  This is what
  makes the Koszul signs compose (`koszul_add_left`), and hence what makes the
  super-Jacobi identity close. -/
  parity_mode : ∀ {p q : ZMod 2} (u : 𝒱), u ∈ parity p → ∀ (v : 𝒱), v ∈ parity q →
    ∀ (n : ℤ), mode (Y u) n v ∈ parity (p + q)
  /-- **VA2 (vacuum).** `Y(𝟙,z) = id`. -/
  vacuum_Y : Y vacuum = (1 : (End ℂ 𝒱)⟦z^±⟧)
  /-- **VA3 (state–field correspondence).** `u₍₋₁₎𝟙 = u` and `u₍ₙ₎𝟙 = 0` for `n ≥ 0`. -/
  creation : ∀ u : 𝒱, mode (Y u) (-1) vacuum = u ∧ ∀ n : ℤ, 0 ≤ n → mode (Y u) n vacuum = 0
  /-- **VA4 (super-locality).** Parity-homogeneous fields are mutually local *up to the
  Koszul sign*: `(z₁-z₂)^N (Y(u,z₁)Y(v,z₂) - (-1)^{|u||v|} Y(v,z₂)Y(u,z₁)) = 0`. -/
  locality : ∀ {p q : ZMod 2} (u : 𝒱), u ∈ parity p → ∀ (v : 𝒱), v ∈ parity q →
    Localε (koszul p q) (Y u) (Y v)
  /-- **VA5 (regularity).** For each `u, v` there is `N` with `u₍ₙ₎v = 0` for `n ≥ N`. -/
  regularity : ∀ u v : 𝒱, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (Y u) n v = 0

/-! ## Spin–statistics as a predicate -/

/-- **Spin–statistics**, stated as a predicate and never as a structure field: a nonzero
vector of integer conformal weight is even, and one of non-integer weight is odd.

Building this into `SuperVertexAlgebra` would silently exclude exactly the examples the
super generalization exists to admit — `βγ` (half-integer weights, purely even) and the
`bc` ghosts (integer weights, odd).  A theorem that needs the relation should take this as
a hypothesis. -/
def SpinStatistics {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : SuperVertexAlgebra 𝒱) : Prop :=
  ∀ (h : ℂ) (p : ZMod 2) (u : 𝒱), u ≠ 0 → u ∈ W.grading h → u ∈ W.parity p →
    ((∃ m : ℤ, (m : ℂ) = h) ↔ p = 0)

/-! ## The mode API -/

namespace SuperVertexAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The `n`-th product `u₍ₙ₎v`, exactly as in the bosonic case: the mode index is `ℤ`
whatever the conformal weights. -/
def smul (V : SuperVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) : 𝒱 := mode (V.Y u) n v

theorem smul_def (V : SuperVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul u n v = mode (V.Y u) n v := rfl

/-- `u₍ₙ₎v` is the `z^{-n-1}` coefficient of `Y(u,z)` applied to `v`. -/
theorem smul_eq_coeff (V : SuperVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul u n v = V.Y u (-n - 1) v := rfl

/-- **VA1 in mode form.**  Weights add and drop by `n+1`. -/
theorem smul_mem_grading (V : SuperVertexAlgebra 𝒱) {h k : ℂ} {u v : 𝒱}
    (hu : u ∈ V.grading h) (hv : v ∈ V.grading k) (n : ℤ) :
    V.smul u n v ∈ V.grading (h + k - n - 1) :=
  V.grading_mode u hu v hv n

/-- **VA1′ in mode form.**  Parities add. -/
theorem smul_mem_parity (V : SuperVertexAlgebra 𝒱) {p q : ZMod 2} {u v : 𝒱}
    (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) (n : ℤ) :
    V.smul u n v ∈ V.parity (p + q) :=
  V.parity_mode u hu v hv n

/-- **VA3.** `u₍₋₁₎𝟙 = u`. -/
@[simp] theorem smul_neg_one_vacuum (V : SuperVertexAlgebra 𝒱) (u : 𝒱) :
    V.smul u (-1) V.vacuum = u := (V.creation u).1

/-- **VA3.** `u₍ₙ₎𝟙 = 0` for `n ≥ 0`. -/
theorem smul_vacuum_eq_zero (V : SuperVertexAlgebra 𝒱) (u : 𝒱) {n : ℤ} (hn : 0 ≤ n) :
    V.smul u n V.vacuum = 0 := (V.creation u).2 n hn

/-- The translation operator `T u = u₍₋₂₎𝟙`, as in the bosonic case. -/
def T (V : SuperVertexAlgebra 𝒱) (u : 𝒱) : 𝒱 := V.smul u (-2) V.vacuum

theorem T_def (V : SuperVertexAlgebra 𝒱) (u : 𝒱) : V.T u = V.smul u (-2) V.vacuum := rfl

/-- Super-locality of the vertex operators, in the form `Dong`'s lemma consumes. -/
theorem localε_Y (V : SuperVertexAlgebra 𝒱) {p q : ZMod 2} {u v : 𝒱}
    (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) :
    Localε (koszul p q) (V.Y u) (V.Y v) :=
  V.locality u hu v hv

/-- **Dong's lemma for the fields of a super vertex algebra.**

The field `k`-th product of `Y(u,·)` and `Y(v,·)` is local with `Y(w,·)` *up to the Koszul
sign of the product field against `w`* — and the product field's parity is `|u| + |v|`,
exactly as `parity_mode` says it should be.  The sign bookkeeping closing here is the
coherence check that `koszul`, `Localε` and `parity_mode` were defined compatibly. -/
theorem dong_fields (V : SuperVertexAlgebra 𝒱) {p q r : ZMod 2} {u v w : 𝒱}
    (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) (hw : w ∈ V.parity r) (k : ℕ) :
    Localε (koszul (p + q) r)
      (cCoeff k (bracketDistε (koszul p q) (V.Y u) (V.Y v))) (V.Y w) := by
  rw [koszul_add_left]
  exact dong_nonnegε (koszul_mul_self p q) (V.localε_Y hu hv) (V.localε_Y hu hw)
    (V.localε_Y hv hw) k

end SuperVertexAlgebra

/-! ## Every ordinary vertex algebra is a super vertex algebra -/

namespace PreVertexAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The `ℂ`-valued weight grading of an ordinary `ℤ`-graded vertex algebra: the original
grading on integer weights, `⊥` elsewhere. -/
noncomputable def gradingC (V : PreVertexAlgebra 𝒱) : ℂ → Submodule ℂ 𝒱 :=
  extendGrading (fun n : ℤ => (n : ℂ)) V.grading

@[simp] theorem gradingC_intCast (V : PreVertexAlgebra 𝒱) (n : ℤ) :
    V.gradingC (n : ℂ) = V.grading n :=
  extendGrading_apply (fun _ _ h => Int.cast_injective h) V.grading n

/-- Off the integers the `ℂ`-graded reading of an ordinary vertex algebra is trivial. -/
theorem gradingC_of_not_int (V : PreVertexAlgebra 𝒱) {h : ℂ} (hh : ¬∃ n : ℤ, (n : ℂ) = h) :
    V.gradingC h = ⊥ :=
  extendGrading_of_notMem_range V.grading hh

/-- **Every ordinary vertex algebra is a super vertex algebra**: `ℤ`-weights read as
`ℂ`-weights, and purely even parity, so that every Koszul sign is `1` and VA4 reduces to
ordinary locality.  This is what makes `SuperVertexAlgebra` a generalization of
`PreVertexAlgebra` rather than a parallel hierarchy. -/
noncomputable def toSuper (V : PreVertexAlgebra 𝒱) : SuperVertexAlgebra 𝒱 where
  grading := V.gradingC
  isInternal := by
    classical
    exact isInternal_extend (fun _ _ h => Int.cast_injective h) V.isInternal
  finrank h := by
    classical
    by_cases hh : ∃ n : ℤ, (n : ℂ) = h
    · obtain ⟨n, rfl⟩ := hh
      rw [V.gradingC_intCast]
      exact V.finrank n
    · rw [V.gradingC_of_not_int hh]
      infer_instance
  parity := (ParityGrading.even 𝒱).parity
  parity_isInternal := (ParityGrading.even 𝒱).isInternal
  Y := V.Y
  vacuum := V.vacuum
  vacuum_mem := by
    have h0 : ((0 : ℤ) : ℂ) = 0 := by norm_num
    rw [← h0, V.gradingC_intCast]
    exact V.vacuum_mem
  vacuum_parity := by simp [ParityGrading.even]
  grading_mode := by
    classical
    intro h k u hu v hv n
    by_cases hh : ∃ a : ℤ, (a : ℂ) = h
    · obtain ⟨a, rfl⟩ := hh
      by_cases hk : ∃ b : ℤ, (b : ℂ) = k
      · obtain ⟨b, rfl⟩ := hk
        rw [V.gradingC_intCast] at hu hv
        have : ((a : ℂ) + b - n - 1) = ((a + b - n - 1 : ℤ) : ℂ) := by push_cast; ring
        rw [this, V.gradingC_intCast]
        exact V.grading_mode u hu v hv n
      · rw [V.gradingC_of_not_int hk, Submodule.mem_bot] at hv
        subst hv
        simp only [map_zero]
        exact Submodule.zero_mem _
    · rw [V.gradingC_of_not_int hh, Submodule.mem_bot] at hu
      subst hu
      simp only [map_zero]
      exact Submodule.zero_mem _
  parity_mode := by
    classical
    intro p q u hu v hv n
    by_cases hp : p = 0
    · by_cases hq : q = 0
      · subst hp; subst hq
        simp [ParityGrading.even]
      · rw [ParityGrading.eq_zero_of_mem_even_of_ne hq hv]
        simp only [map_zero]
        exact Submodule.zero_mem _
    · rw [ParityGrading.eq_zero_of_mem_even_of_ne hp hu]
      simp only [map_zero]
      exact Submodule.zero_mem _
  vacuum_Y := V.vacuum_Y
  creation := V.creation
  locality := by
    classical
    intro p q u hu v hv
    by_cases hp : p = 0
    · by_cases hq : q = 0
      · -- both even: every Koszul sign is `1`, so VA4 is ordinary locality
        subst hp; subst hq
        rw [show koszul (0 : ZMod 2) 0 = 1 by simp, localε_one_iff]
        exact V.locality u v
      · rw [ParityGrading.eq_zero_of_mem_even_of_ne hq hv, map_zero]
        exact localε_zero_right _ _
    · rw [ParityGrading.eq_zero_of_mem_even_of_ne hp hu, map_zero]
      exact localε_zero_left _ _
  regularity := V.regularity

/-- The mode structure is untouched by `toSuper`: every fact proved about `V.smul` is a
fact about the super reading of `V`.  (`Y` is literally the same map.) -/
@[simp] theorem toSuper_smul (V : PreVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    V.toSuper.smul u n v = V.smul u n v := rfl

/-- Likewise the vacuum. -/
@[simp] theorem toSuper_vacuum (V : PreVertexAlgebra 𝒱) : V.toSuper.vacuum = V.vacuum := rfl

end PreVertexAlgebra

end VOA
