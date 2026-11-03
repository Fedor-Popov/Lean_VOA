/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ConvergenceBridge
import VOA.Core.Automorphism
import VOA.Modules.FiniteGenerationProof
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Twisted modules and orbifolds  (Gannon §5.3.6, pp. 345–348)

* **Vertex operator subalgebras** (`VOASubalgebra`): a graded subspace containing `𝟙` and `ω`
  and closed under all products `u₍ₙ₎v`.  **A subalgebra is a VOA** (`VOASubalgebra.toVOA`):
  the restricted state–field correspondence satisfies every axiom of `VertexOperatorAlgebra`,
  with the induced grading (internal, finite-dimensional, CFT type), locality (restricted
  commutators), the same central charge, Virasoro relation and translation.
* **The orbifold** `𝒱^G` (`orbifold`): for a subgroup `G ≤ Aut(𝒱)`, the fixed points
  `{v | ∀ g ∈ G, g v = v}` form a `VOASubalgebra` (automorphisms fix `𝟙`, `ω`, intertwine the
  products and preserve the grading), hence **`𝒱^G` is a VOA** (`orbifoldVOA`).  This is the
  construction that produces `V♮` as the `±1`-orbifold of the Leech lattice VOA.
* **`g`-twisted modules** (5.3.22): for `g ∈ Aut(𝒱)` of order `N`, the eigenspaces
  `𝒱ʲ = {v | g v = ξ_N^{−j} v}` (`Aut.twistedEigenspace`), and `Y_M(u,z) = Σ_{r ∈ −j/N+ℤ} u₍ᵣ₎ z^{−r−1}`
  for `u ∈ 𝒱ʲ` — the fractional-exponent carrier is indexed by `k ∈ ℤ` with `r = k/N`
  (`TwistedModule.YM u k` is `u₍k/N₎`); the support condition (5.3.22a) and the twisted Jacobi
  identity (5.3.22b, mode form, DLM) are fields.
* **Twisted trace functions** (5.3.23): `𝒵(M,h;τ) = q^{−c/24} tr_M φ(h) q^{L₀}` (`twistedTrace`),
  with `φ(h)` carried as the (projective) action of `h`.
* **Conjecture 5.3.10** (Dong–Mason et al.), as a `Prop` (`Conjecture_5_3_10`) — a *conjecture*,
  never asserted.

## Status
`VOASubalgebra`, `VOASubalgebra.toVOA`, `orbifold`, `orbifoldVOA`, `TwistedModule`,
`twistedTrace`, `Conjecture_5_3_10` are real declarations, axiom-clean, `pbw`-free.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Vertex operator subalgebras -/

/-- **A vertex operator subalgebra**: a subspace containing `𝟙` and `ω`, closed under all products
`u₍ₙ₎v`, and **graded** (stable under the projections onto the homogeneous pieces). -/
structure VOASubalgebra (W : VertexOperatorAlgebra 𝒱) where
  carrier : Submodule ℂ 𝒱
  vacuum_mem : W.vacuum ∈ carrier
  conformal_mem : W.conformalVector ∈ carrier
  smul_mem : ∀ u ∈ carrier, ∀ (n : ℤ), ∀ v ∈ carrier, W.smul u n v ∈ carrier
  graded : ∀ (n : ℤ), ∀ v ∈ carrier, piHom W n v ∈ carrier

namespace VOASubalgebra

variable {W : VertexOperatorAlgebra 𝒱} (S : VOASubalgebra W)

/-- Every coefficient of `Y(u,z)` preserves the subalgebra when `u` does. -/
theorem coeff_mem {u : 𝒱} (hu : u ∈ S.carrier) (k : ℤ) {x : 𝒱} (hx : x ∈ S.carrier) :
    W.Y u k x ∈ S.carrier := by
  have := S.smul_mem u hu (-k - 1) x hx
  rwa [PreVertexAlgebra.smul_def, mode_apply, show -(-k - 1) - 1 = k from by ring] at this

/-- The restricted state–field correspondence `Y_S(u,z)`, `u ∈ S`. -/
noncomputable def YS : S.carrier →ₗ[ℂ] FormalDist (Module.End ℂ S.carrier) where
  toFun u := fun k => (W.Y u k).restrict (fun x hx => S.coeff_mem u.2 k hx)
  map_add' u v := by
    funext k
    ext x
    simp only [Submodule.coe_add, map_add, LinearMap.restrict_apply]
    rfl
  map_smul' c u := by
    funext k
    ext x
    simp only [Submodule.coe_smul, map_smul, LinearMap.restrict_apply, RingHom.id_apply]
    rfl

@[simp] theorem YS_apply_coe (u : S.carrier) (k : ℤ) (x : S.carrier) :
    ((S.YS u k x : S.carrier) : 𝒱) = W.Y u k x := rfl

@[simp] theorem mode_YS_coe (u : S.carrier) (n : ℤ) (x : S.carrier) :
    ((mode (S.YS u) n x : S.carrier) : 𝒱) = mode (W.Y u) n x := rfl

/-- The induced grading `Sₙ = S ∩ 𝒱ₙ`. -/
def gradingS (n : ℤ) : Submodule ℂ S.carrier := (W.grading n).comap S.carrier.subtype

theorem mem_gradingS {n : ℤ} {x : S.carrier} : x ∈ S.gradingS n ↔ (x : 𝒱) ∈ W.grading n := Iff.rfl

/-- The induced grading is finite-dimensional. -/
instance gradingS_finrank (n : ℤ) : FiniteDimensional ℂ (S.gradingS n) := by
  haveI := W.finrank n
  refine Module.Finite.of_injective (LinearMap.codRestrict (W.grading n)
    (S.carrier.subtype.comp (S.gradingS n).subtype) (fun x => x.2)) ?_
  intro x y hxy
  have := congrArg Subtype.val hxy
  simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
  exact Subtype.ext (Subtype.ext this)

/-- The induced grading is an internal direct sum. -/
theorem gradingS_isInternal : DirectSum.IsInternal S.gradingS := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · -- independence: pull back the independence of `W.grading` along the injective `subtype`
    have hW := W.isInternal.submodule_iSupIndep
    refine iSupIndep_def.mpr (fun i => ?_)
    rw [Submodule.disjoint_def]
    intro x hxi hxrest
    have h1 : (x : 𝒱) ∈ W.grading i := hxi
    have h2 : (x : 𝒱) ∈ ⨆ (j) (_ : j ≠ i), W.grading j := by
      have hmap : Submodule.map S.carrier.subtype (⨆ (j) (_ : j ≠ i), S.gradingS j)
          ≤ ⨆ (j) (_ : j ≠ i), W.grading j := by
        rw [Submodule.map_iSup]
        refine iSup_mono (fun j => ?_)
        rw [Submodule.map_iSup]
        refine iSup_mono (fun _ => ?_)
        exact Submodule.map_comap_le _ _
      exact hmap ⟨x, hxrest, rfl⟩
    have := (iSupIndep_def.mp hW i)
    rw [Submodule.disjoint_def] at this
    exact Subtype.ext (this _ h1 h2)
  · -- spanning: every `x ∈ S` is the (finite) sum of its homogeneous projections, all in `S`
    rw [eq_top_iff]
    intro x _
    classical
    have hdec := DirectSum.sum_support_decompose W.grading (x : 𝒱)
    have hx : x = ∑ n ∈ (DirectSum.decompose W.grading (x : 𝒱)).support,
        (⟨piHom W n (x : 𝒱), S.graded n x x.2⟩ : S.carrier) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hdec.symm
    rw [hx]
    refine Submodule.sum_mem _ (fun n _ => ?_)
    exact Submodule.mem_iSup_of_mem n (piHom_mem W n (x : 𝒱))

/-- Restricted commutators agree with the commutator's restriction, degree by degree. -/
theorem mulBySubPow_bracket_coe (u v : S.carrier) (N : ℕ) (m n : ℤ) (x : S.carrier) :
    ((mulBySubPow N (bracketDist (S.YS u) (S.YS v)) m n x : S.carrier) : 𝒱)
      = mulBySubPow N (bracketDist (W.Y u) (W.Y v)) m n x := by
  induction N generalizing m n with
  | zero =>
      simp only [mulBySubPow, LinearMap.id_apply, bracketDist_apply, LinearMap.sub_apply,
        Module.End.mul_apply, Submodule.coe_sub]
      rfl
  | succ N ih =>
      simp only [mulBySubPow, LinearMap.comp_apply, mulBySub_apply, LinearMap.sub_apply,
        Submodule.coe_sub, ih]

/-- **A vertex operator subalgebra is a vertex operator algebra**, with the restricted
state–field correspondence, the induced grading, and the same central charge. -/
noncomputable def toVOA : VertexOperatorAlgebra S.carrier where
  grading := S.gradingS
  isInternal := S.gradingS_isInternal
  finrank := S.gradingS_finrank
  Y := S.YS
  vacuum := ⟨W.vacuum, S.vacuum_mem⟩
  vacuum_mem := by rw [mem_gradingS]; exact W.vacuum_mem
  grading_mode := by
    intro k l u hu v hv n
    rw [mem_gradingS] at hu hv ⊢
    rw [mode_YS_coe]
    exact W.grading_mode u hu v hv n
  vacuum_Y := by
    funext k
    ext x
    rw [YS_apply_coe, W.vacuum_Y, FormalDist.one_apply, FormalDist.one_apply]
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk]
  creation := by
    intro u
    refine ⟨Subtype.ext ?_, fun n hn => Subtype.ext ?_⟩
    · rw [mode_YS_coe]; exact (W.creation u).1
    · rw [mode_YS_coe, Submodule.coe_zero]; exact (W.creation u).2 n hn
  locality := by
    intro u v
    obtain ⟨N, hN⟩ := W.locality u v
    refine ⟨N, ?_⟩
    funext m n
    ext x
    rw [S.mulBySubPow_bracket_coe u v N m n x, hN]
    rfl
  regularity := by
    intro u v
    obtain ⟨N, hN⟩ := W.regularity u v
    exact ⟨N, fun n hn => Subtype.ext (by rw [mode_YS_coe, hN n hn]; rfl)⟩
  conformalVector := ⟨W.conformalVector, S.conformal_mem⟩
  conformal_mem := by rw [mem_gradingS]; exact W.conformal_mem
  centralCharge := W.centralCharge
  virasoro := by
    intro m n
    ext x
    have h := congrArg (fun T : Module.End ℂ 𝒱 => T (x : 𝒱)) (W.virasoro m n)
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply] at h ⊢
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, mode_YS_coe]
    rw [h]
    split_ifs <;> simp
  L0_grading := by
    intro n v hv
    rw [mem_gradingS] at hv
    exact Subtype.ext (by rw [mode_YS_coe, Submodule.coe_smul]; exact W.L0_grading v hv)
  translation := by
    intro v
    funext k
    ext x
    rw [YS_apply_coe]
    change W.Y (mode (W.Y W.conformalVector) 0 v) k x = _
    rw [W.translation v, deriv_apply, deriv_apply, LinearMap.smul_apply, LinearMap.smul_apply]
    simp
  vacuum_grade := by
    ext x
    rw [mem_gradingS, W.vacuum_grade, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, Subtype.ext (by rw [Submodule.coe_smul]; exact hc)⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [← hc, Submodule.coe_smul]⟩
  positivity := by
    intro n hn
    ext x
    rw [mem_gradingS, W.positivity n hn]
    simp

theorem toVOA_centralCharge : S.toVOA.centralCharge = W.centralCharge := rfl

end VOASubalgebra

/-! ## The orbifold `𝒱^G` -/

section Orbifold
variable {W : VertexOperatorAlgebra 𝒱}

/-- Automorphisms preserve the grading: `α(𝒱ₙ) ⊆ 𝒱ₙ` (they fix `ω`, hence commute with `L₀`, and
`𝒱ₙ` is the `L₀`-eigenspace of eigenvalue `n`). -/
theorem Aut.map_grading (α : Aut W) {n : ℤ} {v : 𝒱} (hv : v ∈ W.grading n) :
    α v ∈ W.grading n := by
  -- `L₀ (α v) = α (L₀ v) = n • α v`
  have hL : W.L 0 (α v) = (n : ℂ) • α v := by
    have h := α.map_smul' W.conformalVector 1 v
    rw [α.map_omega] at h
    rw [VertexOperatorAlgebra.L_def, zero_add]
    change mode (W.Y W.conformalVector) 1 (α.toLinearEquiv v) = _
    rw [show mode (W.Y W.conformalVector) 1 (α.toLinearEquiv v)
        = W.smul W.conformalVector 1 (α.toLinearEquiv v) from rfl, ← h,
      show W.smul W.conformalVector 1 v = mode (W.Y W.conformalVector) 1 v from rfl,
      W.L0_grading v hv, LinearEquiv.map_smul]
  classical
  -- every homogeneous component of `α v` of degree `m ≠ n` vanishes
  have hcomp : ∀ m : ℤ, m ≠ n → piHom W m (α v) = 0 := by
    intro m hm
    have h1 : piHom W m (W.L 0 (α v)) = (m : ℂ) • piHom W m (α v) := by
      conv_lhs => rw [← DirectSum.sum_support_decompose W.grading (α v)]
      rw [map_sum, map_sum]
      conv_rhs => rw [← DirectSum.sum_support_decompose W.grading (α v), map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hj := (DirectSum.decompose W.grading (α v) j).2
      rw [VertexOperatorAlgebra.L_def, zero_add, W.L0_grading _ hj, LinearMap.map_smul]
      by_cases hjm : j = m
      · subst hjm; rfl
      · rw [piHom_of_mem_ne W hjm hj, smul_zero, smul_zero]
    rw [hL, LinearMap.map_smul] at h1
    have : ((m : ℂ) - n) • piHom W m (α v) = 0 := by rw [sub_smul, h1, sub_self]
    have hmn : ((m : ℂ) - n) ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hm
    exact (smul_eq_zero.mp this).resolve_left hmn
  rw [← DirectSum.sum_support_decompose W.grading (α v)]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hjn : j = n
  · subst hjn; exact (DirectSum.decompose W.grading (α v) j).2
  · have := hcomp j hjn
    rw [piHom_apply] at this
    rw [this]; exact Submodule.zero_mem _

/-- **Normality of `Inn`, conjugation form** (Gannon 5.2.4).  If `exp(u₍₀₎)` is the inner
automorphism `β` (`IsExpInner u β`) and `α : Aut W`, then `α β α⁻¹` is the inner automorphism
for `αu` (`IsExpInner (αu) (α β α⁻¹)`).  The weight-one membership `α u ∈ 𝒱₁` is automatic
(`Aut.map_grading`), so no hypothesis `hαu` is needed. -/
theorem VertexOperatorAlgebra.isExpInner_conj {u : W.grading 1} {β : Aut W}
    (hβ : VertexOperatorAlgebra.IsExpInner u β) (α : Aut W) :
    VertexOperatorAlgebra.IsExpInner (⟨α (u : 𝒱), α.map_grading u.2⟩ : W.grading 1)
      (α * β * α⁻¹) := by
  intro v
  obtain ⟨N, hN⟩ := hβ (α.toLinearEquiv.symm v)
  refine ⟨N, ?_⟩
  show α (β (α.toLinearEquiv.symm v)) = _
  rw [hN, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, VertexOperatorAlgebra.aut_zeroMode_pow]
  congr 2
  simp

/-- The homogeneous projections commute with automorphisms. -/
theorem Aut.map_piHom (α : Aut W) (n : ℤ) (v : 𝒱) : α (piHom W n v) = piHom W n (α v) := by
  classical
  have hsum : α v = ∑ j ∈ (DirectSum.decompose W.grading v).support, α (piHom W j v) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose W.grading v]
    exact map_sum α.toLinearEquiv.toLinearMap _ _
  rw [hsum, map_sum, Finset.sum_eq_single n]
  · rw [piHom_of_mem W (α.map_grading (piHom_mem W n v))]
  · intro j _ hjn
    rw [piHom_of_mem_ne W hjn (α.map_grading (piHom_mem W j v))]
  · intro hn
    rw [DFinsupp.notMem_support_iff] at hn
    rw [show piHom W n v = 0 from by rw [piHom_apply, hn]; rfl, map_zero, map_zero]

/-- **The fixed-point subalgebra `𝒱^G`** of a subgroup `G ≤ Aut(𝒱)`. -/
def orbifold (G : Subgroup (Aut W)) : VOASubalgebra W where
  carrier :=
    { carrier := {v | ∀ g ∈ G, g v = v}
      add_mem' := fun {a b} ha hb g hg => by
        change g.toLinearEquiv (a + b) = a + b
        rw [map_add]; exact congrArg₂ (· + ·) (ha g hg) (hb g hg)
      zero_mem' := fun g _ => by change g.toLinearEquiv 0 = 0; exact map_zero _
      smul_mem' := fun c {a} ha g hg => by
        change g.toLinearEquiv (c • a) = c • a
        rw [map_smul]; exact congrArg (c • ·) (ha g hg) }
  vacuum_mem := fun g _ => g.map_vacuum
  conformal_mem := fun g _ => g.map_omega
  smul_mem := fun u hu n v hv g hg => by
    rw [g.map_smul', hu g hg, hv g hg]
  graded := fun n v hv g hg => by
    rw [g.map_piHom, hv g hg]

/-- **The orbifold `𝒱^G` is a vertex operator algebra.** -/
noncomputable def orbifoldVOA (G : Subgroup (Aut W)) :
    VertexOperatorAlgebra (orbifold G).carrier :=
  (orbifold G).toVOA

theorem orbifoldVOA_centralCharge (G : Subgroup (Aut W)) :
    (orbifoldVOA G).centralCharge = W.centralCharge := rfl

end Orbifold

/-! ## `g`-twisted modules (5.3.22) -/

section Twisted
variable {W : VertexOperatorAlgebra 𝒱}

/-- The `g`-eigenspace `𝒱ʲ = {v | g v = ξ_N^{−j} v}` for `g` of order `N`. -/
noncomputable def Aut.twistedEigenspace (g : Aut W) (N : ℕ) (j : ℕ) : Submodule ℂ 𝒱 :=
  Module.End.eigenspace (g.toLinearEquiv : Module.End ℂ 𝒱)
    (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * j) / N))

/-- The generalised binomial `C(x, i) = x(x−1)⋯(x−i+1)/i!` for a **complex** upper index — the
twisted Jacobi identity needs it at `x ∈ (1/N)ℤ`. -/
noncomputable def cbinom (x : ℂ) (i : ℕ) : ℂ :=
  (∏ k ∈ Finset.range i, (x - k)) / (i.factorial : ℂ)

/-- **A `g`-twisted `𝒱`-module** (Gannon 5.3.22), for `g ∈ Aut(𝒱)` of order `N`.  The vertex
operator `Y_M(u,z) = Σ_{r ∈ (1/N)ℤ} u₍ᵣ₎ z^{−r−1}` is carried by its **fractional modes**
`YM u k = u₍k/N₎`, `k ∈ ℤ`; for `u ∈ 𝒱ʲ` only `r ∈ −j/N + ℤ`, i.e. `k ≡ −j (mod N)`, occur
(5.3.22a); the twisted Jacobi identity (5.3.22b) is the mode identity of Dong–Li–Mason with the
fractional binomials `C(k/N, i)`; the grading is as for `OrdVModule`. -/
structure TwistedModule (g : Aut W) (N : ℕ) (M : Type u) [AddCommGroup M] [Module ℂ M] where
  /-- The fractional modes: `YM u k = u₍k/N₎`. -/
  YM : 𝒱 →ₗ[ℂ] (ℤ → Module.End ℂ M)
  /-- `Y_M(𝟙,z) = id`: only the mode `r = −1`, i.e. `k = −N`, survives. -/
  vacuum_YM : ∀ k : ℤ, YM W.vacuum k = if k = -(N : ℤ) then 1 else 0
  /-- Lower truncation. -/
  truncation : ∀ (u : 𝒱) (x : M), ∃ K : ℤ, ∀ k : ℤ, K ≤ k → YM u k x = 0
  /-- **5.3.22a**: for `u ∈ 𝒱ʲ` the modes are supported on `k ≡ −j (mod N)`.  ⚠ The super analogue
  `SuperTwistedModule.support` (`Modules/SuperTwistedModule.lean`) uses the opposite convention
  `k ≡ j (mod N)`. -/
  support : ∀ (j : ℕ) (u : 𝒱), u ∈ g.twistedEigenspace N j →
    ∀ k : ℤ, (k + j) % (N : ℤ) ≠ 0 → YM u k = 0
  /-- **5.3.22b — the twisted Jacobi identity** (mode form, Dong–Li–Mason): for `u ∈ 𝒱ʲ`,
  `v ∈ 𝒱`, `k, m ∈ ℤ` (fractional modes `k/N`, `m/N`) and `ℓ ∈ ℤ`,
  `Σᶠ_i (−1)^i C(ℓ,i)·[u₍(ℓN+k−iN)/N₎ v₍(m+iN)/N₎ x − (−1)^ℓ v₍(ℓN+m−iN)/N₎ u₍(k+iN)/N₎ x]`
  `= Σᶠ_i C(k/N, i)·(u₍ℓ₊ᵢ₎v)₍(k+m−iN)/N₎ x`.
  The index `k` is restricted to the support coset `k ≡ −j (mod N)` of `u`, as in DLM.  Without
  this restriction the field is unsatisfiable on any nonzero `M` once `N ≥ 2` (certificate:
  `u = v = 𝟙`, `ℓ = −1`, `k = 1`, `m = −N−1` gives `0 = x`; see
  `VOA.jacobiAllIndices_eq_zero` in `VOA/Moonshine/HeisenbergTwistedModuleDefect.lean`). -/
  jacobi : ∀ (j : ℕ) (u : 𝒱), u ∈ g.twistedEigenspace N j → ∀ (v : 𝒱) (x : M) (ℓ k m : ℤ),
    (k + j) % (N : ℤ) = 0 →
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (YM u (ℓ * N + k - i * N) (YM v (m + i * N) x)
          - negOnePow ℓ • YM v (ℓ * N + m - i * N) (YM u (k + i * N) x)))
      = ∑ᶠ i : ℕ, cbinom ((k : ℂ) / N) i • YM (W.smul u (ℓ + i) v) (k + m - i * N) x
  /-- The `ℂ`-grading. -/
  weight : ℂ → Submodule ℂ M
  isInternal : DirectSum.IsInternal weight
  /-- `L₀ = ω₍₁₎` (mode `k = N`) acts on `M_α` by `α`. -/
  L0_weight : ∀ (α : ℂ) (x : M), x ∈ weight α → YM W.conformalVector N x = α • x
  finrank : ∀ α, FiniteDimensional ℂ (weight α)
  boundedBelow : ∃ B : ℝ, ∀ α : ℂ, weight α ≠ ⊥ → B ≤ α.re

/-- The block of an operator on the weight space `M_α` of a twisted module. -/
noncomputable def TwistedModule.weightBlock {g : Aut W} {N : ℕ} {M : Type u} [AddCommGroup M]
    [Module ℂ M] (T : TwistedModule g N M) (A : Module.End ℂ M) (α : ℂ) :
    Module.End ℂ (T.weight α) :=
  (internalProjTo T.isInternal α).comp (A.comp (T.weight α).subtype)

/-- **The twisted trace function** `𝒵(M, h; τ) = q^{−c/24} tr_M φ(h) q^{L₀}` (Gannon 5.3.23), as a
formal `q`-series: `φ(h)` is carried as the (projective) action of `h ∈ C_G(g)` on `M`. -/
noncomputable def twistedTrace {g : Aut W} {N : ℕ} {M : Type u} [AddCommGroup M] [Module ℂ M]
    (T : TwistedModule g N M) (φ : Module.End ℂ M) : FormalQSeries :=
  fun e =>
    haveI := T.finrank (e + W.centralCharge / 24)
    LinearMap.trace ℂ _ (T.weightBlock φ (e + W.centralCharge / 24))

/-- An ordinary `OrdVModule` is an `e`-twisted module (`N = 1`): every mode index is integral. -/
noncomputable def OrdVModule.toTwisted {M : Type u} [AddCommGroup M] [Module ℂ M]
    (Nm : OrdVModule W M) : TwistedModule (1 : Aut W) 1 M where
  YM := { toFun := fun u k => mode (Nm.YM u) k
          map_add' := fun u v => by funext k; rw [map_add, mode_add]; rfl
          map_smul' := fun c u => by funext k; rw [map_smul, mode_smul]; rfl }
  vacuum_YM := fun k => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Nm.vacuum_YM, mode_one, Nat.cast_one]
  truncation := fun u x => Nm.truncation u x
  support := fun j u _ k hk => by
    exfalso
    apply hk
    simp
  jacobi := fun j u _ v x ℓ k m _ => by
    have h := Nm.jacobi u v x ℓ k m
    simp only [Nat.cast_one, mul_one, LinearMap.coe_mk, AddHom.coe_mk, div_one]
    -- the `ℕ`-indexed right side is the `ℤ`-indexed one (negative `i` contribute nothing)
    rw [h, ← finsum_mem_univ,
      finsum_mem_inter_support_eq' _ Set.univ (Set.range (Nat.cast : ℕ → ℤ)) ?_,
      finsum_mem_range Nat.cast_injective]
    · refine finsum_congr (fun i => ?_)
      rw [cbz_apply_nonneg _ (by positivity), Int.toNat_natCast]
      rfl
    · intro i hi
      simp only [Set.mem_univ, Set.mem_range, true_iff]
      rw [Function.mem_support] at hi
      by_cases h0 : 0 ≤ i
      · exact ⟨i.toNat, by omega⟩
      · exact absurd (by rw [cbz_apply_neg _ (not_le.mp h0), zero_smul]) hi
  weight := Nm.weight
  isInternal := Nm.isInternal
  L0_weight := fun α x hx => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Nat.cast_one]
    exact Nm.L0_weight α x hx
  finrank := Nm.finrank
  boundedBelow := Nm.boundedBelow

/-! ## Conjecture 5.3.10 as a statement -/

/-- Evaluation of a formal `q`-series along the fractional progression `h₀ + (1/N)ℕ`:
`Σ_n χ(h₀ + n/N) q^{h₀ + n/N}` — the shape of a twisted trace function, whose `L₀`-weights lie in
`h₀ + (1/N)ℤ`. -/
noncomputable def qEvalAtFrac (χ : FormalQSeries) (h₀ : ℂ) (N : ℕ) (τ : UpperHalfPlane) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * h₀) *
    ∑' n : ℕ, χ (h₀ + (n : ℂ) / N) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * ((n : ℂ) / N))

/-- **The modularity half of Conjecture 5.3.10(b)** for one twisted trace function: `𝒵(M,h;τ)`,
read along `h₀ + (1/N)ℕ`, is invariant under some principal congruence subgroup `Γ(N′)`. -/
def TwistedTraceModular {g : Aut W} {N : ℕ} {M : Type u} [AddCommGroup M] [Module ℂ M]
    (T : TwistedModule g N M) (φ : Module.End ℂ M) (h₀ : ℂ) : Prop :=
  ∃ N' : ℕ, 0 < N' ∧ ∀ A ∈ CongruenceSubgroup.Gamma N', ∀ τ : UpperHalfPlane,
    qEvalAtFrac (twistedTrace T φ) h₀ N (A • τ) = qEvalAtFrac (twistedTrace T φ) h₀ N τ

/-- **Conjecture 5.3.10 (Dong–Mason et al.), the modularity part**, as a `Prop` for the VOA `W`:
for every automorphism `g` of finite order `N`, every `g`-twisted module `T` with `L₀`-weights in
`h₀ + (1/N)ℕ`, and every operator `φ` commuting with the twisted action (the projective action of
`h ∈ C_G(g)`), the twisted trace function is modular for a congruence subgroup.  **A conjecture —
stated, never asserted.**  (Part (a), the count of irreducible `g`-twisted modules, and the full
`SL₂(ℤ)`-transformation law among the `𝒵^i_{(g,h)}` (5.3.25) need isomorphism classes of twisted
modules, not built here.) -/
def Conjecture_5_3_10 (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (g : Aut W) (N : ℕ), 0 < N → g ^ N = 1 →
    ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (T : TwistedModule g N M) (h₀ : ℂ),
      (∀ α : ℂ, T.weight α ≠ ⊥ → ∃ n : ℕ, α = h₀ + (n : ℂ) / N) →
      ∀ φ : Module.End ℂ M, (∀ (u : 𝒱) (k : ℤ), φ * T.YM u k = T.YM u k * φ) →
        TwistedTraceModular T φ h₀

end Twisted

end VOA
