import VOA.Modules.ProjCoverWeakRep

/-!
# The free parabolic module and DLM's universal `Ω_n`-vector

DLM3 (Dong–Li–Mason, J. Algebra 206 (1998), §4) induce a `V̂`-module `M̄_n(U)` from a
`P_n`-module `U` on which the deep part `⨁_{p>n} V̂(−p)` acts trivially and `𝟙(−1)` acts as `1`
(`VHat.DLM3.ParabolicRep`).  This file builds the free such module on one generator:

  `freeParabolic W n = U(P_n) / (U(P_n)·deep + U(P_n)·(𝟙(−1) − 1))`,   `u₀ = [1]`.

The left ideal is two-sided (`mul_mem_freeIdeal`), because the deep part is a Lie ideal of `P_n`
and `𝟙(−1)` is central, so `P_n` acts on the quotient by left multiplication
(`freeParabolicRep`).  Its universal property (`exists_freeParabolic_lift`): for every
`V̂`-representation `ρ` in which `𝟙(−1)` acts as `1`, and every `w ∈ Ω_n(ρ)`, there is a
`P_n`-map `U → M` with `u₀ ↦ w`.

Composed with the universal property of `M̄_n(U)` (`indBarLift`) and with `weakRep`
(`ProjCoverWeakRep`), this yields DLM's universal `Ω_n`-vector:

* `exists_universal_omegaN_vector` — a weak module `M̄_n(U)` and `v ∈ M̄_n(U)` such that every
  `w` in DLM's `Ω_n(A)` (`omegaN W n (weakRep A)`) of every weak module `A` is the image of `v`
  under a weak-module homomorphism.

Nothing here uses `M̄_n(U)(n) = U` (DLM3 Prop 4.6), `A_n(V)`, or `VOA.pbw`.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

namespace VHat

namespace DLM3

/-! ## Induction on a universal enveloping algebra -/

/-- Induction principle for elements of a universal enveloping algebra. -/
theorem uea_induction {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    {C : UniversalEnvelopingAlgebra ℂ L → Prop}
    (h_alg : ∀ r : ℂ, C (algebraMap ℂ _ r))
    (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι ℂ x))
    (h_mul : ∀ a b, C a → C b → C (a * b)) (h_add : ∀ a b, C a → C b → C (a + b))
    (a : UniversalEnvelopingAlgebra ℂ L) : C a := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective ℂ (UniversalEnvelopingAlgebra.Rel ℂ L) a
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact h_alg r
  | ι x => exact h_ι x
  | mul a b ha hb => rw [map_mul]; exact h_mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact h_add _ _ ha hb

/-! ## The free parabolic module -/

variable (W) (n : ℕ)

/-- `U(P_n)`. -/
abbrev PEnv : Type u := UniversalEnvelopingAlgebra ℂ (Pn W n)

/-- The canonical map `P_n → U(P_n)`. -/
noncomputable abbrev pι : Pn W n →ₗ⁅ℂ⁆ PEnv W n := UniversalEnvelopingAlgebra.ι ℂ

/-- The vacuum element `𝟙(−1) ∈ P_n`. -/
noncomputable def pvac : Pn W n := ⟨gen W W.vacuum (-1), vacuumGen_mem_parabolic W n⟩

/-- The generators of the defining left ideal. -/
noncomputable def freeGens : Set (PEnv W n) :=
  {x | ∃ g : Pn W n, (g : VHatCarrier W) ∈ deepPart W n ∧ x = pι W n g} ∪
    {pι W n (pvac W n) - 1}

/-- The defining left ideal `U(P_n)·deep + U(P_n)·(𝟙(−1) − 1)`. -/
noncomputable def freeIdeal : Submodule (PEnv W n) (PEnv W n) :=
  Submodule.span (PEnv W n) (freeGens W n)

variable {W n}

theorem deep_lie_mem {g h : Pn W n} (hg : (g : VHatCarrier W) ∈ deepPart W n) :
    ((⁅g, h⁆ : Pn W n) : VHatCarrier W) ∈ deepPart W n := by
  rw [LieSubalgebra.coe_bracket]
  refine degSpan_lie_mem W (S := deepSet n) (T := parabolicSet n) ?_ hg h.2
  intro d hd e he
  simp only [deepSet, parabolicSet, Set.mem_setOf_eq] at hd he ⊢
  rcases he with rfl | he <;> omega

theorem pvac_central (h : Pn W n) : ⁅pvac W n, h⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket]
  exact gen_vacuum_central W h

/-- The generator `ι(g)` (resp. `ι(𝟙(−1)) − 1`) moves past `ι(h)` modulo the ideal. -/
theorem freeGen_mul_pι {s : PEnv W n} (hs : s ∈ freeGens W n) (h : Pn W n) :
    s * pι W n h ∈ freeIdeal W n := by
  rcases hs with ⟨g, hg, rfl⟩ | hs
  · have hlie : pι W n g * pι W n h = pι W n h * pι W n g + pι W n ⁅g, h⁆ := by
      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      abel
    rw [hlie]
    refine (freeIdeal W n).add_mem ?_ ?_
    · exact (freeIdeal W n).smul_mem (pι W n h)
        (Submodule.subset_span (Or.inl ⟨g, hg, rfl⟩))
    · have h1 : pι W n ⁅g, h⁆ ∈ freeIdeal W n :=
        Submodule.subset_span (Or.inl ⟨⁅g, h⁆, deep_lie_mem hg, rfl⟩)
      simpa using h1
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    have hcomm : pι W n (pvac W n) * pι W n h = pι W n h * pι W n (pvac W n) := by
      have := (pι W n).map_lie (pvac W n) h
      rw [pvac_central, map_zero, LieRing.of_associative_ring_bracket] at this
      exact (sub_eq_zero.mp this.symm)
    have he : (pι W n (pvac W n) - 1) * pι W n h = pι W n h * (pι W n (pvac W n) - 1) := by
      rw [sub_mul, mul_sub, hcomm, one_mul, mul_one]
    rw [he]
    exact (freeIdeal W n).smul_mem (pι W n h) (Submodule.subset_span (Or.inr rfl))

/-- **The left ideal is two-sided.** -/
theorem mul_mem_freeIdeal (x : PEnv W n) : ∀ s ∈ freeIdeal W n, s * x ∈ freeIdeal W n := by
  induction x using uea_induction with
  | h_alg r =>
    intro s hs
    rw [← Algebra.commutes]
    exact (freeIdeal W n).smul_mem _ hs
  | h_ι h =>
    intro s hs
    refine Submodule.span_induction (p := fun s _ => s * pι W n h ∈ freeIdeal W n)
      (fun s hs => freeGen_mul_pι hs h)
      (by change (0 : PEnv W n) * pι W n h ∈ freeIdeal W n
          rw [zero_mul]; exact (freeIdeal W n).zero_mem)
      (fun a b _ _ ha hb => by
        change (a + b) * pι W n h ∈ freeIdeal W n
        rw [add_mul]; exact (freeIdeal W n).add_mem ha hb)
      (fun r a _ ha => by
        change (r • a) * pι W n h ∈ freeIdeal W n
        rw [smul_eq_mul, mul_assoc]; exact (freeIdeal W n).smul_mem r ha) hs
  | h_mul a b ha hb =>
    intro s hs
    rw [← mul_assoc]
    exact hb _ (ha s hs)
  | h_add a b ha hb =>
    intro s hs
    rw [mul_add]
    exact (freeIdeal W n).add_mem (ha s hs) (hb s hs)

variable (W n)

/-- The free parabolic module `U(P_n)/freeIdeal`, as a `ℂ`-module. -/
abbrev FreeParabolic : Type u := PEnv W n ⧸ (freeIdeal W n).restrictScalars ℂ

/-- Left multiplication on the free parabolic module. -/
noncomputable def lmulQ : PEnv W n →ₐ[ℂ] End ℂ (FreeParabolic W n) where
  toFun r := ((freeIdeal W n).restrictScalars ℂ).mapQ ((freeIdeal W n).restrictScalars ℂ)
    (LinearMap.mulLeft ℂ r) (fun x hx => (freeIdeal W n).smul_mem r hx)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_mul' r s := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_zero' := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_add' r s := by
    apply Submodule.linearMap_qext
    ext x
    simp [add_mul]
  commutes' r := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.mulLeft_apply, Module.algebraMap_end_apply]
    rw [← Algebra.smul_def]
    exact Submodule.Quotient.mk_smul _ _ _

@[simp] theorem lmulQ_mk (r x : PEnv W n) :
    lmulQ W n r (Submodule.Quotient.mk x) = Submodule.Quotient.mk (r * x) := rfl

/-- **The free parabolic representation.** -/
noncomputable def freeParabolicRep : ParabolicRep W n (FreeParabolic W n) where
  act := (lmulQ W n).toLieHom.comp (pι W n)
  deep_zero g hg := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LieHom.coe_comp,
      AlgHom.coe_toLieHom, LinearMap.zero_apply]
    rw [lmulQ_mk, Submodule.Quotient.mk_eq_zero]
    exact mul_mem_freeIdeal x _ (Submodule.subset_span (Or.inl ⟨g, hg, rfl⟩))
  vacuum_one := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LieHom.coe_comp,
      AlgHom.coe_toLieHom, Module.End.one_apply]
    change lmulQ W n (pι W n (pvac W n)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk x
    rw [lmulQ_mk, Submodule.Quotient.eq]
    have h := mul_mem_freeIdeal x _ (Submodule.subset_span (Or.inr rfl) :
      pι W n (pvac W n) - 1 ∈ freeIdeal W n)
    rw [sub_mul, one_mul] at h
    exact h

theorem freeParabolicRep_act_mk (g : Pn W n) (x : PEnv W n) :
    (freeParabolicRep W n).act g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (pι W n g * x) := rfl

/-- The generator `u₀ = [1]`. -/
noncomputable def freeGen : FreeParabolic W n := Submodule.Quotient.mk 1

variable {W n}

/-- **Universal property of the free parabolic module.** -/
theorem exists_freeParabolic_lift {M : Type u} [AddCommGroup M] [Module ℂ M] (ρ : VHatRep W M)
    (hvac : ∀ x : M, ρ (gen W W.vacuum (-1)) x = x) {w : M} (hw : w ∈ omegaN W n ρ) :
    ∃ φ : FreeParabolic W n →ₗ[ℂ] M, φ (freeGen W n) = w ∧
      ∀ (g : Pn W n) (u : FreeParabolic W n),
        φ ((freeParabolicRep W n).act g u) = ρ (g : VHatCarrier W) (φ u) := by
  let Φ : PEnv W n →ₐ[ℂ] End ℂ M :=
    UniversalEnvelopingAlgebra.lift ℂ (ρ.comp (Pn W n).incl)
  have hΦι : ∀ g : Pn W n, Φ (pι W n g) = ρ (g : VHatCarrier W) := fun g =>
    UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ g
  let φ0 : PEnv W n →ₗ[ℂ] M :=
    { toFun := fun x => Φ x w
      map_add' := fun x y => by rw [map_add, LinearMap.add_apply]
      map_smul' := fun c x => by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  -- the annihilator of `w` is a left ideal containing the generators
  let K : Submodule (PEnv W n) (PEnv W n) :=
    { carrier := {x | Φ x w = 0}
      add_mem' := fun {x y} hx hy => by
        change Φ (x + y) w = 0
        rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
      zero_mem' := by change Φ 0 w = 0; rw [map_zero, LinearMap.zero_apply]
      smul_mem' := fun r x hx => by
        change Φ (r * x) w = 0
        rw [map_mul, Module.End.mul_apply]
        rw [show Φ x w = 0 from hx, map_zero] }
  have hle : freeIdeal W n ≤ K := by
    refine Submodule.span_le.mpr ?_
    rintro x (⟨g, hg, rfl⟩ | hx)
    · change Φ (pι W n g) w = 0
      rw [hΦι]
      exact hw _ hg
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      change Φ (pι W n (pvac W n) - 1) w = 0
      rw [map_sub, map_one, LinearMap.sub_apply, hΦι, Module.End.one_apply]
      change ρ (gen W W.vacuum (-1)) w - w = 0
      rw [hvac, sub_self]
  refine ⟨((freeIdeal W n).restrictScalars ℂ).liftQ φ0 (fun x hx => hle hx), ?_, ?_⟩
  · change φ0 1 = w
    change Φ 1 w = w
    rw [map_one, Module.End.one_apply]
  · intro g u
    induction u using Submodule.Quotient.induction_on with
    | H x =>
      rw [freeParabolicRep_act_mk, Submodule.liftQ_apply, Submodule.liftQ_apply]
      change Φ (pι W n g * x) w = ρ (g : VHatCarrier W) (Φ x w)
      rw [map_mul, Module.End.mul_apply, hΦι]

/-! ## DLM's universal `Ω_n`-vector -/

/-- A `V̂`-map out of `M̄_n(U)` into a weak module, as a weak-module homomorphism. -/
noncomputable def indBarHom {U : Type u} [AddCommGroup U] [Module ℂ U] (P : ParabolicRep W n U)
    {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = weakRep A (g : VHatCarrier W) (φ u)) :
    (indBarWeakModule P).Hom A where
  toLinearMap := indBarLift P (weakRep A) (weakRep_moduleIterate A) φ hφ
  map_act a p y := by
    rw [indBarWeakModule_act, VHatRep.actMode_def, indBarLift_intertwine, weakRep_gen]
    rfl

/-- **DLM's universal `Ω_n`-vector exists** (unconditionally): there is a weak module `G`
(`M̄_n` of the free parabolic module) and `v ∈ G` such that every vector of DLM's `Ω_n(A)` of every
weak module `A` is the image of `v` under a weak-module homomorphism `G → A`. -/
theorem exists_universal_omegaN_vector (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    ∃ (G : Type u) (_ : AddCommGroup G) (_ : Module ℂ G) (BG : WeakModule W G) (v : G),
      ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M),
        ∀ w ∈ omegaN W n (weakRep A), ∃ φ : BG.Hom A, φ.toLinearMap v = w := by
  refine ⟨IndBar (freeParabolicRep W n), inferInstance, inferInstance,
    indBarWeakModule (freeParabolicRep W n), indBarBottom (freeParabolicRep W n) (freeGen W n),
    ?_⟩
  intro M _ _ A w hw
  have hvac : ∀ x : M, weakRep A (gen W W.vacuum (-1)) x = x := by
    intro x
    rw [weakRep_gen]
    have := A.act_vacuum (-1) x
    simpa only [WeakModule.act_def, if_pos rfl] using this
  obtain ⟨φ, hφ0, hφ⟩ := exists_freeParabolic_lift (weakRep A) hvac hw
  refine ⟨indBarHom (freeParabolicRep W n) A φ hφ, ?_⟩
  change indBarLift (freeParabolicRep W n) (weakRep A) (weakRep_moduleIterate A) φ hφ
    (indBarBottom (freeParabolicRep W n) (freeGen W n)) = w
  rw [indBarLift_bottom, hφ0]

end DLM3

end VHat

end VOA
