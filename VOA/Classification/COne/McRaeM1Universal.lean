import VOA.Classification.COne.McRaeM1Cover
import VOA.Classification.COne.ABDWeakAdmissibleComplete
import VOA.Classification.COne.PlusSplittingLocalFinite
import VOA.Classification.COne.PlusFiniteLengthCyclic

/-!
# McRae's route: Huang's Theorem 3.22 from a universal `Ω_N`-vector

Huang (arXiv:0712.4109, Thm 3.22) proves that the generalized Verma module `M_N(E)` of a
homogeneous projective `A_N(V)`-module `E` is projective among finite-length generalized modules.
The proof uses four facts:

1. `W_[h] ⊆ Ω_N(W)` for every module `W`, once `N` exceeds the spread of the weights
   ("lowest weights are bounded");
2. generalized `L(0)`-eigenspaces are exact;
3. the universal property of `M_N(E)` (DLM Thm 3.5 = DLM3 Thm 4.1);
4. finite length of `M_N(E)` (Huang Prop 3.8 / Cor 3.17, a `C₁`/`C₂` spanning argument).

This file shows that, for a `C₂`-cofinite `W`, the whole of Thm 3.22 + Thm 3.23 follows from ONE
statement about DLM's induced modules, with **no Zhu-algebra input at all** (no `A_N(V)`
associativity, no finite-dimensionality of `A_N(V)`, no projective `A_N(V)`-modules):

* `UniversalOmegaVector W N` (named `Prop`, proved for every VOA in `McRaeM1Main`): there is a
  weak module `G` and a vector `v ∈ G` such that every `w ∈ Ω_N(M)` of every weak module `M` is
  the image of `v` under some homomorphism `G → M`.  This is DLM's `M̄_N(U)` for the free
  parabolic module `U = U(P_N)/(deep, 𝟙(−1) − 1)`; only its existence and universal property are
  used.

Then (`enoughProjFL_of_universalOmegaVector`): for a simple `S` with a nonzero generalized
eigenvector of weight `h`, take `N` with `Re h < b + N + 1` (`b` the uniform spectral lower bound,
a `C₂` theorem), split `v = a + c` with `a` the generalized `h`-component of `v`, and let
`P = ⟨a⟩`.  Then
* `P` has finite length (`finiteLength_of_generalized_cyclic`, a `C₂` theorem);
* `P` is projective against EVERY surjection of weak modules: a map `P → Z` sends `a` into
  `Z_[h]`, which is the image of `Y_[h] ⊆ Ω_N(Y)`; the universal property lifts, and the lift
  sends `a` to the chosen preimage because homomorphisms preserve generalized components;
* `P → S`, `a ↦ s`, is nonzero.

So, for `C₂`-cofinite `W` (all results `#print axioms`-clean, conditional on the displayed
hypotheses):

* `enoughProjFLNonzero_of_universalOmegaVector (hC2) (hU : ∀ N, UniversalOmegaVector W N)`
* `huangCoverFact_of_universalOmegaVector (hC2) (hU) : HuangCoverFact W`.

Supporting results: `OmegaN` (DLM `Ω_N`), `OmegaN_zero` (`= Omega`, the library's `Ω₀`),
`maxGenEigenspace_le_OmegaN` (Huang's step 1, from the uniform spectral bound), and
`L0_locallyFinite_of_c2` (every weak module of a `C₂` VOA has locally finite `L(0)`; ABD).
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.McRaeM1

open VOA VertexOperatorAlgebra PlusSplitting OrbMcRae
open VOA.Huang.LogRemovalAdmissible PlusRational

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## DLM's `Ω_N(M)` -/

section OmegaN

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **Dong–Li–Mason `Ω_N(M)`**: the vectors killed by every homogeneous mode `v₍ₙ₎` of degree
`wt v − n − 1 < −N`, i.e. `wt v + N ≤ n`. -/
def OmegaN (A : WeakModule W M) (N : ℕ) : Submodule ℂ M where
  carrier := {w : M | ∀ (β : ℤ) (v : 𝒱), v ∈ W.grading β → ∀ n : ℤ, β + (N : ℤ) ≤ n →
    mode (A.YM v) n w = 0}
  add_mem' := by
    intro a b ha hb β v hv n hn
    rw [map_add, ha β v hv n hn, hb β v hv n hn, add_zero]
  zero_mem' := by
    intro β v hv n _
    rw [map_zero]
  smul_mem' := by
    intro c a ha β v hv n hn
    rw [map_smul, ha β v hv n hn, smul_zero]

@[simp] theorem mem_OmegaN (A : WeakModule W M) (N : ℕ) (w : M) :
    w ∈ OmegaN A N ↔ ∀ (β : ℤ) (v : 𝒱), v ∈ W.grading β → ∀ n : ℤ, β + (N : ℤ) ≤ n →
      mode (A.YM v) n w = 0 := Iff.rfl

/-- At `N = 0`, `Ω_N` is the library's bottom `Omega`. -/
theorem OmegaN_zero (A : WeakModule W M) : OmegaN A 0 = Omega A := by
  ext w
  simp only [mem_OmegaN, mem_Omega, Nat.cast_zero, add_zero]

theorem OmegaN_mono (A : WeakModule W M) {N N' : ℕ} (h : N ≤ N') : OmegaN A N ≤ OmegaN A N' :=
  fun _ hw β v hv n hn => hw β v hv n (by omega)

/-- **Huang's step 1.**  If every generalized weight of every weak module has real part at least
`b`, then a generalized `h`-eigenvector with `Re h < b + N + 1` lies in `Ω_N`. -/
theorem maxGenEigenspace_le_OmegaN {b : ℝ}
    (hb : ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (α : ℂ),
      (L0 A).maxGenEigenspace α ≠ ⊥ → b ≤ α.re)
    (A : WeakModule W M) {h : ℂ} {N : ℕ} (hN : h.re < b + N + 1) :
    (L0 A).maxGenEigenspace h ≤ OmegaN A N := by
  intro x hx β v hv n hn
  by_contra hne
  have hmem := ABDWeakAdmissible.mode_mem_maxGenEigenspace A hv n hx
  have hb' := hb A _ (fun hbot => hne (by
    rw [hbot] at hmem
    exact (Submodule.mem_bot _).mp hmem))
  rw [Complex.add_re, Complex.intCast_re] at hb'
  have hle : ((β - n - 1 : ℤ) : ℝ) ≤ -(N : ℝ) - 1 := by
    have : β - n - 1 ≤ -(N : ℤ) - 1 := by omega
    exact_mod_cast this
  linarith

end OmegaN

/-! ## Generalized eigen-components -/

section Components

variable {X Y : Type u} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- Every weak module of a `C₂`-cofinite VOA has locally finite `L(0)` (Abe–Buhl–Dong). -/
theorem L0_locallyFinite_of_c2 (hC2 : C2Cofinite W) (A : WeakModule W X) (x : X) :
    ∃ S : Submodule ℂ X, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ y ∈ S, L0 A y ∈ S := by
  obtain ⟨N, rfl⟩ := ABDWeakAdmissible.abdWeakIsAdmissible hC2 A
  exact PlusSplitting.admissible_L0_locally_finite W hC2 N x

/-- The complement of the generalized `h`-eigenspace. -/
def offEigen (f : Module.End ℂ X) (h : ℂ) : Submodule ℂ X :=
  ⨆ k, ⨆ (_ : k ≠ h), f.maxGenEigenspace k

/-- A locally finite operator splits every vector into its `h`-component and the rest. -/
theorem exists_component (f : Module.End ℂ X)
    (hloc : ∀ x : X, ∃ S : Submodule ℂ X, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ y ∈ S, f y ∈ S)
    (h : ℂ) (v : X) : ∃ a ∈ f.maxGenEigenspace h, ∃ c ∈ offEigen f h, v = a + c := by
  have htop : (⊤ : Submodule ℂ X) ≤ f.maxGenEigenspace h ⊔ offEigen f h := by
    calc
      (⊤ : Submodule ℂ X) = ⨆ k, ⊤ ⊓ f.maxGenEigenspace k :=
        eq_iSup_inf_maxGenEigenspace_of_locally_finite f hloc ⊤ (fun _ _ => Submodule.mem_top)
      _ ≤ _ := by
        apply iSup_le
        intro k
        by_cases hk : k = h
        · subst k
          exact inf_le_right.trans le_sup_left
        · intro z hz
          exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem k
            (Submodule.mem_iSup_of_mem hk hz.2))
  obtain ⟨a, ha, c, hc, he⟩ := Submodule.mem_sup.mp (htop (Submodule.mem_top : v ∈ ⊤))
  exact ⟨a, ha, c, hc, he.symm⟩

/-- Intertwiners preserve the complement of a generalized eigenspace. -/
theorem map_mem_offEigen (f : Module.End ℂ X) (g : Module.End ℂ Y) (π : X →ₗ[ℂ] Y)
    (hc : ∀ x, π (f x) = g (π x)) (h : ℂ) {x : X} (hx : x ∈ offEigen f h) :
    π x ∈ offEigen g h := by
  have ht : offEigen f h ≤ (offEigen g h).comap π := by
    apply iSup_le
    intro k
    apply iSup_le
    intro hk z hz
    exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk
      (map_mem_maxGenEigenspace f g π hc k hz))
  exact ht hx

/-- Uniqueness of the `h`-component. -/
theorem component_unique (g : Module.End ℂ Y) (h : ℂ) {a c w : Y}
    (ha : a ∈ g.maxGenEigenspace h) (hc : c ∈ offEigen g h) (hw : w ∈ g.maxGenEigenspace h)
    (he : a + c = w) : a = w := by
  have hc0 : c = 0 := by
    apply Submodule.disjoint_def.mp ((g.independent_genEigenspace ⊤) h)
    · have : c = w - a := by rw [← he]; abel
      rw [this]
      exact (g.maxGenEigenspace h).sub_mem hw ha
    · exact hc
  rw [← he, hc0, add_zero]

/-- A weak-module homomorphism sends the `h`-component of `v` to the `h`-component of its image;
in particular, if `π v` is itself a generalized `h`-vector then `π a = π v`. -/
theorem hom_component {A : WeakModule W X} {B : WeakModule W Y} (π : A.Hom B) (h : ℂ)
    {v a c : X} (ha : a ∈ (L0 A).maxGenEigenspace h) (hc : c ∈ offEigen (L0 A) h)
    (hv : v = a + c) (hw : π.toLinearMap v ∈ (L0 B).maxGenEigenspace h) :
    π.toLinearMap a = π.toLinearMap v := by
  apply component_unique (L0 B) h
    (map_mem_maxGenEigenspace _ _ π.toLinearMap (L0_hom π) h ha)
    (map_mem_offEigen _ _ π.toLinearMap (L0_hom π) h hc) hw
  rw [hv, map_add]

/-- Two homomorphisms out of a cyclic weak module agreeing on the generator agree. -/
theorem hom_ext_of_cyclic {A : WeakModule W X} {B : WeakModule W Y} (f₁ f₂ : A.Hom B)
    (z : X) (hz : cyclic A z = ⊤) (he : f₁.toLinearMap z = f₂.toLinearMap z) (x : X) :
    f₁.toLinearMap x = f₂.toLinearMap x := by
  let E : WeakModule.Submodule' A :=
    { carrier := LinearMap.ker (f₁.toLinearMap - f₂.toLinearMap)
      act_mem := by
        intro u n y hy
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hy ⊢
        rw [f₁.map_act, f₂.map_act, hy] }
  have hle : cyclic A z ≤ toR A E :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by
      change z ∈ LinearMap.ker (f₁.toLinearMap - f₂.toLinearMap)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      exact he))
  rw [hz] at hle
  have hx : x ∈ LinearMap.ker (f₁.toLinearMap - f₂.toLinearMap) :=
    hle (Submodule.mem_top : x ∈ (⊤ : Submodule (modeAlg A) X))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
  exact hx

/-- Generalized eigenspaces are exact along surjections (local finiteness of the source). -/
theorem exists_preimage_maxGenEigenspace (hC2 : C2Cofinite W) {A : WeakModule W X}
    {B : WeakModule W Y} (g : A.Hom B) (hg : Function.Surjective g.toLinearMap) (h : ℂ)
    {z : Y} (hz : z ∈ (L0 B).maxGenEigenspace h) :
    ∃ y ∈ (L0 A).maxGenEigenspace h, g.toLinearMap y = z := by
  have hmap := map_inf_maxGenEigenspace (L0 A) (L0 B) g.toLinearMap (L0_hom g)
    (L0_locallyFinite_of_c2 hC2 A) ⊤ (fun _ _ => Submodule.mem_top) h
  have hz' : z ∈ (⊤ : Submodule ℂ X).map g.toLinearMap ⊓ (L0 B).maxGenEigenspace h := by
    refine ⟨?_, hz⟩
    obtain ⟨x, rfl⟩ := hg z
    exact ⟨x, Submodule.mem_top, rfl⟩
  rw [← hmap] at hz'
  obtain ⟨y, hy, rfl⟩ := hz'
  exact ⟨y, hy.2, rfl⟩

end Components

/-! ## The universal `Ω_N`-vector and Huang's Theorem 3.22 -/

/-- **A universal `Ω_N`-vector** (named `Prop`; proved for every VOA in `McRaeM1Main`,
`universalOmegaVector`): a weak module
`G` and `v ∈ G` such that every vector of `Ω_N(M)`, for every weak module `M`, is the image of
`v` under a homomorphism `G → M`.

Literature: Dong–Li–Mason, J. Algebra 206 (1998), Thm 4.1 (Huang's Thm 3.5): the induced module
`M̄_N(U)` with `U = A_N(V)` (or `U = U(V̂(0))` with `V̂(−k)`, `k > N`, acting by `0`), and
`v = [1 ⊗ 1]`.  Its universal property turns `w ∈ Ω_N(M)` into the `P_N`-map `U → Ω_N(M)`,
`1 ↦ w`.  Only existence and the universal property are needed, not `M̄_N(U)(N) = U`. -/
def UniversalOmegaVector (W : VertexOperatorAlgebra 𝒱) (N : ℕ) : Prop :=
  ∃ (G : Type u) (_ : AddCommGroup G) (_ : Module ℂ G) (BG : WeakModule W G) (v : G),
    ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M), ∀ w ∈ OmegaN A N,
      ∃ φ : BG.Hom A, φ.toLinearMap v = w

section Main

variable {X : Type u} [AddCommGroup X] [Module ℂ X]

/-- A nonzero weak module of a `C₂`-cofinite VOA has a nonzero generalized `L(0)`-eigenvector. -/
theorem exists_genEigenvector (hC2 : C2Cofinite W) (B : WeakModule W X) [Nontrivial X] :
    ∃ h : ℂ, ∃ s ∈ (L0 B).maxGenEigenspace h, s ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have htop := eq_iSup_inf_maxGenEigenspace_of_locally_finite (L0 B)
    (L0_locallyFinite_of_c2 hC2 B) ⊤ (fun _ _ => Submodule.mem_top)
  have hbot : ∀ μ : ℂ, (⊤ : Submodule ℂ X) ⊓ (L0 B).maxGenEigenspace μ = ⊥ := by
    intro μ
    rw [eq_bot_iff]
    intro y hy
    exact (Submodule.mem_bot _).mpr (hall μ y hy.2)
  simp only [hbot, iSup_bot] at htop
  exact hx ((Submodule.mem_bot _).mp (htop ▸ (Submodule.mem_top : x ∈ ⊤)))

/-- **Huang Thm 3.22 + the surjection in Thm 3.23, from a universal `Ω_N`-vector.**  For a
`C₂`-cofinite `W`, universal `Ω_N`-vectors for all `N` give, for every simple weak module, a
finite-length projective weak module with a nonzero map onto it. -/
theorem enoughProjFLNonzero_of_universalOmegaVector (hC2 : C2Cofinite W)
    (hU : ∀ N : ℕ, UniversalOmegaVector W N) : EnoughProjFLNonzero W := by
  intro X _ _ B hS
  haveI : Nontrivial X := IsSimpleModule.nontrivial (modeAlg B) X
  obtain ⟨h, s, hs, hs0⟩ := exists_genEigenvector hC2 B
  obtain ⟨b, hb⟩ := ABDWeakAdmissible.exists_uniform_weak_spectrum_lower_bound (W := W) hC2
  let N : ℕ := ⌈h.re - b⌉₊
  have hN : h.re < b + N + 1 := by
    have := Nat.le_ceil (h.re - b)
    linarith
  have hΩ : ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M),
      (L0 A).maxGenEigenspace h ≤ OmegaN A N :=
    fun A => maxGenEigenspace_le_OmegaN hb A hN
  obtain ⟨G, _, _, BG, v, huniv⟩ := hU N
  obtain ⟨a, ha, c, hc, hv⟩ := exists_component (L0 BG) (L0_locallyFinite_of_c2 hC2 BG) h v
  -- the cyclic module generated by the `h`-component
  let Q := cyclic BG a
  let BQ : WeakModule W (ofR BG Q).carrier := WeakModule.submodule BG (ofR BG Q)
  let z : (ofR BG Q).carrier := ⟨a, Submodule.mem_span_singleton_self a⟩
  let ι : BQ.Hom BG := subIncl BG Q
  have hι : Function.Injective ι.toLinearMap := subIncl_injective BG Q
  have hcyc : cyclic BQ z = ⊤ := ABDWeakAdmissible.cyclic_restriction_eq_top BG a
  obtain ⟨k, hk⟩ := Module.End.mem_genEigenspace_top.mp ha
  have hzk : ((L0 BQ - h • 1) ^ k) z = 0 := by
    apply hι
    rw [pow_hom ι h k z, map_zero]
    exact hk
  have hzgen : z ∈ (L0 BQ).maxGenEigenspace h :=
    Module.End.mem_genEigenspace_top.mpr ⟨k, hzk⟩
  have hFL : IsFiniteLength (modeAlg BQ) (ofR BG Q).carrier :=
    PlusFiniteLength.finiteLength_of_generalized_cyclic hC2 k BQ z h hzk hcyc
  -- the lifting principle: any generalized `h`-vector is the image of `z`
  have hlift : ∀ {Y : Type u} [AddCommGroup Y] [Module ℂ Y] (BY : WeakModule W Y) (y : Y),
      y ∈ (L0 BY).maxGenEigenspace h → ∃ k' : BQ.Hom BY, k'.toLinearMap z = y := by
    intro Y _ _ BY y hy
    obtain ⟨ψ, hψ⟩ := huniv BY y (hΩ BY hy)
    refine ⟨homComp ψ ι, ?_⟩
    rw [homComp_apply]
    change ψ.toLinearMap a = y
    rw [hom_component ψ h ha hc hv (hψ ▸ hy), hψ]
  refine ⟨(ofR BG Q).carrier, _, _, BQ, hFL, ?_, ?_⟩
  · -- projectivity
    intro Y Z _ _ _ _ BY BZ _ g hg f
    have hfz : f.toLinearMap z ∈ (L0 BZ).maxGenEigenspace h :=
      map_mem_maxGenEigenspace _ _ f.toLinearMap (L0_hom f) h hzgen
    obtain ⟨y, hy, hgy⟩ := exists_preimage_maxGenEigenspace hC2 g hg h hfz
    obtain ⟨k', hk'⟩ := hlift BY y hy
    refine ⟨k', fun x => ?_⟩
    have := hom_ext_of_cyclic (homComp g k') f z hcyc (by rw [homComp_apply, hk', hgy]) x
    rwa [homComp_apply] at this
  · -- a nonzero map onto `B`
    obtain ⟨p, hp⟩ := hlift B s hs
    refine ⟨p, fun h0 => hs0 ?_⟩
    rw [← hp, h0, LinearMap.zero_apply]

/-- **`HuangCoverFact` from universal `Ω_N`-vectors** (`C₂`-cofinite `W`). -/
theorem huangCoverFact_of_universalOmegaVector (hC2 : C2Cofinite W)
    (hU : ∀ N : ℕ, UniversalOmegaVector W N) : HuangCoverFact W :=
  huangCoverFact_of_enoughProjFL
    (enoughProjFL_iff_nonzero.mpr (enoughProjFLNonzero_of_universalOmegaVector hC2 hU))

end Main

end VOA.Classification.COne.McRaeM1
