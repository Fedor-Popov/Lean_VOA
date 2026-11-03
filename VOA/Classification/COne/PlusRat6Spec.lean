import VOA.Classification.COne.PlusRat5Main

/-! # Kernel injectivity with an arbitrary joint spectrum

Session 5 (`kernel_ann_exists`, `kernel_inj`) transfers polynomial identities from a model whose
`L(0)`-eigenspaces are spanned by joint eigenvectors of two zero modes with eigenvalues in `ℕ²`.
The twisted models have eigenvalues `(16a-1)/128`, `(8b+1)/256`.  Here the eigenvalues are
`(φ s, ψ t)` for arbitrary maps `φ ψ : ℕ → ℂ` (`s, t ≤ C`, a predicate `Q s t`).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat6
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
  ABDWeakAdmissible PlusRatSign PlusRat3 PlusRational PlusRat4 PlusRat5
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {W : VertexOperatorAlgebra V}

/-- **Kernel annihilators** for an arbitrary spectrum map. -/
theorem kernel_ann_existsG (hC2 : C2Cofinite W) (A : WeakModule W M) (B : WeakModule W N)
    (P : Submodule (modeAlg A) M) (hP : IsAtom P) (χ : VOA.A W → ℂ) {h : ℂ}
    {k₀ : M} {e : N} (hk₀P : k₀ ∈ P) (hk₀0 : k₀ ≠ 0) (hk₀ : k₀ ∈ Omega A) (he : e ∈ Omega B)
    (hχk : ∀ r, topEvaluation A k₀ hk₀ r = χ r • k₀) (hχe : ∀ r, topEvaluation B e he r = χ r • e)
    (hkL : L0 A k₀ = h • k₀) (heL : L0 B e = h • e) (he0 : e ≠ 0)
    (hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (D : ℕ)
    (hmid : ∀ k : ℕ, 0 < k → k < D → ∀ v : M, v ∈ Omega A → L0 A v = (h + (k : ℂ)) • v → v = 0)
    (d : ℕ) (hdD : d ≤ D)
    (a b : HomogeneousLetter W) (ha : a.weight - a.modeIndex - 1 = 0)
    (hb : b.weight - b.modeIndex - 1 = 0) (φ ψ : ℕ → ℂ) (C : ℕ) (Q : ℕ → ℕ → Prop)
    (hspan : ∀ y : N, L0 B y = (h + (d : ℂ)) • y → y ∈ Submodule.span ℂ
      {u | ∃ s t : ℕ, Q s t ∧ s ≤ C ∧ t ≤ C ∧ mode (B.YM a.state) a.modeIndex u = φ s • u ∧
        mode (B.YM b.state) b.modeIndex u = ψ t • u})
    (L : List (ℂ × ℕ × ℕ)) (hne : ∀ s t : ℕ, Q s t → s ≤ C → t ≤ C → polyV L (φ s) (ψ t) ≠ 0) :
    ∃ Vs : List ℂ, (Vs.map fun v => -v).prod ≠ 0 ∧
      ∀ v ∈ P, L0 A v = (h + (d : ℂ)) • v → evalW A (annW a b L Vs) v = 0 := by
  classical
  let pairs : List (ℕ × ℕ) := ((List.range (C + 1)).flatMap fun s =>
    (List.range (C + 1)).map fun t => (s, t)).filter fun p => Q p.1 p.2
  let Vs : List ℂ := pairs.map fun p => polyV L (φ p.1) (ψ p.2)
  have hV0 : (Vs.map fun v => -v).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    simp only [List.mem_map, Vs, pairs, List.mem_filter, List.mem_flatMap, List.mem_range] at hz
    obtain ⟨v, ⟨p, ⟨⟨s, hs, hp⟩, hQ⟩, rfl⟩, hv⟩ := hz
    obtain ⟨t, ht, rfl⟩ := hp
    exact hne s t (by simpa using hQ) (by omega) (by omega) (neg_eq_zero.mp hv)
  have hann := kernel_annihilate hC2 A B P hP χ hk₀P hk₀0 hk₀ he hχk hχe hkL heL he0 hlow D hmid
    d hdD (annW a b L Vs) (WDeg_annW a b ha hb L Vs) (by
      intro y hy
      apply evalW_span B _ _ (hspan y hy)
      rintro u ⟨s, t, hQ, hsC, htC, hus, hut⟩
      rw [evalW_annW_eigen B a b hus hut L Vs]
      have hmem : polyV L (φ s) (ψ t) ∈ Vs :=
        List.mem_map.mpr ⟨(s, t), List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨s,
          List.mem_range.mpr (by omega), List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), rfl⟩⟩,
          decide_eq_true hQ⟩, rfl⟩
      have hz : (Vs.map fun v => polyV L (φ s) (ψ t) - v).prod = 0 :=
        List.prod_eq_zero (List.mem_map.mpr ⟨_, hmem, sub_self _⟩)
      rw [hz, zero_smul])
  exact ⟨Vs, hV0, hann⟩

/-- **Kernel injectivity** for an arbitrary spectrum map. -/
theorem kernel_injG (hC2 : C2Cofinite W) (A : WeakModule W M) (B : WeakModule W N)
    (P : Submodule (modeAlg A) M) (hP : IsAtom P) (χ : VOA.A W → ℂ) {h : ℂ}
    {k₀ : M} {e : N} (hk₀P : k₀ ∈ P) (hk₀0 : k₀ ≠ 0) (hk₀ : k₀ ∈ Omega A) (he : e ∈ Omega B)
    (hχk : ∀ r, topEvaluation A k₀ hk₀ r = χ r • k₀) (hχe : ∀ r, topEvaluation B e he r = χ r • e)
    (hkL : L0 A k₀ = h • k₀) (heL : L0 B e = h • e) (he0 : e ≠ 0)
    (hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0) (D : ℕ)
    (hmid : ∀ k : ℕ, 0 < k → k < D → ∀ v : M, v ∈ Omega A → L0 A v = (h + (k : ℂ)) • v → v = 0)
    (d : ℕ) (hdD : d ≤ D)
    (a b : HomogeneousLetter W) (ha : a.weight - a.modeIndex - 1 = 0)
    (hb : b.weight - b.modeIndex - 1 = 0) (φ ψ : ℕ → ℂ) (C : ℕ) (Q : ℕ → ℕ → Prop)
    (hspan : ∀ y : N, L0 B y = (h + (d : ℂ)) • y → y ∈ Submodule.span ℂ
      {u | ∃ s t : ℕ, Q s t ∧ s ≤ C ∧ t ≤ C ∧ mode (B.YM a.state) a.modeIndex u = φ s • u ∧
        mode (B.YM b.state) b.modeIndex u = ψ t • u})
    (L : List (ℂ × ℕ × ℕ)) (hne : ∀ s t : ℕ, Q s t → s ≤ C → t ≤ C → polyV L (φ s) (ψ t) ≠ 0) :
    ∀ v ∈ P, L0 A v = (h + (d : ℂ)) • v → evalW A (polyW a b L) v = 0 → v = 0 := by
  obtain ⟨Vs, hV0, hann⟩ := kernel_ann_existsG hC2 A B P hP χ hk₀P hk₀0 hk₀ he hχk hχe hkL heL he0
    hlow D hmid d hdD a b ha hb φ ψ C Q hspan L hne
  intro v hvP hvL hT
  have h1 := hann v hvP hvL
  rw [evalW_annW_kernel A a b L hT Vs] at h1
  exact (smul_eq_zero.mp h1).resolve_left hV0

end VOA.Classification.COne.PlusRat6

namespace VOA.Classification.COne.PlusRat6
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3 PlusRat4 PlusRational PlusRat5

variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)

/-- The `w`-eigenspace of `B` is spanned by joint eigenvectors with eigenvalues `(φ s, ψ t)`,
`s, t ≤ C`, `Q s t`. -/
def SpecSpanG {N : Type} [AddCommGroup N] [Module ℂ N] (B : WeakModule (V2mPlus m hm) N) (w : ℂ)
    (φ ψ : ℕ → ℂ) (C : ℕ) (Q : ℕ → ℕ → Prop) : Prop :=
  ∀ y : N, L0 B y = w • y → y ∈ Submodule.span ℂ
    {u | ∃ s t : ℕ, Q s t ∧ s ≤ C ∧ t ≤ C ∧
      mode (B.YM (aL m hm).state) (aL m hm).modeIndex u = φ s • u ∧
      mode (B.YM (bL m hm).state) (bL m hm).modeIndex u = ψ t • u}

/-- A model of the row `l` with joint spectrum maps `φ, ψ`, adapted to the target weight `h'`
(at `h'` every eigenvalue of `o(H⁴)` is nonzero). -/
def ModelSpecG (l : Label m) (h' : ℂ) (φ ψ : ℕ → ℂ) : Prop :=
  ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (B : WeakModule (V2mPlus m hm) N) (e : N)
    (he : e ∈ Omega B), e ≠ 0 ∧ L0 B e = ((weight m l : ℚ) : ℂ) • e ∧
    (∀ r, topEvaluation B e he r = chiT m hm hm2 l r • e) ∧
    (∀ w : ℂ, ∃ C : ℕ, SpecSpanG m hm B w φ ψ C (fun _ _ => True)) ∧
    (∃ C : ℕ, SpecSpanG m hm B h' φ ψ C (fun s _ => φ s ≠ 0))

/-- The `PlusRat5` Fock models are models with the natural spectrum. -/
theorem modelSpecG_of_modelSpec {l : Label m} {h' : ℂ} (H : ModelSpec m hm hm2 l h') :
    ModelSpecG m hm hm2 l h' (fun s => (s : ℂ)) (fun t => (t : ℂ)) := by
  obtain ⟨N, i1, i2, B, e, he, he0, heL, hχ, hall, C, hC⟩ := H
  refine ⟨N, i1, i2, B, e, he, he0, heL, hχ, fun w => ?_, ⟨C, ?_⟩⟩
  · obtain ⟨C, hC⟩ := hall w
    exact ⟨C, hC⟩
  · intro y hy
    refine Submodule.span_mono ?_ (hC y hy)
    rintro u ⟨s, t, hs, hsC, htC, h1, h2⟩
    refine ⟨s, t, ?_, hsC, htC, h1, h2⟩
    have : s ≠ 0 := by omega
    show (s : ℂ) ≠ 0
    exact_mod_cast this

end VOA.Classification.COne.PlusRat6
