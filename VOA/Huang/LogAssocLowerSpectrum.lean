import VOA.Huang.LogAssocCompletedProduct
import VOA.Huang.LogHuangCosetBases

/-! Each actual disjoint intermediate spectrum coset has a genuine lower
base. This reindexes the literal spectrum sum into natural-number rows,
without duplicating any weight or discarding any actual component. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.Huang.LogHuangODEProduct
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- A genuine lower generalized-weight base in each actual spectrum coset. -/
noncomputable def lowerSpectrumRep (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) (mu : ℂ) : ℂ :=
  Classical.choose (exists_cosetBase N.toGW (spectrumCosetRep hC2 N hfg mu))

theorem lowerSpectrumRep_spec (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) (mu : ℂ) :
    (∃ K : ℕ,spectrumCosetRep hC2 N hfg mu=lowerSpectrumRep hC2 N hfg mu+K) ∧
      CosetBase N.toGW (lowerSpectrumRep hC2 N hfg mu) := by
  obtain ⟨K,hK,hL⟩ := Classical.choose_spec
    (exists_cosetBase N.toGW (spectrumCosetRep hC2 N hfg mu))
  exact ⟨⟨K,hK⟩,hL⟩

/-- A scalar sum on a genuine integer spectrum row is exactly the natural
row starting at its proved lower generalized weight base. -/
theorem lowerSpectrum_row (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) (mu : ℂ) (g : ℂ → ℂ)
    (hweight : ∀ a,g a≠0 → N.weight a≠⊥)
    (hs : Summable fun n : ℕ => g (lowerSpectrumRep hC2 N hfg mu+n)) :
    Summable (fun d : ℤ => g (spectrumCosetRep hC2 N hfg mu+d)) ∧
      (∑' d : ℤ,g (spectrumCosetRep hC2 N hfg mu+d))=
        ∑' n : ℕ,g (lowerSpectrumRep hC2 N hfg mu+n) := by
  classical
  obtain ⟨⟨K,hK⟩,hL⟩ := lowerSpectrumRep_spec hC2 N hfg mu
  let e : ℕ → ℤ := fun n => (n : ℤ)-K
  have hinj : Function.Injective e := by
    intro n m he
    dsimp only [e] at he
    omega
  have he (n : ℕ) : spectrumCosetRep hC2 N hfg mu+(e n : ℂ)=
      lowerSpectrumRep hC2 N hfg mu+n := by
    rw [hK]
    dsimp only [e]
    push_cast
    ring
  have hsupport : Function.support (fun d : ℤ => g (spectrumCosetRep hC2 N hfg mu+d))⊆Set.range e := by
    intro d hd
    have hne := hweight _ hd
    have hγ : spectrumCosetRep hC2 N hfg mu+d=
        lowerSpectrumRep hC2 N hfg mu+((K : ℤ)+d : ℤ) := by
      rw [hK]; push_cast; ring
    have hn : 0≤(K : ℤ)+d := by
      by_contra hn
      have hbot := hL ((K : ℤ)+d) (by omega)
      rw [← hγ] at hbot
      exact hne hbot
    refine ⟨((K : ℤ)+d).toNat,?_⟩
    dsimp only [e]
    rw [Int.toNat_of_nonneg hn]
    omega
  have hvan : ∀ d : ℤ,d∉Set.range e → g (spectrumCosetRep hC2 N hfg mu+d)=0 := by
    intro d hd
    by_contra hg
    exact hd (hsupport hg)
  have hse : Summable fun n : ℕ => g (spectrumCosetRep hC2 N hfg mu+(e n : ℂ)) :=
    hs.congr fun n => congrArg g (he n).symm
  refine ⟨(hinj.summable_iff hvan).mp hse,?_⟩
  rw [← hinj.tsum_eq hsupport]
  exact tsum_congr fun n => congrArg g (he n)

/-- The literal whole spectrum sum equals its finitely many genuine lower
natural-number rows, with absolute scalar convergence proved. -/
theorem tsum_lowerSpectrum (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) (g : ℂ → ℂ)
    (hweight : ∀ a,g a≠0 → N.weight a≠⊥)
    (hs : ∀ mu∈spectrumCosets hC2 N hfg,
      Summable fun n : ℕ => g (lowerSpectrumRep hC2 N hfg mu+n)) :
    Summable g ∧ ∑' a : ℂ,g a=
      ∑ mu∈spectrumCosets hC2 N hfg,∑' n : ℕ,g (lowerSpectrumRep hC2 N hfg mu+n) := by
  have hr := fun mu hmu => lowerSpectrum_row hC2 N hfg mu g hweight (hs mu hmu)
  obtain ⟨hg,he⟩ := tsum_spectrumCosets hC2 N hfg g hweight (fun mu hmu => (hr mu hmu).1)
  refine ⟨hg,he.trans ?_⟩
  exact Finset.sum_congr rfl fun mu hmu => (hr mu hmu).2

end VOA.Huang.LogAssocExpansion
