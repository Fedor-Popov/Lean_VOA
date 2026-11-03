import VOA.Huang.LogAssocLowerSpectrum

/-! Unique selection of an actual generalized intermediate weight from the
proved disjoint lower spectrum rows. This will identify literal iterate
logarithmic coefficients without an expansion witness. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor
open Classical
open scoped BigOperators

/-- A natural lower row contains a specified complex exponent at most once. -/
theorem natCoset_indicator (r γ C : ℂ) :
    Summable (fun n : ℕ => if r+n=γ then C else 0) ∧
      (∑' n : ℕ,if r+n=γ then C else 0)=(if ∃ n : ℕ,r+n=γ then C else 0) := by
  classical
  by_cases h : ∃ n : ℕ,r+n=γ
  · obtain ⟨n,hn⟩ := h
    have he (m : ℕ) : (r+(m : ℂ)=γ) ↔ m=n := by
      constructor
      · intro hm
        rw [← hn] at hm
        exact_mod_cast add_left_cancel hm
      · rintro rfl
        exact hn
    have hs : Function.support (fun m : ℕ => if r+m=γ then C else 0)⊆{n} := by
      intro m hm
      by_contra hmn
      have hmn' : m≠n := by simpa only [Set.mem_singleton_iff] using hmn
      change (if r+(m : ℂ)=γ then C else 0)≠0 at hm
      rw [if_neg ((he m).not.mpr hmn')] at hm
      exact hm rfl
    refine ⟨summable_of_hasFiniteSupport ((Set.finite_singleton n).subset hs),?_⟩
    rw [if_pos ⟨n,hn⟩,tsum_eq_single n (fun m hmn => by rw [if_neg ((he m).not.mpr hmn)]),if_pos hn]
  · have he : (fun n : ℕ => if r+n=γ then C else 0)=(fun _ => (0 : ℂ)) := by
      funext n
      rw [if_neg (fun hn => h ⟨n,hn⟩)]
    rw [he,if_neg h]
    exact ⟨summable_zero,tsum_zero⟩

universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Actual spectrum support and proved disjoint lower cosets select exactly
one intermediate weight, even for zero scalar coefficients. -/
theorem lowerSpectrum_indicator (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) (γ C : ℂ) (hweight : C≠0 → N.weight γ≠⊥) :
    (∑ mu∈spectrumCosets hC2 N hfg,
      if ∃ n : ℕ,lowerSpectrumRep hC2 N hfg mu+n=γ then C else 0)=C := by
  classical
  let g : ℂ → ℂ := fun a => if a=γ then C else 0
  have hg : ∀ a,g a≠0 → N.weight a≠⊥ := by
    intro a ha
    by_cases he : a=γ
    · subst a
      exact hweight (by simpa only [g,ite_true] using ha)
    · simp only [g,if_neg he] at ha
      exact False.elim (ha rfl)
  have hs (mu : ℂ) : Summable fun n : ℕ => g (lowerSpectrumRep hC2 N hfg mu+n) :=
    (natCoset_indicator (lowerSpectrumRep hC2 N hfg mu) γ C).1
  have he := (tsum_lowerSpectrum hC2 N hfg g hg (fun mu _ => hs mu)).2
  have hsingle : (∑' a : ℂ,g a)=C := by
    rw [tsum_eq_single γ (fun a ha => by simp only [g,if_neg ha])]
    simp only [g,ite_true]
  rw [hsingle] at he
  have he' : (∑ mu∈spectrumCosets hC2 N hfg,∑' n : ℕ,g (lowerSpectrumRep hC2 N hfg mu+n))=
      ∑ mu∈spectrumCosets hC2 N hfg,if ∃ n : ℕ,lowerSpectrumRep hC2 N hfg mu+n=γ then C else 0 := by
    exact Finset.sum_congr rfl fun mu _ => (natCoset_indicator (lowerSpectrumRep hC2 N hfg mu) γ C).2
  exact he'.symm.trans he.symm

end VOA.Huang.LogAssocExpansion
