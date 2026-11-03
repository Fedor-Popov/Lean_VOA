import VOA.Huang.LogHuangODEProductWeights
import VOA.Modules.LogTensorFinSpan

/-! Finitely generated generalized modules have finitely many genuine
coset bases. Every nonzero weight is a natural-number level above one
of these actual bases; no one-coset or ordinary-module assumption occurs. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEProduct
open VOA VOA.LogTensor VOA.C2Rigid
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- A finite set of actual lower coset bases covers every nonzero generalized weight. -/
theorem exists_finite_cosetBases (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) :
    ∃ H : Finset ℂ,(∀ h∈H,CosetBase N.toGW h) ∧
      ∀ a,N.weight a≠⊥ → ∃ h∈H,∃ j : ℕ,a=h+j := by
  classical
  obtain ⟨S,hS⟩ := LogFin.exists_weight_cosets N hC2 hfg
  choose h K he hl using fun b : ℂ => exists_cosetBase N.toGW b
  refine ⟨S.image h,?_,?_⟩
  · intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    exact hl c
  · intro a ha
    obtain ⟨b,hb,d,hd⟩ := hS a ha
    let j : ℤ := (K b : ℤ)+d
    have hj : a=h b+j := by
      calc a=b+d := hd
        _=(h b+(K b : ℂ))+d := congrArg (fun v : ℂ => v+d) (he b)
        _=h b+j := by dsimp only [j]; push_cast; ring
    have hj0 : 0≤j := by
      by_contra hn
      have hbot := hl b j (by omega)
      rw [← hj] at hbot
      exact ha hbot
    refine ⟨h b,Finset.mem_image.mpr ⟨b,hb,rfl⟩,j.toNat,?_⟩
    rw [hj]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hj0).symm

end VOA.Huang.LogHuangODEProduct
