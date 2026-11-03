import VOA.DeligneAudit.LeviTypeA3GradedEffectiveTarget

/-! A word already in all three homogeneous Garland boxes reaches the target. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

private theorem a3_weight_first_degree (f : ℕ →₀ ℕ) (d s : ℕ)
    (hw : Finsupp.weight om f = (d, s)) : Finsupp.degree f = d := by
  have h := congrArg Prod.fst hw
  simpa [Finsupp.weight_apply, om, Finsupp.degree_apply,
    Finsupp.sum, Prod.fst_sum] using h

/-- The product of three box monomials is one of the finite key vectors. -/
theorem a3_three_box_word_mem (a b c : ℕ) (k : A3RadicalKey)
    (h₁ : k.d₁ ≤ a) (h₂ : k.d₂ ≤ b) (h₃ : k.d₃ ≤ c)
    (f g h : ℕ →₀ ℕ) (r s t : ℕ)
    (hf : BoxP a f) (hg : BoxP b g) (hh : BoxP c h)
    (hwf : Finsupp.weight om f = (k.d₁, r))
    (hwg : Finsupp.weight om g = (k.d₂, s))
    (hwh : Finsupp.weight om h = (k.d₃, t))
    (hd : r + s + t = k.degree) :
    (aWord (fun i => ρ.op (F 0) i) (VOA.DeligneAudit.CLAssembly.lst f) *
      ((VOA.DeligneAudit.CLAssembly.lst g).map
        fun i => ρ.op (F 1) i).prod *
      ((VOA.DeligneAudit.CLAssembly.lst h).map
        fun i => ρ.op (F 2) i).prod) w ∈
        a3EffectiveTarget ρ w a b c k := by
  classical
  have hmf : f ∈ a2BoxModeSet a k.d₁ :=
    (mem_a2BoxModeSet a k.d₁ h₁ f).mpr
      ⟨a3_weight_first_degree f k.d₁ r hwf, hf⟩
  have hmg : g ∈ a2BoxModeSet b k.d₂ :=
    (mem_a2BoxModeSet b k.d₂ h₂ g).mpr
      ⟨a3_weight_first_degree g k.d₂ s hwg, hg⟩
  have hmh : h ∈ a2BoxModeSet c k.d₃ :=
    (mem_a2BoxModeSet c k.d₃ h₃ h).mpr
      ⟨a3_weight_first_degree h k.d₃ t hwh, hh⟩
  have hfg : ((f, g), h) ∈
      a3ThreeBoxKeyTriples a b c k.d₁ k.d₂ k.d₃ k.degree := by
    simp only [a3ThreeBoxKeyTriples, Finset.mem_filter,
      a3ThreeBoxModeSet, Finset.mem_product]
    refine ⟨⟨⟨hmf, hmg⟩, hmh⟩, ?_⟩
    simpa [a3BoxDegree, hwf, hwg, hwh] using hd
  have hv : a3ThreeBoxValue ρ w ((f, g), h) ∈
      a3ThreeBoxKeyVectors ρ w a b c k.d₁ k.d₂ k.d₃ k.degree := by
    exact Finset.mem_image.mpr ⟨((f, g), h), hfg, rfl⟩
  have hs : a3ThreeBoxValue ρ w ((f, g), h) ∈
      a3ThreeBoxTarget ρ w a b c k :=
    (le_sup_left : Submodule.span ℂ
      (a3ThreeBoxKeyVectors ρ w a b c k.d₁ k.d₂ k.d₃ k.degree : Set V) ≤
        a3ThreeBoxTarget ρ w a b c k)
      (Submodule.subset_span hv)
  simpa [a3EffectiveTarget, h₁, h₂, h₃, a3ThreeBoxValue] using hs

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_three_box_word_mem
