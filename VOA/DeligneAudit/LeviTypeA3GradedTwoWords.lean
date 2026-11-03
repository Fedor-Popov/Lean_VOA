import VOA.DeligneAudit.LeviTypeA3GradedThreeWords

/-! The first adjacent-pair box produces a homogeneous two-box word. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- Words with F₁ and F₂ in their homogeneous boxes; F₃ is still arbitrary. -/
def a3TwoBoxKeySpan (a b : ℕ) (k : A3RadicalKey) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ (f g : ℕ →₀ ℕ) (zs : List ℕ) (r s : ℕ),
    BoxP a f ∧ BoxP b g ∧
    Finsupp.weight om f = (k.d₁, r) ∧
    Finsupp.weight om g = (k.d₂, s) ∧
    zs.length = k.d₃ ∧ r + s + zs.sum = k.degree ∧
    v = (aWord (fun i => ρ.op (F 0) i) (VOA.DeligneAudit.CLAssembly.lst f) *
      ((VOA.DeligneAudit.CLAssembly.lst g).map
        fun i => ρ.op (F 1) i).prod *
      (zs.map fun i => ρ.op (F 2) i).prod) w}

/-- The first pair box lies in the two-box target when its fixed first word
already satisfies the node-one box. -/
theorem a3_pair_zero_box_le_two (a b : ℕ) (k : A3RadicalKey)
    (f : ℕ →₀ ℕ) (zs : List ℕ) (r s : ℕ)
    (hf : BoxP a f) (hwf : Finsupp.weight om f = (k.d₁, r))
    (hz : zs.length = k.d₃) (hd : r + s + zs.sum = k.degree) :
    a3PairBoxSpan ρ w 0 (VOA.DeligneAudit.CLAssembly.lst f) zs b k.d₂ s ≤
      a3TwoBoxKeySpan ρ w a b k := by
  rw [a3PairBoxSpan, a3TwoBoxKeySpan, Submodule.span_le]
  intro v hv
  obtain ⟨g, hg, hwg, rfl⟩ := hv
  rw [a2_evAlg_monomial_word]
  apply Submodule.subset_span
  refine ⟨f, g, zs, r, s, hf, hg, hwf, hwg, hz, hd, ?_⟩
  simp [a3ConvA, a3ConvB, a3ConvSpectator, aWord,
    mul_assoc, Module.End.mul_apply]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_pair_zero_box_le_two
