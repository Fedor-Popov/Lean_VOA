import VOA.DeligneAudit.D4LeviKSRzOrbit

/-! A symmetric source polynomial for the Rz Garland generator. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

noncomputable def rzXSeed (a b : ℕ)
    (α : Fin b ⊕ Fin a → ℕ) :
    MvPolynomial (Fin b ⊕ Fin a) ℂ :=
  ∏ t : Fin b ⊕ Fin a, X t ^ α t

noncomputable def rzZSeed (k l s : ℕ) (β : Fin l → ℕ) :
    MvPolynomial (Fin (k + l)) ℂ := by
  classical
  exact rename (Fin.castAdd l) (hsymm (Fin k) ℂ s) *
    ∏ j : Fin l, X (Fin.natAdd k j) ^ β j

noncomputable def rzSourceGenerator (a b k l s : ℕ)
    (α : Fin b ⊕ Fin a → ℕ) (β : Fin l → ℕ) :
    MvPolynomial (PairSource a b (k + l)) ℂ :=
  rename Sum.inl (rzOrbitSum _ (rzXSeed a b α)) *
    rename (fun z : Fin (k + l) =>
      (Sum.inr (Sum.inr z) : PairSource a b (k + l)))
      (rzOrbitSum _ (rzZSeed k l s β))

theorem rzSourceGenerator_mem (a b k l s : ℕ)
    (α : Fin b ⊕ Fin a → ℕ) (β : Fin l → ℕ) :
    rzSourceGenerator a b k l s α β ∈
      pairSourceSymmetric a b (k + l) := by
  unfold rzSourceGenerator
  exact (pairSourceSymmetric a b (k + l)).mul_mem
    (rzOrbitSum_source_X_mem a b (k + l) (rzXSeed a b α))
    (rzOrbitSum_source_Z_mem a b (k + l) (rzZSeed k l s β))

def rzXTarget (a b c : ℕ) : Fin b ⊕ Fin a → PairTarget a b c
  | Sum.inl y => Sum.inr (Sum.inl y)
  | Sum.inr x => Sum.inl x

theorem rzSourceGenerator_restriction (a b k l s : ℕ)
    (α : Fin b ⊕ Fin a → ℕ) (β : Fin l → ℕ) :
    pairRestriction a b (k + l) (rzSourceGenerator a b k l s α β) =
      rename (rzXTarget a b (k + l))
          (rzOrbitSum _ (rzXSeed a b α)) *
        rename (fun z : Fin (k + l) =>
          (Sum.inr (Sum.inr z) : PairTarget a b (k + l)))
          (rzOrbitSum _ (rzZSeed k l s β)) := by
  simp only [rzSourceGenerator, pairRestriction, map_mul,
    rename_rename]
  have hX : pairVariable a b (k + l) ∘ Sum.inl =
      rzXTarget a b (k + l) := by
    funext t
    rcases t with y | x <;> rfl
  have hZ : pairVariable a b (k + l) ∘
      (fun z : Fin (k + l) =>
        (Sum.inr (Sum.inr z) : PairSource a b (k + l))) =
      (fun z : Fin (k + l) =>
        (Sum.inr (Sum.inr z) : PairTarget a b (k + l))) := by
    rfl
  rw [hX, hZ]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzSourceGenerator_mem
#print axioms VOA.DeligneAudit.D4Levi.rzSourceGenerator_restriction
