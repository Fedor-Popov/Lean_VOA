import VOA.DeligneAudit.LeviTypeA3Support

/-! Descending enumeration of the finite keys at each radical depth. -/

namespace VOA.DeligneAudit.A3Sector

def a3KeyDescLE (b c : ℕ) (x y : A3RadicalKey) : Prop :=
  x = y ∨ a3KeyLess b c y x

instance (b c : ℕ) : IsTrans A3RadicalKey (a3KeyDescLE b c) where
  trans := by
    intro x y z hxy hyz
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inr (a3KeyLess_trans b c hyz hxy)

instance (b c : ℕ) : Std.Antisymm (a3KeyDescLE b c) where
  antisymm := by
    intro x y hxy hyx
    rcases hxy with hxy | hxy
    · exact hxy
    rcases hyx with hyx | hyx
    · exact hyx.symm
    · exact False.elim ((a3KeyLess_irrefl b c x)
        (a3KeyLess_trans b c hyx hxy))

instance (b c : ℕ) : Std.Total (a3KeyDescLE b c) where
  total := by
    intro x y
    rcases a3KeyLess_trichotomy b c x y with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)

noncomputable instance (b c : ℕ) : DecidableRel (a3KeyDescLE b c) :=
  Classical.decRel _

noncomputable def a3OrderedKeys (a b c j : ℕ) : List A3RadicalKey :=
  (a3DepthKeyBox a b c j).sort (a3KeyDescLE b c)

theorem mem_a3OrderedKeys (a b c j : ℕ) (k : A3RadicalKey) :
    k ∈ a3OrderedKeys a b c j ↔ k ∈ a3DepthKeyBox a b c j := by
  simpa only [a3OrderedKeys] using
    (Finset.mem_sort (s := a3DepthKeyBox a b c j) (r := a3KeyDescLE b c))

theorem length_a3OrderedKeys (a b c j : ℕ) :
    (a3OrderedKeys a b c j).length = (a3DepthKeyBox a b c j).card := by
  simpa only [a3OrderedKeys] using
    (Finset.length_sort (s := a3DepthKeyBox a b c j) (r := a3KeyDescLE b c))

theorem pairwise_a3OrderedKeys (a b c j : ℕ) :
    (a3OrderedKeys a b c j).Pairwise (a3KeyDescLE b c) := by
  simpa only [a3OrderedKeys] using
    (Finset.pairwise_sort (a3DepthKeyBox a b c j) (a3KeyDescLE b c))

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule bracketTable V) (w : V)

theorem a3KeyBox_contains_nonzero (a b c j : ℕ) (k : A3RadicalKey)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (hdepth : k.d₁ + k.d₂ + k.d₃ = j)
    (hk : a3KeyLayer ρ w k ≠ ⊥) :
    k ∈ a3DepthKeyBox a b c j := by
  have hdeg : k.degree ≤ (a + b + c) * j := by
    by_contra hn
    apply hk
    have hgt : (a + b + c) * (k.d₁ + k.d₂ + k.d₃) < k.degree := by
      rw [hdepth]
      omega
    exact a3KeyLayer_eq_bot_of_degree_gt ρ w a b c k h hgt
  apply mem_a3DepthKeyBox a b c j k
  · omega
  · omega
  · omega
  · exact hdeg

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.mem_a3OrderedKeys
#print axioms VOA.DeligneAudit.A3Sector.length_a3OrderedKeys
#print axioms VOA.DeligneAudit.A3Sector.pairwise_a3OrderedKeys
#print axioms VOA.DeligneAudit.A3Sector.a3KeyBox_contains_nonzero
