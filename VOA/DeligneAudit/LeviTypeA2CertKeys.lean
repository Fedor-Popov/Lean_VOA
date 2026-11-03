import VOA.DeligneAudit.LeviTypeA2CertGeneration

/-! Radical keys and the height-degree lexicographic order. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

structure A2RadicalKey where
  d₁ : ℕ
  d₂ : ℕ
  degree : ℕ
  deriving DecidableEq, Repr

/-- The node-two `sl₂` highest-weight label of a radical key. -/
def a2KeyHeight (q : ℕ) (k : A2RadicalKey) : ℤ :=
  (q : ℤ) + (k.d₁ : ℤ) - (k.d₂ : ℤ)

/-- Height first, then mode degree, then both counts. -/
def a2KeyLess (q : ℕ) (a b : A2RadicalKey) : Prop :=
  a2KeyHeight q a < a2KeyHeight q b ∨
    a2KeyHeight q a = a2KeyHeight q b ∧
      (a.degree < b.degree ∨ a.degree = b.degree ∧
        (a.d₁ < b.d₁ ∨ a.d₁ = b.d₁ ∧ a.d₂ < b.d₂))

theorem a2KeyLess_irrefl (q : ℕ) (a : A2RadicalKey) : ¬ a2KeyLess q a a := by
  simp [a2KeyLess]

theorem a2KeyLess_trans (q : ℕ) {a b c : A2RadicalKey}
    (hab : a2KeyLess q a b) (hbc : a2KeyLess q b c) : a2KeyLess q a c := by
  rcases a with ⟨a₁, a₂, ad⟩
  rcases b with ⟨b₁, b₂, bd⟩
  rcases c with ⟨c₁, c₂, cd⟩
  dsimp [a2KeyLess, a2KeyHeight] at *
  omega

theorem a2KeyLess_trichotomy (q : ℕ) (a b : A2RadicalKey) :
    a2KeyLess q a b ∨ a = b ∨ a2KeyLess q b a := by
  rcases a with ⟨a₁, a₂, ad⟩
  rcases b with ⟨b₁, b₂, bd⟩
  dsimp [a2KeyLess, a2KeyHeight]
  simp only [A2RadicalKey.mk.injEq]
  omega

/-- A positive Cartan mode preserves height and raises degree. -/
theorem a2KeyLess_degree (q : ℕ) (k : A2RadicalKey) (r : ℕ) (hr : 0 < r) :
    a2KeyLess q k { k with degree := k.degree + r } := by
  dsimp [a2KeyLess, a2KeyHeight]
  omega

/-- Replacing one `f₁₂` by `f₁` raises the node-two height by two. -/
theorem a2KeyLess_raise (q : ℕ) (k : A2RadicalKey) :
    a2KeyLess q { k with d₂ := k.d₂ + 1 } { k with d₁ := k.d₁ + 1 } := by
  dsimp [a2KeyLess, a2KeyHeight]
  omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule
    VOA.AffineSl3.bracketTable V) (w : V)

/-- A fixed count and mode-degree subspace of the negative radical orbit. -/
def a2KeyLayer (k : A2RadicalKey) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ l : List (Fin 2 × ℕ),
    l.countP (fun x => x.1 = 0) = k.d₁ ∧
    l.countP (fun x => x.1 = 1) = k.d₂ ∧
    (l.map Prod.snd).sum = k.degree ∧
    l.length = k.d₁ + k.d₂ ∧
    z = radicalWord (a2RadicalOp ρ) l • w}

/-- Every individual radical key has finite-dimensional span. -/
theorem a2KeyLayer_finite (p q : ℕ) (k : A2RadicalKey)
    (h : A2LocalWeylRel ρ w p q) :
    FiniteDimensional ℂ (a2KeyLayer ρ w k) := by
  have hle : a2KeyLayer ρ w k ≤
      radicalLayer (a2RadicalOp ρ) w (k.d₁ + k.d₂) := by
    rw [a2KeyLayer, Submodule.span_le]
    intro z hz
    obtain ⟨l, _, _, _, hlen, rfl⟩ := hz
    exact Submodule.subset_span ⟨l, hlen, rfl⟩
  letI : FiniteDimensional ℂ
      (radicalLayer (a2RadicalOp ρ) w (k.d₁ + k.d₂)) :=
    a2_radicalLayer_finite ρ w p q (k.d₁ + k.d₂) h
  exact FiniteDimensional.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2KeyLess_irrefl
#print axioms VOA.DeligneAudit.A3Sector.a2KeyLess_trans
#print axioms VOA.DeligneAudit.A3Sector.a2KeyLess_trichotomy
#print axioms VOA.DeligneAudit.A3Sector.a2KeyLess_degree
#print axioms VOA.DeligneAudit.A3Sector.a2KeyLess_raise
#print axioms VOA.DeligneAudit.A3Sector.a2KeyLayer_finite
