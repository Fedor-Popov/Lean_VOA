import VOA.DeligneAudit.LeviTypeA3Generation
import VOA.DeligneAudit.A3SectorSl2

/-! Radical keys for the `gl₃` Levi filtration. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

structure A3RadicalKey where
  d₁ : ℕ
  d₂ : ℕ
  d₃ : ℕ
  degree : ℕ
  deriving DecidableEq, Repr

/-- Sum of the two Levi simple-root labels at a radical key. -/
def a3KeyHeight (b c : ℕ) (k : A3RadicalKey) : ℤ :=
  (b : ℤ) + c + k.d₁ - k.d₃

/-- Total order: height, mode degree, and the three letter counts. -/
def a3KeyLess (b c : ℕ) (x y : A3RadicalKey) : Prop :=
  a3KeyHeight b c x < a3KeyHeight b c y ∨
    a3KeyHeight b c x = a3KeyHeight b c y ∧
      (x.degree < y.degree ∨ x.degree = y.degree ∧
        (x.d₁ < y.d₁ ∨ x.d₁ = y.d₁ ∧
          (x.d₂ < y.d₂ ∨ x.d₂ = y.d₂ ∧ x.d₃ < y.d₃)))

theorem a3KeyLess_irrefl (b c : ℕ) (k : A3RadicalKey) :
    ¬ a3KeyLess b c k k := by
  simp [a3KeyLess]

theorem a3KeyLess_trans (b c : ℕ) {x y z : A3RadicalKey}
    (hxy : a3KeyLess b c x y) (hyz : a3KeyLess b c y z) :
    a3KeyLess b c x z := by
  rcases x with ⟨x₁, x₂, x₃, xd⟩
  rcases y with ⟨y₁, y₂, y₃, yd⟩
  rcases z with ⟨z₁, z₂, z₃, zd⟩
  dsimp [a3KeyLess, a3KeyHeight] at *
  omega

theorem a3KeyLess_trichotomy (b c : ℕ) (x y : A3RadicalKey) :
    a3KeyLess b c x y ∨ x = y ∨ a3KeyLess b c y x := by
  rcases x with ⟨x₁, x₂, x₃, xd⟩
  rcases y with ⟨y₁, y₂, y₃, yd⟩
  dsimp [a3KeyLess, a3KeyHeight]
  simp only [A3RadicalKey.mk.injEq]
  omega

theorem a3KeyLess_degree (b c : ℕ) (k : A3RadicalKey)
    (r : ℕ) (hr : 0 < r) :
    a3KeyLess b c k { k with degree := k.degree + r } := by
  dsimp [a3KeyLess, a3KeyHeight]
  omega

theorem a3KeyLess_raise_one (b c : ℕ) (k : A3RadicalKey) :
    a3KeyLess b c { k with d₂ := k.d₂ + 1 }
      { k with d₁ := k.d₁ + 1 } := by
  dsimp [a3KeyLess, a3KeyHeight]
  omega

theorem a3KeyLess_raise_two (b c : ℕ) (k : A3RadicalKey) :
    a3KeyLess b c { k with d₃ := k.d₃ + 1 }
      { k with d₂ := k.d₂ + 1 } := by
  dsimp [a3KeyLess, a3KeyHeight]
  omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule bracketTable V) (w : V)

/-- Fixed radical counts and total mode degree. -/
def a3KeyLayer (k : A3RadicalKey) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ l : List (Fin 3 × ℕ),
    l.countP (fun x => x.1 = 0) = k.d₁ ∧
    l.countP (fun x => x.1 = 1) = k.d₂ ∧
    l.countP (fun x => x.1 = 2) = k.d₃ ∧
    (l.map Prod.snd).sum = k.degree ∧
    l.length = k.d₁ + k.d₂ + k.d₃ ∧
    z = radicalWord (radicalOp ρ) l • w}

theorem a3KeyLayer_finite (a b c : ℕ) (k : A3RadicalKey)
    (h : LocalWeylRel ρ w (weightABC a b c)) :
    FiniteDimensional ℂ (a3KeyLayer ρ w k) := by
  have hle : a3KeyLayer ρ w k ≤
      radicalLayer (radicalOp ρ) w (k.d₁ + k.d₂ + k.d₃) := by
    rw [a3KeyLayer, Submodule.span_le]
    intro z hz
    obtain ⟨l, _, _, _, _, hlen, rfl⟩ := hz
    exact Submodule.subset_span ⟨l, hlen, rfl⟩
  letI : FiniteDimensional ℂ
      (radicalLayer (radicalOp ρ) w (k.d₁ + k.d₂ + k.d₃)) :=
    radical_layer_finite_of_localWeyl ρ w (weightABC a b c) h _
  exact FiniteDimensional.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3KeyLess_irrefl
#print axioms VOA.DeligneAudit.A3Sector.a3KeyLess_trans
#print axioms VOA.DeligneAudit.A3Sector.a3KeyLess_trichotomy
#print axioms VOA.DeligneAudit.A3Sector.a3KeyLess_degree
#print axioms VOA.DeligneAudit.A3Sector.a3KeyLess_raise_one
#print axioms VOA.DeligneAudit.A3Sector.a3KeyLess_raise_two
#print axioms VOA.DeligneAudit.A3Sector.a3KeyLayer_finite
