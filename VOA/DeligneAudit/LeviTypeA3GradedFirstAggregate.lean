import VOA.DeligneAudit.LeviTypeA3GradedFirstStep

/-! Aggregate the exact first-colour box across a fixed radical key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

def a3FirstBoxKeySpan (a : ℕ) (k : A3RadicalKey) : Submodule ℂ V :=
  ⨆ xs : List ℕ, ⨆ ys : List ℕ, ⨆ zs : List ℕ,
    ⨆ (_ : xs.length = k.d₁), ⨆ (_ : ys.length = k.d₂),
      ⨆ (_ : zs.length = k.d₃),
        ⨆ (_ : xs.sum + ys.sum + zs.sum = k.degree),
          a3FirstBoxSortedSpan ρ w a xs ys zs

theorem a3KeyLayer_le_firstBox (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (k : A3RadicalKey) :
    a3KeyLayer ρ w k ≤ a3FirstBoxKeySpan ρ w a k := by
  rw [a3KeyLayer_eq_sorted ρ w k, a3SortedKeySpan, Submodule.span_le]
  intro v hv
  obtain ⟨xs, ys, zs, hx, hy, hz, hd, rfl⟩ := hv
  have hbox := a3_first_box_sorted ρ w a b c h xs ys zs
  have hle : a3FirstBoxSortedSpan ρ w a xs ys zs ≤
      a3FirstBoxKeySpan ρ w a k := by
    unfold a3FirstBoxKeySpan
    exact le_iSup_of_le xs (le_iSup_of_le ys
      (le_iSup_of_le zs (le_iSup_of_le hx
        (le_iSup_of_le hy (le_iSup_of_le hz
          (le_iSup_of_le hd le_rfl))))))
  exact hle hbox

theorem a3FirstBoxKeySpan_le_layer (a : ℕ) (k : A3RadicalKey) :
    a3FirstBoxKeySpan ρ w a k ≤ a3KeyLayer ρ w k := by
  unfold a3FirstBoxKeySpan
  apply iSup_le
  intro xs
  apply iSup_le
  intro ys
  apply iSup_le
  intro zs
  apply iSup_le
  intro hx
  apply iSup_le
  intro hy
  apply iSup_le
  intro hz
  apply iSup_le
  intro hd
  have h := a3FirstBoxSortedSpan_le_key ρ w a xs ys zs
  simpa only [hx, hy, hz, hd] using h

theorem a3KeyLayer_eq_firstBox (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (k : A3RadicalKey) :
    a3KeyLayer ρ w k = a3FirstBoxKeySpan ρ w a k :=
  le_antisymm (a3KeyLayer_le_firstBox ρ w a b c h k)
    (a3FirstBoxKeySpan_le_layer ρ w a k)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3KeyLayer_le_firstBox
#print axioms VOA.DeligneAudit.A3Sector.a3FirstBoxKeySpan_le_layer
#print axioms VOA.DeligneAudit.A3Sector.a3KeyLayer_eq_firstBox
