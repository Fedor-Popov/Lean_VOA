import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleRepresentation
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleMono
import Mathlib.Data.List.Perm.Basic

/-! Exact word permutation for negative and contact blocks, at all modes. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
noncomputable section

theorem negative_bracket_zero : ∀ d e : Fin 3, bracketCoeff (negative d) (negative e) = 0 := by
  decide +kernel

theorem contact_bracket_zero : ∀ d e : Fin 8,
    bracketCoeff (Fin.natAdd 10 d) (Fin.natAdd 10 e) = 0 := by decide +kernel

variable (K : Type*) [Field K]

theorem zero_bracket_commute (m : ℕ) (a b : Fin 18) (h : bracketCoeff a b = 0)
    (k l : ℕ) (p : Ring K m) :
    deriv K m a k (deriv K m b l p) = deriv K m b l (deriv K m a k p) := by
  have hh := congrArg (fun D : Derivation K (Ring K m) (Ring K m) => D p)
    (deriv_bracket K m a b k l)
  apply sub_eq_zero.mp
  simpa only [Derivation.commutator_apply,Derivation.smul_apply,h,zero_zsmul] using hh

/-- Reordering an entire commuting color block preserves its whole polynomial. -/
theorem color_word_perm {ι : Type*} (m : ℕ) (color : ι → Fin 18)
    (hc : ∀ a b, bracketCoeff (color a) (color b) = 0)
    {l l' : List (ι × ℕ)} (h : l.Perm l') (p : Ring K m) :
    wordOp (representation K m) (l.map fun x => (color x.1,x.2)) p =
      wordOp (representation K m) (l'.map fun x => (color x.1,x.2)) p := by
  let op : (ι × ℕ) → Ring K m → Ring K m := fun x p => deriv K m (color x.1) x.2 p
  letI : LeftCommutative op := ⟨fun a b p => zero_bracket_commute K m _ _ (hc _ _) _ _ p⟩
  have he : ∀ (l : List (ι × ℕ)) (p : Ring K m),
      wordOp (representation K m) (l.map fun x => (color x.1,x.2)) p = l.foldr op p := by
    intro l p
    induction l with
    | nil => rfl
    | cons x l ih =>
        change deriv K m (color x.1) x.2
          (wordOp (representation K m) (l.map fun x => (color x.1,x.2)) p) = _
        rw [ih]
        rfl
  rw [he,he]
  exact h.foldr_eq p

theorem negative_word_perm (m : ℕ) {l l' : List (Fin 3 × ℕ)} (h : l.Perm l') (p : Ring K m) :
    wordOp (representation K m) (l.map fun x => (negative x.1,x.2)) p =
      wordOp (representation K m) (l'.map fun x => (negative x.1,x.2)) p :=
  color_word_perm K m negative negative_bracket_zero h p

theorem contact_word_perm (m : ℕ) {l l' : List (Fin 8 × ℕ)} (h : l.Perm l') (p : Ring K m) :
    wordOp (representation K m) (l.map fun x => (Fin.natAdd 10 x.1,x.2)) p =
      wordOp (representation K m) (l'.map fun x => (Fin.natAdd 10 x.1,x.2)) p :=
  color_word_perm K m (Fin.natAdd 10) contact_bracket_zero h p

end
#print axioms negative_word_perm
#print axioms contact_word_perm
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
