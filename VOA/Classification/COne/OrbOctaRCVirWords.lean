import VOA.Classification.COne.OrbOctaRCVirDirect

/-! Words and rational sums of actual negative Virasoro operators. -/
set_option Elab.async false
namespace VOA.Classification.COne.OrbOctaRC
open VOA

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (A : VertexOperatorAlgebra V)

noncomputable def virDesc : List ℕ → V → V
  | [], v => v
  | k :: ks, v => A.L (-(k : ℤ)) (virDesc ks v)

noncomputable def virCombo (q : V) (cs : List (ℚ × List ℕ)) : V :=
  (cs.map fun t => (t.1 : ℂ) • virDesc A t.2 q).sum

theorem virCombo_append (q : V) (cs ds : List (ℚ × List ℕ)) :
    virCombo A q (cs ++ ds) = virCombo A q cs + virCombo A q ds := by
  simp [virCombo]

theorem virDesc_replicate (k n : ℕ) (q : V) :
    virDesc A (List.replicate n k) q = ((A.L (-(k : ℤ))) ^ n) q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, virDesc, ih, pow_succ', Module.End.mul_apply]

end VOA.Classification.COne.OrbOctaRC
