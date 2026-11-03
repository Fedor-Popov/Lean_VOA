import VOA.DeligneAudit.LeviTypeA3GradedWordSplit
import VOA.DeligneAudit.LeviTypeA3FirstBoxGraded
import VOA.DeligneAudit.LeviTypeA2CertGradedTwoBox

/-! The first colour box on an already sorted three-colour radical word. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

def a3FirstBoxSortedSpan (a : ℕ) (xs ys zs : List ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ f : ℕ →₀ ℕ,
    BoxP a f ∧ Finsupp.weight om f = (xs.length, xs.sum) ∧
      v = (Sl2Weyl.evAlg (fun s => ρ.op (F 0) s) (a3_first_comm ρ)
        (MvPolynomial.monomial f 1) *
          (ys.map fun s => ρ.op (F 1) s).prod *
            (zs.map fun s => ρ.op (F 2) s).prod) w}

theorem a3_first_box_sorted (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (xs ys zs : List ℕ) :
    (aWord (fun s => ρ.op (F 0) s) xs *
      (ys.map fun s => ρ.op (F 1) s).prod *
        (zs.map fun s => ρ.op (F 2) s).prod) w ∈
      a3FirstBoxSortedSpan ρ w a xs ys zs := by
  let l : List (Fin 3 × ℕ) :=
    (ys.map fun s => ((1 : Fin 3), s)) ++
      (zs.map fun s => ((2 : Fin 3), s))
  have hbox := a3_first_box_graded_with_spectators ρ w a b c h l
    (a2_mono_hom xs)
  have hB : (l.map fun x => radicalOp ρ x.1 x.2).prod =
      (ys.map fun s => ρ.op (F 1) s).prod *
        (zs.map fun s => ρ.op (F 2) s).prod := by
    simp [l, List.map_append, List.map_map, Function.comp_def, radicalOp]
  simpa [a3FirstBoxSortedSpan, aWord, hB, Module.End.mul_apply,
    VOA.DeligneAudit.CLAssembly.evAlg_mono, mul_assoc] using hbox

/-- The first box is homogeneous for the complete three-colour key. -/
theorem a3FirstBoxSortedSpan_le_key (a : ℕ) (xs ys zs : List ℕ) :
    a3FirstBoxSortedSpan ρ w a xs ys zs ≤
      a3KeyLayer ρ w
        ⟨xs.length, ys.length, zs.length, xs.sum + ys.sum + zs.sum⟩ := by
  rw [a3FirstBoxSortedSpan, Submodule.span_le]
  intro v hv
  obtain ⟨f, _, hweight, rfl⟩ := hv
  let fs := VOA.DeligneAudit.CLAssembly.lst f
  have hlen : fs.length = xs.length := by
    rw [a2_lst_length]
    have h := congrArg Prod.fst hweight
    simpa using h
  have hsum : fs.sum = xs.sum := by
    rw [a2_lst_sum]
    have h := congrArg Prod.snd hweight
    simpa using h
  have hword := a2_evAlg_monomial_word
    (fun s => ρ.op (F 0) s) (a3_first_comm ρ) f
  have hmem := a3_three_mode_mem_key ρ w fs ys zs
  rw [hword]
  simpa only [hlen, hsum, mul_assoc, Module.End.mul_apply] using hmem

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_first_box_sorted
#print axioms VOA.DeligneAudit.A3Sector.a3FirstBoxSortedSpan_le_key
