import VOA.DeligneAudit.D4FusionToroidalFinalCyclic

/-! Exact rank of an exhaustively filtered finite-dimensional toroidal space. -/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : ToroidalAction f V) (w : V)

theorem denominator_coord (v : ℕ →₀ V) (hv : v ∈ denominator A w) (d : ℕ) :
    v d ∈ evalFbelow A w d := by
  change v ∈ Submodule.span ℂ
    {v | ∃ e x, x ∈ evalFbelow A w e ∧ v = Finsupp.single e x} at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨e, x, hx, rfl⟩ := hv
      by_cases he : e = d
      · subst d
        simpa using hx
      · simp [he]
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [Finsupp.add_apply] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      simpa only [Finsupp.smul_apply] using Submodule.smul_mem _ a ih

def pieceRepresentative (B : ℕ)
    (v : Π d : Fin B, evalFbelow A w (d.val + 1)) : numerator A w :=
  ∑ d : Fin B, single A w d.val (v d).1 (v d).2

theorem pieceRepresentative_mk (B : ℕ)
    (v : Π d : Fin B, evalFbelow A w (d.val + 1)) :
    (kernel A w).mkQ (pieceRepresentative A w B v) = pieceSum A w B v := by
  simp [pieceRepresentative, pieceSum, symbol, singleMap, map_sum]

theorem pieceRepresentative_coord (B : ℕ)
    (v : Π d : Fin B, evalFbelow A w (d.val + 1)) (d : Fin B) :
    (pieceRepresentative A w B v).1 d.val = (v d).1 := by
  simp only [pieceRepresentative, Submodule.coe_sum, single, Finset.sum_apply',
    Finsupp.single_apply]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e _ hed
    have he : e.val ≠ d.val := fun h => hed (Fin.ext h)
    simp [he]
  · simp

theorem pieceSum_ker_le_lower (B : ℕ) :
    LinearMap.ker (pieceSum A w B) ≤ LinearMap.range (lowerEmbed A w B) := by
  intro v hv
  have hy : pieceRepresentative A w B v ∈ kernel A w := by
    apply (Submodule.Quotient.mk_eq_zero (kernel A w)).mp
    change (kernel A w).mkQ (pieceRepresentative A w B v) = 0
    rw [pieceRepresentative_mk]
    exact hv
  have hd : ∀ d : Fin B, (v d).1 ∈ evalFbelow A w d.val := by
    intro d
    rw [← pieceRepresentative_coord A w B v d]
    exact denominator_coord A w (pieceRepresentative A w B v).1 hy d.val
  let u : Π d : Fin B, evalFbelow A w d.val := fun d => ⟨(v d).1, hd d⟩
  refine ⟨u, ?_⟩
  funext d
  apply Subtype.ext
  rfl

theorem finrank_gr_eq_source [FiniteDimensional ℂ V] (B : ℕ)
    (hB : evalFbelow A w B = ⊤) :
    Module.finrank ℂ (Gr A w) = Module.finrank ℂ V := by
  letI : FiniteDimensional ℂ (Gr A w) :=
    (finrank_gr_le_source A w B hB).1
  have hker : LinearMap.ker (pieceSum A w B) =
      LinearMap.range (lowerEmbed A w B) := by
    apply le_antisymm
    · exact pieceSum_ker_le_lower A w B
    · rintro _ ⟨v, rfl⟩
      exact pieceSum_lower_zero A w B v
  have hrank := (pieceSum A w B).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (pieceSum_surjective A w B hB), finrank_top,
    hker, LinearMap.finrank_range_of_inj (lowerEmbed_injective A w B),
    Module.finrank_pi_fintype, Module.finrank_pi_fintype] at hrank
  have hsum : (∑ d : Fin B, Module.finrank ℂ (evalFbelow A w (d.val + 1))) =
      (∑ d : Fin B, Module.finrank ℂ (evalFbelow A w d.val)) +
        Module.finrank ℂ V := by
    calc
      _ = ∑ d ∈ Finset.range B,
          Module.finrank ℂ (evalFbelow A w (d + 1)) :=
        Fin.sum_univ_eq_sum_range _ B
      _ = (∑ d ∈ Finset.range B, Module.finrank ℂ (evalFbelow A w d)) +
          Module.finrank ℂ (evalFbelow A w B) := rank_tel A w B
      _ = (∑ d : Fin B, Module.finrank ℂ (evalFbelow A w d.val)) +
          Module.finrank ℂ V := by
        rw [hB, finrank_top]
        exact congrArg (fun q => q + Module.finrank ℂ V)
          (Fin.sum_univ_eq_sum_range
            (fun d => Module.finrank ℂ (evalFbelow A w d)) B).symm
  omega

end

end VOA.DeligneAudit.Toroidal.FusionGr

namespace VOA.DeligneAudit.Toroidal.D4Fusion

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.D1TensorG
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem graded_total_rank_eq (m : ℕ) :
    Module.finrank ℂ (FusionGr.Gr (action m) (generator m)) = 29 ^ m := by
  obtain ⟨B, hB⟩ := exists_evalFbelow_top D4sector
    D1SiteG.D4Check.table_skewC (D1TensorG.points m)
    (D1TensorG.points_injective m)
  change evalFbelow (action m) (generator m) B = ⊤ at hB
  exact (FusionGr.finrank_gr_eq_source (action m) (generator m) B hB).trans
    (dimension m)

end

end VOA.DeligneAudit.Toroidal.D4Fusion

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.finrank_gr_eq_source
#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.graded_total_rank_eq
