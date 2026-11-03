import VOA.Classification.COne.OrbC2hSectors
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2e OrbC2g LatMod

def VectorCertificate (S T : SectorVector) : Prop :=
  ∀ t ∈ compact (S ++ scaleVector (-1) T), t.2 = []

instance (S T : SectorVector) : Decidable (VectorCertificate S T) :=
  inferInstanceAs (Decidable (∀ t ∈ compact (S ++ scaleVector (-1) T), t.2 = []))

theorem evaluate_zero_of_polys (S : SectorVector) (h : ∀ t ∈ S, t.2 = []) :
    evaluate S = 0 := by
  induction S with
  | nil => rfl
  | cons t S ih =>
    rcases t with ⟨d,P⟩
    have hp : P = [] := h (d,P) (by simp)
    rw [evaluate, hp, evRc_nil, map_zero, zero_add]
    apply ih
    intro t ht
    exact h _ (List.mem_cons_of_mem _ ht)

theorem vector_eq_of_certificate (S T : SectorVector) (h : VectorCertificate S T) :
    evaluate S = evaluate T := by
  have hh := evaluate_zero_of_polys _ h
  rw [evaluate_compact, evaluate_append, evaluate_scaleVector] at hh
  norm_num only [Rat.cast_neg, Rat.cast_one, neg_one_smul] at hh
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hh)

theorem neutral_value (Q : RawPoly ℕ) (n : ℤ) (S T : SectorVector)
    (h : VectorCertificate (neutralS Q n S) T) :
    (V2m 4 four_ge_one).smul (ls 4 Q) n (evaluate S) = evaluate T := by
  rw [← evaluate_neutralS]
  exact vector_eq_of_certificate _ _ h

theorem e_value (n : ℤ) (S T : SectorVector)
    (h : VectorCertificate (eS n S) T) :
    (V2m 4 four_ge_one).smul (EP 4 four_ge_one) n (evaluate S) = evaluate T := by
  rw [← evaluate_eS]
  exact vector_eq_of_certificate _ _ h


/-- Add vectors sharing a charge ordering; a mismatched ordering falls back to concatenation. -/
def zipAdd : SectorVector → SectorVector → SectorVector
  | [], T => T
  | S, [] => S
  | (d,P)::S, (e,Q)::T => if d = e then (d,mergeRaw 100000 P Q)::zipAdd S T
      else ((d,P)::S) ++ ((e,Q)::T)

theorem evaluate_zipAdd (S T : SectorVector) : evaluate (zipAdd S T) = evaluate S + evaluate T := by
  induction S generalizing T with
  | nil => simp [zipAdd, evaluate]
  | cons t S ih =>
    rcases t with ⟨d,P⟩
    cases T with
    | nil => simp [zipAdd, evaluate]
    | cons t T =>
      rcases t with ⟨e,Q⟩
      rw [zipAdd]
      split_ifs with h
      · subst e
        simp only [evaluate, evRc_mergeRaw, map_add, ih]
        abel
      · exact evaluate_append _ _

end VOA.Classification.COne.OrbC2h
