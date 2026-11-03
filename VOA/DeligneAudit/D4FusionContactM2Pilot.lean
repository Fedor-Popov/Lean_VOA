import VOA.DeligneAudit.D4FusionContactM2PilotData
import VOA.DeligneAudit.D4FusionContactPolynomialEval

/-!
# Symbolic polynomial membership for the checked two-row pilot

The raw operation is actual multiplication of the parent polynomial by
one variable. Its monomial permutations and integer elimination identity
are checked in the light data module; this assembly keeps them symbolic.
Parent-row membership premises are discharged by the later certificate DAG.
-/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Pilot

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

variable {ι : Type} (f : Fin 18 → ι)

def basis (j : Fin 77) : MvPolynomial ι ℂ := polyWord ((mono j).map f)

def parentPoly (r : Fin 2) : MvPolynomial ι ℂ :=
  ((parents r).map fun x => x.2.1 • polyWord (x.1.map f)).sum

def normalPoly (r : Fin 2) : MvPolynomial ι ℂ := evalZ (basis f) (sparse (normal r))

private theorem polyWord_perm {a b : List ι} (h : a.Perm b) : polyWord a = polyWord b :=
  (h.map MvPolynomial.X).prod_eq

private theorem parent_sum (v : Fin 18) :
    ∀ ps : List (List (Fin 18) × ℤ × Fin 77),
      ps.Forall (fun x => (x.1 ++ [v]).Perm (mono x.2.2)) →
      (ps.map fun x => x.2.1 • basis f x.2.2).sum =
        (ps.map fun x => x.2.1 • polyWord (x.1.map f)).sum * MvPolynomial.X (f v)
  | [], _ => by simp
  | x::ps, hp => by
      have hh := (List.forall_cons _ _ _).mp hp
      simp only [List.map_cons, List.sum_cons, add_mul]
      rw [parent_sum v ps hh.2]
      have hm : basis f x.2.2 = polyWord (x.1.map f) * MvPolynomial.X (f v) := by
        calc
          _ = polyWord ((x.1 ++ [v]).map f) := (polyWord_perm (hh.1.map f)).symm
          _ = _ := by simp [polyWord, List.map_append, List.prod_append]
      rw [hm, smul_mul_assoc]

/-- The certificate's raw vector is the actual parent multiplication,
not an independently assumed relation. -/
theorem raw_poly_eq (r : Fin 2) :
    evalZ (basis f) (sparse (raw r)) = parentPoly f r * MvPolynomial.X (f (multiplier r)) := by
  rw [evalZ_sparse]
  simp only [raw, List.map_map, Function.comp_def]
  exact parent_sum f (multiplier r) (parents r) (parent_target_perm r)

/-- The normalized row follows from actual parent and earlier-row
membership. The full DAG later discharges these structural premises. -/
theorem normalized_row_mem (I : Ideal (MvPolynomial ι ℂ)) (r : Fin 2)
    (hparent : parentPoly f r ∈ I)
    (hearlier : ∀ x ∈ earlier r, evalZ (basis f) (sparse x.2) ∈ I) :
    normalPoly f r ∈ I := by
  apply row_mem_of_identity (I.restrictScalars ℂ) (basis f) (raw r) (normal r) (earlier r)
    (scale r) (factor r) (normalization_nonzero r)
  · funext j
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] using row_identity r j
  · rw [raw_poly_eq]
    exact Ideal.mul_mem_right _ I hparent
  · exact hearlier

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Pilot

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Pilot.raw_poly_eq
#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Pilot.normalized_row_mem
