import VOA.DeligneAudit.D4FusionContactAllMCurrent
import VOA.DeligneAudit.D4FusionContactPolynomialCutoff

/-!
# All-m grouped differential ideal and its actual source map

The generators are whole current coefficients. Arbitrary iterated
current derivations and polynomial multipliers are included. This is
an actual ideal inside the PBW vector annihilator, not a presentation
equality. Its sharp finite count remains a separate obligation.
-/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllM

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

def seedColor (b : Bool) : Fin 9 := if b then 8 else 0

def seedThreshold (m : ℕ) (b : Bool) : ℕ := if b then 2 * m else m

/-- Both power and current degree vary. Theta's sharper linear
truncation is already built into the finite current variables. -/
abbrev SeedIndex (m : ℕ) :=
  {x : Bool × ℕ × ℕ // 1 ≤ x.2.1 ∧ seedThreshold m x.1 < x.2.1 + x.2.2}

def seedPoly (m : ℕ) (j : SeedIndex m) : MvPolynomial (Vars m) ℂ :=
  PowerSeries.coeff j.val.2.2 (current m (seedColor j.val.1) ^ j.val.2.1)

abbrev DerivIndex (m : ℕ) := (Fin 10 × Fin m) ⊕ (Fin 8 × Fin m)

def candidateDeriv (m : ℕ) : DerivIndex m →
    Derivation ℂ (MvPolynomial (Vars m) ℂ) (MvPolynomial (Vars m) ℂ)
  | .inl x => g0Deriv m x.1 x.2.val
  | .inr x => eDeriv m x.1 x.2.val

def derivWord (m : ℕ) : List (DerivIndex m) →
    MvPolynomial (Vars m) ℂ → MvPolynomial (Vars m) ℂ
  | [], p => p
  | d :: l, p => candidateDeriv m d (derivWord m l p)

def candidateIdeal (m : ℕ) : Ideal (MvPolynomial (Vars m) ℂ) :=
  Ideal.span (Set.range fun x : List (DerivIndex m) × SeedIndex m =>
    derivWord m x.1 (seedPoly m x.2))

theorem derivWord_seed_mem_candidate (m : ℕ) (l : List (DerivIndex m)) (j : SeedIndex m) :
    derivWord m l (seedPoly m j) ∈ candidateIdeal m := Ideal.subset_span ⟨(l, j), rfl⟩

theorem seed_mem_candidate (m : ℕ) (j : SeedIndex m) :
    seedPoly m j ∈ candidateIdeal m := derivWord_seed_mem_candidate m [] j

/-- Stability is proved for the whole ideal, including every multiplier. -/
theorem candidateIdeal_deriv (m : ℕ) (d : DerivIndex m) {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ candidateIdeal m) : candidateDeriv m d p ∈ candidateIdeal m := by
  change p ∈ Submodule.span (MvPolynomial (Vars m) ℂ) _ at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨⟨l, j⟩, rfl⟩ := hp
      exact derivWord_seed_mem_candidate m (d :: l) j
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add p q hp hq ihp ihq => rw [map_add]; exact Ideal.add_mem _ ihp ihq
  | smul a p hp ih =>
      change candidateDeriv m d (a * p) ∈ candidateIdeal m
      rw [(candidateDeriv m d).leibniz]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ hp)

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V} {m : ℕ}

theorem source_seed_mem_ann (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m)
    (j : SeedIndex m) : seedPoly m j ∈ annIdeal R w (modeLetter m) := by
  obtain ⟨⟨b, r, s⟩, hr, hs⟩ := j
  cases b with
  | false => exact source_simple_coefficient_mem_ann hm h r s hr hs
  | true => exact source_center_coefficient_mem_ann hm h r s hr hs

theorem source_candidate_deriv_closed (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m)
    (d : DerivIndex m) :
    ∀ p ∈ annIdeal R w (modeLetter m), candidateDeriv m d p ∈ annIdeal R w (modeLetter m) := by
  cases d with
  | inl x => exact source_g0_ann_closed hm h x.1 x.2.val
  | inr x => exact source_e_ann_closed hm h x.1 x.2.val

theorem source_derivWord_seed_mem_ann (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m)
    (l : List (DerivIndex m)) (j : SeedIndex m) :
    derivWord m l (seedPoly m j) ∈ annIdeal R w (modeLetter m) := by
  induction l with
  | nil => exact source_seed_mem_ann hm h j
  | cons d l ih => exact source_candidate_deriv_closed hm h d _ ih

/-- Actual all-m source inclusion; neither equality nor a count is assumed. -/
theorem source_candidateIdeal_le_ann (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m) :
    candidateIdeal m ≤ annIdeal R w (modeLetter m) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨l, j⟩, rfl⟩
  exact source_derivWord_seed_mem_ann hm h l j

/-- The separately proved all-current length cutoff is included explicitly. -/
def modelIdeal (m : ℕ) : Ideal (MvPolynomial (Vars m) ℂ) :=
  candidateIdeal m ⊔ highWordIdeal m

abbrev Model (m : ℕ) := MvPolynomial (Vars m) ℂ ⧸ (modelIdeal m).restrictScalars ℂ

theorem source_modelIdeal_le_ann (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m) :
    modelIdeal m ≤ annIdeal R w (modeLetter m) :=
  sup_le (source_candidateIdeal_le_ann hm h) (source_highWordIdeal_le_ann h)

def modelMap (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m) : Model m →ₗ[ℂ] Gr R w :=
  polyQuotientMap R w (modeLetter m) (modelIdeal m) (source_modelIdeal_le_ann hm h)

theorem modelMap_surjective (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m) :
    Function.Surjective (modelMap hm h) := by
  apply polyQuotientMap_surjective
  apply modeLetter_cover
  intro i q hq
  exact localWeyl_high_kills hm h (radIndex i) q hq

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllM

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllM.candidateIdeal_deriv
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllM.source_candidateIdeal_le_ann
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllM.source_modelIdeal_le_ann
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllM.modelMap_surjective
