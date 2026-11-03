import VOA.DeligneAudit.DeligneFusionCVRectFilteredDimension

/-!
# Finite polynomial realization of the actual PBW graded cyclic module

Negative-current symbols commute by the actual current bracket, and source
high-mode truncations kill the entire graded cyclic module. These facts give
an actual surjection from a finite polynomial ring. Any subsequently proved
coefficient ideal inclusion can therefore transfer its finite quotient bound
back to the original negative-current cyclic module.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

section Evaluation

variable {ι : Type} (letter : ι → NegLtr)

def polyOp (i : ι) : Module.End ℂ (Gr R w) :=
  grOp R w (letter i).1 (letter i).2

theorem polyOp_commute (i j : ι) :
    polyOp R w letter i * polyOp R w letter j =
      polyOp R w letter j * polyOp R w letter i :=
  grOp_commute R w _ _ _ _

abbrev PolyAlg := Algebra.adjoin ℂ (Set.range (polyOp R w letter))

def polyAlg : MvPolynomial ι ℂ →ₐ[ℂ] Module.End ℂ (Gr R w) :=
  letI : CommRing (PolyAlg R w letter) := Algebra.adjoinCommRingOfComm ℂ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact polyOp_commute R w letter i j)
  (PolyAlg R w letter).val.comp
    (MvPolynomial.aeval fun i => ⟨polyOp R w letter i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)

theorem polyAlg_X (i : ι) : polyAlg R w letter (MvPolynomial.X i) = polyOp R w letter i := by
  simp [polyAlg]

def polyEval : MvPolynomial ι ℂ →ₗ[ℂ] Gr R w :=
  (LinearMap.applyₗ (grGenerator R w)).comp (polyAlg R w letter).toLinearMap

theorem polyEval_one : polyEval R w letter 1 = grGenerator R w := by
  change (polyAlg R w letter 1) (grGenerator R w) = _
  rw [map_one]
  rfl

theorem polyEval_X_mul (i : ι) (p : MvPolynomial ι ℂ) :
    polyEval R w letter (MvPolynomial.X i * p) =
      grOp R w (letter i).1 (letter i).2 (polyEval R w letter p) := by
  change (polyAlg R w letter (MvPolynomial.X i * p)) (grGenerator R w) = _
  rw [map_mul, polyAlg_X, Module.End.mul_apply]
  rfl

/-- The finite set of letters covers every source current that does not kill
the cyclic generator. This premise is supplied by actual source truncations. -/
theorem polyEval_surjective
    (hcover : ∀ a r, (∃ i, letter i = (a, r)) ∨ R.op (negRoot a) r w = 0) :
    Function.Surjective (polyEval R w letter) := by
  have hword : ∀ l : List NegLtr, grWord R w l ∈ LinearMap.range (polyEval R w letter) := by
    intro l
    induction l with
    | nil => exact ⟨1, polyEval_one R w letter⟩
    | cons x l ih =>
        obtain ⟨p, hp⟩ := ih
        rcases hcover x.1 x.2 with ⟨i, hi⟩ | hk
        · refine ⟨MvPolynomial.X i * p, ?_⟩
          rw [polyEval_X_mul, hi, hp, grOp_grWord]
        · have hz := grOp_zero_of_source_zero R w x.1 x.2 hk
          refine ⟨0, ?_⟩
          rw [map_zero, ← grOp_grWord, hz]
          rfl
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← grWord_span_top R w]
  exact Submodule.span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hword l)

/-- A proved ideal inclusion gives an actual surjection of vector-space
quotients. It does not assert any unproved coefficient relation. -/
def polyQuotientMap (I : Ideal (MvPolynomial ι ℂ))
    (hI : (I.restrictScalars ℂ) ≤ LinearMap.ker (polyEval R w letter)) :
    (MvPolynomial ι ℂ ⧸ (I.restrictScalars ℂ)) →ₗ[ℂ] Gr R w :=
  (I.restrictScalars ℂ).liftQ (polyEval R w letter) hI

theorem polyQuotientMap_surjective (I : Ideal (MvPolynomial ι ℂ))
    (hI : (I.restrictScalars ℂ) ≤ LinearMap.ker (polyEval R w letter))
    (hcover : ∀ a r, (∃ i, letter i = (a, r)) ∨ R.op (negRoot a) r w = 0) :
    Function.Surjective (polyQuotientMap R w letter I hI) := by
  intro x
  obtain ⟨p, hp⟩ := polyEval_surjective R w letter hcover x
  exact ⟨(I.restrictScalars ℂ).mkQ p, hp⟩

theorem negativeCyclic_bound_of_polynomial (I : Ideal (MvPolynomial ι ℂ))
    (hI : (I.restrictScalars ℂ) ≤ LinearMap.ker (polyEval R w letter))
    (hcover : ∀ a r, (∃ i, letter i = (a, r)) ∨ R.op (negRoot a) r w = 0)
    [FiniteDimensional ℂ (MvPolynomial ι ℂ ⧸ (I.restrictScalars ℂ))] :
    FiniteDimensional ℂ (negativeCyclic R w) ∧
      Module.finrank ℂ (negativeCyclic R w) ≤
        Module.finrank ℂ (MvPolynomial ι ℂ ⧸ (I.restrictScalars ℂ)) := by
  have hs := polyQuotientMap_surjective R w letter I hI hcover
  haveI := Module.Finite.of_surjective (polyQuotientMap R w letter I hI) hs
  obtain ⟨hFD, hdim⟩ := negativeCyclic_bound R w
  exact ⟨hFD, hdim.trans (LinearMap.finrank_le_finrank_of_surjective hs)⟩

end Evaluation

/-- Canonical variables: first-root, highest-root, second-root, with right
association matching the three-color polynomial count. -/
abbrev Vars (Nx Ny Nz : ℕ) := Fin Nx ⊕ (Fin Ny ⊕ Fin Nz)

/-- Direct source-mode evaluation for STAR's reversed polynomial currents:
the polynomial reversal is already in the current's exponent, so its variable
with index i acts by the actual current mode i. -/
def modeLetter (Nx Ny Nz : ℕ) : Vars Nx Ny Nz → NegLtr
  | Sum.inl i => (0, i.1)
  | Sum.inr (Sum.inl i) => (1, i.1)
  | Sum.inr (Sum.inr i) => (2, i.1)

theorem modeLetter_cover (Nx Ny Nz : ℕ)
    (hx : ∀ r, Nx ≤ r → R.op 3 r w = 0)
    (hy : ∀ r, Ny ≤ r → R.op 5 r w = 0)
    (hz : ∀ r, Nz ≤ r → R.op 4 r w = 0) :
    ∀ a r, (∃ i, modeLetter Nx Ny Nz i = (a, r)) ∨
      R.op (negRoot a) r w = 0 := by
  intro a r
  fin_cases a
  · by_cases h : r < Nx
    · exact Or.inl ⟨Sum.inl ⟨r, h⟩, rfl⟩
    · exact Or.inr (hx r (by omega))
  · by_cases h : r < Ny
    · exact Or.inl ⟨Sum.inr (Sum.inl ⟨r, h⟩), rfl⟩
    · exact Or.inr (hy r (by omega))
  · by_cases h : r < Nz
    · exact Or.inl ⟨Sum.inr (Sum.inr ⟨r, h⟩), rfl⟩
    · exact Or.inr (hz r (by omega))

/-- An optional variable permutation, separate from the direct mode map used
with STAR's reversed currents. -/
def reversedLetter (Nx Ny Nz : ℕ) : Vars Nx Ny Nz → NegLtr
  | Sum.inl i => (0, Nx - 1 - i.1)
  | Sum.inr (Sum.inl i) => (1, Ny - 1 - i.1)
  | Sum.inr (Sum.inr i) => (2, Nz - 1 - i.1)

theorem reversedLetter_cover (Nx Ny Nz : ℕ)
    (hx : ∀ r, Nx ≤ r → R.op 3 r w = 0)
    (hy : ∀ r, Ny ≤ r → R.op 5 r w = 0)
    (hz : ∀ r, Nz ≤ r → R.op 4 r w = 0) :
    ∀ a r, (∃ i, reversedLetter Nx Ny Nz i = (a, r)) ∨
      R.op (negRoot a) r w = 0 := by
  intro a r
  fin_cases a
  · by_cases h : r < Nx
    · left
      refine ⟨Sum.inl ⟨Nx - 1 - r, by omega⟩, ?_⟩
      apply Prod.ext
      · rfl
      · change Nx - 1 - (Nx - 1 - r) = r
        omega
    · right; exact hx r (by omega)
  · by_cases h : r < Ny
    · left
      refine ⟨Sum.inr (Sum.inl ⟨Ny - 1 - r, by omega⟩), ?_⟩
      apply Prod.ext
      · rfl
      · change Ny - 1 - (Ny - 1 - r) = r
        omega
    · right; exact hy r (by omega)
  · by_cases h : r < Nz
    · left
      refine ⟨Sum.inr (Sum.inr ⟨Nz - 1 - r, by omega⟩), ?_⟩
      apply Prod.ext
      · rfl
      · change Nz - 1 - (Nz - 1 - r) = r
        omega
    · right; exact hz r (by omega)

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.polyEval_surjective
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.negativeCyclic_bound_of_polynomial
