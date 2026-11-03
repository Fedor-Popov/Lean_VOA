import VOA.DeligneAudit.LeviTypeA2CertFiniteBox
import VOA.DeligneAudit.DeligneFusionSl2Module

/-! A graded sl₂ box consequence: excessive lowering length vanishes. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

private theorem boxP_degree_le (m : ℕ) (f : ℕ →₀ ℕ)
    (hf : BoxP m f) : Finsupp.degree f ≤ m := by
  by_cases hzero : f = 0
  · subst f
    simp
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hzero
    have h := hf i hi
    omega

private theorem box_weight_first (f : ℕ →₀ ℕ) :
    (Finsupp.weight om f).1 = Finsupp.degree f := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
    Prod.fst_sum, om]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (F : ℕ → Module.End ℂ V)
  (hFF : ∀ i j, F i * F j = F j * F i)

/-- A homogeneous lowering polynomial of length greater than the local
Weyl weight kills the highest-weight vector. -/
theorem sl2_box_homogeneous_length_zero (y : V) (m : ℕ)
    (hk : ∀ r s, 1 ≤ r → m + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs F ^ r)) y = 0)
    (p : R) (n : ℕ × ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous om p n)
    (hn : m < n.1) : Sl2Weyl.evAlg F hFF p y = 0 := by
  have hspan := span_box_graded F hFF y m hk hp
  have hset : ∀ v : V,
      (∃ f, BoxP m f ∧ Finsupp.weight om f = n ∧
        v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y) → v = 0 := by
    intro v ⟨f, hf, hw, _⟩
    have hdegree := boxP_degree_le m f hf
    have hfirst := box_weight_first f
    have : n.1 = Finsupp.degree f := by rw [← hw]; exact hfirst
    omega
  have hle : Submodule.span ℂ {v : V | ∃ f, BoxP m f ∧
      Finsupp.weight om f = n ∧
      v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y} ≤ ⊥ := by
    rw [Submodule.span_le]
    intro v hv
    rw [hset v hv]
    exact Submodule.zero_mem _
  exact (Submodule.mem_bot ℂ).mp (hle hspan)

private noncomputable def zWord (l : List ℕ) : R := (l.map z).prod

private theorem zWord_hom : ∀ l : List ℕ,
    MvPolynomial.IsWeightedHomogeneous om (zWord l) (l.length, l.sum) := by
  intro l
  induction l with
  | nil =>
      simpa [zWord] using
        MvPolynomial.isWeightedHomogeneous_one ℂ om
  | cons s l ih =>
      have hz : MvPolynomial.IsWeightedHomogeneous om (z s) (1, s) :=
        MvPolynomial.isWeightedHomogeneous_X ℂ om s
      have hm := hz.mul ih
      simpa [zWord, Nat.add_comm] using hm

private theorem evAlg_zWord (l : List ℕ) :
    Sl2Weyl.evAlg F hFF (zWord l) = (l.map F).prod := by
  induction l with
  | nil => simp [zWord]
  | cons s l ih =>
      simp only [zWord, List.map_cons, List.prod_cons] at *
      rw [map_mul, Sl2Weyl.evAlg_z, ih]

include hFF in
/-- Any product of more than `m` lowering modes kills a local Weyl vector. -/
theorem sl2_box_word_length_zero (y : V) (m : ℕ)
    (hk : ∀ r s, 1 ≤ r → m + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs F ^ r)) y = 0)
    (l : List ℕ) (hl : m < l.length) :
    (l.map F).prod y = 0 := by
  have h := sl2_box_homogeneous_length_zero F hFF y m hk
    (zWord l) (l.length, l.sum) (zWord_hom l) hl
  simpa only [evAlg_zWord] using h

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.sl2_box_homogeneous_length_zero
#print axioms VOA.DeligneAudit.A3Sector.sl2_box_word_length_zero
