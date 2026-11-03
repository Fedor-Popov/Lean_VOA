import VOA.DeligneAudit.LeviTypeA2CertGradedDefectEval
import VOA.DeligneAudit.LeviTypeA2CertGradedKey
import VOA.DeligneAudit.DeligneFusionCLAssembly

/-! Convert an evaluated Garland product into a positional box target. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A monomial F₂ multiplier is an ordinary sorted F₂ word. -/
theorem a2_evAlg_monomial_word (F : ℕ → Module.End ℂ V)
    (hFF : ∀ i j, F i * F j = F j * F i) (f : ℕ →₀ ℕ) :
    Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) =
      ((VOA.DeligneAudit.CLAssembly.lst f).map F).prod := by
  rw [VOA.DeligneAudit.CLAssembly.monomial_eq_mono]
  exact VOA.DeligneAudit.CLAssembly.evAlg_mono F hFF _

/-- The mode word commutes with every F₂ mode. -/
private theorem a2_word_comm (F : ℕ → Module.End ℂ V)
    (hFF : ∀ i j, F i * F j = F j * F i)
    (ys : List ℕ) (i : ℕ) :
    (ys.map F).prod * F i = F i * (ys.map F).prod := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        (F y * (ys.map F).prod) * F i =
            F y * ((ys.map F).prod * F i) := mul_assoc _ _ _
        _ = F y * (F i * (ys.map F).prod) := by rw [ih]
        _ = F i * (F y * (ys.map F).prod) := by
          rw [← mul_assoc, ← hFF i y, mul_assoc]

/-- A monomial multiple of a Garland generator is exactly the defect
term handled by the graded F₂ conversion lemma. -/
theorem a2_graded_defect_as_boxTarget
    (a b : ℕ → Module.End ℂ V)
    (hbb : ∀ i j, b i * b j = b j * b i)
    (xs : List ℕ) (f : ℕ →₀ ℕ) (k s : ℕ) (w : V) :
    (aWord a xs * Sl2Weyl.evAlg b hbb
      (MvPolynomial.monomial f 1 * xx k s)) w =
      boxTarget a b k s xs (VOA.DeligneAudit.CLAssembly.lst f) 1 w := by
  let ys := VOA.DeligneAudit.CLAssembly.lst f
  have hc := spectator_comm_coeff b ((ys.map b).prod)
    (a2_word_comm b hbb ys) k s
  rw [map_mul, a2_evAlg_monomial_word b hbb f,
    Sl2Weyl.evAlg_xx, show VOA.DeligneAudit.Garland.Fs b = fCurrent b from rfl]
  calc
    (aWord a xs * ((ys.map b).prod * PowerSeries.coeff s (fCurrent b ^ k))) w =
        (aWord a xs * (PowerSeries.coeff s (fCurrent b ^ k) *
          (ys.map b).prod)) w := by rw [hc]
    _ = boxTarget a b k s xs ys 1 w := by
      simp [boxTarget, mul_assoc]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_evAlg_monomial_word
#print axioms VOA.DeligneAudit.A3Sector.a2_graded_defect_as_boxTarget
