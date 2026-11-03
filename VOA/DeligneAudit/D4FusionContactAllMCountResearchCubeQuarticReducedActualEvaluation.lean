import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedSemantics
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticMomentCoefficients
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticSource

/-! Whole-current evaluation and the exact finite moments of the original
static quartic source rows. No coefficient tail or top jet is truncated. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

def actualJetTarget (m j : ℕ) (h : Fin 8) :
    PowerSeries (MvPolynomial (Vars m) ℂ) :=
  ((List.finRange 8).map fun c => channelWeight h c •
    (jetDerivative j (actualCurrent m c) *
      currentMap m (orbit ℂ 4 (2 - bit c 0) (2 - bit c 1) (2 - bit c 2)))).sum

def actualJetProduct (m : ℕ) (p : ProductSpec) :
    PowerSeries (MvPolynomial (Vars m) ℂ) :=
  jetDerivative p.a (currentMap m (orbit ℂ 2 p.x2 p.y2 p.z2)) *
    jetDerivative p.b (currentMap m (orbit ℂ 3 p.x3 p.y3 p.z3))

/-- The literal finite mode moments of the static sources constructed above. -/
def actualQuarticMoment (m j : ℕ) (h : Fin 8) : MvPolynomial (Vars m) ℂ :=
  ∑ c : Fin 8, channelWeight h c •
    ∑ k : Fin m, k.val.descFactorial j • quarticBlockSource m c k

theorem currentJetEvaluate_channelVar (m j : ℕ) (c : Fin 8) :
    currentJetEvaluate m (jetVarNat (8 * j + c.val)) =
      jetDerivative j (actualCurrent m c) := by
  have hc := c.isLt
  have hx : jetVarNat (8 * j + c.val) = MvPolynomial.X (c,j) := by
    unfold jetVarNat
    congr 1
    apply Prod.ext
    · apply Fin.ext
      change (8 * j + c.val) % 8 = c.val
      omega
    · change (8 * j + c.val) / 8 = j
      omega
  rw [hx,currentJetEvaluate,jetEvaluate_X]
  rfl

theorem currentJetEvaluate_jetTarget (m j : ℕ) (h : Fin 8) :
    currentJetEvaluate m (jetTarget j h) = actualJetTarget m j h := by
  simp only [jetTarget,actualJetTarget,map_list_sum,List.map_map,Function.comp_def,
    map_zsmul,map_mul,currentJetEvaluate_channelVar,currentJetEvaluate_base]

theorem currentJetEvaluate_jetProduct (m : ℕ) (p : ProductSpec) :
    currentJetEvaluate m (jetProduct p) = actualJetProduct m p := by
  simp only [jetProduct,actualJetProduct,map_mul,currentJetEvaluate_iterate_base,jetDerivative]

theorem quarticBlockAxes_bit : ∀ (c : Fin 8) (d : Fin 3),
    quarticBlockAxes c d = 2 - bit c d.val := by decide +kernel

private theorem sum_finRange {A : Type*} [AddCommMonoid A] (f : Fin 8 → A) :
    ((List.finRange 8).map f).sum = ∑ c : Fin 8, f c := by
  classical
  rw [← List.sum_toFinset f (List.nodup_finRange 8),List.toFinset_finRange]

/-- Every ordinary jet coefficient is the exact falling-factorial moment
of the original static quartic rows, including all small m and high jets. -/
theorem actualJetTarget_coeff_eq_moment (m j : ℕ) (h : Fin 8) :
    PowerSeries.coeff (2 * m - 3 - j) (actualJetTarget m j h) =
      actualQuarticMoment m j h := by
  simp only [actualJetTarget,map_list_sum,List.map_map,Function.comp_def,map_zsmul]
  rw [sum_finRange]
  simp only [actualQuarticMoment,coeff_jet_actualCurrent_mul_quintic,
    quarticBlockSource,quarticBlockAxes_bit]
  rfl

end
#print axioms currentJetEvaluate_jetTarget
#print axioms currentJetEvaluate_jetProduct
#print axioms actualJetTarget_coeff_eq_moment
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
