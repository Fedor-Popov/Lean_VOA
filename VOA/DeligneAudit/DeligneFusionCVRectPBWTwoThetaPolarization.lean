import VOA.DeligneAudit.DeligneFusionCVPolarization

/-!
# Two-factor polarization with a first descendant

If a current coefficient kills both `w` and its first `X` descendant,
and the second descendant vanishes, two commutators polarize that
coefficient into a two-`G` mixed coefficient. The premises are source
relations, not the target mixed relation or a PBW ideal inclusion.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWTwoTheta

open VOA.DeligneAudit.CVsl2
open VOA.DeligneAudit.A2.CVPolarization

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A source coefficient vanishing on the generator and its first
descendant gives its first polarized coefficient on the generator. -/
theorem mixedCoeff_one_zero_of_Q_on_successor
    (F G : ℕ → Module.End ℂ V) (X : Module.End ℂ V)
    (hXF : ∀ k, X * F k - F k * X = G k)
    (hXG : ∀ k, X * G k = G k * X)
    (hFG : ∀ k l, F k * G l = G l * F k)
    {w u : V} (hXw : X w = u) {r s : ℕ}
    (hQw : Q F (r + 1) s w = 0) (hQu : Q F (r + 1) s u = 0) :
    mixedCoeff G F 1 r s w = 0 := by
  have hmw : mixedCoeff G F 0 (r + 1) s w = 0 := by
    simpa only [mixedCoeff, pow_zero, one_mul, Q] using hQw
  have hmu : mixedCoeff G F 0 (r + 1) s u = 0 := by
    simpa only [mixedCoeff, pow_zero, one_mul, Q] using hQu
  have he := congrArg (fun T : Module.End ℂ V => T w)
    (mixedCoeff_commutator F G X hXF hXG hFG 0 r s)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    hmw, hXw, hmu, map_zero, sub_self] at he
  have hz : (r + 1) • mixedCoeff G F 1 r s w = 0 := he.symm
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at hz
  exact hz.resolve_left (by exact_mod_cast Nat.succ_ne_zero r)

/-- The actual two-commutator polarization step for a square-zero
first descendant. Only the two original source coefficients are used. -/
theorem mixedCoeff_two_zero_of_Q_on_successor
    (F G : ℕ → Module.End ℂ V) (X : Module.End ℂ V)
    (hXF : ∀ k, X * F k - F k * X = G k)
    (hXG : ∀ k, X * G k = G k * X)
    (hFG : ∀ k l, F k * G l = G l * F k)
    {w u : V} (hXw : X w = u) (hXu : X u = 0) {r s : ℕ}
    (hQw : Q F (r + 2) s w = 0) (hQu : Q F (r + 2) s u = 0) :
    mixedCoeff G F 2 r s w = 0 := by
  have hw1 : mixedCoeff G F 1 (r + 1) s w = 0 :=
    mixedCoeff_one_zero_of_Q_on_successor F G X hXF hXG hFG hXw hQw hQu
  have hu1 : mixedCoeff G F 1 (r + 1) s u = 0 :=
    mixedCoeff_zero_of_Q F G X hXF hXG hFG hXu hQu 1 (r + 1) (by omega)
  have he := congrArg (fun T : Module.End ℂ V => T w)
    (mixedCoeff_commutator F G X hXF hXG hFG 1 r s)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    hw1, hXw, hu1, map_zero, sub_self] at he
  have hz : (r + 1) • mixedCoeff G F 2 r s w = 0 := he.symm
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at hz
  exact hz.resolve_left (by exact_mod_cast Nat.succ_ne_zero r)

end

end VOA.DeligneAudit.A2.CVRectPBWTwoTheta

#print axioms VOA.DeligneAudit.A2.CVRectPBWTwoTheta.mixedCoeff_one_zero_of_Q_on_successor
#print axioms VOA.DeligneAudit.A2.CVRectPBWTwoTheta.mixedCoeff_two_zero_of_Q_on_successor
