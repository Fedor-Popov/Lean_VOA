import VOA.DeligneAudit.DeligneFusionCVShifted
import VOA.DeligneAudit.DeligneFusionGarlandSl3

/-!
# Polarization of highest-root current relations

The raising mode `e₂(0)` differentiates a highest-root current into a
first-root current, and commutes with the latter. Applying it repeatedly
to a single vanishing current coefficient gives all polarized mixed
coefficients of the same total power and current degree.

The theorem uses only the one source coefficient being polarized. It
does not assume that the entire current series kills the vector, nor
does it prove a fusion dimension bound or a rectangular branching rule.
-/

namespace VOA.DeligneAudit.A2.CVPolarization

noncomputable section

section Ring

variable {A : Type*} [Ring A] {X Y Z : A}

/-- Moving an operator through a power with a central commutator. -/
theorem power_mul_operator (hXY : X * Y - Y * X = Z) (hYZ : Y * Z = Z * Y) :
    ∀ q : ℕ, Y ^ (q + 1) * X = X * Y ^ (q + 1) - (q + 1) • (Z * Y ^ q)
  | 0 => by rw [← hXY]; simp
  | q + 1 => by
      have ih := power_mul_operator hXY hYZ q
      have hYX : Y * X = X * Y - Z := by rw [← hXY]; abel
      calc
        Y ^ (q + 2) * X = Y * (Y ^ (q + 1) * X) := by
          rw [pow_succ' Y (q + 1), mul_assoc]
        _ = Y * (X * Y ^ (q + 1) - (q + 1) • (Z * Y ^ q)) := by rw [ih]
        _ = (Y * X) * Y ^ (q + 1) - (q + 1) • ((Y * Z) * Y ^ q) := by
          rw [mul_sub, mul_smul_comm, mul_assoc, mul_assoc]
        _ = (X * Y - Z) * Y ^ (q + 1) - (q + 1) • ((Z * Y) * Y ^ q) := by
          rw [hYX, hYZ]
        _ = X * Y ^ (q + 2) - (q + 2) • (Z * Y ^ (q + 1)) := by
          rw [pow_succ' Y (q + 1), mul_assoc Z Y, sub_mul, mul_assoc,
            ← pow_succ' Y (q + 1)]
          rw [show (q + 2) • (Z * Y ^ (q + 1)) =
              (q + 1) • (Z * Y ^ (q + 1)) + Z * Y ^ (q + 1) by rw [succ_nsmul]]
          rw [← pow_succ']
          abel

/-- A commutator differentiates the second factor of a mixed power. -/
theorem mixed_power_commutator (hXY : X * Y - Y * X = Z)
    (hXZ : X * Z = Z * X) (hYZ : Y * Z = Z * Y) (p q : ℕ) :
    X * (Z ^ p * Y ^ (q + 1)) - (Z ^ p * Y ^ (q + 1)) * X =
      (q + 1) • (Z ^ (p + 1) * Y ^ q) := by
  have hXZp : X * Z ^ p = Z ^ p * X := (show Commute X Z from hXZ).pow_right p
  have hpow : X * Y ^ (q + 1) - Y ^ (q + 1) * X =
      (q + 1) • (Z * Y ^ q) := by
    rw [power_mul_operator hXY hYZ q]
    abel
  calc
    X * (Z ^ p * Y ^ (q + 1)) - (Z ^ p * Y ^ (q + 1)) * X =
        (X * Z ^ p) * Y ^ (q + 1) - Z ^ p * (Y ^ (q + 1) * X) := by
      noncomm_ring
    _ = Z ^ p * (X * Y ^ (q + 1) - Y ^ (q + 1) * X) := by
      rw [hXZp]
      noncomm_ring
    _ = (q + 1) • (Z ^ (p + 1) * Y ^ q) := by
      rw [hpow, mul_smul_comm, ← mul_assoc, ← pow_succ]

end Ring

section CurrentSeries

open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.Garland

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The mixed coefficient with `p` polarized and `q` original current factors. -/
def mixedCoeff (G F : ℕ → Module.End ℂ V) (p q s : ℕ) : Module.End ℂ V :=
  PowerSeries.coeff s (Fs G ^ p * Fs F ^ q)

/-- The current coefficient version of the mixed-power commutator identity. -/
theorem mixedCoeff_commutator (F G : ℕ → Module.End ℂ V) (X : Module.End ℂ V)
    (hXF : ∀ k, X * F k - F k * X = G k)
    (hXG : ∀ k, X * G k = G k * X)
    (hFG : ∀ k l, F k * G l = G l * F k) (p q s : ℕ) :
    X * mixedCoeff G F p (q + 1) s - mixedCoeff G F p (q + 1) s * X =
      (q + 1) • mixedCoeff G F (p + 1) q s := by
  have hXY : PowerSeries.C X * Fs F - Fs F * PowerSeries.C X = Fs G := by
    apply PowerSeries.ext
    intro k
    simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      Fs, PowerSeries.coeff_mk]
    exact hXF k
  have hXZ : PowerSeries.C X * Fs G = Fs G * PowerSeries.C X := by
    apply PowerSeries.ext
    intro k
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      Fs, PowerSeries.coeff_mk]
    exact hXG k
  have hYZ : Fs F * Fs G = Fs G * Fs F := current_series_commute hFG
  have h := congrArg (PowerSeries.coeff s) (mixed_power_commutator hXY hXZ hYZ p q)
  simpa only [map_sub, map_nsmul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_C, mixedCoeff] using h

/-- Polarize a single vanishing coefficient; all powers have the same total
power and current degree as that source coefficient. -/
theorem mixedCoeff_zero_of_Q (F G : ℕ → Module.End ℂ V) (X : Module.End ℂ V)
    (hXF : ∀ k, X * F k - F k * X = G k)
    (hXG : ∀ k, X * G k = G k * X)
    (hFG : ∀ k l, F k * G l = G l * F k)
    {w : V} (hXw : X w = 0) {r s : ℕ} (hQ : Q F r s w = 0) :
    ∀ p q, p + q = r → mixedCoeff G F p q s w = 0 := by
  intro p
  induction p with
  | zero =>
      intro q hq
      have hrq : r = q := by omega
      rw [hrq] at hQ
      simpa only [mixedCoeff, pow_zero, one_mul, Q] using hQ
  | succ p ih =>
      intro q hpq
      have hprev : mixedCoeff G F p (q + 1) s w = 0 := ih (q + 1) (by omega)
      have h := congrArg (fun T : Module.End ℂ V => T w)
        (mixedCoeff_commutator F G X hXF hXG hFG p q s)
      simp only [LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply, hprev, hXw, map_zero, sub_self] at h
      have hz : (q + 1) • (mixedCoeff G F (p + 1) q s w) = 0 := h.symm
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at hz
      exact hz.resolve_left (by exact_mod_cast Nat.succ_ne_zero q)

end CurrentSeries

section A2

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- In an actual A₂ current module, `e₂(0)` polarizes a highest-root coefficient
into any mixed first-root / highest-root coefficient of the same total power. -/
theorem theta_polarize (R : CurrentModule bracketTable V) {w : V}
    (he2 : R.op 1 0 w = 0) {r s : ℕ} (hQ : Q (R.op 5) r s w = 0)
    (p q : ℕ) (hpq : p + q = r) : mixedCoeff (R.op 3) (R.op 5) p q s w = 0 := by
  apply mixedCoeff_zero_of_Q (R.op 5) (R.op 3) (R.op 1 0) ?_ ?_ ?_ he2 hQ p q hpq
  · intro k
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
  · intro k
    rw [← sub_eq_zero, op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
  · intro k l
    rw [← sub_eq_zero, op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]

/-- The mixed CV coefficient relations obtained from a highest-root partition. -/
theorem theta_cvrel_mixed (R : CurrentModule bracketTable V) {w : V} {ξ : List ℕ}
    (he2 : R.op 1 0 w = 0) (hCV : CVRel (R.op 5) ξ w)
    (p q s k : ℕ) (hr : 1 ≤ p + q)
    (hreg : 1 + (p + q) * k + T k ξ ≤ s + (p + q)) :
    mixedCoeff (R.op 3) (R.op 5) p q s w = 0 :=
  theta_polarize R he2 (hCV (p + q) s k hr hreg) p q rfl

end A2

end

end VOA.DeligneAudit.A2.CVPolarization

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.CVPolarization.mixedCoeff_zero_of_Q
#print axioms VOA.DeligneAudit.A2.CVPolarization.theta_polarize
#print axioms VOA.DeligneAudit.A2.CVPolarization.theta_cvrel_mixed
end AxiomAudit
