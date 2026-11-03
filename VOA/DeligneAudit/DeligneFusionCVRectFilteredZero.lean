import VOA.DeligneAudit.DeligneFusionCVRectFilteredLeading
import VOA.DeligneAudit.DeligneFusionCVRectCommutative
import VOA.DeligneAudit.DeligneFusionCVCrossRoot

/-!
# Actual mixed PBW leading relations with no highest-root factors

The two simple CV coefficient cutoffs suffice for this case. Their symbols
commute on the actual graded cyclic module, so every out-of-region convolution
term kills the generator. Exactness of length symbols then gives the actual
source relation modulo shorter words.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVRectCommutative

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Pairwise commuting current coefficients give pairwise commuting power
coefficients, without an ambient commutative endomorphism ring. -/
theorem Q_commute_of_modes (F G : ℕ → Module.End ℂ V)
    (hFG : ∀ i j, F i * G j = G j * F i) (p s r t : ℕ) :
    Q F p s * Q G r t = Q G r t * Q F p s := by
  have hsingle : ∀ j v, G j (Q F p s v) = Q F p s (G j v) := by
    intro j v
    exact CVCrossRoot.Q_commute_on F (G j) ⊤ (fun _ _ _ => Submodule.mem_top)
      (fun i x _ => congrArg (fun T : Module.End ℂ V => T x) (hFG i j).symm)
      p s v Submodule.mem_top
  apply LinearMap.ext
  intro v
  exact CVCrossRoot.Q_commute_on G (Q F p s) ⊤ (fun _ _ _ => Submodule.mem_top)
    (fun j x _ => (hsingle j x).symm) r t v Submodule.mem_top

theorem part_Q_zero_of_clipped (F : ℕ → Module.End ℂ V) {w : V} {r n e : ℕ}
    (hCV : CVRel F (parts r n e) w) (p s : ℕ)
    (hs : clippedSum (parts r n e) p < s + p) : Q F p s w = 0 := by
  by_cases hp : p = 0
  · subst p
    have hs0 : 0 < s := by simpa [clippedSum] using hs
    simp [Q, hs0.ne']
  · obtain ⟨k, hk⟩ := parts_region_optimizer r n e p (by omega)
    exact hCV p s k (by omega) (by omega)

variable (R : CurrentModule bracketTable V) (w : V)

theorem Q_symbol (a : Fin 3) (p s : ℕ) :
    ((Q (grOp R w a) p s (grGenerator R w)) : AmbientGr R w) =
      symbol R w p (Q (R.op (negRoot a)) p s w) := by
  have hh := currentProduct_symbol R w (List.replicate p a) s
  simpa only [currentProduct_replicate, List.length_replicate, Q, Garland.Fs] using hh

theorem gradedQ_zero_of_source (a : Fin 3) (p s : ℕ)
    (hQ : Q (R.op (negRoot a)) p s w = 0) :
    Q (grOp R w a) p s (grGenerator R w) = 0 := by
  apply Subtype.ext
  rw [Q_symbol, hQ, map_zero]
  rfl

variable {R w}

/-- The q=0 three-color relation, proved from the actual two simple-root CV
relations. The original simple lowering currents need not commute. -/
theorem orderedCoeff_zero_theta_mem {ε ν ϱ : Weight} (h : CV3Rel R w ε ν ϱ 0)
    (p r s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 ε.1) p + clippedSum (parts ϱ.2 ν.2 ε.2) r <
      s + (p + r)) : orderedCoeff R w p 0 r s ∈ Pbelow R w (p + r) := by
  apply (orderedCoeff_mem_iff_zero R w p 0 r s).mpr
  simp only [gradedOrderedCoeff, pow_zero, mul_one]
  rw [PowerSeries.coeff_mul, LinearMap.coe_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hij' : i + j = s := Finset.mem_antidiagonal.mp hij
  change Q (grOp R w 0) p i (Q (grOp R w 2) r j (grGenerator R w)) = 0
  by_cases hZ : clippedSum (parts ϱ.2 ν.2 ε.2) r < j + r
  · have hz := part_Q_zero_of_clipped (R.op 4)
      (by simpa only [Nat.add_zero] using h.second) r j hZ
    rw [gradedQ_zero_of_source R w 2 r j hz, map_zero]
  · have hX : clippedSum (parts ϱ.1 ν.1 ε.1) p < i + p := by omega
    have hx := part_Q_zero_of_clipped (R.op 3)
      (by simpa only [Nat.add_zero] using h.first) p i hX
    rw [← Module.End.mul_apply,
      Q_commute_of_modes (grOp R w 0) (grOp R w 2)
        (fun a b => grOp_commute R w 0 2 a b) p i r j,
      Module.End.mul_apply, gradedQ_zero_of_source R w 0 p i hx, map_zero]

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.orderedCoeff_zero_theta_mem
