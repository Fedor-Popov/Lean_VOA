import VOA.DeligneAudit.D4FusionContactOperators
import VOA.DeligneAudit.D4FusionContactHighestRootTable
import VOA.DeligneAudit.DeligneFusionCLFilt

/-! # Sharp center-cube nilpotence from actual highest-root sl₂ data -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V)

def highestE : Module.End ℂ V := -R.op 15 0

def highestH : Module.End ℂ V :=
  R.op 0 0 + R.op 1 0 + R.op 1 0 + R.op 2 0 + R.op 3 0

private theorem comm_end (a b : Fin 28) :
    R.op a 0 * R.op b 0 - R.op b 0 * R.op a 0 =
      ∑ c : Fin 28, contactF a b c • R.op c 0 := by
  ext v
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] using R.comm a b 0 0 v

theorem highest_EF : highestE R * center R - center R * highestE R = highestH R := by
  have hs : (∑ c : Fin 28, contactF 15 27 c • R.op c 0) = -highestH R := by
    simp only [highest_root_ef, add_smul, ite_smul, zero_smul,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      neg_smul, one_smul, highestH]
    abel
  calc
    highestE R * center R - center R * highestE R =
        -(R.op 15 0 * R.op 27 0 - R.op 27 0 * R.op 15 0) := by
      dsimp only [highestE, center]
      noncomm_ring
    _ = highestH R := by rw [comm_end, hs, neg_neg]

theorem highest_HF : highestH R * center R - center R * highestH R =
    (-2 : ℂ) • center R := by
  have he : highestH R * center R - center R * highestH R =
      (R.op 0 0 * R.op 27 0 - R.op 27 0 * R.op 0 0) +
      (R.op 1 0 * R.op 27 0 - R.op 27 0 * R.op 1 0) +
      (R.op 1 0 * R.op 27 0 - R.op 27 0 * R.op 1 0) +
      (R.op 2 0 * R.op 27 0 - R.op 27 0 * R.op 2 0) +
      (R.op 3 0 * R.op 27 0 - R.op 27 0 * R.op 3 0) := by
    dsimp only [highestH, center]
    noncomm_ring
  rw [he]
  calc
    _ = ∑ c : Fin 28,
        (contactF 0 27 c + contactF 1 27 c + contactF 1 27 c +
          contactF 2 27 c + contactF 3 27 c) • R.op c 0 := by
      simp only [comm_end, add_smul, Finset.sum_add_distrib]
    _ = (-2 : ℂ) • center R := by
      simp only [highest_root_hf, ite_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, center]

variable {R} {w : V}

/-- The source relation has sharp exponent three. Local nilpotence
of the center is later supplied by the already proved D₄ finite table;
no source finite-dimensionality premise is required. -/
theorem center_cube_of_known (h : HighestRel R w 1)
    (hknown : ∃ N, (center R ^ N) w = 0) : (center R ^ 3) w = 0 := by
  obtain ⟨N, hN⟩ := hknown
  have hE : highestE R w = 0 := by
    change -R.op 15 0 w = 0
    rw [h.raising 15 (by decide) 0, neg_zero]
  have h0 : R.op 0 0 w = 0 := by simpa using h.cartan_zero 0 (by decide)
  have h1 : R.op 1 0 w = w := by simpa using h.cartan_zero 1 (by decide)
  have h2 : R.op 2 0 w = 0 := by simpa using h.cartan_zero 2 (by decide)
  have h3 : R.op 3 0 w = 0 := by simpa using h.cartan_zero 3 (by decide)
  have hH : highestH R w = ((2 : ℤ) : ℂ) • w := by
    simp only [highestH, LinearMap.add_apply, h0, h1, h2, h3, zero_add, add_zero,
      Int.cast_ofNat, two_smul ℂ w]
  have hEF : ∀ v : V, highestE R (center R v) - center R (highestE R v) = highestH R v := by
    intro v
    exact congrArg (fun T : Module.End ℂ V => T v) (highest_EF R)
  have hHF : ∀ v : V, highestH R (center R v) - center R (highestH R v) =
      (-2 : ℂ) • center R v := by
    intro v
    exact congrArg (fun T : Module.End ℂ V => T v) (highest_HF R)
  have hk : (center R)^[N] w = 0 := by simpa only [Module.End.pow_apply] using hN
  have hs := (VOA.DeligneAudit.CLFilt.hw_pow (highestE R) (center R) (highestH R)
    hEF hHF hE hH N hk).2 (by norm_num : 0 ≤ (2 : ℤ))
  simpa only [Module.End.pow_apply] using hs

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.center_cube_of_known
