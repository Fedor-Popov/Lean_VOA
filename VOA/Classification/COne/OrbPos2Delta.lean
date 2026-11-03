import VOA.Examples.LiDelta
import VOA.Examples.HeisenbergConformal
import VOA.Classification.COne.OrbPos2Weights

/-!
# The conformal-vector part of the existing Li substitution

At root normalization two, the actual Heisenberg conformal vector is `X₀²/4`.
The existing substitution sends `X₀` to `X₀ - 2t w`, so its conformal-vector
image has coefficients `ω`, `-t α`, and `t² 1`. These are precisely the terms
of `L₀ - t α(0) + t²`. This is a calculation in the existing Fock algebra;
extending the operator across all lattice charges and proving the twisted
Jacobi identity and inverse classification are still separate obligations.
-/

namespace VOA.Classification.COne.OrbPos2
open VOA.Heisenberg MvPolynomial

/-- Exact Δ-image of the actual root-normalized Heisenberg conformal vector. -/
theorem deltaSub_root_conformal (t : ℂ) :
    deltaSub 2 (-t) (ω 2) = includeW (ω 2) -
      t • ((X 0 : FockW) * MvPolynomial.C Polynomial.X) +
      t ^ 2 • MvPolynomial.C (Polynomial.X ^ 2) := by
  simp only [ω, osc_neg_one_sq_vacuum, map_smul, map_pow, deltaSub_X,
    includeW_X, VOA.Heisenberg.deltaCoeff]
  norm_num
  simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) FockW,
    MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq,
    map_pow, map_ofNat]
  have hc : (MvPolynomial.C (Polynomial.C (1 / 4 : ℂ)) : FockW) * 4 = 1 := by
    calc
      _ = MvPolynomial.C (Polynomial.C ((1 / 4 : ℂ) * 4)) := by
        simp only [map_mul, map_ofNat]
      _ = 1 := by norm_num
  linear_combination
    (-(X 0 : FockW) * MvPolynomial.C (Polynomial.C t) * MvPolynomial.C Polynomial.X +
      MvPolynomial.C (Polynomial.C t) ^ 2 * MvPolynomial.C Polynomial.X ^ 2) * hc

end VOA.Classification.COne.OrbPos2
