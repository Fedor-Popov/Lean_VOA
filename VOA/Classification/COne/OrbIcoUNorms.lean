import VOA.Classification.COne.OrbIcoUVacuum74Norm
import VOA.Classification.COne.OrbIcoUVacuum76Norm
import VOA.Classification.COne.OrbIcoUSelf38Norm
import VOA.Classification.COne.OrbIcoUSelf40Norm

/-! Actual positive-form normalizations for the four relevant Virasoro tower levels.
These statements concern towers; the product-mode dual measurements remain separate. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoU
open VOA VertexOperatorAlgebra OrbSpan
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (A : VertexOperatorAlgebra V) (U : VirUnitaryForm A) (q : V)

theorem vacuum74_tower_norm (hc : A.centralCharge = 1)
    (hzero : A.L 0 q = (0 : ℂ) • q)
    (hpos : ∀ m : ℤ, 0 < m → A.L m q = 0) :
    U.form (((A.L (-2)) ^ 37) q) (((A.L (-2)) ^ 37) q) =
      (vacuum74Norm : ℂ) * U.form q q := by
  have hh := form_tower_pairWords A U q 1 0 (by simpa using hc)
    (by simpa using hzero) hpos 37
  rwa [vacuum74_pairing] at hh

theorem vacuum76_tower_norm (hc : A.centralCharge = 1)
    (hzero : A.L 0 q = (0 : ℂ) • q)
    (hpos : ∀ m : ℤ, 0 < m → A.L m q = 0) :
    U.form (((A.L (-2)) ^ 38) q) (((A.L (-2)) ^ 38) q) =
      (vacuum76Norm : ℂ) * U.form q q := by
  have hh := form_tower_pairWords A U q 1 0 (by simpa using hc)
    (by simpa using hzero) hpos 38
  rwa [vacuum76_pairing] at hh

theorem self38_tower_norm (hc : A.centralCharge = 1)
    (hzero : A.L 0 q = (36 : ℂ) • q)
    (hpos : ∀ m : ℤ, 0 < m → A.L m q = 0) :
    U.form (((A.L (-2)) ^ 19) q) (((A.L (-2)) ^ 19) q) =
      (self38Norm : ℂ) * U.form q q := by
  have hh := form_tower_pairWords A U q 1 36 (by simpa using hc)
    (by simpa using hzero) hpos 19
  rwa [self38_pairing] at hh

theorem self40_tower_norm (hc : A.centralCharge = 1)
    (hzero : A.L 0 q = (36 : ℂ) • q)
    (hpos : ∀ m : ℤ, 0 < m → A.L m q = 0) :
    U.form (((A.L (-2)) ^ 20) q) (((A.L (-2)) ^ 20) q) =
      (self40Norm : ℂ) * U.form q q := by
  have hh := form_tower_pairWords A U q 1 36 (by simpa using hc)
    (by simpa using hzero) hpos 20
  rwa [self40_pairing] at hh

end VOA.Classification.COne.OrbIcoU
