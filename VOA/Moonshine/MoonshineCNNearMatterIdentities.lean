import VOA.Moonshine.MoonshineCNNearConsequences
import VOA.Moonshine.MoonshineCNTensorRealization

/-! The ordinary mode identities on the actual Lorentzian and moonshine matter algebras. -/

namespace VOA.Moonshine.ConwayNorton
open Module (End)
open scoped BigOperators

/-- The commutator formula on the constructed near-VOA. -/
theorem moonshineMatter_commutator (u v : moonshineMatterSpace) (m n : ℤ) :
    ∃ N : ℕ, ⁅mode (moonshineMatterNearVOA.Y u) m, mode (moonshineMatterNearVOA.Y v) n⁆ =
      ∑ j : Fin N, gBinom m (j : ℕ) •
        mode (moonshineMatterNearVOA.Y (moonshineMatterNearVOA.smul u (j : ℕ) v)) (m + n - (j : ℕ)) :=
  moonshineMatterNearVOA.mode_commutator_lie u v m n

/-- Borcherds identity for all integer mode indices. -/
theorem moonshineMatter_jacobi (u v x : moonshineMatterSpace) (ℓ m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (moonshineMatterNearVOA.smul u (ℓ + m - i) (moonshineMatterNearVOA.smul v (n + i) x)
          - negOnePow ℓ •
            moonshineMatterNearVOA.smul v (ℓ + n - i) (moonshineMatterNearVOA.smul u (m + i) x))) =
      ∑ᶠ i : ℤ, cbz m i •
        moonshineMatterNearVOA.smul (moonshineMatterNearVOA.smul u (ℓ + i) v) (m + n - i) x := by
  simpa only [one_mul] using moonshineMatterNearVOA.jacobi u v x ℓ m n

theorem moonshineMatter_skew (u v : moonshineMatterSpace) (n : ℤ) :
    moonshineMatterNearVOA.smul v n u = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) •
      sgn (-n - 1 - (j : ℤ)) •
        ((moonshineMatterNearVOA.L (-1) ^ j) (moonshineMatterNearVOA.smul u (n + (j : ℤ)) v)) :=
  moonshineMatterNearVOA.smul_eq_skew u v n

theorem moonshineMatter_zeroMode_derivation (u v : moonshineMatterSpace) (n : ℤ) :
    ⁅mode (moonshineMatterNearVOA.Y u) 0, mode (moonshineMatterNearVOA.Y v) n⁆ =
      mode (moonshineMatterNearVOA.Y (moonshineMatterNearVOA.smul u 0 v)) n :=
  moonshineMatterNearVOA.zeroMode_derivation u v n

theorem moonshineMatter_primary_comm (u : moonshineMatterSpace)
    (hu : moonshineMatterNearVOA.L 0 u = u)
    (hpos : ∀ j : ℤ, 0 < j → moonshineMatterNearVOA.L j u = 0) (m n : ℤ) :
    ⁅moonshineMatterNearVOA.L m, mode (moonshineMatterNearVOA.Y u) n⁆ =
      (-n) • mode (moonshineMatterNearVOA.Y u) (m + n) :=
  moonshineMatterNearVOA.primary_comm u hu hpos m n

theorem moonshineMatter_zeroMode_preserves_spurious (u : moonshineMatterSpace)
    (hu : moonshineMatterNearVOA.L 0 u = u)
    (hpos : ∀ j : ℤ, 0 < j → moonshineMatterNearVOA.L j u = 0)
    (x : moonshineMatterSpace) (hx : x ∈ moonshineMatterNearVOA.spurious) :
    moonshineMatterNearVOA.smul u 0 x ∈ moonshineMatterNearVOA.spurious :=
  moonshineMatterNearVOA.zeroMode_preserves_spurious u hu hpos x hx

theorem moonshineMatter_skew_zero (u v : moonshineMatterSpace) :
    moonshineMatterNearVOA.smul u 0 v + moonshineMatterNearVOA.smul v 0 u ∈
      LinearMap.range (moonshineMatterNearVOA.L (-1)) :=
  moonshineMatterNearVOA.skew_zero u v

/-- The commutator formula on the constructed near-VOA. -/
theorem lorentzian_commutator (u v : LorentzianFockSpace) (m n : ℤ) :
    ∃ N : ℕ, ⁅mode (lorentzianNearVOA.Y u) m, mode (lorentzianNearVOA.Y v) n⁆ =
      ∑ j : Fin N, gBinom m (j : ℕ) •
        mode (lorentzianNearVOA.Y (lorentzianNearVOA.smul u (j : ℕ) v)) (m + n - (j : ℕ)) :=
  lorentzianNearVOA.mode_commutator_lie u v m n

/-- Borcherds identity for all integer mode indices. -/
theorem lorentzian_jacobi (u v x : LorentzianFockSpace) (ℓ m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (lorentzianNearVOA.smul u (ℓ + m - i) (lorentzianNearVOA.smul v (n + i) x)
          - negOnePow ℓ •
            lorentzianNearVOA.smul v (ℓ + n - i) (lorentzianNearVOA.smul u (m + i) x))) =
      ∑ᶠ i : ℤ, cbz m i •
        lorentzianNearVOA.smul (lorentzianNearVOA.smul u (ℓ + i) v) (m + n - i) x := by
  simpa only [one_mul] using lorentzianNearVOA.jacobi u v x ℓ m n

theorem lorentzian_skew (u v : LorentzianFockSpace) (n : ℤ) :
    lorentzianNearVOA.smul v n u = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) •
      sgn (-n - 1 - (j : ℤ)) •
        ((lorentzianNearVOA.L (-1) ^ j) (lorentzianNearVOA.smul u (n + (j : ℤ)) v)) :=
  lorentzianNearVOA.smul_eq_skew u v n

theorem lorentzian_zeroMode_derivation (u v : LorentzianFockSpace) (n : ℤ) :
    ⁅mode (lorentzianNearVOA.Y u) 0, mode (lorentzianNearVOA.Y v) n⁆ =
      mode (lorentzianNearVOA.Y (lorentzianNearVOA.smul u 0 v)) n :=
  lorentzianNearVOA.zeroMode_derivation u v n

theorem lorentzian_primary_comm (u : LorentzianFockSpace)
    (hu : lorentzianNearVOA.L 0 u = u)
    (hpos : ∀ j : ℤ, 0 < j → lorentzianNearVOA.L j u = 0) (m n : ℤ) :
    ⁅lorentzianNearVOA.L m, mode (lorentzianNearVOA.Y u) n⁆ =
      (-n) • mode (lorentzianNearVOA.Y u) (m + n) :=
  lorentzianNearVOA.primary_comm u hu hpos m n

theorem lorentzian_zeroMode_preserves_spurious (u : LorentzianFockSpace)
    (hu : lorentzianNearVOA.L 0 u = u)
    (hpos : ∀ j : ℤ, 0 < j → lorentzianNearVOA.L j u = 0)
    (x : LorentzianFockSpace) (hx : x ∈ lorentzianNearVOA.spurious) :
    lorentzianNearVOA.smul u 0 x ∈ lorentzianNearVOA.spurious :=
  lorentzianNearVOA.zeroMode_preserves_spurious u hu hpos x hx

theorem lorentzian_skew_zero (u v : LorentzianFockSpace) :
    lorentzianNearVOA.smul u 0 v + lorentzianNearVOA.smul v 0 u ∈
      LinearMap.range (lorentzianNearVOA.L (-1)) :=
  lorentzianNearVOA.skew_zero u v

end VOA.Moonshine.ConwayNorton
