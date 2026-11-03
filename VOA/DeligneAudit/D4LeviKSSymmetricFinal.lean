import VOA.DeligneAudit.D4LeviKSSymmetricColour

/-! Independent arbitrary symmetric shifts in the three XYZ alphabets. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviConversion

variable {σ : Type*} [Fintype σ]

noncomputable def xyzSymmetricPolynomial (shape : σ → Fin 6)
    (Ψ : MvPolynomial {t : σ // shape t = 1} ℂ)
    (ρs : MvPolynomial {t : σ // shape t = 4} ℂ)
    (F : MvPolynomial {t : σ // shape t = 5} ℂ) : MvPolynomial σ ℂ :=
  rename (fun i => i.1) Ψ * rename (fun i => i.1) ρs *
    rename (fun i => i.1) F

theorem xyzSymmetricPolynomial_mem (shape : σ → Fin 6)
    (Ψ : MvPolynomial {t : σ // shape t = 1} ℂ)
    (ρs : MvPolynomial {t : σ // shape t = 4} ℂ)
    (F : MvPolynomial {t : σ // shape t = 5} ℂ)
    (hΨ : Ψ ∈ symmetricSubalgebra _ ℂ)
    (hρs : ρs ∈ symmetricSubalgebra _ ℂ)
    (hF : F ∈ symmetricSubalgebra _ ℂ) :
    xyzSymmetricPolynomial shape Ψ ρs F ∈ xyzPowerSumAlgebra shape := by
  change rename (fun i : {t : σ // shape t = 1} => i.1) Ψ *
      rename (fun i : {t : σ // shape t = 4} => i.1) ρs *
      rename (fun i : {t : σ // shape t = 5} => i.1) F ∈
        xyzPowerSumAlgebra shape
  exact (xyzPowerSumAlgebra shape).mul_mem
    ((xyzPowerSumAlgebra shape).mul_mem
      (colourSymmetric_mem_xyzPowerSumAlgebra shape 1 (Or.inl rfl) Ψ hΨ)
      (colourSymmetric_mem_xyzPowerSumAlgebra shape 4
        (Or.inr (Or.inl rfl)) ρs hρs))
    (colourSymmetric_mem_xyzPowerSumAlgebra shape 5
      (Or.inr (Or.inr rfl)) F hF)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Arbitrary independent symmetric shifts of the X, Y, and Z modes
    preserve any fixed-shape XYZ relation in a descending key prefix. -/
theorem xyz_symmetric_prefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (shape : σ → Fin 6)
    (hshape : ∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5)
    (W : MvPolynomial σ ℂ)
    (hW : xyzEvaluation ρ w shape W ∈ keyPrefix ρ w m i)
    (Ψ : MvPolynomial {t : σ // shape t = 1} ℂ)
    (ρs : MvPolynomial {t : σ // shape t = 4} ℂ)
    (F : MvPolynomial {t : σ // shape t = 5} ℂ)
    (hΨ : Ψ ∈ symmetricSubalgebra _ ℂ)
    (hρs : ρs ∈ symmetricSubalgebra _ ℂ)
    (hF : F ∈ symmetricSubalgebra _ ℂ) :
    xyzEvaluation ρ w shape
      (symmetricShiftAction σ (xyzSymmetricPolynomial shape Ψ ρs F) W) ∈
        keyPrefix ρ w m i := by
  exact xyzPowerSumAlgebra_prefix ρ w m i h hi shape hshape _
    (xyzSymmetricPolynomial_mem shape Ψ ρs F hΨ hρs hF) W hW

/-- The arbitrary symmetric Rx family, conditional only on an explicit
    fixed-shape word-polynomial presentation of the XZG contraction. -/
theorem rx_family_prefix {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V) (m i : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs ys : List ℕ) (c s : ℕ)
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey (List.replicate rs.length 0) ys [] c (rs.sum + ys.sum + s))
    (shape : σ → Fin 6)
    (hshape : ∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5)
    (W : MvPolynomial σ ℂ)
    (hW : xyzEvaluation ρ w shape W =
      mixedTop (yOp ρ) (zOp ρ) c s (ys ++ List.replicate c 0)
        (rs.map (transportCurrent (xOp ρ))).prod w)
    (Ψ : MvPolynomial {t : σ // shape t = 1} ℂ)
    (ρs : MvPolynomial {t : σ // shape t = 4} ℂ)
    (F : MvPolynomial {t : σ // shape t = 5} ℂ)
    (hΨ : Ψ ∈ symmetricSubalgebra _ ℂ)
    (hρs : ρs ∈ symmetricSubalgebra _ ℂ)
    (hF : F ∈ symmetricSubalgebra _ ℂ) :
    xyzEvaluation ρ w shape
      (symmetricShiftAction σ (xyzSymmetricPolynomial shape Ψ ρs F) W) ∈
        keyPrefix ρ w m i := by
  exact rx_family_prefix_of_evaluation ρ w m i h rs ys c s hK hks hi hkey
    shape hshape W _ hW
    (xyzSymmetricPolynomial_mem shape Ψ ρs F hΨ hρs hF)

/-- The arbitrary symmetric Ry family under its fixed-shape presentation. -/
theorem ry_family_prefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs xs : List ℕ) (c s : ℕ)
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs (List.replicate rs.length 0) [] c (rs.sum + xs.sum + s))
    (shape : σ → Fin 6)
    (hshape : ∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5)
    (W : MvPolynomial σ ℂ)
    (hW : xyzEvaluation ρ w shape W =
      mixedTop (xOp ρ) (zOp ρ) c s (xs ++ List.replicate c 0)
        (rs.map (transportCurrent (yOp ρ))).prod w)
    (Ψ : MvPolynomial {t : σ // shape t = 1} ℂ)
    (ρs : MvPolynomial {t : σ // shape t = 4} ℂ)
    (F : MvPolynomial {t : σ // shape t = 5} ℂ)
    (hΨ : Ψ ∈ symmetricSubalgebra _ ℂ)
    (hρs : ρs ∈ symmetricSubalgebra _ ℂ)
    (hF : F ∈ symmetricSubalgebra _ ℂ) :
    xyzEvaluation ρ w shape
      (symmetricShiftAction σ (xyzSymmetricPolynomial shape Ψ ρs F) W) ∈
        keyPrefix ρ w m i := by
  exact ry_family_prefix_of_evaluation ρ w m i h rs xs c s hK hks hi hkey
    shape hshape W _ hW
    (xyzSymmetricPolynomial_mem shape Ψ ρs F hΨ hρs hF)

/-- The arbitrary symmetric Rz family under its fixed-shape presentation. -/
theorem rz_family_prefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (xs ys zs : List ℕ) (k s : ℕ)
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs ys zs k (xs.sum + ys.sum + zs.sum + s))
    (shape : σ → Fin 6)
    (hshape : ∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5)
    (W : MvPolynomial σ ℂ)
    (hW : xyzEvaluation ρ w shape W =
      topSum (yOp ρ) (zOp ρ) k s (ys ++ List.replicate k 0) •
        (((xs.map (xOp ρ)).prod * (zs.map (zOp ρ)).prod) • w))
    (Ψ : MvPolynomial {t : σ // shape t = 1} ℂ)
    (ρs : MvPolynomial {t : σ // shape t = 4} ℂ)
    (F : MvPolynomial {t : σ // shape t = 5} ℂ)
    (hΨ : Ψ ∈ symmetricSubalgebra _ ℂ)
    (hρs : ρs ∈ symmetricSubalgebra _ ℂ)
    (hF : F ∈ symmetricSubalgebra _ ℂ) :
    xyzEvaluation ρ w shape
      (symmetricShiftAction σ (xyzSymmetricPolynomial shape Ψ ρs F) W) ∈
        keyPrefix ρ w m i := by
  exact rz_family_prefix_of_evaluation ρ w m i h xs ys zs k s hk hks hi hkey
    shape hshape W _ hW
    (xyzSymmetricPolynomial_mem shape Ψ ρs F hΨ hρs hF)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyzSymmetricPolynomial_mem
#print axioms VOA.DeligneAudit.D4Levi.xyz_symmetric_prefix
#print axioms VOA.DeligneAudit.D4Levi.rx_family_prefix
#print axioms VOA.DeligneAudit.D4Levi.ry_family_prefix
#print axioms VOA.DeligneAudit.D4Levi.rz_family_prefix
