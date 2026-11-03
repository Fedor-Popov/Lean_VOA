import VOA.DeligneAudit.D4FusionToroidalFusionCutoff
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite rank bound for the cyclic toroidal associated graded

A finite filtration cutoff gives a surjection from the product of its
successive source pieces. The product of lower pieces lies in the kernel;
rank-nullity and telescoping bound the graded rank by the source rank.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.D1TensorG
open VOA.DeligneAudit.DeligneSector

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : ToroidalAction f V) (w : V)

def singleMap (d : ℕ) : evalFbelow A w (d + 1) →ₗ[ℂ] numerator A w where
  toFun x := single A w d x.1 x.2
  map_add' x y := by
    apply Subtype.ext
    simp [single]
  map_smul' a x := by
    apply Subtype.ext
    simp [single]

def symbol (d : ℕ) : evalFbelow A w (d + 1) →ₗ[ℂ] Gr A w :=
  (kernel A w).mkQ ∘ₗ singleMap A w d

theorem symbol_apply (d : ℕ) (x : evalFbelow A w (d + 1)) :
    symbol A w d x = (kernel A w).mkQ (single A w d x.1 x.2) := rfl

set_option maxHeartbeats 1000000 in
-- Elaborating the dependent product and the sum of quotient symbols is expensive.
def pieceSum (B : ℕ) :
    (Π d : Fin B, evalFbelow A w (d.val + 1)) →ₗ[ℂ] Gr A w where
  toFun v := ∑ d : Fin B, symbol A w d.val (v d)
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum]

theorem pieceSum_single (B : ℕ) (d : Fin B)
    (x : evalFbelow A w (d.val + 1)) :
    pieceSum A w B (Pi.single d x) = symbol A w d.val x := by
  change (∑ e : Fin B,
    symbol A w e.val ((Pi.single d x : Π j : Fin B,
      evalFbelow A w (j.val + 1)) e)) = _
  rw [Finset.sum_eq_single d]
  · simp
  · intro e _ hed
    have he : (Pi.single d x : Π j : Fin B,
      evalFbelow A w (j.val + 1)) e = 0 := by simp [hed]
    rw [he, map_zero]
  · simp

theorem pieceSum_surjective (B : ℕ) (hB : evalFbelow A w B = ⊤) :
    Function.Surjective (pieceSum A w B) := by
  let P := LinearMap.range (pieceSum A w B)
  let H : Submodule ℂ (ℕ →₀ V) :=
    (P.comap (kernel A w).mkQ).map (numerator A w).subtype
  have hnum : numerator A w ≤ H := by
    rw [numerator, Submodule.span_le]
    rintro _ ⟨d, x, hx, rfl⟩
    refine ⟨single A w d x hx, ?_, rfl⟩
    change (kernel A w).mkQ (single A w d x hx) ∈ P
    by_cases hd : d < B
    · let j : Fin B := ⟨d, hd⟩
      let y : evalFbelow A w (j.val + 1) := ⟨x, hx⟩
      exact ⟨Pi.single j y, by rw [pieceSum_single]; rfl⟩
    · have hBd : evalFbelow A w d = ⊤ := by
        apply top_unique
        rw [← hB]
        exact evalFbelow_mono A w (Nat.le_of_not_lt hd)
      have hlow : x ∈ evalFbelow A w d := by rw [hBd]; trivial
      have hker : single A w d x hx ∈ kernel A w :=
        Submodule.subset_span ⟨d, x, hlow, rfl⟩
      have hz : (kernel A w).mkQ (single A w d x hx) = 0 :=
        (Submodule.Quotient.mk_eq_zero (kernel A w)).mpr hker
      rw [hz]
      exact Submodule.zero_mem P
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (kernel A w) y
  obtain ⟨u, hu, hval⟩ := hnum x.2
  have he : u = x := Subtype.ext hval
  rw [← he]
  exact hu

def lowerEmbed (B : ℕ) :
    (Π d : Fin B, evalFbelow A w d.val) →ₗ[ℂ]
      (Π d : Fin B, evalFbelow A w (d.val + 1)) where
  toFun v d := ⟨(v d).1, evalFbelow_mono A w (Nat.le_succ _) (v d).2⟩
  map_add' _ _ := by funext d; apply Subtype.ext; rfl
  map_smul' _ _ := by funext d; apply Subtype.ext; rfl

theorem lowerEmbed_injective (B : ℕ) : Function.Injective (lowerEmbed A w B) := by
  intro u v huv
  funext d
  apply Subtype.ext
  exact congrArg (fun x => (x d : V)) huv

theorem pieceSum_lower_zero (B : ℕ) (v : Π d : Fin B, evalFbelow A w d.val) :
    pieceSum A w B (lowerEmbed A w B v) = 0 := by
  change (∑ d : Fin B, symbol A w d.val (lowerEmbed A w B v d)) = 0
  apply Finset.sum_eq_zero
  intro d _
  rw [symbol_apply]
  apply (Submodule.Quotient.mk_eq_zero (kernel A w)).mpr
  exact Submodule.subset_span ⟨d.val, (v d).1, (v d).2, rfl⟩

theorem rank_tel [FiniteDimensional ℂ V] (B : ℕ) :
    (∑ d ∈ Finset.range B, Module.finrank ℂ (evalFbelow A w (d + 1))) =
      (∑ d ∈ Finset.range B, Module.finrank ℂ (evalFbelow A w d)) +
        Module.finrank ℂ (evalFbelow A w B) := by
  induction B with
  | zero => rw [evalFbelow_zero]; simp
  | succ B ih =>
      simp only [Finset.sum_range_succ]
      omega

theorem finrank_gr_le_source [FiniteDimensional ℂ V] (B : ℕ)
    (hB : evalFbelow A w B = ⊤) :
    FiniteDimensional ℂ (Gr A w) ∧
      Module.finrank ℂ (Gr A w) ≤ Module.finrank ℂ V := by
  letI : FiniteDimensional ℂ (Gr A w) :=
    FiniteDimensional.of_surjective (pieceSum A w B) (pieceSum_surjective A w B hB)
  have hker : LinearMap.range (lowerEmbed A w B) ≤
      LinearMap.ker (pieceSum A w B) := by
    rintro _ ⟨v, rfl⟩
    exact pieceSum_lower_zero A w B v
  have hle := Submodule.finrank_mono hker
  rw [LinearMap.finrank_range_of_inj (lowerEmbed_injective A w B)] at hle
  have hrank := (pieceSum A w B).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (pieceSum_surjective A w B hB)] at hrank
  rw [finrank_top] at hrank
  rw [Module.finrank_pi_fintype] at hle
  rw [Module.finrank_pi_fintype] at hrank
  have hsum : (∑ d : Fin B, Module.finrank ℂ (evalFbelow A w (d.val + 1))) =
      (∑ d : Fin B, Module.finrank ℂ (evalFbelow A w d.val)) +
        Module.finrank ℂ V := by
    calc
      _ = ∑ d ∈ Finset.range B,
          Module.finrank ℂ (evalFbelow A w (d + 1)) :=
        Fin.sum_univ_eq_sum_range _ B
      _ = (∑ d ∈ Finset.range B, Module.finrank ℂ (evalFbelow A w d)) +
          Module.finrank ℂ (evalFbelow A w B) := rank_tel A w B
      _ = (∑ d : Fin B, Module.finrank ℂ (evalFbelow A w d.val)) +
          Module.finrank ℂ V := by
        rw [hB, finrank_top]
        exact congrArg (fun q => q + Module.finrank ℂ V)
          (Fin.sum_univ_eq_sum_range
            (fun d => Module.finrank ℂ (evalFbelow A w d)) B).symm
  constructor
  · infer_instance
  · omega

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.pieceSum_surjective
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.finrank_gr_le_source
