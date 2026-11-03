import VOA.Classification.COne.OrbIcoVScalarPolynomial

/-! The normalized even scalar polynomial source is exactly the actual
uniform C2 functional of the genuine Ward source, through every finite
coefficient cutoff. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA InverseDS.VirasoroVerma Polynomial
open scoped Classical

theorem polyWidthStep_even_sound (H K : ℂ) (r j N n : ℕ) (hj : j<r)
    (P : ℂ[X]) (u : ℕ → ℂ) (hu : ∀ m≤N, P.coeff m=(2:ℂ)^m*u (2*m)) (hn : n≤N) :
    (polyWidthStep H K r j P).coeff n =
      (2:ℂ)^n*wardUniformStep K H (H+(r:ℂ)) (r-j) (2*n) u := by
  rw [polyWidthStep_coeff,hu n hn]
  have hrj : ((r-j:ℕ):ℂ)+(j:ℂ)=(r:ℂ) := by
    exact_mod_cast Nat.sub_add_cancel (by omega : j≤r)
  unfold wardUniformStep wardCreationDiagonal
  by_cases hk : r-j=2
  · cases n with
    | zero =>
      simp only [Nat.mul_zero,Nat.cast_zero,pow_zero,
        if_neg (by omega : ¬ (r-j=2 ∧ 0<0)),
        if_neg (by omega : ¬ (r-j=2 ∧ 2≤0)),one_mul,add_zero]
      linear_combination u 0*((-1:ℂ)^(r-j))*hrj
    | succ n =>
      rw [if_pos ⟨hk,by omega⟩,if_pos ⟨hk,by omega⟩]
      rw [Nat.add_sub_cancel,hu n (by omega)]
      rw [show 2*(n+1)-2=2*n by omega]
      push_cast
      rw [pow_succ]
      norm_num only [show (2:ℂ)⁻¹=(1/2:ℂ) by norm_num]
      linear_combination (-1:ℂ)^(r-j)*(2:ℂ)^n*u (2*(n+1))*2*hrj
  · rw [if_neg (by tauto),if_neg (by tauto)]
    push_cast
    linear_combination (-1:ℂ)^(r-j)*(2:ℂ)^n*u (2*n)*hrj

theorem polyWidthStage_even_sound (H K t : ℂ) (r N : ℕ) (P : ℂ[X]) (u : ℕ → ℂ)
    (hu : ∀ n≤N, P.coeff n=(2:ℂ)^n*u (2*n)) :
    ∀ n≤N, (polyWidthStage H K t r P).coeff n =
      (2:ℂ)^n*wardBSAUniform K H t H 13 u r (2*n) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro n hn
    cases r with
    | zero => simpa only [polyWidthStage,wardBSAUniform] using hu n hn
    | succ r =>
      simp only [polyWidthStage,wardBSAUniform,coeff_smul,finsetSum_coeff,smul_eq_mul]
      have he (j : Fin (r+1)) := polyWidthStep_even_sound H K (r+1) j N n j.isLt
        (polyWidthStage H K t j P) (wardBSAUniform K H t H 13 u j)
        (ih j j.isLt) hn
      simp only [he,← Finset.mul_sum]
      ring

theorem polyWidthSource_even_sound (H K t : ℂ) (N : ℕ) (P : ℂ[X]) (u : ℕ → ℂ)
    (hu : ∀ n≤N, P.coeff n=(2:ℂ)^n*u (2*n)) (n : ℕ) (hn : n≤N) :
    (polyWidthSource H K t P).coeff n =
      (2:ℂ)^n*wardBSAUniformSource K H t H 13 13 u (2*n) := by
  simp only [polyWidthSource,wardBSAUniformSource,finsetSum_coeff]
  have he (j : Fin 13) := polyWidthStep_even_sound H K 13 j N n j.isLt
    (polyWidthStage H K t j P) (wardBSAUniform K H t H 13 u j)
    (polyWidthStage_even_sound H K t j N P u hu) hn
  simp only [he,Finset.mul_sum]


theorem polyWidthSource_actual_sound (c H K t : ℂ) (N : ℕ)
    (f : wardSequenceSpace c K) (P : ℂ[X])
    (hP : ∀ n≤N, P.coeff n=(2:ℂ)^n*uniformProbe c K (f.val (2*n)))
    (n : ℕ) (hn : n≤N) :
    (polyWidthSource H K t P).coeff n = (2:ℂ)^n*
      uniformProbe c K ((wardSourceAt c K H t H 13 f).val (2*n)) := by
  rw [polyWidthSource_even_sound H K t N P (fun j => uniformProbe c K (f.val j)) hP n hn,wardSourceAt_uniform]

end VOA.Classification.COne.OrbIcoV
