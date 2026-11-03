import VOA.Classification.COne.OrbIcoWJetPole
import VOA.Classification.COne.OrbIcoWScalar

/-! Exact continuous-remainder jets of the BSA parameter H(t)=42/t-6. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoW
open OrbOdd Polynomial Filter Topology

/-- The finite H jet stores exactly its alternating geometric coefficients. -/
theorem coeff_jetH (P : ℕ) {n : ℕ} (hn : n ≤ P) :
    (zp (jetH P)).coeff n = if n=0 then 36 else (42 : ℂ)*(-1)^n := by
  rw [coeff_zp]
  simp only [jetH,List.getElem?_map,List.getElem?_range (by omega : n<P+1),
    Option.map_some,Option.getD_some]
  split_ifs <;> push_cast <;> rfl

/-- Multiplying by the exact denominator leaves only an order-P+1 error. -/
theorem jetH_error_divisible (P : ℕ) :
    Polynomial.X^(P+1) ∣
      Polynomial.C (42 : ℂ)-Polynomial.C 6*(1+Polynomial.X)-
        (1+Polynomial.X)*zp (jetH P) := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro n hn
  have he : Polynomial.C (42 : ℂ)-Polynomial.C 6*(1+Polynomial.X)-
      (1+Polynomial.X)*zp (jetH P) =
      Polynomial.C 36-Polynomial.C 6*Polynomial.X-zp (jetH P)-Polynomial.X*zp (jetH P) := by
    norm_num only [map_ofNat]
    ring
  rw [he]
  cases n with
  | zero => simp [coeff_jetH P (n := 0) (by omega)]
  | succ n =>
    rw [Polynomial.coeff_sub,Polynomial.coeff_sub,Polynomial.coeff_sub,
      Polynomial.coeff_C,Polynomial.coeff_C_mul,Polynomial.coeff_X,
      Polynomial.coeff_X_mul,coeff_jetH P (n := n+1) (by omega),
      coeff_jetH P (n := n) (by omega)]
    cases n with
    | zero => norm_num
    | succ n =>
      simp only [Nat.succ_ne_zero,if_false,Nat.succ_inj,show ¬n+1=0 by omega]
      rw [pow_succ]
      simp

/-- H has the certified rational jet at every finite order, with a continuous
remainder and no Taylor differentiability assumption. -/
theorem widthH_jetApprox (P : ℕ) : JetApproxPL (P+1) widthH (jetH P) := by
  let D : ℂ[X] := 1+Polynomial.X
  let J := zp (jetH P)
  have hden : JetApprox (P+1) (fun t : ℂ => t) D := by
    have h := JetApprox.polynomial (P+1) D
    apply h.congr
    exact Eventually.of_forall (fun t => by simp [D])
  let E := Polynomial.C (42 : ℂ)-Polynomial.C 6*D-D*J
  have he0 : JetApprox (P+1) (fun t : ℂ => E.eval (t-1)) 0 :=
    (JetApprox.polynomial (P+1) E).of_remainder (by
      simpa only [sub_zero,E,D,J] using jetH_error_divisible P)
  have hn : ∀ᶠ t in 𝓝[≠] (1 : ℂ), t≠0 :=
    (continuousAt_id.eventually_ne (by norm_num : (1 : ℂ)≠0)).filter_mono nhdsWithin_le_nhds
  have herr : JetApprox (P+1) (fun t => t*(widthH t-J.eval (t-1))) 0 := by
    apply he0.congr
    filter_upwards [hn] with t ht
    simp only [E,D,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_mul,
      Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_X,widthH]
    field_simp [ht]
    ring
  have h := JetApprox.cancel_pivot hden (v := 0) (by omega)
    (by intro i hi; omega) (by simp [D]) herr
  simpa only [Nat.sub_zero,J] using h

end VOA.Classification.COne.OrbIcoW
