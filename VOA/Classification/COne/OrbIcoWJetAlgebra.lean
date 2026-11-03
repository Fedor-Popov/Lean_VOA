import VOA.Classification.COne.OrbIcoWJets
import Mathlib.Algebra.Polynomial.Coeff

/-! Exact semantics and uniqueness of undivided jet recurrence certificates.
A pivot of order v loses exactly v Taylor orders. No analytic derivatives or
division at a resonant parameter are assumed. -/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoW
open OrbOdd Polynomial
open scoped BigOperators

/-- The stored rational coefficients are exactly the polynomial coefficients. -/
theorem coeff_zp (a : Jet) (n : ℕ) : (zp a).coeff n = (((a[n]?).getD 0 : ℚ) : ℂ) := by
  induction a generalizing n with
  | nil => simp [zp]
  | cons x a ih =>
    cases n with
    | zero => simp [zp]
    | succ n => simp [zp,coeff_X_mul,ih]

/-- Truncation preserves precisely the certified Taylor orders. -/
theorem coeff_jetCut (P : ℕ) (a : Jet) {n : ℕ} (hn : n ≤ P) :
    (zp (jetCut P a)).coeff n = (zp a).coeff n := by
  rw [coeff_zp,coeff_zp]
  simp only [jetCut,List.getElem?_map,List.getElem?_range (by omega : n<P+1),
    Option.map_some,Option.getD_some]

theorem coeff_jetAdd (P : ℕ) (a b : Jet) {n : ℕ} (hn : n ≤ P) :
    (zp (jetAdd P a b)).coeff n = (zp a).coeff n + (zp b).coeff n := by
  rw [jetAdd,coeff_jetCut P _ hn,zp_paddL,coeff_add]

/-- The exact jet multiplication has the ordinary polynomial convolution semantics. -/
theorem coeff_jetMul (P : ℕ) (a b : Jet) {n : ℕ} (hn : n ≤ P) :
    (zp (jetMul P a b)).coeff n = (zp a * zp b).coeff n := by
  rw [jetMul,coeff_jetCut P _ hn,zp_pmulL]

/-- A nonzero coefficient at order v determines a quotient through order P-v
from the undivided equation, retaining every resonant cancellation. -/
theorem coefficients_unique_across_pivot (D F G : ℂ[X]) (P v : ℕ)
    (hbefore : ∀ i < v, D.coeff i=0) (hpivot : D.coeff v ≠ 0)
    (he : ∀ i≤P, (D*F).coeff i=(D*G).coeff i) :
    ∀ k : ℕ, k+v≤P → F.coeff k=G.coeff k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hz : (D*(F-G)).coeff (k+v)=0 := by
      rw [mul_sub,coeff_sub,he (k+v) hk,sub_self]
    rw [coeff_mul,Finset.sum_eq_single (v,k)] at hz
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hpivot)
    · intro ij hij hne
      have hs : ij.1+ij.2=k+v := Finset.mem_antidiagonal.mp hij
      by_cases hlt : ij.1 < v
      · rw [hbefore _ hlt,zero_mul]
      · have hgt : v < ij.1 := by
          by_contra h
          have hi : ij.1=v := by omega
          have hj : ij.2=k := by omega
          exact hne (Prod.ext hi hj)
        rw [coeff_sub,ih ij.2 (by omega) (by omega),sub_self,mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_antidiagonal.mpr (by omega)))

/-- Finite jet uniqueness follows directly from its proved polynomial semantics. -/
theorem jet_coefficients_unique (P v : ℕ) (d f g : Jet)
    (hbefore : ∀ i < v, (zp d).coeff i=0) (hpivot : (zp d).coeff v ≠ 0)
    (he : jetMul P d f=jetMul P d g) :
    ∀ k : ℕ, k+v≤P → (zp f).coeff k=(zp g).coeff k := by
  apply coefficients_unique_across_pivot (zp d) (zp f) (zp g) P v hbefore hpivot
  intro i hi
  have h := congrArg (fun a => (zp a).coeff i) he
  dsimp only at h
  rwa [coeff_jetMul P d f hi,coeff_jetMul P d g hi] at h

end VOA.Classification.COne.OrbIcoW
