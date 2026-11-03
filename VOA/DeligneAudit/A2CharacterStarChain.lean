/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CharacterStar
import VOA.Commutative.QEuler

/-!
# An elementary proof architecture for the A₂ star identity

Write `F = ∑_n q^n D_n/(q)_n` with `D_n = ∑_{i,j ≤ n} [n,i][n,j] G_{n-i+j}` and
`G_M = ∑_r [M,r]` (`demazurePoly`, `rogersSzego`).  The identity `F = ∏_{r ≥ 1}(1+q^r)^8` is reduced
here to three named statements, each an identity of formal power series over `ℤ`:

1. `StarReduction`: `(q)_∞ F = ∑_v q^v U_{2v}`, where `U_m = ∑_s q^s G_s G_{s+m}/(q)_s`.
   Proof on paper (not yet in Lean): the overlapping-subset form of q-Vandermonde,
   `[n,i][n,j] = ∑_k q^{(i-k)(j-k)} (q)_n / ((q)_k (q)_{i-k} (q)_{j-k} (q)_{n-i-j+k})`,
   turns `F` into `∑_{k,u,v,w} q^{k+u+v+w+uv} G_{k+2v+w}/((q)_k(q)_u(q)_v(q)_w)`; Euler's sum
   `∑_u q^{u(1+v)}/(q)_u = (q)_v/(q)_∞` removes `u`, and `∑_{k+w=s} 1/((q)_k(q)_w) = G_s/(q)_s`.
2. `ShiftedMehler`: `U_m (q)_∞^3 (1 - q^{m+1}) = m + 1`.
   Proof on paper: q-Vandermonde again gives `U_m = ∑_p [m,p] W_p` with
   `W_p = ∑_{l,u} q^{l+u(p+1)} G_{l+u}/((q)_l(q)_u)`; Rogers' Mehler formula for the Rogers–Szegő
   polynomials, `∑_M H_M(x) H_M(y) t^M/(q)_M = (xyt²)_∞/((t)_∞(xt)_∞(yt)_∞(xyt)_∞)`, at
   `x = 1, y = q^p, t = q` gives `W_p = (q)_p/((1-q^{p+1})(q)_∞^3)`; and the finite identity
   `∑_{p ≤ m} (q)_m/((q)_{m-p}(1-q^{p+1})) = (m+1)/(1-q^{m+1})` finishes.
3. `FourTriangular`: `∑_{v ≥ 0} (2v+1) q^v/(1-q^{2v+1}) = (q)_∞^4 (-q;q)_∞^8`.  This is Legendre's
   four-triangular-numbers theorem, `ψ(q)^4 = ∑_n σ(2n+1) q^n` with `ψ = ∑ q^{n(n+1)/2}`,
   combined with Gauss's product `ψ(q) = (q²;q²)_∞/(q;q²)_∞ = (q)_∞(-q;q)_∞²`.

All three were checked numerically, outside Lean, through `q^24` (ShiftedMehler for `m ≤ 9`).
This route avoids the flavored Macdonald `t = 0` machinery of the paper entirely.

`starIdentity_of_chain` proves `StarIdentity` from the three statements.  The glue is in Lean; the
three statements are the residual.
-/

namespace VOA.DeligneAudit.A2

open PowerSeries VOA.QSeries

noncomputable section

local notation "q" => (PowerSeries.X : PowerSeries ℤ)

/-- `F = ∑_N demazureCoeff N q^N`. -/
def starF : PowerSeries ℤ := PowerSeries.mk fun N => (demazureCoeff N : ℤ)

/-- `∏_{r ≥ 1}(1+q^r)^8 = ∑_N productCoeff N q^N`. -/
def fermionInf : PowerSeries ℤ := PowerSeries.mk fun N => (productCoeff N : ℤ)

/-- `1/(1-q^m) = ∑_{m ∣ N} q^N` (for `m ≥ 1`). -/
def geomInv (m : ℕ) : PowerSeries ℤ := PowerSeries.mk fun N => if m ∣ N then 1 else 0

theorem geomInv_mul (m : ℕ) (hm : 0 < m) : (1 - q ^ m) * geomInv m = 1 := by
  have key : ∀ N, m ≤ N → (m ∣ N - m ↔ m ∣ N) := fun N h => by
    constructor
    · intro hd
      have := Nat.dvd_add hd (dvd_refl m)
      rwa [Nat.sub_add_cancel h] at this
    · intro hd
      exact Nat.dvd_sub hd (dvd_refl m)
  ext N
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', geomInv, coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [show ¬ m ≤ 0 by omega]
  · by_cases h : m ≤ N
    · rw [if_pos h, coeff_mk, if_neg hN.ne']
      by_cases hd : m ∣ N
      · rw [if_pos hd, if_pos ((key N h).mpr hd), sub_self]
      · rw [if_neg hd, if_neg (fun h' => hd ((key N h).mp h')), sub_self]
    · have : ¬ m ∣ N := fun hd => h (Nat.le_of_dvd hN hd)
      simp [h, this, hN.ne']

/-- `U_m = ∑_s q^s G_s G_{s+m}/(q)_s`. -/
def shiftedU (m : ℕ) : PowerSeries ℤ :=
  powerShiftSum 1 fun s => rogersSzego s * rogersSzego (s + m) * reciprocalQFactorial s

/-- **Residual 1** (elementary: q-Vandermonde + Euler). -/
structure StarReduction : Prop where
  eq : (euler : PowerSeries ℤ) * starF = powerShiftSum 1 fun v => shiftedU (2 * v)

/-- **Residual 2** (Rogers' Mehler formula for Rogers–Szegő polynomials + a finite identity). -/
structure ShiftedMehler : Prop where
  eq : ∀ m : ℕ, shiftedU m * (euler : PowerSeries ℤ) ^ 3 * (1 - q ^ (m + 1)) = (m + 1 : ℕ)

/-- **Residual 3** (Legendre's four-triangular-numbers theorem + Gauss's product for `ψ`). -/
structure FourTriangular : Prop where
  eq : (powerShiftSum 1 fun v => ((2 * v + 1 : ℕ) : PowerSeries ℤ) * geomInv (2 * v + 1)) =
    (euler : PowerSeries ℤ) ^ 4 * fermionInf

theorem shiftedU_eq (hM : ShiftedMehler) (m : ℕ) :
    shiftedU m = ((m + 1 : ℕ) : PowerSeries ℤ) * geomInv (m + 1) * reciprocalEuler ^ 3 := by
  have h := hM.eq m
  have hg := geomInv_mul (m + 1) (Nat.succ_pos m)
  have he : (euler : PowerSeries ℤ) * reciprocalEuler = 1 := euler_mul_reciprocal
  calc shiftedU m
      = shiftedU m * (euler ^ 3 * (1 - q ^ (m + 1))) *
          (geomInv (m + 1) * reciprocalEuler ^ 3) := by
        rw [show shiftedU m * (euler ^ 3 * (1 - q ^ (m + 1))) *
            (geomInv (m + 1) * reciprocalEuler ^ 3) =
            shiftedU m * ((euler * reciprocalEuler) ^ 3 * ((1 - q ^ (m + 1)) * geomInv (m + 1)))
            by ring, he, hg]
        simp
    _ = _ := by rw [← mul_assoc, ← mul_assoc, h]

/-- **The star identity from the three residual statements.** -/
theorem starF_eq_fermionInf (hR : StarReduction) (hM : ShiftedMehler) (hT : FourTriangular) :
    starF = fermionInf := by
  have he : (euler : PowerSeries ℤ) * reciprocalEuler = 1 := euler_mul_reciprocal
  have hsum : (powerShiftSum 1 fun v => shiftedU (2 * v)) =
      (powerShiftSum 1 fun v => ((2 * v + 1 : ℕ) : PowerSeries ℤ) * geomInv (2 * v + 1)) *
        reciprocalEuler ^ 3 := by
    rw [← powerShiftSum_mul 1 one_pos]
    exact powerShiftSum_congr 1 fun v => by rw [shiftedU_eq hM]
  have h := hR.eq
  rw [hsum, hT.eq] at h
  calc starF = (reciprocalEuler * euler) * starF := by rw [mul_comm reciprocalEuler, he, one_mul]
    _ = reciprocalEuler * (euler ^ 4 * fermionInf * reciprocalEuler ^ 3) := by rw [mul_assoc, h]
    _ = (euler * reciprocalEuler) ^ 4 * fermionInf := by ring
    _ = fermionInf := by rw [he, one_pow, one_mul]

/-- **`StarIdentity` from the chain.** -/
theorem starIdentity_of_chain (hR : StarReduction) (hM : ShiftedMehler) (hT : FourTriangular) :
    StarIdentity := by
  refine ⟨fun N => ?_⟩
  have := congrArg (coeff N) (starF_eq_fermionInf hR hM hT)
  simp only [starF, fermionInf, coeff_mk] at this
  exact_mod_cast this

/-- The full character side `D_N ≤ dim V_N` from the chain and Kac–Wakimoto. -/
theorem demazureCharacterBound_of_chain (hR : StarReduction) (hM : ShiftedMehler)
    (hT : FourTriangular) (hkw : KacWakimotoLowerBound) : DemazureCharacterBound :=
  demazureCharacterBound_of_inputs (starIdentity_of_chain hR hM hT) hkw

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.geomInv_mul
#print axioms VOA.DeligneAudit.A2.starF_eq_fermionInf
#print axioms VOA.DeligneAudit.A2.starIdentity_of_chain
#print axioms VOA.DeligneAudit.A2.demazureCharacterBound_of_chain
end AxiomAudit
