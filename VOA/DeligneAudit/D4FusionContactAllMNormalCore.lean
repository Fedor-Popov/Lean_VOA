import VOA.DeligneAudit.D4FusionContactAllMWheelsCore

/-! A fixed-length word ideal from one nil power and actual derivations.
No dimension or presentation equality is assumed. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

open AllMWheels (cancel_nat_factor deriv_pow_succ)

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def word {σ : Type*} (F : σ → A) (l : List σ) : A := (l.map F).prod

omit [Algebra ℂ A] in
@[simp] theorem word_nil {σ : Type*} (F : σ → A) : word F [] = 1 := rfl

omit [Algebra ℂ A] in
@[simp] theorem word_cons {σ : Type*} (F : σ → A) (a : σ) (l : List σ) :
    word F (a :: l) = F a * word F l := rfl

theorem deriv_word_zero {σ : Type*} (D : Derivation ℂ A A) (F : σ → A)
    (hF : ∀ a, D (F a) = 0) (l : List σ) : D (word F l) = 0 := by
  induction l with
  | nil => exact D.map_one_eq_zero
  | cons a l ih =>
      simp only [word_cons, Derivation.leibniz, hF, ih, smul_zero, add_zero]

/-- Derivations with single-letter images preserve fixed-length word spans.
The multiplier and actual ideal relation are retained throughout. -/
theorem deriv_word_mul_mem {σ : Type*} (I : Ideal A) (D : Derivation ℂ A A)
    (F : σ → A) (hF : ∀ a, ∃ c : A, ∃ b : σ, D (F a) = c * F b)
    (l : List σ) (q : A)
    (hword : ∀ l' : List σ, l'.length = l.length → word F l' * q ∈ I) :
    D (word F l) * q ∈ I := by
  induction l generalizing q with
  | nil => simp only [word_nil, Derivation.map_one_eq_zero, zero_mul]; exact I.zero_mem
  | cons a l ih =>
      have htail : D (word F l) * (F a * q) ∈ I := by
        apply ih
        intro l' hl'
        have hh := hword (a :: l') (by simpa only [List.length_cons] using congrArg Nat.succ hl')
        convert hh using 1
        simp only [word_cons]
        ring
      obtain ⟨c, b, hb⟩ := hF a
      have hhead : c * (word F (b :: l) * q) ∈ I :=
        I.mul_mem_left _ (hword (b :: l) rfl)
      convert I.add_mem htail hhead using 1
      simp only [word_cons, Derivation.leibniz, smul_eq_mul, hb]
      ring

/-- Repeated polarization of the zero center produces arbitrary A words. -/
theorem a_word_center_pow_mem {σ : Type*} (I : Ideal A) (F : σ → A) (c₀ : A)
    (E : σ → Derivation ℂ A A)
    (hI : ∀ a p, p ∈ I → E a p ∈ I)
    (hEc : ∀ a, E a c₀ = F a) (hEF : ∀ a b, E a (F b) = 0)
    (r : ℕ) (hpow : c₀ ^ r ∈ I) (l : List σ) (n : ℕ)
    (hlen : l.length + n = r) : word F l * c₀ ^ n ∈ I := by
  induction l generalizing n with
  | nil =>
      have he : n = r := by simpa only [List.length_nil, Nat.zero_add] using hlen
      simpa only [word_nil, one_mul, he] using hpow
  | cons a l ih =>
      have hp := ih (n + 1) (by simp only [List.length_cons] at hlen; omega)
      have hd := hI a _ hp
      have he : E a (word F l * c₀ ^ (n + 1)) =
          ((n + 1 : ℕ) : A) * (word F (a :: l) * c₀ ^ n) := by
        rw [Derivation.leibniz, deriv_pow_succ, hEc,
          deriv_word_zero (E a) F (hEF a)]
        simp only [smul_eq_mul, mul_zero, add_zero, word_cons]
        ring
      rw [he] at hd
      exact cancel_nat_factor I (n + 1) (by omega) hd

/-- Shifted Cartan derivations replace all remaining zero centers.
Hits on prior A/center letters stay in the previous word-length span. -/
theorem mixed_word_mem {σ τ : Type*} (I : Ideal A) (F : σ → A) (G : τ → A)
    (c₀ : A) (H : τ → Derivation ℂ A A)
    (hI : ∀ b p, p ∈ I → H b p ∈ I) (hHc : ∀ b, H b c₀ = G b)
    (hHF : ∀ b a, ∃ c : A, ∃ a', H b (F a) = c * F a')
    (hHG : ∀ b d, ∃ c : A, ∃ d', H b (G d) = c * G d')
    (r : ℕ) (hpure : ∀ a : List σ, ∀ n, a.length + n = r → word F a * c₀ ^ n ∈ I)
    (a : List σ) (c : List τ) (n : ℕ) (hlen : a.length + c.length + n = r) :
    word F a * word G c * c₀ ^ n ∈ I := by
  have hall : ∀ h : ℕ, ∀ c : List τ, c.length = h → ∀ a : List σ, ∀ n,
      a.length + h + n = r → word F a * word G c * c₀ ^ n ∈ I := by
    intro h
    induction h with
    | zero =>
        intro c hc a n hn
        have he : c = [] := List.length_eq_zero_iff.mp hc
        subst c
        simpa only [word_nil, mul_one, Nat.add_zero] using hpure a n (by omega)
    | succ h ih =>
        intro c hc a n hn
        cases c with
        | nil => simp only [List.length_nil] at hc; omega
        | cons b c =>
            have hcl : c.length = h := by simp only [List.length_cons] at hc; omega
            have hp := ih c hcl a (n + 1) (by omega)
            have hd := hI b _ hp
            have ha : H b (word F a) * (word G c * c₀ ^ (n + 1)) ∈ I := by
              apply deriv_word_mul_mem I (H b) F (hHF b)
              intro a' ha'
              have hh := ih c hcl a' (n + 1) (by omega)
              convert hh using 1
              ring
            have hg : H b (word G c) * (word F a * c₀ ^ (n + 1)) ∈ I := by
              apply deriv_word_mul_mem I (H b) G (hHG b)
              intro c' hc'
              have hh := ih c' (by omega) a (n + 1) (by omega)
              convert hh using 1
              ring
            have hrow : ((n + 1 : ℕ) : A) * (word F a * word G (b :: c) * c₀ ^ n) ∈ I := by
              convert I.sub_mem (I.sub_mem hd ha) hg using 1
              simp only [Derivation.leibniz, deriv_pow_succ, hHc, smul_eq_mul, word_cons]
              ring
            exact cancel_nat_factor I (n + 1) (by omega) hrow
  exact hall c.length c rfl a n hlen

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.a_word_center_pow_mem
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.mixed_word_mem
