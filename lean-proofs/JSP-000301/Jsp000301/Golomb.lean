/-!
# JSP-000301 — Golomb's counterexample

Catalog question (problems/catalog-0301-0400.md, JSP-000301):

  If two consecutive positive integers are powerful, must at least one be a
  perfect square?

Answer: no. Solomon W. Golomb, "Powerful numbers", Amer. Math. Monthly 77(8)
(1970), 848–852, recorded the pair

  12167 = 23^3
  12168 = 2^3 * 3^2 * 13^2

These are consecutive. A positive integer is powerful when every exponent in
its prime factorization is at least 2. Neither integer is a square: both lie
strictly between 110^2 = 12100 and 111^2 = 12321.

This file formalizes only that catalog-scoped counterexample. It does not
address the separate counting / infinitude question (Erdős problem #365).

Closed numeric checks use the kernel-checked `decide` tactic. `native_decide`
is not used. There is no Mathlib dependency.
-/

-- The divisor screens below reduce a few thousand concrete `Nat` checks.
-- `maxRecDepth` covers `List.range`'s recursive loop; `maxHeartbeats`
-- turns off the elaborator fuel limit for those closed `decide` proofs.
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Jsp000301

/-- `n` is a perfect square. -/
def IsSquare (n : Nat) : Prop := ∃ k : Nat, k * k = n

/-- `p` is prime: it is greater than 1 and has no proper divisor. -/
def IsPrime (p : Nat) : Prop :=
  1 < p ∧ ∀ d : Nat, 1 < d → d < p → ¬ d ∣ p

/-- A positive integer is powerful when every prime divisor has exponent at
least 2, written as `p ∣ n → p^2 ∣ n`. -/
def Powerful (n : Nat) : Prop :=
  ∀ p : Nat, IsPrime p → p ∣ n → p ^ 2 ∣ n

/-- Boolean screen: `1 < p` and no `d` with `1 < d < p` divides `p`. -/
def isPrimeBool (p : Nat) : Bool :=
  decide (1 < p) &&
    ((List.range p).all fun d => decide (d ≤ 1) || decide (p % d ≠ 0))

theorem isPrimeBool_sound {p : Nat} (h : isPrimeBool p = true) : IsPrime p := by
  unfold isPrimeBool at h
  rw [Bool.and_eq_true_iff] at h
  obtain ⟨hgt, hall⟩ := h
  refine ⟨of_decide_eq_true hgt, ?_⟩
  intro d hd1 hdlt hdiv
  have hmem : d ∈ List.range p := List.mem_range.mpr hdlt
  have hcond : (decide (d ≤ 1) || decide (p % d ≠ 0)) = true :=
    (List.all_eq_true.mp hall) d hmem
  rw [Bool.or_eq_true_iff] at hcond
  cases hcond with
  | inl hle =>
    exact absurd (of_decide_eq_true hle) (Nat.not_le_of_gt hd1)
  | inr hmod =>
    exact (of_decide_eq_true hmod) (Nat.mod_eq_zero_of_dvd hdiv)

theorem isPrimeBool_complete {p : Nat} (hp : IsPrime p) : isPrimeBool p = true := by
  unfold isPrimeBool
  rw [Bool.and_eq_true_iff]
  refine ⟨decide_eq_true hp.1, ?_⟩
  rw [List.all_eq_true]
  intro d hd
  rw [List.mem_range] at hd
  rw [Bool.or_eq_true_iff]
  by_cases hle : d ≤ 1
  · exact Or.inl (decide_eq_true hle)
  · have hd1 : 1 < d := Nat.gt_of_not_le hle
    have hnd : ¬ d ∣ p := hp.2 d hd1 hd
    have hmod : p % d ≠ 0 := fun hzero => hnd (Nat.dvd_of_mod_eq_zero hzero)
    exact Or.inr (decide_eq_true hmod)

/-- Primality of the four primes appearing in Golomb's factorizations,
proved by checking that none of `2, …, p - 1` divides `p`. -/
theorem prime_2 : IsPrime 2 := isPrimeBool_sound (by decide)
theorem prime_3 : IsPrime 3 := isPrimeBool_sound (by decide)
theorem prime_13 : IsPrime 13 := isPrimeBool_sound (by decide)
theorem prime_23 : IsPrime 23 := isPrimeBool_sound (by decide)

/-- Positive divisors of `n`, in increasing order. -/
def positiveDivisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun d => (d != 0) && (n % d == 0)

theorem mem_positiveDivisors_of_dvd {n d : Nat} (hn : 0 < n) (hd : 0 < d) (h : d ∣ n) :
    d ∈ positiveDivisors n := by
  have hle : d ≤ n := Nat.le_of_dvd hn h
  have hlt : d < n + 1 := Nat.lt_succ_of_le hle
  unfold positiveDivisors
  rw [List.mem_filter, List.mem_range]
  refine ⟨hlt, ?_⟩
  show ((d != 0) && (n % d == 0)) = true
  rw [Bool.and_eq_true_iff]
  exact ⟨decide_eq_true (Nat.ne_of_gt hd), decide_eq_true (Nat.mod_eq_zero_of_dvd h)⟩

theorem mem_primeDivisorScreen {n p : Nat} (hn : 0 < n) (hp : IsPrime p) (hdiv : p ∣ n) :
    p ∈ (positiveDivisors n).filter fun d => isPrimeBool d := by
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp.1
  have hmem : p ∈ positiveDivisors n := mem_positiveDivisors_of_dvd hn hp0 hdiv
  have hbool : isPrimeBool p = true := isPrimeBool_complete hp
  exact List.mem_filter.mpr ⟨hmem, hbool⟩

/-- The only prime divisor of `12167` is `23`. -/
theorem primeDivisors_12167 :
    ((positiveDivisors 12167).filter fun d => isPrimeBool d) = [23] := by
  decide

/-- The only prime divisors of `12168` are `2`, `3` and `13`. -/
theorem primeDivisors_12168 :
    ((positiveDivisors 12168).filter fun d => isPrimeBool d) = [2, 3, 13] := by
  decide

/-- Explicit prime-power factorization, evaluated left to right. -/
def evalFactors : List (Nat × Nat) → Nat
  | [] => 1
  | (p, e) :: rest => p ^ e * evalFactors rest

/-- Every exponent in a factorization is at least `k`. -/
def AllExponentsAtLeast (fs : List (Nat × Nat)) (k : Nat) : Prop :=
  ∀ p e, (p, e) ∈ fs → k ≤ e

/-- Every base in a factorization is prime. -/
def AllBasesPrime (fs : List (Nat × Nat)) : Prop :=
  ∀ p e, (p, e) ∈ fs → IsPrime p

theorem sq_dvd_pow {p e : Nat} (he : 2 ≤ e) : p ^ 2 ∣ p ^ e := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le he
  rw [hk, Nat.pow_add]
  exact ⟨p ^ k, rfl⟩

theorem eval_12167 : evalFactors [(23, 3)] = 12167 := by
  decide

theorem eval_12168 : evalFactors [(2, 3), (3, 2), (13, 2)] = 12168 := by
  decide

theorem exponents_12167 : AllExponentsAtLeast [(23, 3)] 2 := by
  intro p e hmem
  rcases List.mem_cons.mp hmem with h | h
  · rcases h with ⟨rfl, rfl⟩
    decide
  · cases h

theorem exponents_12168 : AllExponentsAtLeast [(2, 3), (3, 2), (13, 2)] 2 := by
  intro p e hmem
  rcases List.mem_cons.mp hmem with h | hmem
  · rcases h with ⟨rfl, rfl⟩
    decide
  · rcases List.mem_cons.mp hmem with h | hmem
    · rcases h with ⟨rfl, rfl⟩
      decide
    · rcases List.mem_cons.mp hmem with h | hmem
      · rcases h with ⟨rfl, rfl⟩
        decide
      · cases hmem

theorem bases_12167 : AllBasesPrime [(23, 3)] := by
  intro p e hmem
  rcases List.mem_cons.mp hmem with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact prime_23
  · cases h

theorem bases_12168 : AllBasesPrime [(2, 3), (3, 2), (13, 2)] := by
  intro p e hmem
  rcases List.mem_cons.mp hmem with h | hmem
  · rcases h with ⟨rfl, rfl⟩
    exact prime_2
  · rcases List.mem_cons.mp hmem with h | hmem
    · rcases h with ⟨rfl, rfl⟩
      exact prime_3
    · rcases List.mem_cons.mp hmem with h | hmem
      · rcases h with ⟨rfl, rfl⟩
        exact prime_13
      · cases hmem

/-- The recorded factorizations: the products recover the two integers, every
exponent is at least 2, and every base is prime. -/
theorem factorization_12167 :
    evalFactors [(23, 3)] = 12167 ∧
      AllExponentsAtLeast [(23, 3)] 2 ∧
      AllBasesPrime [(23, 3)] :=
  ⟨eval_12167, exponents_12167, bases_12167⟩

theorem factorization_12168 :
    evalFactors [(2, 3), (3, 2), (13, 2)] = 12168 ∧
      AllExponentsAtLeast [(2, 3), (3, 2), (13, 2)] 2 ∧
      AllBasesPrime [(2, 3), (3, 2), (13, 2)] :=
  ⟨eval_12168, exponents_12168, bases_12168⟩

theorem powerful_12167 : Powerful 12167 := by
  intro p hp hdiv
  have hmem := mem_primeDivisorScreen (n := 12167) (by decide) hp hdiv
  rw [primeDivisors_12167] at hmem
  have hp23 : p = 23 := List.eq_of_mem_singleton hmem
  subst hp23
  have hpack := factorization_12167
  have hexp : 2 ≤ 3 := hpack.2.1 23 3 List.mem_cons_self
  have hfac : evalFactors [(23, 3)] = 12167 := hpack.1
  have _primeBase : IsPrime 23 := hpack.2.2 23 3 List.mem_cons_self
  -- `evalFactors [(23, 3)]` is definitionally `23 ^ 3 * 1`.
  have hpow : 23 ^ 2 ∣ 23 ^ 3 * 1 := Nat.dvd_mul_right_of_dvd (sq_dvd_pow hexp) _
  exact hfac ▸ hpow

theorem powerful_12168 : Powerful 12168 := by
  intro p hp hdiv
  have hmem := mem_primeDivisorScreen (n := 12168) (by decide) hp hdiv
  rw [primeDivisors_12168] at hmem
  have hpack := factorization_12168
  have hfac : evalFactors [(2, 3), (3, 2), (13, 2)] = 12168 := hpack.1
  have he2 : 2 ≤ 3 := hpack.2.1 2 3 List.mem_cons_self
  have he3 : 2 ≤ 2 :=
    hpack.2.1 3 2 (List.mem_cons_of_mem _ List.mem_cons_self)
  have he13 : 2 ≤ 2 :=
    hpack.2.1 13 2
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have _primeBases : IsPrime 2 ∧ IsPrime 3 ∧ IsPrime 13 :=
    ⟨hpack.2.2 2 3 List.mem_cons_self,
      hpack.2.2 3 2 (List.mem_cons_of_mem _ List.mem_cons_self),
      hpack.2.2 13 2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  -- `evalFactors [(2, 3), (3, 2), (13, 2)]` is definitionally
  -- `2 ^ 3 * (3 ^ 2 * (13 ^ 2 * 1))`.
  rcases List.mem_cons.mp hmem with rfl | hmem
  · have h2 : 2 ^ 2 ∣ 2 ^ 3 * (3 ^ 2 * (13 ^ 2 * 1)) :=
      Nat.dvd_mul_right_of_dvd (sq_dvd_pow he2) _
    exact hfac ▸ h2
  · rcases List.mem_cons.mp hmem with rfl | hmem
    · have h3core : 3 ^ 2 ∣ 3 ^ 2 := sq_dvd_pow he3
      have h3mid : 3 ^ 2 ∣ 3 ^ 2 * (13 ^ 2 * 1) := Nat.dvd_mul_right_of_dvd h3core _
      have h3 : 3 ^ 2 ∣ 2 ^ 3 * (3 ^ 2 * (13 ^ 2 * 1)) := Nat.dvd_mul_left_of_dvd h3mid _
      exact hfac ▸ h3
    · have hp13 : p = 13 := List.eq_of_mem_singleton hmem
      subst hp13
      have h13core : 13 ^ 2 ∣ 13 ^ 2 * 1 := Nat.dvd_mul_right_of_dvd (sq_dvd_pow he13) _
      have h13mid : 13 ^ 2 ∣ 3 ^ 2 * (13 ^ 2 * 1) := Nat.dvd_mul_left_of_dvd h13core _
      have h13 : 13 ^ 2 ∣ 2 ^ 3 * (3 ^ 2 * (13 ^ 2 * 1)) := Nat.dvd_mul_left_of_dvd h13mid _
      exact hfac ▸ h13

/-- Squares are monotone: `a ≤ b` implies `a^2 ≤ b^2`. -/
theorem square_mono {a b : Nat} (h : a ≤ b) : a * a ≤ b * b :=
  Nat.mul_le_mul h h

/-- A natural number strictly between two consecutive squares is not a square. -/
theorem not_square_of_consecutive_bounds {n lo : Nat}
    (hlo : lo * lo < n) (hhi : n < (lo + 1) * (lo + 1)) : ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  cases Nat.lt_or_ge k (lo + 1) with
  | inl hklt =>
    have hkle : k ≤ lo := Nat.lt_succ_iff.mp hklt
    have hsq : k * k ≤ lo * lo := square_mono hkle
    rw [hk] at hsq
    exact Nat.not_le_of_gt hlo hsq
  | inr hkge =>
    have hsq : (lo + 1) * (lo + 1) ≤ k * k := square_mono hkge
    rw [hk] at hsq
    exact Nat.not_le_of_gt hhi hsq

theorem square_110 : 110 * 110 = 12100 := by
  decide

theorem square_111 : 111 * 111 = 12321 := by
  decide

theorem not_square_12167 : ¬ IsSquare 12167 := by
  have hlo : 110 * 110 < 12167 := by decide
  have hhi : 12167 < 111 * 111 := by decide
  have hsucc : (111 : Nat) = 110 + 1 := rfl
  rw [hsucc] at hhi
  exact not_square_of_consecutive_bounds hlo hhi

theorem not_square_12168 : ¬ IsSquare 12168 := by
  have hlo : 110 * 110 < 12168 := by decide
  have hhi : 12168 < 111 * 111 := by decide
  have hsucc : (111 : Nat) = 110 + 1 := rfl
  rw [hsucc] at hhi
  exact not_square_of_consecutive_bounds hlo hhi

/-- Negation of the catalog question, witnessed by Golomb's pair: `12167` and
`12168` are consecutive powerful positive integers, and neither is a square. -/
theorem jsp_000301 :
    ∃ a b : Nat,
      a = 12167 ∧
      b = 12168 ∧
      0 < a ∧
      0 < b ∧
      b = a + 1 ∧
      Powerful a ∧
      Powerful b ∧
      ¬ IsSquare a ∧
      ¬ IsSquare b := by
  refine ⟨12167, 12168, rfl, rfl, ?_, ?_, ?_, powerful_12167, powerful_12168,
      not_square_12167, not_square_12168⟩
  · decide
  · decide
  · rfl

end Jsp000301
