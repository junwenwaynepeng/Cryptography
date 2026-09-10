import Cryptography.Basic

/-
Lemma (divisibility is transitive). Let a, b, and c be integers.
If a divides b and b divides c, then a divides c.

Proof.
  By the definition of divisibility, there are integers k and l such
  that b = ak and c = bl. To show that a divides c, we must find an
  integer m such that c = am.

  Choose m = kl. Then:
    c = bl, by the definition of l,
      = (ak)l, using b = ak,
      = a(kl), by associativity of multiplication.
-/

lemma dvd_is_trans -- Lean already has this theorem; it uses dvd_trans.
    {a b c : ℤ} (a_divid_b : a ∣ b) (b_divid_c : b ∣ c) :
    a ∣ c := by
  change ∃ k : ℤ, b = a * k at a_divid_b
  change ∃ l : ℤ, c = b * l at b_divid_c
  change ∃ m : ℤ, c = a * m
  obtain ⟨k, hk⟩ := a_divid_b
  obtain ⟨l, hl⟩ := b_divid_c
  use k * l
  calc
    c = b * l := hl
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by rw [mul_assoc]

/-
Lemma (divisibility in both directions). Let a and b be integers. If a
divides b and b divides a, then a = b or a = -b.

Proof.
  Since a divides b and b divides a, there are integers k and l such that
    b = a * k and a = b * l.

  If a = 0, then b = 0, so a = b.

  If a is not zero, substitute b = a * k into a = b * l. This gives
    a * (k * l) = a.
  Since a is not zero, cancel a to get k * l = 1. Therefore, either
  k = 1 and l = 1, or k = -1 and l = -1. In the first case, a = b;
  in the second case, a = -b.
-/
lemma dvd_antisymm_up_to_sign
    {a b : ℤ}
    (hab : a ∣ b)
    (hba : b ∣ a) :
    a = b ∨ a = -b := by
  change ∃ k : ℤ, b = a * k at hab
  change ∃ l : ℤ, a = b * l at hba
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hba
  by_cases ha : a = 0
  · -- Case 1 : a = 0
    have hb : b = 0 := by
      calc
        b = a * k := by exact hk
        _ = 0 * k := by rw [ha]
        _ = 0 := by simp
    rw[ha, hb]
    simp
  · -- Case 2 : a ≠ 0
    have hkl : k * l = 1 := by
      have preh : a * (k * l) = a * 1 := by
        simpa [hk, mul_assoc] using hl.symm
      apply mul_left_cancel₀ ha preh
    have h : ((k = 1 ∧ l = 1) ∨ (k = -1 ∧ l = -1)) := by
      exact Int.eq_one_or_neg_one_of_mul_eq_one' hkl
    obtain hpos | hneg := h
    · left
      obtain ⟨k1, l1⟩ := hpos
      calc
        a = b * l := by exact hl
        _ = b * 1 := by rw [l1]
        _ = b := by ring
    · right
      obtain ⟨kneg1, lneg1⟩ := hneg
      calc
        a = b * l := by exact hl
        _ = b * -1 := by rw [lneg1]
        _ = -b := by ring

/-
Theorem (linear combinations of divisible integers). Let a, b, and d be
integers. If d divides a and d divides b, then d divides every integer
linear combination r * a + s * b, where r and s are integers.

Proof.
  Since d divides a and d divides b, there are integers k and l such that
  a = d * k and b = d * l. Given r and s, substitute these equalities into the linear
  combination and choose m = r * k + s * l. Then:
    r * a + s * b
      = r * (d * k) + s * (d * l)
      = d * (r * k + s * l),
  using commutativity and associativity of multiplication and
  distributivity of multiplication over addition. Therefore d divides
  r * a + s * b.
-/
lemma comm_dvd
    {a b d : ℤ} (d_divid_a : d ∣ a) (d_divid_b : d ∣ b) :
    ∀ r s : ℤ , d ∣ r * a + s * b := by
  change ∃ k : ℤ, a = d * k at d_divid_a
  change ∃ l : ℤ, b = d * l at d_divid_b
  obtain ⟨k, hk⟩ := d_divid_a
  obtain ⟨l, hl⟩ := d_divid_b
  intro r s
  change ∃ m : ℤ,  r * a + s * b = d * m
  use r * k + s * l
  calc
    r * a + s * b = r * (d * k) + s * (d * l) := by rw [hk, hl]
    _ = r * (k * d) + s * (l * d) := by rw [mul_comm k d, mul_comm d l]
    _ = (r * k) * d + (s * l) * d := by rw [mul_assoc, mul_assoc]
     _ = d * (r * k) +  d * (s * l) := by rw [mul_comm (r * k) d, mul_comm (s * l) d]
    _ = d * (r * k + s * l) := by rw [(mul_add d (r * k) (s * l)).symm]

  /-MAGIC word! You can avoid all of these computation by simply use the tacktic 'ring'
  Try:
  rw[hk, hl]
  ring
  -/

/-
Theorem (Euclidean step). Let a, b, q, r, and d be integers. If
a = b * q + r, then d divides both a and b if and only if d divides
both b and r. Consequently, the common divisors of a and b are exactly
the common divisors of b and r. In particular,
  gcd(a, b) = gcd(b, r).

Remark. This consequence follows immediately from the equivalence above,
so it does not require a separate proof here.

Proof.
  Suppose first that d divides a and b. Write a = d * l and b = d * m.
  We claim r = d * m if m = l - m * q.
  Since r = a - b * q, we have
    r = d * l - (d * m) * q
      = d * (l - m * q),
  Therefore, the claim follows.

  Conversely, suppose that d divides b and r. Write b = d * k and
  r = d * l.
  We claim a = d * m with m = k * q + l.
  Using a = b * q + r, we obtain
    a = (d * k) * q + d * l
      = d * (k * q + l),
  Therefore, the claim follows.
-/
theorem Euclidean_step
    {a b q r : ℤ} (h : a = b * q + r) :
    (d ∣ a ∧ d ∣ b) ↔ (d ∣ b ∧ d ∣ r) := by
  constructor --To prove P↔Q, we can instead prove P→Q and Q→P.
  · intro dab
    obtain ⟨d_divid_a, d_divid_b⟩ := dab
    constructor
    · exact d_divid_b
    · change ∃ k : ℤ, r = d * k
      change ∃ l : ℤ, a = d * l at d_divid_a
      change ∃ m : ℤ, b = d * m at d_divid_b
      obtain ⟨l, hl⟩ := d_divid_a
      obtain ⟨m, hm⟩ := d_divid_b
      use l - m * q
      calc
        r = a - b * q := by rw [h]; ring
        _ = d * l - d * m * q := by rw[hl, hm]
        _ = d * (l - m * q) := by ring
  · intro dab
    obtain ⟨d_divid_b, d_divid_r⟩ := dab
    constructor
    · change ∃ k : ℤ, b = d * k at d_divid_b
      change ∃ l : ℤ, r = d * l at d_divid_r
      change ∃ m : ℤ, a = d * m
      obtain ⟨k, hk⟩ := d_divid_b
      obtain ⟨l, hl⟩ := d_divid_r
      use k * q + l
      calc
        a = b * q + r := by exact h
        _ = (d * k) * q + d * l := by rw [hk, hl]
        _ = d * (k * q + l) := by ring
    · exact d_divid_b
