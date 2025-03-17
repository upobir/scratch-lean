import Mathlib

#check Int
#check ℤ

#check (0:ℤ)
#check Int.ofNat 0

#check -5
#check Int.negSucc 4

-- cast natural literal to int
#check (2:ℤ)
#check @OfNat.ofNat ℤ 2 _

-- cast natural variable to int
#check fun (n : ℕ) => (n : ℤ)
-- clamped cast int variable to natural
#check fun (x : ℤ) => x.toNat

-- if a property is true for nats it's true for ints greater than 5 (positive ints)
example (x : ℤ) (hx: 5 ≤ x) (P : ℤ → Prop) (h: ∀ n : ℕ, P n) : P x := by
  have hx_nat : x = x.toNat := by exact Eq.symm (Int.toNat_of_nonneg (by positivity))
  rw [hx_nat]
  exact h _

-- simple fact true in naturals iff true in integers
example (a b : ℕ) : a + b = b + a ↔ (a:ℤ) + b = b + a := by
  constructor
  . rintro h
    norm_cast   -- lowering type from int to nat
  . rintro h
    zify        -- lifting type to int from nat
    assumption

-- taking away int-ness from a expression of just nats
example (a b : ℕ) (h: a - (3:ℤ) = b - 3) : a = b := by
  have : (a:ℤ) = b := by linarith
  norm_cast at this

#check Int.neg
#eval -(-5)

#check Int.add
#eval 1 + (-2)

#check Int.sub
#eval (-2) - (-2)

#check Int.mul
#eval (-1) * 5

#check Int.ediv     -- there is also tdiv, fdiv
#eval -7 / -2
#eval -5 / 0

#check Int.pow
#eval -3 ^ 2
#eval (0:ℤ) ^ 0


-- calculation, -3 causes int
example : (2 + -3) * (5) + 5 = 0 := by
  norm_num

-- (a-b)^2 formula
example (a b :ℤ) : (a - b)^2 = a^2 - 2 * a * b + b^2 := by
  ring

-- multiple equation via linear formula
example (a b : ℤ) (h₁ : 2 * a + b = 10) (h₂ : a - 2 * b = 20) : a = 8 ∧ b = -6 := by
  constructor <;> linarith

-- impossible linear equation (linarith can't help for ints)
example (a b : ℤ) (h₁ : 2 * a + b = 10) (h₂ : a - 2 * b = 21) : False := by
  omega

-- linear equation solving
example (a : ℤ) (h: a^2 + 3 * a + 1 = -8 + 1 + a^2) : a = -3 := by
  linarith

-- "division" to cancel multiplication
example (a b : ℤ) (ha : a ≠ 0) (h: b + a * b = 2 * b + a - b ) : b = 1 := by
  have : b * a = 1 * a := by linarith
  exact (Int.mul_eq_mul_right_iff ha).mp this

-- handling denominator cancelling
example (a b : ℤ) (ha: a + 1 ≠ 1) (hb: b ≠ 0): (a * b + b) / b + 1 = a + 2 := by
  have : a ≠ 0 := by omega
  calc
    (a * b + b) / b + 1 = (a + 1) * b / b + 1 := by congr; ring
    _ = (a + 1) + 1 := by
      congr 1
      field_simp
    _ = _ := by ring

-- cancelling inside int division works for positive terms only
example (a : ℤ) (ha: a > 1) : (a^2 - 1) / (3 * (a-1)) = (a + 1) / 3 := by
  have : a - 1 > 0 := by linarith
  calc
    (a^2 - 1) / (3 * (a-1)) = (a+1) * (a-1) / (3 * (a-1)) := by ring_nf
    _ = (a+1) / 3 := by
      exact Int.mul_ediv_mul_of_pos_left (a + 1) 3 this

-- cancelling doesnt work for negative terms
#eval (10 * -2) / (7 * -2) = 10 / 7

-- using the fact that it's floor division, but note that it's euclidean division
example (x : ℤ)  : (7 * x - 1) / 7 = (-6 + 7*x) / 7 := by calc
  (7 * x - 1)/7 = (7 * x + -1) / 7 := by ring_nf
  _ = (7 * x) / 7 + -1 / 7 := by
    refine Int.add_ediv_of_dvd_left ?_
    omega
  _ = -6 / 7 + (7 * x) / 7 := by norm_num; ring
  _ = (-6 + 7 * x) / 7 := by
    refine (Int.add_ediv_of_dvd_right ?_).symm
    omega

-- converting nat subtraction to int subtraction
example (a b c d e f g h : ℕ) : a + b + c + d + e + f - b + g / h = a + c + d + e + f + g / h := by
  have : a + b + c + d + e + f ≥ b := by linarith
  zify [this]
  ring

-- power add and multiplications, nothing new from naturals
example (a d : ℤ) (b c : ℕ) : a^(2 * b + 3) + (a^c)^b + (a * d)^b = a^b * a^b * a^3 + a^(b * c) + a^b * d^b := by
  ring

-- power division, apparently no such theorem
example (a : ℤ) (ha : a ≠ 0) : a^(2 * x + 1) = a^(3 * x + 1) / a^x := by
  calc
    a^(2*x + 1) = a^(3*x + 1 - x) := by congr; omega
    _ = a^(3 * x + 1) / a^x := by
      generalize hu: 3 * x + 1 = u
      refine (Int.ediv_eq_of_eq_mul_left ?_ ?_).symm
      positivity
      calc
        a^u = a^((u-x) + x) := by congr; omega
        _ = _ := by ring

-- zeroness of powers
example (a : ℤ) (h: a ≠ 0) : a^n ≠ 0 := by simp [h]
example (a : ℤ) (h: a^n ≠ 0) (h': n ≠ 0) : a ≠ 0  := by exact ne_zero_pow h' h

-- taking "root"
example (a b : ℤ) (n : ℕ) (hn: n > 0) (h : a^n = b^n) : a = b ∨ a = -b := by
  have hor : n = 0 ∨ a = b ∨ (a = -b ∧ Even n ) :=  pow_eq_pow_iff_cases.mp h
  have hor := Or.resolve_left hor (by linarith: n ≠ 0)
  obtain h' | h' := hor
  all_goals simp [h']

-- square rooting is simpler
example (a : ℤ) (ha : a < 0) (h: a^2 = 64) : a = -8 := by
  convert_to a^2 = 8^2 at h
  have : a = 8 ∨ a = -8 := by exact sq_eq_sq_iff_eq_or_eq_neg.mp h
  obtain rfl | rfl := this
  all_goals linarith

-- taking "log" for positive base
example (a : ℤ) (n m : ℕ) (ha: a > 0) (ha': a ≠ 1) (h: a^n = a^m) : n = m := by
  exact (pow_right_inj₀ ha ha').mp h

-- taking "log" using the fact that a is not 1, -1 or 0
example (a : ℤ) (n m : ℕ) (ha'': a ≠ 0) (ha: a ≠ 1) (ha': a ≠ -1) (h: a^n = a^m) : n = m := by
  have : 1 < a.natAbs := by omega
  exact Int.pow_right_injective this h

-- trichotomy law for ints
example (x : ℤ) (h: x^2 ≠ 0) : 0 < x ∨ x < 0 := by
  obtain h' | h' | h' := Int.lt_trichotomy x 0
  . right; assumption
  . have : x^2 = 0 := by exact sq_eq_zero_iff.mpr h'
    contradiction
  . left; assumption


#check Int.NonNeg
#check Int.NonNeg (2:ℤ)
#check Int.NonNeg (-2)

#check Int.le
#eval -2 ≤ 1

#check Int.lt
#eval -2 < -1

-- inequalities working with linear arithmetic easily handled
example (x y : ℤ) (h₁ : 2*x + y ≤ -5) (h₂ : x - y ≤ y) : 3*x - y ≤ -5 := by
  linarith

-- some facts (like 0 < x → 1 ≤ x and y/2 ≤ 3 → y ≤ 7) require omega
example (x y : ℤ) (h₁ : 0 < x) (h₂: y / 2 ≤ 3) : (y ≤ x + 6) := by
  omega

-- even powers are nonnegative and positive multiplication in inequality
example (x y : ℤ) (h₁ : x + 2 < y + 1) : (x+1) * (x^8+1) < y * (x^8+1) := by
  have : 0 < x^8 + 1 := by positivity
  gcongr
  linarith

-- negative multiplication in inequality and odd powers retatining negativity
example (x y z : ℤ) (hz : z < 0) (h: x + y < z) : z^6 < z^5 * (x + y) := by
  calc
    z^6 = z^5 * z := by rfl
    _ < z^5 * (x + y) := by
      refine Int.mul_lt_mul_of_neg_left h ?_
      refine Odd.pow_neg ?_ hz
      dsimp [Odd]; use 2; norm_num
