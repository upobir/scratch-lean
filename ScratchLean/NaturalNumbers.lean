import Mathlib

#check Nat
#check ℕ
#check Nat.succ
#check Nat.pred

#check 0
#eval Nat.succ 0
#eval Nat.pred 0

#check 2
#eval Nat.succ 2
#eval Nat.pred 2

-- successor's predecessor is self
example (x: ℕ) : (x.succ).pred = x := by rfl

-- predecessor's successor is not always self
example : ¬ (∀ x: ℕ, (x.pred).succ = x) := by
  push_neg
  use 0
  simp

#check Nat.add
#eval 3 + 2

#check Nat.sub
#eval 3 - 2
#eval 2 - 3

#check Nat.mul
#eval 2 * 3

#check Nat.div
#eval 4 / 2
#eval 4 / 3
#eval 4 / 0

#check Nat.pow
#eval 3 ^ 2
#eval 0 ^ 0

-- a calculation
example : (3 + 2 * 3 - 10 + 5)/4 = 1 := by
  norm_num

-- a plus b squared formula
example (a b : ℕ) : (a + b)^2 = a^2 + 2 * a * b + b^2 := by
  ring

-- handling division
example (a b : ℕ) : (a^2 + 3 + 2) / (b + 1) + 1 = (6 + a*a  + b) / (1 + b) := by
  have : 0 < b + 1 := by positivity
  rw [← Nat.add_mul_div_left _ _ this]
  ring_nf

-- linear manipulations
example (a : ℕ) (h: 3 * a^2 - 9 = 0) (h': a^2 - 3 = 5) : False := by
  omega

-- handling subtraction
example (a : ℕ) : (a + 1) * (b + 1) - 1 = a * b + a + b := by
  ring_nf
  omega

-- solving linear equation
example (x : ℕ) (h : 3 * x - 2 = 10) : x = 4 := by
  omega

-- algebra with minus and denominator cancelling
example (x : ℕ) (hx : 0 < x) : (x^2 - 1) / (x + 1) = x - 1 := by
  have h_sq_minus : x^2 - 1 = (x-1) * (x + 1) := by
    calc
      x^2 - 1 = ((x-1) + 1)^2 - 1 := by
        congr; omega
      _ = (x-1)^2 + 2 * (x-1) + 1 - 1 := by ring_nf
      _ = (x-1)^2 + 2*(x-1) := by simp
      _ = (x-1) * ((x-1) + 2) := by ring
      _ = (x-1) * (x+1) := by
        congr 1; omega
  calc
    (x^2 - 1) / (x + 1) = (x - 1) * (x + 1) / (x + 1) := by rw [h_sq_minus]
    _ = x - 1 := by field_simp

-- properties that follow floor division
example (x : ℕ) : 2 * (7 * x + 1) / 7 = (14 * x + 5) / 7 := by
  ring_nf
  omega

-- division to 0
example (x :ℕ) (h: 2 < x) : 1 / x = 2 / x := by
  calc
    1 / x = 0 := by refine Nat.div_eq_of_lt ?_; omega
    _ = 2 / x := by refine (Nat.div_eq_of_lt ?_).symm; omega

-- division equality for abnormal case, using division to 0
example (x y : ℕ) (h: 3 < y) : (x * y + y + 1)/y = 1 + (x * y + 2)/y := by
  have : y > 0 := by positivity
  calc
    (x * y + y + 1) / y = (1 + (x + 1) * y) / y := by ring_nf
    _ = 1 / y + (x + 1) := by
      exact Nat.add_mul_div_right 1 (x + 1) this
    _ = 0 + (x + 1) := by
      congr
      refine Nat.div_eq_of_lt ?_; omega
    _ = 2 / y + (x + 1) := by
      congr 1
      refine (Nat.div_eq_of_lt ?_).symm; omega
    _ = 1 + (2 / y + x) := by ring
    _ = 1 + (2 + x * y) / y := by congr; exact Eq.symm (Nat.add_mul_div_right 2 x this)
    _ =  1 + (x * y + 2)/y := by ring_nf

-- a^2 - b^2 formula
example (x y :ℕ) : x^2 - y^2 = (x + y) * (x - y) := by
  exact Nat.sq_sub_sq x y

-- power add and multiplication
example (a b c : ℕ) : a^(2 * b + 3) + (a^c)^b = a^b * a^b * a^3 + a^(b * c) := by
  ring

-- using the fact that a = 0 or a > 0 with power division
example (a b : ℕ) : a ^ (b + 2) / a ^ b = a ^ 2 := by
  obtain h | h := Nat.eq_zero_or_pos a
  . simp [h]
  . rw [Nat.pow_div]
    . congr 1; omega
    . simp
    . assumption

-- taking "root"
example (a : ℕ) (h: a ^ 5 = 32) : a = 2 := by
  convert_to a^5 = 2^5 at h
  refine (Nat.pow_left_inj ?_).mp h
  norm_num

-- taking "log"
example (a b c: ℕ) (h' : a > 10) (h : a^b = a^2 * a^c) : b = c + 2 := by
  convert_to a^b = a^(c + 2) at h
  . ring
  refine (Nat.pow_right_inj ?_).mp h
  linarith

#check Nat.pow_left_inj

#check Nat.le
#eval 1 ≤ 1
#eval 2 ≥ 1

#check Nat.lt
#eval 1 < 2
#eval 2 > 1

-- calculatable inequality
example : 1 + 2 * 3 < (10 - 2) * 2 := by norm_num

-- simple linear inequality
example (k : ℕ) : 2 * k < 3 * k + 1 := by omega

-- multiple linear inequality
example (a b : ℕ) (h: a ≤ 3 * b + 1) (h': 2 * b < 5) : a + b ≤ 10 := by omega

-- proving positivness by proving necessary parts first
example (a b : ℕ) (h: a > 3) : (a-3) * (b + 1) > 0 := by
  have : a - 3 > 0 := by omega
  positivity

-- squeezing between bounds
example (a : ℕ) (h₁ : 3 < 2 * a) (h₂ : a < 2) : a = 2 := by omega

-- multiplication of variables in inequality
example (a b : ℕ) (h: a > 0) (h: a * b + a + 1 ≤ a^2 + 1) : b + 1 ≤ a := by
  simp at h
  calc
    b + 1 = (b+1) * a / a := by field_simp
    _ = (a * b + a) / a := by ring_nf
    _ ≤ a*a / a := by
      gcongr
      convert h using 1
      ring
    _ = a := by field_simp

-- inequality requiring multiplication and linear manipulation
example (a b c : ℕ) (h₁: a + c ≤ 10) (h₂: 1 ≤ b + c) : a * b + c ≤ 10 * b + c^2 := by
  have : a * b + c * b ≤ 10 * b := by
    calc
      a * b + c * b = (a + c) * b := by ring
      _ ≤ 10 * b := by gcongr
  have : c ≤ c * b + c * c := by
    calc
      c = c * 1 := by ring
      _ ≤ c * (b + c) := by gcongr
      _ = c * b + c * c := by ring
  convert_to a * b + c ≤ 10 * b + c * c
  . congr
    ring
  . omega

-- difficult inequality due to floor division by numerals
example (x : ℕ) (h: 3 < x) : x / 3 < x / 2 := by
  omega

-- a powerful division theorem a ≤ b, c ≤ d with c ≠ 0 means a / d ≤ b / c
example (x y : ℕ) (h: y < x) (h': y ≠ 0) : 100 / x ≤ 100 / y := by
  refine Nat.div_le_div ?_ ?_ ?_
  . norm_num
  . omega
  . assumption

-- power related ineq chaining
example (a n : ℕ) (h: a > 3) (h': n > 0) : a ^ n > 3 := by
  calc
    a^n > 3^n := by
      refine Nat.pow_lt_pow_left h ?_
      positivity
    _ ≥ 3^1 := by
      refine Nat.pow_le_pow_right ?_ h'
      norm_num
    _ = 3 := by norm_num

-- zero ness from power
example (a n : ℕ) (h: a ≠ 0) : a^n ≠ 0 := by simp [h]
example (a n : ℕ) (h': n ≠ 0) (h: a^n ≠ 0) : a ≠ 0 := by exact ne_zero_pow h' h
