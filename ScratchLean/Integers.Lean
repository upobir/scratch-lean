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

-- TODO not field division
-- TODO floor division

-- converting nat subtraction to int subtraction
example (a b c d e f g h : ℕ) : a + b + c + d + e + f - b + g / h = a + c + d + e + f + g / h := by
  have : a + b + c + d + e + f ≥ b := by linarith
  zify [this]
  ring

-- TODO power

-- TODO inequality
