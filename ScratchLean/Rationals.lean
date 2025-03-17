import Mathlib

#check Rat
#check ℚ

#check (2: ℚ)
#check Rat.mk' 2 1 (by norm_num: 1 ≠ 0) (by norm_num: Nat.Coprime (Int.natAbs 2) 1)

#check (3/2:ℚ)
#check ({num := 3, den := 2, den_nz := by norm_num, reduced := by norm_num}:ℚ)

-- cast natural or int to rat
#check (2:ℚ)
#check @OfNat.ofNat ℚ 2

#check ((-2:ℤ):ℚ)
#check @IntCast.intCast ℚ inferInstance (-2)

-- forcing a rat to nat or int is basically doing a normcast
example (a : ℕ) (b: ℚ) (hab: a = b) (P : ℚ → ℚ → Prop) (h: ∀ n: ℕ, ∀ m: ℤ, P n m) : P b b := by
  rw [← hab]
  have := h a a
  norm_num at this
  assumption

-- normast can utilize divisibility
example (a : ℕ) (b : ℕ) (h: b ∣ a) : ↑(a / b) = (a: ℚ)/ b := by
  norm_cast

#check Rat.normalize
#eval Rat.normalize 10 4

#check Rat.neg
#eval -(1:ℚ)/2

#check Rat.add
#eval (1:ℚ)/2 + 1/3

#check Rat.sub
#eval (1:ℚ)/3 - 1/2

#check Rat.mul
#eval ((10/3):ℚ) * ((9/4):ℚ)

#check Rat.inv
#eval ((-5/4):ℚ)⁻¹
#eval (0⁻¹:ℚ)

#check Rat.div
#eval ((10/3):ℚ) / ((-4/9):ℚ)

-- evaluation of just values is easy
example : (1 / 3 + 1 / 2) * 1 / 5 / 6⁻¹ = (1:ℚ) := by
  norm_num

-- +,-,* can be handled by ring and ring_nf
example (a b : ℚ) : a + b * 3 + a - b^2 = 3*b + 2*a -b*b := by ring

-- working with division may require non-zeroness
example (a b : ℚ) (ha : a ≠ 0) (hb: b ≠ 0) : 1 / a + 1 / b = (a + b)/(a * b) := by
  field_simp
  ring

-- cancelling division requires field_simp
example (x : ℚ) (h: x ≠ 1) : (x^2 - 1) / (x - 1) = x+1 := by
  have : x - 1 ≠ 0 := by
    by_contra h'
    have : x = 1 := by linarith
    rw [this] at h
    norm_num at h
  field_simp
  ring

-- since rationals are monoid with multiplication, power is defined in a generic way
#check @Monoid.toNatPow ℚ (inferInstance)
#eval (3/2:ℚ)^2

#check @DivInvMonoid.toZPow ℚ
#eval (3/2:ℚ)^(-2:ℤ)


-- power add and multiplications, for nat same as before, for int, different, also note how powers seem to become nat
example (a d : ℚ) (b c : ℤ) (ha: a ≠ 0) : a^(2 * b + 3) + (a^c)^b + (a * d)^b = a^b * a^b * a^3 + a^(b * c) + a^b * d^b := by
  congr 2
  . calc
      a^(2*b+3) = a^(2*b) * a^(3:ℤ) := by exact zpow_add₀ ha (2*b) 3
      _ = a^(b*2) * a^3 := by ring_nf; norm_cast
      _ = (a^b)^2 * a^3 := by rw [zpow_mul]; norm_cast
      _ = a^b * a^b * a^3 := by ring
  . exact Eq.symm (zpow_mul' a b c)
  . exact mul_zpow a d b

-- power division is tricky, I suggest convert powers to int
example (a : ℚ) (b c : ℕ) (d e : ℤ) (ha: a ≠ 0) (hbc: c ≤ b) : a^(b-c) + a^d/a^e = a^b/a^c + a^(d-e) := by
  congr
  . convert_to a^((b:ℤ)-c) = a^(b:ℤ) / a^(c:ℤ) using 0
    . norm_cast
    . rw [zpow_sub₀ ha]
  . rw [zpow_sub₀ ha]

-- zeroness of power is same as int

-- TODO root, log, inequalities
