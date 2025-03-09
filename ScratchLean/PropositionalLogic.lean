import Mathlib

#check Prop
#check And
#check Or
#check Iff
#check Not

-- p implies p
example (p : Prop) : p → p := by
  intro hp
  exact hp

-- p implies q implies p
example (p q : Prop) : p → q → p := by
  intro hp hq
  assumption

-- from p, p implies q you can prove q
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  exact hpq hp

-- from p, q, you can prove p and q
example (p q : Prop) (hp: p) (hq: q) : p ∧ q := by
  constructor
  . exact hp
  . exact hq

-- from p, p implies q, q implies r, r implies t you can prove q and t
example (p q r t: Prop) (hp: p) (hpq : p → q) (hqr : q → r) (hrt: r → t) : q ∧ t ∧ r := by
  have hq : q := hpq hp
  have hr : r := hqr hq
  have ht : t := hrt hr
  exact ⟨hq, ht, hr⟩

-- p implies q or r or s or t
-- q implies u
-- r or s implies u
-- t implies that t implies p implies u
-- all above prove p implies u
example (p q r s t u: Prop) (h₁: p → (q ∨ r ∨ s ∨ t)) (h₂: q → u) (h₃ : (r ∨ s) → u) (h₄: t → (t → p) → u) : p → u := by
  intro hp
  have hqrst : q ∨ r ∨ s ∨ t := by exact h₁ hp
  obtain hq | hr | hs | ht := hqrst
  . exact h₂ hq
  . apply h₃
    left
    assumption
  . apply h₃
    right
    assumption
  . have htpu : (t → p) → u := by exact h₄ ht
    apply htpu
    intro ht'
    assumption

-- p, not p prove False
example (p : Prop) (hp: p) (hnp: ¬p) : False := by
  contradiction

-- not p, p or q prove q
example (p q : Prop) (hnp : ¬ p) (hpq : p ∨ q) : q := by
  exact Or.resolve_left hpq hnp

-- p iff q, r implies not (p or s) prove r implies not (q or s)
example (p q r s: Prop) (hpq : p ↔ q) (hqr: r → ¬ (p ∨ s)) : r → ¬ (q ∨ s) := by
  rw [← hpq]
  assumption

-- p iff q, r iff s, p, s prove q and r
example (p q r s : Prop) (hpq: p ↔ q) (hqr : r ↔ s) (hp: p) (hs: s) : q ∧ r := by
  constructor
  . exact hpq.mp hp
  . exact hqr.mpr hs
