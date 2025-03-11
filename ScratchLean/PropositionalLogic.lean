import Mathlib

#check Prop
#check True
#check False

/- implies is just a function -/
#check True → True

#check And
#check True ∧ True

#check Or
#check False ∨ True

#check Iff
#check False ↔ False

#check Not
#check ¬ False

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

-- p and q and r, prove r
example (p q r: Prop) (hpqr : p ∧ q ∧ r) : r := by
  obtain ⟨hp, hq, hr⟩ := hpqr
  exact hr

-- from p, p implies q, q implies r, r implies t you can prove q and t
example (p q r t: Prop) (hp: p) (hpq : p → q) (hqr : q → r) (hrt: r → t) : q ∧ t ∧ r := by
  have hq : q := hpq hp
  have hr : r := hqr hq
  have ht : t := hrt hr
  exact ⟨hq, ht, hr⟩

/- caseworking -/
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

-- p or q implies q or p
example (p q : Prop) : p ∨ q →  q ∨ p := by
  rintro (hp | hq)
  . right; assumption
  . left; assumption

-- p, not p prove False
example (p : Prop) (hp: p) (hnp: ¬p) : False := by
  contradiction

-- not p, p or q prove q
example (p q : Prop) (hnp : ¬ p) (hpq : p ∨ q) : q := by
  exact Or.resolve_left hpq hnp

/- iff rewriting -/
-- p iff q, r implies not (p or s) prove r implies not (q or s)
example (p q r s: Prop) (hpq : p ↔ q) (hqr: r → ¬ (p ∨ s)) : r → ¬ (q ∨ s) := by
  rw [← hpq]
  assumption

-- p iff q, r iff s, p, s prove q and r
example (p q r s : Prop) (hpq: p ↔ q) (hqr : r ↔ s) (hp: p) (hs: s) : q ∧ r := by
  constructor
  . exact hpq.mp hp
  . exact hqr.mpr hs

-- p, p implies q, q implies r and s and t, then t is true
example (p q r s t : Prop) (hp : p) (hpq : p → q) (hqrst: q → r ∧ s ∧ t) : t := by
  suffices hrst: r ∧ s ∧ t by
    exact hrst.right.right
  apply hqrst
  apply hpq
  assumption

/- de morgans law -/
-- not (p and q or not r), p, not q implies s proves r and s
set_option push_neg.use_distrib true
example (p q r s : Prop) (h: ¬((p ∧ q) ∨ ¬r)) (hp : p) (hqs : ¬ q → s) : r ∧ s := by
  push_neg at h
  obtain ⟨hpq, hr⟩ := h
  have hnq: ¬ q := Or.neg_resolve_left hpq hp
  have hs: s := by exact hqs hnq
  exact ⟨hr, hs⟩

-- p iff q, q proves not not p
example (p q: Prop) (hpq : p ↔ q) (hq: q) : ¬¬p := by
  push_neg
  rw [hpq]
  assumption

/- contradiction -/
-- p implies q, not q proves not p
example (p q : Prop) (hpq : p → q) (hnq: ¬q) : ¬p := by
  by_contra hp
  exact absurd (hpq hp) (hnq)

/- contrapositive -/
-- p implies not q, not p implies q proves p iff not q
example (p q : Prop) (h₁ : p → ¬q) (h₂ : ¬ p → q) : p ↔ ¬ q := by
  constructor
  . assumption
  . contrapose
    push_neg
    assumption

/- law of excluded middle -/
-- p implies q iff r, not p implies r iff q, proves q iff r
example (p q r : Prop) (hp: p → (q ↔ r)) (hnp: ¬ p → (r ↔ q)) : q ↔ r := by
  by_cases h: p
  . exact hp h
  . exact (hnp h).symm
