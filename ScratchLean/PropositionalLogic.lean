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

-- proving simple implication by introducing precondition and providing exact proof
example (p : Prop) : p → p := by
  intro hp
  exact hp

-- multiple introduction and then using "assumption"
example (p q : Prop) : p → q → p := by
  intro hp hq
  assumption

-- providing exact proof by using modus ponens on-spot
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  exact hpq hp

-- proving and by using constructor to bring separate goals
example (p q : Prop) (hp: p) (hq: q) : p ∧ q := by
  constructor
  . exact hp
  . exact hq

-- "destructure" and hypothesis
example (p q r: Prop) (hpqr : p ∧ q ∧ r) : r := by
  obtain ⟨hp, hq, hr⟩ := hpqr
  exact hr

-- establish intermediary facts and use shortcut notation to provide and proof
example (p q r t: Prop) (hp: p) (hpq : p → q) (hqr : q → r) (hrt: r → t) : q ∧ t ∧ r := by
  have hq : q := hpq hp
  have hr : r := hqr hq
  have ht : t := hrt hr
  exact ⟨hq, ht, hr⟩

-- "reverse proving", by using an implication to change goal to the precondition
example (p q r t: Prop) (hp: p) (hpq : p → q) (hqr : p → (q → r)) (hrt: r → t) : t := by
  apply hrt
  apply hqr hp
  apply hpq
  assumption

-- "destructure" a or to get separate cases and prove in each case
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

-- introduce assumption with destructuring and prove or by explicitly proving left or right terms
example (p q : Prop) : p ∨ q →  q ∨ p := by
  rintro (hp | hq)
  . right; assumption
  . left; assumption

-- proving False from contradictory propositions (i.e. P and not P)
example (p : Prop) (hp: p) (hnp: ¬p) : False := by
  contradiction

-- terms from left can be removed if not of that is proved
example (p q : Prop) (hnp : ¬ p) (hpq : p ∨ q) : q := by
  exact Or.resolve_left hpq hnp

-- sides of iff can be rewrited inside complex propositional expressions
example (p q r s: Prop) (hpq : p ↔ q) (hqr: r → ¬ (p ∨ s)) : r → ¬ (q ∨ s) := by
  rw [← hpq]
  assumption

-- use the implications inside iff for proof
example (p q r s : Prop) (hpq: p ↔ q) (hqr : r ↔ s) (hp: p) (hs: s) : q ∧ r := by
  constructor
  . exact hpq.mp hp
  . exact hqr.mpr hs

-- change goal to a intermediate fact and show that the fact proves the initial goal, this generally loosen's the goal
example (p q r s t : Prop) (hp : p) (hpq : p → q) (hqrst: q → r ∧ s ∧ t) : t := by
  suffices hrst: r ∧ s ∧ t by
    exact hrst.right.right
  apply hqrst
  apply hpq
  assumption

-- de morgan's law on and/or expression, using the or version
set_option push_neg.use_distrib true
example (p q r s : Prop) (h: ¬((p ∧ q) ∨ ¬r)) (hp : p) (hqs : ¬ q → s) : r ∧ s := by
  push_neg at h
  obtain ⟨hpq, hr⟩ := h
  have hnq: ¬ q := Or.neg_resolve_left hpq hp
  have hs: s := by exact hqs hnq
  exact ⟨hr, hs⟩

-- double negation removal
example (p q: Prop) (hpq : p ↔ q) (hq: q) : ¬¬p := by
  push_neg
  rw [hpq]
  assumption

-- prove negation of target creats contradiction, provide exact construction to supply contradiction
example (p q : Prop) (hpq : p → q) (hnq: ¬q) : ¬p := by
  by_contra hp
  exact absurd (hpq hp) (hnq)

-- change a implication goal to contrapositive
example (p q : Prop) (h₁ : p → ¬q) (h₂ : ¬ p → q) : p ↔ ¬ q := by
  constructor
  . assumption
  . contrapose
    push_neg
    assumption

-- use law of excluded middle for some propsition to get two separate cases
example (p q r : Prop) (hp: p → (q ↔ r)) (hnp: ¬ p → (r ↔ q)) : q ↔ r := by
  by_cases h: p
  . exact hp h
  . exact (hnp h).symm

-- when some terms in a logical exprssion have proof, simp easily proves it
example (p q r s t : Prop) (hp: p) (hs: ¬ s) : (p ∨ q) ∧ ¬ p ∧ r ↔ t ∧ s ∧ (p → s) := by
  simp [hp, hs]

-- bunch of true preconditions of implies are redundant, handled by simp
example (p q r s: Prop) (hp: p) (hq: q) (hr: r) : p → q → r → s ↔ s := by
  simp [hp, hq, hr]

-- in a iff expression, common terms on both side can be turned to a precondition and shorter target in implication, useful for simp_rw in many cases
example (p q r s u v : Prop) : (p ∧ q ∧ u ∧ r ∧ s ↔ p ∧ q ∧ v ∧ r ∧ s) ↔ (p → q → r → s → (u ↔ v)) := by
  simp
