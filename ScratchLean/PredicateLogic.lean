import Mathlib

/- predicate is anything of type α → Prop, α → β → Prop etc -/
#check Eq
#check True = True
#check Ne
#check True ≠ True

#check forall x: Prop, x ∨ ¬ x
#check ∀ x: Prop, x ∨ ¬ x
#check ∀ (x y : Prop), x ∨ y

#check Exists
#check exists x: Prop, x
#check ∃ x y, x ∧ y

-- a = a
example (a : α) : a = a := by rfl

-- P(a), a = b proves P(b)
example (P : α → Prop) (a b : α) (hab : a = b) (hpa : P a) : P b := by
  rw [← hab]
  assumption

-- for all x, P(x) proves P(a)
example (P : α → Prop) (a : α) (h: ∀ x: α, P x) : P a := by
  exact h a

-- for all x, y, P(x) or Q(y); not P (a). this proves Q(x) for all x
example (P Q : α → Prop) (a: α) (hp: ∀ (x y: α), P x ∨ Q y) (hpa: ¬ P a) : ∀ x: α, Q x := by
  intro x
  have hpa_qx : P a ∨ Q x := by exact hp a x
  apply Or.resolve_left hpa_qx
  assumption

-- for all x, P(x); an instance a, proves there exists x s.t. P(x)
example (P : α → Prop) (a: α) (hall: ∀ x : α, P x) : ∃ x : α, P x := by
  use a
  exact hall a

-- a, exists x s.t. P(x), for all x P(x) implies Q(a) proves Q(a)
example (P Q : α → Prop) (a : α) (h: ∃ x, P x) (h': ∀ x, P x → Q a) : Q a := by
  obtain ⟨x, hpx⟩ := h
  apply h' x
  assumption

-- a, not exists x, y s.t. P(x, y) proves not P(a, a)
example (P : α → α → Prop) (a: α) (h: ¬ ∃ x y, P x y) : ¬ P a a := by
  push_neg at h
  exact h a a

#check (x : Prop) → ∃ y ≠ x, y
#check (x : Prop) → ∀ y ≠ x, y

-- for all x, P(x) ↔ Q(x), ∃ x ≠ a, P(x) proves ∃ x ≠ a, Q(x)
example (P Q : α → Prop) (h: ∀ x, P x ↔ Q x) (a: α) (h': ∃ x ≠ a, P x) : ∃ x ≠ a, Q x := by
  obtain ⟨x, h_neq, hpx⟩ := h'
  use x
  have hqx : Q x := (h x).mp hpx
  exact ⟨h_neq, hqx⟩

-- for all x, P(x) ↔ Q(x), ∀ x ≠ a, P(x) proves ∀ x ≠ a, Q(x)
example (P Q : α → Prop) (h: ∀ x, P x ↔ Q x) (a: α) (h': ∀ x ≠ a, P x) : ∀ x ≠ a, Q x := by
  rintro x h_neq
  have hpx : P x := (h' x h_neq)
  apply (h x).mp
  exact hpx

#check ExistsUnique
#check ∃! x : Prop, x

-- there exists unique x s.t. P(x) proves there exists x s.t. P(x)
example (P : α → Prop) (h: ∃! x, P x) : ∃ x, P x := by
  exact ExistsUnique.exists h
