open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
iff.intro 
    (assume hpq : p ∧ q, and.intro hpq.right hpq.left)
    (assume hqp : q ∧ p, and.intro hqp.right hqp.left)

example : p ∨ q ↔ q ∨ p := 
iff.intro 
    (assume hpq : p ∨ q, 
     or.elim hpq 
        (assume hp : p, show q ∨ p, from or.intro_right q hp)
        (assume hq : q, show q ∨ p, from or.intro_left p hq)
    )
    (assume hqp : q ∨ p, 
     or.elim hqp 
        (assume hq : q, show p ∨ q, from or.intro_right p hq)
        (assume hp : p, show p ∨ q, from or.intro_left q hp)
    )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro 
    (assume h : (p ∧ q) ∧ r, 
     show p ∧ (q ∧ r), 
     from and.intro (h.left.left) (and.intro h.left.right h.right))
    (assume h : p ∧ (q ∧ r), 
     show (p ∧ q) ∧ r, 
     from and.intro (and.intro h.left h.right.left) (h.right.right))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
iff.intro 
    (assume h : (p ∨ q) ∨ r, 
     show p ∨ (q ∨ r), 
     from or.elim h
        (λ hpq : p ∨ q, or.elim hpq
            (λ hp : p, or.intro_left (q ∨ r) hp)
            (λ hq : q, or.intro_right p (or.intro_left r hq)))
        (λ hr : r, or.intro_right p (or.intro_right q hr)))
    (assume h : p ∨ (q ∨ r), 
     show (p ∨ q) ∨ r, 
     from or.elim h
        (λ hp : p, or.intro_left r (or.intro_left q hp))
        (λ hqr : q ∨ r, or.elim hqr
            (λ hq : q, or.intro_left r (or.intro_right p hq))
            (λ hr : r, or.intro_right (p ∨ q) hr))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : ¬(p ↔ ¬p) := sorry
example : (p → q) → (¬q → ¬p) := sorry

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry