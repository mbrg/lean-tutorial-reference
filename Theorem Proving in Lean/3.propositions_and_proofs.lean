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
            (λ hr : r, or.intro_right (p ∨ q) hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro 
    (λ h : p ∧ (q ∨ r), or.elim h.right
        (λ hq: q, or.intro_left (p ∧ r) (and.intro h.left hq))
        (λ hr: r, or.intro_right (p ∧ q) (and.intro h.left hr)))
    (λ h : (p ∧ q) ∨ (p ∧ r), or.elim h
        (λ hpq: p ∧ q, and.intro hpq.left (or.intro_left r hpq.right))
        (λ hpr: p ∧ r, and.intro hpr.left (or.intro_right q hpr.right)))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
iff.intro 
    (λ h : p ∨ (q ∧ r), or.elim h
        (λ hp: p, and.intro (or.intro_left q hp) (or.intro_left r hp))
        (λ hqr: q ∧ r, and.intro (or.intro_right p hqr.left) (or.intro_right p hqr.right)))
    (λ h : (p ∨ q) ∧ (p ∨ r), or.elim h.left
        (λ hp: p, or.intro_left (q ∧ r) hp)
        (λ hq: q, or.elim h.right
            (λ hp: p, or.intro_left (q ∧ r) hp)
            (λ hr: r, or.intro_right p (and.intro hq hr))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
iff.intro
    (assume h: p → (q → r),
    assume hpq: p ∧ q,
    have hqr: q → r, from h hpq.left,
    show r, from hqr hpq.right)
    (assume h: p ∧ q → r,
    assume hp: p,
    assume hq: q,
    show r, from h (and.intro hp hq))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
iff.intro
    (assume h : (p ∨ q) → r, and.intro
        (assume hp: p, show r, from h (or.intro_left q hp))
        (assume hq: q, show r, from h (or.intro_right p hq)))
    (assume h : (p → r) ∧ (q → r),
    assume hpq: p ∨ q, or.elim hpq
        (assume hp: p, show r, from h.left hp)
        (assume hq: q, show r, from h.right hq))

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