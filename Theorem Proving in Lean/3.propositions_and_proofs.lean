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

example : ¬(p ∨ q) → ¬p :=
    assume h : ¬(p ∨ q),
    show ¬p, from (
        assume hp: p,
        have hpq: p ∨ q, from or.intro_left q hp,
        show false, from absurd hpq h)

-- changed to lemma for later use
lemma not_or_and_not : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro
    (assume h : ¬(p ∨ q), and.intro 
        (assume hp: p,
        have hpq: p ∨ q, from or.intro_left q hp,
        show false, from absurd hpq h)
        (assume hq: q,
        have hpq: p ∨ q, from or.intro_right p hq,
        show false, from absurd hpq h))
    (assume npq: ¬p ∧ ¬q,
    assume hpq: p ∨ q,
    have np: ¬p, from npq.left,
    have nq: ¬q, from npq.right,
    show false, from or.elim hpq
        (assume hp: p, absurd hp np)
        (assume hq: q, absurd hq nq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    assume npq: ¬p ∨ ¬q,
    assume hpq: p ∧ q,
    have hp: p, from hpq.left,
    have hq: q, from hpq.right,
    show false, from or.elim npq
        (assume np: ¬p, absurd hp np)
        (assume nq: ¬q, absurd hq nq)

example : ¬(p ∧ ¬p) :=
    assume h : p ∧ ¬p,
    have hp: p, from h.left,
    have np: ¬p, from h.right,
    show false, from absurd hp np

example : p ∧ ¬q → ¬(p → q) :=
    assume hpnq: p ∧ ¬q,
    assume hpq: p → q,
    have hp: p, from hpnq.left,
    have nq: ¬q, from hpnq.right,
    have hq: q, from hpq hp,
    show false, from absurd hq nq

example : ¬p → (p → q) :=
    assume np: ¬p,
    assume hp: p,
    show q, from absurd hp np

example : (¬p ∨ q) → (p → q) :=
    assume h: ¬p ∨ q,
    assume hp: p,
    show q, from or.elim h
        (assume np: ¬p, absurd hp np)
        (assume hq: q, hq)

example : p ∨ false ↔ p :=
iff.intro
    (assume h : p ∨ false, or.elim h
        (assume hp: p, hp)
        (assume f: false, false.elim f))
    (assume hp: p, or.intro_left false hp)

example : p ∧ false ↔ false := 
iff.intro
    (assume h : p ∧ false, false.elim h.right)
    (assume f: false, false.elim f)

/-
Exercise 2. Prove ¬(p ↔ ¬p) without using classical logic.
-/
lemma implies_to_double_not_and : (p → q) → ¬¬(¬p ∨ q):=
    assume h: p → q,
    assume h₂ : ¬(¬p ∨ q),
    have h₃ : ¬¬p ∧ ¬q, from iff.elim_left (not_or_and_not (¬p) q) h₂,
    have nnp: ¬¬p, from h₃.left,
    have nq: ¬q, from h₃.right,
    have np: ¬p, from (
        assume hp: p,
        have hq: q, from h hp,
        show false, from absurd hq nq),
    show false, from absurd np nnp
lemma iff_to_not_iff : (p ↔ q) → (¬p ↔ ¬q) :=
    assume h : p ↔ q, iff.intro
        (assume np : ¬p,
        assume hq : q,
        have hp: p, from iff.elim_right h hq,
        show false, from absurd hp np)
        (assume nq : ¬q,
        assume hp : p,
        have hq: q, from iff.elim_left h hp,
        show false, from absurd hq nq)
lemma not_and_same : ¬(p ∧ p) → ¬p :=
    assume h: ¬(p ∧ p),
    assume hp: p,
    have hpp: p ∧ p, from and.intro hp hp,
    show false, from absurd hpp h
example : ¬(p ↔ ¬p) :=
    -- enumerate negations
    assume h₀: p ↔ ¬p,
    have h₁ : ¬p ↔ ¬¬p, from iff_to_not_iff p (¬p) h₀,
    have h₂ : ¬¬p ↔ ¬¬¬p, from iff_to_not_iff (¬p) (¬¬p) h₁,
    -- get negated p
    have hnnnp : ¬(¬¬p ∧ ¬¬p), from (
        -- (p → ¬p) → ¬(¬¬p ∧ ¬¬p)
        have h₁ : ¬¬(¬p ∨ ¬p), from implies_to_double_not_and p (¬p) (iff.elim_left h₀),
        have h₂ : ¬¬(¬p ∨ ¬p) ↔ ¬(¬¬p ∧ ¬¬p), from iff_to_not_iff (¬(¬p ∨ ¬p)) (¬¬p ∧ ¬¬p) (not_or_and_not (¬p) (¬p)),
        show ¬(¬¬p ∧ ¬¬p), from (iff.elim_left h₂) h₁),
    --implies_to_andish p (¬p) (iff.elim_left h₀),
    have nnnp : ¬¬¬p, from not_and_same (¬¬p) hnnnp,
    -- eliminate negations
    have nnp : ¬¬p, from iff.elim_right h₂ nnnp,
    show false, from absurd nnp nnnp

-- changed to lemma for later use
lemma reverse_imp : (p → q) → (¬q → ¬p) :=
    assume hpq: p → q,
    assume nq: ¬q,
    assume hp: p,
    have hq: q, from hpq hp,
    show false, from absurd hq nq

-- these require classical reasoning

lemma notnot : ¬¬p ↔ p :=
    iff.intro
        (assume h: ¬¬p,
        by_contradiction (assume h1 : ¬p, show false, from h h1))
        (assume h: p,
        by_cases 
            (assume h1 : ¬p, absurd h h1)
            (assume h1 : ¬¬p, h1))

lemma imp_substitue_frst : ((p → q) ∧ (p ↔ r)) → (r → q) :=
    assume h: (p → q) ∧ (p ↔ r),
    assume hr: r,
    have hp: p, from iff.elim_right (and.elim_right h) hr,
    show q, from and.elim_left h hp

lemma imp_substitue_scnd : ((p → q) ∧ (q ↔ r)) → (p → r) :=
    assume h: (p → q) ∧ (q ↔ r),
    assume hp: p,
    have hq: q, from and.elim_left h hp,
    show r, from iff.elim_left (and.elim_right h) hq

lemma not_and_to_imp : ¬(p ∧ ¬q) → (p → q) :=
    assume h : ¬(p ∧ ¬q),
    assume hp : p,
    show q, from
    or.elim (em q)
        (assume hq : q, hq)
        (assume hnq : ¬q, absurd (and.intro hp hnq) h)

lemma not_iff : ¬(p → q) → p ∧ ¬q :=
    assume h : ¬(p → q),
    by_contradiction
        (assume n₀ : ¬(p ∧ ¬q),
        have n₁ : p → q, from not_and_to_imp  p q n₀,
        show false, from absurd n₁ h)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
    assume h : p → r ∨ s,
    by_contradiction
        (assume n₀ : ¬((p → r) ∨ (p → s)),
        have n₁ : ¬(p → r) ∧ ¬(p → s), from iff.elim_left (not_or_and_not (p → r) (p → s)) n₀,
        have n₂ : p ∧ ¬r, from not_iff p r (and.elim_left n₁),
        have n₃ : p ∧ ¬s, from not_iff p s (and.elim_right n₁),
        have hrs: r ∨ s, from h (and.elim_left n₂),
        have nrs: ¬(r ∨ s), from iff.elim_right (not_or_and_not r s) (and.intro n₂.right n₃.right),
        show false, from absurd hrs nrs)

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    assume h : ¬(p ∧ q),
    by_cases
        (assume hp: p, 
        have nq: ¬q, from by_contradiction(
            assume nnq: ¬¬q,
            have hq: q, from iff.elim_left (notnot q) nnq,
            have n : p ∧ q, from and.intro hp hq,
            show false, from absurd n h),
        show ¬p ∨ ¬q, from or.intro_right (¬p) nq)
        (assume np: ¬p, show ¬p ∨ ¬q, from or.intro_left (¬q) np)
    
-- changed to lemma for later use
lemma implies_as_or : (p → q) → (¬p ∨ q) :=
assume h : p → q,
by_cases
    (assume hp : p,
    have hq: q, from h hp,
    show ¬p ∨ q, from or.intro_right (¬p) hq)
    (assume np : ¬p, show ¬p ∨ q, from or.intro_left (q) np)

example : (¬q → ¬p) → (p → q) :=
    assume h : ¬q → ¬p

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := sorry