namespace one
    /-
    Prove these equivalences:

    You should also try to understand why the reverse implication is not derivable in the last example.
    -/

    variables (α : Type) (p q : α → Prop)

    lemma forall_and_to_and_forall : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    iff.intro
        (assume h : ∀ x, p x ∧ q x,
        and.intro
            (assume x : α, show p x, from (h x).left)
            (assume x : α, show q x, from (h x).right))
        (assume h : (∀ x, p x) ∧ (∀ x, q x),
        assume x : α,
        and.intro (h.left x) (h.right x))

    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
        assume h₀ : ∀ x, p x → q x,
        assume h₁ : (∀ x, p x),
        assume x : α,
        have hpx : p x, from h₁ x,
        show q x, from h₀ x hpx

    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
        assume h₀ : (∀ x, p x) ∨ (∀ x, q x),
        assume x : α,
        or.elim h₀
            (assume h₁ : (∀ x, p x), or.intro_left (q x) (h₁ x))
            (assume h₁ : (∀ x, q x), or.intro_right (p x) (h₁ x))

end one

namespace two
    /-
    It is often possible to bring a component of a formula outside a universal quantifier, 
    when it does not depend on the quantified variable. 
    Try proving these (one direction of the second of these requires classical logic):
    -/
    open classical

    variables (α : Type) (p q : α → Prop)
    variable r : Prop

    example : α → ((∀ x : α, r) ↔ r) :=
        assume x : α,
        iff.intro
            (assume h : (∀ x : α, r), h x)
            (assume hr : r, assume y : α, hr)

    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
        iff.intro
            (assume h : (∀ x, p x ∨ r),
            by_cases
                (assume hr : r, or.intro_right (∀ x, p x) hr)
                (assume nr : ¬r, 
                have h₀ : (∀ x, p x), from 
                    (assume x : α,
                    have h₁ : (p x ∨ r), from h x,
                    or.resolve_right h₁ nr),
                or.intro_left r h₀))
            (assume h : (∀ x, p x) ∨ r,
            or.elim h
                (assume h₀ : ∀ x, p x, 
                assume x : α, or.intro_left r (h₀ x))
                (assume h₀ : r,
                assume x : α, or.intro_right (p x) h₀))

    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
        iff.intro
            (assume h : (∀ x, r → p x),
            assume hr : r,
            (assume x : α, h x hr))
            (assume h : (r → ∀ x, p x),
            assume x : α,
            assume hr : r,
            h hr x)

end two

namespace three
    /-
    Consider the “barber paradox,” that is, the claim that in a certain town there 
    is a (male) barber that shaves all and only the men who do not shave themselves. 
    Prove that this is a contradiction:
    -/
    open classical

    variables (men : Type) (barber : men)
    variable  (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
        have h_iff_barber : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
        by_cases
            (assume h_barber : shaves barber barber, absurd h_barber (iff.elim_left h_iff_barber h_barber))
            (assume n_barber : ¬shaves barber barber, absurd (iff.elim_right h_iff_barber n_barber) n_barber)

end three

namespace four
    /-
    Below, we have put definitions of divides and even in a special namespace to 
    avoid conflicts with definitions in the library. 
    The instance declaration make it possible to use the notation m | n for divides m n. 
    Don’t worry about how it works; you will learn about that later.
    -/

    namespace hidden

    def divides (m n : ℕ) : Prop := ∃ k, m * k = n

    instance : has_dvd nat := ⟨divides⟩

    def even (n : ℕ) : Prop := 2 ∣ n

    section
    variables m n : ℕ

    #check m ∣ n
    #check m^n
    #check even (m^n +3)

    /-
    Remember that, without any parameters, an expression of type Prop is just an assertion. 
    Fill in the definitions of prime and Fermat_prime below, and construct the given assertion. 
    For example, you can say that there are infinitely many primes by asserting that for every natural number n, 
    there is a prime number greater than n. 
    Goldbach’s weak conjecture states that every odd number greater than 5 is the sum of three primes. 
    Look up the definition of a Fermat prime or any of the other statements, if necessary.
    -/

    def prime (n : ℕ) : Prop := ∀ x : ℕ, divides x n → x = n ∨ x = 1
    
    def infinitely_many_primes : Prop := ∀ p : ℕ, prime p → ∃ p' : ℕ, prime p' ∧ p' > p

    -- A Fermat prime, is a prime of the form 2^(2^k)) + 1, where k is a nonnegative integer
    def Fermat_prime (n : ℕ) : Prop := prime n ∧ ∃ k : ℕ, n = 2^(2^k) + 1

    def infinitely_many_Fermat_primes : Prop := ∀ p : ℕ, Fermat_prime p → ∃ p' : ℕ, Fermat_prime p' ∧ p' > p

    -- Every integer greater than 2 can be written as the sum of three primes.
    def goldbach_conjecture : Prop := ∀ a : ℕ, a > 2 → ∃ x z y : ℕ, a = x + y + z

    -- Every odd number greater than 5 is the sum of three primes
    def Goldbach's_weak_conjecture : Prop := ∀ a : ℕ, ¬even a ∧ a > 5 → ∃ x z y : ℕ, a = x + y + z

    -- No three positive integers a, b, and c satisfy the equation a^n + b^n = c^n for any integer value of n greater than 2
    def Fermat's_last_theorem : Prop := ∀ n : ℕ, n > 2 → ∀ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 → ¬(a^n + b^n = c^n)

    end
    end hidden

end four

namespace five
    /-
    Prove as many of the identities listed in Section 4.4 as you can.
    -/
    open classical
    open not

    variables (α : Type) (p q : α → Prop)
    variable a : α
    variables r s : Prop

    example : (∃ x : α, r) → r :=
    assume h : ∃ x : α, r,
    match h with ⟨w, hw⟩ :=
        show r, from hw
    end

    example : (∃ x : α, r) → r :=
    assume h : ∃ x : α, r,
    let ⟨w, hw⟩ := h in hw

    lemma notnot : r ↔ ¬¬r :=
    iff.intro
        not_not_intro
        (assume nrr : ¬¬r,by_contradiction (assume nr : ¬r, absurd nr nrr))

    lemma not_exists : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
    iff.intro
        (assume ne : ¬ ∃ x, p x,
        assume x : α,
        show ¬p x, from by_contradiction (
            assume nnp : ¬¬p x,
            have hp : p x, from by_contradiction (assume np : ¬p x, absurd np nnp),
            have he : (∃ x, p x), from exists.intro x hp,
            absurd he ne))
        (assume ha : (∀ x, ¬ p x),
        by_contradiction (
        assume nne : ¬(¬ ∃ x, p x),
        have he : (∃ x, p x), from by_contradiction (assume ne : ¬(∃ x, p x), absurd ne nne),
        let ⟨w, hw⟩ := he in (
            have nw : ¬p w, from ha w,
            absurd hw nw)))
    
    lemma not_and_to_imp : ¬(r ∧ ¬s) → (r → s) :=
    assume h : ¬(r ∧ ¬s),
    assume hp : r,
    show s, from
    or.elim (em s)
        (assume hq : s, hq)
        (assume hnq : ¬s, absurd (and.intro hp hnq) h)
    lemma not_imp : ¬(r → s) → r ∧ ¬s :=
    assume h : ¬(r → s),
    by_contradiction
        (assume n₀ : ¬(r ∧ ¬s),
        have n₁ : r → s, from not_and_to_imp r s n₀,
        show false, from absurd n₁ h)

    -- use the fact that there is at least one element of α, namely a
    example : r → (∃ x : α, r) :=
    assume hr : r,
    by_contradiction
    (assume n: ¬(∃ x : α, r),
    have h: (∀ x : α, ¬r), from iff.elim_left (not_exists α (λ a : α, r)) n,
    have nr : ¬r, from h a,
    absurd hr nr)

    lemma not_or_and_not : ¬(r ∨ s) ↔ ¬r ∧ ¬s :=
    iff.intro
        (assume h : ¬(r ∨ s), and.intro 
            (assume hr: r,
            have hrs: r ∨ s, from or.intro_left s hr,
            show false, from absurd hrs h)
            (assume hs: s,
            have hrs: r ∨ s, from or.intro_right r hs,
            show false, from absurd hrs h))
        (assume nrs: ¬r ∧ ¬s,
        assume hrs: r ∨ s,
        have nr: ¬r, from nrs.left,
        have ns: ¬s, from nrs.right,
        show false, from or.elim hrs
            (assume hr: r, absurd hr nr)
            (assume hs: s, absurd hs ns))

    lemma not_and_iff_or_not : ¬ (r ∧ s) ↔ ¬ r ∨ ¬ s :=
    iff.intro
    (λ h : ¬ (r ∧ s),
    by_cases
        (assume hr : r, 
        by_contradiction
            (assume n : ¬(¬ r ∨ ¬ s),
            have nns : ¬¬s, from (iff.elim_left (not_or_and_not (¬r) (¬s)) n).right,
            have hs : s, from by_contradiction (assume ns : ¬s, absurd ns nns),
            absurd (and.intro hr hs) h))
        (assume nr : ¬r, or.inl nr))
    (λ h ⟨hr, hs⟩, or.elim h (λ h, h hr) (λ h, h hs))

    example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    iff.intro 
        (assume h : ∃ x, p x ∧ r,
        by_contradiction
        (assume n : ¬((∃ x, p x) ∧ r),
        have h1 : ¬(∃ x, p x) ∨ ¬r, from iff.elim_left (not_and_iff_or_not (∃ x, p x) r) n,
        match h with ⟨w, hw⟩ :=
            have hr : r, from hw.right,
            have hw : p w, from hw.left,
            or.elim h1
                (assume h2 : ¬(∃ x, p x), absurd (exists.intro w hw) h2)
                (assume nr : ¬r, absurd hr nr)
        end)) 
        (assume h : (∃ x, p x) ∧ r,
        have hr : r, from h.right,
        have he : (∃ x, p x), from h.left,
        let ⟨w, hw⟩ := he in exists.intro w (and.intro hw hr))

    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    iff.intro
    (assume h : (∃ x, p x ∨ q x), 
    match h with ⟨w, hw⟩ :=
    show (∃ x, p x) ∨ (∃ x, q x), from or.elim hw
            (assume hpw : p w, show (∃ x, p x) ∨ (∃ x, q x), from or.intro_left (∃ x, q x) (exists.intro w hpw))
            (assume hqw : q w, show (∃ x, p x) ∨ (∃ x, q x), from or.intro_right (∃ x, p x) (exists.intro w hqw))
    end)
    (assume h : (∃ x, p x) ∨ (∃ x, q x),
    or.elim h
        (assume h1 : (∃ x, p x), let ⟨w, hw⟩ := h1 in exists.intro w (or.inl hw))
        (assume h1 : (∃ x, q x), let ⟨w, hw⟩ := h1 in exists.intro w (or.inr hw)))
    
    lemma universal_notnot_arg : (∀ x, p x) ↔ (∀ x, ¬¬ p x) :=
    iff.intro 
        (assume h : (∀ x, p x), assume x, not_not_intro (h x))
        (assume h : (∀ x, ¬¬ p x), assume x, by_contradiction (assume np : ¬p x, absurd np (h x)))
    
    lemma exists_notnot_arg : (∃ x, p x) ↔ (∃ x, ¬¬ p x) :=
    iff.intro 
        (assume h : (∃ x, p x), let ⟨w, hw⟩ := h in exists.intro w (not_not_intro hw))
        (assume h : (∃ x, ¬¬ p x), match h with ⟨w, hw⟩ := 
            have hp : p w, from by_contradiction (assume np : ¬p w, absurd np hw),
            exists.intro w hp
        end)

    lemma not_exists_not : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
        have h: ¬ (∃ x, ¬ p x) ↔ (∀ x, ¬¬ p x), from not_exists α (λ x, ¬ p x),
        have h1 : (∀ x, ¬¬ p x) ↔ ¬ (∃ x, ¬ p x), from iff.symm h,
        have h2 : (∀ x, p x) ↔ (∀ x, ¬¬ p x), from universal_notnot_arg _ _,
        show (∀ x, p x) ↔ ¬ (∃ x, ¬ p x), from iff.trans h2 h1

    lemma not_universal_not : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    have h₀ : (∀ x, ¬p x) ↔ ¬(∃ x, ¬¬ p x), from not_exists_not _ _,
    have h₁ : ¬(∃ x, ¬¬ p x) ↔ ¬(∃ x, p x), from not_congr (iff.symm (exists_notnot_arg _ _)),
    have h₂ : ¬(∀ x, ¬p x) ↔ ¬¬(∃ x, p x), from not_congr (iff.trans h₀ h₁),
    have h₃ : ¬¬(∃ x, p x) ↔ (∃ x, p x), from 
        (iff.intro (assume nrr : ¬¬(∃ x, p x), by_contradiction (assume nr : ¬(∃ x, p x), absurd nr nrr))
         not_not_intro),
    iff.symm (iff.trans h₂ h₃)

    lemma not_universal_iff_exists_not : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    have h₀ : (∃ x, ¬p x) ↔ ¬ (∀ x, ¬¬ p x), from not_universal_not _ _,
    have h₁ : ¬¬(∀ x, ¬¬ p x) ↔ ¬(∃ x, ¬ p x), from iff.symm (not_congr h₀),
    have h₂ : (∀ x, ¬¬ p x) ↔ ¬¬(∀ x, ¬¬ p x), from 
        (iff.intro not_not_intro
        (assume nrr : ¬¬(∀ x, ¬¬ p x), by_contradiction (assume nr : ¬(∀ x, ¬¬ p x), absurd nr nrr))),
    have h₃ : (∀ x, p x) ↔ ¬(∃ x, ¬ p x), from iff.trans (universal_notnot_arg _ _) (iff.trans h₂ h₁), 
    have h₄ : ¬¬(∃ x, ¬ p x) ↔ (∃ x, ¬ p x), from 
        (iff.intro (assume nrr : ¬¬(∃ x, ¬ p x), by_contradiction (assume nr : ¬(∃ x, ¬ p x), absurd nr nrr))
         not_not_intro),
    iff.trans (not_congr h₃) h₄

    example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
    iff.intro 
    (assume h1 : (∀ x, p x → r), 
    assume h2 : (∃ x, p x),
    let ⟨w, hw⟩ :=  h2 in h1 w hw)
    (assume h1 : (∃ x, p x) → r,
    by_contradiction
        (assume h2 : ¬(∀ x, p x → r),
        have h3 : ∃ x, ¬(p x → r), from iff.elim_left (not_universal_iff_exists_not _ _) h2,
        match h3 with ⟨w, hw⟩ :=
            have h4 : p w ∧ ¬ r, from not_imp _ _ hw,
            have h5 : (∃ x, p x), from exists.intro w h4.left,
            absurd (h1 h5) h4.right
        end))

    -- use the fact that there is at least one element of α, namely a
    example : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
    iff.intro 
    (assume h1 : (∃ x, p x → r) , 
    assume h2 : (∀ x, p x),
    let ⟨w, hw⟩ :=  h1 in hw (h2 w))
    (assume h : (∀ x, p x) → r,
    by_contradiction 
        (assume h1 : ¬(∃ x, p x → r),
        have h2 : (∀ x, ¬(p x → r)), from iff.elim_left (not_exists _ _) h1,
        have h3 : (∀ x, p x ∧ ¬r), from (assume x : α, not_imp _ _ (h2 x)),
        have h4 : (∀ x, p x), from (assume x, (h3 x).left),
        have hr : r, from h h4,
        have nr : ¬r, from (h3 a).right,
        absurd hr nr))

    lemma false_imp_any : ¬r → r → s :=
    assume nr : ¬r,
    assume hr : r,
    show s, from absurd hr nr
    
    -- use the fact that there is at least one element of α, namely a
    example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
    iff.intro 
    (assume h1 : (∃ x, r → p x),
    assume hr : r,
    let ⟨w, hrw⟩ := h1 in exists.intro w (hrw hr))
    (assume h1 : (r → ∃ x, p x),
    by_cases
        (assume hr : r, 
        have ex : ∃ x, p x, from h1 hr,
        let ⟨w, hrw⟩ := (h1 hr) in exists.intro w (λ r, hrw))
        (assume nr : ¬r,
        -- here we use that fact that a : α exists
        exists.intro a (false_imp_any _ _ nr)))
        
end five