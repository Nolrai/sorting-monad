import Mathlib

universe u v

section Zero'

variable (κ : Type u)

class Zero' extends AddSemigroup κ where
  toZero : κ → κ
  toZero_const : ∀ c₀ c₁ : κ, toZero c₀ = toZero c₁
  toZero_left_id : ∀ c₁, toZero c₁ + c₁ = c₁
  toZero_right_id : ∀ c₁, c₁ + toZero c₁ = c₁

instance [AddMonoid κ] : Zero' κ where
  toZero := λ _ => 0
  toZero_const := λ _ _ => rfl
  toZero_left_id := λ c₁ => zero_add c₁
  toZero_right_id := λ c₁ => add_zero c₁

instance : Zero' Empty where
  toZero := λ x => x.elim
  toZero_const := λ x => x.elim
  toZero_left_id := λ x => x.elim
  toZero_right_id := λ x => x.elim
  add := λ x => x.elim
  add_assoc := λ x => x.elim

def non_zero {α} [Zero' α] (a : α) : Prop := a ≠ Zero'.toZero a

abbrev NonZero κ [Zero' κ] := {k : κ // non_zero k}

end Zero'

section Terms

structure Term (κ π : Type) [Zero' κ] where
  (coeff : NonZero κ)
  (power : π)

structure Terms (κ π : Type) [Zero' κ] [π_lo : LinearOrder π] where
  (length : ℕ)
  (term : Fin length → Term κ π)
  (ordered : ∀ i j, i < j → (term i).power > (term j).power)

variable {κ π : Type} [π_lo : LinearOrder π] [LinearOrder κ] [Zero' κ]

infix:50 "·X^" => Term.mk

inductive Term.lt : Term κ π → Term κ π → Prop where
  | power {p₀ p₁} {c₀ c₁} : p₀ < p₁ → Term.lt (c₀·X^p₀) (c₁·X^p₁)
  | coeff {p} {c₀ c₁} : c₀ < c₁ → Term.lt (c₀·X^p) (c₁·X^p)

theorem Term.lt_iff' (p₀ p₁ : π) (c₀ c₁ : NonZero κ) : Term.lt (c₀·X^p₀) (c₁·X^p₁) ↔ (p₀ < p₁ ∨ (p₀ = p₁ ∧ c₀ < c₁)) where
  mp h := by
    cases h
    case power h => left; exact h
    case coeff h => right; simp; exact h
  mpr h := by
    cases h
    case inl h =>
      apply Term.lt.power h
    case inr h =>
      rw [h.1]
      apply Term.lt.coeff h.2

variable [LinearOrder κ]

instance Term.sto : IsStrictTotalOrder (Term κ π) Term.lt where
  irrefl a := by
    let ⟨c, p⟩ := a
    intros h
    cases h
    case power h =>
      apply lt_irrefl p h
    case coeff h =>
      apply lt_irrefl c h
  trans t₀ t₁ t₂ t₀_lt_t₁ t₁_lt_t₂ := by
    cases t₀_lt_t₁
    case power p₀ p₁ c₀ c₁ h01 =>
      cases t₁_lt_t₂
      case power p₂ c₂ h12 =>
        apply Term.lt.power
        apply lt_trans h01 h12
      case coeff c₂ h12 =>
        apply Term.lt.power
        exact h01
    case coeff p c₀ c₁ h01 =>
      cases t₁_lt_t₂
      case power p₂ c₂ h12 =>
        apply Term.lt.power
        exact h12
      case coeff c₂ h12 =>
        apply Term.lt.coeff
        apply lt_trans h01 h12
  trichotomous t₀ t₁ := by
    let ⟨c₀, p₀⟩ := t₀
    let ⟨c₁, p₁⟩ := t₁
    have : p₀ < p₁ ∨ p₀ = p₁ ∨ p₀ > p₁ := trichotomous_of (· < ·) p₀ p₁
    match this with
    | .inl h =>
      left; apply Term.lt.power h
    | .inr (.inr h) =>
      right; right; apply Term.lt.power h
    | .inr (.inl h) =>
      cases h
      simp [Term.lt_iff']
      exact trichotomous_of (· < ·) c₀ c₁

variable [LinearOrder π]

instance Term.decLt : DecidableRel (Term.lt : Term κ π → Term κ π → Prop)
  | c₀ ·X^ p₀, c₁ ·X^ p₁ =>
    if p_lt : p₀ < p₁
    then by right; constructor; exact p_lt
    else if p_gt : p₀ > p₁
      then by
        apply isFalse
        intros h
        cases h
        case power h => apply lt_asymm h p_gt
        case coeff h => apply lt_irrefl p₀ p_gt
      else by
        have : p₀ = p₁ := by
          simp only [not_lt, gt_iff_lt] at *
          apply le_antisymm p_gt p_lt
        cases this
        by_cases c_lt : c₀ < c₁
        case pos => right; apply Term.lt.coeff c_lt
        case neg =>
          left
          intros h
          cases h
          case power p_lt₂ => apply p_lt p_lt₂
          case coeff c_lt₂ => apply c_lt c_lt₂

instance : LinearOrder (Term κ π) := linearOrderOfSTO Term.lt

end Terms

namespace Terms

variable {κ π} [Zero' κ] [LinearOrder π]

def term' (x : Terms κ π) (n : ℕ) : WithBot (Term κ π) :=
  if h : n < x.length
  then ↑(x.term ⟨n, h⟩)
  else ⊥

theorem term'_eq_coe (x : Terms κ π) (n : ℕ) : n < x.length ↔ ∃ (t : Term κ π), x.term' n = ↑t where
  mp h := by
    exists x.term ⟨n, h⟩
    simp [Terms.term']
    rw [dif_pos]

  mpr h := by
    let ⟨t, h⟩ := h
    contrapose h
    rw [Terms.term', dif_neg h]
    simp

theorem term'_ext_aux {x y : Terms κ π} (term'_eq : x.term' = y.term') : x.length = y.length := by
  let ⟨xl, xt, xo⟩ := x
  let ⟨yl, yt, yo⟩ := y
  revert term'_eq
  contrapose
  simp [funext_iff]
  intros length_ne'
  have length_ne : xl ≠ yl := length_ne'; clear length_ne'
  rw [ne_iff_lt_or_gt] at length_ne
  cases length_ne
  case inl xl_lt_yl =>
    exists xl
    simp [Terms.term', dif_pos xl_lt_yl]
  case inr yl_lt_xl =>
    exists yl
    simp [Terms.term', dif_pos yl_lt_xl]

theorem term'_ext (x y : Terms κ π) (term'_eq : x.term' = y.term') : x = y := by
  have : x.length = y.length := Terms.term'_ext_aux term'_eq
  let ⟨xl, xt, xo⟩ := x
  let ⟨yl, yt, yo⟩ := y
  simp only at this
  simp only [mk.injEq] at *
  exists this
  cases this
  have : xt = yt := by
    funext i
    cases xl
    case zero => apply i.elim0
    case succ n =>
      have : Terms.term' ⟨_, xt, xo⟩ i = Terms.term' ⟨_, yt, yo⟩ i := by
        rw [term'_eq]
      simp [Terms.term'] at this
      exact this
  rw [this]

theorem term'_ext_iff (x y : Terms κ π) : x.term' = y.term' ↔ x = y where
  mp := term'_ext x y
  mpr h := by rw [h]

end Terms

namespace Terms

variable {κ π} [Zero' κ] [LinearOrder κ] [LinearOrder π]

def test : LinearOrder (Term κ π) := by infer_instance

def lt (x y : Terms κ π) : Prop := toLex x.term' < toLex y.term'

@[simp]
theorem lt_def : Terms.lt = λ (x y : Terms κ π) => toLex x.term' < toLex y.term' := rfl

instance lex_trichotimous : IsTrichotomous (Lex (ℕ → WithBot (Term κ π))) (· < ·) := by
  apply Pi.isTrichotomous_lex
  apply Nat.lt_wfRel.wf

instance isSTO : IsStrictTotalOrder (Terms κ π) Terms.lt where
  irrefl t := by simp
  trans a b c ab bc := by
    simp at *
    apply lt_trans ab bc
  trichotomous a b := by
    simp
    have : (a = b) ↔ toLex a.term' = toLex b.term' := by
      simp
      symm
      apply term'_ext_iff
    rw [this]
    apply trichotomous (r := (· < ·)) (a := toLex a.term') (b := toLex b.term')

instance : DecidableRel (α := Terms κ π) Terms.lt := by
  simp

instance : LinearOrder (Terms κ π) := linearOrderOfSTO (α := (Terms κ π)) Terms.lt

section

variable (κ : Type) [Zero' κ] [LinearOrder κ]

def Raw₀ : ℕ → Sigma LinearOrder
  | 0 => ⟨Unit, inferInstance⟩
  | (n+1) =>
    have ⟨π, _⟩ := Raw₀ n
    let τ := Terms κ π
    have : IsStrictTotalOrder τ (· < ·) := Terms.isSTO
    ⟨τ, linearOrderOfSTO Terms.lt⟩

abbrev Raw n := (Raw₀ κ n).fst

instance (n : ℕ) : LinearOrder (Raw κ n) := Sigma.snd (Raw₀ κ n)

end

namespace Raw

variable {κ : Type} [Zero' κ] [LinearOrder κ] [DecidablePred (non_zero : κ → Prop)]

def zero : ∀ {n : ℕ}, Raw κ n
  | 0 => ()
  | (n+1) => {
    length := 0
    term := λ i => i.elim0
    ordered := by simp
  }

def ofNat (m' : ℕ) {n} [OfNat κ m'] : Raw κ (n+1) :=
  let m := (OfNat.ofNat m' : κ)
  if h : non_zero m
    then {
      length := 1
      term := λ _ => {power := zero, coeff := ⟨m, h⟩}
      ordered := λ _ => by simp
    }
    else zero

def lift₁ : {n : ℕ} → {f : Raw κ n → Raw κ (n+1) // ∀ x y, x < y → f x < f y}
  | 0 => by
    exists (λ _ => zero)
    intros x y h
    cases h
  | n+1 => by
    have f : Raw κ (n + 1) → Raw κ ((n + 1) + 1) := λ x => {
      term := λ i =>
        let ⟨c, p⟩ := x.term i
        ⟨c, lift₁.val p⟩
      ordered := by
        intros i j i_lt_j
        simp
        apply lift₁.prop
        apply x.ordered
        apply i_lt_j
    }

def lift {n : ℕ} : {m : ℕ} → Raw κ n → Raw κ (n + m)
  | 0, x => x
  | m+1, x => lift₁.val (lift (m := m) x)
