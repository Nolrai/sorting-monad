import Mathlib

section AList

theorem List.nodup_of_map_nodup {α β} (l : List α) (f : α → β) : (l.map f).Nodup → l.Nodup := by
  contrapose
  intros h
  rw [List.nodup_iff_sublist, not_forall_not] at *
  let ⟨x, h⟩ := h
  exists f x
  rw [List.sublist_map_iff]
  exists [x, x]

universe u v

variable {α₀ : Type u} {β: α₀ → Type v}

theorem AList.nodup (m : AList β) : m.entries.Nodup := by
  apply List.nodup_of_map_nodup (f := Sigma.fst) (l := m.entries)
  have : List.map Sigma.fst = (List.keys : List (Sigma β) → _) := by rw [List.keys]
  rw [this]
  apply AList.nodupKeys

universe u₁ v₁
variable [DecidableEq α₀] {α₁ : Type u₁} [DecidableEq α₁] {γ : α₁ → Type v₁}

def AList.bimap
  (f : α₀ → α₁) (g : (a : α₀) → β a → γ (f a))
  (f_injective : Function.Injective f)
  (m : AList β)
  : AList γ where
  entries := m.entries.map (λ ⟨key, value⟩ => Sigma.mk (f key) (g key value))
  nodupKeys := by
    simp only [List.NodupKeys, List.keys, List.map_map]
    rw [List.nodup_map_iff_inj_on]
    · simp only [Function.comp_apply]
      intros x x_in_entries y y_in_entries
      let ⟨x_a, x_b⟩ := x
      let ⟨y_a, y_b⟩ := y
      intros key_eq
      simp at key_eq
      have := f_injective key_eq
      cases this
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      rw [← Option.some_inj]
      rw [← AList.mem_lookup_iff, Option.mem_def] at *
      rw [← y_in_entries, ← x_in_entries]
    · apply m.nodup

end AList

namespace Finmap

universe u₀ v₀ u₁ v₁

variable {α₀ : Type u₀} {α₁ : Type u₁} [DecidableEq α₀] [DecidableEq α₁]

variable {β: α₀ → Type v₀} {γ: α₁ → Type v₁}

-- map over a Finmap as if it was a quotient of ALists
def bimap (m : Finmap β) (f : α₀ → α₁) (g : (a : α₀) → β a → γ (f a)) (f_injective : Function.Injective f) : Finmap γ :=
  m.liftOn (AList.toFinmap ∘ AList.bimap f g f_injective) <| by
  intros a b a_perm_b
  simp [AList.toFinmap_eq]
  simp [AList.bimap] at *
  apply List.Perm.map _ a_perm_b

end Finmap

universe u v

infix:50 "⇒¹" => λ a b => AList (λ _ : a => b)

infix:50 "⇒" => λ a b => Finmap (λ _ : a => b)

def Raw (α : Type u) : ℕ → Type u
  | 0 => PEmpty
  | (n+1) => Raw α n ⇒ α

variable {α : Type u} [DecidableEq α]


