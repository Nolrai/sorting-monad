import Mathlib

def P (Coeff : Type) (n : ℕ) : Type :=
  Finmap (λ (_ : Σ (i : Fin n), P Coeff i) ↦ Coeff)

def GExpr (Coeff : Type) : Type := Σ n, P Coeff n

section finmap_map

variable {ι} {α β : ι → Type} (f : ∀ {i}, α i → β i)

theorem List.map_snd {l : List (Sigma α)} : (l.map (λ p => ⟨p.1, f p.2⟩)).keys = l.keys := by
  induction l
  case nil => simp
  case cons head tail tail_ih =>
    simp at *
    apply tail_ih

def AList.map_aux : (l: List (Sigma α)) → (l.map (λ p => ⟨p.1, f p.2⟩)).keys = l.keys
  | [] => by
    simp
  | ⟨x₁, x₂⟩ :: xs => by
    simp
    apply AList.map_aux

def AList.map [DecidableEq ι] : AList α → AList β
  | ⟨l, h⟩ => {
    entries := l.map (λ p => ⟨p.1, f p.2⟩)
    nodupKeys := by
      rw [List.NodupKeys, AList.map_aux f]
      apply h
  }

@[simp]
theorem AList.map_nil [DecidableEq ι] : AList.map f (∅ : AList α) = ∅ := rfl

@[simp]
theorem AList.map_insert [DecidableEq ι] (xs : AList α) (key : ι) (value) (key_not_in : key ∉ xs) :
  AList.map f (insert key value xs) = insert key (f value) (xs.map f) := by
  induction xs
  case H0 => simp [singleton, AList.map, insert]
  case IH key₂ value₂ tail key₂_not_in_tail tail_ih =>
    simp [singleton, AList.map, insert]
    rw [List.kerase_of_not_mem_keys, List.kerase_of_not_mem_keys, List.kerase_of_not_mem_keys]
    simp
    · simp at *
      rw [AList.map_aux]
      apply key_not_in
    · exact key₂_not_in_tail
    · simp at *
      rw [List.keys_kerase, List.mem_erase_of_ne key_not_in.1]
      exact key_not_in

infix:50 " ~ " => List.Perm

theorem Finmap.map_aux [DecidableEq ι]
  (aList₁ aList₂ : AList α)
  (l₁_perm_l₂ : aList₁.entries.Perm aList₂.entries) :
  (AList.toFinmap ∘ AList.map fun {i} ↦ f) aList₁ = (AList.toFinmap ∘ AList.map fun {i} ↦ f) aList₂ := by
    simp [AList.toFinmap_eq]
    rw [List.perm_ext_iff_of_nodup]
    intros p
    have ⟨i, b⟩ := p; clear p
    simp [AList.map]
    rw [List.perm_ext_iff_of_nodup] at l₁_perm_l₂
    apply Iff.intro
    case mp =>
      intros h
      have ⟨i', a, a_h⟩ := h
      exists i'
      exists a
      rw [l₁_perm_l₂] at a_h
      exact a_h
    case mpr =>
      intros h
      have ⟨i', a, a_h⟩ := h
      exists i'
      exists a
      rw [← l₁_perm_l₂] at a_h
      exact a_h
    · apply List.NodupKeys.nodup
      exact aList₁.2
    · apply List.NodupKeys.nodup
      exact aList₂.2
    · apply List.NodupKeys.nodup
      apply (AList.map (fun {i} ↦ f) aList₁).2
    · apply List.NodupKeys.nodup
      apply (AList.map (fun {i} ↦ f) aList₂).2

def Finmap.map [DecidableEq ι] (x : Finmap α) : Finmap β :=
  x.liftOn (AList.toFinmap ∘ AList.map f) (Finmap.map_aux f)

end finmap_map

instance {α n} : EmptyCollection (P α n) where
  emptyCollection :=

def GExpr.map {α β} (f : α → β) : GExpr α → GExpr β
  | ⟨0, _⟩ => ⟨0, ∅⟩
