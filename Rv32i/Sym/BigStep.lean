import Rv32i.Sym.SmallStep

namespace Rv32i.Sym
section
variable {ℓ : Library}

/-!
# Big-Step Semantics for `Sym`
The symbolic jumps of `Sym` allow us to define a big step semantics over individual
blocks and programs.
This is (only) possible, because `Sym.State.step` does **not** depend on a `Sym.Program`.

A `Program` may be cyclic, so running it need not terminate. Hence the big step semantics
is an inductive *relation*: a diverging run simply has no derivation.
-/

/-- Execute the non-terminal instructions of a block, failing if any gets stuck. -/
def Block.body (b : Block ℓ) (s : State) (w : ℓ.World) : Option (State × ℓ.World) :=
  b.instrs.dropLast.foldlM (fun (s, w) i => s.step w i) (s, w)

/-- The terminal instruction of a block. -/
def Block.last (b : Block ℓ) : Instr ℓ := b.instrs.getLast b.neq

/-- Big step semantics: run whole blocks until `Ret` on an empty stack. The final state
is the one right before that `Ret`. -/
inductive Program.BigStep (p : Program ℓ) : State → ℓ.World → State → ℓ.World → Prop
  /-- Run a block, and continue wherever its terminator jumps to. -/
  | block {s s₁ s₂ s' : State} {w w₁ w₂ w' : ℓ.World} (b : Block ℓ)
      (hb : p.blocks[s.pc.block]? = some b) (h0 : s.pc.idx = 0)
      (hbody : b.body s w = some (s₁, w₁))
      (hterm : s₁.step w₁ b.last = some (s₂, w₂))
      (rest : BigStep p s₂ w₂ s' w') : BigStep p s w s' w'
  /-- The program finishes by returning with an empty stack. -/
  | exit {s s₁ : State} {w w₁ : ℓ.World} (b : Block ℓ)
      (hb : p.blocks[s.pc.block]? = some b) (h0 : s.pc.idx = 0)
      (hbody : b.body s w = some (s₁, w₁))
      (hret : b.last = .Ret) (hstack : s₁.pc.stack = []) : BigStep p s w s₁ w₁

/-! ### Soundness w.r.t. the small step semantics -/

theorem SInstr_store_pc {op : Asm.SInstr} {s s' : State} {a v : Word}
    (h : op.store s a v = some s') : s'.pc = s.pc := by
  cases op <;> simp only [Asm.SInstr.store] at h <;> (try split at h) <;> simp at h <;> subst h <;> rfl

/-- Non-terminal instructions advance within the block (they may change the stack). -/
theorem State.step_next_of_not_terminal {s s' : State} {w w' : ℓ.World} {i : Instr ℓ}
    (hi : i.isTerminal = false) (h : s.step w i = some (s', w')) :
    s'.pc.block = s.pc.block ∧ s'.pc.idx = s.pc.idx + 1 := by
  cases i <;> simp [Instr.isTerminal] at hi <;> simp only [State.step] at h
  all_goals (try split at h)
  all_goals simp at h
  case ILI.isFalse =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨v, -, rfl, -⟩ := h
    simp [State.next]
  case SI.isFalse =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨s2, hs2, rfl, -⟩ := h
    have := SInstr_store_pc hs2
    simp [State.next, this]
  all_goals obtain ⟨rfl, -⟩ := h
  all_goals simp [State.next, State.push, State.pop]

/-- Running the non-terminal instructions `is`, which sit at index `k` of block `l`,
is a sequence of small steps that advances the index by `is.length`. -/
theorem Program.body_star (p : Program ℓ) (l : Label) :
    ∀ (is : List (Instr ℓ)) (k : Nat) (s s₁ : State) (w w₁ : ℓ.World),
      (∀ j (hj : j < is.length) st, p.fetch ⟨l, k + j, st⟩ = some is[j]) →
      s.pc.block = l → s.pc.idx = k → (∀ i ∈ is, i.isTerminal = false) →
      is.foldlM (fun (s, w) i => s.step w i) (s, w) = some (s₁, w₁) →
      Step.Star p s s₁ w w₁ ∧ s₁.pc.block = l ∧ s₁.pc.idx = k + is.length := by
  intro is
  induction is with
  | nil =>
    intro k s s₁ w w₁ _ hb hk _ h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.refl _ _, hb, by simp [hk]⟩
  | cons i is ih =>
    intro k s s₁ w w₁ hf hb hk hnt h
    rcases h2 : s.step w i with _ | ⟨s₂, w₂⟩
    · simp [List.foldlM_cons, h2] at h
    rw [List.foldlM_cons] at h
    simp only [h2] at h
    have h3 : is.foldlM (fun (s, w) i => s.step w i) (s₂, w₂) = some (s₁, w₁) := h
    have e : s.pc = ⟨l, k, s.pc.stack⟩ := by rw [← hb, ← hk]
    have hfe : p.fetch s.pc = some i := by
      have := hf 0 (by simp) s.pc.stack
      rw [e]; simpa using this
    have hi : i.isTerminal = false := hnt i (by simp)
    obtain ⟨hb2, hk2⟩ := State.step_next_of_not_terminal hi h2
    obtain ⟨hst, hb3, hk3⟩ := ih (k + 1) s₂ s₁ w₂ w₁
      (fun j hj st => by
        have := hf (j + 1) (by simp; omega) st
        rw [show k + (j + 1) = k + 1 + j by omega] at this
        simpa using this)
      (hb2.trans hb) (by omega) (fun i' hi' => hnt i' (by simp [hi'])) h3
    exact ⟨Step.Star.head i hfe h2 hst, hb3, by simp; omega⟩

/-- The terminator of a block is fetched at its last index. -/
theorem Program.fetch_last (p : Program ℓ) {b : Block ℓ} {s : State}
    (hb : p.blocks[s.pc.block]? = some b) (hk : s.pc.idx = b.instrs.length - 1) :
    p.fetch s.pc = some b.last := by
  have hpos : 0 < b.instrs.length := List.length_pos_iff.mpr b.neq
  simp [Program.fetch, hb, hk, Block.last, List.getLast_eq_getElem]

/-- Running the body of a block, started at its first instruction, is a run of small steps
that ends at the terminator. -/
theorem Program.body_star' (p : Program ℓ) {b : Block ℓ} {s s₁ : State} {w w₁ : ℓ.World}
    (hb : p.blocks[s.pc.block]? = some b) (h0 : s.pc.idx = 0)
    (h : b.body s w = some (s₁, w₁)) :
    Step.Star p s s₁ w w₁ ∧ s₁.pc.block = s.pc.block ∧ s₁.pc.idx = b.instrs.length - 1 := by
  have hnt : ∀ i ∈ b.instrs.dropLast, i.isTerminal = false := by
    intro i hi
    have := List.all_eq_true.mp b.wf i hi
    simpa using this
  obtain ⟨hst, hb1, hk1⟩ := p.body_star s.pc.block b.instrs.dropLast 0 s s₁ w w₁
    (fun j hj st => by
      simp [Program.fetch, hb, List.length_dropLast] at hj ⊢)
    rfl h0 hnt h
  exact ⟨hst, hb1, by simpa using hk1⟩

theorem Program.BigStep.star {p : Program ℓ} {s s' : State} {w w' : ℓ.World}
    (h : p.BigStep s w s' w') : Step.Star p s s' w w' := by
  induction h with
  | block b hb h0 hbody hterm rest ih =>
    obtain ⟨hst, hb1, hk1⟩ := p.body_star' hb h0 hbody
    have hf := p.fetch_last (s := _) (hb1 ▸ hb) hk1
    exact .trans hst (.trans (.step ⟨_, hf, hterm⟩) ih)
  | exit b hb h0 hbody hret hstack =>
    exact (p.body_star' hb h0 hbody).1

theorem Program.BigStep.terminal {p : Program ℓ} {s s' : State} {w w' : ℓ.World}
    (h : p.BigStep s w s' w') : s'.terminal p := by
  induction h with
  | block _ _ _ _ _ _ ih => exact ih
  | exit b hb h0 hbody hret hstack =>
    obtain ⟨-, hb1, hk1⟩ := p.body_star' hb h0 hbody
    exact ⟨hret ▸ p.fetch_last (hb1 ▸ hb) hk1, hstack⟩

end
end Rv32i.Sym
