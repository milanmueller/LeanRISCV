import Rv32i.Asm

open Asm

-- Branch / jump immediates are in units of 2 bytes (the implicit bit 0
-- is not encoded), so `n` means a byte offset of `2 * n`.

open Instr in
def example1 : Program :=
  [ II .addi Reg.a0 Reg.zero 0           -- 0x00: sum := 0
  , II .addi Reg.t0 Reg.zero 10          -- 0x04: i := 10
  , RI .add Reg.a0 Reg.a0 Reg.t0         -- 0x08: sum += i
  , II .addi Reg.t0 Reg.t0 (-1)          -- 0x0c: i -= 1
  , BI .bne Reg.t0 Reg.zero (-4)         -- 0x10: while i != 0 (-8 bytes: back to `add`)
  , II .addi Reg.a7 Reg.zero 93          -- 0x14: Linux `exit` syscall
  , ISysI .ecall                         -- 0x18: exit(a0) = exit(55)
  , ISysI .ebreak ]                      -- 0x1c

def main : IO Unit := IO.print example1.render

/-!
## Correctness of `example1`
-/


/-- `tri k = k + (k-1) + ... + 1`. -/
def tri : Nat → Nat
  | 0 => 0
  | k + 1 => (k + 1) + tri k

/-- Loop invariant: entering the loop at `add` (pc 8) with `t0 = k`, the loop exits
at pc `0x14` having added `k + (k-1) + ... + 1` to `a0`. -/
theorem example1_loop (k : Nat) : ∀ s : State, 1 ≤ k → k ≤ 10 →
    s.pc = 8 → s.read .t0 = BitVec.ofNat 32 k →
    ∃ s', Step.Star example1 s s' ∧ s'.pc = 0x14
      ∧ s'.read .a0 = s.read .a0 + BitVec.ofNat 32 (tri k) := by
  induction k with
  | zero => intro s h; omega
  | succ k ih =>
    intro s _ hk hpc ht0
    -- add a0, a0, t0
    let s1 := (s.write .a0 (s.read .a0 + s.read .t0)).next
    have h1 : fetch example1 s.pc = some (.RI .add .a0 .a0 .t0) := by rw [hpc]; rfl
    have e1 : step s (.RI .add .a0 .a0 .t0) = some s1 := rfl
    -- addi t0, t0, -1
    let s2 := (s1.write .t0 (s1.read .t0 + (-1 : BitVec 12).signExtend 32)).next
    have h2 : fetch example1 s1.pc = some (.II .addi .t0 .t0 (-1)) := by simp [s1, hpc]; rfl
    have e2 : step s1 (.II .addi .t0 .t0 (-1)) = some s2 := rfl
    -- bne t0, zero, -8
    have h3 : fetch example1 s2.pc = some (.BI .bne .t0 .zero (-4)) := by simp [s2, s1, hpc]; rfl
    have ht0' : s2.read .t0 = BitVec.ofNat 32 k := by simp [s2, s1, ht0]; bv_omega
    by_cases hk0 : k = 0
    · -- last iteration: fall through
      subst hk0
      have e3 : step s2 (.BI .bne .t0 .zero (-4)) = some s2.next := by
        simp [step, BInstr.eval, ht0']
      refine ⟨s2.next, .head _ h1 e1 (.head _ h2 e2 (.head _ h3 e3 (.refl _))), ?_, ?_⟩
      · simp [s2, s1, hpc]
      · simp [s2, s1, ht0, tri]
    · -- jump back to `add` and continue by induction
      have e3 : step s2 (.BI .bne .t0 .zero (-4)) = some { s2 with pc := 8 } := by
        have : BitVec.ofNat 32 k ≠ 0 := by bv_omega
        simp only [step, BInstr.eval, ht0', State.read_zero]
        simp [State.jump, s2, s1, hpc]
        exact fun h => absurd h this
      obtain ⟨s', hst, hpc', ha0⟩ := ih { s2 with pc := 8 } (by omega) (by omega) rfl ht0'
      refine ⟨s', .head _ h1 e1 (.head _ h2 e2 (.head _ h3 e3 hst)), hpc', ?_⟩
      rw [ha0]
      show s2.read .a0 + _ = _
      simp [s2, s1, ht0, tri, BitVec.ofNat_add, BitVec.add_assoc]

/-- From any initial registers and memory, `example1` exits with code 55. -/
theorem example1_correct (s : State) (hpc : s.pc = 0) : Terminates example1 s 55 := by
  -- addi a0, zero, 0
  let s1 := (s.write .a0 (s.read .zero + (0 : BitVec 12).signExtend 32)).next
  have e1 : step s (.II .addi .a0 .zero 0) = some s1 := rfl
  -- addi t0, zero, 10
  let s2 := (s1.write .t0 (s1.read .zero + (10 : BitVec 12).signExtend 32)).next
  have e2 : step s1 (.II .addi .t0 .zero 10) = some s2 := rfl
  -- the loop
  obtain ⟨s3, hst, hpc3, ha0⟩ :=
    example1_loop 10 s2 (by decide) (by decide) (by simp [s2, s1, hpc]) (by simp [s2, s1])
  -- addi a7, zero, 93
  let s4 := (s3.write .a7 (s3.read .zero + (93 : BitVec 12).signExtend 32)).next
  have e4 : step s3 (.II .addi .a7 .zero 93) = some s4 := rfl
  refine ⟨s4, .head _ (by rw [hpc]; rfl) e1 (.head _ (by simp [s1, hpc]; rfl) e2
    (.trans hst (.head _ (by rw [hpc3]; rfl) e4 (.refl _)))), ⟨?_, ?_⟩, ?_⟩
  · simp [s4, hpc3]; rfl
  · simp [s4]
  · simp [s4, ha0, s2, s1, tri]
