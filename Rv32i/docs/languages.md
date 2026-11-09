# Sprachen

## Sym (symbolisch)

- Sprungziele sind ausschließlich `Label`s, keine numerischen Offsets.
- `Instr` ist über die Zieltypen parametrisiert: `Instr (BT JT : Type)`, `Sym := Instr Label Label`.
- Programm = CFG aus Basic Blocks:
  - Rumpf: geradlinige Instruktionen (keine Sprünge)
  - Terminator: `jal l` | `bcond rs1 rs2 lThen lElse` | `jalr` | `ebreak`
- Pseudo-Instruktionen für PC-relative Adressen: `la rd, l`, `call l`.
- Wohlgeformtheit: Labels eindeutig, alle referenzierten Labels existieren, Einstieg `_start`.
- Semantik: PC = `(Label, Index)`.

## Asm (assemblernah)

- Flache Instruktionsliste mit numerischen Offsets: `Asm := Instr Imm13 Imm21`.
- Semantik: PC = `BitVec 32`, Sprung = `pc + offset`.
- Ausgabe als gültiges RISC-V-Assembly (`.option norvc`).

## Compilation Sym → Asm

- Layout: Blöcke linear anordnen, ergibt `addr : Label → BitVec 32`.
- Pseudo-Instruktionen expandieren (`la` → `auipc`+`addi`, `call` → `auipc`+`jalr`).
- Targets auflösen (im Kern ein `traverse`): `offset = addr l - pc`.
- `bcond … lThen lElse` → `b<cond> lThen`; `jal lElse` entfällt, wenn `lElse` der Folgeblock ist.
- Reichweite: Branch ±4 KiB, `jal` ±1 MiB.
  - v1: partiell (`Except`), Fehler bei Überlauf
  - später: Relaxation (`b<¬cond> skip; jal l`), Fixpunkt über Codegrößen
- Korrektheit: Simulation, `(l, i)` ↦ `addr l + 4*i`.
