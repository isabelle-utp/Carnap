# carnap-check

A command-line tool for checking natural deduction proofs using the Carnap proof-checking library, without needing to run the web server.

## Building

```bash
stack build Carnap:exe:carnap-check
```

## Usage

```
carnap-check [<default-logic>] <file>
carnap-check --list
```

- `<default-logic>` — optional; the logic system used when a lemma does not specify one
- `<file>` — a proof file in the structured lemma format described below
- `--list` — print all available logic systems

## File format

Proof files use an Isabelle-inspired structured format.

### Lemma blocks

```
lemma <Name> in <Logic>: <Goal>
begin
<proof lines>
end
```

All three of `<Name>`, `in <Logic>`, and `: <Goal>` are optional:

| Part | Omitted behaviour |
|------|-------------------|
| `<Name>` | lemma is numbered automatically (1, 2, …) |
| `in <Logic>` | inherits the current default logic |
| `: <Goal>` | the proven sequent is printed; no pass/fail check |

### Logic declarations

```
logic <name>
```

Sets the default logic for all subsequent lemmas in the file.

### Comments

Lines beginning with `--` are comments and are ignored.

### Goal syntax

Goals are sequents: premises separated by commas, then `|-` (or `⊢`), then the conclusion.

```
P /\ Q, ~Q \/ R |- (P /\ Q) /\ R
```

## Example

```
-- Mixed propositional and first-order file

logic fosterAndLaursenTFL

lemma AndElim: P /\ Q |- P
begin
P /\ Q :PR
P :/\E 1
end

lemma DisjSyl
begin
P \/ Q :PR
~P :PR
Q :\/E 1,2
end

lemma UIExample in firstOrder: Ax F(x) |- F(a)
begin
Ax F(x) :PR
F(a) :UI 1
end
```

Running `carnap-check myproofs.txt` produces:

```
lemma AndElim (fosterAndLaursenTFL): (P ∧ Q) ⊢ P
lemma DisjSyl (fosterAndLaursenTFL): (P ∨ Q), ¬P ⊢ Q
lemma UIExample (firstOrder): ∀xF(x) ⊢ F(a)

Summary: all lemmas proved.
```

## Logic systems

Use `carnap-check --list` to see all available systems.

**Propositional** examples: `prop`, `fosterAndLaursenTFL`, `magnusSL`, `thomasBolducAndZachTFL`

**First-order** examples: `firstOrder`, `fosterAndLaursenFOL`, `magnusQL`, `thomasBolducAndZachFOL`

### First-order syntax

The `firstOrder` system (and most FOL systems) use:

| Item | Symbols |
|------|---------|
| Predicates | `F G H I J K L M N O` (uppercase, require parenthesised arguments: `F(x)`) |
| Constants | `a b c d e` |
| Free variables / quantifier variables | `v w x y z` |
| Quantifiers | `A` (∀), `E` (∃) — written prefix: `Ax F(x)` |
| Rules | `UI` (universal instantiation), `EG` (existential generalisation), … |
