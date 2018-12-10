# LMC-Lisp

## Introduction
LMC-Lisp is a LMC (Little Machine Computer) Assembly Interpreter for Common Lisp developed as part
of the PL (Programming Languages) semester project.

## Functionalities
- AOT (Ahead-of-time) Compilation & Execution.
- JIT (Just-in-time) Interpretation [**WIP**].

## Compatibility
LMC-Lisp has been developed and tested on ANSI Common Lisp, although other Lisp implementations may work
with or without minor changes.

## Implementation
LMC-Lisp boils down to:
- **DFA** for the **lexer**
- **PDA** for the **LALR(1) parser**
- **AOT** execution engine

## Usage
```lisp
(lmc-run "path/to/lmc/assembly/file.lmc" input-list)
```

## License
The project is licensed under the MIT License. See LICENSE for further information.
