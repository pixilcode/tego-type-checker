# Tego TypeChecker

This project is a typechecker for the Tego programming language, implemented in Coq. It ensures that Tego programs are type-safe by verifying that expressions and values follow the language's type rules.

This project was done for *CS 401R: Software Foundations* at BYU. It is intended for learning and exploration rather than completion.

## Goals

- **Type Inference**: Automatically determines the type of expressions.
- **Type Checking**: Verifies that expressions match expected types.
- **Supported Constructs**:
  - Literals (e.g., integers, booleans)
  - Variables and let bindings
  - Functions and applications
  - If expressions
  - Pattern matching with `match`

## Requirements

- [Coq](https://coq.inria.fr/) (version 8.13 or later)

## How to Use

1. Clone the repository:
   ```bash
   git clone https://github.com/theDragonFire/tego-typechecker.git
   cd tego-typechecker
   ```

2. Open the Coq files in your Coq IDE (e.g., CoqIDE or VS Code with the Coq extension).

3. Step through the code to explore or verify the typechecker.
