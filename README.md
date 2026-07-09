# Mining Equations

This project contains a translator from an arbitrary SHA-256 mining problem into a system of bit-wise equations of the form

```c = a op b```

It also has automatic inversion and substitution functionalities where possible.

This project is currently abandoned.

## Contents

- `Mining/Basic.lean`: main flow of the program
- `Mining/Test.lean`: an example with a real-world Bitcoin block header
- Other Lean modules inside `Mining/`

## How to run

- [Install Lean](https://lean-lang.org/install/manual/)
- You can run with `lake exe mining`, but I recommend editing `Mining/Basic.lean` and `Mining/Test.lean` with the VSCode extension and consulting the Lean Info View
