# Independent check with Comparator

[Comparator](https://github.com/leanprover/comparator) is the Lean FRO's tool for checking a proof
against a separately written statement. Here:

- `BGChallenge.lean` states the Brualdi-Goldwasser theorem in Mathlib's vocabulary, with `sorry`, and
  imports only the definitions of the answer (`R3Cert.BGAnswer`), not the proof.
- `BGSolution.lean` states the same two theorems and proves them.
- `bg.comparator.json` asks Comparator to confirm that the solution proves exactly the challenge's
  statements, that the proofs use only `propext`, `Quot.sound` and `Classical.choice`, and that the
  exported proof is accepted both by Lean's kernel and by
  [nanoda](https://github.com/ammkrn/nanoda_lib), an independent implementation of the Lean kernel in
  Rust. A soundness bug would have to fool two independently written kernels.

## Run it

```bash
# build the tools once (tag = this project's Lean version)
git clone --depth 1 --branch v4.32.0 https://github.com/leanprover/comparator.git
(cd comparator && lake build lean4export comparator)
git clone --depth 1 https://github.com/ammkrn/nanoda_lib.git && (cd nanoda_lib && cargo build --release)

# then, from formalization/ (after ./build.sh)
export COMPARATOR_LEAN4EXPORT=$PWD/../comparator/.lake/packages/lean4export/.lake/build/bin/lean4export
export COMPARATOR_NANODA=$PWD/../nanoda_lib/target/release/nanoda_bin
export COMPARATOR_LANDRUN=/path/to/landrun   # a sandbox; on macOS a pass-through shim works
lake env comparator comparator/bg.comparator.json
```

## Result

On 27 September 2026 the check passed at commit `295d0ac` (the Lean sources have not changed since):
Comparator reported "Nanoda kernel accepts the solution", "Lean default kernel accepts the solution" and
"Your solution is okay!". The run took 5.1 hours and peaked at 63 GB of memory on an Apple-silicon Mac,
with the pass-through shim described below in place of the landrun sandbox. It has not yet been run in CI.

## The sandbox

Comparator runs its children inside [landrun](https://github.com/Zouuup/landrun), a Linux sandbox.
Since the solution here is our own, a pass-through shim that preserves the `--` separator is enough
(the kernel replay, not the sandbox, is the guarantee); use a real sandbox for untrusted solutions.
