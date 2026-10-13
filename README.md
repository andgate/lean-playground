# Lean playground

A sandbox for standalone Lean experiments, with Mathlib available to every
`.lean` file in this folder.

## Open in VS Code

Open this entire folder in VS Code. The Lean 4 extension uses `lean-toolchain`
to select Lean and `lakefile.toml` to find the project's dependencies.
If the folder was already open during setup, run **Developer: Reload Window**
from the Command Palette.

## Check an experiment

Run these commands from this folder in PowerShell:

```powershell
lake env lean .\set-theory.lean
lake env lean .\eval.lean
```

These are loose experiments rather than a library or executable, so check the
file you are working on directly. A warning about `sorry` means the file loads
but a proof is still unfinished.

## Restore dependencies after cloning

```powershell
lake update
lake exe cache get
```

`elan` manages Lean versions; `lake` manages project dependencies; Mathlib is a
separate mathematics library. Lean and Mathlib are pinned to version 4.34.1.
Keep `lake-manifest.json` in version control to preserve resolved dependencies.
Downloaded packages and compiled files live in `.lake/`, which is ignored.

If a terminal opened before Lean was installed cannot find `lake`, restart the
terminal's parent application to refresh PATH, or use:

```powershell
& "$env:USERPROFILE\.elan\bin\lake.exe" env lean .\set-theory.lean
```
