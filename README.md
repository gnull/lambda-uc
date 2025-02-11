# ΛUCk: Purely Functional EDSL for Universal Composability

[![builds.sr.ht status](https://builds.sr.ht/~ph14nix/haskell-uc.svg)](https://builds.sr.ht/~ph14nix/haskell-uc?)
—
[Haddock](https://arrakeen-worm.xyz/haddock/haskell-uc/)

The goal of this project is to express the protocols and functionalities of [Universal Composability](https://dl.acm.org/doi/abs/10.1145/3402457) in an actual programming language,
  where programs can be written unambiguously,
  take advantage of Haskell's expressive types and modern programming tools/techniques.
Another advantage of having a programming language is automatic extraction of a prototype
  for any protocol implemented using ΛUCk.

To enter development enviornment, run `nix-shell` or `nix develop` in this directory
  (this uses [Nix](https://nixos.org/)).

From there, you can run `cabal build` or `cabal repl` to inspect the code.
