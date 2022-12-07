# haskell-definitions

You'll need
[Stack](https://docs.haskellstack.org/en/stable/install_and_upgrade/) to build
and run this code.

To build documentation, do

```sh
stack haddock --open
```

This will give you a huge list of modules, you'll need to find
`haskell-definitions` there. Inside each module, you can click on ‘source’ link
to see the Literate Haskell implementation.

To run Haskell repl with modules described here, you need to do

```sh
stack ghci
```
