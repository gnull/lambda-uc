# https://nixos.wiki/wiki/Haskell#Using_developPackage_.28use_the_nix_packages_set_for_haskell.29
# https://github.com/NixOS/nixpkgs/blob/master/doc/languages-frameworks/haskell.section.md

let
  pkgs = import <nixpkgs> { };
  haskell = pkgs.haskellPackages;
  # haskell = pkgs.haskell.packages.ghc96;

  pa = haskell.developPackage {
    root = ./.;
    # cabal2nixOptions = "-f -newVty";
  };

  tools = drv: pkgs.haskell.lib.addBuildTools drv (with haskell;
    [ cabal-install
      haskell-language-server
    ]);
	sh = haskell.developPackage {
  	root = ./.;
    # cabal2nixOptions = "-f -newVty";
    modifier = drv: tools drv;
	};

in
  if pkgs.lib.inNixShell then sh else pa
