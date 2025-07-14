# file: flake.nix
{
  inputs = {
    # ...
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake = {
      url = "github:srid/haskell-flake";
    };
    nixpkgs = {
      url = "nixpkgs/nixos-24.11";
    };
  };

  outputs = inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      imports = [
        # ...
        inputs.haskell-flake.flakeModule
      ];
      perSystem = { self', system, lib, config, pkgs, ... }: {
        haskellProjects.default = {
          # basePackages = pkgs.haskellPackages;

          # Packages to add on top of `basePackages`, e.g. from Hackage
          packages = {
            # aeson.source = "1.5.0.0"; # Hackage version
          };

          # my-haskell-package development shell configuration
          devShell = {
            hlsCheck.enable = true;
            tools = hp: with hp; {
              inherit
                cabal-install
                ghcid
                # haskell-language-server
                ;
            };
          };

          # What should haskell-flake add to flake outputs?
          autoWire = [ "packages" "apps" "checks" ]; # Wire all but the devShell
        };

        devShells.default = pkgs.mkShell {
          name = "ΛUC dev";
          inputsFrom = [
            # ...
            config.haskellProjects.default.outputs.devShell
          ];
          nativeBuildInputs = with pkgs; [
            # other development tools.
          ];
        };
      };
    };
}
