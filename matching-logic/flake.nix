{
  description = "A template that shows all standard flake outputs";

  inputs = {
    nixpkgs.url = "github:NixOs/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
   };

  outputs = { self, nixpkgs, flake-utils }: (
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
      in {
        packages.hello = pkgs.hello;

        devShell = pkgs.mkShell {
          buildInputs = [
            pkgs.coq
            pkgs.coqPackages.equations
            pkgs.coqPackages.stdpp
          ];
         };
      }
    )
  );
}
