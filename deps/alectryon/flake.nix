{
    description = "Alectryon";

    inputs = {
        nixpkgs.url = "github:NixOs/nixpkgs";
        flake-utils.url = "github:numtide/flake-utils";
    };

    outputs = { self, nixpkgs, flake-utils }: (
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
        {
            packages.default
            = pkgs.python310Packages.buildPythonPackage rec {
                pname = "alectryon";
                version = "1.4.0";

                src = pkgs.fetchFromGitHub {
                    owner = "cpitclaudel";
                    repo = "alectryon";
                    rev = "739b46da22d272e748f60f3efcd2989d696fba71";
                };

                propagatedBuildInputs = [
                   pkgs.python310Packages.pygments
                    pkgs.python310Packages.dominate
                    pkgs.python310Packages.beautifulsoup4
                    pkgs.python310Packages.docutils
                    pkgs.python310Packages.sphinx
                ];

                doCheck = false;
            };
        }
    )
    );
}