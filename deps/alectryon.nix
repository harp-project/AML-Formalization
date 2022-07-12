{
    description = "Alectryon";

    inputs = {
        nixpkgs.url = "github:NixOs/nixpkgs";
        flake-utils.url = "github:numtide/flake-utils";
    };

    outputs = { self, nixpkgs, flake-utils, alectryon }: (
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
        {
            packages.default
            = pkgs.python310Packages.buildPythonPackage rec {
                pname = "alectryon";
                version = "1.4.0";

                src = fetchFromGitHub {
                    owner = "cpitclaudel";
                    repo = "alectryon";
                    rev = "739b46da22d272e748f60f3efcd2989d696fba71";
                };

                propagatedBuildInputs = [
                   pygments
                    dominate
                    beautifulsoup4
                    docutils
                    sphinx
                ];

                doCheck = false;;
            }
        }
    )
)
}