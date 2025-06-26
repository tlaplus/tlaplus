let pkgs = import <nixpkgs> {};
in pkgs.mkShell {
  packages = with pkgs; [
    jdk11
    ant
    maven
    git
  ];
}

