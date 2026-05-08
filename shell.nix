{ nixpkgs ? import <nixpkgs> {} }:
nixpkgs.mkShell {
  nativeBuildInputs = with nixpkgs; [
    alire
    gnat14Packages.gnat
    gnat14Packages.gprbuild
    gnat14Packages.gnatprove
    z3
  ];
}
