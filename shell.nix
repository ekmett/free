{ pkgs ? import <nixpkgs> {} }:
let X11-deps = with pkgs.xorg; [ libX11 libXrandr libXScrnSaver libXext ]; # needed for building mandelbrot example
in pkgs.mkShell {
  buildInputs = X11-deps;
}
