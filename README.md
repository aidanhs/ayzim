Ayzim
=====

> Ayy, zim!

Ayzim is a rewrite of the [Emscripten asm.js optimizer](https://github.com/kripken/emscripten/tree/1.36.0/tools/optimizer) in Rust (from C++). It should be a drop-in replacement, though you may observe a few minor differences - Ayzim is a little better at choosing a float representation, Emscripten has at least one almost-insignificant pattern it optimises better than Ayzim.

The rewrite fixed a few bugs in the original optimizer along the way (most contributed back) and cleaned up a few things. However, as with any non-trivial rewrite it's probably still quite buggy. The rewrite is neither significantly faster than the original nor is it memory safe.

However, it does consume significantly less memory than the original - I've seen between 2x and 6x reduction depending on the passes I was running. Given that the original can hit > 7GB of memory if trying to optimise a single large .js file in one go, this is pretty useful to avoid swapping on average machines.

In practice Emscripten splits up files to be optimised to avoid this problem...but that still doesn't help in some cases. The original motivation for ayzim to keep my machine usable when trying to optimise what was (probably) the largest asm.js file ever generated (~700MB).

The future
----------

 - Make it more useful as a library
 - WASM
