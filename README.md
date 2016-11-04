Ayzim
=====

> Ayy, zim!

Ayzim is a rewrite of the [Emscripten asm.js optimizer](https://github.com/kripken/emscripten/tree/1.36.0/tools/optimizer) (referred to here as 'Emopt') in Rust (from C++). It should be a drop-in replacement, though you may observe a few minor differences - Ayzim is a little better at choosing a float representation, Emopt has at least one almost-insignificant pattern it optimises better than Ayzim. The rewrite fixed a few bugs in Emopt along the way (most contributed back) and cleaned up a few things. As with any non-trivial rewrite it's probably a little buggy, but the enormous Emscripten test suite reports no issues of consequence so it should be reasonably correct.

Ayzim consumes significantly less memory than Emopt - I've seen between 2x and 6x reduction depending on the passes I was running (with larger multiplier reductions seen when memory usage is larger). Given that Emopt can hit > 7GB of memory if trying to optimise a single large .js file in one go, a 6x reduction is pretty useful (and note that Windows users should see a bit more of an improvement, as Emopt suffers due to some missing features in the MSVC compiler). Ayzim also happens to be a bit faster - ~25% faster on `-O2` (when registerize is used) and ~50% faster on `-O3` (when registerizeHarder is used). Typically the asm.js optimizer isn't a hugely dominating factor in an overall build (it's perhaps 25% of just the link stage), so this generally isn't particularly exciting.

The original motivation for ayzim was to keep my machine usable when trying to optimise what was (probably) the largest asm.js file ever generated (~700MB). The memory consumption would end up swapping out my desktop environment if I allowed it to run everything in parallel (as it does by default), which was annoying. Clearly the correct solution was to rewrite Emopt rather than just buying a new machine :)

The future
----------

 - Make it more useful as a library
 - WASM
