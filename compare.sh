#!/bin/bash
set -o errexit
set -o pipefail
set -o nounset

if [ $# != 1 ]; then
    echo "$0 <args>"
    exit 1
fi
ARGS="$1"

EMITJSON=$(echo "$ARGS" | grep -vq emitJSON; echo $?)

echo em
/usr/bin/time ./emsdk/emscripten/incoming_64bit_optimizer/optimizer $ARGS > emoptout
echo ay
/usr/bin/time ./ayzim $ARGS > ayzimout

rmleadingspace() {
    sed 's/^ *//'
}

if [ $EMITJSON = 1 ]; then
    cat emoptout | python -m json.tool | rmleadingspace > emoptoutfmt &
    cat ayzimout | python -m json.tool | rmleadingspace > ayzimoutfmt &
    for job in $(jobs -p); do
        wait $job
    done
else
    cp emoptout emoptoutfmt
    # convert 1.2e-06 to 1.2e-6, since emopt is inefficient here
    sed -i 's/\([.0-9]e-*\)0*\([1-9]\)/\1\2/g' emoptoutfmt
    cp ayzimout ayzimoutfmt
fi
