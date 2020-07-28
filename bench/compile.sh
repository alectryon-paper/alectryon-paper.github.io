#!/usr/bin/env bash
compiler=$1
repeat=$2
file=$3

export TIMEFORMAT=$compiler$'\t'$file$'\treal: %3R\tuser: %3U\tsys: %3S'

ALECTRYON="$ALECTRYON $COQC_ARGS --output-directory $(dirname "$file")"
input="$(mktemp)"

if [ "$compiler" = "sertop" ]; then
    $ALECTRYON --debug --frontend coq --backend null "$file" | grep "^>>" | sed 's/^>>//' > "$input"
fi

echo $(which coqc) $COQC_ARGS
function compile() {
    { time { case "$compiler" in
                 coqc) coqc $COQC_ARGS "$file";;
                 coqtop) coqtop $COQC_ARGS  < "$file" > /dev/null 2>&1;;
                 sercomp) sercomp $SERAPI_ARGS  "$file";;
                 sertop) sertop $SERAPI_ARGS  < "$input" > /dev/null;;
                 alectryon-api) $ALECTRYON --frontend coq --backend null "$file" -o "${file%.v}.null";;
                 alectryon-json) $ALECTRYON --frontend coq "$file" -o "${file%.v}.io.json";;
                 alectryon-coqdoc) $ALECTRYON --frontend coqdoc "$file" -o "${file%.v}.html";;
                 alectryon) $ALECTRYON --frontend coq "$file" -o "${file%.v}.v.html";;
                 alectryon-html) $ALECTRYON --frontend coq "$file" -o "${file%.v}.v.html";;
             esac } } 2>&1
}

for i in $(seq "$repeat"); do
    tm=$(compile)
    printf "%s\t$?\n" "$tm"
done
