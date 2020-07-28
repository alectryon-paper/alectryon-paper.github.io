#!/usr/bin/env sh
cd $1
# if [ ! -f index.html ]; then
echo $(pwd)
tree -H '.' -L 1 --noreport --charset utf-8 \
     -P "*.v|*.rst|*.coq|*.ml|*.html" \
     > index.html
# else
#     echo "Skipping $(pwd)"
# fi
