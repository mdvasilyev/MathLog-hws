#!/usr/bin/env sh

if [ "$#" -ne 1 ] ; then
    echo "Usage: sh $0 <hw#>"
    exit 1
fi

git add template.tex "$1"
git commit -m "new: add $1"
git push

echo "Done!"
exit 0
