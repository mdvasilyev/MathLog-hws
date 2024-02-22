#!/usr/bin/env sh

if [ "$#" -ne 2 ] ; then
    echo "Usage: sh $0 <hw#> <task#>"
    exit 1
fi

git add "$1"
git commit -m "sln: add sln to $2"
git push

echo "Done!"
exit 0
