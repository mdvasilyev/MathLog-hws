#!/usr/bin/env sh

if [ "$#" -ne 2 ] ; then
    echo "Usage: sh $0 <hw#> <task#>"
    exit 1
fi

task=$2
number=$(echo "$task" | sed 's/[^0-9]*//g')
last_char="${task:0-1}"

git add "$1.tex"
if [ $(printf '%s' "$last_char" | grep -c '[[:alpha:]]') -eq 1 ] ; then
    git commit -m "sln: add sln to task $number $last_char"
else
    git commit -m "sln: add sln to $number"
fi
git push

echo "Done!"
exit 0
