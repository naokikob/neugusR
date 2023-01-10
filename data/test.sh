#!/bin/bash
echo 'processing sorted.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 1 -nodes2 8 sorted.dat
echo 'processing sortedrev.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 1 -nodes2 8 sortedrev.dat
echo 'processing starge.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 1 -nodes2 8 stairge.dat
echo 'processing allge.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 1 -nodes2 8 allge.dat
echo 'processing allle.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 1 -nodes2 8 allle.dat
echo 'processing somege.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 1 -nodes2 8 somege.dat
echo 'processing avge.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 1 -nodes2 8 avge.dat
echo 'processing listle.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 1 -nodes2 8 listle.dat
echo 'processing sumle.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 1 -nodes2 8 sumle.dat
echo 'processing updown.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 2 -nodes2 16 updown.dat
echo 'processing max.dat'
time timeout 1200 ../learn.sh -rnodes 1 -rbnodes 2 -nodes 8 -nodes2 16 max.dat
