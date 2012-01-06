#!/bin/sh

# This file is run by the LRDE autobuilder after a successful compilation.
# It is not meant to be distributed with Spot.

set -e
set -x

# Buildbot will tell us the name of the branch being compiled using $1.
rev=$1

case $rev in
  master) rev=;;
  *) rev="-$rev";;
esac

# Retrieve the package version
VERSION=`autoconf --trace='AC_INIT:$2'`

rm -rf /lrde/dload/spot/spot-snapshot$rev.tmp
cp -pR doc/spot.html /lrde/dload/spot/spot-snapshot$rev.tmp
chmod -R a+rX /lrde/dload/spot/spot-snapshot$rev.tmp
mv -f spot-$VERSION.tar.gz /lrde/dload/spot/spot-snapshot$rev.tar.gz
chmod a+rX /lrde/dload/spot/spot-snapshot$rev.tar.gz
rm -rf /lrde/dload/spot/spot-snapshot$rev.html
mv -f /lrde/dload/spot/spot-snapshot$rev.tmp /lrde/dload/spot/spot-snapshot$rev.html
