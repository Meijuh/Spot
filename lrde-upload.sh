#!/bin/sh

# This file is run by the LRDE autobuilder after a successful compilation.
# It is not meant to be distributed with Spot.

set -e
set -x

# Buildbot will tell us the name of the branch being compiled using $1.
rev=$1

# Retrieve the package version
VERSION=`autoconf --trace='AC_INIT:$2'`

DEST=/lrde/dload/spot/snapshots/

umask 022

rm -rf $DEST/$rev.tmp
mkdir -p $DEST/$rev.tmp
cp -pR doc/spot.html $DEST/$rev.tmp
chmod -R a+rX $DEST/$rev.tmp
mv -f spot-$VERSION.tar.gz $DEST/$rev.tar.gz
chmod a+rX $DEST/$rev.tar.gz
rm -rf $DEST/$rev.html
mv -f $DEST/$rev.tmp $DEST/$rev.html
